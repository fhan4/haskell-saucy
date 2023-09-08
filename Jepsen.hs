 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts, Rank2Types,
 PartialTypeSignatures
  #-} 

module Tendermint where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper
import TestTools

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map, member, empty)
import Data.List (elemIndex, delete)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Map.Strict as Map

import System.Process (createProcess, proc, std_out, StdStream(..))
import GHC.IO.Handle

{-
  v tx creator 
  * curl execute
  * receive output 
  * quick check generate them
  * check linearizability
-}

--data CliP2F a = CliP2F_Input a deriving (Show, Eq)
data CliF2P a = CliF2P_Ok | CliF2P_Deliver a deriving (Show, Eq)
-- data CliA2F a = CliA2F_Deliver PID a deriving (Show, Eq)
data CliF2A a = CliF2A a deriving (Show, Eq)

fCmdCli :: MonadFunctionalityAsync m t =>
  Functionality t (CliF2P t) Void Void Void Void m
fCmdCli (p2f, f2p) (a2f, f2a) (z2f, f2z) = do
  let sid = ?sid :: SID
  --let (pidS :: PID, sssid :: String) = readNote "fCmd" $ snd sid

  --if not $ member pidS ?crupt then do
  fork $ forever $ do
    (pid, m) <- readChan p2f
    liftIO $ putStrLn $ "\n\n received an input from party " ++ show pid
    --if pid == pidS then do
    eventually $ do
      liftIO $ putStrLn $ "eventually the input"
      writeChan f2p (pid, CliF2P_Deliver m)
    writeChan f2p (pid, CliF2P_Ok)
    --else error "cant get message from non-sender"
  return ()
  --else return ()

type BlockHeight = Int
type Hash = String 

data MerkleP2F = MerkleP2F_Get String | MerkleP2F_Set String String | MerkleP2F_CAS String String String | MerkleP2F_Tx Hash deriving (Show, Eq)
data MerkleF2P = MerkleF2P_TxHash Hash | MerkleF2P_Value String | MerkleF2P_Tx String | MerkleF2P_Arb String | MerkleF2P_Ok deriving (Show, Eq) 

possibleKeys = [return "alice", return "bob", return "charlie", return "dave", return "eric", return "frank"]
possibleValues = [return "crypto", return "cs", return "security", return "biology", return "circuits", return "architecture", return "design"]

-- the generator for merkle inputs, it shoudl be doing READs, WRITES, and CAS from a small
-- group of keys. Here we use the pool of keys and values above
merkleGenerator :: Int -> [Gen PID] -> Gen [(PID, ClockP2F MerkleP2F)]
merkleGenerator n parties = frequency $
  [ (1, return []),
    (5, if n==0 then return [] else (:) <$> 
      (oneof parties >>=
        \pid -> (oneof possibleKeys >>= 
          \k -> (oneof possibleValues >>= 
            \v -> return (pid, ClockP2F_Through $ MerkleP2F_Set k v)))) <*> merkleGenerator (n-1) parties),
    (5, if n==0 then return [] else (:) <$> 
      (oneof parties >>=
        \pid -> oneof possibleKeys >>= 
          \k -> (oneof possibleValues >>= 
            \c -> (oneof possibleValues >>= 
              \v -> return (pid, ClockP2F_Through $ MerkleP2F_CAS k c v)))) <*> merkleGenerator (n-1) parties),
    (5, if n==0 then return [] else (:) <$> 
      (oneof parties >>=
        \pid -> oneof possibleKeys >>= 
          \k -> return (pid, ClockP2F_Through $ MerkleP2F_Get k)) <*> merkleGenerator (n-1) parties)
  ]


wschars = "\t\r\n"
lstrip :: String -> String
lstrip s = case s of 
              [] -> []
              (x:xs) -> if elem x wschars
                        then lstrip xs
                        else s

rstrip :: String -> String
rstrip = reverse . lstrip . reverse

-- protocol wrapper around parties that accepts messages, delays and then gives as input to their respective nodes
protMerkleeyes :: MonadAsyncP m =>  
  Protocol (ClockP2F MerkleP2F) MerkleF2P (CliF2P MerkleP2F) MerkleP2F m
--Void Void m
protMerkleeyes (z2p, p2z) (f2p, p2f) = do
  let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "merkle" $ snd ?sid

  let _set_tx k v = do
        (_, Just hout, _, _) <- createProcess (proc "python3" ["jepsen/query.py", "set", ?pid, show k, show v]){ std_out = CreatePipe }
        threadDelay 500000
        hGetContents hout

  let _get_tx k = do
        (_, Just hout, _, _) <- createProcess (proc "python3" ["jepsen/query.py", "get", ?pid, show k]){ std_out = CreatePipe }
        threadDelay 1500000
        hGetContents hout

  let _cas_tx k c v = do
        (_, Just hout, _, _) <- createProcess (proc "python3" ["jepsen/query.py", "cas", ?pid, show k, show c, show v]){ std_out = CreatePipe }
        threadDelay 1500000
        hGetContents hout

  let _tx_tx h = do
        (_, Just hout, _, _) <- createProcess (proc "python3" ["jepsen/query.py", "txinfo", ?pid, h]){ std_out = CreatePipe }
        hGetContents hout

  fork $ forever $ do
    mf <- readChan z2p
    case mf of
      ClockP2F_Through x -> do
        writeChan p2f x
        return ()
      ClockP2F_Pass -> ?pass

  fork $ forever $ do
    m <- readChan f2p
    case m of 
      CliF2P_Deliver x -> do
        case x of 
          MerkleP2F_Get k -> do
            r <- liftIO $ _get_tx k
            writeChan p2z (MerkleF2P_TxHash (rstrip r))
          MerkleP2F_Set k v -> do
            r <- liftIO $ _set_tx k v
            writeChan p2z (MerkleF2P_TxHash (rstrip r))
          MerkleP2F_CAS k c v -> do
            r <- liftIO $ _cas_tx k c v
            writeChan p2z (MerkleF2P_TxHash (rstrip r))
          MerkleP2F_Tx h -> do
            liftIO $ putStrLn $ "[" ++ show ?pid ++ "] txing"
            r <- liftIO $ _tx_tx h
            writeChan p2z (MerkleF2P_Arb r)
      CliF2P_Ok -> do
            liftIO $ putStrLn $ "got the OK"
            writeChan p2z MerkleF2P_Ok
  return ()

testTenderEnv :: MonadEnvironment m =>
  Environment MerkleF2P (ClockP2F MerkleP2F)
    (SttCruptA2Z (CliF2P MerkleP2F) 
                 (Either (ClockF2A MerkleP2F) Void))
    (SttCruptZ2A (ClockP2F MerkleP2F) (Either ClockA2F Void)) 
    Void ClockZ2F String m
testTenderEnv z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("merkle", show("2", ["2", "3", "4"], ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

  --fork $ forever $ do
  --  (pid, m) <- readChan p2z
  --  liftIO $ putStrLn $ "[test merkle]: pid[" ++ show pid ++ "] output " ++ show m
  --  ?pass

  writeChan z2p ("3", ClockP2F_Through $ MerkleP2F_Get "eric")
  (pid, m) <- readChan p2z
  case m of
    MerkleF2P_TxHash h -> do
      liftIO $ putStrLn $ "[" ++ show pid ++ "] " ++ show h
      threadDelay 2000000
      writeChan z2p ("3", ClockP2F_Through $ MerkleP2F_Tx h)
      (pid, m) <- readChan p2z
      liftIO $ putStrLn $ "[" ++ show pid ++ "] " ++ show m
      writeChan z2p ("2", ClockP2F_Through $ MerkleP2F_Tx h)
      (pid, m) <- readChan p2z
      case m of
        MerkleF2P_TxHash h -> liftIO $ putStrLn $ "[" ++ show pid ++ "] " ++ show m

  --  _ -> return ()

  writeChan outp "test"

  return ()
      
test :: IO String
test = runITMinIO 120 $ execUC
  testTenderEnv
  (runAsyncP protMerkleeyes)
  (runAsyncF fCmdCli)
  dummyAdversary


propEnvTest :: (MonadEnvironment m) =>
  Environment MerkleF2P (ClockP2F MerkleP2F)
    (SttCruptA2Z (CliF2P MerkleP2F) 
                 (Either (ClockF2A MerkleP2F) Void)) 
    (SttCruptZ2A (ClockP2F MerkleP2F) (Either ClockA2F Void)) 
    Void ClockZ2F ([(PID, MerkleF2P)]) m
propEnvTest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("merkle", show("2", ["2", "3", "4"], ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty

  let parties = [return "2", return "3", return "4"]

  () <- readChan pump
  --inps <- liftIO $ generate $ merkleGenerator 30 parties
  txHashes <- newIORef []
  transcript <- newIORef []
  --forMseq_ inps $ \cmd -> do
  --  writeChan z2p cmd
  --  (pid, m) <- readChan p2z 
  --  modifyIORef transcript (++ [(pid, m)])
  --  case m of
  --    MerkleF2P_TxHash h -> do modifyIORef txHashes $ (++) [h]
  --    _ -> do return ()

  (lastOut, _, clockChan) <- envReadOut p2z a2z

  inps <- liftIO $ generate $ merkleGenerator 50 parties
  forMseq_ inps $ \cmd -> do
    writeChan z2p cmd
    () <- readChan pump
    m <- readIORef lastOut
    --(pid, m) <- readChan p2z
    case m of
      Just (Right (pid, MerkleF2P_TxHash h)) -> do modifyIORef txHashes $ (++) [h]
      _ -> do return ()

  writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount)) 
  c <- readChan clockChan 
  delivers <- liftIO $ generate $ rqDeliverAll c  
  forMseq_ delivers $ \d -> do
    case d of
      CmdDeliver idx' -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')))
      _ -> error "should't have any other messages"
    readChan pump

  tr <- readIORef transcript  
 
  writeChan outp tr 
  return ()
  
prop_test = monadicIO $ do
  t <- run $runITMinIO 120 $ execUC
    propEnvTest
    (runAsyncP protMerkleeyes)
    (runAsyncF fCmdCli)
    dummyAdversary
  assert True
