 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
  #-} 

module CheckABA where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper
import ABA
import TestTools

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List ((\\), elemIndex, delete)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data ABACmd = CmdABAP2F PID Bool | CmdAux SID PID Int Bool MulticastTokens | CmdEst SID PID Int Bool MulticastTokens | CmdCoin SID Int deriving (Show, Eq, Read)

type ABAInput = (ABACmd, Tokens)
type ABAConfig = (SID, [PID], CruptList, Int)

makeSBCastSid :: [PID] -> PID -> Int -> Bool -> SID
makeSBCastSid ps p r b = (show ("sbcast", p, r, b), show (p, ps, ""))

makeMainSid :: [PID] -> PID -> Int -> Bool -> SID
makeMainSid ps p r w = (show ("maincast", p, r, w), show (p, ps, ""))

abaGenerator :: Int -> Int -> (Bool -> SID) -> (Bool -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [Either ABAInput AsyncInput]
abaGenerator n numQueue mainssid sbssid parties inputs round dts = frequency $
  [ (1, return []), 
    (10, if n==0 then return []
         else if numQueue==0 then (abaGenerator n 0 mainssid sbssid parties inputs round dts)
         else (:) <$> (choose (0,numQueue-1) >>= \i -> return (Right (CmdDeliver i, 0))) <*> (abaGenerator (n-1) (numQueue-1) mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>=
          (\pl -> oneof inputs >>=
            \i -> return (Left (CmdEst (sbssid i) (pl !! 0) round i dts, 0)))) <*> (abaGenerator (n-1) numQueue mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> 
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> return (Left (CmdAux (mainssid i) (pl !! 0) round i dts, 0))))) <*> (abaGenerator (n-1) numQueue mainssid sbssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> return (Left (CmdCoin (show ("sRO", round), show ("-1", parties,"")) round, 0)) <*> (abaGenerator (n-1) numQueue mainssid sbssid parties inputs round dts))
  ]

-- TODO hard-coded 32 import
envExecABACmd :: (MonadITM m) =>
  (Chan (PID, ((ClockP2F Bool), CarryTokens Int))) ->
  (Chan ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int))) (Either _ (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int)) ->
  (Chan ()) -> (Either ABAInput _) -> m ()
envExecABACmd z2p z2a pump cmd = do
  case cmd of
      Left ((CmdABAP2F pid' x'), st') -> do
          writeChan z2p $ (pid', ((ClockP2F_Through $ x'), SendTokens 32))
          readChan pump
      Left ((CmdEst ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', ((CoinCastA2F_Deliver pid' (EST r' x', DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      Left ((CmdAux ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', ((CoinCastA2F_Deliver pid' (AUX r' x', DeliverTokensWithMessage 0)), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      Left ((CmdCoin ssid' r'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (CoinCastA2F_ro r', DeliverTokensWithMessage 0))), SendTokens 1)
          readChan pump

performABAEnv 
    :: (MonadEnvironment m) =>
    ABAConfig -> [Either ABAInput AsyncInput] ->
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      --(Either ClockA2F (SID, (CoinCastA2F ABACast, CarryTokens Int)))), CarryTokens Int) Void
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) ABATranscript m
performABAEnv abaConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  return ()

testUEnvABA
    :: (MonadEnvironment m) =>
    Environment (ABAF2P, CarryTokens Int) (ClockP2F Bool, CarryTokens Int)
        (SttCruptA2Z (SID, ((CoinCastF2P ABACast), CarryTokens Int))
                     (Either (ClockF2A (SID, ((ABACast, TransferTokens Int), CarryTokens Int)))
                             (SID, CoinCastF2A)))
        ((SttCruptZ2A (ClockP2F (SID, (CoinCastP2F ABACast, CarryTokens Int)))
                      --(Either ClockA2F (SID, (CoinCastA2F ABACast, CarryTokens Int)))), CarryTokens Int) Void
                      (Either ClockA2F (SID, (CoinCastA2F ABACast, TransferTokens Int)))), CarryTokens Int) Void
        (ClockZ2F) (ABAConfig, [Either ABAInput AsyncInput], ABATranscript) m
testUEnvABA z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let parties = ["Alice", "Bob", "Charlie", "Mary"]
  let sid = ("sidTestEnvMulticastCoin", show (parties, 1, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Bob",())]
  
  let parties = ["Alice", "Bob", "Charlie", "Mary"] :: [PID]
  let t = 1 :: Int
  let crupt = "Bob" :: PID
  let honest = parties \\ [crupt]
  let sssid = "sidTestEnvMulticastCoin"
  let sid = (sssid, show (parties, t, ""))
  
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])
  
  transcript <- newIORef []
  cmdList <- newIORef []  
  debugLog <- newIORef []
  thingsHappened <- newIORef 0


  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  clockChan <- newChan
  fork $ forever $ do
    mb <- readChan a2z
    modifyIORef transcript (++ [Left mb])
    case mb of
      SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
        printEnvReal $ "Pass"
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
        writeChan clockChan c
      SttCruptA2Z_P2A (pid, m) -> do
        case m of
          _ -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
        ?pass
      _ -> error $ "Help!" ++ show mb

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 1000))])
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 

  let inputs = do [return True, return False]
 
  let checkQueue n = do
        modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 0))])
        modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
        writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
        
        c <- readChan clockChan
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  let inputTokens = 64
  -- Give somehonest parties some inputs
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdABAP2F h x, inputTokens)])
    modifyIORef debugLog $ (++ [Left (Left (CmdABAP2F h x, inputTokens))])
    writeChan z2p $ (h, ((ClockP2F_Through $ x), SendTokens inputTokens))
    readChan pump

  firstInp <- newIORef []
  forMseq_ [1..20] $ \r -> do 
    modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
    modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 0))])
    writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
    c <- readChan clockChan
    inps <- liftIO $ generate $ abaGenerator (max 40 c) c (makeMainSid parties crupt r) (makeSBCastSid parties crupt r) parties inputs r 64

    forMseq_ inps $ \i -> do
      modifyIORef debugLog $ (++ [Left i])
      modifyIORef cmdList $ (++ [i])
      envExecAsyncCmd z2p z2a z2f clockChan pump i envExecABACmd

  tr <- readIORef transcript  
  cl <- readIORef cmdList
  
  writeChan outp ((sid, parties, (Map.fromList [(crupt,())]), t), cl, tr)

prop_uABATest = monadicIO $ do
  let prot () = protABA
  (config', c', t') <- run $ runITMinIO 120 $ execUC
    testUEnvABA
    (runAsyncP $ prot ())
    (runAsyncF $ bangFAsync fMulticastAndCoinToken)
    dummyAdversaryToken
  outputs <- newIORef Set.empty
  forMseq_ [0..(length t')-1] $ \i -> do
    case (t' !! i) of
      Right (pid, (ABAF2P_Out b, SendTokens st)) -> do
        modifyIORef outputs $ Set.insert b
      Right _ -> return ()
      Left _ -> return ()
  o <- readIORef outputs

  printYellow ("[Config]\n\n" ++ show config')
  printYellow ("[Inputs]\n\n" ++ show c')

  assert ( (Set.size o) == 0)
