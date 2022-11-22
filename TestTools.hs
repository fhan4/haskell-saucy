 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, Rank2Types
  #-} 

module TestTools where

import ProcessIO
import StaticCorruptions
import Multisession
import Multicast
import Async
import TokenWrapper

import Safe
import Control.Concurrent.MonadIO 
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List (elemIndex, delete)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

type CruptList = Map PID ()
type Tokens = Int
type MulticastTokens = Int

--forMseq_ xs f = sequence_ $ map f xs

shuffleParties pids = do return (liftIO $ (generate $ shuffle pids))

selectPIDs :: (MonadIO m) => [PID] -> m [PID]
selectPIDs pids = do
    s_pids <- liftIO $ (generate $ shuffle pids)
    n <- liftIO $ (generate $ choose (1, length pids))
    let r_pids :: [PID] = take n s_pids
    return r_pids

--multicastSid :: (MonadIO m) => String -> PID -> [PID] -> String -> m SID
multicastSid sssid snd ps s = (sssid, show (snd, ps, s))

data AsyncCmd = CmdDeliver Int | CmdMakeProgress | CmdGetCount deriving Show

type AsyncInput = (AsyncCmd, Tokens)

{- Generate a list of indices for run queue deliver requests.
   The output list indices can all always be execued if `n` is set correctly -}
rqIndexList :: Int -> Gen [Int]
rqIndexList n = frequency
    [ (1,return []),
      (5, if n==0 then return [] else (:) <$> choose (0,n-1) <*> (rqIndexList (n-1)))
    ] 

rqDeliverList :: Int -> Gen [AsyncCmd]
rqDeliverList n = frequency
    [ (1, return []),
      (50, if n==0 then return [] else (:) <$> (choose (0,n-1) >>= return . CmdDeliver) <*> (rqDeliverList (n-1)))
    ]

rqDeliverAll :: Int -> Gen [AsyncCmd]
rqDeliverAll n = oneof 
  [ if n == 0 then return [] else (:) <$> (choose (0,n-1) >>= return . CmdDeliver) <*> (rqDeliverAll (n-1)) ]

rqDeliverOrProgress :: Int -> Gen [AsyncCmd]
rqDeliverOrProgress n = frequency
    [ (1, return []),
      (5, if n==0 then return [] else (:) <$> (choose (0,n-1) >>= return . CmdDeliver) <*> (rqDeliverList (n-1))),
      (10, if n==0 then return [] else (:) <$> return CmdMakeProgress <*> (rqDeliverOrProgress (n-1)))
    ]

-- clockChan -> tokensWithGetCount -> cmdListChan -> Environment 
deliverOrProgressSubset :: (MonadEnvironment m) =>
    Chan Int -> Int -> Chan [Either customCmd AsyncCmd] -> 
  (Environment _f2p ((ClockP2F _p2f), CarryTokens Int)
    (SttCruptA2Z p2a2z (Either (ClockF2A lf2a) rf2a))
    ((SttCruptZ2A (ClockP2F z2a2p) (Either ClockA2F z2a2f)), CarryTokens Int) Void
    ClockZ2F (config, [Either customcmd AsyncCmd], ts) m)
deliverOrProgressSubset clockChan t forCmdList _ _ (a2z, z2a) (f2z, z2f) pump _ = do
  
  cmdList <- newIORef []
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens t)
  num <- readChan clockChan
  delivers <- liftIO $ generate $ rqDeliverOrProgress num
  modifyIORef cmdList $ (++) [Right $ CmdGetCount]

  forMseq_ delivers $ \d -> do
    case d of
      CmdDeliver idx' -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens t)
        c <- readChan clockChan
        if idx' < c then do
          modifyIORef cmdList $ (++) [Right $ d]
          writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
        else return ()
      CmdMakeProgress -> do
        writeChan z2f ClockZ2F_MakeProgress
        modifyIORef cmdList $ (++) [Right $ d]
      _ -> error "Z: unexpected command"

    () <- readChan pump
    return ()
 
  c <- readIORef cmdList
  writeChan forCmdList c
  

