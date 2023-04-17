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

data AsyncCmd = CmdDeliver Int | CmdMakeProgress | CmdGetCount deriving (Eq, Show, Ord)

type AsyncInput = (AsyncCmd, Tokens)

{- Generate a list of indices for run queue deliver requests.
   The output list indices can all always be execued if `n` is set correctly -}
rqIndexListWeights f n = [ (1, return []), (5, if n==0 then return [] else (:) <$> choose (0,n-1) <*> (f (n-1))) ]

rqIndexList :: Int -> Gen [Int]
rqIndexList n = frequency $ (rqIndexListWeights rqIndexList n)
      --[ (1,return []),
    --  (5, if n==0 then return [] else (:) <$> choose (0,n-1) <*> (rqIndexList (n-1)))
    --] 

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

-- environment generate a sequence of Deliver and MakeProgress messages
-- and executes them
envDeliverOrProgressSubset :: (MonadEnvironment m) =>
    Chan Int -> Int -> Chan [Either customCmd AsyncInput] -> 
  (Environment _f2p ((ClockP2F _p2f), CarryTokens Int)
    (SttCruptA2Z p2a2z (Either (ClockF2A lf2a) rf2a))
    ((SttCruptZ2A (ClockP2F z2a2p) (Either ClockA2F z2a2f)), CarryTokens Int) Void
    ClockZ2F (config, [Either customcmd AsyncInput], ts) m)
envDeliverOrProgressSubset clockChan t forCmdList _ _ (a2z, z2a) (f2z, z2f) pump _ = do
  
  cmdList <- newIORef []
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
  num <- readChan clockChan
  delivers <- liftIO $ generate $ rqDeliverOrProgress num
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]

  forMseq_ delivers $ \d -> do
    case d of
      CmdDeliver idx' -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
        c <- readChan clockChan
        modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
        if idx' < c then do
          modifyIORef cmdList $ (++) [Right (d, 0)]
          writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
        else return ()
      CmdMakeProgress -> do
        writeChan z2f ClockZ2F_MakeProgress
        modifyIORef cmdList $ (++) [Right (d, 0)]
      _ -> error "Z: unexpected command"

    () <- readChan pump
    return ()
 
  c <- readIORef cmdList
  writeChan forCmdList c
  
-- Does the same as above, but at the end does Deliver messages
-- until the all the _existing_ codeblocks in the runqueue
-- and not new codeblocks using `thingsHappened` 
envDeliverOrProgressAll :: (MonadEnvironment m) =>
    IORef Int -> Chan Int -> Int -> Chan [Either customCmd AsyncInput] -> 
  (Environment _f2p ((ClockP2F _p2f), CarryTokens Int)
    (SttCruptA2Z p2a2z (Either (ClockF2A lf2a) rf2a))
    ((SttCruptZ2A (ClockP2F z2a2p) (Either ClockA2F z2a2f)), CarryTokens Int) Void
    ClockZ2F (config, [Either customcmd AsyncInput], ts) m)
envDeliverOrProgressAll thingsHappened clockChan t forCmdList _ _ (a2z, z2a) (f2z, z2f) pump _ = do
  
  cmdList <- newIORef []
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
  num <- readChan clockChan
  liftIO $ putStrLn $ "\n\t num: " ++ show num
  th <- readIORef thingsHappened
  liftIO $ putStrLn $ "\n\tthings happened: " ++ show th
  delivers <- liftIO $ generate $ rqDeliverOrProgress num
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]

  forMseq_ delivers $ \d -> do
    case d of
      CmdDeliver idx' -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
        c <- readChan clockChan
        modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
        if idx' < c then do
          modifyIORef cmdList $ (++) [Right (d, 0)]
          writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
        else return ()
      CmdMakeProgress -> do
        writeChan z2f ClockZ2F_MakeProgress
        modifyIORef cmdList $ (++) [Right (d, 0)]
      _ -> error "Z: unexpected command"

    () <- readChan pump
    return ()

  th <- readIORef thingsHappened
  liftIO $ putStrLn $ "\n\tthings happened: " ++ show th
 
  if (th > num) then error "thingshappened doesn't work"
  else return ()
  delivers <- liftIO $ generate $ rqDeliverAll (num - th)
  
  forMseq_ delivers $ \d -> do
    case d of
      CmdDeliver idx' -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
        modifyIORef cmdList $ (++) [Right (d,0)]
      _ -> error "shouldn't be a makeprogress"
    () <- readChan pump
    return ()
 
  th <- readIORef thingsHappened
  if (th /= num) then error ("didn't deliver everything (num " ++ show num ++ ") (th " ++ show th ++ ")")
  else return ()
 
  c <- readIORef cmdList
  writeChan forCmdList c
 
-- does no MakeProgress messages only Delivers
-- until the runqueue is empty
envDeliverAll :: (MonadEnvironment m) =>
  Chan Int -> Int -> Chan [Either customCmd AsyncInput] -> 
  (Environment _f2p ((ClockP2F _p2f), CarryTokens Int)
    (SttCruptA2Z p2a2z (Either (ClockF2A lf2a) rf2a))
    ((SttCruptZ2A (ClockP2F z2a2p) (Either ClockA2F z2a2f)), CarryTokens Int) Void
    ClockZ2F (config, [Either customcmd AsyncInput], ts) m)
envDeliverAll clockChan t forCmdList _ _ (a2z, z2a) (f2z, z2f) pump _ = do
  cmdList <- newIORef [] 
 
  let checkQueue = do
          writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
          c <- readChan clockChan
          modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
          return (c > 0) 

  whileM_ checkQueue $ do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
    c <- readChan clockChan
    modifyIORef cmdList $ (++) [Right (CmdGetCount,0)]
    idx <- liftIO $ generate $ choose (0,c-1) 
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx)), SendTokens 0)
    () <- readChan pump 
    modifyIORef cmdList $ (++) [Right (CmdDeliver idx, 0)]
    return ()

  c <- readIORef cmdList
  writeChan forCmdList c
     
envExecAsyncCmd :: (MonadITM m) =>
  (Chan (PID, ((ClockP2F _z2p), CarryTokens Int) )) ->
  (Chan ((SttCruptZ2A (ClockP2F _p2f) (Either ClockA2F _a2f)), CarryTokens Int)) ->
  (Chan ClockZ2F) -> Chan Int -> Chan () -> (Either _protInput AsyncInput) -> 
  (Chan (PID, ((ClockP2F _z2p), CarryTokens Int)) -> 
   Chan ((SttCruptZ2A (ClockP2F _p2f) (Either ClockA2F _a2f)), CarryTokens Int) ->
   Chan () -> (Either _protInput AsyncInput) -> m ()) -> m ()
envExecAsyncCmd z2p z2a z2f clockChan pump cmd f = do
  case cmd of
    Right (CmdDeliver idx', st') -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens st')
        readChan pump
    Right (CmdGetCount, st') -> do     
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens st')
        readChan clockChan
        return ()
    Right (CmdMakeProgress, _) -> do
        writeChan z2f ClockZ2F_MakeProgress
        readChan pump
    Left _ -> do f z2p z2a pump cmd
  return ()

 
---- SID, Parties, Crupt, Custom tuple
--type EnvConfig a = (SID, [PID], CruptList, a)
--type ClockZ2A = (SttCruptZ2A (ClockP2F (SID, 
-- 
--performEnv
--  :: (MonadEnvironment m) => 
--  EnvConfig a -> [Either ProtInput AsyncInput] -> --[Either ACastInput AsyncInput] ->
--  --(Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
--    (Environment ProtF2P           ((ClockP2F ProtP2F),           CarryTokens Int)
--     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int)) 
--       (SttCruptA2Z FuncP2F 
--                  --(Either (ClockF2A (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
--                    (Either (ClockF2A (SID, ((LeakMsg, TransferTokens Int), CarryTokens Int)))
--                          --(SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
--                          (SID, (F2AMsg, TransferTokens Int))))
--     --((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int))) 
--     ((SttCruptZ2A (ClockP2F (SID, ((LeakMsg, TransferTokens Int), CarryTokens Int))) 
--                  --(Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
--                  (Either ClockA2F (SID, (A2FMsg, TransferTokens Int)))), CarryTokens Int) Void
--     (ClockZ2F) Transcript m)
--performACastEnv aCastConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
--    let (sid :: SID, parties :: [PID], crupt :: Map PID (), t :: Int, leader :: PID) = aCastConfig 
--    writeChan z2exec $ SttCrupt_SidCrupt sid crupt
--
--    transcript <- newIORef []
--    fork $ forever $ do
--      (pid, m) <- readChan p2z
--      modifyIORef transcript (++ [Right (pid, m)])
--      --printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
--      ?pass
--
--    clockChan <- newChan
--    fork $ forever $ do
--      mb <- readChan a2z
--      modifyIORef transcript (++ [Left mb])
--      case mb of
--        SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
--          printEnvReal $ "Pass"
--          ?pass
--        SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
--          writeChan clockChan c
--        SttCruptA2Z_P2A (pid, m) -> do
--          case m of
--            _ -> do
--              printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
--          ?pass
--        SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
--          p--printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
--          ?pass
--        SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
--          printEnvReal $ "Forced Clock advance"
--          ?pass
--        _ -> error $ "Help!" ++ show mb
--        
--    () <- readChan pump 
--  
--    -- TODO: need to do something about this
--    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
--    readChan clockChan
--    let n = length parties
--
--    forMseq_ cmdList $ \cmd -> do
--        case cmd of
--            Left (CmdVAL ssid' pid' m' dt', st') -> do
--                writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (ACast_VAL m'), DeliverTokensWithMessage dt'))), SendTokens st')
--                readChan pump
--            Left (CmdECHO ssid' pid' m' dt', st') -> do
--                writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (ACast_ECHO m'), DeliverTokensWithMessage dt'))), SendTokens st')
--                readChan pump
--            Left (CmdREADY ssid' pid' m' dt', st') -> do
--                writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (ACast_READY m'), DeliverTokensWithMessage dt'))), SendTokens st')
--                readChan pump
--            Right (CmdDeliver idx', st') -> do
--                writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens st')
--                readChan pump
--            Right (CmdGetCount, st') -> do     
--                writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens st')
--                readChan clockChan
--                return ()
--            Right (CmdMakeProgress, _) -> do
--                writeChan z2f ClockZ2F_MakeProgress
--                readChan pump
--    writeChan outp =<< readIORef transcript
--
