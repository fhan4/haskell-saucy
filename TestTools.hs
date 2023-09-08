{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE Rank2Types #-} 

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

-- alias the types frequently used for readability
type CruptList = Map PID ()
type Tokens = Int
type MulticastTokens = Int

-- shuffle a list of PIDs
shuffleParties :: (MonadIO mio, Monad m2) => [PID] -> m2 (mio [PID])
shuffleParties pids = do return (liftIO $ (generate $ shuffle pids))

-- select a random subset of PIDs 
selectPIDs :: (MonadIO m) => [PID] -> m [PID]
selectPIDs pids = do
    s_pids <- liftIO $ (generate $ shuffle pids)
    n <- liftIO $ (generate $ choose (1, length pids))
    let r_pids :: [PID] = take n s_pids
    return r_pids

-- random mod t number
smallOffset :: Int -> Gen Int
smallOffset t = fmap ((`mod` t) . abs) arbitrary

-- generate a list of parties of length between x and y
partiesBetween :: Int -> Int -> Gen [PID]
partiesBetween x y = do
  d <- smallOffset (y-x+1)
  vector (x+d) :: Gen [PID]

-- does the list of parties contain empty PIDs?
nonZeroParties :: [PID] -> Bool
nonZeroParties [] = True
nonZeroParties (x:xs) = case x of
                          "" -> False
                          _ -> nonZeroParties xs

-- does the list of parties contain duplicates?
noRepeatParties :: [PID] -> Bool
noRepeatParties ps = length ps /= length set
  where set = Set.fromList ps

-- is the list of parties non-trivial (no "" and no duplicates)
nonTrivialParties :: [PID] -> Bool
nonTrivialParties ps = (nonZeroParties ps) && (noRepeatParties ps)

-- select at most `t` parties to corrupt from `ps`
cruptFrom :: [PID] -> Int -> Gen [PID]
cruptFrom ps t = do
  i <- choose (0, t)
  shuffle ps >>= sublistOf . take i

--multicastSid :: (MonadIO m) => String -> PID -> [PID] -> String -> m SID
multicastSid sssid snd ps s = (sssid, show (snd, ps, s))

data AsyncCmd = CmdDeliver Int | CmdMakeProgress | CmdGetCount deriving (Eq, Show, Ord)

type AsyncInput = (AsyncCmd, Tokens)

{- Generate a list of indices for run queue deliver requests.
   The output list indices can all always be execued if `n` is set correctly -}
rqIndexListWeights f n = [ (1, return []), (5, if n==0 then return [] else (:) <$> choose (0,n-1) <*> (f (n-1))) ]

rqIndexList :: Int -> Gen [Int]
rqIndexList n = frequency $ (rqIndexListWeights rqIndexList n)

-- gen a list of deliver commands with indicies for a lst of size `n` 
rqDeliverList :: Int -> Gen [AsyncCmd]
rqDeliverList n = frequency
    [ (1, return []),
      (25, if n==0 then return [] else (:) <$> (choose (0,n-1) >>= return . CmdDeliver) <*> (rqDeliverList (n-1)))
    ]

-- generate indices to execute based on a frequence parameter `f`
rqDeliverChoice :: Int -> Int -> Gen [AsyncCmd]
rqDeliverChoice n f = frequency
    [ (1, return []),
      (f, if n==0 then return [] else (:) <$> (choose (0,n-1) >>= return . CmdDeliver) <*> (rqDeliverChoice (n-1) f))
    ]

-- gen deliver commands for the whole list of size `n` in some random order
rqDeliverAll :: Int -> Gen [AsyncCmd]
rqDeliverAll n = oneof 
  [ if n == 0 then return [] else (:) <$> (choose (0,n-1) >>= return . CmdDeliver) <*> (rqDeliverAll (n-1)) ]

-- gen deliver or make progress commands for a list of sized `n`
rqDeliverOrProgress :: Int -> Gen [AsyncCmd]
rqDeliverOrProgress n = frequency
    [ (1, return []),
      (5, if n==0 then return [] else (:) <$> (choose (0,n-1) >>= return . CmdDeliver) <*> (rqDeliverList (n-1))),
      (10, if n==0 then return [] else (:) <$> return CmdMakeProgress <*> (rqDeliverOrProgress (n-1)))
    ]

-- shift down all indices higher than `ref` 
updateIndex :: Int -> [Int] -> [Int]
updateIndex ref [] = []
updateIndex ref (x:xs) = [if x > ref then (x-1) else x] ++ (updateIndex ref xs)

-- given an set of indices to censor, generate a deliver list 		
rqDeliverWithCensor :: [Int] -> Int -> Gen [AsyncCmd]
rqDeliverWithCensor censoredIdxs n = frequency 
	[ (1, return []),
		(10, if n==0 then return [] else (choose (0,n-1) >>= \i -> if (elem i censoredIdxs) then (rqDeliverWithCensor censoredIdxs n) else (:) <$> return (CmdDeliver i) <*> (rqDeliverWithCensor (updateIndex i censoredIdxs) (n-1))))
	]

-- takes a list of indices to deliver
-- returns a list of deliver commands wit indices
-- adjusted with delivers
deliverListAll :: [Int] -> [AsyncCmd]
deliverListAll [] = []
deliverListAll (x:xs) = [CmdDeliver x] ++ deliverListAll (updateIndex x xs)

countPOutputs :: [Either _ a] -> a -> IO Int
countPOutputs transcript output = do
  num <- newIORef 0
  forMseq_ transcript $ \out -> do
    case out of
      Right output -> modifyIORef num $ (+) 1
      _ -> return ()
  n <- readIORef num
  return n

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

envReadOut :: (MonadEnvironment m, Show p2z) => Chan (PID, p2z) -> 
  Chan (SttCruptA2Z f2p (Either (ClockF2A leak) f2a)) ->
  m (IORef (Maybe (Either (SttCruptA2Z f2p (Either (ClockF2A leak) f2a)) (PID, p2z))),
  IORef [Either (SttCruptA2Z f2p (Either (ClockF2A leak) f2a)) (PID, p2z)], 
  Chan Int)
envReadOut _p2z _a2z = do
  clockChan <- newChan
  lastOut <- newIORef Nothing
  transcript <- newIORef []
  fork $ forever $ do
    (pid, m) <- readChan _p2z 
    liftIO $ putStrLn $ "\ESC[31mParty [" ++ show pid ++ "]: " ++ show m ++ "\ESC[0m"
    modifyIORef transcript $ (++ [Right (pid, m)])
    writeIORef lastOut (Just (Right (pid, m)))
    ?pass
  fork $ forever $ do
    m <- readChan _a2z
    modifyIORef transcript $ (++ [Left m])
    case m of
      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) -> writeChan clockChan c
      _ -> do 
        writeIORef lastOut (Just (Left m))
        ?pass
  return (lastOut, transcript, clockChan) 

envQueueSize :: (MonadEnvironment m) =>
  (Chan ((SttCruptZ2A (ClockP2F _p2f) (Either ClockA2F _a2f)), CarryTokens Int)) ->
  Chan Int -> Int -> m Int
envQueueSize z2a clockChan tk = do
  writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
  readChan clockChan

envCheckQueue :: (MonadEnvironment m) => 
  (Chan ((SttCruptZ2A (ClockP2F _p2f) (Either ClockA2F _a2f)), CarryTokens Int)) ->
  Chan Int -> Int -> m Bool 
envCheckQueue z2a clockChan tk = do
  envQueueSize z2a clockChan tk >>= (\c -> return (c>0))

invert :: (a,b) -> (b,a)
invert (a,b) = (b,a)

envMapQueue :: (MonadEnvironment m) =>
  (Chan ((SttCruptZ2A (ClockP2F _p2f) (Either ClockA2F _a2f)), CarryTokens Int)) ->
  (Chan (SttCruptA2Z _f2p (Either (ClockF2A (SID, ((_leak, TransferTokens Int), CarryTokens Int))) _f2a))) -> Chan Int -> 
  IORef (Maybe (Either (SttCruptA2Z f2p (Either (ClockF2A (SID, ((_leak, TransferTokens Int), CarryTokens Int))) f2a)) (PID, p2z))) ->
  Chan () ->
    m ( ([(PID,PID)] -> AsyncCmd -> m ()), ([(PID,PID)] -> m ()) )
envMapQueue z2a a2z clockChan lastOut pump = do
  ctr <- newIORef 0
  sendPairs <- newIORef []

  let handleLeak (sid :: SID, ((m, (DeliverTokensWithMessage st)), SendTokens a)) = do
                       liftIO $ putStrLn $ "Leak handler" 
                       let (pidS :: PID, parties :: [PID], sssid :: String) = readNote "fMulticast" $ snd sid
                       forMseq_ parties $ \p -> do 
                         modifyIORef sendPairs $ (++ [(pidS, p)])    
  
  --let invert (a,b) = (b,a)
    
  let deliverIdx idx st censorList = do
                       -- first get the leas
                       writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetLeaks), SendTokens 0)
                       () <- readChan pump
                       mf <- readIORef lastOut
                       let Just (Left (SttCruptA2Z_F2A (Left (ClockF2A_Leaks leaks)))) = mf
                       t <- readIORef ctr
                       let tail = drop t leaks
                       modifyIORef ctr (+ length tail)
                       forMseq_ tail handleLeak
                       
                       -- what is this idx
                       toFrom <- (readIORef sendPairs >>= return . (!! idx))
                       --liftIO $ putStrLn $ "Delivering a msg between: " ++ show toFrom
                       --liftIO $ putStrLn $ "Censor pair: " ++ show censorList
                       --liftIO $ putStrLn $ "and: " ++ show (map invert censorList)
                       if (elem toFrom censorList) || (elem (invert toFrom) censorList) then do
                         liftIO $ putStrLn $ "\n\t" ++ show toFrom ++ " is in censorList\n"
                         writeChan pump ()
                       else do 
                         modifyIORef sendPairs (deleteNth idx)
                         writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx)), SendTokens st)
  let doDeliver censorList cmd = do
               case cmd of 
                 (CmdDeliver idx') -> do
                     () <- deliverIdx idx' 0 censorList
                     readChan pump
                 _ -> error "should only be doing delivers" 
               return ()

  let deliverByPairs (ps :: [(PID,PID)])  = do
              let ips = map invert ps
              sp <- readIORef sendPairs
              let idxToDeliver = map fst $ filter (\(_,x) -> (elem x ps) || (elem x ips)) $ zip [0..] sp
              let deliveries = deliverListAll $ idxToDeliver
              forMseq_ deliveries $ (doDeliver [])
              return ()

  return (doDeliver, deliverByPairs)

censoredIdxs :: (Eq a) => [(a,a)] -> [(Int, (a,a))] -> [Int]
censoredIdxs cL [] = []
censoredIdxs cL (x:xs) = if (elem (snd x) cL) || (elem (invert (snd x)) cL) then [fst x] ++ (censoredIdxs cL xs) else (censoredIdxs cL xs)

-- does no MakeProgress messages only Delivers
-- until the runqueue is empty
-- WARNING: this doesn' work for protocols like BenOr where parties
-- don't halt once they've decided
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
  (Chan ClockZ2F) -> Chan Int -> Chan () -> AsyncInput -> m () -- (Either _protInput AsyncInput) -> m ()
envExecAsyncCmd z2p z2a z2f clockChan pump cmd = do
  case cmd of
    (CmdDeliver idx', st') -> do
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens st')
        readChan pump
    (CmdGetCount, st') -> do     
        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens st')
        readChan clockChan
        return ()
    (CmdMakeProgress, _) -> do
        writeChan z2f ClockZ2F_MakeProgress
        readChan pump
  return ()


envExecCmd :: (MonadITM m) =>
  (Chan (PID, ((ClockP2F _z2p), CarryTokens Int) )) ->
  (Chan ((SttCruptZ2A (ClockP2F _p2f) (Either ClockA2F _a2f)), CarryTokens Int)) ->
  (Chan ClockZ2F) -> Chan Int -> Chan () -> (Either _protInput AsyncInput) -> 
  (Chan (PID, ((ClockP2F _z2p), CarryTokens Int)) -> 
   Chan ((SttCruptZ2A (ClockP2F _p2f) (Either ClockA2F _a2f)), CarryTokens Int) ->
   Chan () -> _protInput ->
   m ()) -> m ()
envExecCmd z2p z2a z2f clockChan pump cmd f = do
  let asyncExec = envExecAsyncCmd z2p z2a z2f clockChan pump
  let protExec = f z2p z2a pump
  case cmd of
    Right x -> asyncExec x
    Left x -> protExec x
  return ()

--testEnvironment :: MonadEnvironment m => Chan SttCrupt_SidCrupt ->  
--  (Chan (PID, p2z), Chan (PID, ((ClockP2F z2p), CarryTokens Int))) -> 
--  (Chan (SttCruptA2Z a2z (Either (ClockF2A leakmsg) f2a)), Chan ((SttCruptZ2A (ClockP2F z2a) (Either ClockA2F a2f)), CarryTokens Int)) -> (Chan Void, Chan ClockZ2F) -> Chan () -> Chan outz ->
--  (Environment p2z (ClockP2F z2p, CarryTokens Int)
--    (SttCruptA2Z a2z (Either (ClockF2A leakmsg) f2a)) 
--    ((SttCruptZ2A (ClockP2F z2a) (Either ClockA2F a2f)), CarryTokens Int) Void ClockZ2F outz m) -> 
--  m ()
--testEnvironment sidcrupt (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp z = do
--  z sidcrupt (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp

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
