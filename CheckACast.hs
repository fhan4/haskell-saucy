 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
  #-} 

module CheckACast where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper
import ACast
import TestTools

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
--import TestTools (selectPIDs, AsyncCmd (..), rqDeliverList, rqDeliverOrProgress)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

{- a simple property environment that just chooses some random number of parties, 
   a random leader, they're all honest, and it runs the experiment -}
propIdealACastSafetyEnv
  :: MonadEnvironment m =>
  Environment (ACastF2P String) (ClockP2F (ACastP2F String)) (SttCruptA2Z a (Either (ClockF2A String) Void)) (SttCruptZ2A b (Either ClockA2F Void)) Void (ClockZ2F) String m
propIdealACastSafetyEnv z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)

  -- choose the parties and the leader  
  n <- liftIO $ (generate $ choose (4,100))
  let parties = fmap show [1..n]

  leader <- liftIO $ (generate $ choose (4,n)) >>= return . show
    
  let t :: Int = if ((n `div` 3) * 3) < n then (n `div` 3)
                 else (n `div` 3)-1
 
  let sid = ("sidtestacast", show (leader, parties, t, "")) 

  --let sid = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], 1::Integer, ""))
  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  fork $ forever $ do
    (pid, m) <- readChan p2z
    printEnvIdeal $ "[testEnvACastIdeal]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  -- Have Alice write a message
  () <- readChan pump 
  writeChan z2p (leader, ClockP2F_Through $ ACastP2F_Input ("I'm " ++ leader))

  -- Empty the queue
  let checkQueue = do
        writeChan z2a $ SttCruptZ2A_A2F (Left ClockA2F_GetCount)
        mb <- readChan a2z
        let SttCruptA2Z_F2A (Left (ClockF2A_Count c)) = mb
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do
    {- Two ways to make progress -}
    {- 1. Environment to Functionality - make progress -}
    -- writeChan z2f ClockZ2F_MakeProgress
    {- 2. Environment to Adversary - deliver the next message -}
    writeChan z2a $ SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))
    readChan pump

  writeChan outp "environment output: 1"

-- runs the above property environment
prop_dummySafety = monadicIO $ do
    t <- run $ runITMinIO 120 $ execUC propIdealACastSafetyEnv (idealProtocol) (runAsyncF $ fACast) dummyAdversary
    let x :: String = show t
    assert (1 == 1) 


data ACastCmd = CmdVAL SID PID String MulticastTokens | CmdECHO SID PID String MulticastTokens | CmdREADY SID PID String MulticastTokens | CmdHonestInput PID String  deriving (Eq, Show, Ord)
type ACastInput = (ACastCmd, Tokens)

-- SID, Parties, Crupt, t < n/3, leader
type ACastLeader = PID
type ACastConfig = (SID, [PID], CruptList , Int, ACastLeader)

performACastEnv 
  :: (MonadEnvironment m) => 
  ACastConfig -> [Either ACastInput AsyncInput] ->
  (Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) Transcript m)

performACastEnv aCastConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let (sid :: SID, parties :: [PID], crupt :: Map PID (), t :: Int, leader :: PID) = aCastConfig 
    writeChan z2exec $ SttCrupt_SidCrupt sid crupt

    debugLog <- newIORef []
    transcript <- newIORef []
    fork $ forever $ do
      (pid, m) <- readChan p2z
      modifyIORef debugLog $ (++ [Right (Right (pid, m))])
      modifyIORef transcript (++ [Right (pid, m)])
      --printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
      ?pass

    clockChan <- newChan
    fork $ forever $ do
      mb <- readChan a2z
      modifyIORef transcript (++ [Left mb])
      modifyIORef debugLog $ (++ [Right (Left mb)])
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
        SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
          --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
          ?pass
        SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
          printEnvReal $ "Forced Clock advance"
          ?pass
        _ -> error $ "Help!" ++ show mb
        
    () <- readChan pump 
  
    -- TODO: need to do something about this
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
    --modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 1000))])
    readChan clockChan
    let n = length parties

    forMseq_ cmdList $ \cmd -> do
        --envExecAsyncCmd z2p z2a z2f clockChan pump cmd envExecACastCmd  
        modifyIORef debugLog $ (++ [Left cmd])
        envExecAsyncCmd z2p z2a z2f clockChan pump cmd envExecACastCmd
    dl <- readIORef debugLog  
    liftIO $ putStrLn $ "\n\t[Real World dl]\n" ++ (show dl)
    liftIO $ putStrLn $ "\n\t[Real World cl]\n" ++ (show cmdList)
    writeChan outp =<< readIORef transcript


aCastGenerator :: Int -> Int -> [Gen SID] -> [PID] -> [Gen String] -> Int -> Gen [Either ACastInput AsyncInput]
aCastGenerator n numQueue ssids parties inputs dts = frequency $
  [ (1, return []), 
    (2, if n==0 then return []
         else if numQueue==0 then (aCastGenerator n 0 ssids parties inputs dts)
         --else if numQueue==0 then (:) <$> (return (Right (CmdMakeProgress, 0))) <*> (aCastGenerator (n-1) 0 ssids parties inputs) 
         else (:) <$> (choose (0,numQueue-1) >>= \i -> return (Right (CmdDeliver i, 0))) <*> (aCastGenerator (n-1) (numQueue-1) ssids parties inputs dts)),
    --(4, if n==0 then return [] else (:) <$> return (Right (CmdMakeProgress, 0)) <*> (aCastGenerator (n-1) numQueue ssids parties inputs dts)),
--    (3, if n==0 then return [] else (:) <$> ((shuffle parties) >>= (\pl -> oneof inputs >>= (\i -> return (Left (CmdHonestInput (pl !! 0) i, 0)) ) )) <*> (aCastGenerator (n-1) (numQueue-1) ssids parties inputs)),
    (2, if n==0 then return [] else (:) <$> 
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> oneof ssids >>=
              (\s -> return (Left (CmdVAL s (pl !! 0) i dts, 0)))))) <*> (aCastGenerator (n-1) numQueue ssids parties inputs dts)),
    (2, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> oneof ssids >>=
              (\s -> return (Left (CmdECHO s (pl !! 0) i 0, 0)))))) <*> (aCastGenerator (n-1) numQueue ssids parties inputs dts)),
    (2, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> oneof ssids >>=
              (\s -> return (Left (CmdREADY s (pl !! 0) i 0, 0)))))) <*> (aCastGenerator (n-1) numQueue ssids parties inputs dts)) 
  ]

envExecACastCmd :: (MonadITM m) =>
  (Chan (PID, ((ClockP2F (ACastP2F String)), CarryTokens Int))) ->
  (Chan ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int))) (Either _ (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int)) ->
  (Chan ()) -> (Either ACastInput _) -> m ()
envExecACastCmd z2p z2a pump cmd = do
  case cmd of
      Left (CmdVAL ssid' pid' m' dt', st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (ACast_VAL m'), DeliverTokensWithMessage dt'))), SendTokens st')
          readChan pump
      Left (CmdECHO ssid' pid' m' dt', st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (ACast_ECHO m'), DeliverTokensWithMessage dt'))), SendTokens st')
          readChan pump
      Left (CmdREADY ssid' pid' m' dt', st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (ACast_READY m'), DeliverTokensWithMessage dt'))), SendTokens st')
          readChan pump
      Left (CmdHonestInput pid' x, st') -> do
          writeChan z2p (pid', ((ClockP2F_Through $ ACastP2F_Input x), SendTokens st'))
          readChan pump
  return ()

propUEnvBrachaSafety
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (ACastConfig, [Either ACastInput AsyncInput], Transcript) m
propUEnvBrachaSafety z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave"]
  let leader = "Alice"
  let t = 1 :: Int
  let crupt = Map.fromList [("Alice",())] :: Map PID () 
  let sid = ("sidTestACast", show (leader, parties, t, ""))
  let n = length parties
 
  -- compute ssids
  let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))

  let ssids = do [return ssidAlice1, return ssidAlice2, return ssidAlice3]
 
  writeChan z2exec $ SttCrupt_SidCrupt sid crupt

  transcript <- newIORef []
  cmdList <- newIORef []
  --debugLog <- newIORef Map.empty
  debugLog <- newIORef []

  numDelivers <- newIORef 0
  
  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    modifyIORef debugLog $ (++ [Right (Right (pid, m))])
    ?pass

  clockChan <- newChan
  fork $ forever $ do
    mb <- readChan a2z
    modifyIORef transcript $ (++ [Left mb])
    modifyIORef debugLog $ (++ [Right (Left mb)])
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
      SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
        printEnvReal $ "Forced Clock advance"
        ?pass
      _ -> error $ "Help!" ++ show mb

  () <- readChan pump
  liftIO $ putStrLn $ "asking for count"
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan
 
  -- Select a set of parties and select one of 0 and 1 for each VAL message
  to_send_val <- selectPIDs parties
  
  let inputs = do [return "1", return "2"]
  
  someCounter <- newIORef 0 
 
  let checkQueue n = do
        liftIO $ putStrLn $ "\t\t\t\t\t\tgetting checkQueue"
        modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 0))])
        modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
        writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
        
        c <- readChan clockChan
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  let randomf x = do return ()

  firstInp <- newIORef []
  forMseq_ [1..10] $ \_ -> do
    -- generate at least 20 single inputs hoping something triggers the protocol
    inp <- liftIO $ generate $ aCastGenerator 1 0 ssids parties inputs (n*5)
    writeIORef firstInp inp 

    {- One case of the grammar is an empty list, keep trying till we get a real input -}
    whileM_ (readIORef firstInp >>= return . (/=) 1 . length) $ do
      inp <- liftIO $ generate $ aCastGenerator 1 0 ssids parties inputs (n*5)
      writeIORef firstInp inp
      return ()
     
    inp :: [Either ACastInput AsyncInput] <- readIORef firstInp 
    liftIO $ putStrLn $ "Input: " ++ show inp
    modifyIORef debugLog $ (++ [Left (inp !! 0)])
    modifyIORef cmdList $ (++ [(inp !! 0)])
    () <- envExecAsyncCmd z2p z2a z2f clockChan pump (inp !! 0) envExecACastCmd


    {- we hope something happens and there are protocol messgaes to make progress with -}
    sc <- readIORef someCounter
    whileM_ (checkQueue sc) $ do
      modifyIORef someCounter $ (+) 1
      sc <- readIORef someCounter
      modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
      modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 0))])
      writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
      c <- readChan clockChan
      
      inps <- liftIO $ generate $ aCastGenerator 20 c ssids parties inputs (n*5)
      forMseq_ inps $ \i -> do
        modifyIORef debugLog $ (++ [Left i])
        modifyIORef cmdList $ (++ [i])
        envExecAsyncCmd z2p z2a z2f clockChan pump i envExecACastCmd

  tr <- readIORef transcript
  cl <- readIORef cmdList
  
  dl <- readIORef debugLog
  liftIO $ putStrLn $ "\n\t[Ideal World dl]\n" ++ (show dl)
  liftIO $ putStrLn $ "\n\t[Ideal World cl]\n" ++ (show cl)

  writeChan outp ((sid, parties, crupt, t, leader), cl, tr)

  return ()

prop_uBrachaSafety = monadicIO $ do
    let variantT = ACastTSmall
    let variantR = ACastRSmall
    let variantD = ACastDSmall
    let prot () = protACastBroken variantT variantR variantD 
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      propUEnvBrachaSafety 
      idealProtocolToken 
      (runAsyncF fACastToken) 
      (runTokenA $ simACastBroken $ prot ())
    t <- run $ runITMinIO 120 $ execUC 
      (performACastEnv config' c') 
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    let x :: String = show t
    -- require that all deliverances are the same
    outputs <- newIORef Set.empty
    forMseq_ [0..(length t)-1] $ \i -> do
        case (t !! i) of 
            Right (pid, ACastF2P_Deliver m) -> do
                printYellow (show (t !! i))
                modifyIORef outputs $ Set.insert m
            Left m -> return ()
    o <- readIORef outputs

    --printYellow ("[Config]\n\n" ++ show config')
    --printYellow ("[Inputs]\n\n" ++ show c')
    printYellow ("[ ideal world ] \n" ++ show t')
    printYellow ("[ real world ] \n" ++ show t)
    assert ( (Set.size o) <= 1 )
    assert (t' == t)
       
propEnvBrachaSafety
  :: (MonadEnvironment m) =>
  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (ACastConfig, [Either ACastInput AsyncInput], Transcript) m
propEnvBrachaSafety z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave"]
  let leader = "Alice"
  let t = 1 :: Int
  let crupt = Map.fromList [("Alice",())] :: Map PID () 
  let sid = ("sidTestACast", show (leader, parties, t, ""))

  -- compute ssids
  let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))
  
  writeChan z2exec $ SttCrupt_SidCrupt sid crupt

  transcript <- newIORef []
  cmdList <- newIORef []

  numDelivers <- newIORef 0
  
  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    --printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
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
      SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
        --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
        printEnvReal $ "Forced Clock advance"
        ?pass
      _ -> error $ "Help!" ++ show mb

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan
  --modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]

  -- Select a set of parties and select one of 0 and 1 for each VAL message
  to_send_val <- selectPIDs parties
  printYellow ("\nParties: " ++ show to_send_val ++ "\n")

  let n = length parties
  let n' = length to_send_val

  -- send VAL to each of the with one of [0,1] as the value
  forMseq_ [0..(length to_send_val)-1] $ \i -> do
    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice1, (MulticastA2F_Deliver (to_send_val !! i) (ACast_VAL this_val), DeliverTokensWithMessage (n*5)))), SendTokens 0)
    modifyIORef cmdList $ (++) [Left (CmdVAL ssidAlice1 (to_send_val !! i) this_val (n*5), 0)]
    () <- readChan pump
    return ()

  -- deliver / make progress  
  getCmdChan <- newChan  
  () <- envDeliverOrProgressSubset clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  -- do the same with ECHO
  to_send_echo <- selectPIDs parties 
  printYellow ("\nParties: " ++ show to_send_echo ++ "\n")
  
  -- send VAL to each of the with one of [0,1] as the value
  forMseq_ [0..(length to_send_echo)-1] $ \i -> do
    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice2, (MulticastA2F_Deliver (to_send_echo !! i) (ACast_ECHO this_val), DeliverTokensWithMessage 0))), SendTokens 0)
    modifyIORef cmdList $ (++) [Left (CmdECHO ssidAlice2 (to_send_echo !! i) this_val 0, 0)]
    () <- readChan pump
    return ()

  -- deliver / make progress
  getCmdChan <- newChan  
  () <- envDeliverOrProgressSubset clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList
  
  -- do the same with READY
  to_send_ready <- selectPIDs parties 
  printYellow ("\nParties: " ++ show to_send_ready ++ "\n")
  
  -- send VAL to each of the with one of [0,1] as the value
  forMseq_ [0..(length to_send_ready)-1] $ \i -> do
    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice3, (MulticastA2F_Deliver (to_send_ready !! i) (ACast_READY this_val), DeliverTokensWithMessage 0))), SendTokens 0)
    modifyIORef cmdList $ (++) [Left (CmdREADY ssidAlice3 (to_send_ready !! i) this_val 0, 0)]
    () <- readChan pump
    return ()
  
  -- deliver / make progress
  getCmdChan <- newChan  
  () <- envDeliverOrProgressSubset clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  tr <- readIORef transcript
  cl <- readIORef cmdList
  --writeChan outp =<< readIORef transcript
  writeChan outp ((sid, parties, crupt, t, leader), reverse cl, tr)

{- 		
		[ PROPERTY ]
-}
prop_brachaSafety = monadicIO $ do
    let variantT = ACastTSmall
    let variantR = ACastRSmall
    let variantD = ACastDSmall
    let prot () = protACastBroken variantT variantR variantD 
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      propEnvBrachaSafety 
      idealProtocolToken 
      (runAsyncF fACastToken) 
      (runTokenA $ simACastBroken $ prot ())
    t <- run $ runITMinIO 120 $ execUC 
      (performACastEnv config' c') 
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    let x :: String = show t
    -- require that all deliverances are the same
    outputs <- newIORef Set.empty
    forMseq_ [0..(length t)-1] $ \i -> do
        case (t !! i) of 
            Right (pid, ACastF2P_Deliver m) -> 
                modifyIORef outputs $ Set.insert m
            Left m -> return ()
    o <- readIORef outputs

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')
    assert ( (Set.size o) <= 1 )
    assert (t == t')

{- 		
		[ PROPERTY ]
-}
prop_compareSafetyStructure = monadicIO $ do 
    let variantT = ACastTSmall
    let variantR = ACastRSmall
    let variantD = ACastDSmall
    let prot () = protACastBroken variantT variantR variantD 
    (configU', cU', tU') <- run $ runITMinIO 120 $ execUC 
      propUEnvBrachaSafety 
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    -- require that all deliverances are the same
    numOutputs <- newIORef 0
    forMseq_ [0..(length tU')-1] $ \i -> do
        case (tU' !! i) of 
            Right (pid, ACastF2P_Deliver m) -> do
                printYellow (show (tU' !! i))
                modifyIORef numOutputs $ (+) 1
            Left m -> return ()
    no <- readIORef numOutputs
    monitor (collect ("Unstructured", no))

    (configS', cS', tS') <- run $ runITMinIO 120 $ execUC 
      propEnvBrachaSafety 
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    -- require that all deliverances are the same
    numOutputs <- newIORef 0
    forMseq_ [0..(length tS')-1] $ \i -> do
        case (tS' !! i) of 
            Right (pid, ACastF2P_Deliver m) -> do
                printYellow (show (tS' !! i))
                modifyIORef numOutputs $ (+) 1
            Left m -> return ()
    no <- readIORef numOutputs
    monitor (collect ("Structured", no))

-- same as safety environment except all messages are delievered
-- in the right logical round         
--propEnvBrachaLiveness
--  :: (MonadEnvironment m) =>
--  Environment (ACastF2P String) ((ClockP2F (ACastP2F String)), CarryTokens Int)
--     (SttCruptA2Z (SID, (MulticastF2P (ACastMsg String), TransferTokens Int)) 
--                  (Either (ClockF2A (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int)))
--                          (SID, (MulticastF2A (ACastMsg String), TransferTokens Int))))
--     ((SttCruptZ2A (ClockP2F (SID, ((ACastMsg String, TransferTokens Int), CarryTokens Int))) 
--                  (Either ClockA2F (SID, (MulticastA2F (ACastMsg String), TransferTokens Int)))), CarryTokens Int) Void
--     (ClockZ2F) (ACastConfig, [Either ACastCmd AsyncCmd], Transcript) m
--propEnvBrachaLiveness z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
--  let extendRight conf = show ("", conf)
--  
--  let parties = ["Alice", "Bob", "Carol", "Dave"]
--  let honest = ["Bob", "Carol", "Dave"]
--  let leader = "Alice"
--  let t = 1 :: Int
--  let crupt = Map.fromList [("Alice",())] :: Map PID () 
--  let sid = ("sidTestACast", show (leader, parties, t, ""))
--
--  -- compute ssids
--  let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
--  let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
--  let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))
--  
--  writeChan z2exec $ SttCrupt_SidCrupt sid crupt
--
--  transcript <- newIORef []
--  cmdList <- newIORef []
--
--  numDelivers <- newIORef 0
--  
--  fork $ forever $ do
--    (pid, m) <- readChan p2z
--    modifyIORef transcript (++ [Right (pid, m)])
--    --printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
--    ?pass
--
--  clockChan <- newChan
--  fork $ forever $ do
--    mb <- readChan a2z
--    modifyIORef transcript (++ [Left mb])
--    case mb of
--      SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
--        printEnvReal $ "Pass"
--        ?pass
--      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
--        writeChan clockChan c
--      SttCruptA2Z_P2A (pid, m) -> do
--        case m of
--          _ -> do
--            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
--        ?pass
--      SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
--        --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
--        ?pass
--      SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
--        printEnvReal $ "Forced Clock advance"
--        ?pass
--      _ -> error $ "Help!" ++ show mb
--
--  --forMseq_ [1..24] $ \x -> do
--  --  () <- readChan pump
--  --  writeChan z2a SttCruptZ2A_TokenSend
--  () <- readChan pump
--  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
--
--  --() <- readChan pump
--  c <- readChan clockChan
--  -- Select a set of parties and select one of 0 and 1 for each VAL message
--  --to_send_val <- selectPIDs parties
--  --printYellow ("\nParties: " ++ show to_send_val ++ "\n")
--
--  --let n = length parties
--  --let n' = length to_send_val
--  sp_val <- shuffleParties honest
--  forMseq_ sp_val $ \p -> do
--    this_val <- liftIO $ (generate 
--
--  -- send VAL to each of the with one of [0,1] as the value
--  forMseq_ [0..(length to_send_val)-1] $ \i -> do
--    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
--    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice1, (MulticastA2F_Deliver (to_send_val !! i) (ACast_VAL this_val), DeliverTokensWithMessage (n*5)))), SendTokens 0)
--    modifyIORef cmdList $ (++) [Left $ CmdVAL ssidAlice1 (to_send_val !! i) this_val]
--    () <- readChan pump
--    return ()
--
--  -- get the number of things in the runqueue
--  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 10)
--  num <- readChan clockChan
--  delivers <- liftIO $ generate $ rqDeliverOrProgress num
--  --idxToDeliver <- liftIO $ generate $ rqIndexList num  
--  modifyIORef cmdList $ (++) [Right CmdGetCount]
--
--
--  -- deliver the indices
--  --forMseq_ [0..(length idxToDeliver)-1] $ \i -> do
--  forMseq_ delivers $ \d -> do
--    case d of 
--      CmdDeliver idx' -> do
--        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 10)
--        c <- readChan clockChan
--        if idx' < c then do 
--          modifyIORef cmdList $ (++) [Right d]
--          writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
--        else return ()
--      CmdMakeProgress -> do 
--        modifyIORef cmdList $ (++) [Right d]
--        writeChan z2f ClockZ2F_MakeProgress
--      _ -> error "Z: unexpected command"
--    --writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver (idxToDeliver !! i))), SendTokens 0)
--    () <- readChan pump
--    --modifyIORef cmdList $ (++) [Left $ CmdDeliver (idxToDeliver !! i)]
--    modifyIORef numDelivers $ (+) 1 
--    readIORef numDelivers >>= (\n -> printYellow ("numDelivers: " ++ show n))
--    return ()
--
--  -- do the same with ECHO
--  to_send_echo <- selectPIDs parties 
--  printYellow ("\nParties: " ++ show to_send_echo ++ "\n")
--  
--  -- send VAL to each of the with one of [0,1] as the value
--  forMseq_ [0..(length to_send_echo)-1] $ \i -> do
--    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
--    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice2, (MulticastA2F_Deliver (to_send_echo !! i) (ACast_ECHO this_val), DeliverTokensWithMessage 0))), SendTokens 0)
--    modifyIORef cmdList $ (++) [Left $ CmdECHO ssidAlice2 (to_send_echo !! i) this_val]
--    () <- readChan pump
--    return ()
--
--  -- get the number of things in the runqueue
--  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 10)
--  num <- readChan clockChan
--  delivers <- liftIO $ generate $ rqDeliverOrProgress num
--  --idxToDeliver <- liftIO $ generate $ rqIndexList num
--  modifyIORef cmdList $ (++) [Right $ CmdGetCount]
--
--  -- deliver the indices
--  --forMseq_ [0..(length idxToDeliver)-1] $ \i -> do
--  forMseq_ delivers $ \d -> do
--    case d of 
--      CmdDeliver idx' -> do
--        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 10)
--        c <- readChan clockChan
--        if idx' < c then do
--          modifyIORef cmdList $ (++) [Right $ d]
--          writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
--        else return ()
--      CmdMakeProgress -> do
--        writeChan z2f ClockZ2F_MakeProgress
--        modifyIORef cmdList $ (++) [Right $ d]
--      _ -> error "Z: unexpected command"
--    --writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver (idxToDeliver !! i))), SendTokens 0)
--    () <- readChan pump
--    --modifyIORef cmdList $ (++) [Right $ CmdDeliver (idxToDeliver !! i)]
--    modifyIORef numDelivers $ (+) 1 
--    readIORef numDelivers >>= (\n -> printYellow ("numDelivers: " ++ show n))
--    return ()
--  
--  -- do the same with READY
--  to_send_ready <- selectPIDs parties 
--  printYellow ("\nParties: " ++ show to_send_ready ++ "\n")
--  
--  -- send VAL to each of the with one of [0,1] as the value
--  forMseq_ [0..(length to_send_ready)-1] $ \i -> do
--    this_val <- liftIO $ (generate $ choose (0 :: Int, 1 :: Int)) >>= return . show 
--    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssidAlice3, (MulticastA2F_Deliver (to_send_ready !! i) (ACast_READY this_val), DeliverTokensWithMessage 0))), SendTokens 0)
--    modifyIORef cmdList $ (++) [Left $ CmdREADY ssidAlice3 (to_send_ready !! i) this_val]
--    () <- readChan pump
--    return ()
--
--  -- get the number of things in the runqueue
--  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 10)
--  num <- readChan clockChan
--  delivers <- liftIO $ generate $ rqDeliverOrProgress num
--  --idxToDeliver <- liftIO $ generate $ rqIndexList num  
--  modifyIORef cmdList $ (++) [Right CmdGetCount]
--
--  -- deliver the indices
--  --forMseq_ [0..(length idxToDeliver)-1] $ \i -> do
--  forMseq_ delivers $ \d -> do
--    case d of 
--      CmdDeliver idx' -> do
--        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 10)
--        c <- readChan clockChan
--        if idx' < c then do
--          modifyIORef cmdList $ (++) [Right d]
--          writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
--        else return ()
--      CmdMakeProgress -> do
--          modifyIORef cmdList $ (++) [Right d]
--          writeChan z2f ClockZ2F_MakeProgress
--      _ -> error "Z: unexpected command"
--    --writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver (idxToDeliver !! i))), SendTokens 0)
--    () <- readChan pump
--    --modifyIORef cmdList $ (++) [Right $ CmdDeliver (idxToDeliver !! i)]
--    modifyIORef numDelivers $ (+) 1 
--    readIORef numDelivers >>= (\n -> printYellow ("numDelivers: " ++ show n))
--    return ()
--
--  tr <- readIORef transcript
--  cl <- readIORef cmdList
--  --writeChan outp =<< readIORef transcript
--  writeChan outp ((sid, parties, crupt, t, leader), reverse cl, tr)
--
