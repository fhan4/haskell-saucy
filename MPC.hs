{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds, PartialTypeSignatures
  #-} 

module MPC where

import Control.Concurrent.MonadIO
import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map
import Control.Monad (forever,foldM)

import Data.Poly
import Data.Field.Galois (Prime, toP)
import Data.Vector (Vector,forM,fromList)
import qualified Data.Vector ((++))

import ProcessIO
import StaticCorruptions
import OptionallyLeak (MonadOptionally, runOptionally, optionally)
import Polynomial
import Safe

data Void


{--
 We model an MPC protocol as a service that keeps track of a table of
 secret data, but computes a given sequence of operations on this data.

 This is the "Arithmetic Black Box", or `fABB`.

 We have to ensure that all the MPC parties agree on the opcode sequence to run.
 To do this in a flexible way, we let the adversary adaptively choose the
  opcode sequence, but the sequence becomes common knowledge to the honest
  parties so they can follow along.

 Inputs are similarly provided by the adversary.

 The operations available in the fABB service are
  INPUT, LIN, MULT, OPEN.

 - INPUT provides a secret input
 - OPEN discloses a secret value
 - LIN defines a linear combination over existing secret values
 - MULT we'll mention in a moment

 The type of share IDs is Sh.


 Our main functionality `fMPC` keeps track of not just the secret data,
  but also the entire secret sharing polynomial.

 Since our MPC model is designed to demonstrate the compositional style of UC,


 The final application `fCircMPC` evaluates an entire arithmetic circuit and
  abstracts away the secret sharing polynomials.

 To summarize, our construction plan is:
   fMPC_sansMult  ---Beaver---> fMPC ---Adaptor---> fABB

 --}

mpcCircuitTest :: MonadMPCProgram m sh => m Fq
mpcCircuitTest = do
  alice <- input
  bob <- input
  carol <- input

  ab <- mult alice bob
  abc <- mult ab carol

  result <- openShare abc
  return result

openShare sh = do
  mp <- ?op $ OPEN sh
  let FmpcRes_Fq x = mp
  return x

input :: MonadMPCProgram m sh => m sh
input = do
  mp <- ?op INPUT
  let FmpcRes_Sh x = mp
  return x

mult x y = do
  mp <- ?op $ MULT x y
  let FmpcRes_Sh xy = mp
  return xy

data TestAbbZ2P = TestAbbZ2P_Inputs (Fq,Fq,Fq)
                | TestAbbZ2P_Log 

data TestAbbP2Z sh = TestAbbP2Z_Product Fq
                   | TestAbbP2Z_Log [(FmpcOp sh,FmpcRes sh)]

runAbbTestProg :: MonadProtocol m =>
    (forall sh. MonadMPCProgram m sh => m Fq) ->
    Protocol TestAbbZ2P (TestAbbP2Z sh) (FmpcF2P sh) (FmpcP2F sh) m
runAbbTestProg mpcProg (z2p,p2z) (f2p,p2f) = do
   let _op opcode = do
         writeChan p2f $ FmpcP2F_Op opcode
         res <- readChan f2p
         let (FmpcF2P_Op r) = res
         return r

   if ?pid == "InputParty" then do
     mz <- readChan z2p
     let TestAbbZ2P_Inputs (a,b,c) = mz
     writeChan p2f $ FmpcP2F_Input a
     mp <- readChan f2p; let FmpcF2P_Ok = mp
     writeChan p2f $ FmpcP2F_Input b
     mp <- readChan f2p; let FmpcF2P_Ok = mp
     writeChan p2f $ FmpcP2F_Input c
     mp <- readChan f2p; let FmpcF2P_Ok = mp

     x <- let ?op = _op in mpcProg
     writeChan p2z $ TestAbbP2Z_Product x

   else do
    fork $ forever $ do
     mz <- readChan z2p; let TestAbbZ2P_Log = mz
     writeChan p2f $ FmpcP2F_Log
     mp <- readChan f2p; let FmpcF2P_Log log = mp
     writeChan p2z $ TestAbbP2Z_Log log
    return ()
      
   return ()

type Sh = Int

fABB :: MonadFunctionality m => Functionality (FmpcP2F Sh) (FmpcF2P Sh) Void Void Void Void m
fABB = let ?n = 0; ?t = 0 in -- these are unused
         fMPC_ False True

-- Stunning.... the Sh type is parametric in the Z2P/P2Z channels, but Concrete from the viewpoint of the adversary

envTestAbb :: MonadEnvironment m =>
  Environment (TestAbbP2Z sh) (TestAbbZ2P) (SttCruptA2Z (FmpcF2P Sh) Void) (SttCruptZ2A (FmpcP2F Sh) Void) Void Void String m
envTestAbb z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
   -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("mpc","") (Map.fromList [("Observer",())])
  
  fork $ forever $ do
    (pid,x) <- readChan p2z
    case x of
      TestAbbP2Z_Product fq | pid == "InputParty" -> do
        -- Append result
        liftIO $ putStrLn $ "Z:[" ++ pid ++ "] sent Fq " ++ show fq
      TestAbbP2Z_Log log -> do
        liftIO $ putStrLn $ "Z:[" ++ pid ++ "] sent Log"
    ?pass

  -- Listen to log from dummy adversary
  fork $ forever $ do
    mf <- readChan a2z
    case mf of
      SttCruptA2Z_P2A (pid, FmpcF2P_Log log) | pid == "Observer" -> do
           liftIO $ putStrLn $ "Z: Observer receive Log: " ++ show log
           ?pass

  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2p ("InputParty", TestAbbZ2P_Inputs (2,3,4))

  () <- readChan pump; liftIO $ putStrLn "pump"
  writeChan z2a $ SttCruptZ2A_A2P ("Observer", FmpcP2F_Log)

  () <- readChan pump
  writeChan outp "environment output: 1"

testMpc0 = runITMinIO 120 $ execUC envTestAbb (runAbbTestProg mpcCircuitTest) (fABB) dummyAdversary

-- Here are the data definitions
data FmpcOp sh = INPUT
               | OPEN sh
               | LIN [(Fq,sh)]
               | CONST Fq
               | MULT sh sh
               | RAND deriving (Eq, Show)

data FmpcRes sh = FmpcRes_Ok
                | FmpcRes_Fq Fq
                | FmpcRes_Sh sh
                | FmpcRes_Trip (sh,sh,sh) deriving Show

type MonadMPCProgram m sh = (Monad m,
                             ?op :: FmpcOp sh -> m (FmpcRes sh))


data FmpcP2F sh = FmpcP2F_Op (FmpcOp sh)
                | FmpcP2F_Log
                | FmpcP2F_Input Fq
                | FmpcP2F_MyShare sh

data FmpcF2P sh = FmpcF2P_Op (FmpcRes sh)
                | FmpcF2P_Log [(FmpcOp sh,FmpcRes sh)]
                | FmpcF2P_Ok
                | FmpcF2P_MyShare Fq
  

{----
 Interacting with the MPC Arithmetic BlackBox functionality

 It's essential in every MPC protocol that the honest parties agree on which sequence of operations to run. For maximum flexibility, we can allow these to be chosen by the adversary, but allow honest parties to match with them.

 `fABB`
   Keeps track of confidential data namespace.
   Carries out a specified arithmetic-circuit on the data within the confidential namespace.
   Discloses only the information specified by explicit "Open" commands.

 `fMPC_sansMult`
   In addition to an underlying confidential data stream, it keeps track of a secret share encoding of each secret value.
   Each party can also read their polynomial share. Naturally, the adversary receives $t$ shares, but these reveal no information about $x$ (to summarize why F_MPC easily realizes ABB).

 `fMPC`
   The main construction we analyze is the Beaver Multiplication.
   This shows how to enrich the operation with multiplication. It's an intermediate step between F_MPC and F_ArithmeticBlackBox.


In a more realistic model, the sequence of operations would be chosen through a consensus process, like a smart contract. Allow us to provide Availability guarantees.

Defining F_MPC in more detail.
  The interface should be easily extensible, the way we add MULT should be a good example for how to add others.

 We know we want to write MPC pseudocode that looks like:
 BeaverMult: [x] [y]
   Preprocessing get [a][b][ab].
   D= open([x]-[a]) ...
   return [xy] := [ab]+D ...


The real challenge is that we want to be able to construct simulator proofs as well.
The simulator proof will need to intercept the Ids.
  See the real world, with additional variables present, such as the D and E in beaver multiplication. The environment expects to see these from the real world dummy adversary, but the functionality in the ideal world does not have any values for those. So if [x] and [y] correspond to registers $1 and $2, then [xy] in the ideal world would be $3, while in the real world.

Environment asks an honest party to query for one of the ephemeral values, it won't exist...
 ---}

mpcBeaver :: MonadMPCProgram m sh => sh -> sh -> m sh
mpcBeaver x y = do
  (a,b,ab) <- getTriple
  d <- openShare =<< sub x a 
  e <- openShare =<< sub y b
  de <- constant (d*e)
  xy <- lin [(1,de),(1,ab),(d,b),(e,a)]
  return xy

lin xs = do
  rsp <- ?op $ LIN xs
  let FmpcRes_Sh r = rsp
  return r

constant v = do
  rsp <- ?op $ CONST v
  let FmpcRes_Sh r = rsp
  return r

sub x a = lin [(1,x),(-1,a)]

getTriple :: MonadMPCProgram m sh => m (sh,sh,sh)
getTriple = do
  r <- ?op $ RAND
  let FmpcRes_Trip(a,b,ab) = r
  return (a,b,ab)


runMPCnewmul :: MonadProtocol m =>
    (forall sh. MonadMPCProgram m sh => sh -> sh -> m sh) ->
    Protocol (FmpcP2F sh) (FmpcF2P sh) (FmpcF2P sh) (FmpcP2F sh) m
runMPCnewmul mulProg (z2p,p2z) (f2p,p2f) = do

   let _op opcode = do
         writeChan p2f $ FmpcP2F_Op opcode
         res <- readChan f2p
         let (FmpcF2P_Op r) = res
         return r
  
   fork $ forever $ do
        zp <- readChan z2p
        case zp of
          FmpcP2F_Op (MULT x y) -> do
             -- Intercept the "MULT" operations and replace them with
             -- a call to the MPC program
             xy <- let ?op = _op in mulProg x y
             writeChan p2z $ FmpcF2P_Op (FmpcRes_Sh xy)
          _ -> do
             -- Everything else, we can simply forward along and 
             -- expect one response
             writeChan p2f $ zp
             readChan f2p >>= writeChan p2z

   return ()


zero :: PolyFq
zero = polyFromCoeffs []

randomWithZero :: MonadITM m => Int -> Fq -> m PolyFq
randomWithZero t z = do
  -- Random degree t polynomial phi, such that phi(0) = z
  coeffs <- forM (fromList [1..(t-1)]) (\_ -> randFq)
  return $ toPoly $ fromList [z] Data.Vector.++ coeffs

type MonadMPC_F m = (MonadFunctionality m,
                     ?n :: Int,
                     ?t :: Int)


fMPC :: MonadMPC_F m => Functionality (FmpcP2F Sh) (FmpcF2P Sh) Void Void Void Void m
fMPC = fMPC_ True True

fMPC_sansMult :: MonadMPC_F m => Functionality (FmpcP2F Sh) (FmpcF2P Sh) Void Void Void Void m
fMPC_sansMult = fMPC_ True False

fMPC_ :: MonadMPC_F m => Bool -> Bool -> Functionality (FmpcP2F Sh) (FmpcF2P Sh) Void Void Void Void m
fMPC_ hasMPC hasMul (p2f, f2p) (_,_) (_,_) = do

  -- List of operations and results (chosen by Input party)
  ops    <- newIORef ([] :: [(FmpcOp Sh, FmpcRes Sh)])

  -- Inputs provided by input party
  inputs <- newIORef []

  -- MPC only
  -- Maps share IDs to polynomials
  shareTbl <- newIORef (Map.empty :: Map Sh PolyFq)

  -- Counters viewed by each of the participant parties
  let initCtrs = [("P:"++show i, 0) | i <- [1.. ?n]]
  counters <- newIORef $ Map.fromList initCtrs

  -- Generate a fresh handle
  freshCtr <- newIORef 0
  let fresh = do
        x <- readIORef freshCtr
        modifyIORef freshCtr $ (+) 1
        return x

  -- Commit this operation and output to the log
  let commit op outp = do
        modifyIORef ops $ (++ [(op,outp)])
        writeChan f2p $ ("InputParty", FmpcF2P_Op outp)

  fork $ forever $ do
   (pid,m) <- readChan p2f
   case m of
    -- Anyone can see the log
    FmpcP2F_Log -> do
       log <- readIORef ops
       writeChan f2p (pid, FmpcF2P_Log log)
       
    FmpcP2F_Input x | pid == "InputParty" -> do
       modifyIORef inputs $ (++ [x])
       writeChan f2p (pid, FmpcF2P_Ok)
     
    -- Operations from MPC parties are in "Follow" mode.
    -- They have to provide a next op, which is matched up
    -- against the next one chosen by the input party.
    -- They receive the output, typically a handle.
    FmpcP2F_Op op | hasMPC && (not (pid == "InputParty")) -> do
     ctbl <- readIORef counters
     let Just c = Map.lookup pid ctbl
     oplist <- readIORef ops
     let (op',res) = oplist !! c
     if op == op' then do
       modifyIORef counters $ Map.insert pid (c+1)
       writeChan f2p $ (pid, FmpcF2P_Op res)
     else do
       liftIO $ putStrLn $ show oplist
       liftIO $ putStrLn $ show ctbl
       liftIO $ putStrLn $ show op
       liftIO $ putStrLn $ show op'
       error "follow mode failed" 
     
    FmpcP2F_Op op | pid == "InputParty" -> do
     -- Operations send from the input party get carried out
     -- immediately and committed to the log of operations.
     case op of
       MULT x y -> do
         -- This is a parameter so we can show how to realize it from
         -- the other operations. Generates a random polynomial whose
         -- zero-value coincides with the product of x and y
         if hasMul then do
           tbl <- readIORef shareTbl
           let Just xx = Map.lookup x tbl
           let Just yy = Map.lookup y tbl
           xy <- fresh
           phi <- randomWithZero ?t (eval xx 0 * eval yy 0)
           modifyIORef shareTbl $ Map.insert xy phi
           commit op $ FmpcRes_Sh xy

         else error "mult unimplemented"

       LIN cs -> do
         -- Construct a new secret sharing polynomial simply by
         -- scaling and summing the linear combination of existing
         -- polys from the table
         k <- fresh
         r <- foldM (\r -> \(c::Fq,x::Sh) ->  do
                     tbl <- readIORef shareTbl
                     let Just xx = Map.lookup x tbl
                     return $ r + (polyFromCoeffs [c]) * xx) zero cs
         modifyIORef shareTbl $ Map.insert k r
         commit op $ FmpcRes_Sh k

       OPEN k -> do
         -- The result of opening is included directly in the log
         tbl <- readIORef shareTbl
         let Just phi = Map.lookup k tbl
         commit op $ FmpcRes_Fq (eval phi 0)

       CONST v | hasMPC-> do
         -- Create the constant (degree-0) poly
         k <- fresh
         let phi = polyFromCoeffs [v]
         modifyIORef shareTbl $ Map.insert k phi
         commit op $ FmpcRes_Sh k

       RAND | hasMPC -> do
         -- Return a beaver triple
         ka <- fresh; kb <- fresh; kab <- fresh
         a <- randomDegree ?t
         b <- randomDegree ?t
         ab <- randomWithZero ?t (eval a 0 * eval b 0)
         modifyIORef shareTbl $ Map.insert ka a
         modifyIORef shareTbl $ Map.insert kb b
         modifyIORef shareTbl $ Map.insert kab ab
         commit op $ FmpcRes_Trip (ka, kb, kab)

       INPUT -> do
         -- Collect input from the input party some other way?
         k <- fresh
         inps <- readIORef inputs
         let x:rest = inps
         writeIORef inputs rest
         phi <- randomWithZero ?t x
         modifyIORef shareTbl $ Map.insert k phi
         commit op $ FmpcRes_Sh k

  return ()



envTestMPC :: MonadEnvironment m =>
  Environment (FmpcF2P sh) (FmpcP2F sh) a b Void Void String m
envTestMPC z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
   -- Choose the sid and corruptions
  writeChan z2exec $ SttCrupt_SidCrupt ("mpc","") empty

  -- Opened Values
  openTable <- newIORef $ Map.fromList [("P:"++show i, []) | i <- [1.. 3]]
  lastHandle <- newIORef Nothing
  
  fork $ forever $ do
    (pid,x) <- readChan p2z
    case x of
      FmpcF2P_Op (FmpcRes_Fq r) -> do
        -- Append openings
        modifyIORef openTable $ Map.insertWith (++) pid [r]
        liftIO $ putStrLn $ "Z:[" ++ pid ++ "] sent Fq " ++ show r
      FmpcF2P_Op (FmpcRes_Sh sh) -> do
        liftIO $ putStrLn $ "Z:[" ++ pid ++ "] sent Sh"
        writeIORef lastHandle $ Just sh
      _ -> do
        liftIO $ putStrLn $ "Z:[" ++ pid ++ "] sent something"
    ?pass

  fork $ forever $ do
    m <- readChan a2z
    liftIO $ putStrLn $ "Z: a sent " -- ++ show m
    writeChan outp "environment output: 1"

  () <- readChan pump
  liftIO $ putStrLn "pump"
  writeChan z2p ("InputParty", FmpcP2F_Op $ CONST 2)

  () <- readChan pump
  liftIO $ putStrLn "pump"
  _sh <- readIORef lastHandle; let Just x = _sh
  writeChan z2p ("InputParty", FmpcP2F_Op $ CONST 5)

  () <- readChan pump
  liftIO $ putStrLn "pump"
  _sh <- readIORef lastHandle; let Just y = _sh  
  writeChan z2p ("InputParty", FmpcP2F_Op $ MULT x y)

  () <- readChan pump
  liftIO $ putStrLn "pump"
  _sh <- readIORef lastHandle; let Just xy = _sh    
  writeChan z2p ("InputParty", FmpcP2F_Op $ OPEN xy)

  () <- readChan pump
  writeChan outp "environment output: 1"

runMPCFunc :: MonadFunctionality m => Int -> Int ->
    (MonadMPC_F m => Functionality a b c d e f m) ->
     Functionality a b c d e f m
runMPCFunc n t f = let ?n = n; ?t = t in f

testMpc1 = runITMinIO 120 $ execUC envTestMPC (idealProtocol) (runMPCFunc 3 1 $ fMPC) dummyAdversary

testMpc2 = runITMinIO 120 $ execUC envTestMPC (runMPCnewmul mpcBeaver) (runMPCFunc 3 1 $ fMPC_sansMult) dummyAdversary


-- TODO: We should construct a simulator simBeaver proving that
-- fMPC_sansMult --Beaver--> fMPC


