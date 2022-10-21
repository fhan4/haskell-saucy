{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds
  #-}


module TokenWrapper where

import ProcessIO
import StaticCorruptions
import Multisession
import Async

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map


data CarryTokens a = SendTokens a deriving (Show, Eq)
data TransferTokens a = DeliverTokensWithMessage a deriving (Show, Eq)


type MonadAdversaryToken m = (MonadAdversary m,
                              -- ?sendToken :: m () -> m (),
                              ?getToken :: m Int)

-- sendToken :: MonadAdversaryToken m => m () -> m ()
-- sendToken = ?sendToken

getToken :: MonadAdversaryToken m => m Int
getToken = ?getToken



runTokenA :: MonadAdversary m =>
          (MonadAdversaryToken m => Adversary ((SttCruptZ2A z2a (Either (ClockA2F) (SID, (z2a2f, TransferTokens Int)))),
                                                CarryTokens Int)
                                              a2z p2a (ClockP2F (a2p, CarryTokens Int)) f2a (Either ClockA2F a2f) m)
          -> Adversary ((SttCruptZ2A z2a (Either (ClockA2F) (SID, (z2a2f, TransferTokens Int)))),
                       CarryTokens Int)
                       a2z p2a (ClockP2F (a2p, CarryTokens Int)) f2a (Either ClockA2F a2f) m
runTokenA a (z2a, a2z) (p2a, a2p) (f2a, a2f) = do

  tokens <- newIORef 0

  z2a' <- newChan
  a2f' <- newChan
  a2p' <- newChan

  fork $ forever $ do
    (mf, SendTokens a) <- readChan z2a
    if a>=0 then do
      tk <- readIORef tokens
      writeIORef tokens (tk+a)
    else
      error "sending negative tokens"
    case mf of
      (SttCruptZ2A_A2F (Right (_, (_, DeliverTokensWithMessage b)))) -> do
        if b>=0 then do
          tk <- readIORef tokens
          writeIORef tokens (tk+b)
          printAdv $ "simulator acquired " ++ (show b) ++ " tokens from corrupt party"
        else
          error "sending negative tokens"
      _ -> return()
    writeChan z2a' (mf, SendTokens a)

  fork $ forever $ do
    mf <- readChan a2f'
    case mf of
      Left (ClockA2F_Deliver _) -> do
        tk <- readIORef tokens
        if (tk-1) < 0 then
          error "not enough tokens"
        else
          writeIORef tokens (tk-1)
      Left (ClockA2F_Delay rounds) -> do
        if rounds > 0 then do
          tk <- readIORef tokens
          if (tk-rounds) < 0 then
            error "not enough tokens"
          else
            writeIORef tokens (tk-rounds)
        else
          return()
      _ -> return()
    writeChan a2f mf

  fork $ forever $ do
    mf <- readChan a2p'
    case mf of
      (_, (ClockP2F_Through (_, SendTokens k))) -> do
        if k >= 0 then do
          tk <- readIORef tokens
          if (tk-k) < 0 then
            error "not enough tokens"
          else
            writeIORef tokens (tk-k)
        else
          error "sending negative tokens"
        liftIO $ putStrLn $ "simulator sends " ++ (show k) ++ " tokens to ideal functionality"
      _ -> return()
    writeChan a2p mf

  let _getToken = do
        tk <- readIORef tokens
        return tk

  let ?getToken = _getToken in
    a (z2a', a2z) (p2a, a2p') (f2a, a2f')
  return ()

dummyAdversaryToken :: MonadAdversary m => Adversary ((SttCruptZ2A b d), CarryTokens Int)
                                                     (SttCruptA2Z a (Either (ClockF2A (SID, (c, CarryTokens Int))) f2a))
                                                     a b (Either (ClockF2A (SID, (c, CarryTokens Int))) f2a) d m
dummyAdversaryToken (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >>= \mf ->
      case mf of
        ((SttCruptZ2A_A2F b), SendTokens _)        -> writeChan a2f b
        ((SttCruptZ2A_A2P (pid, m)), SendTokens _) -> writeChan a2p (pid, m)
  fork $ forever $ readChan f2a >>= writeChan a2z . SttCruptA2Z_F2A
  fork $ forever $ readChan p2a >>= writeChan a2z . SttCruptA2Z_P2A
  return ()

idealProtocolToken :: MonadProtocol m => Protocol (ClockP2F a, CarryTokens Int) b b (ClockP2F (a, CarryTokens Int)) m
idealProtocolToken (z2p, p2z) (f2p, p2f) = do
  fork $ forever $ do
    mf <- readChan z2p
    --liftIO $ putStrLn $ "idealProtocol received from z2p " ++ pid
    case mf of
      (ClockP2F_Pass, SendTokens _)       -> writeChan p2f ClockP2F_Pass
      (ClockP2F_Through m, SendTokens tk) -> writeChan p2f (ClockP2F_Through (m, SendTokens tk))
  fork $ forever $ do
    m <- readChan f2p
    --liftIO $ putStrLn $ "idealProtocol received from f2p " ++ pid
    writeChan p2z m
  return ()
