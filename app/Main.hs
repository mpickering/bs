{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Development.IDE.Core.Service
import Development.IDE.Types.Action
import           Control.Concurrent.Extra

import Development.IDE.Types.Options
import Control.Concurrent.MVar
import qualified Data.Dependent.Map as D
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HMap
import System.IO
import Data.GADT.Compare
import Data.Dependent.Sum
import Control.Concurrent.Async
import Control.Monad
import System.Random
import Control.Concurrent
import Control.Applicative
import Control.Applicative.Free
import Data.Coerce
import Data.List (delete)
import Data.Maybe
import Debug.Trace
import Data.List
import Reflex
import Data.Functor.Compose
import Control.Monad.Trans.Class
import Control.Monad.State.Class
import Control.Monad.State
import Control.Monad.IO.Class
import Reflex.Host.Basic
import Control.Monad.Ref
import Reflex.Host.Class
import Algebra.Graph
import Algebra.Graph.Export.Dot
import Control.Monad.RWS hiding (Any, Ap)

import           Development.Shake.Database
import Unsafe.Coerce

import Control.DeepSeq
import GHC.Generics
import Development.IDE.Core.Shake hiding (shakeOpen)
import Development.IDE.Types.Logger
import qualified Development.Shake as S
import Data.Hashable
import qualified Data.Binary as B
import Data.Default
import Control.Concurrent.STM
import GHC.Exts

data ModNode = ModNode { mn :: String } deriving (Eq, Ord, Show, Generic)

data HomeModInfo = HomeModInfo deriving (Eq, Generic, Show)



n1 = (ModNode "m1")
n2 = (ModNode "m2")
n3 = (ModNode "m3")
n4 = (ModNode "m4")
n5 = (ModNode "m5")


modMap :: M.Map ModNode [ModNode]
modMap = M.fromList [(n5, [n4, n3]), (n4, [n1]), (n3, [n2]), (n1, []), (n2, [n1])]

compileMod :: ModNode -> [HomeModInfo] -> IO HomeModInfo
compileMod mn _ = do
  delay <- randomRIO (0, 1000000)
  print ("START", mn , delay)
  threadDelay delay
  print ("END", mn)
  return HomeModInfo


main = do
--  mkTaskMap >>= runTasks
--  print (allNodes fullBuildTree)
--  actions fullBuildTree
--  interpK fullBuildTreeP ()
--  print (allActions fullBuildTreeP)
--  interpC fullBuildTreeP ()
  print (regenDepMap fullBuildTreeP)
  print (transitiveReduce (regenDepMap fullBuildTreeP))
  print modMap
  print (transitiveReduce modMap)
  print (transitiveReduce (regenDepMap fullBuildTreeP) == transitiveReduce modMap)

  runK (interpFreer interpK depBuild) ()
  putStrLn "C"
  runK (interpFreer interpC depBuild) ()


  putStrLn "G"

  let g = interpG fullBuildTreeP
  putStrLn $ export (defaultStyle mn) g


  putStrLn "R"

  basicHostWithQuit $ do
    (start, trigger) <- newTriggerEvent
    (network, nodes) <- runStateT (unwrap $ (getR (interpR fullBuildTreeP) start)) M.empty

    liftIO $ (trigger ())
    return $ (() <$ (updated $ fromJust $  M.lookup n5 nodes))

  putStrLn "S"


  act <- async $ do
    (ide, act) <- interpShake fullBuildTreeP ()
    act
    shakeShut ide
  wait act



data Comp p a b where
  CUnit :: Comp p () ()
  CEff :: p a b -> Comp p a b
  CMap :: (c -> a) -> (b -> d) -> Comp p a b -> Comp p c d
  CAp :: (e -> (a, c)) -> ((b, d) -> f) -> Comp p a b -> Comp p c d -> Comp p e f
  CComp :: Comp p b c -> Comp p a b -> Comp p a c

class Profunctor p where
  dimap :: (c -> a) -> (b -> d) -> p a b -> p c d

instance Profunctor (->) where
  dimap f g h = g . h . f

class (Profunctor p) => ProfunctorApp p where
  cunit :: p () ()
  pap :: (e -> (a, c)) -> ((b, d) -> f) -> p a b -> p c d -> p e f

class Category p where
  cid :: p a a
  comp :: p b c -> p a b -> p a c

instance Profunctor (Comp p) where
  dimap = CMap

instance ProfunctorApp (Comp p) where
  cunit = CUnit
  pap = CAp

instance Category (Comp p) where
  comp = CComp

injP :: p a b -> Comp p a b
injP fa = CEff fa

interpP :: (Category p, ProfunctorApp p) => (forall a b . q a b -> p a b) -> Comp q a b -> p a b
interpP f CUnit = cunit
interpP f (CEff ef) = f ef
interpP f (CMap to from pab) = dimap to from (interpP f pab)
interpP f (CAp to from pab pcd) = pap to from (interpP f pab) (interpP f pcd)
interpP f (CComp pbc pab) = comp (interpP f pbc) (interpP f pab)

data PAction inp out where
  CompileModP :: ModNode -> PAction [HomeModInfo] HomeModInfo

type BuildTreeP = Comp PAction

p :: ModNode -> BuildTreeP [HomeModInfo] HomeModInfo
p s = injP (CompileModP s)

instance Functor (Comp f ()) where
  fmap f c = CMap id f c

dup :: a -> (a, a)
dup a = (a, a)

instance Applicative (Comp f ()) where
  pure a = dimap id (const a) CUnit
  fab <*> fb = CAp dup (uncurry ($)) fab fb


traverseP :: (Traversable f, Applicative (p ())) => (a -> p () c) -> f a -> p () (f c)
traverseP = traverse


mkBuildTreeP :: M.Map ModNode [ModNode] -> M.Map ModNode (BuildTreeP () HomeModInfo)
mkBuildTreeP depMap = actions

  where actions :: M.Map ModNode (BuildTreeP () HomeModInfo)
        actions = M.mapWithKey (\k deps -> p k `comp` traverse (\dep -> actions M.! dep) deps) depMap

fullBuildTreeP = mkBuildTreeP modMap M.! n5


interpFreer :: Monad m => (forall a . f a -> m a) -> Freer f a -> m a
interpFreer f (FPure a) = return a
interpFreer f (FRoll fa afb) = f fa >>= interpFreer f . afb



data Freer f b where
    FPure :: a  -> Freer f a
    FRoll :: f a  -> (a -> Freer f b) -> Freer f b

instance Functor (Freer f) where
  fmap = liftM

instance Applicative (Freer f) where
  pure = return
  (<*>) = ap

instance Monad (Freer f) where
  return = FPure
  FPure a >>= k = k a
  FRoll fa afb >>= k = FRoll fa (afb >=> k)

-- | Just produce a value a
produce :: a -> Comp PAction () a
produce = pure

li :: f a -> Freer f a
li fa = FRoll fa pure

type MBuild a b = Freer (Comp PAction a) b

getTop :: Eq a => M.Map a [a] -> a
getTop m = head $ (M.keys m) \\ (concat (M.elems m))

-- | Simple dependent build
depBuild :: MBuild () HomeModInfo
depBuild = do
  mm <- li $ produce modMap
  let g = mkBuildTreeP mm
  li (g M.! (getTop mm))

newtype K m a b = K { runK :: a -> m b } deriving Functor

hoist :: (forall a . m a -> n a) -> K m a b -> K n a b
hoist f (K k) = K $ \a -> f (k a)



instance Monad m => Applicative (K m a) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (K m a) where
  return a = K $ \_ -> pure a
  (K fa) >>= afb = K $ \a -> do
    res <- fa a
    case afb res of
      K k -> k a

instance Applicative m => Profunctor (K m) where
  dimap f g (K h) = K (fmap g . h . f)

instance Applicative m => ProfunctorApp (K m) where
  cunit = K pure
--  CAp :: (e -> (a, c)) -> ((b, d) -> f) -> Comp p a b -> Comp p c d -> Comp p e f
  pap eac bdf (K cpab) (K cpcd) = K (\e -> let (a, c) = eac e
                                           in curry bdf <$> cpab a <*> cpcd c )
--  CComp :: Comp p b c -> Comp p a b -> Comp p a c

instance Monad Concurrently where
  ma >>= f = Concurrently (runConcurrently ma  >>= (runConcurrently . f))

instance Monad m => Category (K m) where
  comp (K ab) (K cd) = K (ab <=< cd)

interpK :: BuildTreeP a b -> K IO a b
interpK =  interpP go
  where
    go :: PAction inp out -> K IO inp out
    go (CompileModP mn) = K (compileMod mn)

interpC :: BuildTreeP a b -> K IO a b
interpC b = hoist runConcurrently (interpP go b)
  where
    go :: PAction inp out -> K Concurrently inp out
    go (CompileModP mn) = K (Concurrently . compileMod mn)

allActions :: BuildTreeP a b -> [ModNode]
allActions = getKP . interpP go
  where
    go :: PAction inp out -> KP [ModNode] inp out
    go (CompileModP mn) = KP [mn]

newtype KP e a b = KP { getKP :: e }

instance Profunctor (KP e) where
  dimap f g h = coerce h

instance Monoid e => ProfunctorApp (KP e) where
  cunit = KP mempty
--  CAp :: (e -> (a, c)) -> ((b, d) -> f) -> Comp p a b -> Comp p c d -> Comp p e f
  pap eac bdf (KP a) (KP b) = KP (a <> b)
--  CComp :: Comp p b c -> Comp p a b -> Comp p a c

instance Semigroup e => Category (KP e) where
  comp (KP ab) (KP cd) = KP (ab <> cd)



newtype DepMap a b = DepMap { getDepMap :: M.Map ModNode [ModNode] }

instance Profunctor (DepMap) where
  dimap f g h = coerce h

instance  ProfunctorApp (DepMap) where
  cunit = DepMap mempty
--  CAp :: (e -> (a, c)) -> ((b, d) -> f) -> Comp p a b -> Comp p c d -> Comp p e f
  pap eac bdf (DepMap a) (DepMap b) = DepMap (M.unionWith (++) a b)
--  CComp :: Comp p b c -> Comp p a b -> Comp p a c

instance Category (DepMap) where
  comp (DepMap ab) (DepMap cd) =
    DepMap (M.unionsWith (++) [ab, cd
                              , M.fromListWith (++) [(from, [to]) | from <- M.keys ab, to <- M.keys cd]
                              , M.fromListWith (++) [(from, [to]) | froms <- M.elems ab, from <- froms, to <- M.keys cd]])

regenDepMap :: BuildTreeP a b -> M.Map ModNode [ModNode]
regenDepMap = getDepMap . interpP go
  where
    go :: PAction inp out -> DepMap inp out
    go (CompileModP mn) = DepMap (M.singleton mn [])


transitiveReduce :: (Ord a, Eq a) => M.Map a [a] -> M.Map a [a]
transitiveReduce graph = foldr (\(x, y , z) g -> if hasEdge g x y && hasEdge  g y z
                                                  then deleteEdge g x z
                                                  else g) graph [(x, y, z) | x <- M.keys graph, y <- M.keys graph, z <- M.keys graph, x /= y, y /= z, (x /= y && x /= z)]

  where

    hasEdge g x y  = fromMaybe False ((y `elem`) <$> M.lookup x g)
    deleteEdge g x y = M.adjust (delete y) x g

-- Free Monad


-- Reflex

newtype WrappedDyn t m a = WrappedDyn { unwrap ::  (m (Dynamic t (Maybe a))) }

--instance Functor (WrappedDyn t m) where
--  fmap f (WrappedDyn mdta) = fmap (fmap f) mdta


-- Reflex interpretation
newtype RArr t m a b = RArr (Event t a -> WrappedDyn t m b)

getR (RArr f) = f

instance (Functor (Dynamic t), Functor m) => Functor (WrappedDyn t m) where
  fmap f (WrappedDyn m) = WrappedDyn (fmap (fmap (fmap f)) m)

instance (Applicative (Dynamic t), Applicative m) => Applicative (WrappedDyn t m) where
  pure a = WrappedDyn $ pure (pure (pure a))
  (WrappedDyn m) <*> (WrappedDyn n) = WrappedDyn $ (\e1 e2 -> (\d1 d2 -> ($) <$> d1 <*> d2) <$> e1 <*> e2) <$> m <*> n


{-
deriving via (K (Dynamic t) (Event t a)) instance Reflex t => (Functor (RArr t a))
deriving via (K (Dynamic t) (Event t a)) instance Reflex t => (Applicative (RArr t a))
deriving via (K (Dynamic t) (Event t a)) instance Reflex t => (Monad (RArr t a))
-}




instance (Reflex t, Functor m) => Profunctor (RArr t m) where
  dimap f g (RArr arr) = RArr (\e -> g <$> arr (f <$> e))

instance  (Applicative m, Reflex t, MonadHold t m) => ProfunctorApp (RArr t m) where
  cunit = RArr (\e -> WrappedDyn $ holdDyn Nothing (Just <$> e))
--  CAp :: (e -> (a, c)) -> ((b, d) -> f) -> Comp p a b -> Comp p c d -> Comp p e f
  pap eac bdf (RArr a) (RArr b) = RArr (\ete -> do case splitE (fmap eac ete) of
                                                    (le, re) -> curry bdf  <$> a le <*> b re)
--  CComp :: Comp p b c -> Comp p a b -> Comp p a c

instance (Monad m, Reflex t) => Category (RArr t m) where
  comp (RArr ab) (RArr cd) = RArr (\t -> WrappedDyn (unwrap . ab . fmapMaybe id . updated =<< unwrap (cd t)))

interpR :: (_) => BuildTreeP a b -> RArr t m a b
interpR bg = interpP go bg
  where

    compileOne :: _ => ModNode -> Event t [HomeModInfo] -> m (Event t HomeModInfo)
    compileOne mn e = performEventAsync ((\hmis k -> () <$ liftIO (forkIO ((compileMod mn hmis >>= k)))) <$> e)

    init :: (MonadIO (Performable m), Monad m , MonadState (M.Map ModNode (Dynamic t (Maybe HomeModInfo))) m, TriggerEvent t m, MonadHold t m, Reflex t, PerformEvent t m) => ModNode -> Event t [HomeModInfo] -> WrappedDyn t m HomeModInfo
    init mn e = WrappedDyn $ do
     m <- get
     case M.lookup mn m of
       Just d -> return d
       Nothing -> do
        e' <- compileOne mn e
        d <- holdDyn Nothing (Just <$> e')
        modify (M.insert mn d)
        return d
    go :: (MonadState (M.Map ModNode (Dynamic t (Maybe HomeModInfo))) m, TriggerEvent t m, PerformEvent t m, MonadIO (Performable m), MonadHold t m) => PAction inp out -> RArr t m inp out
    go (CompileModP mn) = RArr $ \e -> init mn e


instance PerformEvent t m => PerformEvent t (StateT s m) where
  type Performable (StateT s m) = Performable m
  performEvent_ = lift . performEvent_
  performEvent = lift . performEvent

instance MonadSample t m => MonadSample t (StateT s m) where
  sample = lift . sample

instance MonadHold t m => MonadHold t (StateT s m) where
  hold a0 = lift . hold a0
  holdDyn a0 = lift . holdDyn a0
  holdIncremental a0 = lift . holdIncremental a0
  buildDynamic a0 = lift . buildDynamic a0
  headE = lift . headE


-- Forgetful embedding to untyped graphs

newtype GP a b = GP { runGP :: (Graph ModNode) }

interpG :: BuildTreeP a b -> Graph ModNode
interpG = runGP . interpP go
  where
    go :: PAction inp out -> GP inp out
    go (CompileModP mn) = GP (Vertex mn)

instance Profunctor GP where
  dimap f g h = coerce h

instance  ProfunctorApp GP where
  cunit = GP Empty
--  CAp :: (e -> (a, c)) -> ((b, d) -> f) -> Comp p a b -> Comp p c d -> Comp p e f
  pap eac bdf (GP a) (GP b) = GP (Overlay a b)
--  CComp :: Comp p b c -> Comp p a b -> Comp p a c

instance Category GP where
  comp (GP ab) (GP cd) =
    GP (Connect cd ab)


-- Shake

type SS a = RWS () (M.Map ModNode (S.Action ShowableAny)) Int (S.Action a)


-- Idea: Generate a rule for each node, then `_Se



data ShakeAct a b = ShakeAct { runShake :: (S.Action a -> SS b) }

instance Profunctor ShakeAct where
  dimap f g (ShakeAct act) = ShakeAct (dimap (fmap f) ((fmap . fmap) g) act)

instance  ProfunctorApp ShakeAct where
  cunit = ShakeAct return
--  CAp :: (e -> (a, c)) -> ((b, d) -> f) -> Comp p a b -> Comp p c d -> Comp p e f
  pap eac bdf (ShakeAct a) (ShakeAct b) = ShakeAct (
               \e -> case eac <$> e of
                        r -> liftA2Par bdf <$> (a (fst <$> r)) <*> b (snd <$> r))
--  CComp :: Comp p b c -> Comp p a b -> Comp p a c

liftA2Par f a b = f <$> (S.par a b)

instance Category ShakeAct where
  comp (ShakeAct (ab)) (ShakeAct (cd)) =
    ShakeAct $ (ab <=< cd)


data CMRule = CMRule ModNode  deriving (Show, Generic, Eq)

instance Hashable CMRule where
  hashWithSalt s (CMRule (ModNode mn) ) = hashWithSalt s mn

instance B.Binary CMRule where
instance B.Binary ModNode where
instance B.Binary HomeModInfo where
instance NFData CMRule where
instance NFData ModNode where
instance NFData HomeModInfo where


type instance S.RuleResult CMRule = HomeModInfo

interpShake :: BuildTreeP a b -> a -> IO (IdeState, IO b)
interpShake bg a = do
  let (ShakeAct f) = interpP go bg
      (act, _, deps) = runRWS (f (return a)) () 0
  ide <- shakeOpen (mkRule deps >> (addIdeGlobal $ GlobalIdeOptions (defaultIdeOptions undefined)))
  return (ide, runAction "I" ide act)
  where
    mkRule deps = define $ \(SRule n) _ -> do
                    res <- fromJust $ M.lookup n deps
                    return ([], Just res)

    go :: PAction inp out -> ShakeAct inp out
    go (CompileModP mn) =
      ShakeAct $ \deps -> do
        let

          forgetType :: S.Action HomeModInfo -> S.Action ShowableAny
          forgetType = fmap mkShowableAny

          act :: S.Action [HomeModInfo] -> S.Action HomeModInfo
          act deps = do
            ds <- deps
            liftIO $ compileMod mn ds
        n <- get
        modify (+1)
        tell (M.singleton mn (forgetType (act deps)))
        return $ fmap coerceShowableAny (useNoFile_ (SRule mn))
      where

mkShowableAny :: Show a => a -> ShowableAny
mkShowableAny x = ShowableAny (unsafeCoerce x) (show x)

coerceShowableAny :: ShowableAny -> a
coerceShowableAny (ShowableAny x _) = unsafeCoerce x


data ShowableAny = ShowableAny Any String

instance Show ShowableAny where
  show (ShowableAny _ s) =s

instance NFData ShowableAny where
    rnf _ = ()


data SRule = SRule ModNode deriving (Show, Generic, Eq)

instance Hashable ModNode where
  hashWithSalt s (ModNode mn) = hashWithSalt s mn

instance Hashable SRule where
  hashWithSalt s (SRule i) = hashWithSalt s i

instance B.Binary SRule where
instance NFData SRule where

type instance S.RuleResult SRule = ShowableAny




shakeOpen rules = mdo
    inProgress <- newVar HMap.empty
    (shakeExtras, stopProgressReporting) <- do
        globals <- newVar HMap.empty
        state <- newVar HMap.empty
        diagnostics <- newVar mempty
        hiddenDiagnostics <- newVar mempty
        publishedDiagnostics <- newVar mempty
        positionMapping <- newVar HMap.empty
        knownTargetsVar <- newVar $ hashed HMap.empty
        let restartShakeSession = shakeRestart ideState
        let session = shakeSession
        mostRecentProgressEvent <- newTVarIO KickCompleted
        persistentKeys <- newVar HMap.empty
        let progressUpdate = atomically . writeTVar mostRecentProgressEvent
        indexPending <- newTVarIO HMap.empty
        indexCompleted <- newTVarIO 0
        indexProgressToken <- newVar Nothing
        let hiedbWriter = HieDbWriter{..}
--        progressAsync <- async $ return ()
        exportsMap <- newVar mempty

        actionQueue <- newQueue

        let clientCapabilities = def

        pure (ShakeExtras{..}, return ())
    (shakeDbM, shakeClose) <-
        shakeOpenDatabase
            S.shakeOptions { S.shakeExtra = S.addShakeExtra shakeExtras (S.shakeExtra S.shakeOptions), S.shakeThreads = 5 }
            rules
    shakeDb <- shakeDbM
    initSession <- newSession shakeExtras shakeDb []
    shakeSession <- newMVar initSession
    shakeDatabaseProfile <- return undefined
    let ideState = IdeState{..}

    return ideState


class ProfunctorSum2 p where
  branch :: p a (Either b c) -> p a (p b d) -> p a (p c d) -> p a d

instance ProfunctorSum2 (->) where
  branch c k1 k2 = \a ->
    let bran = c a
    in case bran of
         Left b -> k1 a b
         Right c -> k2 a c

instance ProfunctorSum2 (K IO) where
  branch (K c) (K k1) (K k2) = K $ \a -> do
    brana <- async $ c a
    k1a <- async $ k1 a
    k2a <- async $ k2 a
    bran <- wait brana
    case bran of
      Left b -> do
        cancel k2a
        (K k1') <- wait k1a
        k1' b
      Right c -> do
        cancel k1a
        K k2' <- wait k2a
        k2' c

normalChoice :: (Profunctor p, Category p, ProfunctorSum2 p) => p a b -> p a' b' -> p (Either a a') (Either b b')
normalChoice l r = branch cid (dimap id (\_ -> dimap id Left l) cid) (dimap id (\_ -> dimap id Right r) cid)









{-

-- Free applicative structure
data Struct f a where
  SPure :: a -> Struct f a
  Eff  :: (a -> b) -> f a -> Struct f b
  Comb :: (a -> b -> c) -> Struct f a -> Struct f b -> Struct f c

inj :: f a -> Struct f a
inj fa = Eff id fa

interp :: Applicative g => (forall a . f a -> g a) -> Struct f a -> g a
interp f (SPure a) = pure a
interp f (Eff g ef) = g <$> f ef
interp f (Comb g a b) = liftA2 g (interp f a) (interp f b)

instance Functor (Struct f) where
  fmap f (SPure a) = SPure (f a)
  fmap f (Eff g ef) = Eff (f . g) ef
  fmap f (Comb g a b) = Comb (\a b -> f (g a b)) a b

instance Applicative (Struct f) where
  pure = SPure
  liftA2 = Comb


data ActionNew a where
  CompileModNew :: ModNode -> ActionNew ([HomeModInfo] -> HomeModInfo)

type BuildTreeNew a = Struct ActionNew a

c :: ModNode -> BuildTreeNew ([HomeModInfo] -> HomeModInfo)
c s = inj (CompileModNew s)


mkBuildTreeNew :: M.Map ModNode [ModNode] -> M.Map ModNode (BuildTreeNew HomeModInfo)
mkBuildTreeNew depMap = actions

  where actions :: M.Map ModNode (BuildTreeNew HomeModInfo)
        actions = M.mapWithKey (\k deps -> c k <*> traverse (\dep -> actions M.! dep) deps) depMap



fullBuildTreeNew = mkBuildTreeNew modMap M.! n5


data Phases = C | CG

-- The things we can do
data Phase a where
  CompileMod :: ModNode -> Phase C

data WrappedPhase where
  WrappedPhase :: Phase a -> WrappedPhase

instance Eq WrappedPhase where
  wp == wp' = compare wp wp' == EQ

instance Ord WrappedPhase where
  (WrappedPhase p1) `compare` (WrappedPhase p2) = case gcompare p1 p2 of
                                                    GEQ -> EQ
                                                    GLT -> LT
                                                    GGT -> GT

data WrappedResult where
  WrappedResult :: Result a -> WrappedResult

instance GEq Phase where

instance GCompare Phase where
  gcompare (CompileMod m) (CompileMod n) = case compare m n of
                                             LT -> GLT
                                             GT -> GGT
                                             EQ -> GEQ

-- Results of things we can do
data Result a where
  ModResult :: HomeModInfo -> Result C

data Task a where
  Task :: { action :: IO ()
          , resVar :: Var (Result a) }
       -> Task a

waitVar = undefined
fillVar = undefined


data Action a = Action { aaction :: a
                       , name :: String }



type BuildTree = Ap Action

allNodes bg = runAp_ (((:[])) . name) bg
actions :: BuildTree (IO a) -> IO a
actions bg  = join $ runAp (pure . aaction) bg

mkBuildTree :: M.Map ModNode [ModNode] -> M.Map ModNode (BuildTree (IO HomeModInfo))
mkBuildTree depMap = actions

  where actions :: M.Map ModNode (BuildTree (IO HomeModInfo))
        actions = M.mapWithKey (\k deps -> mkAction k <*> fmap sequence (traverse (\dep -> actions M.! dep) deps)) depMap

        mkAction :: ModNode -> BuildTree (IO [HomeModInfo] -> IO HomeModInfo)
        mkAction mn = liftAp $ Action ((compileMod' mn)) (show mn)

fullBuildTree = mkBuildTree modMap M.! n5

compileMod' :: ModNode -> IO [HomeModInfo] -> IO HomeModInfo
compileMod' mn wait = do
  mods <- wait
  compileMod mn mods

getHomeMods :: [WrappedResult] -> [HomeModInfo]
getHomeMods [] = []
getHomeMods (WrappedResult (ModResult m) : xs) = m : getHomeMods xs

execute :: Phase a -> [WrappedResult] -> IO (Result a)
execute (CompileMod m) wrs = ModResult <$> compileMod m (getHomeMods wrs)

m1 = WrappedPhase (CompileMod (ModNode "m1"))
m2 = WrappedPhase (CompileMod (ModNode "m2"))
m3 = WrappedPhase (CompileMod (ModNode "m3"))
m4 = WrappedPhase (CompileMod (ModNode "m4"))
m5 = WrappedPhase (CompileMod (ModNode "m5"))

depsMap :: M.Map WrappedPhase [WrappedPhase]
depsMap = M.fromList [(m4, []), (m1, []), (m2,[]), (m3, [m1, m2]), (m5, [m4])]

type TaskMap = D.DMap Phase Task

mkTaskMap =
  fixIO $ \t -> M.foldrWithKey (mkTask t) (return D.empty) depsMap

mkTask :: TaskMap -> WrappedPhase -> [WrappedPhase] -> IO TaskMap -> IO TaskMap
mkTask final_tm (WrappedPhase p) wps tm = do
    rv <- undefined -- newVar
    tm' <- tm
    return $ D.insert p (Task (runTask rv) rv) tm'
  where
    getResVar (WrappedPhase p) = WrappedResult <$> (waitVar (resVar (final_tm D.! p)))
    runTask rv = do
      ds <- mapM getResVar wps
      res <- execute p ds
      fillVar res rv

runTasks :: TaskMap -> IO ()
runTasks tm = do
  -- Queue up all tasks
  threads <- mapM ((\(_ :=> t) -> async . action $ t)) (D.assocs tm)
  -- Wait for them to finish
  mapM_ wait threads

-}
