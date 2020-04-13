{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}

import Data.Maybe
import System.Directory
import System.Random.PCG.Unique(create, uniform)
import Data.Kind(Type)
import Data.Functor.Classes(Eq1)
import Test.QuickCheck(Arbitrary(arbitrary), Gen, oneof, shrink, quickCheck, withMaxSuccess, Property, (===))
import Test.QuickCheck.Monadic(monadicIO, run)
import GHC.Generics (Generic, Generic1)
import Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2
import System.IO
import Data.List
import Data.List.Split

--------------------------
-- the system under test
pushToQueue :: String -> Int -> IO ()
pushToQueue fname x = do
    fe <- doesFileExist fname
    if (not fe) then do
            withFile fname WriteMode $ \handle -> hPutStr handle $ show x -- write the number
        else do
            txt <- withFile fname ReadMode $ \handle -> hGetLine handle
            let split = splitOn ":" txt
            withFile fname WriteMode $ \handle -> hPutStr handle $ intercalate ":" (show x : split) -- append the number to the beginning of the string

popFromQueue :: String -> IO (Maybe Int)
popFromQueue fname = do
    fe <- doesFileExist fname
    if (not fe) then return $ Nothing else do
        txt <- withFile fname ReadMode $ \handle -> hGetLine handle
        let split = splitOn ":" txt
        if (length split == 1) then
                removeFile fname -- remove the file if queue is empty
            else
                withFile fname WriteMode $ \handle -> hPutStr handle $ intercalate ":" $ init split -- remove the last element
        return $ if null split then Nothing else Just (read (last split) :: Int)

lengthQueue :: String -> IO Int
lengthQueue fname = do
    fe <- doesFileExist fname
    if (not fe) then return 0 else do
        txt <- withFile fname ReadMode $ \handle -> hGetLine handle
        let split = splitOn ":" txt
        return $ length split

--------------------------
--- the model
--- in this case, also an array
--- for the pretty printing to work, Model Concrete needs to
--- derive from ToExpr but not Model Symbolic
--- to enable this, we use the StandaloneDeriving language feature
data Model (r :: Type -> Type) = Model [Int] deriving (Show, Eq, Generic)
deriving anyclass instance ToExpr (Model Concrete)

--------------------------
data Command (r :: Type -> Type)
  = Push Int
  | Pop
  | AskLength
  deriving stock (Eq, Show, Generic1)
  deriving anyclass (Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

data Response (r :: Type -> Type)
  = Pushed
  | Popped (Maybe Int)
  | TellLength Int
  deriving stock (Show, Generic1)
  deriving anyclass (Rank2.Foldable)
------------------------------------
-- initModel creates an initial model for all polymorphic types
-- in this case, as the model is just a list
-- we can use an empty list for the constructor
initModel :: Model r
initModel = Model []
-----------------------------------------------
-- transition creates transitions for the model
-- from command to response
transition :: Model r -> Command r -> Response r -> Model r
transition (Model m) (Push x) Pushed = Model (x : m)
transition (Model m) Pop (Popped _) = Model (if null m then m else init m)
transition m AskLength (TellLength _) = m
----------------------------------------------
-- precondition tells us if the state machine can execute
-- should return a boolean
-- note that the return type must be a logic type
-- quickheck-state-machine comes with all the
-- boolean operaters needed to form the logic type
-- in our case, because there are no preconditions, we can start
-- at the top every time, which is represented by `Top`
precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition _ _ = Top

-------------------------------------------------
-- postcondition contains all of the requirements
-- after the state has changed

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition mod cmd@(Push x) resp = x .== head m'
  where Model m' = transition mod cmd resp
postcondition (Model m) Pop (Popped x) = x .== if null m then Nothing else Just $ last m
postcondition (Model m) AskLength (TellLength x) = length m .== x

-----------------------------
-- the invariant, which takes the form Maybe (model Concrete -> Logic)
-- if Nothing, then no invariant will run
-- because invariants are expensive (they run after every rule)
-- we want it to be Nothing if there are no invariants to run
invariant = Nothing

----------------------------------------------
-- the generator generates arbitraries
-- we use the same combinators as quickcheck (oneof, etc)
-- here, the oneof generator will pick a random action

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator _ = Just $ oneof [(pure Pop), (Push <$> arbitrary), (pure AskLength)]

----------------------------------------------
-- the shrinker specifies how to hone in on problematic actions
-- here, the only thing we  shrink is the
-- number going into push because we want to test if a specific range
-- of numbers would provoke a crash
-- everything else doesn't need shrinking

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ (Push x) = [ Push x' | x' <- shrink x ]
shrinker _ _             = []

---------------------------------
-- semantics is what actually happens
-- the monadic context needs to be specified
-- and in this case it is IO

semantics :: String -> Command Concrete -> IO (Response Concrete)
semantics fname (Push x) = do
    pushToQueue fname x
    return Pushed
semantics fname Pop = do
    val <- popFromQueue fname
    return $ Popped val
semantics fname AskLength = do
    val <- lengthQueue fname
    return $ TellLength val

---------------------------------
-- mock is a mock of the logic of the model
-- it is used to document how the model works
-- but is not currently functional, so it can output
-- any values

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock _ (Push _) = pure Pushed
mock _ Pop = pure $ Popped Nothing
mock _ AskLength = pure $ TellLength 0

cleanup :: model Concrete -> IO ()
cleanup _ = return ()

sm :: String -> StateMachine Model Command IO Response
sm s = StateMachine initModel transition precondition postcondition
      invariant generator shrinker (semantics s) mock cleanup

newRand :: IO Int
newRand = do
  g <- create
  i <- uniform g
  return i

state_machine_properties :: Property
state_machine_properties = forAllCommands (sm "") Nothing $ \cmds -> monadicIO $ do
  id <- run newRand
  let fname = "queues/queue" <> (show id) <> ".txt"
  let sm' = sm fname
  (hist, _model, res) <- runCommands sm' cmds
  prettyCommands sm' hist (checkCommandNames cmds (res === Ok))

main :: IO ()
main = do
    createDirectoryIfMissing False "queues"
    quickCheck state_machine_properties
