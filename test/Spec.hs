import Data.Maybe
import Data.Functor.Classes(Eq1)
import Test.QuickCheck(Arbitrary(arbitrary), Gen, oneof, shrink)
import Test.StateMachine
-- data StateMachine model cmd m resp = StateMachine
--   { initModel      :: forall r. model r
--   , transition     :: forall r. (Show1 r, Ord1 r) => model r -> cmd r -> resp r -> model r
--   , precondition   :: model Symbolic -> cmd Symbolic -> Logic
--   , postcondition  :: model Concrete -> cmd Concrete -> resp Concrete -> Logic
--   , invariant      :: Maybe (model Concrete -> Logic)
--   , generator      :: model Symbolic -> Maybe (Gen (cmd Symbolic))
--   , shrinker       :: model Symbolic -> cmd Symbolic -> [cmd Symbolic]
--   , semantics      :: cmd Concrete -> m (resp Concrete)
--   , mock           :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)
--   , cleanup        :: model Concrete -> m ()
--   }
--------------------------
--- the system under test
--- in this case, an array to represent a FIFO queue
data SUT r = SUT [r]
--------------------------
--- the model
--- in this case, also an array
data Model r = Model [Int]
--------------------------
data Command r
  = Push Int
  | Pop
  | AskLength
data Response r
  = Pushed
  | Popped (Maybe Int)
  | TellLength Int
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
precondition :: Model (Symbolic ()) -> Command (Symbolic ()) -> Logic
precondition _ _ = Top

-------------------------------------------------
-- postcondition contains all of the requirements
-- after the state has changed

postcondition :: Model (Concrete ()) -> Command (Concrete ()) -> Response (Concrete ()) -> Logic
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

generator :: Model (Symbolic ()) -> Maybe (Gen (Command (Symbolic ())))
generator _ = Just $ oneof [(pure Pop), (Push <$> arbitrary), (pure AskLength)]

----------------------------------------------
-- the shrinker specifies how to hone in on problematic actions
-- here, the only thing we need to shrink is the
-- number going into push
-- everything else doesn't need shrinking

shrinker :: Model (Symbolic ()) -> Command (Symbolic ()) -> [Command (Symbolic ())]
shrinker _ (Push x) = [ Push x' | x' <- shrink x ]
shrinker _ _             = []

---------------------------------
-- mock is the logic of the model

mock :: Model (Symbolic ()) -> Command (Symbolic ()) -> GenSym (Response (Symbolic ()))
mock _ (Push _) = pure Pushed
mock (Model m) Pop = pure $ Popped (if null m then Nothing else Just $ last m)
mock (Model m) AskLength = pure $ TellLength $ length m

-- sm :: StateMachine Model Command IO Response
-- sm = StateMachine initModel transitios precondition postcondition
--       Nothinvarianting generator shrinker semantics mock noCleanup

main :: IO ()
main = putStrLn "Test suite not yet implemented"