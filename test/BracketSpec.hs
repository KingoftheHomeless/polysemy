module BracketSpec where

import Control.Monad
import Data.Either
import Polysemy
import Polysemy.Error
import Polysemy.Output
import Polysemy.Resource
import Polysemy.State
import Polysemy.Trace
import Test.Hspec
import Unsafe.Coerce



spec :: Spec
spec = parallel $ do
  testAllThree "persist state and call the finalizer"
      (\(ts, (s, e)) -> do
        s `shouldBe` "finalized"
        e `shouldBe` Left ()
        ts `shouldBe` ["allocated", "starting block"]
      ) $ do
    bracket
      (put "allocated" >> pure ())
      (\() -> do
        get >>= trace
        put "finalized"
      )
      (\() -> do
        get >>= trace
        put "starting block"
        _ <- throw ()
        put "don't get here"
      )

  testAllThree "persist state and call the finalizer with bracketOnError"
      (\(ts, (s, e)) -> do
        ts `shouldContain` ["allocated"]
        ts `shouldContain` ["starting block"]
        s `shouldBe` "finalized"
        e `shouldBe` Left ()
      ) $ do
    bracketOnError
      (put "allocated" >> pure ())
      (\() -> do
        get >>= trace
        put "finalized"
      )
      (\() -> do
        get >>= trace
        put "starting block"
        _ <- throw ()
        put "don't get here"
      )

  testAllThree "should not call the finalizer if there no error"
      (\(ts, (s, e)) -> do
        ts `shouldContain` ["allocated"]
        ts `shouldNotContain` ["starting block"]
        s `shouldBe` "don't get here"
        e `shouldBe` Right ()
      ) $ do
    bracketOnError
      (put "allocated" >> pure ())
      (\() -> do
        get >>= trace
        put "finalized"
      )
      (\() -> do
        get >>= trace
        put "starting block"
        put "don't get here"
      )

  testAllThree "should call the finalizer on Error"
      (\(ts, (s, e)) -> do
        ts `shouldContain` ["beginning transaction"]
        ts `shouldContain` ["rolling back transaction"]
        s `shouldBe` ""
        e `shouldBe` Left ()
      ) $ do
    withTransaction $ do
      void $ throw ()
      pure "hello"

  testTheIOTwo "io dispatched bracket"
      (\(ts, (s, e)) -> do
        ts `shouldContain` ["allocated"]
        ts `shouldContain` ["starting block"]
        s `shouldBe` "finalized"
        e `shouldBe` Left ()
      ) $ do
    bracket
      (put "allocated" >> pure ())
      (\() -> do
        get >>= trace
        put "finalized"
      )
      (\() -> do
        get >>= trace
        put "starting block"
        _ <- throw ()
        put "don't get here"
      )

  testTheIOTwo "should not lock when done recursively"
      (\(ts, (s, e)) -> do
        ts `shouldContain` [ "hello 1"
                           , "hello 2"
                           , "RUNNING"
                           , "goodbye 2"
                           ]
        s `shouldBe` "finished"
        e `shouldBe` Left ()
      ) $ do
    bracket
      (put "hello 1")
      (\() -> do
        get >>= trace
        put "finished"
      )
      (\() -> do
        get >>= trace
        void $
          bracket (put "hello 2")
                  (const $ do
                    get >>= trace
                    put "goodbye 2"
                  )
                  (const $ do
                    get >>= trace
                    put "RUNNING"
                    throw ()
                  )
        -- This doesn't run due to the thrown error above
        get >>= trace
        put "goodbye 1"
      )

  describe "How effects are dropped by exceptions:" $ do
    let
        bracketPreserveAllOnNoError        = ["alloc pure", "use pure", "dealloc pure"]
        bracketOnErrorPreserveAllOnNoError = ["alloc pure", "use pure"]

        preserveAllOn str = [ "alloc " ++ str, "use " ++ str, "dealloc " ++ str ]
        loseDeallocOn str = [ "alloc " ++ str, "use " ++ str ]
        loseAllOn _str    = []
    it "runResource bracket/OnError only protects against pure local exceptions." $ do
      let
          iosShouldBe =
                loseDeallocOn "IO"
            ++  loseDeallocOn "global"
            ++  preserveAllOn "local"

          globalsShouldBe =
                loseAllOn "IO"
            ++  loseDeallocOn "global"
            ++  preserveAllOn "local"

          localsShouldBe =
                loseAllOn "IO"
            ++  loseAllOn "global"
            ++  loseDeallocOn "local"
      runTest4Expecting (runTest4Pure test4Bracket) $ \ios globals locals -> do
        ios `shouldBe` bracketPreserveAllOnNoError ++ iosShouldBe
        globals `shouldBe` bracketPreserveAllOnNoError ++ globalsShouldBe
        locals `shouldBe` bracketPreserveAllOnNoError ++ localsShouldBe

      runTest4Expecting (runTest4Pure test4BracketOnError) $ \ios globals locals -> do
        ios `shouldBe` bracketOnErrorPreserveAllOnNoError ++ iosShouldBe
        globals `shouldBe` bracketOnErrorPreserveAllOnNoError ++ globalsShouldBe
        locals `shouldBe` bracketOnErrorPreserveAllOnNoError ++ localsShouldBe

    it "resourceToIO bracket/OnError protects against IO and pure local exceptions, \
       \ but not pure global ones." $ do
      let
          iosShouldBe =
                preserveAllOn "IO"
            ++  loseDeallocOn "global"
            ++  preserveAllOn "local"

          globalsShouldBe =
                loseAllOn "IO"
            ++  loseDeallocOn "global"
            ++  preserveAllOn "local"

          localsShouldBe =
                loseAllOn "IO"
            ++  loseAllOn "global"
            ++  loseDeallocOn "local"
      runTest4Expecting (runTest4Forklift test4Bracket) $ \ios globals locals -> do
        ios `shouldBe` bracketPreserveAllOnNoError ++ iosShouldBe
        globals `shouldBe` bracketPreserveAllOnNoError ++ globalsShouldBe
        locals `shouldBe` bracketPreserveAllOnNoError ++ localsShouldBe

      runTest4Expecting (runTest4Forklift test4BracketOnError) $ \ios globals locals -> do
        ios `shouldBe` bracketOnErrorPreserveAllOnNoError ++ iosShouldBe
        globals `shouldBe` bracketOnErrorPreserveAllOnNoError ++ globalsShouldBe
        locals `shouldBe` bracketOnErrorPreserveAllOnNoError ++ localsShouldBe

    it "resourceToIOFinal bracket/OnError protects against all kinds of exceptions. \
       \ Effects are preserved according to the table." $ do
      let
          iosShouldBe =
                preserveAllOn "IO"
            ++  preserveAllOn "global"
            ++  preserveAllOn "local"

          globalsShouldBe =
                loseAllOn "IO"
            ++  loseDeallocOn "global"
            ++  preserveAllOn "local"

          localsShouldBe =
                loseAllOn "IO"
            ++  loseAllOn "global"
            ++  loseDeallocOn "local"
      runTest4Expecting (runTest4Final test4Bracket) $ \ios globals locals -> do
        ios `shouldBe` bracketPreserveAllOnNoError ++ iosShouldBe
        globals `shouldBe` bracketPreserveAllOnNoError ++ globalsShouldBe
        locals `shouldBe` bracketPreserveAllOnNoError ++ localsShouldBe

      runTest4Expecting (runTest4Final test4BracketOnError) $ \ios globals locals -> do
        ios `shouldBe` bracketOnErrorPreserveAllOnNoError ++ iosShouldBe
        globals `shouldBe` bracketOnErrorPreserveAllOnNoError ++ globalsShouldBe
        locals `shouldBe` bracketOnErrorPreserveAllOnNoError ++ localsShouldBe

------------------------------------------------------------------------------


runTest
  :: Sem '[Error (), Resource, State [Char], Trace] a
  -> IO ([String], ([Char], Either () a))
runTest = pure
        . run
        . runTraceList
        . runState ""
        . runResource
        . runError @()

runTest2
  :: Sem '[Error (), Resource, State [Char], Trace, Output String, Embed IO] a
  -> IO ([String], ([Char], Either () a))
runTest2 = runM
         . ignoreOutput
         . runTraceList
         . runState ""
         . resourceToIO
         . runError @()

runTest3
  :: Sem '[Error (), Resource, State [Char], Trace, Output String, Embed IO, Final IO] a
  -> IO ([String], ([Char], Either () a))
runTest3 = runFinal
         . embedToFinal
         . outputToIOMonoid (:[])
         . traceToOutput
         . stateToIO ""
         . resourceToIOFinal
         . runError @()


testAllThree
    :: String
    -> (([String], ([Char], Either () a)) -> Expectation)
    -> (Sem '[Error (), Resource, State [Char], Trace] a)
    -> Spec
testAllThree name k m = do
  describe name $ do
    it "via runResource" $ do
      z <- runTest m
      k z
    -- NOTE(sandy): These unsafeCoerces are safe, because we're just weakening
    -- the end of the union
    it "via resourceToIO" $ do
      z <- runTest2 $ unsafeCoerce m
      k z
    it "via resourceToIOFinal" $ do
      z <- runTest3 $ unsafeCoerce m
      k z


testTheIOTwo
    :: String
    -> (([String], ([Char], Either () a)) -> Expectation)
    -> (Sem '[Error (), Resource, State [Char], Trace, Output String, Embed IO] a)
    -> Spec
testTheIOTwo name k m = do
  describe name $ do
    it "via resourceToIO" $ do
      z <- runTest2 m
      k z
    -- NOTE(sandy): This unsafeCoerces are safe, because we're just weakening
    -- the end of the union
    it "via resourceToIOFinal" $ do
      z <- runTest3 $ unsafeCoerce m
      k z


withTransaction :: (Member Resource r, Member Trace r) => Sem r a -> Sem r a
withTransaction m =
  bracketOnError
    (trace "beginning transaction")
    (const $ trace "rolling back transaction")
    (const $ m <* trace "committing transaction")



runTest4Expecting
  :: IO ([String], Either String ([String], Either Bool ([String], Either () ())))
  -> ([String] -> [String] -> [String] -> Expectation)
  -> Expectation
runTest4Expecting testRun expectations = do
  (ioEffs, rest) <- testRun
  rest `shouldSatisfy` isRight
  case rest of
    Right (globalEffs, rest') -> do
      rest' `shouldSatisfy` isRight
      case rest' of
        Right (localEffs, rest'') -> do
          rest'' `shouldBe` Right ()
          expectations ioEffs globalEffs localEffs
        _ -> pure ()
    _ -> pure ()


test4Bracket
  :: forall r
   . Members '[
      Output String  -- IO stateful effect
    , State [String] -- Global pure stateful effect
    , Trace          -- Local pure stateful effect
    , Error String   -- IO exceptions
    , Error Bool     -- Global exceptions
    , Error ()       -- Local exceptions
    , Resource
    ] r
  => Sem r ()
test4Bracket = do
  let
    record :: String -> Sem r ()
    record str = do
      trace str
      modify' (++[str])
      output str

  -- On no exceptions
  bracket
    (record "alloc pure")
    (\_ -> record "dealloc pure")
    (\_ -> record "use pure")

  -- On IO exception
  bracket
    (record "alloc IO")
    (\_ -> record "dealloc IO")
    (\_ -> record "use IO" >> throw "")
      `catch` \"" -> pure ()

  -- On global exception
  bracket
    (record "alloc global")
    (\_ -> record "dealloc global")
    (\_ -> record "use global" >> throw True)
      `catch` \True -> pure ()

  -- On local exception
  bracket
    (record "alloc local")
    (\_ -> record "dealloc local")
    (\_ -> record "use local" >> throw ())
      `catch` \() -> pure ()

test4BracketOnError
  :: forall r
   . Members '[
      Output String  -- IO stateful effect
    , State [String] -- Global pure stateful effect
    , Trace          -- Local pure stateful effect
    , Error String   -- IO exceptions
    , Error Bool     -- Global exceptions
    , Error ()       -- Local exceptions
    , Resource
    ] r
  => Sem r ()
test4BracketOnError = do
  let
    record :: String -> Sem r ()
    record str = do
      trace str
      modify' (++[str])
      output str

  -- On no exceptions
  bracketOnError
    (record "alloc pure")
    (\_ -> record "dealloc pure")
    (\_ -> record "use pure")

  -- On IO exception
  bracketOnError
    (record "alloc IO")
    (\_ -> record "dealloc IO")
    (\_ -> record "use IO" >> throw "")
      `catch` \"" -> pure ()

  -- On global exception
  bracketOnError
    (record "alloc global")
    (\_ -> record "dealloc global")
    (\_ -> record "use global" >> throw True)
      `catch` \True -> pure ()

  -- On local exception
  bracketOnError
    (record "alloc local")
    (\_ -> record "dealloc local")
    (\_ -> record "use local" >> throw ())
      `catch` \() -> pure ()

runTest4Pure
  :: Sem '[
       Error ()
     , Trace
     , Resource
     , Error Bool
     , Output String
     , Error String
     , State [String]
     , Embed IO
     , Final IO
     ] ()
  -> IO ([String], Either String ([String], Either Bool ([String], Either () ())))
runTest4Pure =
    runFinal
  . embedToFinal
  . stateToIO @[String] []
  . errorToIOFinal @String
  . runOutputList @String
  . runError @Bool
  . runResource
  . runTraceList
  . runError @()

runTest4Forklift
  :: Sem '[
       Error ()
     , Trace
     , Resource
     , Error Bool
     , Output String
     , Error String
     , State [String]
     , Embed IO
     , Final IO
     ] ()
  -> IO ([String], Either String ([String], Either Bool ([String], Either () ())))
runTest4Forklift =
    runFinal
  . embedToFinal
  . stateToIO @[String] []
  . errorToIOFinal @String
  . runOutputList @String
  . runError @Bool
  . resourceToIO
  . runTraceList
  . runError @()

runTest4Final
  :: Sem '[
       Error ()
     , Trace
     , Resource
     , Error Bool
     , Output String
     , Error String
     , State [String]
     , Embed IO
     , Final IO
     ] ()
  -> IO ([String], Either String ([String], Either Bool ([String], Either () ())))
runTest4Final =
    runFinal
  . embedToFinal
  . stateToIO @[String] []
  . errorToIOFinal @String
  . runOutputList @String
  . runError @Bool
  . resourceToIOFinal
  . runTraceList
  . runError @()
