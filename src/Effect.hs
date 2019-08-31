module Effect where

import Data.List
import Data.Maybe
import Data.Foldable
import Control.Monad.State
import Control.Monad.Identity
import qualified Parser as P
import qualified Lambda.Calculus as LC
import qualified Lambda.Inference as LI

type Description = (String, [(String, Int)])

-- Convert an effect, as given by the parser, into a list of declarations suited
-- to be added into the lambda context
effectIntoDeclarations :: String -> [P.EffFunction] -> LC.Environment -> ([(String, LC.Scheme)], Description)
effectIntoDeclarations effect functions g =
  (fmap worker functions, (effect, effectCases))
  where
    worker (P.EffFunction name params result) =
      -- For now we're ignoring generic effects (as they are not implemented in
      -- the parser yet), so we just map parameters and return types in a simple
      -- way
      (name, prepare $ declaration params result)

    prepare command =
      case runIdentity runInfererM of
        Right scheme ->
          scheme
        Left message ->
          error $ show message
      where
        runInfererM = LI.runInferer' $ do
          t <- command
          put 0
          result <- LI.instantiate $ LI.generalize g t
          return $ LI.generalize g result

    declaration [] result = do
      var <- LI.newTypeVar
      return $ LC.Arrow LC.Unit (LC.Row (LC.Constant effect) var) (lift result)
    declaration params result = do
      initial <- bar
      res <- foldrM foo initial params
      return $ snd res
      where
        foo a (e, b) = do
          var <- LI.newTypeVar
          return (var, LC.Arrow (lift a) e b)

        bar = do
          var <- LI.newTypeVar
          return (LC.Row (LC.Constant effect) var, lift result)

    effectCases =
      fmap getEffectDescrition functions
      where
        getEffectDescrition (P.EffFunction name params _) =
          (name, length params)

    lift :: P.DeclarableType -> LC.Type
    lift (P.TypeVar) = error "unrecheable"
    lift (P.TypeInt) = LC.Int
    lift (P.TypeBool) = LC.Bool
    lift (P.TypeString) = LC.String
    lift (P.TypeUnit) = LC.Unit

decideEffectHandler :: [P.HandlerCase] -> [Description] -> Description
decideEffectHandler [] _ =
  error "Handler doesn't have any cases"
decideEffectHandler [P.HandlerPure _ _] _ =
  error "This handler doesn't cover any case"
decideEffectHandler _ [] =
  error "This handler didn't match any known effect"
decideEffectHandler cases (desc@(_, params):descs) =
  if length (filter isPureCase cases) > 1 then
    error "There is more than one pure case in this handler"
  else
    let desc_names = fmap fst params in
    let actual_cases = mapMaybe getName cases in
    -- If we have any overlapping case, this is at best the handler we want
    if length (desc_names `intersect` actual_cases) > 0 then
      -- Bingo
      let missing = desc_names \\ actual_cases in
      if length missing > 0 then
        error $ "There are missing cases in this handler: " ++ intercalate ", " missing
      else
        let extra = actual_cases \\ desc_names in
        if length extra > 0 then
          error $ "There are erroneous cases in this handler: " ++ intercalate "," extra
        else
          -- TODO: verify arity here
          desc
    else
      -- Keep searching
      decideEffectHandler cases descs
  where
    isPureCase (P.HandlerPure _ _) = True
    isPureCase _ = False

    getName (P.HandlerPure _ _) = Nothing
    getName (P.HandlerCase name _ _) = Just name