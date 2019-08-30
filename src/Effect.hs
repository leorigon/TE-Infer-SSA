module Effect where

  import Data.Foldable
  import Control.Monad.State
  import Control.Monad.Identity
  import qualified Parser as P
  import qualified Lambda.Calculus as LC
  import qualified Lambda.Inference as LI
  
  -- Convert an effect, as given by the parser, into a list of declarations suited
  -- to be added into the lambda context
  effectIntoDeclarations :: String -> [P.EffFunction] -> LC.Environment -> [(String, LC.Scheme)]
  effectIntoDeclarations effect functions g =
    fmap worker functions
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
        return $ LC.Arrow LC.Unit (LC.Constant effect) (lift result)
      declaration params result = do
        initial <- bar
        res <- foldrM foo initial params
        return $ snd res
        where
          --foo :: Monad m =>  P.DeclarableType -> (LC.Type, LC.Type) -> m (LC.Type, LC.Type)
          foo a (e, b) = do
            var <- LI.newTypeVar
            return (var, LC.Arrow (lift a) e b)
  
          --bar :: (LC.Type, LC.Type)
          bar = do
            var <- LI.newTypeVar
            return (LC.Row (LC.Constant effect) var, lift result)
  
      lift :: P.DeclarableType -> LC.Type
      lift (P.TypeVar) = error "unrecheable"
      lift (P.TypeInt) = LC.Int
      lift (P.TypeBool) = LC.Bool
      lift (P.TypeString) = LC.String
      lift (P.TypeUnit) = LC.Unit