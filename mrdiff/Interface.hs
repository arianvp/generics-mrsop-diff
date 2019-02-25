module Interface where

data Language :: * where
  Language :: { ext :: String
              , parser :: FilePath -> IO (Either String (Fix ki codes ix))
              } -> Language
