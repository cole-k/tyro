module Utils where

import Data.Monoid (First(..))

-- | Searches for the first 'a' that produces a 'Just b' in 't' and then returns
-- that 'Just b'.
findWith :: (Foldable t) => (a -> Maybe b) -> t a -> Maybe b
findWith f = getFirst . foldMap (First . f)
