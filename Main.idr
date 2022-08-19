module Main

import PLFI.Part1.Naturals
import PLFI.Part1.Induction
import PLFI.Part1.Relations
import PLFI.Part1.Equality
import PLFI.Part1.Isomorphism
import PLFI.Part1.Connectives
import PLFI.Part1.Negation
import PLFI.Part1.Decidable


main : IO ()
main = do
  putStrLn "[x] Part1.Naturals"
  putStrLn "[x] Part1.Induction"
  putStrLn "[x] Part1.Relations"
  putStrLn "[x] Part1.Equality"
  putStrLn "[x] Part1.Isomorphism"
  putStrLn "[x] Part1.Connectives"
  putStrLn "[x] Part1.Negation"
  putStrLn "[ ] Part1.Decidable"
  Part1.Negation.test
