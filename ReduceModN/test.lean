import ReduceModN.Basic

-- Example 1: Basic success case (n=4)
example : ¬ (∃ (x y : ℤ), x^2 + y^2 = 7) := by
  -- searchModN will run from 2 to 50, fail at 2, 3, succeed at 4, and stop.
  reduceModN 4

-- Example 2: Testing the configurable maximum (set to 3, so it fails)
set_option searchModN.max_modulus 3
example : ¬ (∃ (x y : ℤ), x^2 + y^2 = 7) := by
  -- searchModN will run from 2 to 3, fail at both, and report no solution found.
  searchModN
  -- The goal is left unsolved.

-- Example 3: Testing with a high max modulus (set to 100)
set_option searchModN.max_modulus 100
example : ¬ (∃ (x y : ℤ), x^2 + y^2 = 7) := by
  -- searchModN will run until 4 and then succeed, despite the max being 100.
  reduceModN 4

-- Example 4: Testing another basic Success case (n = 7)
example : ¬ ∃ (x y: ℤ), x^3 + 14*y^3 = 5 := by
  searchModN


example (A B : Prop) : A ∧ B := by
  apply And.intro
