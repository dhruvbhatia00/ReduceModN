import ReduceModN.Basic

example : ¬ (∃ (x y : ℤ), x^2 + y^2 = 7) := by
  reduceModN 4

set_option searchModN.max_modulus 50
example : ¬ (∃ (x y : ℤ), x^2 + y^2 = 7) := by
  searchModN

/--
error: searchModN failed to find a working modulus between 2 and 3. The max_modulus for this tactic was set to 3. You can change this using 'set_option searchModN.max_modulus'.
---
error: unsolved goals
⊢ ¬∃ x y, x ^ 2 + y ^ 2 = 7
-/
#guard_msgs in
example : ¬ (∃ (x y : ℤ), x^2 + y^2 = 7) := by
  set_option searchModN.max_modulus 3 in
  searchModN

example : ¬ ∃ (x y: ℤ), x^3 + 14*y^3 = 5 := by
  searchModN

example : ¬ (∃ (x y : ℤ), x^4 + y^7 = 43) := by
  searchModN

/--
error: searchModN failed to find a working modulus between 2 and 50. The max_modulus for this tactic was set to 50. You can change this using 'set_option searchModN.max_modulus'.
---
error: unsolved goals
⊢ ¬∃ x y, x ^ 2 + y ^ 2 = 176
-/
#guard_msgs in
example : ¬ ∃ x y : ℤ, x^2 + y^2 = 176 := by
  searchModN

set_option searchModN.max_modulus 64 in
-- Searching up to `64` needs a higher recursion limit than Lean's default.
set_option maxRecDepth 10000 in
example : ¬ ∃ x y : ℤ, x^2 + y^2 = 176 := by
  searchModN
