# ReduceModN

This project is a small Lean tactic experiment that I originally worked on a
while ago and only recently got around to cleaning up.

The main tactic, `reduceModN`, is meant for proving that certain Diophantine
equations have no integer solutions. Given a negated existential goal, it
introduces the purported solution, reduces the equation modulo `n`, and then
uses `decide` to solve the resulting finite problem in `ZMod n`.

The companion tactic `searchModN` automates the choice of modulus by trying
values of `n` from `2` up to a configurable bound.

## What It Does

The intended shape of goal is something like:

```lean
¬ ∃ x y : ℤ, x^2 + y^2 = 7
```

and then:

```lean
reduceModN 4
```

proves the goal by showing the equation has no solutions modulo `4`.

## Example

```lean
import ReduceModN.Basic

example : ¬ ∃ x y : ℤ, x^2 + y^2 = 7 := by
  reduceModN 4
```

You can also ask the tactic to search for a working modulus automatically:

```lean
import ReduceModN.Basic

example : ¬ ∃ x y : ℤ, x^3 + 14 * y^3 = 5 := by
  searchModN
```

The maximum modulus checked by `searchModN` is controlled by the option
`searchModN.max_modulus`, which defaults to `50`.
