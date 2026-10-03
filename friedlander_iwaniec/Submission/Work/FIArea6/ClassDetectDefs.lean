/-
# `Submission.Work.FIArea6.ClassDetectDefs` — the modulus-8 character detection, vocabulary

*FI* §16, remark after (16.25): "the congruence (5.7) can be detected by characters to modulus
eight so we can relax it by changing `χ` in `ψ`", the detected character having modulus
`lcm(4d,8) = 4·lcm(d,2)`.

This module fixes the vocabulary of that detection:

* `G8` — the finite abelian group `(ℤ[i]/8ℤ[i])^*` of units of the Gaussian integers modulo eight,
  in coordinates `(ZMod 8)²` with the multiplication `gaussMul` of `Work.FIArea7.GaussUnits`;
* `char8Of` — the multiplicative character `ℤ[i] → ℂ` modulo eight attached (through the duality
  `Work.FIArea7.chiEquivAddChar` at modulus `4·2 = 8`) to an additive character of `G8`.

The detection identity itself (`classDetect8Gauss`) and the elementary extraction lemmas about
`char8Of` are proved in `Submission.Work.FIArea6.classDetect8Gauss`; the multiplicativity of the
product with a strict character is in `Submission.Work.FIArea6.strictChar8_mul`.
-/
import Mathlib
import Submission.Work.FIArea7.ChiEquivAddChar
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The Gaussian unit group modulo eight**: the units of `ℤ[i]/8ℤ[i]`, in coordinates.  The
multiplication is `Work.FIArea7.gaussMul` (the group instance is in `Work.FIArea7.GaussUnits`). -/
abbrev G8 : Type := {p : ZMod 8 × ZMod 8 // IsUnit (Work.FIArea7.gaussNorm p)}

/-- **The character of `ℤ[i]` modulo eight attached to an additive character of `G8`.**  It is the
`chi`-side of the duality `Work.FIArea7.chiEquivAddChar` at modulus `4·2 = 8`: a function
`ℤ[i] → ℂ` which is multiplicative, periodic modulo eight, bounded by one, and vanishes off the
classes coprime to eight (the `IsCharMod4dStrict 2` class of functions). -/
def char8Of (ψ : AddChar (Additive G8) ℂ) : GaussianInt → ℂ :=
  ((Work.FIArea7.chiEquivAddChar 2 (by norm_num)).symm ψ).1

end

end Work.FIArea6
