import Mathlib

/-!
# The clamped extension of a function away from a set

For `Ω ⊆ ℂ`, `V : ℂ → ℝ` and `C : ℝ` we define `clampExt Ω V C : ℂ → ℝ` by

`clampExt Ω V C z = if z ∈ Ω then max (V z) C else C`.

On `Ω` this is the pointwise maximum of `V` and the constant `C`; outside `Ω` it is the constant
`C`.  This is the tool that turns a boundary *limsup* bound for `V` into an honest global
continuity statement for `max (V ·) C`: if `V` has limsup `≤ C` at every frontier point of `Ω`,
then `clampExt Ω V C` is continuous.
-/

open Classical

namespace Work.TMComp.RedC8

/-- The function agreeing with `max (V ·) C` on `Ω` and equal to `C` outside `Ω`. -/
noncomputable def clampExt (Ω : Set ℂ) (V : ℂ → ℝ) (C : ℝ) : ℂ → ℝ :=
  fun z => if z ∈ Ω then max (V z) C else C

@[simp] lemma clampExt_of_mem {Ω : Set ℂ} {V : ℂ → ℝ} {C : ℝ} {z : ℂ} (hz : z ∈ Ω) :
    clampExt Ω V C z = max (V z) C := if_pos hz

@[simp] lemma clampExt_of_notMem {Ω : Set ℂ} {V : ℂ → ℝ} {C : ℝ} {z : ℂ} (hz : z ∉ Ω) :
    clampExt Ω V C z = C := if_neg hz

end Work.TMComp.RedC8
