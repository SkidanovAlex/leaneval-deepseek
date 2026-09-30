import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the pointwise remainder bound `remPointwise_le`

The pointwise bound `Work.BMF.mr_direct.remPointwise_le` controls the weighted window sum

`∑_{X ≤ m ≤ 2X} g m · (ω(m;P,Q)+1)^{-1} · m^{-(1+it)}`.

The weight is not multiplicative, so it is linearised by the integral identity

`(ω+1)^{-1} = ∫_0^1 x^ω dx`,

which rewrites the sum as the integral over `x ∈ [0,1]` of the *multiplicative* weight
`x^{ω(m;P,Q)}`.  This file only fixes the notation:

* `omegaPow P Q x m = x^{ω(m;P,Q)}`;
* `omegaWeighted g P Q x = m ↦ x^{ω(m;P,Q)} · g m` (multiplicative when `g` is);
* `omegaWindowSum g P Q X t x = ∑_{m ∈ [X,2X]} x^{ω(m;P,Q)} g m m^{-(1+it)}`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- `x ^ ω(m;P,Q)`, the multiplicative weight whose average over `x ∈ [0,1]` recovers the
non-multiplicative weight `(ω(m;P,Q)+1)^{-1}`. -/
def omegaPow (P Q : ℝ) (x : ℂ) (m : ℕ) : ℂ := x ^ Work.BMF.mrDirect.omegaCount P Q m

/-- The `ω`-weighted multiplicative function `m ↦ x^{ω(m;P,Q)} · g m`. -/
def omegaWeighted (g : ℕ → ℂ) (P Q : ℝ) (x : ℂ) : ℕ → ℂ :=
  fun m ↦ omegaPow P Q x m * g m

/-- The `ω`-weighted pointwise Dirichlet polynomial
`∑_{m ∈ [X,2X]} x^{ω(m;P,Q)} g m m^{-(1+it)}`. -/
def omegaWindowSum (g : ℕ → ℂ) (P Q X t : ℝ) (x : ℂ) : ℂ :=
  ∑ m ∈ Work.BMF.natIcc X (2 * X),
    omegaWeighted g P Q x m * (m : ℂ) ^ (-(1 + Complex.I * t))

end

end Work.BMF.mr_direct
