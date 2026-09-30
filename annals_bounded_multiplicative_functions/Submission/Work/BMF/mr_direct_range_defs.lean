import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Range-generalised Buchstab vocabulary

`Work.BMF.mrDirect.dirPolyM` and `Work.BMF.mrDirect.remPoly` are tied to the dyadic range
`[X,2X]` (as in Matomäki–Radziwiłł's Lemma `lem:decomp`).  The target statement
`Work.BMF.mr_dirichlet_L2_direct` however sums over `[Y,3Y]`, so the Buchstab decomposition
is needed for a general range `[X₁,X₂]` with bounded ratio.

This file only fixes the notation:

* `dirPolyR a X₁ X₂ t = Σ_{X₁ ≤ n ≤ X₂} a n · n^{-(1+it)}`;
* `remPolyR b P Q K X₁ X₂ j t`
  `= Σ_{X₁ e^{-(j+1)/K} ≤ m ≤ X₂ e^{-j/K}} b m · (ω(m;P,Q)+1)^{-1} · m^{-(1+it)}`.

For `X₂ = 2 X₁` they reduce (up to the `e^{-1/K}` boundary) to `dirPolyM` and `remPoly`.
-/

set_option autoImplicit false

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace mrDirect

noncomputable section

/-- The Dirichlet polynomial `Σ_{X₁ ≤ n ≤ X₂} a n · n^{-(1+it)}` over a general range. -/
def dirPolyR (a : ℕ → ℂ) (X₁ X₂ t : ℝ) : ℂ :=
  ∑ n ∈ natIcc X₁ X₂, a n * (n : ℂ) ^ (-(1 + Complex.I * t))

/-- The remainder polynomial of the Buchstab decomposition, for a general range
`[X₁,X₂]` of the decomposed polynomial: the `m`'s run over the interval
`[X₁ e^{-(j+1)/K}, X₂ e^{-j/K}]`. -/
def remPolyR (b : ℕ → ℂ) (P Q K X₁ X₂ : ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ natIcc (X₁ * Real.exp (-((j : ℝ) + 1) / K)) (X₂ * Real.exp (-(j : ℝ) / K)),
    b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ * (m : ℂ) ^ (-(1 + Complex.I * t))

end

end mrDirect

end Work.BMF
