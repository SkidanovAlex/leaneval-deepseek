/-
# The basic objects of the Weyl/Liouville pair lemma

This module holds the definitions used by `Work.FTS.PressureOn.weyl_pair` and by the auxiliary
lemmas about them, so that those auxiliary lemmas can be stated and proved *without* importing
`weyl_pair` itself (which would be circular, since `weyl_pair` consumes them).

* `Dpair q Φ f = ∫ ⟪Φ, f⟫ + ∫ q · div f` is the pairing of the distribution `D = Φ - ∇q`;
* `bump n`, `rho n` are the mollifier bumps (with `rOut → 0` and `∫ rho n = 1`), and
* `moll n g`, `mollV n G` the induced scalar/vector mollifications.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

noncomputable section

/-- The pairing `⟨D, f⟩ = ∫ ⟪Φ, f⟫ + ∫ q · div f` of the distribution `D := Φ - ∇q` against the
test field `f`.  (`hdiv` says `⟨D, ∇φ⟩ = 0` and `hcurl` that `⟨D, ∇×ψ⟩ = 0`.) -/
def Dpair (q : R3 → ℝ) (Φ : R3 → R3) (f : R3 → R3) : ℝ :=
  (∫ x, inner ℝ (Φ x) (f x)) + ∫ x, q x * FiniteTimeSingularity.div f x

theorem Dpair_apply (q : R3 → ℝ) (Φ : R3 → R3) (f : R3 → R3) :
    Dpair q Φ f = (∫ x, inner ℝ (Φ x) (f x)) + ∫ x, q x * FiniteTimeSingularity.div f x :=
  rfl

/-- The mollifier bump at scale `n`: the `ContDiffBump` at the origin with `rIn = 1/(n+2)` and
`rOut = 1/(n+1)`. -/
noncomputable def bump (n : ℕ) : ContDiffBump (0 : R3) :=
  ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1),
    by positivity,
    by
      rw [one_div, one_div, inv_lt_inv₀ (by positivity) (by positivity)]
      linarith⟩

/-- The normalised bump at scale `n`: a smooth nonnegative function with `∫ rho n = 1`. -/
noncomputable def rho (n : ℕ) : R3 → ℝ := (bump n).normed MeasureTheory.volume

/-- Scalar mollification at scale `n`. -/
noncomputable def moll (n : ℕ) (g : R3 → ℝ) : R3 → ℝ :=
  MeasureTheory.convolution (rho n) g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

/-- Vector mollification at scale `n`. -/
noncomputable def mollV (n : ℕ) (G : R3 → R3) : R3 → R3 :=
  MeasureTheory.convolution (rho n) G (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

end

end Work.FTS.PressureOn
