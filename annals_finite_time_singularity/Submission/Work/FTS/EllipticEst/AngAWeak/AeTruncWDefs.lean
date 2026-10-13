import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak.AeTruncWDefs` — the vocabulary of the truncated `w²`-energy identity

This module fixes the objects used by the proof of

`Work.FTS.EllipticEst.AngAWeak.aeTruncIdentW`:

for `AeData α u G` (the almost-everywhere class of the level-`0` elliptic estimate), the
truncated `w²`-energy identity

`∫_z W w² (∫_θ G u) = α² ∫_z W w² z² (∫_θ (∂_zu)²) + ∫_z W w² (∫_θ (L₀u) u)
   - (α²/2) ∫_z (W w² z²)'' (∫_θ u²) + (α(5+α)/2) ∫_z (W w² z)' (∫_θ u²)`

holds for every `W ∈ C²` with compact support vanishing near `0`.

## The weight

* `sigW W z = W z · w z²` is the radial weight `σ` multiplying the solutions `u`;
* `sigW2 W z = z²·σ z` is the weight of `∂_zzu` (the `z²σ` of the integration by parts
  `∫ σ z² φ'' φ = ½∫ (σ z²)'' φ² - ∫ σ (z φ')²`);
* `sigW1 W z = z·σ z` is the weight of `∂_zu` (the `zσ` of `∫ σ z φ' φ = -½∫ (zσ)' φ²`).

## Getting rid of the irrelevant `z ≤ 0` and `z ≤ δ`

All the integrals of the identity are over `Set.Ioi 0`, while the norms of `Work.Spaces` are
stated over `Iz = [0,∞)`.  The two measures agree (`restrict_Iz_eq_restrict_Ioi`), and the
weight `σ` is supported in the region where `W ≠ 0`, which is why the whole identity can be
proved on a compact interval `[a,b]` containing the support of `W` in its interior
(`exists_bound_W` produces the upper end of that support).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The radial weight of the truncated identity: `σ(z) = W(z)·w(z)²`. -/
def sigW (W : ℝ → ℝ) : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2

/-- `σ(z)·z²`, the weight multiplying `∂_zzu` (the weight of `ibpZZ`). -/
def sigW2 (W : ℝ → ℝ) : ℝ → ℝ := fun z => z ^ 2 * sigW W z

/-- `σ(z)·z`, the weight multiplying `∂_zu` (the weight of `ibpZ`). -/
def sigW1 (W : ℝ → ℝ) : ℝ → ℝ := fun z => z * sigW W z

@[simp] theorem sigW_apply (W : ℝ → ℝ) (z : ℝ) :
    sigW W z = W z * (Work.Spaces.w z) ^ 2 := rfl

@[simp] theorem sigW2_apply (W : ℝ → ℝ) (z : ℝ) : sigW2 W z = z ^ 2 * sigW W z := rfl

@[simp] theorem sigW1_apply (W : ℝ → ℝ) (z : ℝ) : sigW1 W z = z * sigW W z := rfl

/-- The restricted Lebesgue measure on `Iz = [0,∞)` is the restricted Lebesgue measure on
`(0,∞)`: the two differ by the null set `{0}`. -/
theorem restrict_Iz_eq_restrict_Ioi :
    MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Set.Ici (0 : ℝ) :=
    MeasureTheory.Ioi_ae_eq_Ici
  have h2 := MeasureTheory.Measure.restrict_congr_set h
  exact h2.symm

/-- `z`-set integrals over `Iz = [0,∞)` and over `(0,∞)` agree. -/
theorem setIntegral_Iz_eq_Ioi (f : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, f z) = ∫ z in Set.Ioi (0 : ℝ), f z := by
  rw [← restrict_Iz_eq_restrict_Ioi]

/-- A `C²` function with compact support on `ℝ` is supported in `(-∞,R]` for some `R > 0`. -/
theorem exists_bound_W (W : ℝ → ℝ) (hcpt : HasCompactSupport W) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℝ, R ≤ z → W z = 0 := by
  obtain ⟨b, hb⟩ := hcpt.bddAbove
  refine ⟨max b 0 + 1, by positivity, fun z hz => ?_⟩
  by_contra hne
  have hmem : z ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hne)
  have h1 : z ≤ b := hb hmem
  have h2 : b ≤ max b 0 := le_max_left b 0
  linarith

end Work.FTS.EllipticEst.AngAWeak
