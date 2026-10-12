import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `bsL2_le_of_bounded_support` — the `L²` mass of a bounded state supported in the box

If a real one-body state `h` is bounded by `C` in sup norm and vanishes outside the centred
box `acube ℓ` of volume `ℓ³`, then its unweighted `L²` mass is at most `C² · ℓ³`:

    `bsL2 h = ∫_z (h z)² ≤ C² · ℓ³`.

The proof dominates the (everywhere nonnegative) integrand `z ↦ (h z)²` pointwise by the
integrable function `C² · 1_{acube ℓ}` — the bound being `|h z| ≤ C` on the box and `h z = 0`
off it — and evaluates `∫_z C² · 1_{acube ℓ} = C² · vol(acube ℓ) = C² ℓ³`
(`acube_volume`).  No measurability of `h` is required: `integral_mono_of_nonneg` holds for
arbitrary functions (the non-integrable case contributes `0` by convention).
-/

noncomputable section

open MeasureTheory

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

theorem bsL2_le_of_bounded_support {ℓ : ℝ} (hℓ : 0 < ℓ)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, |h z| ≤ C)
    (hzero : ∀ z ∉ Submission.BoseGases.acube ℓ, h z = 0) :
    Work.BSKinetic.Decomp.bsL2 h ≤ C ^ 2 * ℓ ^ 3 := by
  set s := Submission.BoseGases.acube ℓ with hs
  have hs_meas : MeasurableSet s := Submission.BoseGases.acube_measurable ℓ
  have hs_lt : (volume : Measure ℝ³) s < ⊤ := by
    rw [hs]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le
  have hg_int : Integrable (s.indicator (fun _ : ℝ³ => C ^ 2)) (volume : Measure ℝ³) := by
    rw [integrable_indicator_iff hs_meas]
    exact integrableOn_const (ne_of_lt hs_lt) (by simp)
  have hf_nonneg : 0 ≤ᵐ[(volume : Measure ℝ³)] (fun z : ℝ³ => (h z) ^ 2) :=
    ae_of_all _ (fun z => sq_nonneg _)
  have hle : (fun z : ℝ³ => (h z) ^ 2)
      ≤ᵐ[(volume : Measure ℝ³)] (s.indicator (fun _ => C ^ 2)) := by
    apply ae_of_all
    intro z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz]
      rw [sq_le_sq, abs_of_nonneg hC]
      exact hb z
    · rw [Set.indicator_of_notMem hz]
      have hz0 : h z = 0 := hzero z hz
      simp [hz0]
  calc Work.BSKinetic.Decomp.bsL2 h
      = ∫ z : ℝ³, (h z) ^ 2 := rfl
    _ ≤ ∫ z : ℝ³, s.indicator (fun _ => C ^ 2) z :=
        integral_mono_of_nonneg hf_nonneg hg_int hle
    _ = C ^ 2 * ℓ ^ 3 := by
        rw [integral_indicator hs_meas, setIntegral_const, smul_eq_mul, Measure.real_def,
            hs, Submission.BoseGases.acube_volume ℓ hℓ.le,
            ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]
        ring

end Work.BSKinetic.Decomp
