import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory

/-- **Integrability of the weighted dilated profile** (`0 < ε`): if `Φ` has an integrable first
moment then so does its dilation `u ↦ (ε^3)⁻¹ • Φ (ε⁻¹ • u)`:
`Integrable (fun η => (1 + ‖η‖) * ‖(ε^3)⁻¹ • Φ (ε⁻¹ • η)‖)`.
Hints (`open MeasureTheory`).  Write `c := (ε^3)⁻¹` (so `c > 0`) and set
`g v := (1 + ε * ‖v‖) * (c * ‖Φ v‖)`.  Then the pointwise identity
`g (ε⁻¹ • η) = (1 + ‖η‖) * ‖c • Φ (ε⁻¹ • η)‖` holds (use `norm_smul`, `norm_inv`, `norm_smul` on
`ε⁻¹ • η`, `Real.norm_of_nonneg`, `mul_comm`/`mul_assoc`, and `ε * ε⁻¹ = 1` from `hε`), and
`g v ≤ (1 + ε) * (c * ((1 + ‖v‖) * ‖Φ v‖))` pointwise (`nlinarith` from `0 < ε`, `0 ≤ ‖v‖`).
So `Integrable g` by `MeasureTheory.Integrable.mono'` from `hΦm.const_mul c` (multiplying an
integrable function by the constant `(1+ε)*c`) together with the a.e. strong measurability of `g`
built from a.e. strong measurability of `‖Φ ·‖` and continuity of `v ↦ (1 + ε * ‖v‖) * c`; note
`AEStronglyMeasurable (fun v => ‖Φ v‖)` follows from `hΦ.aestronglyMeasurable` (or from `hΦm`
via `MeasureTheory.AEStronglyMeasurable.norm`-style API: `‖Φ v‖ = ((1+‖v‖)*‖Φ v‖)/(1+‖v‖)`).
Finally `Integrable (fun η => g (ε⁻¹ • η))` is `MeasureTheory.Integrable.comp_smul hg (hε.ne')`.
(Be careful with the `ε⁻³` factor: it does *not* cancel against `(1+ε)`.) -/
theorem scaled_moment_integrable {Φ : EuclideanSpace ℝ (Fin 3) → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hΦ : MeasureTheory.Integrable Φ)
    (hΦm : MeasureTheory.Integrable (fun η => (1 + ‖η‖) * ‖Φ η‖)) :
    MeasureTheory.Integrable (fun η => (1 + ‖η‖) * ‖(ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)‖) := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hcnn : (0 : ℝ) ≤ (ε ^ 3)⁻¹ := by positivity
  -- strong measurability of `‖Φ ·‖`, hence of the weight `v ↦ (1 + ε * ‖v‖) * (c * ‖Φ v‖)`
  have hΦnorm : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin 3) => ‖Φ v‖) :=
    hΦ.aestronglyMeasurable.norm
  have hgmeas : AEStronglyMeasurable
      (fun v : EuclideanSpace ℝ (Fin 3) => (1 + ε * ‖v‖) * ((ε ^ 3)⁻¹ * ‖Φ v‖)) := by
    have h1 : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin 3) => (ε ^ 3)⁻¹ * ‖Φ v‖) :=
      hΦnorm.const_mul _
    have h2 : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin 3) => (1 : ℝ) + ε * ‖v‖) :=
      (continuous_const.add (continuous_norm.const_mul ε)).aestronglyMeasurable
    exact h2.mul h1
  -- the weighted profile `g v = (1 + ε * ‖v‖) * (c * ‖Φ v‖)` is integrable, dominated by
  -- `(1 + ε) * (c * ((1 + ‖v‖) * ‖Φ v‖))`
  have hg : Integrable
      (fun v : EuclideanSpace ℝ (Fin 3) => (1 + ε * ‖v‖) * ((ε ^ 3)⁻¹ * ‖Φ v‖)) := by
    refine Integrable.mono' ((hΦm.const_mul ((ε ^ 3)⁻¹)).const_mul (1 + ε)) hgmeas ?_
    filter_upwards with v
    have ha : 0 ≤ ‖v‖ := norm_nonneg v
    have hb : 0 ≤ ‖Φ v‖ := norm_nonneg _
    have hcb : 0 ≤ (ε ^ 3)⁻¹ * ‖Φ v‖ := mul_nonneg hcnn hb
    have h1 : 1 + ε * ‖v‖ ≤ (1 + ε) * (1 + ‖v‖) := by nlinarith [hε, ha]
    rw [Real.norm_of_nonneg (by positivity)]
    calc (1 + ε * ‖v‖) * ((ε ^ 3)⁻¹ * ‖Φ v‖)
        ≤ ((1 + ε) * (1 + ‖v‖)) * ((ε ^ 3)⁻¹ * ‖Φ v‖) :=
          mul_le_mul_of_nonneg_right h1 hcb
      _ = (1 + ε) * ((ε ^ 3)⁻¹ * ((1 + ‖v‖) * ‖Φ v‖)) := by ring
  -- dilate: `g (ε⁻¹ • ·)` is integrable, and equals the target weight pointwise
  have hcomp := hg.comp_smul (inv_ne_zero hεne)
  refine hcomp.congr (Filter.Eventually.of_forall fun η => ?_)
  show (1 + ε * ‖ε⁻¹ • η‖) * ((ε ^ 3)⁻¹ * ‖Φ (ε⁻¹ • η)‖)
      = (1 + ‖η‖) * ‖(ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)‖
  have hnorm_inv : ‖ε⁻¹‖ = ε⁻¹ := Real.norm_of_nonneg (by positivity)
  have hnorm_scalar : ‖(ε ^ 3)⁻¹‖ = (ε ^ 3)⁻¹ := Real.norm_of_nonneg hcnn
  simp only [norm_smul, hnorm_inv, hnorm_scalar]
  have hinner : ε * (ε⁻¹ * ‖η‖) = ‖η‖ := by
    rw [← mul_assoc, mul_inv_cancel₀ hεne, one_mul]
  rw [hinner]

end Work.BoseBogFS
