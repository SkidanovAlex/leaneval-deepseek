import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP

/-- Off `z = 0` the `z`-weight of the "flat price" collapses to `(1+z)^{-2}`:
`w(z)² · (z²/(1+z)³)² = (1+z)^{-2}`. -/
theorem w_sq_mul_flat_sq (z : ℝ) (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 * (z ^ 2 / (1 + z) ^ 3) ^ 2 = ((1 + z) ^ 2)⁻¹ := by
  rw [Work.Spaces.w]
  field_simp

/-- The line `{z = 0}` is null in `ℝ²`. -/
theorem volume_fst_eq_zero : (volume : Measure (ℝ × ℝ)) {p | p.1 = 0} = 0 := by
  have h : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ Set.univ := by ext p; simp
  rw [h, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  simp

theorem zWeight_flat (b : ℝ → ℝ) (B : ℝ)
    (hbint : MeasureTheory.IntegrableOn b Work.Spaces.Iθ)
    (hble : (∫ θ in Work.Spaces.Iθ, b θ) ≤ B) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) ∧
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) ≤ B := by
  set s : Set (ℝ × ℝ) := Work.Spaces.Iz ×ˢ Work.Spaces.Iθ with hs
  -- null set where the pointwise collapse fails
  have hae0 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_fst_eq_zero
  -- a.e. the integrand is `b θ · (1+z)^{-2}`
  have hae : (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2)
      =ᵐ[volume.restrict s]
      (fun p : ℝ × ℝ => ((1 + p.1) ^ 2)⁻¹ * b p.2) := by
    filter_upwards [hae0.filter_mono MeasureTheory.ae_restrict_le] with p hp
    calc (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2
        = ((Work.Spaces.w p.1) ^ 2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) * b p.2 := by ring
      _ = ((1 + p.1) ^ 2)⁻¹ * b p.2 := by rw [w_sq_mul_flat_sq p.1 hp]
  -- the `z`-factor `(1+z)^{-2}` is integrable on `Iz` with integral `1`
  have hGint : IntegrableOn (fun p : ℝ × ℝ => ((1 + p.1) ^ 2)⁻¹ * b p.2) s := by
    rw [hs]
    exact Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
      (f := fun z : ℝ => ((1 + z) ^ 2)⁻¹) (g := b)
      integrableOn_inv_sq_Iz hbint
  have hvalG : ∫ p in s, ((1 + p.1) ^ 2)⁻¹ * b p.2
      = (∫ z in Work.Spaces.Iz, ((1 + z) ^ 2)⁻¹) * (∫ θ in Work.Spaces.Iθ, b θ) := by
    rw [hs, Measure.volume_eq_prod ℝ ℝ]
    exact setIntegral_prod_mul (fun z : ℝ => ((1 + z) ^ 2)⁻¹) b
      Work.Spaces.Iz Work.Spaces.Iθ
  constructor
  · exact hGint.congr hae.symm
  · calc ∫ p in s, (Work.Spaces.w p.1) ^ 2 * b p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2
        = ∫ p in s, ((1 + p.1) ^ 2)⁻¹ * b p.2 := integral_congr_ae hae
      _ = (∫ z in Work.Spaces.Iz, ((1 + z) ^ 2)⁻¹) * (∫ θ in Work.Spaces.Iθ, b θ) := hvalG
      _ = 1 * (∫ θ in Work.Spaces.Iθ, b θ) := by rw [integral_inv_sq_Iz]
      _ ≤ B := by simpa using hble

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP
