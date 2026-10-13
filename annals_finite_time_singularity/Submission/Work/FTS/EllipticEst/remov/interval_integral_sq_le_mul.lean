import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory

/-- If two real functions agree on the open interval `Ioo a b`, then they are equal almost
everywhere for the Lebesgue measure restricted to `Ioc a b`: the two sets differ only by the
single point `b`. -/
lemma ae_eq_of_eq_on_Ioo {F G : ℝ → ℝ} {a b : ℝ} (h : ∀ x ∈ Set.Ioo a b, F x = G x) :
    F =ᵐ[volume.restrict (Set.Ioc a b)] G := by
  show ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), F x = G x
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := b))
  intro x hx
  change ¬(x ∈ Set.Ioc a b → F x = G x) at hx
  obtain ⟨hxI, hxne⟩ := not_imp.mp hx
  rw [Set.mem_singleton_iff]
  by_contra hxb
  exact hxne (h x (by
    rw [Set.mem_Ioo]
    exact ⟨(Set.mem_Ioc.mp hxI).1, lt_of_le_of_ne (Set.mem_Ioc.mp hxI).2 hxb⟩))

/-- Weighted Cauchy–Schwarz (Bunyakovsky) inequality for interval integrals: if `σ > 0` on
`(a,b)` and both `f²σ` and `σ⁻¹` are integrable on `(a,b]`, then
`(∫_a^b f)² ≤ (∫_a^b f²σ)(∫_a^b σ⁻¹)`.

No measurability of `f` is assumed: the bound is obtained by writing `|f| = √(f²σ)·√(σ⁻¹)`,
which exhibits `f` as a product of two genuine `L²` functions, and applying Cauchy–Schwarz to
them; the sign of `f` is handled by `‖∫ f‖ ≤ ∫ ‖f‖`. -/
theorem interval_integral_sq_le_mul {f σ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hσ : ∀ s ∈ Set.Ioo a b, 0 < σ s)
    (hf : MeasureTheory.IntegrableOn (fun s => (f s) ^ 2 * σ s) (Set.Ioc a b))
    (hσi : MeasureTheory.IntegrableOn (fun s => (σ s)⁻¹) (Set.Ioc a b)) :
    (∫ s in a..b, f s) ^ 2 ≤ (∫ s in a..b, (f s) ^ 2 * σ s) * (∫ s in a..b, (σ s)⁻¹) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  have haesm_u : AEStronglyMeasurable (fun x : ℝ => Real.sqrt ((f x) ^ 2 * σ x))
      (volume.restrict (Set.Ioc a b)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have haesm_v : AEStronglyMeasurable (fun x : ℝ => Real.sqrt ((σ x)⁻¹))
      (volume.restrict (Set.Ioc a b)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hσi.aestronglyMeasurable
  have hsq_u : ∀ x ∈ Set.Ioo a b, (f x) ^ 2 * σ x = (Real.sqrt ((f x) ^ 2 * σ x)) ^ 2 :=
    fun x hx => (Real.sq_sqrt (mul_nonneg (sq_nonneg (f x)) (le_of_lt (hσ x hx)))).symm
  have hsq_v : ∀ x ∈ Set.Ioo a b, (σ x)⁻¹ = (Real.sqrt ((σ x)⁻¹)) ^ 2 :=
    fun x hx => (Real.sq_sqrt (inv_nonneg.mpr (le_of_lt (hσ x hx)))).symm
  have hmem_u : MemLp (fun x : ℝ => Real.sqrt ((f x) ^ 2 * σ x)) 2
      (volume.restrict (Set.Ioc a b)) :=
    (memLp_two_iff_integrable_sq haesm_u).mpr (hf.congr (ae_eq_of_eq_on_Ioo hsq_u))
  have hmem_v : MemLp (fun x : ℝ => Real.sqrt ((σ x)⁻¹)) 2 (volume.restrict (Set.Ioc a b)) :=
    (memLp_two_iff_integrable_sq haesm_v).mpr (hσi.congr (ae_eq_of_eq_on_Ioo hsq_v))
  have hI1 : (∫ x in Set.Ioc a b, Real.sqrt ((f x) ^ 2 * σ x) * Real.sqrt ((σ x)⁻¹))
      = ∫ x in Set.Ioc a b, |f x| :=
    integral_congr_ae (ae_eq_of_eq_on_Ioo (fun x hx => by
      have hxpos : 0 < σ x := hσ x hx
      rw [Real.sqrt_mul (sq_nonneg (f x)), Real.sqrt_sq_eq_abs, Real.sqrt_inv, mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hxpos)), mul_one]))
  have hI2 : (∫ x in Set.Ioc a b, (Real.sqrt ((f x) ^ 2 * σ x)) ^ 2)
      = ∫ x in Set.Ioc a b, (f x) ^ 2 * σ x :=
    integral_congr_ae (ae_eq_of_eq_on_Ioo (fun x hx => (hsq_u x hx).symm))
  have hI3 : (∫ x in Set.Ioc a b, (Real.sqrt ((σ x)⁻¹)) ^ 2)
      = ∫ x in Set.Ioc a b, (σ x)⁻¹ :=
    integral_congr_ae (ae_eq_of_eq_on_Ioo (fun x hx => (hsq_v x hx).symm))
  have hcs := Work.Spaces.cs_integral hmem_u hmem_v
  have hle : |∫ x in Set.Ioc a b, f x| ≤ ∫ x in Set.Ioc a b, |f x| := by
    simpa using MeasureTheory.norm_integral_le_integral_norm (fun x : ℝ => f x)
      (μ := volume.restrict (Set.Ioc a b))
  calc
    (∫ x in Set.Ioc a b, f x) ^ 2 = |∫ x in Set.Ioc a b, f x| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x in Set.Ioc a b, |f x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
    _ = (∫ x in Set.Ioc a b, Real.sqrt ((f x) ^ 2 * σ x) * Real.sqrt ((σ x)⁻¹)) ^ 2 := by
          rw [hI1]
    _ ≤ (∫ x in Set.Ioc a b, (Real.sqrt ((f x) ^ 2 * σ x)) ^ 2) *
          (∫ x in Set.Ioc a b, (Real.sqrt ((σ x)⁻¹)) ^ 2) := hcs
    _ = (∫ x in Set.Ioc a b, (f x) ^ 2 * σ x) * (∫ x in Set.Ioc a b, (σ x)⁻¹) := by
          rw [hI2, hI3]

end Work.FTS.EllipticEst.remov
