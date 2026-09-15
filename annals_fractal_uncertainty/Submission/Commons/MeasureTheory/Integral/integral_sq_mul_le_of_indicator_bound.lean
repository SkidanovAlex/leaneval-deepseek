import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory

theorem integral_sq_mul_le_of_indicator_bound {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨm : Measurable Ψ) (hΨ0 : ∀ x, 0 ≤ Ψ x)
    (hΨ1 : ∀ x, Ψ x ≤ 1) {c' C : ℝ} (hc' : 0 ≤ c') (hC : 0 < C)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U) (hΨU : ∀ x ∈ U, Ψ x ≤ c')
    (hbound : ∫ x, ‖f x‖ ^ 2 ≤ C ^ 2 * ∫ x in U, ‖f x‖ ^ 2) :
    ∫ x, Ψ x ^ 2 * ‖f x‖ ^ 2
      ≤ (1 - (1 - c' ^ 2) / C ^ 2) * ∫ x, ‖f x‖ ^ 2 := by
  have hg_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖f x‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hf.integrable_norm_pow (by norm_num)
  have hg_nn : ∀ x, 0 ≤ ‖f x‖ ^ 2 := fun x => sq_nonneg _
  have hΨsq_le_one : ∀ x, Ψ x ^ 2 ≤ 1 := fun x => by
    have := pow_le_pow_left₀ (hΨ0 x) (hΨ1 x) 2
    simpa using this
  have hh_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Ψ x ^ 2 * ‖f x‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    refine hg_int.mono' ((hΨm.pow_const 2).aestronglyMeasurable.mul hg_int.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (hg_nn x) (hΨsq_le_one x)
  set e : ℝ := min c' 1 with he
  have he_nn : 0 ≤ e := by rw [he]; exact le_min hc' zero_le_one
  have he_le_one : e ≤ 1 := by rw [he]; exact min_le_right _ _
  have he_le_c' : e ≤ c' := by rw [he]; exact min_le_left _ _
  have hesq_le_c'sq : e ^ 2 ≤ c' ^ 2 := pow_le_pow_left₀ he_nn he_le_c' 2
  have hesq_le_one : e ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ he_nn he_le_one 2
  have hU_le : ∀ x ∈ U, Ψ x ^ 2 * ‖f x‖ ^ 2 ≤ e ^ 2 * ‖f x‖ ^ 2 := by
    intro x hx
    have hxe : Ψ x ≤ e := by rw [he]; exact le_min (hΨU x hx) (hΨ1 x)
    have hs : Ψ x ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (hΨ0 x) hxe 2
    exact mul_le_mul_of_nonneg_right hs (hg_nn x)
  have hcompl_le : ∀ x ∈ Uᶜ, Ψ x ^ 2 * ‖f x‖ ^ 2 ≤ ‖f x‖ ^ 2 := by
    intro x _
    have := mul_le_of_le_one_left (hg_nn x) (hΨsq_le_one x)
    simpa using this
  have hU_bound : (∫ x in U, Ψ x ^ 2 * ‖f x‖ ^ 2) ≤ e ^ 2 * (∫ x in U, ‖f x‖ ^ 2) := by
    have h1 : (∫ x in U, Ψ x ^ 2 * ‖f x‖ ^ 2) ≤ (∫ x in U, e ^ 2 * ‖f x‖ ^ 2) :=
      setIntegral_mono_on hh_int.integrableOn (hg_int.const_mul (e ^ 2)).integrableOn hUm hU_le
    rwa [integral_const_mul] at h1
  have hcompl_bound : (∫ x in Uᶜ, Ψ x ^ 2 * ‖f x‖ ^ 2) ≤ (∫ x in Uᶜ, ‖f x‖ ^ 2) :=
    setIntegral_mono_on hh_int.integrableOn hg_int.integrableOn hUm.compl hcompl_le
  have hdecomp : (∫ x, Ψ x ^ 2 * ‖f x‖ ^ 2)
      = (∫ x in U, Ψ x ^ 2 * ‖f x‖ ^ 2) + (∫ x in Uᶜ, Ψ x ^ 2 * ‖f x‖ ^ 2) :=
    (integral_add_compl hUm hh_int).symm
  have hcompl_eq : (∫ x in Uᶜ, ‖f x‖ ^ 2) = (∫ x, ‖f x‖ ^ 2) - (∫ x in U, ‖f x‖ ^ 2) :=
    setIntegral_compl hUm hg_int
  have hmain : (∫ x, Ψ x ^ 2 * ‖f x‖ ^ 2)
      ≤ (∫ x, ‖f x‖ ^ 2) - (1 - e ^ 2) * (∫ x in U, ‖f x‖ ^ 2) := by
    rw [hdecomp]
    calc (∫ x in U, Ψ x ^ 2 * ‖f x‖ ^ 2) + (∫ x in Uᶜ, Ψ x ^ 2 * ‖f x‖ ^ 2)
        ≤ e ^ 2 * (∫ x in U, ‖f x‖ ^ 2) + (∫ x in Uᶜ, ‖f x‖ ^ 2) :=
          add_le_add hU_bound hcompl_bound
      _ = e ^ 2 * (∫ x in U, ‖f x‖ ^ 2) + ((∫ x, ‖f x‖ ^ 2) - (∫ x in U, ‖f x‖ ^ 2)) := by
          rw [hcompl_eq]
      _ = (∫ x, ‖f x‖ ^ 2) - (1 - e ^ 2) * (∫ x in U, ‖f x‖ ^ 2) := by ring
  have hA_ge : (∫ x, ‖f x‖ ^ 2) / C ^ 2 ≤ (∫ x in U, ‖f x‖ ^ 2) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < C ^ 2)]
    simpa [mul_comm] using hbound
  have hone_minus_e_nn : 0 ≤ 1 - e ^ 2 := by linarith [hesq_le_one]
  have hstep : (∫ x, ‖f x‖ ^ 2) - (1 - e ^ 2) * (∫ x in U, ‖f x‖ ^ 2)
      ≤ (∫ x, ‖f x‖ ^ 2) - (1 - e ^ 2) * ((∫ x, ‖f x‖ ^ 2) / C ^ 2) := by
    have := mul_le_mul_of_nonneg_left hA_ge hone_minus_e_nn
    linarith
  have hfinal : (∫ x, ‖f x‖ ^ 2) - (1 - e ^ 2) * ((∫ x, ‖f x‖ ^ 2) / C ^ 2)
      = (1 - (1 - e ^ 2) / C ^ 2) * (∫ x, ‖f x‖ ^ 2) := by ring
  have hcoef : 1 - (1 - e ^ 2) / C ^ 2 ≤ 1 - (1 - c' ^ 2) / C ^ 2 := by
    have hC2 : (0:ℝ) < C ^ 2 := by positivity
    have h : (1 - c' ^ 2) ≤ (1 - e ^ 2) := by linarith [hesq_le_c'sq]
    have := div_le_div_of_nonneg_right h hC2.le
    linarith
  have hG_nn : 0 ≤ (∫ x, ‖f x‖ ^ 2) := integral_nonneg hg_nn
  calc (∫ x, Ψ x ^ 2 * ‖f x‖ ^ 2)
      ≤ (∫ x, ‖f x‖ ^ 2) - (1 - e ^ 2) * ((∫ x, ‖f x‖ ^ 2) / C ^ 2) := le_trans hmain hstep
    _ = (1 - (1 - e ^ 2) / C ^ 2) * (∫ x, ‖f x‖ ^ 2) := hfinal
    _ ≤ (1 - (1 - c' ^ 2) / C ^ 2) * (∫ x, ‖f x‖ ^ 2) := mul_le_mul_of_nonneg_right hcoef hG_nn

end Commons.MeasureTheory.Integral