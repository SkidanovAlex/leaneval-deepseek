import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Filter
open scoped Topology

namespace Commons.Analysis.MeasureTheory

theorem tendsto_eLpNorm_mul_exp_neg_sq {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
    Filter.Tendsto (fun n : ℕ => MeasureTheory.eLpNorm
        (fun x : EuclideanSpace ℝ (Fin d) =>
          f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x)
        2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
      Filter.atTop (nhds 0) := by
  -- Pointwise domination of the multiplier difference by `1`.
  have hbE : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      ‖(Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - 1‖ₑ ≤ 1 := by
    intro n x
    have ht : 0 < (((n : ℝ) + 1) ^ 2) := by positivity
    have hexp : -(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ ht.le
      exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hb : ‖(Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - 1‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hφ0 : 0 ≤ Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) :=
        Real.exp_nonneg _
      have hφ1 : Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr hexp
      constructor <;> linarith
    rw [enorm_eq_nnnorm, ENNReal.coe_le_one_iff]
    exact_mod_cast hb
  have hpt : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ
        ≤ ‖f x‖ₑ := by
    intro n x
    have heq : f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x
        = f x * ((Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - 1) := by
      ring
    rw [heq, enorm_mul]
    calc ‖f x‖ₑ * ‖(Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - 1‖ₑ
        ≤ ‖f x‖ₑ * 1 := by gcongr; exact hbE n x
      _ = ‖f x‖ₑ := by simp
  have hpt2 : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ ^ (2:ℝ)
        ≤ ‖f x‖ₑ ^ (2:ℝ) := fun n x => ENNReal.rpow_le_rpow (hpt n x) (by norm_num)
  -- Measurability of the integrands.
  have hmeas : ∀ n : ℕ, AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
      ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ
        ^ (2:ℝ)) volume := by
    intro n
    have hfa : AEMeasurable f (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      hf.aestronglyMeasurable.aemeasurable
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
        Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2))) := by fun_prop
    have hmeas_phi : AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
        (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ)) volume :=
      (Complex.continuous_ofReal.comp hcont).aemeasurable
    have hg : AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
        f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x) volume :=
      (hfa.mul hmeas_phi).sub hfa
    exact (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hg.enorm)
  -- Pointwise convergence to `0`.
  have hlim : ∀ x : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ =>
      ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ
        ^ (2:ℝ)) atTop (nhds 0) := by
    intro x
    have harg : Tendsto (fun n : ℕ =>
        -(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) atTop (nhds 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      have h1 : Tendsto (fun n : ℕ => (n:ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
      simpa [pow_two] using h1.atTop_mul_atTop₀ h1
    have hreal : Tendsto (fun n : ℕ =>
        Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2))) atTop (nhds 1) := by
      have h2 := (Real.continuous_exp.tendsto (0:ℝ)).comp harg
      rw [Real.exp_zero] at h2
      exact h2
    have hcomplex : Tendsto (fun n : ℕ =>
        (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ)) atTop (nhds 1) := by
      have h2 := (Complex.continuous_ofReal.tendsto (1:ℝ)).comp hreal
      rw [Complex.ofReal_one] at h2
      exact h2
    have hg : Tendsto (fun n : ℕ =>
        f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x)
        atTop (nhds 0) := by
      have h2 : Tendsto (fun n : ℕ =>
          f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ))
          atTop (nhds (f x * 1)) :=
        Tendsto.mul (tendsto_const_nhds (x := f x)) hcomplex
      have h3 : Tendsto (fun n : ℕ =>
          f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x)
          atTop (nhds (f x * 1 - f x)) :=
        Tendsto.sub h2 (tendsto_const_nhds (x := f x))
      simpa using h3
    have hnorm : Tendsto (fun n : ℕ =>
        ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ)
        atTop (nhds 0) := by
      have h2 := (continuous_enorm.tendsto (0:ℂ)).comp hg
      rw [enorm_zero] at h2
      exact h2
    have h3 := hnorm.ennrpow_const (2:ℝ)
    simpa using h3
  -- Finiteness of the dominating function.
  have hfin : ∫⁻ x : EuclideanSpace ℝ (Fin d), ‖f x‖ₑ ^ (2:ℝ)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) ≠ ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2:ENNReal))
      (by norm_num) (by norm_num) hf.eLpNorm_lt_top
    simpa using h.ne
  -- Dominated convergence for the integrals.
  have hlin : Tendsto (fun n : ℕ => ∫⁻ x : EuclideanSpace ℝ (Fin d),
      ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ
        ^ (2:ℝ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) atTop (nhds 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (ι := ℕ) (l := atTop)
      (F := fun (n : ℕ) x => ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2))
                          / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ ^ (2:ℝ))
      (f := fun _ : EuclideanSpace ℝ (Fin d) => (0 : ENNReal))
      (bound := fun x : EuclideanSpace ℝ (Fin d) => ‖f x‖ₑ ^ (2:ℝ))
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall (hpt2 n))
      hfin
      (Filter.Eventually.of_forall hlim)
    simpa using h
  -- Take the square root.
  have hmain : Tendsto (fun n : ℕ => (∫⁻ x : EuclideanSpace ℝ (Fin d),
      ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ
        ^ (2:ℝ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) ^ (1/2:ℝ)) atTop (nhds 0) := by
    have h := hlin.ennrpow_const (1/2:ℝ)
    simpa using h
  have hfun : (fun n : ℕ => eLpNorm
        (fun x : EuclideanSpace ℝ (Fin d) =>
          f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x)
        2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      = fun n : ℕ => (∫⁻ x : EuclideanSpace ℝ (Fin d),
      ‖f x * (Real.exp (-(Finset.univ.sum (fun i => (x i) ^ 2)) / (((n : ℝ) + 1) ^ 2)) : ℂ) - f x‖ₑ
        ^ (2:ℝ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) ^ (1/2:ℝ) := by
    funext n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal)) (by norm_num) (by norm_num)]
    simp
  rw [hfun]
  exact hmain

end Commons.Analysis.MeasureTheory