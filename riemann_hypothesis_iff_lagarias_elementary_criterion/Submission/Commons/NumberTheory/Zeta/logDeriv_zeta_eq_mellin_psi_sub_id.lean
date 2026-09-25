import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Topology.Separation.CompletelyRegular

open Complex Filter Set Finset
open ArithmeticFunction hiding log id
open scoped ArithmeticFunction
open scoped Topology
open MeasureTheory
open Asymptotics

namespace Commons.NumberTheory.Zeta

private lemma setIntegral_Ioi0_trunc {f : ℝ → ℂ} :
    (∫ t : ℝ in Ioi (0 : ℝ), (if 1 ≤ t then f t else 0)) = ∫ t : ℝ in Ioi (1 : ℝ), f t := by
  have hset : Ioi (0 : ℝ) ∩ Ici (1 : ℝ) = Ici (1 : ℝ) := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      constructor
      · have hxle : 1 ≤ x := by simpa [Set.mem_Ici] using hx
        have hxpos : 0 < x := by linarith
        simpa [Set.mem_Ioi] using hxpos
      · exact hx
  calc
    (∫ t : ℝ in Ioi (0 : ℝ), (if 1 ≤ t then f t else 0))
        = ∫ t : ℝ in Ioi (0 : ℝ), (Ici (1 : ℝ)).indicator f t := by
          apply integral_congr_ae
          filter_upwards with t
          by_cases h : 1 ≤ t <;> simp [h]
    _ = ∫ t : ℝ in (Ioi (0 : ℝ)) ∩ Ici (1 : ℝ), f t := by
          rw [setIntegral_indicator measurableSet_Ici]
    _ = ∫ t : ℝ in Ici (1 : ℝ), f t := by rw [hset]
    _ = ∫ t : ℝ in Ioi (1 : ℝ), f t := integral_Ici_eq_integral_Ioi

private lemma psi_partialSum (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (Λ k : ℂ)) = (Chebyshev.psi t : ℂ) := by
  rw [Chebyshev.psi]
  push_cast
  congr 1

private lemma psi_partialSum_real (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, Λ k = Chebyshev.psi (n : ℝ) := by
  rw [Chebyshev.psi]
  simp
  congr 1

private lemma psi_bigO_atTop_nat : (fun n : ℕ => Chebyshev.psi (n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4 + 4, ?_⟩
  filter_upwards with n
  have hnorm : ‖(n : ℝ)‖ = (n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hnorm, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg (n : ℝ))]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

private lemma sum_Λ_Icc_bigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, Λ k) =O[atTop] fun n : ℕ => (n : ℝ) := by
  simpa [psi_partialSum_real] using psi_bigO_atTop_nat

private lemma mangoldt_LSeries_eq_integral (w : ℂ) (hw : 1 < w.re) :
    LSeries (fun n : ℕ => (Λ n : ℂ)) w =
      w * ∫ t : ℝ in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (Λ k : ℂ)) * (t : ℂ) ^ (-(w + 1)) := by
  have hbigO := sum_Λ_Icc_bigO
  have hbigO' : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, Λ k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    simpa [Real.rpow_one] using hbigO
  simpa using LSeries_eq_mul_integral_of_nonneg Λ (r := (1 : ℝ)) (by norm_num : 0 ≤ (1 : ℝ))
    (by simpa using hw : (1 : ℝ) < w.re) hbigO' (fun n => vonMangoldt_nonneg (n := n))

private noncomputable def psiTrunc (t : ℝ) : ℂ := if 1 ≤ t then (Chebyshev.psi t : ℂ) else 0

private lemma mellin_psiTrunc_eq (w : ℂ) :
    mellin psiTrunc (-w) = ∫ t : ℝ in Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
  have hexp : (-w) - 1 = -(w + 1) := by ring
  calc
    mellin psiTrunc (-w) = ∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ ((-w) - 1) * psiTrunc t := by
      rfl
    _ = ∫ t : ℝ in Ioi (0 : ℝ), (if 1 ≤ t then (t : ℂ) ^ ((-w) - 1) * (Chebyshev.psi t : ℂ) else 0) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases h : 1 ≤ t <;> simp [psiTrunc, h]
    _ = ∫ t : ℝ in Ioi (1 : ℝ), (t : ℂ) ^ ((-w) - 1) * (Chebyshev.psi t : ℂ) := by
      simpa using (setIntegral_Ioi0_trunc (f := fun t : ℝ => (t : ℂ) ^ ((-w) - 1) * (Chebyshev.psi t : ℂ)))
    _ = ∫ t : ℝ in Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hexp]
      ring

private lemma LSeries_vonMangoldt_eq_mellin_psiTrunc (w : ℂ) (hw : 1 < w.re) :
    LSeries (fun n : ℕ => (Λ n : ℂ)) w = w * mellin psiTrunc (-w) := by
  rw [mangoldt_LSeries_eq_integral w hw]
  congr 1
  calc
    (∫ t : ℝ in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (Λ k : ℂ)) * (t : ℂ) ^ (-(w + 1)))
        = ∫ t : ℝ in Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
          apply integral_congr_ae
          filter_upwards with t
          rw [psi_partialSum]
    _ = mellin psiTrunc (-w) := by
          rw [mellin_psiTrunc_eq]

private noncomputable def idTrunc (t : ℝ) : ℂ := if 1 ≤ t then (t : ℂ) else 0

private lemma cpow_sub_one_mul_self {t : ℝ} (ht : t ≠ 0) (w : ℂ) :
    (t : ℂ) ^ ((-w) - 1) * (t : ℂ) = (t : ℂ) ^ (-w) := by
  calc
    (t : ℂ) ^ ((-w) - 1) * (t : ℂ)
        = (t : ℂ) ^ (((-w) - 1) + 1) := by
          rw [Complex.cpow_add (x := (t : ℂ)) ((-w) - 1) (1 : ℂ) (ofReal_ne_zero.mpr ht)]
          rw [Complex.cpow_one]
    _ = (t : ℂ) ^ (-w) := by
          congr 1
          ring

private lemma mellin_idTrunc_eq_integral (w : ℂ) :
    mellin idTrunc (-w) = ∫ t : ℝ in Ioi (1 : ℝ), (t : ℂ) ^ (-w) := by
  calc
    mellin idTrunc (-w) = ∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ ((-w) - 1) * idTrunc t := by
      rfl
    _ = ∫ t : ℝ in Ioi (0 : ℝ), (if 1 ≤ t then (t : ℂ) ^ ((-w) - 1) * (t : ℂ) else 0) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases h : 1 ≤ t <;> simp [idTrunc, h]
    _ = ∫ t : ℝ in Ioi (1 : ℝ), (t : ℂ) ^ ((-w) - 1) * (t : ℂ) := by
      simpa using (setIntegral_Ioi0_trunc (f := fun t : ℝ => (t : ℂ) ^ ((-w) - 1) * (t : ℂ)))
    _ = ∫ t : ℝ in Ioi (1 : ℝ), (t : ℂ) ^ (-w) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))] with t ht
      have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
      exact cpow_sub_one_mul_self (ne_of_gt (lt_trans zero_lt_one ht1)) w

private lemma MellinConvergent_trunc_iff (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (fun t : ℝ => if 1 ≤ t then f t else 0) s ↔
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioi (1 : ℝ)) := by
  have hpoint : (fun t : ℝ => (t : ℂ) ^ (s - 1) • (if 1 ≤ t then f t else 0))
      = (Ici (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) := by
    funext t
    by_cases h : 1 ≤ t <;> simp [h]
  rw [MellinConvergent, hpoint]
  rw [integrableOn_indicator_iff measurableSet_Ici]
  have hset : Ici (1 : ℝ) ∩ Ioi (0 : ℝ) = Ici (1 : ℝ) := by
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx
      constructor
      · exact hx
      · have hxle : 1 ≤ x := by simpa [Set.mem_Ici] using hx
        have hxpos : 0 < x := by linarith
        simpa [Set.mem_Ioi] using hxpos
  rw [hset]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]

private lemma MellinConvergent_idTrunc {w : ℂ} (hw : 1 < w.re) : MellinConvergent idTrunc (-w) := by
  change MellinConvergent (fun t : ℝ => if 1 ≤ t then (t : ℂ) else 0) (-w)
  rw [MellinConvergent_trunc_iff (fun t : ℝ => (t : ℂ)) (-w)]
  have hre : (-w).re < -1 := by
    rw [Complex.neg_re]
    linarith
  apply IntegrableOn.congr_fun_ae (integrableOn_Ioi_cpow_of_lt (a := -w) hre (by norm_num : 0 < (1 : ℝ)))
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))] with t ht
  have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
  have htpos : 0 < t := lt_trans zero_lt_one ht1
  simp [smul_eq_mul, cpow_sub_one_mul_self (ne_of_gt htpos) w]

private lemma norm_psi_mul_cpow (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(w + 1))‖ = Chebyshev.psi t * t ^ (-w.re - 1) := by
  rw [Complex.norm_mul]
  have hpsi : ‖(Chebyshev.psi t : ℂ)‖ = Chebyshev.psi t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg t)]
  rw [hpsi, Complex.norm_cpow_eq_rpow_re_of_pos ht (-(w + 1))]
  congr 2
  simp [Complex.neg_re, Complex.add_re, Complex.one_re, sub_eq_add_neg]
  ring

private lemma integrableOn_psi_mul_cpow_Ioi {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun t : ℝ => (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(w + 1))) (Ioi (1 : ℝ)) := by
  let C : ℝ := Real.log 4 + 4
  have hb : IntegrableOn (fun t : ℝ => C * t ^ (-w.re)) (Ioi (1 : ℝ)) := by
    have hint := integrableOn_Ioi_rpow_of_lt (a := -w.re) (c := (1 : ℝ)) (by linarith) (by norm_num)
    change Integrable (fun t : ℝ => C * t ^ (-w.re)) (volume.restrict (Ioi (1 : ℝ)))
    exact MeasureTheory.Integrable.const_mul hint C
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(w + 1)))
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · have hm : Measurable (Complex.ofReal ∘ Chebyshev.psi) :=
        Complex.continuous_ofReal.measurable.comp Chebyshev.psi_mono.measurable
      simpa [Function.comp_def] using hm.aestronglyMeasurable
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      exact (Complex.continuousAt_ofReal_cpow_const t (-(w + 1))
        (Or.inr (ne_of_gt (lt_trans zero_lt_one (Set.mem_Ioi.mp ht))))).continuousWithinAt
  refine Integrable.mono' (μ := volume.restrict (Ioi (1 : ℝ))) hb hmeas ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))] with t ht
  have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  rw [norm_psi_mul_cpow w ht0]
  have hpsi : Chebyshev.psi t ≤ C * t := by
    have := Chebyshev.psi_le_const_mul_self (show 0 ≤ t by linarith)
    simpa [C] using this
  calc
    Chebyshev.psi t * t ^ (-w.re - 1) ≤ (C * t) * t ^ (-w.re - 1) := by
      exact mul_le_mul_of_nonneg_right hpsi (Real.rpow_nonneg (by linarith) (-w.re - 1))
    _ = C * (t * t ^ (-w.re - 1)) := by ring
    _ = C * t ^ (-w.re) := by
      congr 1
      calc
        t * t ^ (-w.re - 1) = t ^ (1 + (-w.re - 1)) := by
          nth_rw 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht0 (1 : ℝ) (-w.re - 1)]
        _ = t ^ (-w.re) := by
          congr 1
          ring

private lemma MellinConvergent_psiTrunc {w : ℂ} (hw : 1 < w.re) : MellinConvergent psiTrunc (-w) := by
  change MellinConvergent (fun t : ℝ => if 1 ≤ t then (Chebyshev.psi t : ℂ) else 0) (-w)
  rw [MellinConvergent_trunc_iff (fun t : ℝ => (Chebyshev.psi t : ℂ)) (-w)]
  refine IntegrableOn.congr_fun_ae (integrableOn_psi_mul_cpow_Ioi hw) ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))] with t ht
  have hexp : (-w) - 1 = -(w + 1) := by ring
  rw [smul_eq_mul, hexp]
  ring

private lemma mellin_idTrunc_val {w : ℂ} (hw : 1 < w.re) : mellin idTrunc (-w) = 1 / (w - 1) := by
  rw [mellin_idTrunc_eq_integral w]
  have hre : (-w).re < -1 := by
    rw [Complex.neg_re]
    linarith
  rw [integral_Ioi_cpow_of_lt (a := -w) (c := (1 : ℝ)) hre (by norm_num : 0 < (1 : ℝ))]
  have h1 : (1 : ℂ) ^ ((-w) + 1) = 1 := by rw [Complex.one_cpow]
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have : (w - 1).re = 0 := congrArg Complex.re h
    simp at this
    linarith
  have h1' : ((1 : ℝ) : ℂ) ^ ((-w) + 1) = 1 := by simpa using h1
  have hw1' : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : ((1 : ℂ) - w).re = 0 := congrArg Complex.re h
    simp at this
    linarith
  rw [h1']
  calc
    -1 / ((-w) + 1) = -1 / (1 - w) := by congr 1; ring
    _ = 1 / (w - 1) := by
      field_simp [hw1, hw1']
      ring

private noncomputable def corrTrunc (t : ℝ) : ℂ :=
  if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0

private lemma corrTrunc_eq_sub (t : ℝ) : corrTrunc t = psiTrunc t - idTrunc t := by
  by_cases h : 1 ≤ t <;> simp [corrTrunc, psiTrunc, idTrunc, h]

private lemma mellin_corrTrunc_split {w : ℂ} (hw : 1 < w.re) :
    mellin corrTrunc (-w) = mellin psiTrunc (-w) - mellin idTrunc (-w) := by
  calc
    mellin corrTrunc (-w) = mellin (fun t : ℝ => psiTrunc t - idTrunc t) (-w) := by
      congr 1
      funext t
      exact corrTrunc_eq_sub t
    _ = mellin psiTrunc (-w) - mellin idTrunc (-w) := by
      exact (hasMellin_sub (f := psiTrunc) (g := idTrunc) (s := -w)
        (MellinConvergent_psiTrunc hw) (MellinConvergent_idTrunc hw)).2

theorem logDeriv_zeta_eq_mellin_psi_sub_id {w : ℂ} (hw : 1 < w.re) :
    -(deriv riemannZeta w) / riemannZeta w - w / (w - 1) =
      w * mellin (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-w) := by
  have hfun : (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) = corrTrunc := by
    funext t
    simp [corrTrunc]
  calc
    -(deriv riemannZeta w) / riemannZeta w - w / (w - 1)
        = LSeries (fun n : ℕ => (Λ n : ℂ)) w - w / (w - 1) := by
          rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
    _ = w * mellin psiTrunc (-w) - w / (w - 1) := by
          rw [LSeries_vonMangoldt_eq_mellin_psiTrunc w hw]
    _ = w * mellin psiTrunc (-w) - w * mellin idTrunc (-w) := by
          have hid : w * mellin idTrunc (-w) = w / (w - 1) := by
            rw [mellin_idTrunc_val hw]
            ring
          rw [← hid]
    _ = w * (mellin psiTrunc (-w) - mellin idTrunc (-w)) := by ring
    _ = w * mellin corrTrunc (-w) := by
          rw [← mellin_corrTrunc_split hw]
    _ = w * mellin (fun t : ℝ => if 1 ≤ t then ((Chebyshev.psi t : ℂ) - (t : ℂ)) else 0) (-w) := by
          rw [hfun]

end Commons.NumberTheory.Zeta