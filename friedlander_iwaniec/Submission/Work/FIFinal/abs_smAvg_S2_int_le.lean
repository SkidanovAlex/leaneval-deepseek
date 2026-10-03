import Mathlib
import Submission.Work.FIChain.BprimeWindowIntegrated
import Submission.Work.FIChain.RhoWindowIntegrated2
import Submission.ASP.Defs
import Submission.ASP.S3v
import Submission.ASP.S7b
import Submission.ASP.S7c
import Submission.ASP.S7d
import Submission.ASP.S7e
import Submission.ASP.S8
import Submission.ASP.S8b
import Submission.Work.FIFinal.smAvg_Bint_int_le
import Submission.Work.FIFinal.Kmerge_le_dyadic_Bint
import Submission.Work.FIFinal.smAvg_Ksum_le_Kmerge
-- direct imports of the vocabulary used below, so that this file does not depend on the
-- exact import set of `IntTools`:
-- the three decomposed sub-results (see the docstring of each module):

namespace Work.FIFinal

open Finset MeasureTheory
open scoped Interval

/-!
# The integrated `S₂` bound

`Work.FIFinal.abs_smAvg_S2_int_le` is the analogue of `Submission.ASP.abs_smAvg_S2_le` in which
the bilinear hypothesis (B′) is replaced by the *integrated* window
`Work.FIChain.BprimeWindowInt`.  On each dyadic piece the substitution `t = 2^j u` turns the
integrated hypothesis into an integral over a sub-interval of its own window, so each piece costs
`E` (rather than `E(1+log Δ)`); the factor `J` comes from the `J` dyadic levels and `log N` from
`Submission.ASP.abs_S2_le_log_Ksum`.
-/

theorem abs_smAvg_S2_int_le (a lam : ℕ → ℝ) (N : ℕ) {w : ℕ → ℝ} {s E Y : ℝ} {J : ℕ} {Δ : ℕ}
    {z : ℝ} (hs : s = (2 : ℝ) ^ J) (hY : 0 < Y) (hΔ : 1 ≤ Δ) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hE : 0 ≤ E) (hN : 1 ≤ N)
    (hw : ∀ ℓ, 1 ≤ ℓ → ((ℓ.divisors.card : ℝ)) ^ 2 ≤ w ℓ)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1)
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hB : Work.FIChain.BprimeWindowInt a N w E (Y / (Δ : ℝ)) (s * (Real.exp 1 * Y))) :
    (∫ y in Y..(Real.exp 1 * Y), |Submission.ASP.S2 a lam N y z (s * y)| / y)
      ≤ Real.log (N : ℝ) * ((J : ℝ) * (E * (1 + Real.log (Δ : ℝ)))) := by
  have hspos : 0 < s := by rw [hs]; positivity
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNpos
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)
  have hYle : Y ≤ Real.exp 1 * Y := le_mul_of_one_le_left hY.le he1
  have hApos : 0 < Y / (Δ : ℝ) := div_pos hY hΔpos
  have hAeY : Y / (Δ : ℝ) ≤ Real.exp 1 * Y := by
    rw [div_le_iff₀ hΔpos]; nlinarith [hY.le, hΔ1, he1, hY]
  have hcongr : (∫ y in Y..(Real.exp 1 * Y), |Submission.ASP.S2 a lam N y z (s * y)| / y)
      = ∫ y in Y..(Real.exp 1 * Y), |Submission.ASP.S2 a lam N y z (s * y) / y| := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hy0 : (0 : ℝ) ≤ y := by
      have h1 := hy.1
      rw [min_eq_left hYle] at h1
      linarith [hY]
    rw [abs_div, abs_of_nonneg hy0]
  rw [hcongr]
  have hstep : (∫ y in Y..(Real.exp 1 * Y), |Submission.ASP.S2 a lam N y z (s * y) / y|)
      ≤ ∫ y in Y..(Real.exp 1 * Y),
          Real.log (N : ℝ) *
            ∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k| / y := by
    rw [intervalIntegral.integral_of_le hYle, intervalIntegral.integral_of_le hYle]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          (0 : ℝ) ≤ |Submission.ASP.S2 a lam N y z (s * y) / y|
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun y _ => abs_nonneg _)
    · have hsum := IntervalIntegrable.sum (Finset.Icc 1 N) (fun k _ =>
        Submission.ASP.intervalIntegrable_Ksum_div a lam N k hspos (p := Y)
          (q := Real.exp 1 * Y) hY hYle)
      have h2 := hsum.const_mul (Real.log (N : ℝ))
      simpa only [IntegrableOn, Finset.sum_fn, Finset.mul_sum] using h2.1
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          |Submission.ASP.S2 a lam N y z (s * y) / y|
            ≤ Real.log (N : ℝ) *
                ∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k| / y
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      have hy0 : 0 < y := lt_trans hY hy.1
      rw [abs_div, abs_of_pos hy0]
      calc |Submission.ASP.S2 a lam N y z (s * y)| / y
          ≤ (Real.log (N : ℝ) *
              ∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|) / y :=
            div_le_div_of_nonneg_right (Submission.ASP.abs_S2_le_log_Ksum a lam N y z (s * y)) hy0.le
        _ = Real.log (N : ℝ) *
              ∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k| / y := by
            simp only [Finset.sum_div, mul_div_assoc]
  refine hstep.trans ?_
  have hstep2 : (∫ y in Y..(Real.exp 1 * Y),
        Real.log (N : ℝ) *
          ∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k| / y)
      = Real.log (N : ℝ) *
        ∫ y in Y..(Real.exp 1 * Y),
          (∑ k ∈ Finset.Icc 1 N, |Submission.ASP.Ksum a lam N y (s * y) k|) / y := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [Finset.sum_div]
  rw [hstep2]
  refine mul_le_mul_of_nonneg_left ?_ hlogN
  -- main bound
  have hB' : Work.FIChain.BprimeWindowInt a N w E (Y / (Δ : ℝ)) ((2 : ℝ) ^ J * (Real.exp 1 * Y)) := by
    simpa only [hs] using hB
  refine (smAvg_Ksum_le_Kmerge (w := w) a lam N hs hY hΔ hlam_supp hlam_le1 ha).trans ?_
  -- goal: ∫ z in Y/Δ..eY, Kmerge/z ≤ J*(E*(1+logΔ))
  have hKmerge : ∀ z : ℝ, Submission.ASP.Kmerge a lam N s Δ z
      ≤ ∑ j ∈ Finset.range J, Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z) :=
    fun z => Kmerge_le_dyadic_Bint a lam N w Δ hs hΔ hw hlam_le1
  have hstepC1 : (∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Kmerge a lam N s Δ z / z)
      ≤ ∑ j ∈ Finset.range J,
          ∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z) / z := by
    have h1 : (∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Kmerge a lam N s Δ z / z)
        ≤ ∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y),
            (∑ j ∈ Finset.range J, Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z)) / z := by
      rw [intervalIntegral.integral_of_le hAeY, intervalIntegral.integral_of_le hAeY]
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · change ∀ᵐ z ∂(volume.restrict (Set.Ioc (Y / (Δ : ℝ)) (Real.exp 1 * Y))),
            (0 : ℝ) ≤ Submission.ASP.Kmerge a lam N s Δ z / z
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun z hz => div_nonneg
          (Finset.sum_nonneg (fun _ _ => Submission.ASP.Kfac_nonneg a lam N s _ _))
          (le_of_lt (lt_trans hApos hz.1)))
      · have hsum := IntervalIntegrable.sum (Finset.range J) (fun j _ =>
          Submission.ASP.intervalIntegrable_Bint_div (a := a) (N := N) (w := w)
            (c := (2 : ℝ) ^ j) hApos hAeY)
        simpa only [IntegrableOn, Finset.sum_fn, Finset.sum_div] using hsum.1
      · change ∀ᵐ z ∂(volume.restrict (Set.Ioc (Y / (Δ : ℝ)) (Real.exp 1 * Y))),
            Submission.ASP.Kmerge a lam N s Δ z / z
              ≤ (∑ j ∈ Finset.range J, Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z)) / z
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun z hz =>
          div_le_div_of_nonneg_right (hKmerge z) (le_of_lt (lt_trans hApos hz.1)))
    refine h1.trans (le_of_eq ?_)
    rw [show (∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y),
          (∑ j ∈ Finset.range J, Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z)) / z)
        = ∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y),
            ∑ j ∈ Finset.range J, Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z) / z from
      intervalIntegral.integral_congr (fun z _ => by rw [Finset.sum_div])]
    exact intervalIntegral.integral_finsetSum (fun j _ =>
      Submission.ASP.intervalIntegrable_Bint_div (a := a) (N := N) (w := w)
        (c := (2 : ℝ) ^ j) hApos hAeY)
  refine hstepC1.trans ?_
  have h2 : (∑ j ∈ Finset.range J,
        ∫ z in Y / (Δ : ℝ)..(Real.exp 1 * Y), Submission.ASP.Bint a N w ((2 : ℝ) ^ j * z) / z)
      ≤ ∑ _j ∈ Finset.range J, E :=
    Finset.sum_le_sum (fun j hj =>
      smAvg_Bint_int_le a N w (J := J) (Δ := Δ) (Finset.mem_range.mp hj) hY hΔ hw0 hB')
  refine h2.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg J)
  have hlogΔ : 0 ≤ Real.log (Δ : ℝ) := Real.log_nonneg hΔ1
  nlinarith [hE, hlogΔ]

end Work.FIFinal
