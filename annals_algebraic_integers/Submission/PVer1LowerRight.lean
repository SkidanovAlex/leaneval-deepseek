import Submission.PVer1Base
import Submission.ScaleBoundLower
import Submission.ScaleBoundAny

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.PVer1LowerRight

open Submission.PotentialDefs
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.Quantile
open Submission.QuantileExt
open Submission.ThreePages
open Submission.Bclps
open Submission.Contracts
open Submission.WeightedNorm
open Submission.WnormShift
open Submission.WnormToolkit
open Submission.ScaleBoundLower
open Submission.ScaleBoundAny
open Submission.PVer1

/-- If a continuous function is `≥ c` for all points just left of `x`, then
`c ≤ f x`. (Mirror of `Submission.PVer1.const_le_of_forall_gt_near`.) -/
lemma const_le_of_forall_lt_near {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y < x → x - y < δ → c ≤ f y) : c ≤ f x := by
  by_contra hnot
  have hlt : f x < c := lt_of_not_ge hnot
  let ε : ℝ := (c - f x) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  rcases hδ with ⟨δ0, hδ0pos, hδ0⟩
  have hmet := Metric.continuousAt_iff.mp hf ε hε
  rcases hmet with ⟨δ1, hδ1pos, hδ1⟩
  let δ : ℝ := min δ0 δ1
  have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
  let y : ℝ := x - δ / 2
  have hylt : y < x := by
    dsimp [y]
    linarith
  have hdiff : x - y = δ / 2 := by
    dsimp [y]
    ring
  have hdy0 : x - y < δ0 := by
    rw [hdiff]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_left δ0 δ1)
  have hyc : c ≤ f y := hδ0 y hylt hdy0
  have hdy1 : |y - x| < δ1 := by
    have hd : |y - x| = δ / 2 := by
      have hlt : 0 < x - y := by linarith
      rw [abs_sub_comm]
      rw [abs_of_pos hlt]
      exact hdiff
    rw [hd]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_right δ0 δ1)
  have hdist1' : dist y x < δ1 := by
    simpa [Real.dist_eq] using hdy1
  have hclose : |f y - f x| < ε := hδ1 hdist1'
  have hfy : f y < c := by
    dsimp [ε] at hclose
    have h1 : f y - f x < (c - f x) / 2 := (abs_lt.mp hclose).2
    linarith
  exact (not_lt_of_ge hyc) hfy

/-- Pointwise lower bound for the pruned polynomial, at the right extreme root
`x = α_{N+2,N+2}`:

`∃ C, 0 < C ∧ ∀ N ≥ 2, ∀ s ≤ Bclps.Dconst :
   N^{-C}·ρ_{P̃}(x) ≤ w_μ(x)^{N+s}·|P̃_N(x)|` at `x = α_{N+2,N+2}`. -/
lemma lower_right_root :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ s : ℕ, s ≤ Bclps.Dconst →
      (N : ℝ) ^ (-C) * rhoKept N (alpha (N + 2) (N + 2)) ≤
        (weight muS (alpha (N + 2) (N + 2))) ^ (N + s) *
          |(prunePoly N).eval (alpha (N + 2) (N + 2))| := by
  rcases ThreePages.potential_approx_lower with ⟨C0, hC0pos, hPAL⟩
  rcases ScaleBoundLower.scale_bound_gen C0 Kshift Dserre hC0pos Kshift_nonneg Dserre_ge_one with ⟨C, hCpos, hS⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN s hs
  have hN1 : 1 ≤ N := by omega
  let x : ℝ := alpha (N + 2) (N + 2)
  have hn : 1 ≤ N + 2 := by omega
  have hx : x ∈ Set.Icc aSerre bSerre := by
    dsimp [x]
    exact alpha_mem_Icc (n := N + 2) (i := N + 2) hn (by omega) (le_rfl)
  -- order facts about the extreme roots
  have hα1x : alpha (N + 2) 1 < x := by
    dsimp [x]
    exact alpha_strict_mono hn (by norm_num) (by omega) (le_rfl)
  have hαN1x : alpha (N + 2) (N + 1) < x := by
    dsimp [x]
    exact alpha_strict_mono hn (by omega) (by omega) (le_rfl)
  have hα1N1 : alpha (N + 2) 1 < alpha (N + 2) (N + 1) := by
    exact alpha_strict_mono hn (by norm_num) (by omega) (by omega)
  have hxα1 : 0 < x - alpha (N + 2) 1 := sub_pos.mpr hα1x
  have hxN1 : 0 < x - alpha (N + 2) (N + 1) := sub_pos.mpr hαN1x
  -- continuity step: the claimed bound holds on a punctured left neighbourhood of x
  let f : ℝ → ℝ := fun y : ℝ =>
    (weight muS y) ^ (N + 2) * |(prunePoly N).eval y| * (y - alpha (N + 2) 1)
  have hfcont : ContinuousAt f x := by
    have h1 : Continuous (fun y : ℝ => (weight muS y) ^ (N + 2) * |(prunePoly N).eval y|) :=
      continuous_weight_pow_eval (N + 2) (prunePoly N)
    have h2 : Continuous (fun y : ℝ => y - alpha (N + 2) 1) :=
      continuous_id.sub continuous_const
    have hprod : Continuous (fun y : ℝ =>
        (weight muS y) ^ (N + 2) * |(prunePoly N).eval y| * (y - alpha (N + 2) 1)) := h1.mul h2
    simpa [f] using hprod.continuousAt
  have hloc : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y < x → x - y < δ →
      ((N + 2 : ℕ) : ℝ) ^ (-C0) ≤ f y := by
    refine ⟨(x - alpha (N + 2) (N + 1)) / 2, div_pos hxN1 (by norm_num), ?_⟩
    intro y hyx hxy
    have hy_gt_mid : x - (x - alpha (N + 2) (N + 1)) / 2 < y := by linarith
    have hyN1 : alpha (N + 2) (N + 1) < y := by
      have hmid : x - (x - alpha (N + 2) (N + 1)) / 2 = (x + alpha (N + 2) (N + 1)) / 2 := by ring
      rw [hmid] at hy_gt_mid
      linarith
    have hyIcc : y ∈ Set.Icc aSerre bSerre := by
      have hN1Icc : alpha (N + 2) (N + 1) ∈ Set.Icc aSerre bSerre :=
        alpha_mem_Icc (n := N + 2) (i := N + 1) hn (by omega) (by omega)
      constructor
      · exact le_trans hN1Icc.1 (le_of_lt hyN1)
      · exact le_trans (le_of_lt hyx) hx.2
    have hy1 : alpha (N + 2) 1 < y := lt_trans hα1N1 hyN1
    have hyx_pos : 0 < x - y := sub_pos.mpr hyx
    have hxy_mid : x - y < (x - alpha (N + 2) (N + 1)) / 2 := hxy
    have hrho : ThreePages.rho (N + 2) y = x - y := by
      have hrf := rhoFull_eq_lt_right (N := N) hN (x := y) hyx hxy_mid
      dsimp [rhoFull] at hrf
      change ThreePages.rho (N + 2) y = x - y
      exact hrf
    have hfac0 := abs_factor_full_pruned N y
    have hfac : |(approxPoly (N + 2)).eval y| = (y - alpha (N + 2) 1) * (x - y) * |(prunePoly N).eval y| := by
      rw [hfac0]
      have h1 : |y - alpha (N + 2) 1| = y - alpha (N + 2) 1 := abs_of_pos (sub_pos.mpr hy1)
      have h2 : |y - alpha (N + 2) (N + 2)| = x - y := by
        dsimp [x]
        rw [abs_sub_comm]
        exact abs_of_nonneg (sub_nonneg.mpr (le_of_lt hyx))
      rw [h1, h2]
    have hPALn := hPAL (N + 2) (by omega : 2 ≤ N + 2) y hyIcc
    have hmain' : ((N + 2 : ℕ) : ℝ) ^ (-C0) * (x - y) ≤
        (weight muS y) ^ (N + 2) * ((y - alpha (N + 2) 1) * (x - y) * |(prunePoly N).eval y|) := by
      calc
        ((N + 2 : ℕ) : ℝ) ^ (-C0) * (x - y)
            = ((N + 2 : ℕ) : ℝ) ^ (-C0) * ThreePages.rho (N + 2) y := by rw [hrho]
        _ ≤ (weight muS y) ^ (N + 2) * |(approxPoly (N + 2)).eval y| := hPALn
        _ = (weight muS y) ^ (N + 2) * ((y - alpha (N + 2) 1) * (x - y) * |(prunePoly N).eval y|) := by rw [hfac]
    have hmain'' : ((N + 2 : ℕ) : ℝ) ^ (-C0) * (x - y) ≤
        ((weight muS y) ^ (N + 2) * |(prunePoly N).eval y| * (y - alpha (N + 2) 1)) * (x - y) := by
      calc
        ((N + 2 : ℕ) : ℝ) ^ (-C0) * (x - y)
            ≤ (weight muS y) ^ (N + 2) * ((y - alpha (N + 2) 1) * (x - y) * |(prunePoly N).eval y|) := hmain'
        _ = ((weight muS y) ^ (N + 2) * |(prunePoly N).eval y| * (y - alpha (N + 2) 1)) * (x - y) := by ring
    have hcancel : ((N + 2 : ℕ) : ℝ) ^ (-C0) ≤
        (weight muS y) ^ (N + 2) * |(prunePoly N).eval y| * (y - alpha (N + 2) 1) := by
      exact le_of_mul_le_mul_right hmain'' hyx_pos
    change ((N + 2 : ℕ) : ℝ) ^ (-C0) ≤ f y
    simpa [f] using hcancel
  have hgap0 : ((N + 2 : ℕ) : ℝ) ^ (-C0) ≤
      (weight muS x) ^ (N + 2) * |(prunePoly N).eval x| * (x - alpha (N + 2) 1) := by
    have hc := const_le_of_forall_lt_near (x := x) (c := ((N + 2 : ℕ) : ℝ) ^ (-C0)) (f := f) hfcont hloc
    simpa [f] using hc
  -- ρKept(x) ≤ diam
  have hρ : rhoKept N x ≤ Dserre := by
    dsimp [x]
    exact rhoKept_le_diam hN1 hx
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hpowN : 0 ≤ (N : ℝ) ^ (-C) := Real.rpow_nonneg hN0 (-C)
  have hstep1 : (N : ℝ) ^ (-C) * rhoKept N x ≤ (N : ℝ) ^ (-C) * Dserre := by
    exact mul_le_mul_of_nonneg_left hρ hpowN
  have hstep2 : (N : ℝ) ^ (-C) * Dserre ≤
      Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / Dserre := by
    have hS' : (N : ℝ) ^ (-C) ≤ Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / Dserre ^ 2 :=
      hS N hN
    have hDle : 0 ≤ Dserre := le_of_lt Dserre_pos
    have hprod := mul_le_mul_of_nonneg_right hS' hDle
    calc
      (N : ℝ) ^ (-C) * Dserre ≤ (Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / Dserre ^ 2) * Dserre := hprod
      _ = Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / Dserre := by
        have hDne : Dserre ≠ 0 := ne_of_gt Dserre_pos
        field_simp [hDne]
  have hA0 : 0 ≤ ((N + 2 : ℕ) : ℝ) ^ (-C0) :=
    Real.rpow_nonneg (by positivity : 0 ≤ ((N + 2 : ℕ) : ℝ)) (-C0)
  have hxα1D : x - alpha (N + 2) 1 ≤ Dserre := by
    have hα1Icc : alpha (N + 2) 1 ∈ Set.Icc aSerre bSerre :=
      alpha_mem_Icc (n := N + 2) (i := 1) hn (by norm_num) (by omega)
    have habs : |x - alpha (N + 2) 1| ≤ Dserre := dist_le_diam hx hα1Icc
    rwa [abs_of_pos hxα1] at habs
  have hinv : Dserre⁻¹ ≤ (x - alpha (N + 2) 1)⁻¹ := by
    exact (inv_le_inv₀ Dserre_pos hxα1).mpr hxα1D
  have hA0e : 0 ≤ Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) :=
    mul_nonneg (Real.exp_pos (-Kshift)).le hA0
  have hstep3 : Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / Dserre ≤
      Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / (x - alpha (N + 2) 1) := by
    have hm := mul_le_mul_of_nonneg_left hinv hA0e
    simpa [div_eq_mul_inv, mul_assoc] using hm
  -- (d): A / (x−α1) ≤ w^{N+2}|P̃(x)|
  have hd0 : ((N + 2 : ℕ) : ℝ) ^ (-C0) ≤
      (weight muS x) ^ (N + 2) * |(prunePoly N).eval x| * (x - alpha (N + 2) 1) := hgap0
  have hd : ((N + 2 : ℕ) : ℝ) ^ (-C0) / (x - alpha (N + 2) 1) ≤
      (weight muS x) ^ (N + 2) * |(prunePoly N).eval x| := by
    exact (div_le_iff₀ hxα1).mpr hd0
  have hstep4 : Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ) ^ (-C0) / (x - alpha (N + 2) 1)) ≤
      Real.exp (-Kshift) * ((weight muS x) ^ (N + 2) * |(prunePoly N).eval x|) := by
    exact mul_le_mul_of_nonneg_left hd (Real.exp_pos (-Kshift)).le
  have hstep4' : Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / (x - alpha (N + 2) 1) ≤
      Real.exp (-Kshift) * ((weight muS x) ^ (N + 2) * |(prunePoly N).eval x|) := by
    calc
      Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / (x - alpha (N + 2) 1)
          = Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ) ^ (-C0) / (x - alpha (N + 2) 1)) := by ring
      _ ≤ Real.exp (-Kshift) * ((weight muS x) ^ (N + 2) * |(prunePoly N).eval x|) := hstep4
  have hPabs : 0 ≤ |(prunePoly N).eval x| := abs_nonneg _
  have hshift := weight_shift_lower hx N hs
  have h2 : Real.exp (-Kshift) * (weight muSerre x) ^ (N + 2) * |(prunePoly N).eval x| ≤
      (weight muSerre x) ^ (N + s) * |(prunePoly N).eval x| := by
    exact mul_le_mul_of_nonneg_right hshift hPabs
  have hstep5 : Real.exp (-Kshift) * ((weight muS x) ^ (N + 2) * |(prunePoly N).eval x|) ≤
      (weight muS x) ^ (N + s) * |(prunePoly N).eval x| := by
    calc
      Real.exp (-Kshift) * ((weight muS x) ^ (N + 2) * |(prunePoly N).eval x|)
          = Real.exp (-Kshift) * (weight muS x) ^ (N + 2) * |(prunePoly N).eval x| := by ring
      _ ≤ (weight muS x) ^ (N + s) * |(prunePoly N).eval x| := by
        simpa [muSerre] using h2
  calc
    (N : ℝ) ^ (-C) * rhoKept N x ≤ (N : ℝ) ^ (-C) * Dserre := hstep1
    _ ≤ Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / Dserre := hstep2
    _ ≤ Real.exp (-Kshift) * ((N + 2 : ℕ) : ℝ) ^ (-C0) / (x - alpha (N + 2) 1) := hstep3
    _ ≤ Real.exp (-Kshift) * ((weight muS x) ^ (N + 2) * |(prunePoly N).eval x|) := hstep4'
    _ ≤ (weight muS x) ^ (N + s) * |(prunePoly N).eval x| := hstep5

end Submission.PVer1LowerRight
