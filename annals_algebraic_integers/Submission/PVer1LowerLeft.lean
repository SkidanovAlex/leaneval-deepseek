import Submission.PVer1Base
import Submission.ScaleBoundLower
import Submission.ScaleBoundAny

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.PVer1LowerLeft

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

/-- On `(-∞, α_{N+2,2})` the kept distance `ρ_{P̃_N}` is attained at the
second root: `ρKept N y = α_{N+2,2} − y` whenever `y < α_{N+2,2}`. -/
lemma rhoKept_eq_under_second {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : y < alpha (N + 2) 2) :
    rhoKept N y = alpha (N + 2) 2 - y := by
  unfold rhoKept
  rw [dif_pos (kept_nonempty hN)]
  apply le_antisymm
  · have h2 : 2 ∈ kept N := by
      unfold kept
      rw [Finset.mem_Icc]
      omega
    calc
      (kept N).inf' (kept_nonempty hN) (fun i : ℕ => |y - alpha (N + 2) i|) ≤
          |y - alpha (N + 2) 2| := Finset.inf'_le (fun i : ℕ => |y - alpha (N + 2) i|) h2
      _ = alpha (N + 2) 2 - y := by
          rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy))]
          ring
  · apply Finset.le_inf' (kept_nonempty hN) (fun i : ℕ => |y - alpha (N + 2) i|)
    intro j hj
    have hjI : 2 ≤ j ∧ j ≤ N + 1 := by
      unfold kept at hj
      rwa [Finset.mem_Icc] at hj
    have h2j : alpha (N + 2) 2 ≤ alpha (N + 2) j := by
      by_cases hEq : j = 2
      · rw [hEq]
      · have hlt2 : 2 < j := by omega
        exact le_of_lt (alpha_strict_mono (n := N + 2) (by omega) (by norm_num) hlt2 (by omega))
    have hyj : y ≤ alpha (N + 2) j := le_trans (le_of_lt hy) h2j
    calc
      alpha (N + 2) 2 - y ≤ alpha (N + 2) j - y := by linarith [h2j]
      _ = |y - alpha (N + 2) j| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hyj)]
          ring
      _ = |y - alpha (N + 2) j| := rfl

/-- The regular (`0 < rhoFull N y`) weighted lower bound assembled from the
potential lower bound (exponent `C0`), the exponent shift `N+2 → N+s`, and the
scaling constant `Csc`; valid at every `y ∈ Icc aSerre bSerre` that is not a
root of the full approximating polynomial. -/
lemma regular_lower_bound {N : ℕ} (hN : 2 ≤ N) {s : ℕ} (hs : s ≤ Bclps.Dconst)
    (C0 : ℝ)
    (hC0bd : ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      ((n : ℕ) : ℝ) ^ (-C0) * rho n x ≤ (weight muS x) ^ n * |(approxPoly n).eval x|)
    (Csc : ℝ)
    (hCscbd : (N : ℝ) ^ (-Csc) ≤
      Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ)) ^ (-C0) / (bSerre - aSerre) ^ 2)
    {y : ℝ} (hy : y ∈ Set.Icc aSerre bSerre) (hρ : 0 < rhoFull N y) :
    (N : ℝ) ^ (-Csc) * rhoKept N y ≤
      (weight muS y) ^ (N + s) * |(prunePoly N).eval y| := by
  have hN1 : 1 ≤ N := by omega
  have hd2 : 2 ≤ N + 2 := by omega
  have hn : 1 ≤ N + 2 := by omega
  -- (i) potential lower bound at degree N+2
  have hPot : (((N + 2 : ℕ) : ℝ)) ^ (-C0) * rhoFull N y ≤
      (weight muS y) ^ (N + 2) * |(approxPoly (N + 2)).eval y| := by
    simpa [rhoFull] using hC0bd (N + 2) hd2 y hy
  -- (ii) factor the full polynomial
  have hPot2 : (((N + 2 : ℕ) : ℝ)) ^ (-C0) * rhoFull N y ≤
      (weight muS y) ^ (N + 2) *
        (|y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)| * |(prunePoly N).eval y|) := by
    rwa [abs_factor_full_pruned N y] at hPot
  -- (iii) ratio bound (needs 0 < rhoFull)
  have hRatio : 1 / (bSerre - aSerre) ^ 2 * rhoKept N y ≤
      rhoFull N y / (|y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)|) :=
    rhoKept_ratio_lower hN1 hy hρ
  -- A and B are strictly positive
  have hleA : rhoFull N y ≤ |y - alpha (N + 2) 1| := by
    unfold rhoFull
    exact rho_le_root (n := N + 2) hn y (by rw [Finset.mem_Icc]; omega)
  have hleB : rhoFull N y ≤ |y - alpha (N + 2) (N + 2)| := by
    unfold rhoFull
    exact rho_le_root (n := N + 2) hn y (by rw [Finset.mem_Icc]; omega)
  have hApos : 0 < |y - alpha (N + 2) 1| := lt_of_lt_of_le hρ hleA
  have hBpos : 0 < |y - alpha (N + 2) (N + 2)| := lt_of_lt_of_le hρ hleB
  have hABpos : 0 < |y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)| := mul_pos hApos hBpos
  have hRatioAB : ((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) *
        (|y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)|) ≤ rhoFull N y := by
    exact (le_div_iff₀ hABpos).mp hRatio
  have hL0nn : 0 ≤ (((N + 2 : ℕ) : ℝ)) ^ (-C0) :=
    Real.rpow_nonneg (by positivity : 0 ≤ (((N + 2 : ℕ) : ℝ))) (-C0)
  -- combine: divide the potential bound by A*B
  have hbase : (((N + 2 : ℕ) : ℝ)) ^ (-C0) * ((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) ≤
      (weight muS y) ^ (N + 2) * |(prunePoly N).eval y| := by
    have hmul : (((N + 2 : ℕ) : ℝ)) ^ (-C0) *
        (((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) *
          (|y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)|)) ≤
        (weight muS y) ^ (N + 2) * |(prunePoly N).eval y| *
          (|y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)|) := by
      calc
        (((N + 2 : ℕ) : ℝ)) ^ (-C0) *
            (((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) *
              (|y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)|))
            ≤ (((N + 2 : ℕ) : ℝ)) ^ (-C0) * rhoFull N y := by
                exact mul_le_mul_of_nonneg_left hRatioAB hL0nn
        _ ≤ (weight muS y) ^ (N + 2) * |(prunePoly N).eval y| *
              (|y - alpha (N + 2) 1| * |y - alpha (N + 2) (N + 2)|) := by
                nlinarith
    exact le_of_mul_le_mul_right (by simpa [mul_assoc] using hmul) hABpos
  -- (iv) exponent shift N+2 -> N+s
  have hshift : Real.exp (-Kshift) * (weight muS y) ^ (N + 2) ≤ (weight muS y) ^ (N + s) := by
    exact weight_shift_lower hy (N := N) hs
  have hbaseshift : Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ)) ^ (-C0) *
        ((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) ≤
      (weight muS y) ^ (N + s) * |(prunePoly N).eval y| := by
    have hstep1 : Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ)) ^ (-C0) *
          ((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) ≤
        Real.exp (-Kshift) * ((weight muS y) ^ (N + 2) * |(prunePoly N).eval y|) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg (-Kshift))
    have hstep2 : Real.exp (-Kshift) * ((weight muS y) ^ (N + 2) * |(prunePoly N).eval y|) ≤
        (weight muS y) ^ (N + s) * |(prunePoly N).eval y| := by
      calc
        Real.exp (-Kshift) * ((weight muS y) ^ (N + 2) * |(prunePoly N).eval y|)
            = (Real.exp (-Kshift) * (weight muS y) ^ (N + 2)) * |(prunePoly N).eval y| := by ring
        _ ≤ (weight muS y) ^ (N + s) * |(prunePoly N).eval y| := by
            exact mul_le_mul_of_nonneg_right hshift (abs_nonneg _)
    exact le_trans hstep1 hstep2
  -- (v) scaling: N^{-Csc} ≤ exp(-Kshift)·(N+2)^{-C0}/D²
  have hD2ne : (bSerre - aSerre) ^ 2 ≠ 0 := by
    have hD : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
    exact pow_ne_zero 2 (ne_of_gt hD)
  have hscale : (N : ℝ) ^ (-Csc) * rhoKept N y ≤
      Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ)) ^ (-C0) *
        ((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) := by
    calc
      (N : ℝ) ^ (-Csc) * rhoKept N y
          ≤ (Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ)) ^ (-C0) / (bSerre - aSerre) ^ 2) *
              rhoKept N y := by
              exact mul_le_mul_of_nonneg_right hCscbd (rhoKept_nonneg N y)
      _ = Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ)) ^ (-C0) *
              ((1 / (bSerre - aSerre) ^ 2) * rhoKept N y) := by
              field_simp [hD2ne]
  exact le_trans hscale hbaseshift

/-- The claim of `lower_left_root` with the two constants `C0`, `Csc` made
explicit (point at the pruned left extreme root `x0 = α_{N+2,1}`).  The bound
is proved just to the right of `x0`, where `0 < rhoFull N x` and
`rhoKept N x = α_{N+2,2} − x`, and then passed to the limit by continuity. -/
lemma lower_left_pt (C0 Csc : ℝ)
    (hC0bd : ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      ((n : ℕ) : ℝ) ^ (-C0) * rho n x ≤ (weight muS x) ^ n * |(approxPoly n).eval x|)
    {N : ℕ} (hN : 2 ≤ N) (s : ℕ) (hs : s ≤ Bclps.Dconst)
    (hCscN : (N : ℝ) ^ (-Csc) ≤
      Real.exp (-Kshift) * (((N + 2 : ℕ) : ℝ)) ^ (-C0) / (bSerre - aSerre) ^ 2) :
    (N : ℝ) ^ (-Csc) * rhoKept N (alpha (N + 2) 1) ≤
      (weight muS (alpha (N + 2) 1)) ^ (N + s) * |(prunePoly N).eval (alpha (N + 2) 1)| := by
  have hN1 : 1 ≤ N := by omega
  set x0 : ℝ := alpha (N + 2) 1 with hx0
  have hx0a2 : x0 < alpha (N + 2) 2 := by
    rw [hx0]
    exact alpha_strict_mono (n := N + 2) (by omega) (by norm_num) (by norm_num) (by omega)
  have haserre : aSerre ≤ x0 := by
    rw [hx0]
    exact (alpha_mem_Icc (n := N + 2) (i := 1) (by omega) (by norm_num) (by omega)).1
  have ha2b : alpha (N + 2) 2 ≤ bSerre :=
    (alpha_mem_Icc (n := N + 2) (i := 2) (by omega) (by norm_num) (by omega)).2
  let δ : ℝ := (alpha (N + 2) 2 - x0) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  let F : ℝ → ℝ := fun z =>
    (weight muS z) ^ (N + s) * |(prunePoly N).eval z| - (N : ℝ) ^ (-Csc) * (alpha (N + 2) 2 - z)
  have hg : ContinuousAt (fun z : ℝ => (weight muS z) ^ (N + s) * |(prunePoly N).eval z|) x0 :=
    (continuous_weight_pow_eval (N + s) (prunePoly N)).continuousAt
  have hl : ContinuousAt (fun z : ℝ => (N : ℝ) ^ (-Csc) * (alpha (N + 2) 2 - z)) x0 := by
    have hsub : ContinuousAt (fun z : ℝ => alpha (N + 2) 2 - z) x0 :=
      (continuousAt_const (y := alpha (N + 2) 2)).sub continuousAt_id
    exact (continuousAt_const (y := (N : ℝ) ^ (-Csc))).mul hsub
  have hFcont : ContinuousAt F x0 := by
    dsimp [F]
    exact hg.sub hl
  have hnear : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ y : ℝ, x0 < y → y - x0 < δ0 → 0 ≤ F y := by
    refine ⟨δ, hδpos, ?_⟩
    intro y hygt hyδ
    dsimp [F]
    have hyI : y ∈ Set.Icc aSerre bSerre := by
      constructor
      · linarith [haserre, hygt]
      · have hb : y ≤ alpha (N + 2) 2 := by
          dsimp [δ] at hyδ
          linarith [hx0a2, hyδ]
        exact le_trans hb ha2b
    have hρ : 0 < rhoFull N y := by
      have hA : alpha (N + 2) 1 < y := by rwa [← hx0]
      have hd : y - alpha (N + 2) 1 < (alpha (N + 2) 2 - alpha (N + 2) 1) / 2 := by
        dsimp [δ] at hyδ
        linarith [hx0]
      have hval := rhoFull_eq_gt_left hN hA hd
      rw [hval]
      linarith [hA]
    have hbnd := regular_lower_bound hN hs C0 hC0bd Csc hCscN hyI hρ
    have hylt : y < alpha (N + 2) 2 := by
      dsimp [δ] at hyδ
      linarith [hx0a2, hyδ]
    have hrk : rhoKept N y = alpha (N + 2) 2 - y := rhoKept_eq_under_second hN1 hylt
    rw [hrk] at hbnd
    linarith
  have hx0pos : 0 ≤ F x0 := const_le_of_forall_gt_near (f := F) hFcont hnear
  have hrk0 : rhoKept N x0 = alpha (N + 2) 2 - x0 := rhoKept_eq_under_second hN1 hx0a2
  dsimp [F] at hx0pos
  rw [hrk0]
  linarith

lemma lower_left_root :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ s : ℕ, s ≤ Bclps.Dconst →
      (N : ℝ) ^ (-C) * rhoKept N (alpha (N + 2) 1) ≤
        (weight muS (alpha (N + 2) 1)) ^ (N + s) * |(prunePoly N).eval (alpha (N + 2) 1)| := by
  rcases potential_approx_lower with ⟨C0, hC0pos, hC0⟩
  have hD1 : 1 ≤ bSerre - aSerre := by simpa [Dserre] using Dserre_ge_one
  rcases scale_bound_gen C0 Kshift (bSerre - aSerre) hC0pos Kshift_nonneg hD1 with ⟨Csc, hCscpos, hCsc⟩
  refine ⟨Csc, hCscpos, ?_⟩
  intro N hN s hs
  exact lower_left_pt C0 Csc hC0 hN s hs (hCsc N hN)

end Submission.PVer1LowerLeft
