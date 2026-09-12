import Submission.PVer1Base
import Submission.ScaleBoundLower
import Submission.ScaleBoundAny

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.PVer1UpperPtw

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

/-- If a continuous function is `≤ c` for all points to the left of `x`
(arbitrarily close), then `f x ≤ c`. -/
lemma le_const_of_forall_lt_near {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y < x → x - y < δ → f y ≤ c) : f x ≤ c := by
  by_contra hnot
  have hgt : c < f x := lt_of_not_ge hnot
  let ε : ℝ := (f x - c) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  rcases hδ with ⟨δ0, hδ0pos, hδ0⟩
  have hmet := Metric.continuousAt_iff.mp hf ε hε
  rcases hmet with ⟨δ1, hδ1pos, hδ1⟩
  let δ : ℝ := min δ0 δ1
  have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
  let y : ℝ := x - δ / 2
  have hltx : y < x := by
    dsimp [y]
    linarith
  have hdiff : x - y = δ / 2 := by
    dsimp [y]
    ring
  have hdy0 : x - y < δ0 := by
    rw [hdiff]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_left δ0 δ1)
  have hyc : f y ≤ c := hδ0 y hltx hdy0
  have hdy1 : |y - x| < δ1 := by
    have hd : |y - x| = δ / 2 := by
      rw [abs_sub_comm]
      have hlt : 0 < x - y := by linarith
      rw [abs_of_pos hlt]
      exact hdiff
    rw [hd]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_right δ0 δ1)
  have hclose : |f y - f x| < ε := hδ1 hdy1
  have hfy : f y > c := by
    dsimp [ε] at hclose
    have h1 : -((f x - c) / 2) < f y - f x := (abs_lt.mp hclose).1
    linarith
  exact (not_lt_of_ge hyc) hfy

lemma upper_ptwise :
    ∃ Cu Cc : ℝ, 0 < Cu ∧ 0 < Cc ∧
      ∀ N : ℕ, 2 ≤ N → ∀ s : ℕ, s ≤ Bclps.Dconst →
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        (weight muSerre x) ^ (N + s) * |(prunePoly N).eval x| ≤
          Real.exp Kshift * ((N + 2 : ℕ) : ℝ) ^ Cu * Cc := by
  rcases ThreePages.potential_approx_upper with ⟨Cp, hCp, hUp⟩
  rcases exists_full_ratio_upper with ⟨Cr, hCr, hRat⟩
  refine ⟨Cp, Cr, hCp, hCr, ?_⟩
  intro N hN s hs x hx
  have hN1 : 1 ≤ N := by omega
  have hNp : 1 ≤ N + 2 := by omega
  have hd2 : 2 ≤ N + 2 := by omega
  let M : ℝ := Real.exp Kshift * ((N + 2 : ℕ) : ℝ) ^ Cp * Cr
  let f : ℝ → ℝ := fun y : ℝ => (weight muSerre y) ^ (N + s) * |(prunePoly N).eval y|
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have hcont : Continuous f := by
    dsimp [f]
    simpa [muSerre] using (continuous_weight_pow_eval (N + s) (prunePoly N))
  have hmain : ∀ y : ℝ, y ∈ Set.Icc aSerre bSerre → 0 < rhoFull N y → f y ≤ M := by
    intro y hy hρ
    have hρnn : 0 ≤ rhoFull N y := by
      unfold rhoFull
      exact rho_nonneg (n := N + 2) y
    let A : ℝ := |y - alpha (N + 2) 1|
    let B : ℝ := |y - alpha (N + 2) (N + 2)|
    let PP : ℝ := |(prunePoly N).eval y|
    have hleA : rhoFull N y ≤ A := by
      unfold rhoFull A
      exact rho_le_root (n := N + 2) hNp y (by rw [Finset.mem_Icc]; omega)
    have hleB : rhoFull N y ≤ B := by
      unfold rhoFull B
      exact rho_le_root (n := N + 2) hNp y (by rw [Finset.mem_Icc]; omega)
    have hApos : 0 < A := lt_of_lt_of_le hρ hleA
    have hBpos : 0 < B := lt_of_lt_of_le hρ hleB
    have hABpos : 0 < A * B := mul_pos hApos hBpos
    have hpot0 : (weight muS y) ^ (N + 2) * |(approxPoly (N + 2)).eval y| ≤
        ((N + 2 : ℕ) : ℝ) ^ Cp * rho (N + 2) y := hUp (N + 2) hd2 y hy
    have hpot : (weight muSerre y) ^ (N + 2) * |(approxPoly (N + 2)).eval y| ≤
        ((N + 2 : ℕ) : ℝ) ^ Cp * rho (N + 2) y := by
      simpa [muSerre] using hpot0
    have hpotF : (weight muSerre y) ^ (N + 2) * |(approxPoly (N + 2)).eval y| ≤
        ((N + 2 : ℕ) : ℝ) ^ Cp * rhoFull N y := by
      simpa [rhoFull] using hpot
    have hfac : |(approxPoly (N + 2)).eval y| = A * B * PP := by
      simpa [A, B, PP] using (abs_factor_full_pruned N y)
    have hppr : (weight muSerre y) ^ (N + 2) * (A * B * PP) ≤
        ((N + 2 : ℕ) : ℝ) ^ Cp * rhoFull N y := by
      calc
        (weight muSerre y) ^ (N + 2) * (A * B * PP)
            = (weight muSerre y) ^ (N + 2) * |(approxPoly (N + 2)).eval y| := by
                rw [← hfac]
        _ ≤ ((N + 2 : ℕ) : ℝ) ^ Cp * rhoFull N y := hpotF
    have hppr2 : ((weight muSerre y) ^ (N + 2) * PP) * (A * B) ≤
        ((N + 2 : ℕ) : ℝ) ^ Cp * rhoFull N y := by
      have hconv : (weight muSerre y) ^ (N + 2) * (A * B * PP) =
          ((weight muSerre y) ^ (N + 2) * PP) * (A * B) := by ring
      rwa [hconv] at hppr
    have hdiv : (weight muSerre y) ^ (N + 2) * PP ≤
        ((N + 2 : ℕ) : ℝ) ^ Cp * (rhoFull N y / (A * B)) := by
      calc
        (weight muSerre y) ^ (N + 2) * PP ≤
            (((N + 2 : ℕ) : ℝ) ^ Cp * rhoFull N y) / (A * B) :=
              (le_div_iff₀ hABpos).2 hppr2
        _ = ((N + 2 : ℕ) : ℝ) ^ Cp * (rhoFull N y / (A * B)) := by
              rw [mul_div_assoc]
    have hpowCp : 0 ≤ ((N + 2 : ℕ) : ℝ) ^ Cp := by
      exact Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ N + 2)) Cp
    have hrat : rhoFull N y / (A * B) ≤ Cr := by
      simpa [A, B] using (hRat N hN1 y hy hρ)
    have hstep : ((N + 2 : ℕ) : ℝ) ^ Cp * (rhoFull N y / (A * B)) ≤
        ((N + 2 : ℕ) : ℝ) ^ Cp * Cr := by
      exact mul_le_mul_of_nonneg_left hrat hpowCp
    have hwPP : (weight muSerre y) ^ (N + 2) * PP ≤ ((N + 2 : ℕ) : ℝ) ^ Cp * Cr := by
      exact le_trans hdiv hstep
    have hws : (weight muSerre y) ^ (N + s) ≤ Real.exp Kshift * (weight muSerre y) ^ (N + 2) :=
      weight_shift_upper hy N hs
    have h1 : f y ≤ Real.exp Kshift * (weight muSerre y) ^ (N + 2) * PP := by
      calc
        f y = (weight muSerre y) ^ (N + s) * PP := by simp [f, PP]
        _ ≤ (Real.exp Kshift * (weight muSerre y) ^ (N + 2)) * PP := by
            exact mul_le_mul_of_nonneg_right hws (abs_nonneg ((prunePoly N).eval y))
        _ = Real.exp Kshift * (weight muSerre y) ^ (N + 2) * PP := by ring
    have h2 : Real.exp Kshift * ((weight muSerre y) ^ (N + 2) * PP) ≤
        Real.exp Kshift * (((N + 2 : ℕ) : ℝ) ^ Cp * Cr) := by
      exact mul_le_mul_of_nonneg_left hwPP (Real.exp_pos Kshift).le
    calc
      f y ≤ Real.exp Kshift * (weight muSerre y) ^ (N + 2) * PP := h1
      _ = Real.exp Kshift * ((weight muSerre y) ^ (N + 2) * PP) := by ring
      _ ≤ Real.exp Kshift * (((N + 2 : ℕ) : ℝ) ^ Cp * Cr) := h2
      _ = M := by
          dsimp [M]
          ring
  have hmainall : ∀ y : ℝ, y ∈ Set.Icc aSerre bSerre →
      y ≠ alpha (N + 2) 1 → y ≠ alpha (N + 2) (N + 2) → f y ≤ M := by
    intro y hy hy1 hyT
    by_cases hρ0 : rhoFull N y = 0
    · rcases exists_index_rho (n := N + 2) hNp y with ⟨i, hi, hatt⟩
      have hrho0 : rho (N + 2) y = 0 := by
        unfold rhoFull at hρ0
        exact hρ0
      have habs : |y - alpha (N + 2) i| = 0 := by
        calc
          |y - alpha (N + 2) i| = rho (N + 2) y := hatt.symm
          _ = 0 := hrho0
      have hyi : y = alpha (N + 2) i := by
        have hsub : y - alpha (N + 2) i = 0 := abs_eq_zero.mp habs
        linarith
      have hine : i ≠ 1 := by
        intro hEq
        have hyEq : y = alpha (N + 2) 1 := by
          simpa [hEq] using hyi
        exact hy1 hyEq
      have hinT : i ≠ N + 2 := by
        intro hEq
        have hyEq : y = alpha (N + 2) (N + 2) := by
          simpa [hEq] using hyi
        exact hyT hyEq
      have hiKept : i ∈ kept N := by
        unfold kept
        rw [Finset.mem_Icc]
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hin : i ≤ N + 2 := (Finset.mem_Icc.mp hi).2
        omega
      have hPf : (prunePoly N).eval y = 0 := by
        rw [prunePoly_eval]
        exact Finset.prod_eq_zero hiKept (by simp [hyi])
      have hfy : f y = 0 := by
        dsimp [f]
        simp [hPf]
      rw [hfy]
      exact hMnn
    · have hρpos : 0 < rhoFull N y := lt_of_le_of_ne
        (by unfold rhoFull; exact rho_nonneg (n := N + 2) y) (Ne.symm hρ0)
      exact hmain y hy hρpos
  let A1 : ℝ := alpha (N + 2) 1
  let AT : ℝ := alpha (N + 2) (N + 2)
  have hA1I : A1 ∈ Set.Icc aSerre bSerre := by
    dsimp [A1]
    exact alpha_mem_Icc hNp (by norm_num) (by omega)
  have hATI : AT ∈ Set.Icc aSerre bSerre := by
    dsimp [AT]
    exact alpha_mem_Icc hNp (by omega) (by omega)
  have hA1T : A1 < AT := by
    dsimp [A1, AT]
    exact alpha_strict_mono hNp (by norm_num) (by omega) (by omega)
  let δ : ℝ := (AT - A1) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos (sub_pos.mpr hA1T) (by norm_num)
  have hAtA1 : f A1 ≤ M := by
    apply le_const_of_forall_gt_near (f := f) (x := A1) (c := M)
    · exact hcont.continuousAt
    · refine ⟨δ, hδpos, ?_⟩
      intro y hyA1 hyd
      have hyI : y ∈ Set.Icc aSerre bSerre := by
        constructor
        · linarith [hA1I.1, hyA1]
        · have hyb : y < A1 + δ := by linarith
          have hδeq : A1 + δ = (A1 + AT) / 2 := by dsimp [δ]; ring
          have hhalf : (A1 + AT) / 2 < AT := by linarith
          have hATb : AT ≤ bSerre := hATI.2
          linarith
      have hyne1 : y ≠ A1 := by linarith
      have hyneT : y ≠ AT := by
        intro hEq
        have hyb : y < A1 + δ := by linarith
        have hδeq : A1 + δ = (A1 + AT) / 2 := by dsimp [δ]; ring
        have hhalf : (A1 + AT) / 2 < AT := by linarith
        linarith
      exact hmainall y hyI hyne1 hyneT
  have hAtAT : f AT ≤ M := by
    apply le_const_of_forall_lt_near (f := f) (x := AT) (c := M)
    · exact hcont.continuousAt
    · refine ⟨δ, hδpos, ?_⟩
      intro y hyAT hyd
      have hyI : y ∈ Set.Icc aSerre bSerre := by
        constructor
        · have hyg : AT - δ < y := by linarith [hyd]
          have hδeq : AT - δ = (A1 + AT) / 2 := by dsimp [δ]; ring
          have hA1b : aSerre ≤ A1 := hA1I.1
          have hmid : A1 ≤ (A1 + AT) / 2 := by linarith
          linarith
        · linarith [hATI.2, hyAT]
      have hyne1 : y ≠ A1 := by
        intro hEq
        have hyg : AT - δ < y := by linarith [hyd]
        have hδeq : AT - δ = (A1 + AT) / 2 := by dsimp [δ]; ring
        have hmid : A1 < (A1 + AT) / 2 := by linarith
        linarith
      have hyneT : y ≠ AT := by linarith
      exact hmainall y hyI hyne1 hyneT
  by_cases hx1 : x = A1
  · rw [hx1]
    exact hAtA1
  · by_cases hxT : x = AT
    · rw [hxT]
      exact hAtAT
    · have hbd := hmainall x hx hx1 hxT
      simpa [M, f] using hbd
end Submission.PVer1UpperPtw
