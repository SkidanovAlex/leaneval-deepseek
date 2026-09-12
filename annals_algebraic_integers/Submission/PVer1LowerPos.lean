import Submission.PVer1Base
import Submission.ScaleBoundLower
import Submission.ScaleBoundAny

/-!
# Weighted lower bound on `Σ = [aSerre,bSerre]` away from the pruned roots

`Submission.PVer1LowerPos.lower_pos` is the pointwise weighted lower bound of
`lem:P_ver1(2)` specialised to points `x` where the *full* distance
`rhoFull N x = ρ_{N+2}(x)` is positive (i.e. `x` is not one of the roots of
the degree-`(N+2)` approximating polynomial):

    ∃ C > 0, ∀ N ≥ 2, ∀ s ≤ Dconst, ∀ x ∈ [aSerre,bSerre], 0 < rhoFull N x :
        N^{-C}·ρKept_N(x) ≤ w_μ(x)^{N+s}·|P̃_N(x)|

Here `w_μ = weight muS`, `P̃_N = prunePoly N`, `ρKept_N = rhoKept N` and
`muS` is (definitionally) the same Serre measure `muSerre` used by the
explicit potential/weight estimates.

## Proof route

* `ThreePages.potential_approx_lower` at degree `n = N+2` gives
  `(N+2)^{-C1}·ρ_{N+2}(x) ≤ w^{N+2}·|P_{N+2}(x)|`; factor
  `|P_{N+2}(x)| = |x−α₁|·|x−α_{N+2}|·|P̃_N(x)|`
  (`PVer1.abs_factor_full_pruned`) and divide by `|x−α₁|·|x−α_{N+2}| > 0`
  (positive because `0 < rhoFull N x` and `rhoFull ≤` each factor).
* `PVer1.exists_full_ratio_lower` gives
  `ρKept_N(x)/C_l ≤ ρ_{N+2}(x)/(|x−α₁|·|x−α_{N+2}|)` (its constant `C_l > 0`).
* shift the exponent `N+2 ↦ N+s` by `PVer1.weight_shift_lower` at the cost
  of the fixed factor `e^{-Kshift}`;
* absorb the fixed constants with `exists_scaling` below
  (`N^{-C} ≤ e^{-Kshift}·(N+2)^{-C1}/C_l` for a large enough `C`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.PVer1LowerPos

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

/-- Generic `N^{-C}` scaling with an arbitrary positive divisor `M > 0`:
`∃ C > 0, ∀ N ≥ 2, N^{-C} ≤ e^{-K}·(N+2)^{-C1}/M` for `0 < C1`. -/
lemma exists_scaling (C1 K M : ℝ) (hC1 : 0 < C1) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (N : ℝ) ^ (-C) ≤ Real.exp (-K) * ((N + 2 : ℕ) : ℝ) ^ (-C1) / M := by
  let M1 : ℝ := Real.exp K * M * (2 : ℝ) ^ C1
  have hM1pos : 0 < M1 := by
    dsimp [M1]
    exact mul_pos (mul_pos (Real.exp_pos K) hM)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) C1)
  have hmax1 : 1 ≤ max M1 1 := le_max_right M1 1
  rcases ScaleBoundLower.exists_large_rpow (M := max M1 1) hmax1 with ⟨A, hA0, hA⟩
  refine ⟨C1 + A, by linarith, ?_⟩
  intro N hN
  let x : ℝ := (N : ℝ)
  let t : ℝ := ((N + 2 : ℕ) : ℝ)
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hN
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx2
  have hxge0 : 0 ≤ x := le_of_lt hxpos
  have htpos : 0 < t := by dsimp [t]; exact_mod_cast (by omega : 0 < N + 2)
  have htge0 : 0 ≤ t := le_of_lt htpos
  have ht2 : t ≤ 2 * x := by
    dsimp [x, t]
    norm_num
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hmono : t ^ C1 ≤ (2 * x) ^ C1 := Real.rpow_le_rpow htge0 ht2 (le_of_lt hC1)
  have hmul : (2 * x) ^ C1 = (2 : ℝ) ^ C1 * x ^ C1 :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxge0
  have hA_N : M1 ≤ x ^ A := by
    dsimp [M1, x]
    exact le_trans (le_max_left M1 1) (hA N hN)
  have hmain : Real.exp K * M * t ^ C1 ≤ x ^ (C1 + A) := by
    calc
      Real.exp K * M * t ^ C1
          ≤ Real.exp K * M * (2 * x) ^ C1 := by
              exact mul_le_mul_of_nonneg_left hmono (mul_pos (Real.exp_pos K) hM).le
      _ = M1 * x ^ C1 := by
          dsimp [M1]
          rw [hmul]
          ring
      _ ≤ x ^ A * x ^ C1 := by
              exact mul_le_mul_of_nonneg_right hA_N (Real.rpow_nonneg hxge0 C1)
      _ = x ^ (C1 + A) := by
          rw [mul_comm]
          rw [← Real.rpow_add hxpos C1 A]
  have hden : 0 < Real.exp K * M * t ^ C1 := by
    exact mul_pos (mul_pos (Real.exp_pos K) hM) (Real.rpow_pos_of_pos htpos C1)
  have hxpow : 0 < x ^ (C1 + A) := Real.rpow_pos_of_pos hxpos (C1 + A)
  have hinv : (x ^ (C1 + A))⁻¹ ≤ (Real.exp K * M * t ^ C1)⁻¹ :=
    (inv_le_inv₀ hxpow hden).mpr hmain
  calc
    (N : ℝ) ^ (-(C1 + A)) = x ^ (-(C1 + A)) := by dsimp [x]
    _ = (x ^ (C1 + A))⁻¹ := by rw [Real.rpow_neg hxge0]
    _ ≤ (Real.exp K * M * t ^ C1)⁻¹ := hinv
    _ = (Real.exp K)⁻¹ * (t ^ C1)⁻¹ / M := by
        field_simp [ne_of_gt (Real.exp_pos K), ne_of_gt (Real.rpow_pos_of_pos htpos C1), ne_of_gt hM]
    _ = Real.exp (-K) * t ^ (-C1) / M := by
        rw [Real.exp_neg]
        rw [Real.rpow_neg (le_of_lt htpos)]

lemma lower_pos :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ s : ℕ, s ≤ Bclps.Dconst →
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → 0 < rhoFull N x →
        (N : ℝ) ^ (-C) * rhoKept N x ≤
          (weight muS x) ^ (N + s) * |(prunePoly N).eval x| := by
  rcases ThreePages.potential_approx_lower with ⟨C1, hC1pos, hC1⟩
  rcases exists_full_ratio_lower with ⟨Cl, hClpos, hCl⟩
  rcases exists_scaling C1 Kshift Cl hC1pos hClpos with ⟨C, hCpos, hCscale⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN s hs x hx hρ
  have hN1 : 1 ≤ N := by omega
  have hn1 : 1 ≤ N + 2 := by omega
  have hd2 : 2 ≤ N + 2 := by omega
  let A : ℝ := |x - alpha (N + 2) 1|
  let B : ℝ := |x - alpha (N + 2) (N + 2)|
  let t : ℝ := ((N + 2 : ℕ) : ℝ) ^ (-C1)
  let PP : ℝ := |(prunePoly N).eval x|
  have hTge0 : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ N + 2) : 0 ≤ ((N + 2 : ℕ) : ℝ)) (-C1)
  have hleA : rhoFull N x ≤ A := by
    dsimp [A]
    unfold rhoFull
    exact rho_le_root (n := N + 2) hn1 x (by rw [Finset.mem_Icc]; omega)
  have hleB : rhoFull N x ≤ B := by
    dsimp [B]
    unfold rhoFull
    exact rho_le_root (n := N + 2) hn1 x (by rw [Finset.mem_Icc]; omega)
  have hApos : 0 < A := lt_of_lt_of_le hρ hleA
  have hBpos : 0 < B := lt_of_lt_of_le hρ hleB
  have hABpos : 0 < A * B := mul_pos hApos hBpos
  have hratio : (1 / Cl) * rhoKept N x ≤ rhoFull N x / (A * B) := by
    simpa [A, B] using (hCl N hN1 x hx hρ)
  have hpot0 : t * rhoFull N x ≤ (weight muS x) ^ (N + 2) * |(approxPoly (N + 2)).eval x| := by
    dsimp [t]
    simpa [rhoFull] using (hC1 (N + 2) hd2 x hx)
  have hfac : |(approxPoly (N + 2)).eval x| = A * B * PP := by
    simpa [A, B, PP] using (abs_factor_full_pruned N x)
  have hpot2 : t * rhoFull N x ≤ (weight muS x) ^ (N + 2) * (A * B * PP) := by
    calc
      t * rhoFull N x ≤ (weight muS x) ^ (N + 2) * |(approxPoly (N + 2)).eval x| := hpot0
      _ = (weight muS x) ^ (N + 2) * (A * B * PP) := by rw [hfac]
  have hdiv : t * (rhoFull N x / (A * B)) ≤ (weight muS x) ^ (N + 2) * PP := by
    calc
      t * (rhoFull N x / (A * B)) = (t * rhoFull N x) / (A * B) := by ring
      _ ≤ (weight muS x) ^ (N + 2) * PP := by
        rw [div_le_iff₀ hABpos]
        calc
          t * rhoFull N x ≤ (weight muS x) ^ (N + 2) * (A * B * PP) := hpot2
          _ = ((weight muS x) ^ (N + 2) * PP) * (A * B) := by ring
  have hratio_mul : t * ((1 / Cl) * rhoKept N x) ≤ (weight muS x) ^ (N + 2) * PP := by
    calc
      t * ((1 / Cl) * rhoKept N x) ≤ t * (rhoFull N x / (A * B)) := by
          exact mul_le_mul_of_nonneg_left hratio hTge0
      _ ≤ (weight muS x) ^ (N + 2) * PP := hdiv
  have hws0 : Real.exp (-Kshift) * (weight muSerre x) ^ (N + 2) ≤ (weight muSerre x) ^ (N + s) :=
    weight_shift_lower hx N hs
  have hws : Real.exp (-Kshift) * (weight muS x) ^ (N + 2) ≤ (weight muS x) ^ (N + s) := by
    simpa [muSerre] using hws0
  have hshift : Real.exp (-Kshift) * ((weight muS x) ^ (N + 2) * PP) ≤
      (weight muS x) ^ (N + s) * PP := by
    calc
      Real.exp (-Kshift) * (((weight muS x) ^ (N + 2)) * PP)
          = (Real.exp (-Kshift) * (weight muS x) ^ (N + 2)) * PP := by ring
      _ ≤ (weight muS x) ^ (N + s) * PP := by
        exact mul_le_mul_of_nonneg_right hws (abs_nonneg ((prunePoly N).eval x))
  have hstep2 : Real.exp (-Kshift) * (t * ((1 / Cl) * rhoKept N x)) ≤
      (weight muS x) ^ (N + s) * PP := by
    calc
      Real.exp (-Kshift) * (t * ((1 / Cl) * rhoKept N x))
          ≤ Real.exp (-Kshift) * (((weight muS x) ^ (N + 2)) * PP) := by
              exact mul_le_mul_of_nonneg_left hratio_mul (Real.exp_pos (-Kshift)).le
      _ ≤ (weight muS x) ^ (N + s) * PP := hshift
  have hsc := hCscale N hN
  have hstep3 : (N : ℝ) ^ (-C) * rhoKept N x ≤
      Real.exp (-Kshift) * (t * ((1 / Cl) * rhoKept N x)) := by
    calc
      (N : ℝ) ^ (-C) * rhoKept N x ≤ (Real.exp (-Kshift) * t / Cl) * rhoKept N x := by
          exact mul_le_mul_of_nonneg_right hsc (rhoKept_nonneg N x)
      _ = Real.exp (-Kshift) * (t * ((1 / Cl) * rhoKept N x)) := by ring
  simpa [PP] using le_trans hstep3 hstep2
end Submission.PVer1LowerPos
