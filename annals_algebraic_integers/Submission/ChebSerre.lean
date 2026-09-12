import Submission.SerreExample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic

/-!
# Full Chebyshev alternation structure for the Serre interval

For `Σ = [aSerre, bSerre]`, κ := (b−a)/4 > 1, every degree `N ≥ 1` has a
real monic polynomial `T` of degree `N` with:

* all `N` roots real, distinct, inside the OPEN interval `(aSerre, bSerre)`;
* `N+1` alternating extremal points `x_0 > x_1 > … > x_N` in `[aSerre,bSerre]`
  with `|T(x_i)| = 2·κ^N` and alternating signs; and
* one root strictly between consecutive extremal points.

This is the affine image of the classical Chebyshev polynomial `T_N`
(Mathlib: `Polynomial.Chebyshev.T ℝ N`): if `L(x) = (2x−a−b)/(b−a)`, then
`T = C(2κ^N) · (T_N ∘ L)`, with extremal points `x_i = L⁻¹(cos(iπ/N))`
(`cos` decreasing on `[0,π]`, so `x_0 = b > … > x_N = a`) and roots
`L⁻¹(cos((2k+1)π/(2N)))` interleaved.

These facts are the input to the pruned/“adjusted Chebyshev” step of the
early-integer-coefficient construction (Smith, adjust.tex, Lemmas
`lem:Chebyshev`, `lem:adjusted_Cheb`).
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.ChebSerre

open Submission.SerreExample

/-- Capacity constant of the Serre interval (same as `Contracts.kappa`). -/
noncomputable def kappaC : ℝ := (bSerre - aSerre) / 4

/-- κ > 1. -/
lemma kappaC_gt_one : 1 < kappaC := by
  unfold kappaC
  norm_num [aSerre, bSerre]

/-- Affine normalizer `L(x) = (2x − a − b)/(b − a)` sending `[a,b]` onto `[−1,1]`. -/
noncomputable def intervalL : Polynomial ℝ :=
  C (2 / (bSerre - aSerre)) * (X - C ((aSerre + bSerre) / 2))

/-- Evaluation of the normalizer. -/
lemma intervalL_eval (x : ℝ) :
    intervalL.eval x = (2 * x - (aSerre + bSerre)) / (bSerre - aSerre) := by
  simp only [intervalL, eval_mul, eval_sub, eval_X, eval_C]
  have hb : bSerre - aSerre ≠ 0 := by norm_num [aSerre, bSerre]
  field_simp [hb]

/-- The monic Chebyshev polynomial of degree `N` of the Serre interval:
`2κ^N · T_N(L(x))`. -/
noncomputable def chebT (N : ℕ) : Polynomial ℝ :=
  C (2 * kappaC ^ N) * (Polynomial.Chebyshev.T ℝ (N : ℤ)).comp intervalL

/-- Evaluation of `chebT` at the point whose `L`-value is `cos θ`
(where `N` is the degree). -/
lemma chebT_eval_cos (N : ℕ) (θ : ℝ) :
    (chebT N).eval ((aSerre + bSerre) / 2 + (bSerre - aSerre) / 2 * Real.cos θ) =
      2 * kappaC ^ N * Real.cos ((N : ℝ) * θ) := by
  unfold chebT
  rw [eval_mul, eval_comp]
  simp only [eval_C]
  have hL : intervalL.eval ((aSerre + bSerre) / 2 + (bSerre - aSerre) / 2 * Real.cos θ) =
      Real.cos θ := by
    rw [intervalL_eval]
    have hb : bSerre - aSerre ≠ 0 := by norm_num [aSerre, bSerre]
    field_simp [hb]
    ring
  rw [hL, Polynomial.Chebyshev.T_real_cos]
  norm_cast

/-- Classical Chebyshev evaluated at its extremal points: `T_N(cos(kπ/N)) = (−1)^k`. -/
lemma T_real_cos_mul_pi_div_negOnePow (N k : ℕ) (hN : N ≠ 0) (_hk : k ≤ N) :
    (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval (Real.cos (k * Real.pi / (N : ℝ))) =
      ((-1 : ℝ) ^ k) := by
  have h := Polynomial.Chebyshev.eval_T_real_cos_int_mul_pi_div (n := N) (k := k) hN
  -- T.eval (cos (k·π/N)) = (−1)^k for the real cast of k
  rw [h]
  norm_num [Int.cast_negOnePow]

/-- Image under the affine inverse of the normalizer: the point of `[a,b]` with
`L`-value `t ∈ [−1,1]` is `(a+b)/2 + (b−a)/2·t`. -/
def chebPoint (t : ℝ) : ℝ :=
  (aSerre + bSerre) / 2 + (bSerre - aSerre) / 2 * t

/-- `chebPoint` is the affine inverse of `L` on the line. -/
lemma intervalL_chebPoint (t : ℝ) : intervalL.eval (chebPoint t) = t := by
  rw [intervalL_eval, chebPoint]
  have hb : bSerre - aSerre ≠ 0 := by norm_num [aSerre, bSerre]
  field_simp [hb]
  ring

-- Piece A: monic / natDegree

private lemma h_ba_pos : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
private lemma h_ba_ne : bSerre - aSerre ≠ 0 := ne_of_gt h_ba_pos
private lemma kappa_pos : 0 < kappaC := by
  unfold kappaC
  exact div_pos h_ba_pos (by norm_num)

private lemma cheb_scale_lc_m {w : ℝ} (hw : w ≠ 0) (m : ℕ) :
    (2 * (w / 4) ^ (m + 1)) * (2 ^ m) * (2 / w) ^ (m + 1) = 1 := by
  have h24 : (w / 4) * (2 / w) = 1 / 2 := by
    field_simp [hw]
    ring
  calc
    (2 * (w / 4) ^ (m + 1)) * (2 ^ m) * (2 / w) ^ (m + 1)
        = 2 * 2 ^ m * ((w / 4) ^ (m + 1) * (2 / w) ^ (m + 1)) := by ring
    _ = 2 * 2 ^ m * ((w / 4) * (2 / w)) ^ (m + 1) := by rw [← mul_pow]
    _ = 2 ^ (m + 1) * ((w / 4) * (2 / w)) ^ (m + 1) := by rw [← pow_succ']
    _ = (2 * ((w / 4) * (2 / w))) ^ (m + 1) := by rw [← mul_pow]
    _ = (2 * (1 / 2)) ^ (m + 1) := by rw [h24]
    _ = 1 := by
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num]
      simp

private lemma cheb_scale_lc {w : ℝ} (hw : w ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (2 * (w / 4) ^ n) * (2 ^ (n - 1)) * (2 / w) ^ n = 1 := by
  cases n with
  | zero => omega
  | succ m =>
      have h := cheb_scale_lc_m hw m
      simpa [Nat.add_sub_cancel] using h

lemma intervalL_natDegree : intervalL.natDegree = 1 := by
  have hbne : (2 / (bSerre - aSerre) : ℝ) ≠ 0 := div_ne_zero (by norm_num) h_ba_ne
  simp only [intervalL]
  rw [natDegree_C_mul hbne, natDegree_X_sub_C]

lemma intervalL_leadingCoeff : intervalL.leadingCoeff = 2 / (bSerre - aSerre) := by
  have hm : (X - C ((aSerre + bSerre) / 2)).Monic := monic_X_sub_C ((aSerre + bSerre) / 2)
  simp only [intervalL]
  exact Monic.leadingCoeff_C_mul hm (2 / (bSerre - aSerre))

lemma intervalL_natDegree_ne_zero : intervalL.natDegree ≠ 0 := by
  rw [intervalL_natDegree]
  norm_num

lemma chebT_natDegree (N : ℕ) (hN : 1 ≤ N) : (chebT N).natDegree = N := by
  have hcne : (2 * kappaC ^ N : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero N (ne_of_gt kappa_pos))
  have hPdeg : (Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree = N := by
    rw [Polynomial.Chebyshev.natDegree_T ℝ (N : ℤ)]
    exact Int.natAbs_natCast N
  have hLdeg : intervalL.natDegree = 1 := intervalL_natDegree
  have hcompdeg : ((Polynomial.Chebyshev.T ℝ (N : ℤ)).comp intervalL).natDegree = N := by
    simp [natDegree_comp, hPdeg, hLdeg]
  dsimp [chebT]
  rw [natDegree_C_mul hcne, hcompdeg]

lemma chebT_leadingCoeff (N : ℕ) (hN : 1 ≤ N) : (chebT N).leadingCoeff = 1 := by
  have hPdeg : (Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree = N := by
    rw [Polynomial.Chebyshev.natDegree_T ℝ (N : ℤ)]
    exact Int.natAbs_natCast N
  have hlcP : (Polynomial.Chebyshev.T ℝ (N : ℤ)).leadingCoeff = 2 ^ (N - 1) := by
    rw [Polynomial.Chebyshev.leadingCoeff_T ℝ (N : ℤ)]
    have hnat : ((N : ℤ)).natAbs = N := Int.natAbs_natCast N
    have hexp : ((N : ℤ)).natAbs - 1 = N - 1 := by rw [hnat]
    rw [hexp]
  have hLdegne : intervalL.natDegree ≠ 0 := intervalL_natDegree_ne_zero
  have hlcL : intervalL.leadingCoeff = 2 / (bSerre - aSerre) := intervalL_leadingCoeff
  have hscale := cheb_scale_lc (w := bSerre - aSerre) h_ba_ne hN
  dsimp [chebT]
  rw [leadingCoeff_mul]
  simp only [leadingCoeff_C]
  rw [leadingCoeff_comp hLdegne]
  rw [hlcP, hlcL, hPdeg]
  rw [← mul_assoc]
  rw [show kappaC = (bSerre - aSerre) / 4 by rfl]
  exact hscale

lemma chebT_monic (N : ℕ) (hN : 1 ≤ N) : (chebT N).Monic := by
  rw [Monic]
  exact chebT_leadingCoeff N hN

-- Piece B: angles and points

/-- angle of k-th Chebyshev node of degree N: kπ/N -/
noncomputable def extAngle (N k : ℕ) : ℝ := (k : ℝ) * Real.pi / (N : ℝ)

/-- angle of k-th root of degree N: (2k+1)π/(2N) -/
noncomputable def rootAngle (N k : ℕ) : ℝ := (((2 * k + 1 : ℕ) : ℝ) * Real.pi) / (2 * (N : ℝ))

/-- k-th extremal point of the Serre Chebyshev polynomial: chebPoint(cos(kπ/N)) -/
noncomputable def extPoint (N k : ℕ) : ℝ := chebPoint (Real.cos (extAngle N k))

/-- k-th root point: chebPoint(cos((2k+1)π/2N)) -/
noncomputable def rootPoint (N k : ℕ) : ℝ := chebPoint (Real.cos (rootAngle N k))

private lemma extAngle_nonneg (N k : ℕ) (hN : 1 ≤ N) : 0 ≤ extAngle N k := by
  unfold extAngle
  exact div_nonneg (mul_nonneg (by positivity) (le_of_lt Real.pi_pos))
    (le_of_lt (by positivity : 0 < (N : ℝ)))

private lemma extAngle_le_pi {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) : extAngle N k ≤ Real.pi := by
  unfold extAngle
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  have hmul : (k : ℝ) * Real.pi ≤ (N : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_right hk' (le_of_lt Real.pi_pos)
  rw [div_le_iff₀ hNpos]
  simpa [mul_comm] using hmul

private lemma extAngle_strictMono {N k l : ℕ} (hN : 1 ≤ N) (hkl : k < l) :
    extAngle N k < extAngle N l := by
  unfold extAngle
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hk' : (k : ℝ) < (l : ℝ) := by exact_mod_cast hkl
  have hmul : (k : ℝ) * Real.pi < (l : ℝ) * Real.pi :=
    mul_lt_mul_of_pos_right hk' Real.pi_pos
  exact (div_lt_div_iff₀ hNpos hNpos).mpr (mul_lt_mul_of_pos_right hmul hNpos)

private lemma rootAngle_pos {N k : ℕ} (hN : 1 ≤ N) (_hk : k < N) : 0 < rootAngle N k := by
  unfold rootAngle
  positivity

private lemma rootAngle_lt_pi {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) : rootAngle N k < Real.pi := by
  unfold rootAngle
  have hden : 0 < 2 * (N : ℝ) := by positivity
  have hnum : ((2 * k + 1 : ℕ) : ℝ) < (2 : ℝ) * (N : ℝ) := by
    have hk' : (2 * k + 1 : ℕ) < 2 * N := by omega
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact_mod_cast hk'
  have hmul : ((2 * k + 1 : ℕ) : ℝ) * Real.pi < (2 : ℝ) * (N : ℝ) * Real.pi := by
    calc
      ((2 * k + 1 : ℕ) : ℝ) * Real.pi < ((2 : ℝ) * (N : ℝ)) * Real.pi :=
        mul_lt_mul_of_pos_right hnum Real.pi_pos
      _ = (2 : ℝ) * (N : ℝ) * Real.pi := by ring
  have h' : ((2 * k + 1 : ℕ) : ℝ) * Real.pi < Real.pi * ((2 : ℝ) * (N : ℝ)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  exact (div_lt_iff₀ hden).mpr h'

private lemma cos_lt_cos_angles {u v : ℝ} (hu0 : 0 ≤ u) (hvπ : v ≤ Real.pi) (huv : u < v) :
    Real.cos v < Real.cos u :=
  Real.cos_lt_cos_of_nonneg_of_le_pi hu0 hvπ huv

-- chebPoint is strictly increasing
private lemma chebPoint_strictMono {u v : ℝ} (huv : u < v) : chebPoint u < chebPoint v := by
  unfold chebPoint
  have hhalf : 0 < (bSerre - aSerre) / 2 := div_pos h_ba_pos (by norm_num)
  nlinarith

private lemma chebPoint_neg_one : chebPoint (-1) = aSerre := by
  unfold chebPoint
  ring

private lemma chebPoint_one : chebPoint 1 = bSerre := by
  unfold chebPoint
  ring

lemma extPoint_zero (N : ℕ) : extPoint N 0 = bSerre := by
  unfold extPoint extAngle
  simp [chebPoint_one]

private lemma extPoint_self (N : ℕ) (hN : 1 ≤ N) : extPoint N N = aSerre := by
  unfold extPoint extAngle
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp [hNc]
  simp [chebPoint_neg_one]

lemma extPoint_antitone {N i j : ℕ} (hN : 1 ≤ N) (hj : j ≤ N) (hij : i < j) :
    extPoint N j < extPoint N i := by
  unfold extPoint
  apply chebPoint_strictMono
  exact cos_lt_cos_angles (extAngle_nonneg N i hN) (extAngle_le_pi hN hj)
    (extAngle_strictMono hN hij)


/-- the cos-value of root k lies in the open unit interval -/
private lemma cos_rootAngle_mem_Ioo {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) :
    Real.cos (rootAngle N k) ∈ Set.Ioo (-1) 1 := by
  constructor
  · have hc : Real.cos Real.pi < Real.cos (rootAngle N k) :=
      cos_lt_cos_angles (le_of_lt (rootAngle_pos hN hk)) (le_refl Real.pi) (rootAngle_lt_pi hN hk)
    rwa [Real.cos_pi] at hc
  · have hc : Real.cos (rootAngle N k) < Real.cos 0 :=
      cos_lt_cos_angles (le_refl 0) (le_of_lt (rootAngle_lt_pi hN hk)) (rootAngle_pos hN hk)
    rwa [Real.cos_zero] at hc

/-- chebPoint maps the open unit interval into (aSerre,bSerre) -/
private lemma chebPoint_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (-1) 1) : chebPoint t ∈ Set.Ioo aSerre bSerre := by
  constructor
  · calc aSerre = chebPoint (-1) := chebPoint_neg_one.symm
      _ < chebPoint t := chebPoint_strictMono ht.1
  · calc chebPoint t < chebPoint 1 := chebPoint_strictMono ht.2
      _ = bSerre := chebPoint_one

lemma rootPoint_mem_Ioo {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) :
    rootPoint N k ∈ Set.Ioo aSerre bSerre := by
  unfold rootPoint
  exact chebPoint_mem_Ioo (cos_rootAngle_mem_Ioo hN hk)

-- root angle strictly increasing
private lemma rootAngle_strictMono {N k l : ℕ} (hN : 1 ≤ N) (hkl : k < l) :
    rootAngle N k < rootAngle N l := by
  unfold rootAngle
  have hden : 0 < 2 * (N : ℝ) := by positivity
  have hnum : ((2 * k + 1 : ℕ) : ℝ) < ((2 * l + 1 : ℕ) : ℝ) := by
    have hk' : 2 * k + 1 < 2 * l + 1 := by omega
    exact_mod_cast hk'
  have hmul : ((2 * k + 1 : ℕ) : ℝ) * Real.pi < ((2 * l + 1 : ℕ) : ℝ) * Real.pi :=
    mul_lt_mul_of_pos_right hnum Real.pi_pos
  exact (div_lt_div_iff₀ hden hden).mpr (mul_lt_mul_of_pos_right hmul hden)

lemma rootPoint_antitone {N k l : ℕ} (hN : 1 ≤ N) (hl : l < N) (hkl : k < l) :
    rootPoint N l < rootPoint N k := by
  unfold rootPoint
  apply chebPoint_strictMono
  exact cos_lt_cos_angles (le_of_lt (rootAngle_pos hN (lt_trans hkl hl))) (le_of_lt (rootAngle_lt_pi hN hl))
    (rootAngle_strictMono hN hkl)

/-- extrema angle (2k-form) matches root angle numerator relation: kπ/N = (2k)π/2N -/
private lemma extAngle_twoN {N k : ℕ} (hN : 1 ≤ N) : extAngle N k = (((2 * k : ℕ) : ℝ) * Real.pi) / (2 * (N : ℝ)) := by
  unfold extAngle
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have htwoNc : (2 : ℝ) * (N : ℝ) ≠ 0 := by positivity
  field_simp [hNc, htwoNc]
  norm_num [Nat.cast_mul]
  ring

/-- root angle is strictly between the k-th and (k+1)-th extrema angles -/
lemma extAngle_lt_rootAngle {N k : ℕ} (hN : 1 ≤ N) (_hk : k < N) : extAngle N k < rootAngle N k := by
  rw [extAngle_twoN hN]
  unfold rootAngle
  have hden : 0 < 2 * (N : ℝ) := by positivity
  have hnum : ((2 * k : ℕ) : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
    have hk' : 2 * k < 2 * k + 1 := by omega
    exact_mod_cast hk'
  have hmul : ((2 * k : ℕ) : ℝ) * Real.pi < ((2 * k + 1 : ℕ) : ℝ) * Real.pi :=
    mul_lt_mul_of_pos_right hnum Real.pi_pos
  exact (div_lt_div_iff₀ hden hden).mpr (mul_lt_mul_of_pos_right hmul hden)

private lemma rootAngle_lt_extAngle_succ {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) :
    rootAngle N k < extAngle N (k + 1) := by
  have h_twoN : extAngle N (k + 1) = (((2 * (k + 1) : ℕ) : ℝ) * Real.pi) / (2 * (N : ℝ)) := extAngle_twoN hN
  rw [h_twoN]
  unfold rootAngle
  have hden : 0 < 2 * (N : ℝ) := by positivity
  have hnum : ((2 * k + 1 : ℕ) : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by
    have hk' : 2 * k + 1 < 2 * (k + 1) := by omega
    exact_mod_cast hk'
  have hmul : ((2 * k + 1 : ℕ) : ℝ) * Real.pi < ((2 * (k + 1) : ℕ) : ℝ) * Real.pi :=
    mul_lt_mul_of_pos_right hnum Real.pi_pos
  exact (div_lt_div_iff₀ hden hden).mpr (mul_lt_mul_of_pos_right hmul hden)

/-- root point k lies strictly between extrema k+1 and k -/
lemma extPoint_rootPoint_interleave {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) :
    extPoint N (k + 1) < rootPoint N k ∧ rootPoint N k < extPoint N k := by
  constructor
  · unfold extPoint rootPoint
    apply chebPoint_strictMono
    exact cos_lt_cos_angles
      (le_of_lt (rootAngle_pos hN hk))
      (extAngle_le_pi hN (by omega : k + 1 ≤ N))
      (rootAngle_lt_extAngle_succ hN hk)
  · unfold extPoint rootPoint
    apply chebPoint_strictMono
    exact cos_lt_cos_angles
      (extAngle_nonneg N k hN)
      (le_of_lt (rootAngle_lt_pi hN hk))
      (extAngle_lt_rootAngle hN hk)

-- Piece C: evaluations

private lemma kappa_ne_zero : kappaC ≠ 0 := ne_of_gt kappa_pos

/-- eval of chebT N at extPoint = alternating values 2κ^N (−1)^k -/
lemma chebT_eval_extPoint (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    (chebT N).eval (extPoint N k) = 2 * kappaC ^ N * ((-1 : ℝ) ^ k) := by
  unfold extPoint chebPoint
  rw [chebT_eval_cos]
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have harg : (N : ℝ) * extAngle N k = (k : ℝ) * Real.pi := by
    unfold extAngle
    field_simp [hNc]
  rw [harg]
  rw [Real.cos_nat_mul_pi]

private lemma cos_odd_pi_half (k : ℕ) : Real.cos ((((2 * k + 1 : ℕ) : ℝ) * Real.pi) / 2) = 0 := by
  have h : (((2 * k + 1 : ℕ) : ℝ) * Real.pi) / 2 = (k : ℝ) * Real.pi + Real.pi / 2 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [h, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  norm_num

/-- eval of chebT N at rootPoint k is zero -/
lemma chebT_eval_rootPoint (N k : ℕ) (hN : 1 ≤ N) (_hk : k < N) :
    (chebT N).eval (rootPoint N k) = 0 := by
  unfold rootPoint chebPoint
  rw [chebT_eval_cos]
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have harg : (N : ℝ) * rootAngle N k = (((2 * k + 1 : ℕ) : ℝ) * Real.pi) / 2 := by
    unfold rootAngle
    field_simp [hNc]
  rw [harg, cos_odd_pi_half]
  ring

-- bound on [aSerre,bSerre]
private lemma intervalL_eval_mem_Icc {y : ℝ} (hy : y ∈ Set.Icc aSerre bSerre) :
    intervalL.eval y ∈ Set.Icc (-1) 1 := by
  have hbma : 0 < bSerre - aSerre := h_ba_pos
  rw [intervalL_eval]
  constructor
  · have hnum : (-1 : ℝ) * (bSerre - aSerre) ≤ 2 * y - (aSerre + bSerre) := by nlinarith [hy.1]
    exact (le_div_iff₀ hbma).2 hnum
  · have hnum : 2 * y - (aSerre + bSerre) ≤ (1 : ℝ) * (bSerre - aSerre) := by nlinarith [hy.2]
    exact (div_le_iff₀ hbma).2 hnum

lemma chebT_bound (N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : y ∈ Set.Icc aSerre bSerre) :
    |(chebT N).eval y| ≤ 2 * kappaC ^ N := by
  have htab : |intervalL.eval y| ≤ 1 := by
    exact abs_le.mpr (intervalL_eval_mem_Icc hy)
  have hPb : |(Polynomial.Chebyshev.T ℝ (N : ℤ)).eval (intervalL.eval y)| ≤ 1 := by
    exact Polynomial.Chebyshev.abs_eval_T_real_le_one (N : ℤ) htab
  have hcnonneg : 0 ≤ 2 * kappaC ^ N :=
    mul_nonneg (by norm_num) (pow_nonneg (le_of_lt kappa_pos) N)
  dsimp [chebT]
  calc
    |(C (2 * kappaC ^ N) * ((Polynomial.Chebyshev.T ℝ (N : ℤ)).comp intervalL)).eval y|
        = (2 * kappaC ^ N) * |(Polynomial.Chebyshev.T ℝ (N : ℤ)).eval (intervalL.eval y)| := by
            simp [eval_comp, abs_mul, abs_of_nonneg hcnonneg]
    _ ≤ (2 * kappaC ^ N) * 1 := by
        exact mul_le_mul_of_nonneg_left hPb hcnonneg
    _ = 2 * kappaC ^ N := by ring


-- Piece D: complex-root classification
private lemma r_injective (N : ℕ) (hN : 1 ≤ N) :
    Function.Injective (fun k : Fin N => rootPoint N k.val) := by
  intro k l h
  have hroot : rootPoint N k.val = rootPoint N l.val := by simpa using h
  by_contra hne
  have hvne : k.val ≠ l.val := fun hv => hne (Fin.ext hv)
  rcases lt_or_gt_of_ne hvne with hkl | hlk
  · have hlt : rootPoint N l.val < rootPoint N k.val := rootPoint_antitone hN l.isLt hkl
    exact (ne_of_lt hlt hroot.symm)
  · have hlt : rootPoint N k.val < rootPoint N l.val := rootPoint_antitone hN k.isLt hlk
    exact (ne_of_lt hlt hroot)

private lemma root_classify_monic {K : Type*} [Field K] {P : K[X]} {n : ℕ}
    (hP : P.Monic) (hdeg : P.natDegree = n) {S : Finset K}
    (hS : S.card = n) (hroot : ∀ x ∈ S, P.eval x = 0) :
    ∀ z : K, P.eval z = 0 → z ∈ S := by
  intro z hz
  have hPn0 : P ≠ 0 := hP.ne_zero
  have hroots : P.roots = S.val :=
    roots_eq_of_natDegree_le_card_of_ne_zero hroot (by rw [hS, hdeg]) hPn0
  have hzmem : z ∈ P.roots := (mem_roots hPn0).mpr (by simpa [Polynomial.IsRoot] using hz)
  exact Finset.mem_val.mp (by simpa [hroots] using hzmem)

-- Piece E: theorem assembly (practice copy)


private lemma chebT_root_eval_map (N : ℕ) (hN : 1 ≤ N) (k : Fin N) :
    (((chebT N).map (algebraMap ℝ ℂ)).eval ((rootPoint N k.val : ℂ))) = 0 := by
  have ht : (chebT N).eval (rootPoint N k.val) = 0 := chebT_eval_rootPoint N k.val hN k.isLt
  rw [Polynomial.eval_map]
  -- goal: eval₂ (algebraMap ℝ ℂ) ↑(rootPoint N k.val) (chebT N) = 0
  rw [← Polynomial.aeval_def]
  have hmap : ((rootPoint N k.val : ℂ) : ℂ) = algebraMap ℝ ℂ (rootPoint N k.val) := by simp
  rw [hmap]
  have h := aeval_algebraMap_apply_eq_algebraMap_eval (R := ℝ) (A := ℂ)
    (x := rootPoint N k.val) (p := chebT N)
  -- h : aeval (algebraMap ℝ ℂ (rootPoint N k.val)) (chebT N) = algebraMap ℝ ℂ (eval (rootPoint N k.val) (chebT N))
  rw [h, ht]
  norm_num


/-- Full alternation data for the monic Chebyshev polynomial of the Serre interval
(extremal points `x`, roots `r`, sup-norm and complex-root classification). -/
theorem cheb_alternation (N : ℕ) (hN : 1 ≤ N) :
    let T := chebT N
    T.Monic ∧ T.natDegree = N ∧
    ∃ x : Fin (N + 1) → ℝ, ∃ r : Fin N → ℝ,
      (x 0 = bSerre) ∧ (x ⟨N, Nat.lt_succ_self N⟩ = aSerre) ∧
      (∀ i : Fin (N + 1), ∀ j : Fin (N + 1), i.val < j.val → x j < x i) ∧
      (∀ i : Fin (N + 1),
        T.eval (x i) = 2 * kappaC ^ N * ((-1 : ℝ) ^ i.val)) ∧
      (∀ k : Fin N, r k ∈ Set.Ioo aSerre bSerre) ∧
      (∀ k : Fin N, ∀ l : Fin N, k.val < l.val → r l < r k) ∧
      (∀ k : Fin N, T.eval (r k) = 0) ∧
      (∀ z : ℂ, Polynomial.aeval z T = 0 → ∃ k : Fin N, z = (r k : ℂ)) ∧
      (∀ y : ℝ, y ∈ Set.Icc aSerre bSerre → |T.eval y| ≤ 2 * kappaC ^ N) ∧
      (∀ k : Fin N, let i : Fin (N + 1) := ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
        x ⟨k.val + 1, by omega⟩ < r k ∧ r k < x i) := by
  change (chebT N).Monic ∧ (chebT N).natDegree = N ∧
    ∃ x : Fin (N + 1) → ℝ, ∃ r : Fin N → ℝ,
      (x 0 = bSerre) ∧ (x ⟨N, Nat.lt_succ_self N⟩ = aSerre) ∧
      (∀ i : Fin (N + 1), ∀ j : Fin (N + 1), i.val < j.val → x j < x i) ∧
      (∀ i : Fin (N + 1),
        (chebT N).eval (x i) = 2 * kappaC ^ N * ((-1 : ℝ) ^ i.val)) ∧
      (∀ k : Fin N, r k ∈ Set.Ioo aSerre bSerre) ∧
      (∀ k : Fin N, ∀ l : Fin N, k.val < l.val → r l < r k) ∧
      (∀ k : Fin N, (chebT N).eval (r k) = 0) ∧
      (∀ z : ℂ, Polynomial.aeval z (chebT N) = 0 → ∃ k : Fin N, z = (r k : ℂ)) ∧
      (∀ y : ℝ, y ∈ Set.Icc aSerre bSerre → |(chebT N).eval y| ≤ 2 * kappaC ^ N) ∧
      (∀ k : Fin N, let i : Fin (N + 1) := ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
        x ⟨k.val + 1, by omega⟩ < r k ∧ r k < x i)
  refine ⟨chebT_monic N hN, chebT_natDegree N hN, ?_⟩
  let x : Fin (N + 1) → ℝ := fun i => extPoint N i.val
  let r : Fin N → ℝ := fun k => rootPoint N k.val
  refine ⟨x, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [x] using (extPoint_zero (N := N))
  · simpa [x] using (extPoint_self N hN)
  · intro i j hij
    change extPoint N j.val < extPoint N i.val
    exact extPoint_antitone hN (by omega) hij
  · intro i
    change (chebT N).eval (extPoint N i.val) = 2 * kappaC ^ N * ((-1 : ℝ) ^ i.val)
    exact chebT_eval_extPoint N i.val hN (by omega)
  · intro k
    change rootPoint N k.val ∈ Set.Ioo aSerre bSerre
    exact rootPoint_mem_Ioo hN k.isLt
  · intro k l hkl
    change rootPoint N l.val < rootPoint N k.val
    exact rootPoint_antitone hN l.isLt hkl
  · intro k
    change (chebT N).eval (rootPoint N k.val) = 0
    exact chebT_eval_rootPoint N k.val hN k.isLt
  · -- complex roots
    let P : Polynomial ℂ := (chebT N).map (algebraMap ℝ ℂ)
    let S : Finset ℂ := Finset.univ.image (fun k : Fin N => (rootPoint N k.val : ℂ))
    have hPmonic : P.Monic := by
      dsimp [P]
      exact (chebT_monic N hN).map (algebraMap ℝ ℂ)
    have hPdeg : P.natDegree = N := by
      dsimp [P]
      rw [Polynomial.natDegree_map]
      exact chebT_natDegree N hN
    have hS : S.card = N := by
      dsimp [S]
      rw [Finset.card_image_of_injOn]
      · simp
      · intro a _ b _ h
        have hreal : rootPoint N a.val = rootPoint N b.val := Complex.ofReal_inj.mp h
        exact r_injective N hN hreal
    have hmroot (k : Fin N) : P.eval ((rootPoint N k.val : ℂ)) = 0 := by
      exact chebT_root_eval_map N hN k
    have hroot : ∀ x ∈ S, P.eval x = 0 := by
      intro z hzS
      rcases Finset.mem_image.mp hzS with ⟨k, _hk, hz⟩
      rw [← hz]
      exact hmroot k
    intro z hz
    have hzP : P.eval z = 0 := by
      dsimp [P]
      rw [Polynomial.eval_map]
      simpa [Polynomial.aeval_def] using hz
    have hzmem := root_classify_monic hPmonic hPdeg hS hroot z hzP
    rcases Finset.mem_image.mp hzmem with ⟨k, _hk, hz⟩
    exact ⟨k, by simpa [r] using hz.symm⟩
  · intro y hy
    exact chebT_bound N hN hy
  · intro k
    change extPoint N (k.val + 1) < rootPoint N k.val ∧ rootPoint N k.val < extPoint N k.val
    exact extPoint_rootPoint_interleave hN k.isLt

end Submission.ChebSerre
