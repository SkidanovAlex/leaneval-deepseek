import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

set_option maxHeartbeats 2000000

/-! ## The canonical representative `[0,1)` of a point of the circle -/

/-- The representative in `[0,1)` of a point of the circle `ℝ/ℤ`. -/
noncomputable def circleRep (y : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 y).val

theorem coe_circleRep (y : AddCircle (1 : ℝ)) :
    ((circleRep y : ℝ) : AddCircle (1 : ℝ)) = y := by
  simpa [circleRep] using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := y))

theorem circleRep_nonneg (y : AddCircle (1 : ℝ)) : 0 ≤ circleRep y := by
  simpa [circleRep] using (AddCircle.equivIco (1 : ℝ) 0 y).prop.1

theorem circleRep_lt_one (y : AddCircle (1 : ℝ)) : circleRep y < 1 := by
  simpa [circleRep] using (AddCircle.equivIco (1 : ℝ) 0 y).prop.2

/-! ## Periodisation of a function supported in a short interval -/

/-- **The periodisation collapses to at most the two shifts `k = -1, 0`.**  If `φ` vanishes on
`|ξ| ≥ R` with `R ≤ 1`, then for the canonical representative `x ∈ [0,1)` of `y` only the shifts
`x` and `x - 1` can contribute. -/
theorem periodize_eq_pair {φ : ℝ → ℂ} {R : ℝ} (hR : R ≤ 1)
    (hφ : ∀ ξ : ℝ, R ≤ |ξ| → φ ξ = 0) (y : AddCircle (1 : ℝ)) :
    periodize φ y = φ (circleRep y) + φ (circleRep y - 1) := by
  rw [periodize]
  change (∑' k : ℤ, φ (circleRep y + (k : ℝ))) = φ (circleRep y) + φ (circleRep y - 1)
  have hzero : ∀ k : ℤ, k ∉ ({-1, 0} : Finset ℤ) → φ (circleRep y + (k : ℝ)) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    refine hφ _ ?_
    rcases (show (1 : ℤ) ≤ k ∨ k ≤ -2 by omega) with h1 | h2
    · have h1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
      rw [abs_of_nonneg (by linarith [circleRep_nonneg y, h1'] : (0 : ℝ) ≤ circleRep y + (k : ℝ))]
      linarith [circleRep_nonneg y, h1', hR]
    · have h2' : (k : ℝ) ≤ -2 := by exact_mod_cast h2
      rw [abs_of_nonpos (by linarith [circleRep_lt_one y, h2'] : circleRep y + (k : ℝ) ≤ 0)]
      linarith [circleRep_lt_one y, h2', hR]
  rw [tsum_eq_sum (s := ({-1, 0} : Finset ℤ)) hzero,
      Finset.sum_pair (by norm_num : (-1 : ℤ) ≠ 0)]
  rw [show circleRep y + ((-1 : ℤ) : ℝ) = circleRep y - 1 by push_cast; ring,
      show circleRep y + ((0 : ℤ) : ℝ) = circleRep y by push_cast; ring]
  exact add_comm _ _

/-- The pointwise consequence of `periodize_eq_pair`. -/
theorem norm_periodize_le_two_mul {φ : ℝ → ℂ} {R C : ℝ} (hR : R ≤ 1)
    (hφ : ∀ ξ : ℝ, R ≤ |ξ| → φ ξ = 0) (hC : ∀ ξ : ℝ, ‖φ ξ‖ ≤ C)
    (y : AddCircle (1 : ℝ)) : ‖periodize φ y‖ ≤ 2 * C := by
  rw [periodize_eq_pair hR hφ y]
  calc ‖φ (circleRep y) + φ (circleRep y - 1)‖
      ≤ ‖φ (circleRep y)‖ + ‖φ (circleRep y - 1)‖ := norm_add_le _ _
    _ ≤ C + C := add_le_add (hC _) (hC _)
    _ = 2 * C := by ring

/-- The norm of a point of the circle whose representative lies in `[0, 1/2]`. -/
theorem norm_circle_eq_val {y : AddCircle (1 : ℝ)} (hx : circleRep y ≤ 1 / 2) :
    ‖y‖ = circleRep y := by
  have h0 : (0 : ℝ) ≤ circleRep y := circleRep_nonneg y
  have hle : |circleRep y| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_of_nonneg h0, abs_one]
    linarith
  have hnorm : ‖((circleRep y : ℝ) : AddCircle (1 : ℝ))‖ = |circleRep y| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero (x := circleRep y)).mpr hle
  rw [coe_circleRep y] at hnorm
  rw [hnorm, abs_of_nonneg h0]

/-- The norm of a point of the circle whose representative lies in `[1/2, 1)`. -/
theorem norm_circle_eq_one_sub_val {y : AddCircle (1 : ℝ)} (hx : 1 / 2 ≤ circleRep y) :
    ‖y‖ = 1 - circleRep y := by
  have h0 : (0 : ℝ) ≤ circleRep y := circleRep_nonneg y
  have h1 : circleRep y < 1 := circleRep_lt_one y
  have hle : |circleRep y - 1| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_of_nonpos (by linarith : circleRep y - 1 ≤ 0), abs_one]
    linarith
  have hcoe : ((circleRep y - 1 : ℝ) : AddCircle (1 : ℝ)) = y := by
    rw [AddCircle.coe_sub, coe_circleRep y, AddCircle.coe_period, sub_zero]
  have hnorm : ‖((circleRep y - 1 : ℝ) : AddCircle (1 : ℝ))‖ = |circleRep y - 1| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero (x := circleRep y - 1)).mpr hle
  rw [hcoe] at hnorm
  rw [hnorm, abs_of_nonpos (by linarith : circleRep y - 1 ≤ 0)]
  ring

/-- **Only one shift contributes when `R ≤ 1/4`**, and the surviving term is at distance `‖y‖`
from the origin. -/
theorem periodize_single {φ : ℝ → ℂ} {R : ℝ} (hR : R ≤ 1 / 4)
    (hφ : ∀ ξ : ℝ, R ≤ |ξ| → φ ξ = 0) (y : AddCircle (1 : ℝ)) :
    ∃ ξ : ℝ, periodize φ y = φ ξ ∧ ‖y‖ = |ξ| := by
  have hR1 : R ≤ 1 := by linarith
  rcases lt_or_ge (circleRep y) (1 / 2) with hx | hx
  · refine ⟨circleRep y, ?_, ?_⟩
    · rw [periodize_eq_pair hR1 hφ y]
      have hzero : φ (circleRep y - 1) = 0 := by
        refine hφ _ ?_
        rw [abs_of_nonpos (by linarith [circleRep_lt_one y] : circleRep y - 1 ≤ 0)]
        linarith [circleRep_nonneg y]
      rw [hzero, add_zero]
    · rw [norm_circle_eq_val (le_of_lt hx), abs_of_nonneg (circleRep_nonneg y)]
  · refine ⟨circleRep y - 1, ?_, ?_⟩
    · rw [periodize_eq_pair hR1 hφ y]
      have hzero : φ (circleRep y) = 0 := by
        refine hφ _ ?_
        rw [abs_of_nonneg (circleRep_nonneg y)]
        linarith
      rw [hzero, zero_add]
    · rw [norm_circle_eq_one_sub_val hx]
      rw [abs_of_nonpos (by linarith [circleRep_lt_one y] : circleRep y - 1 ≤ 0)]
      ring

/-! ## Bounds for the modified bump `φ̃_{N,t,j}` -/

/-- If the cutoff `η` does not vanish at `2^a ξ`, then `|ξ| < 2^{-a}`. -/
private lemma eta_lt_of_ne_zero {a ξ : ℝ} (h : Work.KMTContract.kmtEta ((2 : ℝ) ^ a * ξ) ≠ 0) :
    |ξ| < (2 : ℝ) ^ (-a) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlt : |(2 : ℝ) ^ a * ξ| < 1 := by
    by_contra hc
    exact h (Work.KMTContract.kmtEta_zero (le_of_not_gt hc))
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2 _)] at hlt
  have hA : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos h2 _
  have hstep := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hA)
  rw [inv_mul_cancel_left₀ hA.ne', mul_one] at hstep
  calc |ξ| < ((2 : ℝ) ^ a)⁻¹ := hstep
    _ = (2 : ℝ) ^ (-a) := (Real.rpow_neg (le_of_lt h2) a).symm

/-- **The support of `φ̃_N`.**  A nonzero value forces `|ξ| < 2^{d(k - Log N)}`. -/
private lemma varphitildeN_ne_zero_abs_lt (d N k : ℕ) {ξ : ℝ}
    (h : Work.KMTAreas.A7.varphitildeN d N k ξ ≠ 0) :
    |ξ| < (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  by_cases hk : k = 0
  · subst hk
    rw [Work.KMTAreas.A7.varphitildeN, if_pos rfl] at h
    have h1 := eta_lt_of_ne_zero h
    have hexp : -((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) =
        (d : ℝ) * (((0 : ℕ) : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by push_cast; ring
    rwa [hexp] at h1
  · rw [Work.KMTAreas.A7.varphitildeN, if_neg hk] at h
    have hor : Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ) ≠ 0 ∨
        Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) ≠ 0 := by
      by_contra hc
      simp only [not_or, not_ne_iff] at hc
      exact h (by rw [hc.1, hc.2, sub_zero])
    rcases hor with h1 | h1
    · have h2 := eta_lt_of_ne_zero h1
      have hexp : -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) =
          (d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by ring
      rwa [hexp] at h2
    · have h2 := eta_lt_of_ne_zero h1
      refine lt_of_lt_of_le h2 ?_
      rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
      nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- The support of the modified bump `φ̃_{N,t,j}`: a nonzero value forces
`|ξ| < 2^{d(k - Log N)}`. -/
theorem varphitildeNtj_support_lt (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t ξ : ℝ)
    (h : varphitildeNtj P N k j t ξ ≠ 0) :
    |ξ| < (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  have hNt : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ ≠ 0 := by
    intro h0
    exact h (by rw [varphitildeNtj, h0, mul_zero])
  have hN : Work.KMTAreas.A7.varphitildeN P.natDegree N k ξ ≠ 0 := (mul_ne_zero_iff.mp hNt).1
  exact varphitildeN_ne_zero_abs_lt P.natDegree N k hN

/-- If `u, v ∈ [0,1]` then `‖η u - η v‖ ≤ 1`. -/
private lemma norm_kmtEta_sub_le_one (x y : ℝ) :
    ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖ ≤ 1 := by
  have hx : Work.KMTContract.kmtEta x = ((Work.KMTContract.kmtBump x : ℝ) : ℂ) := rfl
  have hy : Work.KMTContract.kmtEta y = ((Work.KMTContract.kmtBump y : ℝ) : ℂ) := rfl
  rw [hx, hy, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  refine ⟨?_, ?_⟩
  · have h1 := Work.KMTContract.kmtEta_le_one y
    have h2 := Work.KMTContract.kmtEta_nonneg x
    linarith
  · have h1 := Work.KMTContract.kmtEta_le_one x
    have h2 := Work.KMTContract.kmtEta_nonneg y
    linarith

/-- `‖φ̃_N‖ ≤ 1`. -/
private lemma norm_varphitildeN_le_one (d N k : ℕ) (ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeN d N k ξ‖ ≤ 1 := by
  rw [Work.KMTAreas.A7.varphitildeN]
  by_cases hk : k = 0
  · rw [if_pos hk]
    exact Work.KMTContract.norm_kmtEta_le _
  · rw [if_neg hk]
    exact norm_kmtEta_sub_le_one _ _

/-- `‖e(x)‖ = 1`. -/
private lemma norm_ee_one (x : ℝ) : ‖Work.KMTAreas.A7.ee x‖ = 1 := by
  have hrepr : Work.KMTAreas.A7.ee x = Complex.exp (((2 * Real.pi * x : ℝ)) * Complex.I) := by
    rw [Work.KMTAreas.A7.ee]
    congr 1
    push_cast
    ring
  rw [hrepr, Complex.norm_exp_ofReal_mul_I]

/-- `‖φ̃_{N,t}‖ ≤ 1`. -/
private lemma norm_varphitildeNt_le_one (P : Polynomial ℤ) (N k : ℕ) (t ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖ ≤ 1 := by
  rw [Work.KMTAreas.A7.varphitildeNt, norm_mul, norm_ee_one, mul_one]
  exact norm_varphitildeN_le_one P.natDegree N k ξ

/-- **The arithmetic `N^d · 2^{-d·Log N} < 2^d`.** -/
private lemma natPow_mul_two_rpow_neg_lt (d N : ℕ) (hd : 1 ≤ d) :
    (N : ℝ) ^ d * (2 : ℝ) ^ (-((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) < (2 : ℝ) ^ d := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  set L : ℤ := Work.Analysis.EndVar.logN N with hL
  set A : ℝ := (2 : ℝ) ^ L with hA
  have hApos : 0 < A := zpow_pos (by norm_num : (0 : ℝ) < 2) L
  have hAr : A = (2 : ℝ) ^ ((L : ℝ)) := by rw [hA, Real.rpow_intCast]
  have hLR : (Work.Analysis.EndVar.logN N : ℝ) = (L : ℝ) := by rw [hL]
  have hNA : (N : ℝ) < 2 * A := by
    have h3 : N < 2 ^ ((Nat.log 2 (max N 2)) + 1) := by
      have h4 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) (max N 2)
      rw [Nat.succ_eq_add_one] at h4
      exact lt_of_le_of_lt (le_max_left N 2) h4
    have h5 : (N : ℝ) < (2 : ℝ) ^ ((Nat.log 2 (max N 2)) + 1) := by exact_mod_cast h3
    have h6 : (L : ℝ) + 1 = ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ) := by
      have h7 : L = ((Nat.log 2 (max N 2) : ℤ)) := by rw [hL]; rfl
      rw [h7]; push_cast; ring
    have h8 : (N : ℝ) < (2 : ℝ) ^ ((L : ℝ) + 1) := by
      rw [h6, Real.rpow_natCast]
      exact h5
    rw [Real.rpow_add h2, Real.rpow_one, ← hAr] at h8
    linarith
  have hR : (2 : ℝ) ^ (-((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) = (A ^ d)⁻¹ := by
    rw [hLR, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (d : ℝ) * (L : ℝ) = (L : ℝ) * (d : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← hAr, Real.rpow_natCast]
  calc (N : ℝ) ^ d * (2 : ℝ) ^ (-((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
      = (N : ℝ) ^ d * (A ^ d)⁻¹ := by rw [hR]
    _ < (2 : ℝ) ^ d := by
        rw [← div_eq_mul_inv, div_lt_iff₀ (pow_pos hApos d), ← mul_pow]
        exact pow_lt_pow_left₀ (n := d) hNA (Nat.cast_nonneg N) (by omega)

/-- `|2^{-dk} N^d ξ| < 2^d` on the support of the bump. -/
private lemma scale_mul_abs_lt (d N k : ℕ) (hd : 1 ≤ d) {ξ : ℝ}
    (h : |ξ| < (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) :
    |(2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * ((N : ℝ) ^ d) * ξ| < (2 : ℝ) ^ d := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rcases eq_or_ne N 0 with hN0 | hN0
  · subst hN0
    have hz : (((0 : ℕ) : ℝ)) ^ d = 0 := by
      rw [Nat.cast_zero, zero_pow (by omega : d ≠ 0)]
    rw [hz, mul_zero, zero_mul, abs_zero]
    positivity
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
    set L : ℤ := Work.Analysis.EndVar.logN N with hL
    set A : ℝ := (2 : ℝ) ^ L with hA
    have hApos : 0 < A := zpow_pos (by norm_num : (0 : ℝ) < 2) L
    have hAr : A = (2 : ℝ) ^ ((L : ℝ)) := by rw [hA, Real.rpow_intCast]
    have hLR : (Work.Analysis.EndVar.logN N : ℝ) = (L : ℝ) := by rw [hL]
    have hNA : (N : ℝ) < 2 * A := by
      have h3 : N < 2 ^ ((Nat.log 2 (max N 2)) + 1) := by
        have h4 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) (max N 2)
        rw [Nat.succ_eq_add_one] at h4
        exact lt_of_le_of_lt (le_max_left N 2) h4
      have h5 : (N : ℝ) < (2 : ℝ) ^ ((Nat.log 2 (max N 2)) + 1) := by exact_mod_cast h3
      have h6 : (L : ℝ) + 1 = ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ) := by
        have h7 : L = ((Nat.log 2 (max N 2) : ℤ)) := by rw [hL]; rfl
        rw [h7]; push_cast; ring
      have h8 : (N : ℝ) < (2 : ℝ) ^ ((L : ℝ) + 1) := by
        rw [h6, Real.rpow_natCast]
        exact h5
      rw [Real.rpow_add h2, Real.rpow_one, ← hAr] at h8
      linarith
    have hR : (2 : ℝ) ^ (-((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) = (A ^ d)⁻¹ := by
      rw [hLR, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [show (d : ℝ) * (L : ℝ) = (L : ℝ) * (d : ℝ) by ring,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← hAr, Real.rpow_natCast]
    have hlt : |ξ| < (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (L : ℝ))) := by rwa [hLR] at h
    have h1 : |(2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * ((N : ℝ) ^ d) * ξ|
        < (2 : ℝ) ^ (-((d : ℝ) * (L : ℝ))) * (N : ℝ) ^ d := by
      have hpos : 0 < (2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * (N : ℝ) ^ d :=
        mul_pos (Real.rpow_pos_of_pos h2 _) (pow_pos hNpos d)
      have hfac : |(2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * ((N : ℝ) ^ d) * ξ|
          = ((2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * (N : ℝ) ^ d) * |ξ| := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2 _),
            abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) d)]
      rw [hfac]
      calc ((2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * (N : ℝ) ^ d) * |ξ|
          < ((2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * (N : ℝ) ^ d)
              * (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (L : ℝ))) := mul_lt_mul_of_pos_left hlt hpos
        _ = (2 : ℝ) ^ (-((d : ℝ) * (L : ℝ))) * (N : ℝ) ^ d := by
            rw [mul_assoc, mul_comm ((N : ℝ) ^ d) ((2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (L : ℝ)))),
                ← mul_assoc, ← Real.rpow_add h2,
                show -((d : ℝ) * (k : ℝ)) + (d : ℝ) * ((k : ℝ) - (L : ℝ))
                  = -((d : ℝ) * (L : ℝ)) by ring]
    calc |(2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * ((N : ℝ) ^ d) * ξ|
        < (2 : ℝ) ^ (-((d : ℝ) * (L : ℝ))) * (N : ℝ) ^ d := h1
      _ = (A ^ d)⁻¹ * (N : ℝ) ^ d := by rw [hR]
      _ < (2 : ℝ) ^ d := by
          rw [mul_comm (A ^ d)⁻¹, ← div_eq_mul_inv, div_lt_iff₀ (pow_pos hApos d), ← mul_pow]
          exact pow_lt_pow_left₀ (n := d) hNA (Nat.cast_nonneg N) (by omega)

/-- **Vanishing of `φ̃_N` on the closed ball of radius `2^{-(d(Log N - k) + d + 1)}`** for
`k ≠ 0`. -/
private lemma varphitildeN_eq_zero_of_abs_le (d N k : ℕ) (hk : k ≠ 0) {ξ : ℝ}
    (h : |ξ| ≤ (2 : ℝ) ^ (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
      + ((d : ℝ) + 1)))) : Work.KMTAreas.A7.varphitildeN d N k ξ = 0 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Work.KMTAreas.A7.varphitildeN, if_neg hk]
  have hA : (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |ξ| ≤ 1 / 2 := by
    have he : (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
        * (2 : ℝ) ^ (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + ((d : ℝ) + 1)))
        = (2 : ℝ) ^ (-((d : ℝ) + 1)) := by
      rw [← Real.rpow_add h2]
      congr 1
      ring
    calc (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |ξ|
        ≤ (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
          * (2 : ℝ) ^ (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
              + ((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos h2 _).le
      _ = (2 : ℝ) ^ (-((d : ℝ) + 1)) := he
      _ ≤ 1 / 2 := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; norm_num]
          exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
            (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hB : (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * |ξ| ≤ 1 / 2 := by
    have he : (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))
        * (2 : ℝ) ^ (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + ((d : ℝ) + 1)))
        = 1 / 2 := by
      rw [← Real.rpow_add h2]
      rw [show (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
          + (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + ((d : ℝ) + 1))) = -1
          by ring]
      rw [Real.rpow_neg_one]
      norm_num
    calc (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * |ξ|
        ≤ (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))
          * (2 : ℝ) ^ (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
              + ((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos h2 _).le
      _ = 1 / 2 := he
  have hA1 : Work.KMTContract.kmtEta
      ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ) = 1 := by
    refine Work.KMTContract.kmtEta_one ?_
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2 _)]
    exact hA
  have hB1 : Work.KMTContract.kmtEta
      ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) = 1 := by
    refine Work.KMTContract.kmtEta_one ?_
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2 _)]
    exact hB
  rw [hA1, hB1, sub_self]

/-- The vanishing near the origin, for the modified bump. -/
theorem varphitildeNtj_eq_zero_of_abs_le (P : Polynomial ℤ) (N k : ℕ) (hk : k ≠ 0) (j : ℤ)
    (t : ℝ) {ξ : ℝ}
    (h : |ξ| ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
      + ((P.natDegree : ℝ) + 1)))) : varphitildeNtj P N k j t ξ = 0 := by
  have hNt : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ = 0 := by
    rw [Work.KMTAreas.A7.varphitildeNt, varphitildeN_eq_zero_of_abs_le P.natDegree N k hk h,
      zero_mul]
  rw [varphitildeNtj, hNt, mul_zero]

/-- **The pointwise bound `‖φ̃_{N,t,j}(ξ)‖ ≤ 2^d`** for `j ∈ {0,1}`. -/
theorem varphitildeNtj_norm_le (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (hj : j = 0 ∨ j = 1)
    (hd : 1 ≤ P.natDegree) (t ξ : ℝ) : ‖varphitildeNtj P N k j t ξ‖ ≤ (2 : ℝ) ^ P.natDegree := by
  rcases hj with rfl | rfl
  · rw [varphitildeNtj]
    simp only [zpow_zero, one_mul]
    refine le_trans (norm_varphitildeNt_le_one P N k t ξ) ?_
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  · rw [varphitildeNtj]
    simp only [zpow_one]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hz : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ = 0
    · rw [hz, norm_zero, mul_zero]
      positivity
    · have hw : ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖ ≤ 1 :=
        norm_varphitildeNt_le_one P N k t ξ
      have hN : Work.KMTAreas.A7.varphitildeN P.natDegree N k ξ ≠ 0 := (mul_ne_zero_iff.mp hz).1
      have hs : |ξ| < (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
        varphitildeN_ne_zero_abs_lt P.natDegree N k hN
      calc |(2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ) ^ P.natDegree) * ξ|
            * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖
          ≤ |(2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ) ^ P.natDegree) * ξ| * 1 :=
            mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ = |(2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ) ^ P.natDegree) * ξ| :=
            mul_one _
        _ ≤ (2 : ℝ) ^ P.natDegree :=
            le_of_lt (scale_mul_abs_lt P.natDegree N k hd hs)

/-- The bottom-scale decay of the modified bump: `‖φ̃_{N,t,1}‖ ≤ N^d |ξ|` for `k = 0`. -/
theorem varphitildeNtj_zero_scale_le (P : Polynomial ℤ) (N : ℕ) (t ξ : ℝ) :
    ‖varphitildeNtj P N 0 1 t ξ‖ ≤ (N : ℝ) ^ P.natDegree * |ξ| := by
  rw [varphitildeNtj]
  simp only [zpow_one]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc : (2 : ℝ) ^ (-((P.natDegree : ℝ) * ((0 : ℕ) : ℝ))) = 1 := by
    rw [show -((P.natDegree : ℝ) * ((0 : ℕ) : ℝ)) = 0 by push_cast; ring, Real.rpow_zero]
  rw [hc, one_mul, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) P.natDegree)]
  have h1 : ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t ξ‖ ≤ 1 :=
    norm_varphitildeNt_le_one P N 0 t ξ
  calc (N : ℝ) ^ P.natDegree * |ξ| * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N 0 t ξ‖
      ≤ (N : ℝ) ^ P.natDegree * |ξ| * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (N : ℝ) ^ P.natDegree * |ξ| := by ring

/-! ## The main statement -/

theorem periodizeVarphitildeNtjBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (N k₂ : ℕ) (j₂ : ℤ)
    (hj₂ : j₂ ∈ ({0, 1} : Finset ℤ)) (t : ℝ) (hk : k₂ ≠ 0 ∨ j₂ = 1)
    (hlog : (k₂ : ℤ) ≤ Work.Analysis.EndVar.logN N) :
    (∀ y : Work.Analysis.IonescuWainger.Circle,
        ‖Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) y‖
          ≤ (2 : ℝ) ^ (P.natDegree + 1)) ∧
    (k₂ = 0 → ∀ y : Work.Analysis.IonescuWainger.Circle,
        ‖Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) y‖
          ≤ (N : ℝ) ^ P.natDegree * ‖y‖) ∧
    (k₂ = 0 → ∀ y : Work.Analysis.IonescuWainger.Circle,
        Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) y ≠ 0 →
          (N : ℝ) ^ P.natDegree * ‖y‖ < (2 : ℝ) ^ P.natDegree) ∧
    (k₂ ≠ 0 → (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN N →
      ∀ y : Work.Analysis.IonescuWainger.Circle,
        Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) y ≠ 0 →
          (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N - (k₂ : ℤ) : ℤ) : ℝ))
              * ‖y‖ ∈ Set.Ioo ((2 : ℝ) ^ ((-(P.natDegree + 1) : ℤ) : ℝ)) 1) := by
  have hj₂' : j₂ = 0 ∨ j₂ = 1 := by simpa using hj₂
  set d : ℕ := P.natDegree with hddef
  have hd2 : 2 ≤ d := hd
  have hdc : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdpos : 1 ≤ d := by omega
  set L : ℤ := Work.Analysis.EndVar.logN N with hLdef
  have hL1 : 1 ≤ L := by
    have h2max : 2 ≤ max N 2 := le_max_right _ _
    have hp : 2 ^ 1 ≤ max N 2 := by simpa using h2max
    have hlog2 := Nat.le_log_of_pow_le (b := 2) (by norm_num : 1 < 2) hp
    have hLval : L = ((Nat.log 2 (max N 2) : ℤ)) := by rw [hLdef]; rfl
    rw [hLval]
    exact_mod_cast hlog2
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by
    have h0 : (0 : ℤ) ≤ L := le_trans (by norm_num : (0 : ℤ) ≤ 1) hL1
    exact_mod_cast h0
  by_cases hk₂ : k₂ = 0
  · have hj1 : j₂ = 1 := hk.resolve_left (by simp [hk₂])
    subst hk₂
    subst hj1
    set R : ℝ := (2 : ℝ) ^ ((d : ℝ) * (((0 : ℕ) : ℝ) - (L : ℝ))) with hRdef
    have hsp : ∀ ξ : ℝ, varphitildeNtj P N 0 1 t ξ ≠ 0 → |ξ| < R := by
      intro ξ hξ
      have h1 := varphitildeNtj_support_lt P N 0 1 t ξ hξ
      rwa [hRdef]
    have hvan : ∀ ξ : ℝ, R ≤ |ξ| → varphitildeNtj P N 0 1 t ξ = 0 := by
      intro ξ hξ
      by_contra hne
      exact absurd (hsp ξ hne) (not_lt.mpr hξ)
    have hbd : ∀ ξ : ℝ, ‖varphitildeNtj P N 0 1 t ξ‖ ≤ (2 : ℝ) ^ d := fun ξ =>
      varphitildeNtj_norm_le P N 0 1 (Or.inr rfl) hdpos t ξ
    have hR1 : R ≤ 1 := by
      rw [hRdef, show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
      refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
      rw [Nat.cast_zero]
      nlinarith [hdc, hLnn]
    have hR4 : R ≤ 1 / 4 := by
      have h14 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = -(((2 : ℕ)) : ℝ) by norm_num,
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        norm_num
      rw [hRdef, h14]
      refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
      rw [Nat.cast_zero]
      have hd2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
      have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
      nlinarith
    have hcore : (N : ℝ) ^ d * R < (2 : ℝ) ^ d := by
      have hReq : R = (2 : ℝ) ^ (-((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) := by
        rw [hRdef]
        congr 1
        have hthis : (L : ℝ) = (Work.Analysis.EndVar.logN N : ℝ) := by rw [hLdef]
        rw [hthis, Nat.cast_zero]
        ring
      rw [hReq]
      exact natPow_mul_two_rpow_neg_lt d N hdpos
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      have h1 := norm_periodize_le_two_mul hR1 hvan hbd y
      calc ‖periodize (varphitildeNtj P N 0 1 t) y‖ ≤ 2 * (2 : ℝ) ^ d := h1
        _ = (2 : ℝ) ^ (d + 1) := by rw [pow_succ]; ring
    · intro _ y
      obtain ⟨ξ, hξ, hnorm⟩ := periodize_single hR4 hvan y
      rw [hξ, hnorm]
      exact varphitildeNtj_zero_scale_le P N t ξ
    · intro _ y hy
      obtain ⟨ξ, hξ, hnorm⟩ := periodize_single hR4 hvan y
      have hne : varphitildeNtj P N 0 1 t ξ ≠ 0 := by
        intro h0
        exact hy (by rw [hξ, h0])
      have hlt : |ξ| < R := hsp ξ hne
      rw [hnorm]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlt.le (pow_nonneg (Nat.cast_nonneg N) d))
        hcore
    · intro hcon
      exact absurd rfl hcon
  · set R : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - (L : ℝ))) with hRdef
    have hsp : ∀ ξ : ℝ, varphitildeNtj P N k₂ j₂ t ξ ≠ 0 → |ξ| < R := by
      intro ξ hξ
      have h1 := varphitildeNtj_support_lt P N k₂ j₂ t ξ hξ
      rwa [hRdef]
    have hvan : ∀ ξ : ℝ, R ≤ |ξ| → varphitildeNtj P N k₂ j₂ t ξ = 0 := by
      intro ξ hξ
      by_contra hne
      exact absurd (hsp ξ hne) (not_lt.mpr hξ)
    have hbd : ∀ ξ : ℝ, ‖varphitildeNtj P N k₂ j₂ t ξ‖ ≤ (2 : ℝ) ^ d := fun ξ =>
      varphitildeNtj_norm_le P N k₂ j₂ hj₂' hdpos t ξ
    have hkL : (k₂ : ℤ) ≤ L := hlog
    have hR1 : R ≤ 1 := by
      rw [hRdef, show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
      refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
      have hkL' : (k₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hkL
      nlinarith [hdc, hkL']
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      have h1 := norm_periodize_le_two_mul hR1 hvan hbd y
      calc ‖periodize (varphitildeNtj P N k₂ j₂ t) y‖ ≤ 2 * (2 : ℝ) ^ d := h1
        _ = (2 : ℝ) ^ (d + 1) := by rw [pow_succ]; ring
    · intro h0
      exact absurd h0 hk₂
    · intro h0
      exact absurd h0 hk₂
    · intro hk₂' hkL4 y hy
      have hR4 : R ≤ 1 / 4 := by
        have h14 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
          rw [show (-2 : ℝ) = -(((2 : ℕ)) : ℝ) by norm_num,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          norm_num
        rw [hRdef, h14]
        refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
        have hd2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
        have h4 : (k₂ : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hkL4
        nlinarith
      obtain ⟨ξ, hξ, hnorm⟩ := periodize_single hR4 hvan y
      have hne : varphitildeNtj P N k₂ j₂ t ξ ≠ 0 := by
        intro h0
        exact hy (by rw [hξ, h0])
      have hlt : |ξ| < R := hsp ξ hne
      have hgt : (2 : ℝ) ^ (-((d : ℝ) * ((L : ℝ) - (k₂ : ℝ)) + ((d : ℝ) + 1))) < |ξ| := by
        by_contra hle
        exact hne (varphitildeNtj_eq_zero_of_abs_le P N k₂ hk₂ j₂ t (le_of_not_gt hle))
      have hcast : (((L - (k₂ : ℤ) : ℤ)) : ℝ) = (L : ℝ) - (k₂ : ℝ) := by push_cast; ring
      rw [hcast, hnorm, Set.mem_Ioo]
      refine ⟨?_, ?_⟩
      · have hdelta : (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k₂ : ℝ)))
            * (2 : ℝ) ^ (-((d : ℝ) * ((L : ℝ) - (k₂ : ℝ)) + ((d : ℝ) + 1)))
            = (2 : ℝ) ^ (-((d : ℝ) + 1)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        have hcast2 : (2 : ℝ) ^ (((-(d + 1) : ℤ)) : ℝ) = (2 : ℝ) ^ (-((d : ℝ) + 1)) := by
          rw [Real.rpow_intCast, zpow_neg,
              show ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
          rw [show (-((d : ℝ) + 1)) = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        rw [hcast2]
        calc (2 : ℝ) ^ (-((d : ℝ) + 1))
            = (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k₂ : ℝ)))
              * (2 : ℝ) ^ (-((d : ℝ) * ((L : ℝ) - (k₂ : ℝ)) + ((d : ℝ) + 1))) := hdelta.symm
          _ < (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k₂ : ℝ))) * |ξ| :=
              mul_lt_mul_of_pos_left hgt (Real.rpow_pos_of_pos (by norm_num) _)
      · have hSR : (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k₂ : ℝ))) * R = 1 := by
          rw [hRdef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          rw [show (d : ℝ) * ((L : ℝ) - (k₂ : ℝ)) + (d : ℝ) * ((k₂ : ℝ) - (L : ℝ)) = 0 by ring,
              Real.rpow_zero]
        calc (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k₂ : ℝ))) * |ξ|
            < (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k₂ : ℝ))) * R :=
              mul_lt_mul_of_pos_left hlt (Real.rpow_pos_of_pos (by norm_num) _)
          _ = 1 := hSR

end Work.KMTPlan.A6
