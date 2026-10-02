import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Submission.Commons.Analysis.Asymptotics.geom_finset_le
import Submission.Commons.Analysis.Asymptotics.sum_range_mul_geom_le

open scoped BigOperators
noncomputable section

namespace Commons.NumberTheory.Linnik

-- =====================================================================
-- Part A: dyadic shell index
-- =====================================================================

/-- dyadic shell index: floor of log base 2. -/
private def dIdx (x : ℝ) : ℕ := Nat.floor (Real.logb 2 x)

private lemma dIdx_pow_le {x : ℝ} (hx : 1 ≤ x) : (2 : ℝ) ^ dIdx x ≤ x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hx
  have hfl : ((dIdx x : ℕ) : ℝ) ≤ Real.logb 2 x := Nat.floor_le hlog
  calc
    (2 : ℝ) ^ dIdx x = (2 : ℝ) ^ ((dIdx x : ℕ) : ℝ) := by rw [← Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ Real.logb 2 x := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hfl
    _ = x := Real.rpow_logb (b := (2:ℝ)) (x := x) (by norm_num) (by norm_num) hx0

private lemma dIdx_lt_pow_succ {x : ℝ} (hx : 1 ≤ x) : x < (2 : ℝ) ^ (dIdx x + 1) := by
  have hx0 : 0 < x := by linarith
  have hlt : Real.logb 2 x < ((dIdx x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpow : (2 : ℝ) ^ Real.logb 2 x < (2 : ℝ) ^ (((dIdx x : ℕ) : ℝ) + 1) := by
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hlt
  have hid : (2 : ℝ) ^ Real.logb 2 x = x := Real.rpow_logb (b := (2:ℝ)) (x := x)
    (by norm_num) (by norm_num) hx0
  have hE : (2 : ℝ) ^ (((dIdx x : ℕ) : ℝ) + 1) = (2 : ℝ) ^ (dIdx x + 1) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [Real.rpow_natCast, pow_succ, Real.rpow_one]
  have hx' : x < (2 : ℝ) ^ (((dIdx x : ℕ) : ℝ) + 1) := by rw [hid] at hpow; exact hpow
  rw [hE] at hx'
  exact hx'

private lemma dIdx_le_of_lt_pow {x : ℝ} (hx : 1 ≤ x) {N : ℕ}
    (hxN : x < (2 : ℝ) ^ (N + 1)) : dIdx x ≤ N := by
  have hx0 : 0 < x := by linarith
  have hlt : Real.logb 2 x < (N : ℝ) + 1 := by
    have hlog : Real.logb 2 x < Real.logb 2 ((2 : ℝ) ^ (N + 1)) := by
      exact Real.logb_lt_logb (b := (2:ℝ)) (x := x) (y := (2 : ℝ) ^ (N + 1))
        (by norm_num : (1:ℝ) < 2) hx0 hxN
    have hred : Real.logb 2 ((2 : ℝ) ^ (N + 1)) = ((N + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.logb_rpow (b := (2:ℝ)) (x := ((N + 1 : ℕ) : ℝ)) (by norm_num) (by norm_num)
    rw [hred] at hlog
    simpa using hlog
  have hfl : (dIdx x : ℝ) < (N : ℝ) + 1 :=
    lt_of_le_of_lt (Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hx)) hlt
  have hcast : dIdx x < N + 1 := by exact_mod_cast hfl
  omega

private lemma dIdx_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : dIdx x ≤ dIdx y := by
  have hy : 1 ≤ y := le_trans hx hxy
  have hlogx : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hx
  have hlogxy : Real.logb 2 x ≤ Real.logb 2 y := by
    exact (Real.logb_le_logb (b := (2:ℝ)) (by norm_num : (1:ℝ) < 2)
      (by linarith : (0 : ℝ) < x) (by linarith : (0 : ℝ) < y)).2 hxy
  exact Nat.floor_mono hlogxy

private lemma two_pow_succ_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (2 : ℝ) ^ (dIdx x + 1) ≤ 2 * x := by
  have h1 := dIdx_pow_le hx
  calc (2 : ℝ) ^ (dIdx x + 1) = 2 * (2 : ℝ) ^ dIdx x := by rw [pow_succ]; ring
    _ ≤ 2 * x := mul_le_mul_of_nonneg_left h1 (by norm_num)

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have he : Real.exp (1 : ℝ) < Real.exp (Real.log (4 : ℝ)) := by
    rw [Real.exp_log h4pos]
    exact lt_trans Real.exp_one_lt_three (by norm_num)
  have h1 : (1 : ℝ) < Real.log (4 : ℝ) := (Real.exp_lt_exp.mp he)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.log_pow (2 : ℝ) 2]
    norm_num
  linarith

private lemma two_pow_add_two_eq (m : ℕ) :
    (2 : ℝ) ^ (m + 2) = 4 * ((1 / 2 : ℝ) ^ m) * (4 : ℝ) ^ m := by
  have hprod : (4 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = (2 : ℝ) ^ m := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : ℝ) ^ (m + 2) = (2 : ℝ) ^ m * 4 := by
      rw [pow_add]
      norm_num
    _ = ((4 : ℝ) ^ m * (1 / 2 : ℝ) ^ m) * 4 := by rw [← hprod]
    _ = 4 * ((1 / 2 : ℝ) ^ m) * (4 : ℝ) ^ m := by ring

private lemma two_pow_ge_one (k : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
  have hk : (0 : ℕ) ≤ k := Nat.zero_le k
  simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk : (2:ℝ)^0 ≤ (2:ℝ)^k)

private lemma dIdx_pow_succ_ge_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    x ≤ (2 : ℝ) ^ (dIdx x + 1) := by
  by_cases h1 : 1 ≤ x
  · exact le_of_lt (dIdx_lt_pow_succ h1)
  · have hx1 : x < 1 := lt_of_not_ge h1
    have hk : (1 : ℕ) ≤ dIdx x + 1 := by omega
    have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (dIdx x + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (dIdx x + 1) := by simpa using h
    linarith

private lemma pow_succ_two_add_one_le {k : ℕ} : (2 : ℝ) ^ (k + 1) + 1 ≤ (2 : ℝ) ^ (k + 2) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := two_pow_ge_one (k + 1)
  calc
    (2 : ℝ) ^ (k + 1) + 1 ≤ (2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 1) := add_le_add (le_refl _) h1
    _ = 2 * (2 : ℝ) ^ (k + 1) := by ring
    _ = (2 : ℝ) ^ (k + 2) := by rw [pow_succ]; ring

private lemma one_div_le_of_pow_le {x : ℝ} (hxpos : 0 < x) (k : ℕ)
    (h : (2 : ℝ) ^ k ≤ x) : (1 : ℝ) / x ≤ 1 / (2 : ℝ) ^ k := by
  exact one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) k) h

private lemma log_two_add_pow_le {R : ℝ} (hR : 0 < R) (k : ℕ) :
    Real.log (R + (2 : ℝ) ^ (k + 1) + 2) ≤ Real.log (R + 2) + ((k + 2 : ℕ) : ℝ) * Real.log 2 := by
  have hk2 : (2 : ℝ) ^ (k + 1) + 2 ≤ (2 : ℝ) ^ (k + 2) := by
    have h1 : 2 ≤ (2 : ℝ) ^ (k + 1) := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : (1 : ℕ) ≤ k + 1)
        : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (k + 1))
    calc
      (2 : ℝ) ^ (k + 1) + 2 ≤ (2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 1) := by linarith
      _ = 2 * (2 : ℝ) ^ (k + 1) := by ring
      _ = (2 : ℝ) ^ (k + 2) := by rw [pow_succ]; ring
  have hRle : R ≤ R * (2 : ℝ) ^ (k + 2) := by
    have h1' : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := two_pow_ge_one (k + 2)
    have := mul_le_mul_of_nonneg_left h1' (le_of_lt hR)
    simpa using this
  have hsumle : (2 : ℝ) ^ (k + 1) + 2 ≤ 2 * (2 : ℝ) ^ (k + 2) := by
    have h2p : 0 ≤ (2 : ℝ) ^ (k + 2) := by positivity
    nlinarith [hk2, h2p]
  have hle : R + (2 : ℝ) ^ (k + 1) + 2 ≤ (R + 2) * (2 : ℝ) ^ (k + 2) := by
    calc
      R + (2 : ℝ) ^ (k + 1) + 2 = R + ((2 : ℝ) ^ (k + 1) + 2) := by ring
      _ ≤ R * (2 : ℝ) ^ (k + 2) + 2 * (2 : ℝ) ^ (k + 2) := add_le_add hRle hsumle
      _ = (R + 2) * (2 : ℝ) ^ (k + 2) := by ring
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < R + (2 : ℝ) ^ (k + 1) + 2) hle
  have hmul := Real.log_mul (by nlinarith : (R + 2) ≠ 0)
    (pow_ne_zero (k + 2) (by norm_num : (2 : ℝ) ≠ 0))
  rw [hmul, Real.log_pow] at hlog
  nlinarith [hlog]

private lemma log_pow_add_two_le {k : ℕ} :
    Real.log ((2 : ℝ) ^ (k + 1) + 2) ≤ ((k + 2 : ℕ) : ℝ) * Real.log 2 := by
  have hle : (2 : ℝ) ^ (k + 1) + 2 ≤ (2 : ℝ) ^ (k + 2) := by
    have h1 : 2 ≤ (2 : ℝ) ^ (k + 1) := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : (1 : ℕ) ≤ k + 1)
        : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (k + 1))
    calc
      (2 : ℝ) ^ (k + 1) + 2 ≤ (2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 1) := by linarith
      _ = 2 * (2 : ℝ) ^ (k + 1) := by ring
      _ = (2 : ℝ) ^ (k + 2) := by rw [pow_succ]; ring
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + 1) + 2) hle
  rw [Real.log_pow] at hlog
  exact hlog

-- =====================================================================
-- Part B: generic shell-weighted sum over a finite set of indices
-- =====================================================================

private lemma sum_le_shell_sum {S : Finset ℂ} {M : ℂ → ℝ} (hM : ∀ u ∈ S, 0 ≤ M u)
    {P : ℂ → Prop} [DecidablePred P] {K : ℂ → ℕ} {I : Finset ℕ}
    (hK : ∀ u ∈ S, P u → K u ∈ I)
    {wt : ℂ → ℝ} {W : ℕ → ℝ} (hW : ∀ u ∈ S, P u → ∀ k ∈ I, K u = k → wt u ≤ W k)
    (hW0 : ∀ k ∈ I, 0 ≤ W k) :
    (∑ u ∈ S.filter P, M u * wt u) ≤
      ∑ k ∈ I, W k * (∑ u ∈ S.filter (fun u => K u = k), M u) := by
  classical
  calc
    (∑ u ∈ S.filter P, M u * wt u) = ∑ u ∈ S, (if P u then M u * wt u else 0) := by
      rw [Finset.sum_filter]
    _ ≤ ∑ u ∈ S, ∑ k ∈ I, (if (P u ∧ K u = k) then M u * W k else 0) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hp : P u
      · have hKu : K u ∈ I := hK u hu hp
        rw [if_pos hp]
        have hw' : wt u ≤ W (K u) := hW u hu hp (K u) hKu rfl
        have hMW : M u * wt u ≤ M u * W (K u) := mul_le_mul_of_nonneg_left hw' (hM u hu)
        have hsum : (∑ k ∈ I, (if (K u = k) then M u * W k else 0)) = M u * W (K u) := by
          rw [Finset.sum_eq_single (K u)]
          · simp
          · intro b hb hbne
            by_cases h : K u = b
            · exact False.elim (hbne h.symm)
            · simp [h]
          · intro hnot
            exact False.elim (hnot hKu)
        calc
          M u * wt u ≤ M u * W (K u) := hMW
          _ = ∑ k ∈ I, (if (K u = k) then M u * W k else 0) := hsum.symm
          _ = ∑ k ∈ I, (if (P u ∧ K u = k) then M u * W k else 0) := by
            apply Finset.sum_congr rfl
            intro k hk'
            by_cases hke : K u = k <;> simp [hp, hke]
      · rw [if_neg hp]
        have hnon : 0 ≤ ∑ k ∈ I, (if (P u ∧ K u = k) then M u * W k else 0) := by
          refine Finset.sum_nonneg ?_
          intro k hk'
          by_cases h : P u ∧ K u = k
          · have hW0k : 0 ≤ W k := hW0 k hk'
            have hm0 : 0 ≤ M u := hM u hu
            rw [if_pos h]
            exact mul_nonneg hm0 hW0k
          · simp [h]
        simpa [hp] using hnon
    _ = ∑ k ∈ I, ∑ u ∈ S, (if (P u ∧ K u = k) then M u * W k else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ I, ∑ u ∈ S.filter (fun u => P u ∧ K u = k), M u * W k := by
      apply Finset.sum_congr rfl
      intro k hk'
      rw [Finset.sum_filter]
    _ = ∑ k ∈ I, W k * (∑ u ∈ S.filter (fun u => P u ∧ K u = k), M u) := by
      apply Finset.sum_congr rfl
      intro k hk'
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ ∑ k ∈ I, W k * (∑ u ∈ S.filter (fun u => K u = k), M u) := by
      apply Finset.sum_le_sum
      intro k hk'
      have hsub : S.filter (fun u => P u ∧ K u = k) ⊆ S.filter (fun u => K u = k) := by
        intro u hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2.2⟩
      have hWk : 0 ≤ W k := hW0 k hk'
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro u hu hu'
        exact hM u (Finset.mem_filter.mp hu).1)) hWk

-- =====================================================================
-- Part C: low / mid / far regime bounds
-- =====================================================================

/-- low regime: points with `‖u‖ ≤ R/4`; weight `(4/3)/‖u‖`. -/
private theorem lowBound {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) {S : Finset ℂ} {m : ℂ → ℤ}
    (hu1 : ∀ u ∈ S, 1 ≤ ‖u‖) (hm : ∀ u ∈ S, 0 ≤ (m u : ℤ))
    (hN : ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ), (((m u : ℤ) : ℝ))) ≤
        C * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2))
    {R : ℝ} (hR : 2 ≤ R) :
    (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), (((m u : ℤ) : ℝ)) * (4 / 3 / ‖u‖)) ≤
      (64 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by
  classical
  let M : ℂ → ℝ := fun u => (((m u : ℤ) : ℝ))
  change (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) ≤
      (64 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1)
  set A : ℝ := Real.log (R + 2) + q + 2
  have hMm : ∀ u ∈ S, 0 ≤ M u := by
    intro u hu
    exact Int.cast_nonneg (hm u hu)
  have hlogR : 0 ≤ Real.log (R + 2) := by
    refine Real.log_nonneg ?_
    linarith
  have hApos : 0 ≤ A := by dsimp [A]; linarith
  have hAge : (1 : ℝ) ≤ A := by dsimp [A]; linarith
  have hlogA : Real.log (R + 2) ≤ A := by dsimp [A]; linarith
  let s1 : ℝ := max (R / 4) 1
  have hs1ge1 : 1 ≤ s1 := by dsimp [s1]; exact le_max_right _ _
  have hs1le : s1 ≤ R / 2 := by
    dsimp [s1]
    exact max_le (by linarith) (by linarith)
  have h2s1 : 2 * s1 ≤ R := by linarith
  let N1 : ℕ := dIdx s1
  have hcov : ∀ u ∈ S, ‖u‖ ≤ R / 4 → dIdx ‖u‖ ≤ N1 := by
    intro u hu hule
    have hx1 : 1 ≤ ‖u‖ := hu1 u hu
    have hus : ‖u‖ ≤ s1 := le_trans hule (by dsimp [s1]; exact le_max_left _ _)
    have hsp : ‖u‖ < (2 : ℝ) ^ (N1 + 1) := lt_of_le_of_lt hus (by
      dsimp [N1]
      exact dIdx_lt_pow_succ hs1ge1)
    exact dIdx_le_of_lt_pow hx1 hsp
  have h2N : (2 : ℝ) ^ (N1 + 1) ≤ R := by
    have h1 : (2 : ℝ) ^ (dIdx s1 + 1) ≤ 2 * s1 := two_pow_succ_le_two_mul hs1ge1
    calc
      (2 : ℝ) ^ (N1 + 1) ≤ 2 * s1 := by simpa [N1] using h1
      _ ≤ R := h2s1
  let I1 : Finset ℕ := Finset.range (N1 + 1)
  have hK1 : ∀ u ∈ S, ‖u‖ ≤ R / 4 → dIdx ‖u‖ ∈ I1 := by
    intro u hu hule
    have hle : dIdx ‖u‖ ≤ N1 := hcov u hu hule
    exact Finset.mem_range.mpr (by omega)
  have hW1 : ∀ u ∈ S, ‖u‖ ≤ R / 4 → ∀ k ∈ I1, dIdx ‖u‖ = k → (4 / 3 / ‖u‖) ≤ (4 / 3 / (2 : ℝ) ^ k) := by
    intro u hu _ k hk hke
    have h2k : (2 : ℝ) ^ k ≤ ‖u‖ := by
      have h0 := dIdx_pow_le (hu1 u hu)
      simpa [hke] using h0
    have hpos : (0 : ℝ) < ‖u‖ := by
      have := hu1 u hu
      linarith
    have hinv : (1 : ℝ) / ‖u‖ ≤ 1 / (2 : ℝ) ^ k := one_div_le_of_pow_le hpos k h2k
    have h43 : (0 : ℝ) ≤ 4 / 3 := by norm_num
    simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_left hinv h43)
  have hW01 : ∀ k ∈ I1, 0 ≤ 4 / 3 / (2 : ℝ) ^ k := by
    intro k hk
    positivity
  have hshell := sum_le_shell_sum (S := S) (M := M) hMm
    (P := fun u : ℂ => ‖u‖ ≤ R / 4) (K := fun u : ℂ => dIdx ‖u‖) (I := I1) hK1
    (wt := fun u : ℂ => 4 / 3 / ‖u‖) (W := fun k : ℕ => 4 / 3 / (2 : ℝ) ^ k) hW1 hW01
  have hmass : ∀ k ∈ I1,
      (∑ u ∈ S.filter (fun u => dIdx ‖u‖ = k), M u) ≤
        C * ((2 : ℝ) ^ (k + 1) + 1) * (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2) := by
    intro k hk
    have hρ : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := two_pow_ge_one (k + 1)
    have hNk := hN (0 : ℂ) ((2 : ℝ) ^ (k + 1)) hρ
    have hcb : (∑ u ∈ S.filter (fun u => ‖u‖ ≤ (2 : ℝ) ^ (k + 1)), M u) ≤
        C * ((2 : ℝ) ^ (k + 1) + 1) * (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2) := by
      simpa [M, zero_add] using hNk
    have hsub : S.filter (fun u => dIdx ‖u‖ = k) ⊆ S.filter (fun u => ‖u‖ ≤ (2 : ℝ) ^ (k + 1)) := by
      intro u hu
      have huS : u ∈ S := (Finset.mem_filter.mp hu).1
      have hke : dIdx ‖u‖ = k := (Finset.mem_filter.mp hu).2
      have hus : ‖u‖ < (2 : ℝ) ^ (dIdx ‖u‖ + 1) := dIdx_lt_pow_succ (hu1 u huS)
      rw [hke] at hus
      exact Finset.mem_filter.mpr ⟨huS, le_of_lt hus⟩
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro u hu hu'
      exact hMm u (Finset.mem_filter.mp hu).1)) hcb
  have hN1A : ((N1 : ℕ) : ℝ) + 1 ≤ 3 * A := by
    have hlogm : ((N1 + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (R + 2) := by
      have hlog1 : Real.log ((2 : ℝ) ^ (N1 + 1)) ≤ Real.log R := by
        exact Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) (N1 + 1)) h2N
      have hlp : Real.log ((2 : ℝ) ^ (N1 + 1)) = ((N1 + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow (2 : ℝ) (N1 + 1)]
      have hlog2 : Real.log R ≤ Real.log (R + 2) := by
        exact Real.log_le_log (by linarith : (0 : ℝ) < R) (by linarith)
      rw [hlp] at hlog1
      exact le_trans hlog1 hlog2
    have h1 : ((N1 + 1 : ℕ) : ℝ) * Real.log 2 ≤ A := le_trans hlogm hlogA
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [half_lt_log_two]
    have hdiv : ((N1 + 1 : ℕ) : ℝ) ≤ A / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      simpa [mul_comm] using h1
    have hinv : (1 / Real.log 2 : ℝ) ≤ 2 := by
      have h2le : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt half_lt_log_two
      calc
        (1 / Real.log 2 : ℝ) ≤ 1 / (1 / 2 : ℝ) := by
          exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) h2le
        _ = 2 := by norm_num
    have hA2 : A / Real.log 2 ≤ 2 * A := by
      calc
        A / Real.log 2 = A * (1 / Real.log 2) := by ring
        _ ≤ A * 2 := mul_le_mul_of_nonneg_left hinv hApos
        _ = 2 * A := by ring
    have hn : ((N1 + 1 : ℕ) : ℝ) = (N1 : ℝ) + 1 := by norm_cast
    have h2A : ((N1 + 1 : ℕ) : ℝ) ≤ 3 * A := by
      rw [hn]
      linarith only [hdiv, hA2, hApos, hn]
    simpa [hn] using h2A
  have hW0' : ∀ k ∈ I1, 0 ≤ 4 / 3 / (2 : ℝ) ^ k := hW01
  have hchain1 : (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) ≤
      ∑ k ∈ I1,
        (4 / 3 / (2 : ℝ) ^ k) * (∑ u ∈ S.filter (fun u => dIdx ‖u‖ = k), M u) := by
    exact hshell
  have hchain2 :
      (∑ k ∈ I1,
        (4 / 3 / (2 : ℝ) ^ k) * (∑ u ∈ S.filter (fun u => dIdx ‖u‖ = k), M u)) ≤
        ∑ k ∈ I1,
          (4 / 3 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
            (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hmass k hk) (hW0' k hk)
  have hterm : ∀ k ∈ I1,
      (4 / 3 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2)) ≤ (16 / 3) * C * A := by
    intro k hk
    have hk1 : k + 1 ≤ N1 + 1 := by
      have hlt : k < N1 + 1 := Finset.mem_range.mp hk
      omega
    have h2k1 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (N1 + 1) :=
      pow_le_pow_right₀ (by norm_num) hk1
    have h2R : (2 : ℝ) ^ (k + 1) ≤ R := le_trans h2k1 h2N
    have hlog2 : Real.log ((2 : ℝ) ^ (k + 1) + 2) ≤ Real.log (R + 2) := by
      refine Real.log_le_log ?_ ?_
      · positivity
      · linarith only [h2R]
    have hmain : Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2 ≤ A := by
      calc
        Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2 ≤ Real.log (R + 2) + q + 2 := by linarith only [hlog2]
        _ = A := by dsimp [A]
    have hfac1 : C * ((2 : ℝ) ^ (k + 1) + 1) * (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2)
        ≤ C * (2 : ℝ) ^ (k + 2) * A := by
      have hps : (2 : ℝ) ^ (k + 1) + 1 ≤ (2 : ℝ) ^ (k + 2) := pow_succ_two_add_one_le (k := k)
      have hposLog : (0 : ℝ) ≤ Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2 := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) + 2 := by linarith only [two_pow_ge_one (k + 1)]
        have hl : 0 ≤ Real.log ((2 : ℝ) ^ (k + 1) + 2) := Real.log_nonneg h1
        linarith only [hl, hq]
      have hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by positivity
      have hmul1 : ((2 : ℝ) ^ (k + 1) + 1) * (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2)
          ≤ (2 : ℝ) ^ (k + 2) * A := mul_le_mul hps hmain hposLog hpos2
      have hmul2 : C * (((2 : ℝ) ^ (k + 1) + 1) * (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2))
          ≤ C * ((2 : ℝ) ^ (k + 2) * A) := mul_le_mul_of_nonneg_left hmul1 hC
      calc
        C * ((2 : ℝ) ^ (k + 1) + 1) * (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2)
            = C * (((2 : ℝ) ^ (k + 1) + 1) * (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2)) := by ring
        _ ≤ C * ((2 : ℝ) ^ (k + 2) * A) := hmul2
        _ = C * (2 : ℝ) ^ (k + 2) * A := by ring
    have hcoef : (4 / 3 / (2 : ℝ) ^ k) * ((2 : ℝ) ^ (k + 2)) ≤ 16 / 3 := by
      have hk0 : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num : (0 : ℝ) < 2) k
      have hrat : (2 : ℝ) ^ (k + 2) / (2 : ℝ) ^ k = 4 := by
        field_simp [hk0.ne']
        rw [pow_succ, pow_succ]
        ring
      calc
        (4 / 3 / (2 : ℝ) ^ k) * (2 : ℝ) ^ (k + 2) = (4 / 3) * ((2 : ℝ) ^ (k + 2) / (2 : ℝ) ^ k) := by
          field_simp [hk0.ne']
        _ = (4 / 3) * 4 := by rw [hrat]
        _ = 16 / 3 := by norm_num
        _ ≤ 16 / 3 := by norm_num
    have hWk0 : (0 : ℝ) ≤ 4 / 3 / (2 : ℝ) ^ k := by positivity
    have hstep : (4 / 3 / (2 : ℝ) ^ k) * (C * (2 : ℝ) ^ (k + 2) * A) ≤ (16 / 3) * C * A := by
      calc
        (4 / 3 / (2 : ℝ) ^ k) * (C * (2 : ℝ) ^ (k + 2) * A)
            = C * A * ((4 / 3 / (2 : ℝ) ^ k) * (2 : ℝ) ^ (k + 2)) := by ring
        _ ≤ C * A * (16 / 3) := by
          exact mul_le_mul_of_nonneg_left hcoef (mul_nonneg hC hApos)
        _ = (16 / 3) * C * A := by ring
    calc
      (4 / 3 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2))
          ≤ (4 / 3 / (2 : ℝ) ^ k) * (C * (2 : ℝ) ^ (k + 2) * A) := by
              exact mul_le_mul_of_nonneg_left hfac1 hWk0
      _ ≤ (16 / 3) * C * A := hstep
  have hsum : (∑ k ∈ I1,
        (4 / 3 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
            (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2))) ≤
          ((N1 + 1 : ℕ) : ℝ) * ((16 / 3) * C * A) := by
    calc
      (∑ k ∈ I1,
          (4 / 3 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
            (Real.log ((2 : ℝ) ^ (k + 1) + 2) + q + 2)))
          ≤ ∑ k ∈ I1, ((16 / 3) * C * A) := Finset.sum_le_sum hterm
      _ = ((N1 + 1 : ℕ) : ℝ) * ((16 / 3) * C * A) := by
        simp [I1, Finset.sum_const, nsmul_eq_mul]
  have hfinal1 :
      (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) ≤
        ((N1 + 1 : ℕ) : ℝ) * ((16 / 3) * C * A) :=
    le_trans (le_trans hchain1 hchain2) hsum
  have hfac : 0 ≤ (16 / 3) * C * A := by
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 3) hC) hApos
  have hN1A' : ((N1 + 1 : ℕ) : ℝ) ≤ 3 * A := by
    have hn : ((N1 + 1 : ℕ) : ℝ) = (N1 : ℝ) + 1 := by norm_cast
    rw [hn]
    exact hN1A
  have hfinal2 : ((N1 + 1 : ℕ) : ℝ) * ((16 / 3) * C * A) ≤ (16 : ℝ) * C * A ^ 2 := by
    calc
      ((N1 + 1 : ℕ) : ℝ) * ((16 / 3) * C * A) ≤ (3 * A) * ((16 / 3) * C * A) := by
        exact mul_le_mul_of_nonneg_right hN1A' hfac
      _ = (16 : ℝ) * C * A ^ 2 := by ring
  have hfinal3 : (16 : ℝ) * C * A ^ 2 ≤ (64 : ℝ) * C * (A ^ 2 + 1) := by
    linarith only [mul_nonneg hC (sq_nonneg A), hC]
  calc
    (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) ≤
        ((N1 + 1 : ℕ) : ℝ) * ((16 / 3) * C * A) := hfinal1
    _ ≤ (16 : ℝ) * C * A ^ 2 := hfinal2
    _ ≤ (64 : ℝ) * C * (A ^ 2 + 1) := hfinal3
    _ = (64 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by rfl

/-- log `10 ≤ 9` and `11 ≤ 10` (crude). -/
private lemma log_ten_le_nine : Real.log (10 : ℝ) ≤ 9 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
  norm_num at h ⊢
  exact h

private lemma log_eleven_le_ten : Real.log (11 : ℝ) ≤ 10 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
  norm_num at h ⊢
  exact h

/-- mid regime: points with `‖u‖ ≤ 4R` at distance `> 1` from `w`; weight `4/‖w-u‖`. -/
private theorem midBound {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) {S : Finset ℂ} {m : ℂ → ℤ}
    (hu1 : ∀ u ∈ S, 1 ≤ ‖u‖) (hm : ∀ u ∈ S, 0 ≤ (m u : ℤ))
    (hN : ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ), (((m u : ℤ) : ℝ))) ≤
        C * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2))
    {R : ℝ} (hR : 2 ≤ R) {w : ℂ} (hw : ‖w‖ = R) :
    (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖),
        (((m u : ℤ) : ℝ)) * (4 / ‖w - u‖)) ≤
      (8192 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by
  classical
  let M : ℂ → ℝ := fun u => (((m u : ℤ) : ℝ))
  change (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) ≤
      (8192 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1)
  set A : ℝ := Real.log (R + 2) + q + 2
  have hMm : ∀ u ∈ S, 0 ≤ M u := by
    intro u hu
    exact Int.cast_nonneg (hm u hu)
  have hlogR : 0 ≤ Real.log (R + 2) := by
    refine Real.log_nonneg ?_
    linarith
  have hApos : 0 ≤ A := by dsimp [A]; linarith
  have hA2 : (2 : ℝ) ≤ A := by dsimp [A]; linarith
  have hlogA : Real.log (R + 2) ≤ A := by dsimp [A]; linarith
  let s2 : ℝ := 5 * R
  have hs2ge1 : 1 ≤ s2 := by dsimp [s2]; linarith only [hR]
  let J : ℕ := dIdx s2
  have h2J : (2 : ℝ) ^ (J + 1) ≤ 10 * R := by
    have h1 : (2 : ℝ) ^ (dIdx s2 + 1) ≤ 2 * s2 := two_pow_succ_le_two_mul hs2ge1
    calc
      (2 : ℝ) ^ (J + 1) ≤ 2 * s2 := by simpa [J, s2] using h1
      _ = 10 * R := by dsimp [s2]; ring
  let I2 : Finset ℕ := Finset.range (J + 1)
  -- covering: u ∈ P ⟹ dIdx ‖w-u‖ ≤ J
  have hcov2 : ∀ u ∈ S, (‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖) → dIdx ‖w - u‖ ≤ J := by
    intro u hu hp
    have hd1 : 1 ≤ ‖w - u‖ := le_of_lt hp.2
    have htri : ‖w - u‖ ≤ ‖w‖ + ‖u‖ := norm_sub_le w u
    have hd5 : ‖w - u‖ ≤ 5 * R := by
      have h1 : ‖w - u‖ ≤ R + ‖u‖ := by
        calc
          ‖w - u‖ ≤ ‖w‖ + ‖u‖ := htri
          _ = R + ‖u‖ := by rw [hw]
      linarith only [h1, hp.1]
    have hds : ‖w - u‖ ≤ s2 := by simpa [s2] using hd5
    have hsp : ‖w - u‖ < (2 : ℝ) ^ (J + 1) := lt_of_le_of_lt hds (by
      dsimp [J, s2]
      exact dIdx_lt_pow_succ hs2ge1)
    exact dIdx_le_of_lt_pow hd1 hsp
  have hK2 : ∀ u ∈ S, (‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖) → dIdx ‖w - u‖ ∈ I2 := by
    intro u hu hp
    have hle : dIdx ‖w - u‖ ≤ J := hcov2 u hu hp
    exact Finset.mem_range.mpr (by omega)
  have hW2 : ∀ u ∈ S, (‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖) →
      ∀ k ∈ I2, dIdx ‖w - u‖ = k → (4 / ‖w - u‖) ≤ (4 / (2 : ℝ) ^ k) := by
    intro u hu hp k hk hke
    have hd1 : 1 ≤ ‖w - u‖ := le_of_lt hp.2
    have h2k : (2 : ℝ) ^ k ≤ ‖w - u‖ := by
      have h0 := dIdx_pow_le hd1
      simpa [hke] using h0
    have hpos : (0 : ℝ) < ‖w - u‖ := by
      have := hp.2
      linarith
    have hinv : (1 : ℝ) / ‖w - u‖ ≤ 1 / (2 : ℝ) ^ k := one_div_le_of_pow_le hpos k h2k
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_left hinv h4)
  have hW02 : ∀ k ∈ I2, 0 ≤ 4 / (2 : ℝ) ^ k := by
    intro k hk
    positivity
  have hshell := sum_le_shell_sum (S := S) (M := M) hMm
    (P := (fun u : ℂ => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖))
    (K := fun u : ℂ => dIdx ‖w - u‖) (I := I2) hK2
    (wt := fun u : ℂ => 4 / ‖w - u‖) (W := fun k : ℕ => 4 / (2 : ℝ) ^ k) hW2 hW02
  -- mass over shell k
  have hmass2 : ∀ k ∈ I2,
      (∑ u ∈ S.filter (fun u => dIdx ‖w - u‖ = k), M u) ≤
        C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2) := by
    intro k hk
    have hρ : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := two_pow_ge_one (k + 1)
    have hNk := hN w ((2 : ℝ) ^ (k + 1)) hρ
    have hcb : (∑ u ∈ S.filter (fun u => ‖u - w‖ ≤ (2 : ℝ) ^ (k + 1)), M u) ≤
        C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2) := by
      simpa [M, hw, norm_sub_rev] using hNk
    have hsub : S.filter (fun u => dIdx ‖w - u‖ = k) ⊆
        S.filter (fun u => ‖u - w‖ ≤ (2 : ℝ) ^ (k + 1)) := by
      intro u hu
      have huS : u ∈ S := (Finset.mem_filter.mp hu).1
      have hke : dIdx ‖w - u‖ = k := (Finset.mem_filter.mp hu).2
      have hus : ‖w - u‖ ≤ (2 : ℝ) ^ (dIdx ‖w - u‖ + 1) :=
        dIdx_pow_succ_ge_of_nonneg (norm_nonneg (w - u))
      rw [hke] at hus
      exact Finset.mem_filter.mpr ⟨huS, by simpa [norm_sub_rev] using hus⟩
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro u hu hu'
      exact hMm u (Finset.mem_filter.mp hu).1)) hcb
  -- bound the number of shells: (J:ℝ)+1 ≤ 2*(A+9)
  have hJln : ((J + 1 : ℕ) : ℝ) * Real.log 2 ≤ A + Real.log (10 : ℝ) := by
    have hlog1 : Real.log ((2 : ℝ) ^ (J + 1)) ≤ Real.log (10 * R) := by
      exact Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) (J + 1)) h2J
    have hlp : Real.log ((2 : ℝ) ^ (J + 1)) = ((J + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Real.log_pow (2 : ℝ) (J + 1)]
    have h10 : Real.log (10 * R) = Real.log (10 : ℝ) + Real.log R := by
      exact Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) (by linarith : R ≠ 0)
    have hRle : Real.log R ≤ Real.log (R + 2) := by
      exact Real.log_le_log (by linarith : (0 : ℝ) < R) (by linarith)
    rw [hlp, h10] at hlog1
    calc
      ((J + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (10 : ℝ) + Real.log R := hlog1
      _ ≤ Real.log (10 : ℝ) + Real.log (R + 2) := by linarith only [hRle]
      _ ≤ Real.log (10 : ℝ) + A := by linarith only [hlogA]
      _ = A + Real.log (10 : ℝ) := by ring
  have hJp1 : ((J : ℕ) : ℝ) + 1 ≤ 2 * (A + 9) := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [half_lt_log_two]
    have hdiv : ((J + 1 : ℕ) : ℝ) ≤ (A + Real.log (10 : ℝ)) / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      simpa [mul_comm] using hJln
    have hA9 : 0 ≤ A + Real.log (10 : ℝ) := by
      have hl10 : 0 ≤ Real.log (10 : ℝ) := by
        refine Real.log_nonneg ?_
        norm_num
      linarith only [hl10, hApos]
    have hinv : (1 / Real.log 2 : ℝ) ≤ 2 := by
      have h2le : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt half_lt_log_two
      calc
        (1 / Real.log 2 : ℝ) ≤ 1 / (1 / 2 : ℝ) := by
          exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) h2le
        _ = 2 := by norm_num
    have hstep1 : (A + Real.log (10 : ℝ)) / Real.log 2 ≤ 2 * (A + Real.log (10 : ℝ)) := by
      calc
        (A + Real.log (10 : ℝ)) / Real.log 2 = (A + Real.log (10 : ℝ)) * (1 / Real.log 2) := by ring
        _ ≤ (A + Real.log (10 : ℝ)) * 2 := mul_le_mul_of_nonneg_left hinv hA9
        _ = 2 * (A + Real.log (10 : ℝ)) := by ring
    have hten : Real.log (10 : ℝ) ≤ 9 := log_ten_le_nine
    have hst : 2 * (A + Real.log (10 : ℝ)) ≤ 2 * (A + 9) := by
      linarith only [hten]
    have hc : ((J + 1 : ℕ) : ℝ) ≤ 2 * (A + 9) := le_trans (le_trans hdiv hstep1) hst
    have hn : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by norm_cast
    rw [hn] at hc
    exact hc
  -- chain of shell sums
  have hW0'2 : ∀ k ∈ I2, 0 ≤ 4 / (2 : ℝ) ^ k := hW02
  have hchain1b : (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) ≤
      ∑ k ∈ I2, (4 / (2 : ℝ) ^ k) * (∑ u ∈ S.filter (fun u => dIdx ‖w - u‖ = k), M u) := by
    exact hshell
  have hchain2b :
      (∑ k ∈ I2, (4 / (2 : ℝ) ^ k) * (∑ u ∈ S.filter (fun u => dIdx ‖w - u‖ = k), M u)) ≤
        ∑ k ∈ I2, (4 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hmass2 k hk) (hW0'2 k hk)
  have hterm2 : ∀ k ∈ I2,
      (4 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2)) ≤ (16 : ℝ) * C * (A + 10) := by
    intro k hk
    have hk1 : k + 1 ≤ J + 1 := by
      have hlt : k < J + 1 := Finset.mem_range.mp hk
      omega
    have h2k1 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (J + 1) :=
      pow_le_pow_right₀ (by norm_num) hk1
    have h2R : (2 : ℝ) ^ (k + 1) ≤ 10 * R := le_trans h2k1 h2J
    have hlog1 : Real.log (R + (2 : ℝ) ^ (k + 1) + 2) ≤ Real.log (11 : ℝ) + Real.log (R + 2) := by
      have hle11 : R + (2 : ℝ) ^ (k + 1) + 2 ≤ 11 * (R + 2) := by
        linarith only [h2R, hR]
      have hlogl := Real.log_le_log (by positivity : (0 : ℝ) < R + (2 : ℝ) ^ (k + 1) + 2) hle11
      have hmul : Real.log (11 * (R + 2)) = Real.log (11 : ℝ) + Real.log (R + 2) :=
        Real.log_mul (by norm_num : (11 : ℝ) ≠ 0) (ne_of_gt (by linarith only [hR] : (0 : ℝ) < R + 2))
      rwa [hmul] at hlogl
    have hmain2 : Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2 ≤ A + 10 := by
      have h11le : Real.log (11 : ℝ) ≤ 10 := log_eleven_le_ten
      calc
        Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2 ≤ Real.log (11 : ℝ) + Real.log (R + 2) + q + 2 := by linarith only [hlog1]
        _ ≤ 10 + Real.log (R + 2) + q + 2 := by
          have hadd := add_le_add_right h11le (Real.log (R + 2) + q + 2)
          linarith only [hadd]
        _ = A + 10 := by dsimp [A]; ring
    have hps : (2 : ℝ) ^ (k + 1) + 1 ≤ (2 : ℝ) ^ (k + 2) := pow_succ_two_add_one_le (k := k)
    have hposLog : (0 : ℝ) ≤ Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2 := by
      have h1 : (1 : ℝ) ≤ R + (2 : ℝ) ^ (k + 1) + 2 := by
        have hp2 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) (k + 1)
        linarith only [hp2, hR]
      have hl : 0 ≤ Real.log (R + (2 : ℝ) ^ (k + 1) + 2) := Real.log_nonneg h1
      linarith only [hl, hq]
    have hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by positivity
    have hA10pos : (0 : ℝ) ≤ A + 10 := by linarith only [hApos]
    have hmul1 : ((2 : ℝ) ^ (k + 1) + 1) * (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2)
        ≤ (2 : ℝ) ^ (k + 2) * (A + 10) := mul_le_mul hps hmain2 hposLog hpos2
    have hmul2 : C * (((2 : ℝ) ^ (k + 1) + 1) * (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2))
        ≤ C * ((2 : ℝ) ^ (k + 2) * (A + 10)) := mul_le_mul_of_nonneg_left hmul1 hC
    have hfacb : C * ((2 : ℝ) ^ (k + 1) + 1) * (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2)
        ≤ C * (2 : ℝ) ^ (k + 2) * (A + 10) := by
      calc
        C * ((2 : ℝ) ^ (k + 1) + 1) * (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2)
            = C * (((2 : ℝ) ^ (k + 1) + 1) * (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2)) := by ring
        _ ≤ C * ((2 : ℝ) ^ (k + 2) * (A + 10)) := hmul2
        _ = C * (2 : ℝ) ^ (k + 2) * (A + 10) := by ring
    have hcoef : (4 / (2 : ℝ) ^ k) * ((2 : ℝ) ^ (k + 2)) ≤ 16 := by
      have hk0 : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num : (0 : ℝ) < 2) k
      have hrat : (2 : ℝ) ^ (k + 2) / (2 : ℝ) ^ k = 4 := by
        field_simp [hk0.ne']
        rw [pow_succ, pow_succ]
        ring
      calc
        (4 / (2 : ℝ) ^ k) * (2 : ℝ) ^ (k + 2) = 4 * ((2 : ℝ) ^ (k + 2) / (2 : ℝ) ^ k) := by
          field_simp [hk0.ne']
        _ = 4 * 4 := by rw [hrat]
        _ = 16 := by norm_num
        _ ≤ 16 := by norm_num
    have hWk0 : (0 : ℝ) ≤ 4 / (2 : ℝ) ^ k := by positivity
    have hstepb : (4 / (2 : ℝ) ^ k) * (C * (2 : ℝ) ^ (k + 2) * (A + 10)) ≤ (16 : ℝ) * C * (A + 10) := by
      calc
        (4 / (2 : ℝ) ^ k) * (C * (2 : ℝ) ^ (k + 2) * (A + 10))
            = C * (A + 10) * ((4 / (2 : ℝ) ^ k) * (2 : ℝ) ^ (k + 2)) := by ring
        _ ≤ C * (A + 10) * 16 := by
          exact mul_le_mul_of_nonneg_left hcoef (mul_nonneg hC (by linarith only [hApos] : (0 : ℝ) ≤ A + 10))
        _ = (16 : ℝ) * C * (A + 10) := by ring
    calc
      (4 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2))
          ≤ (4 / (2 : ℝ) ^ k) * (C * (2 : ℝ) ^ (k + 2) * (A + 10)) := by
              exact mul_le_mul_of_nonneg_left hfacb hWk0
      _ ≤ (16 : ℝ) * C * (A + 10) := hstepb
  have hsum2 : (∑ k ∈ I2,
        (4 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
          (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2))) ≤
          ((J + 1 : ℕ) : ℝ) * ((16 : ℝ) * C * (A + 10)) := by
    calc
      (∑ k ∈ I2,
          (4 / (2 : ℝ) ^ k) * (C * ((2 : ℝ) ^ (k + 1) + 1) *
            (Real.log (R + (2 : ℝ) ^ (k + 1) + 2) + q + 2)))
          ≤ ∑ k ∈ I2, ((16 : ℝ) * C * (A + 10)) := Finset.sum_le_sum hterm2
      _ = ((J + 1 : ℕ) : ℝ) * ((16 : ℝ) * C * (A + 10)) := by
        simp [I2, Finset.sum_const, nsmul_eq_mul]
  have hfinalb1 :
      (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) ≤
        ((J + 1 : ℕ) : ℝ) * ((16 : ℝ) * C * (A + 10)) :=
    le_trans (le_trans hchain1b hchain2b) hsum2
  have hjn : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by norm_cast
  have hfacb : 0 ≤ (16 : ℝ) * C * (A + 10) := by
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hC) (by linarith only [hApos] : (0 : ℝ) ≤ A + 10)
  have hfinalb2 : ((J + 1 : ℕ) : ℝ) * ((16 : ℝ) * C * (A + 10)) ≤
      (32 : ℝ) * C * (A + 9) * (A + 10) := by
    calc
      ((J + 1 : ℕ) : ℝ) * ((16 : ℝ) * C * (A + 10))
          = ((J : ℝ) + 1) * ((16 : ℝ) * C * (A + 10)) := by rw [hjn]
      _ ≤ (2 * (A + 9)) * ((16 : ℝ) * C * (A + 10)) := by
        exact mul_le_mul_of_nonneg_right hJp1 hfacb
      _ = (32 : ℝ) * C * (A + 9) * (A + 10) := by ring
  have hA0 : 0 ≤ A := hApos
  have hAleA2 : A ≤ A ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (by linarith only [hA2] : (1 : ℝ) ≤ A) hA0
    simpa [mul_one, pow_two] using h
  have hfinalb3 : (32 : ℝ) * C * (A + 9) * (A + 10) ≤ (8192 : ℝ) * C * (A ^ 2 + 1) := by
    linarith only [mul_le_mul_of_nonneg_left hAleA2 hC, mul_nonneg hC (sq_nonneg A), hC]
  calc
    (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) ≤
        ((J + 1 : ℕ) : ℝ) * ((16 : ℝ) * C * (A + 10)) := hfinalb1
    _ ≤ (32 : ℝ) * C * (A + 9) * (A + 10) := hfinalb2
    _ ≤ (8192 : ℝ) * C * (A ^ 2 + 1) := hfinalb3
    _ = (8192 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by rfl


/-- `(2^m)^2 = 4^m`. -/
private lemma pow_two_sq_eq_four_pow (m : ℕ) : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
  calc
    ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (m * 2) := by rw [pow_mul]
    _ = (2 : ℝ) ^ (2 * m) := by rw [mul_comm]
    _ = ((2 : ℝ) ^ 2) ^ m := by rw [pow_mul]
    _ = (4 : ℝ) ^ m := by norm_num

/-- far regime: points with `‖u‖ > 4R`; weight `(4R/3)/‖u‖²`. -/
private theorem farBound {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) {S : Finset ℂ} {m : ℂ → ℤ}
    (hu1 : ∀ u ∈ S, 1 ≤ ‖u‖) (hm : ∀ u ∈ S, 0 ≤ (m u : ℤ))
    (hN : ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ), (((m u : ℤ) : ℝ))) ≤
        C * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2))
    {R : ℝ} (hR : 2 ≤ R) :
    (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), (((m u : ℤ) : ℝ)) * ((4 * R / 3) / ‖u‖ ^ 2)) ≤
      (8192 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by
  classical
  let M : ℂ → ℝ := fun u => (((m u : ℤ) : ℝ))
  change (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) ≤
      (8192 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1)
  set A : ℝ := Real.log (R + 2) + q + 2
  have hMm : ∀ u ∈ S, 0 ≤ M u := by
    intro u hu
    exact Int.cast_nonneg (hm u hu)
  have hlogR : 0 ≤ Real.log (R + 2) := by
    refine Real.log_nonneg ?_
    linarith
  have hApos : 0 ≤ A := by dsimp [A]; linarith
  have hA2 : (2 : ℝ) ≤ A := by dsimp [A]; linarith
  have hlogA : Real.log (R + 2) ≤ A := by dsimp [A]; linarith
  let K0 : ℕ := dIdx (4 * R)
  have hK0pow : (2 : ℝ) ^ K0 ≤ 4 * R := by
    have h1 := dIdx_pow_le (by linarith only [hR] : (1 : ℝ) ≤ 4 * R)
    simpa [K0] using h1
  have hK0lt : 4 * R < (2 : ℝ) ^ (K0 + 1) := by
    have h1 := dIdx_lt_pow_succ (by linarith only [hR] : (1 : ℝ) ≤ 4 * R)
    simpa [K0] using h1
  have hK0large : 2 * R ≤ (2 : ℝ) ^ K0 := by
    have h : 4 * R < 2 * (2 : ℝ) ^ K0 := by
      rw [pow_succ] at hK0lt
      simpa [mul_comm, mul_left_comm, mul_assoc] using hK0lt
    linarith only [h]
  have hK0le : ((K0 : ℕ) : ℝ) ≤ 2 * A + 4 := by
    have hlogm : ((K0 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (4 * R) := by
      have hlog1 : Real.log ((2 : ℝ) ^ K0) ≤ Real.log (4 * R) := by
        exact Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) K0) hK0pow
      have hlp : Real.log ((2 : ℝ) ^ K0) = ((K0 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow (2 : ℝ) K0]
      rwa [hlp] at hlog1
    have h4 : Real.log (4 * R) = Real.log (4 : ℝ) + Real.log R := by
      exact Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by linarith : R ≠ 0)
    have hRle : Real.log R ≤ Real.log (R + 2) := by
      exact Real.log_le_log (by linarith : (0 : ℝ) < R) (by linarith)
    have hlogm' : ((K0 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (4 : ℝ) + A := by
      calc
        ((K0 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (4 : ℝ) + Real.log R := by
          rwa [h4] at hlogm
        _ ≤ Real.log (4 : ℝ) + A := by linarith only [hRle, hlogA]
    have h4le : Real.log (4 : ℝ) ≤ 2 := by
      have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
        have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h2
        exact h2
      have hmul : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        rw [Real.log_pow (2 : ℝ) 2]
        norm_num
      rw [hmul]
      linarith only [hlog2le]
    have hmain : ((K0 : ℕ) : ℝ) * Real.log 2 ≤ A + 2 := by
      calc
        ((K0 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (4 : ℝ) + A := hlogm'
        _ ≤ 2 + A := by linarith only [h4le]
        _ = A + 2 := by ring
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [half_lt_log_two]
    have hdiv : ((K0 : ℕ) : ℝ) ≤ (A + 2) / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      simpa [mul_comm] using hmain
    have hA2pos : 0 ≤ A + 2 := by linarith only [hApos]
    have hinv : (1 / Real.log 2 : ℝ) ≤ 2 := by
      have h2le : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt half_lt_log_two
      calc
        (1 / Real.log 2 : ℝ) ≤ 1 / (1 / 2 : ℝ) := by
          exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) h2le
        _ = 2 := by norm_num
    have hst : (A + 2) / Real.log 2 ≤ 2 * A + 4 := by
      calc
        (A + 2) / Real.log 2 = (A + 2) * (1 / Real.log 2) := by ring
        _ ≤ (A + 2) * 2 := mul_le_mul_of_nonneg_left hinv hA2pos
        _ = 2 * A + 4 := by ring
    exact le_trans hdiv hst
  let F : ℂ → ℕ := fun u => dIdx ‖u‖ - K0
  let J3 : ℕ := S.sup F
  let I3 : Finset ℕ := Finset.range (J3 + 1)
  have hK3 : ∀ u ∈ S, 4 * R < ‖u‖ → F u ∈ I3 := by
    intro u hu hfar
    have hs : F u ≤ S.sup F := Finset.le_sup (f := F) hu
    exact Finset.mem_range.mpr (by dsimp [J3, I3]; omega)
  -- weight bound on shell j
  have hW3 : ∀ u ∈ S, 4 * R < ‖u‖ → ∀ j ∈ I3, F u = j →
      ((4 * R / 3) / ‖u‖ ^ 2) ≤ (4 * R / 3) / (4 : ℝ) ^ (K0 + j) := by
    intro u hu hfar j hjin hfj
    have hge : K0 ≤ dIdx ‖u‖ := by
      have h4Ru : 4 * R ≤ ‖u‖ := le_of_lt hfar
      have hm := dIdx_mono (by linarith only [hR] : (1 : ℝ) ≤ 4 * R) h4Ru
      simpa [K0] using hm
    have hdIdx : dIdx ‖u‖ = K0 + j := by
      have hsub : dIdx ‖u‖ - K0 = j := by
        simpa [F] using hfj
      omega
    have h2u : (2 : ℝ) ^ (K0 + j) ≤ ‖u‖ := by
      have h0 := dIdx_pow_le (hu1 u hu)
      rw [hdIdx] at h0
      exact h0
    have hsq : ((2 : ℝ) ^ (K0 + j)) ^ 2 ≤ ‖u‖ ^ 2 := by
      have hX : 0 ≤ (2 : ℝ) ^ (K0 + j) := by positivity
      have hY : 0 ≤ ‖u‖ := norm_nonneg u
      rw [sq_le_sq]
      rw [abs_of_nonneg hX, abs_of_nonneg hY]
      exact h2u
    have h4u : (4 : ℝ) ^ (K0 + j) ≤ ‖u‖ ^ 2 := by
      rwa [pow_two_sq_eq_four_pow (K0 + j)] at hsq
    have hdenpos : (0 : ℝ) < (4 : ℝ) ^ (K0 + j) := pow_pos (by norm_num : (0 : ℝ) < 4) (K0 + j)
    have hupos : 0 < ‖u‖ ^ 2 := by
      have hnorm : 0 < ‖u‖ := by
        have := hu1 u hu
        linarith
      exact pow_pos hnorm 2
    have hdivv := div_le_div_of_nonneg_left (by linarith only [hR] : (0 : ℝ) ≤ 4 * R / 3)
      hdenpos h4u
    exact hdivv
  have hW03 : ∀ j ∈ I3, 0 ≤ (4 * R / 3) / (4 : ℝ) ^ (K0 + j) := by
    intro j hj
    exact div_nonneg (by linarith only [hR] : (0 : ℝ) ≤ 4 * R / 3) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (K0 + j))
  have hshell3 := sum_le_shell_sum (S := S) (M := M) hMm
    (P := fun u : ℂ => 4 * R < ‖u‖) (K := F) (I := I3) hK3
    (wt := fun u : ℂ => (4 * R / 3) / ‖u‖ ^ 2)
    (W := fun k : ℕ => (4 * R / 3) / (4 : ℝ) ^ (K0 + k)) hW3 hW03
  -- mass over shell j
  have hdIdx_le : ∀ {u : ℂ} {j : ℕ}, u ∈ S → F u = j → dIdx ‖u‖ ≤ K0 + j := by
    intro u j hu hfj
    have hsub : dIdx ‖u‖ - K0 = j := by simpa [F] using hfj
    by_cases hge : K0 ≤ dIdx ‖u‖
    · omega
    · have hlt : dIdx ‖u‖ < K0 := by omega
      have htrunc : dIdx ‖u‖ - K0 = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
      have hfj0 : j = 0 := by
        have hs : (0 : ℕ) = j := by simpa [htrunc] using hsub
        exact hs.symm
      omega
  have hmass3 : ∀ j ∈ I3,
      (∑ u ∈ S.filter (fun u => F u = j), M u) ≤
        C * ((2 : ℝ) ^ (K0 + j + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2) := by
    intro j hj
    have hρ : (1 : ℝ) ≤ (2 : ℝ) ^ (K0 + j + 1) := two_pow_ge_one (K0 + j + 1)
    have hNk := hN (0 : ℂ) ((2 : ℝ) ^ (K0 + j + 1)) hρ
    have hcb : (∑ u ∈ S.filter (fun u => ‖u‖ ≤ (2 : ℝ) ^ (K0 + j + 1)), M u) ≤
        C * ((2 : ℝ) ^ (K0 + j + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2) := by
      simpa [M, zero_add] using hNk
    have hsub : S.filter (fun u => F u = j) ⊆
        S.filter (fun u => ‖u‖ ≤ (2 : ℝ) ^ (K0 + j + 1)) := by
      intro u hu
      have huS : u ∈ S := (Finset.mem_filter.mp hu).1
      have hfj : F u = j := (Finset.mem_filter.mp hu).2
      have hdle : dIdx ‖u‖ ≤ K0 + j := hdIdx_le huS hfj
      have hus : ‖u‖ ≤ (2 : ℝ) ^ (dIdx ‖u‖ + 1) := dIdx_pow_succ_ge_of_nonneg (norm_nonneg u)
      have hle : dIdx ‖u‖ + 1 ≤ K0 + j + 1 := by omega
      have hpowle : (2 : ℝ) ^ (dIdx ‖u‖ + 1) ≤ (2 : ℝ) ^ (K0 + j + 1) :=
        pow_le_pow_right₀ (by norm_num) hle
      exact Finset.mem_filter.mpr ⟨huS, le_trans hus hpowle⟩
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro u hu hu'
      exact hMm u (Finset.mem_filter.mp hu).1)) hcb
  -- chain: TF ≤ Σ_j W3 j · mass_j ≤ Σ_j W3 j · (ball-bound)
  have hW0'3 : ∀ j ∈ I3, 0 ≤ (4 * R / 3) / (4 : ℝ) ^ (K0 + j) := hW03
  have hchain1c : (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) ≤
      ∑ j ∈ I3, (4 * R / 3) / (4 : ℝ) ^ (K0 + j) *
        (∑ u ∈ S.filter (fun u => F u = j), M u) := by
    exact hshell3
  have hchain2c :
      (∑ j ∈ I3, (4 * R / 3) / (4 : ℝ) ^ (K0 + j) *
        (∑ u ∈ S.filter (fun u => F u = j), M u)) ≤
        ∑ j ∈ I3, (4 * R / 3) / (4 : ℝ) ^ (K0 + j) *
          (C * ((2 : ℝ) ^ (K0 + j + 1) + 1) *
            (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hmass3 j hj) (hW0'3 j hj)
  -- per-term bound
  have hlog2le1 : Real.log (2 : ℝ) ≤ 1 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2
    exact h2
  have hlogterm : ∀ j ∈ I3,
      Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2 ≤ ((K0 + j : ℕ) : ℝ) + q + 4 := by
    intro j hj
    have hl := log_pow_add_two_le (k := K0 + j)
    have hn : ((K0 + j + 2 : ℕ) : ℝ) = ((K0 + j : ℕ) : ℝ) + 2 := by norm_cast
    rw [hn] at hl
    have hc : (0 : ℝ) ≤ ((K0 + j : ℕ) : ℝ) + 2 := by positivity
    have hm : (((K0 + j : ℕ) : ℝ) + 2) * Real.log 2 ≤ ((K0 + j : ℕ) : ℝ) + 2 := by
      have hmm := mul_le_mul_of_nonneg_left hlog2le1 hc
      simpa using hmm
    calc
      Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2 ≤ (((K0 + j : ℕ) : ℝ) + 2) * Real.log 2 + q + 2 := by linarith only [hl]
      _ ≤ ((K0 + j : ℕ) : ℝ) + 2 + q + 2 := by
        have hmm := add_le_add_right hm (q + 2)
        linarith only [hmm]
      _ = ((K0 + j : ℕ) : ℝ) + q + 4 := by ring
  have hterm3 : ∀ j ∈ I3,
      (4 * R / 3) / (4 : ℝ) ^ (K0 + j) *
        (C * ((2 : ℝ) ^ (K0 + j + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2)) ≤
        (16 * R / 3) * C * ((1 / 2 : ℝ) ^ (K0 + j)) * (((K0 + j : ℕ) : ℝ) + q + 4) := by
    intro j hj
    have hps : (2 : ℝ) ^ (K0 + j + 1) + 1 ≤ (2 : ℝ) ^ (K0 + j + 2) :=
      pow_succ_two_add_one_le (k := K0 + j)
    have hposLog : (0 : ℝ) ≤ Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2 := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (K0 + j + 1) + 2 := by linarith only [two_pow_ge_one (K0 + j + 1)]
      have hl : 0 ≤ Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) := Real.log_nonneg h1
      linarith only [hl, hq]
    have hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (K0 + j + 2) := by positivity
    have hmainlog : Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2 ≤ ((K0 + j : ℕ) : ℝ) + q + 4 :=
      hlogterm j hj
    have hpq : (0 : ℝ) ≤ ((K0 + j : ℕ) : ℝ) + q + 4 := by
      have hn0 : 0 ≤ ((K0 + j : ℕ) : ℝ) := by positivity
      linarith only [hn0, hq]
    have hmul1 : ((2 : ℝ) ^ (K0 + j + 1) + 1) * (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2)
        ≤ (2 : ℝ) ^ (K0 + j + 2) * (((K0 + j : ℕ) : ℝ) + q + 4) :=
      mul_le_mul hps hmainlog hposLog hpos2
    have hmul2 : C * (((2 : ℝ) ^ (K0 + j + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2))
        ≤ C * ((2 : ℝ) ^ (K0 + j + 2) * (((K0 + j : ℕ) : ℝ) + q + 4)) :=
      mul_le_mul_of_nonneg_left hmul1 hC
    have hfac1 : C * ((2 : ℝ) ^ (K0 + j + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2)
        ≤ C * (2 : ℝ) ^ (K0 + j + 2) * (((K0 + j : ℕ) : ℝ) + q + 4) := by
      calc
        C * ((2 : ℝ) ^ (K0 + j + 1) + 1) * (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2)
            = C * (((2 : ℝ) ^ (K0 + j + 1) + 1) * (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2)) := by ring
        _ ≤ C * ((2 : ℝ) ^ (K0 + j + 2) * (((K0 + j : ℕ) : ℝ) + q + 4)) := hmul2
        _ = C * (2 : ℝ) ^ (K0 + j + 2) * (((K0 + j : ℕ) : ℝ) + q + 4) := by ring
    have hcoef : (4 * R / 3) / (4 : ℝ) ^ (K0 + j) * ((2 : ℝ) ^ (K0 + j + 2)) =
        (16 * R / 3) * ((1 / 2 : ℝ) ^ (K0 + j)) := by
      have hk0 : (4 : ℝ) ^ (K0 + j) ≠ 0 := pow_ne_zero (K0 + j) (by norm_num : (4 : ℝ) ≠ 0)
      have htwo4 := two_pow_add_two_eq (K0 + j)
      calc
        (4 * R / 3) / (4 : ℝ) ^ (K0 + j) * (2 : ℝ) ^ (K0 + j + 2)
            = (4 * R / 3) * ((2 : ℝ) ^ (K0 + j + 2) / (4 : ℝ) ^ (K0 + j)) := by
                field_simp [hk0]; try ring
        _ = (4 * R / 3) * (4 * ((1 / 2 : ℝ) ^ (K0 + j)) * (4 : ℝ) ^ (K0 + j) / (4 : ℝ) ^ (K0 + j)) := by
            rw [htwo4]
        _ = (4 * R / 3) * (4 * ((1 / 2 : ℝ) ^ (K0 + j))) := by
            field_simp [hk0]; try ring
        _ = (16 * R / 3) * ((1 / 2 : ℝ) ^ (K0 + j)) := by ring
    have hWk0 : (0 : ℝ) ≤ (4 * R / 3) / (4 : ℝ) ^ (K0 + j) := by positivity
    calc
      (4 * R / 3) / (4 : ℝ) ^ (K0 + j) * (C * ((2 : ℝ) ^ (K0 + j + 1) + 1) *
          (Real.log ((2 : ℝ) ^ (K0 + j + 1) + 2) + q + 2))
          ≤ (4 * R / 3) / (4 : ℝ) ^ (K0 + j) *
              (C * (2 : ℝ) ^ (K0 + j + 2) * (((K0 + j : ℕ) : ℝ) + q + 4)) := by
              exact mul_le_mul_of_nonneg_left hfac1 hWk0
      _ = ((4 * R / 3) / (4 : ℝ) ^ (K0 + j) * (2 : ℝ) ^ (K0 + j + 2)) *
          (C * (((K0 + j : ℕ) : ℝ) + q + 4)) := by ring
      _ = ((16 * R / 3) * ((1 / 2 : ℝ) ^ (K0 + j))) *
          (C * (((K0 + j : ℕ) : ℝ) + q + 4)) := by rw [hcoef]
      _ = (16 * R / 3) * C * ((1 / 2 : ℝ) ^ (K0 + j)) * (((K0 + j : ℕ) : ℝ) + q + 4) := by ring
  have hbound_j : ∀ j ∈ I3,
      (16 * R / 3) * C * ((1 / 2 : ℝ) ^ (K0 + j)) * (((K0 + j : ℕ) : ℝ) + q + 4) ≤
        (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * ((1 / 2 : ℝ) ^ j) *
          ((((K0 : ℕ) : ℝ) + q + 4) + (j : ℝ)) := by
    intro j hj
    have hk1 : (1 / 2 : ℝ) ^ (K0 + j) = (1 / 2 : ℝ) ^ K0 * (1 / 2 : ℝ) ^ j := by
      rw [← pow_add]
    have hn : ((K0 + j : ℕ) : ℝ) = ((K0 : ℕ) : ℝ) + (j : ℝ) := by norm_cast
    rw [hk1, hn]
    exact le_of_eq (by ring)
  have hsum_j :
      (∑ j ∈ I3, (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * ((1 / 2 : ℝ) ^ j) *
          ((((K0 : ℕ) : ℝ) + q + 4) + (j : ℝ))) ≤
        (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := by
    calc
      (∑ j ∈ I3, (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * ((1 / 2 : ℝ) ^ j) *
          ((((K0 : ℕ) : ℝ) + q + 4) + (j : ℝ)))
          = (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) *
              (∑ j ∈ I3, ((1 / 2 : ℝ) ^ j) * ((((K0 : ℕ) : ℝ) + q + 4) + (j : ℝ))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ ≤ (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) *
          (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := by
        have hgeomA : (∑ j ∈ I3, ((1 / 2 : ℝ) ^ j)) ≤ 2 := by
          have hg : (∑ j ∈ I3, ((1 / 2 : ℝ) ^ j)) ≤ 1 / (1 - (1 / 2 : ℝ)) :=
            Commons.Analysis.Asymptotics.geom_finset_le (r := (1 / 2 : ℝ))
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) I3
          calc
            (∑ j ∈ I3, ((1 / 2 : ℝ) ^ j)) ≤ 1 / (1 - (1 / 2 : ℝ)) := hg
            _ = 2 := by norm_num
        have hmulA : (∑ j ∈ I3, (j : ℝ) * ((1 / 2 : ℝ) ^ j)) ≤ 2 := by
          have h1 : (∑ j ∈ Finset.range (J3 + 1), (j : ℝ) * ((1 / 2 : ℝ) ^ j)) ≤
              (1 / 2 : ℝ) / (1 - (1 / 2 : ℝ)) ^ 2 :=
            Commons.Analysis.Asymptotics.sum_range_mul_geom_le (r := (1 / 2 : ℝ))
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) J3
          calc
            (∑ j ∈ I3, (j : ℝ) * ((1 / 2 : ℝ) ^ j)) ≤ (1 / 2 : ℝ) / (1 - (1 / 2 : ℝ)) ^ 2 := by
              simpa [I3] using h1
            _ = 2 := by norm_num
        have hc1 : (0 : ℝ) ≤ (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) := by
          have hRp : (0 : ℝ) ≤ R := by linarith only [hR]
          positivity
        have hK0p : (0 : ℝ) ≤ ((K0 : ℕ) : ℝ) + q + 4 := by positivity
        have hinner :
            (∑ j ∈ I3, ((1 / 2 : ℝ) ^ j) * ((((K0 : ℕ) : ℝ) + q + 4) + (j : ℝ))) ≤
              2 * (((K0 : ℕ) : ℝ) + q + 4) + 2 := by
          calc
            (∑ j ∈ I3, ((1 / 2 : ℝ) ^ j) * ((((K0 : ℕ) : ℝ) + q + 4) + (j : ℝ)))
                = (∑ j ∈ I3, ((((K0 : ℕ) : ℝ) + q + 4) * ((1 / 2 : ℝ) ^ j) +
                    ((j : ℝ) * ((1 / 2 : ℝ) ^ j)))) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = (((K0 : ℕ) : ℝ) + q + 4) * (∑ j ∈ I3, ((1 / 2 : ℝ) ^ j)) +
                (∑ j ∈ I3, (j : ℝ) * ((1 / 2 : ℝ) ^ j)) := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            _ ≤ (((K0 : ℕ) : ℝ) + q + 4) * 2 + 2 := by
                    exact add_le_add (mul_le_mul_of_nonneg_left hgeomA hK0p) hmulA
            _ = 2 * (((K0 : ℕ) : ℝ) + q + 4) + 2 := by ring
        exact mul_le_mul_of_nonneg_left hinner hc1
  have hsum3 :
      (∑ j ∈ I3, (16 * R / 3) * C * ((1 / 2 : ℝ) ^ (K0 + j)) * (((K0 + j : ℕ) : ℝ) + q + 4)) ≤
        (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := by
    exact le_trans (Finset.sum_le_sum hbound_j) hsum_j
  -- bound the decay factor
  have hR0 : R ≠ 0 := by linarith
  have hfac_half : (16 * R / 3) * ((1 / 2 : ℝ) ^ K0) ≤ 8 / 3 := by
    have h12 : (1 / 2 : ℝ) ^ K0 = 1 / (2 : ℝ) ^ K0 := one_div_pow (2 : ℝ) K0
    rw [h12]
    have h2Rpos : (0 : ℝ) < 2 * R := by positivity
    have hdiv : 1 / (2 : ℝ) ^ K0 ≤ 1 / (2 * R) := by
      exact one_div_le_one_div_of_le h2Rpos hK0large
    have hcoeff : (0 : ℝ) ≤ 16 * R / 3 := by
      have hRle : (0 : ℝ) ≤ R := by linarith only [hR]
      exact div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hRle) (by norm_num : (0 : ℝ) ≤ 3)
    calc
      (16 * R / 3) * (1 / (2 : ℝ) ^ K0) ≤ (16 * R / 3) * (1 / (2 * R)) :=
        mul_le_mul_of_nonneg_left hdiv hcoeff
      _ = 8 / 3 := by
        field_simp [hR0]
        ring
  have hboundK : (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) ≤ 30 * A := by
    have hqA : q ≤ A := by dsimp [A]; linarith only [hlogR]
    have hK0b : ((K0 : ℕ) : ℝ) ≤ 2 * A + 4 := hK0le
    linarith only [hK0b, hqA, hA2]
  have hA0 : 0 ≤ A := hApos
  have hAleA2 : A ≤ A ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (by linarith only [hA2] : (1 : ℝ) ≤ A) hA0
    simpa [mul_one, pow_two] using h
  have hfacA : (8 / 3) * (30 * A) ≤ 8192 * (A ^ 2 + 1) := by
    linarith only [hAleA2, sq_nonneg A]
  have hfinal1c :
      (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) ≤
        (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) :=
    le_trans (le_trans hchain1c hchain2c) (le_trans (Finset.sum_le_sum hterm3) hsum3)
  have hfinal2c :
      (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) ≤
        (8 / 3) * C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := by
    have hc1 : 0 ≤ C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := by
      have h2 : 0 ≤ 2 * (((K0 : ℕ) : ℝ) + q + 4) + 2 := by positivity
      exact mul_nonneg hC h2
    calc
      (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2)
          = ((16 * R / 3) * ((1 / 2 : ℝ) ^ K0)) * (C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2)) := by ring
      _ ≤ (8 / 3) * (C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2)) := by
          exact mul_le_mul_of_nonneg_right hfac_half hc1
      _ = (8 / 3) * C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := by ring
  have hfinal3c : (8 / 3) * C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) ≤
      (8192 : ℝ) * C * (A ^ 2 + 1) := by
    have hb : (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) ≤ 30 * A := hboundK
    calc
      (8 / 3) * C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2)
          = (8 / 3) * C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := rfl
      _ ≤ (8 / 3) * C * (30 * A) := by
          exact mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8 / 3) hC)
      _ ≤ (8192 : ℝ) * C * (A ^ 2 + 1) := by
        have hfac := hfacA
        have hm1 : (8 / 3) * C * (30 * A) ≤ (8192 : ℝ) * C * (A ^ 2 + 1) := by
          -- (8/3)·C·30A ≤ C·(8/3·30A) ≤ C·(8192(A²+1))
          have hA' : (0 : ℝ) ≤ A ^ 2 + 1 := by positivity
          have hprod : (8 / 3) * (30 * A) ≤ 8192 * (A ^ 2 + 1) := hfacA
          calc
            (8 / 3) * C * (30 * A) = C * ((8 / 3) * (30 * A)) := by ring
            _ ≤ C * (8192 * (A ^ 2 + 1)) := mul_le_mul_of_nonneg_left hprod hC
            _ = (8192 : ℝ) * C * (A ^ 2 + 1) := by ring
        exact hm1
  calc
    (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) ≤
        (16 * R / 3) * C * ((1 / 2 : ℝ) ^ K0) * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := hfinal1c
    _ ≤ (8 / 3) * C * (2 * (((K0 : ℕ) : ℝ) + q + 4) + 2) := hfinal2c
    _ ≤ (8192 : ℝ) * C * (A ^ 2 + 1) := hfinal3c
    _ = (8192 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by rfl


/-- low-region weight bound: `R/(‖u‖·d) ≤ (4/3)/‖u‖` when `d ≥ 3R/4`. -/
private lemma lowWeightBound {R : ℝ} (hR : 0 < R) {u : ℂ} (_hu1 : 1 ≤ ‖u‖)
    (hu4 : ‖u‖ ≤ R / 4) {d : ℝ} (hdpos : 0 < d) (hdge : 3 * R / 4 ≤ d) :
    R / (‖u‖ * d) ≤ 4 / 3 / ‖u‖ := by
  have hupos : 0 < ‖u‖ := by linarith
  have hden : 0 < ‖u‖ * d := mul_pos hupos hdpos
  rw [div_le_iff₀ hden]
  field_simp [hupos.ne', hdpos.ne']
  nlinarith

/-- far-region weight bound: `R/(‖u‖·d) ≤ (4R/3)/‖u‖²` when `‖u‖ ≥ 4R`, `d ≥ ‖u‖−R`. -/
private lemma farWeightBound {R : ℝ} (hR : 0 < R) {u : ℂ} {d : ℝ}
    (hdpos : 0 < d) (hu : (4 * R : ℝ) ≤ ‖u‖) (hdu : ‖u‖ - R ≤ d) :
    R / (‖u‖ * d) ≤ (4 * R / 3) / ‖u‖ ^ 2 := by
  have hupos : 0 < ‖u‖ := by nlinarith
  have hden : 0 < ‖u‖ * d := mul_pos hupos hdpos
  have hdge : 3 * ‖u‖ / 4 ≤ ‖u‖ - R := by nlinarith
  rw [div_le_iff₀ hden]
  have hmain : (4 * R / 3) / ‖u‖ ^ 2 * (‖u‖ * d) ≥ R := by
    field_simp [hupos.ne']
    nlinarith [hdge]
  exact hmain

/-- mid-region weight bound: `R/(‖u‖·d) ≤ 4/d` when `‖u‖ ≥ R/4`. -/
private lemma midWeightBound {R : ℝ} (hR : 0 < R) {u : ℂ} {d : ℝ}
    (hdpos : 0 < d) (hu : R / 4 ≤ ‖u‖) :
    R / (‖u‖ * d) ≤ 4 / d := by
  have hupos : 0 < ‖u‖ := by nlinarith [hu]
  have hden : 0 < ‖u‖ * d := mul_pos hupos hdpos
  rw [div_le_iff₀ hden]
  field_simp [hupos.ne', hdpos.ne']
  nlinarith

theorem farSum_weight_bound {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : Finset ℂ) (m : ℂ → ℤ),
        (∀ u ∈ S, 1 ≤ ‖u‖) →
        (∀ u ∈ S, 0 ≤ (m u : ℤ)) →
        (∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
          (∑ u ∈ S.filter (fun u => ‖u - a‖ ≤ ρ), (((m u : ℤ) : ℝ))) ≤
            C * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + q + 2)) →
        ∀ R : ℝ, 2 ≤ R → ∀ w : ℂ, ‖w‖ = R →
          (∑ u ∈ S.filter (fun u => 1 < ‖w - u‖),
              (((m u : ℤ) : ℝ)) * (R / (‖u‖ * ‖w - u‖))) ≤
            c * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by
  classical
  refine ⟨(16448 : ℝ) * C, ?_, ?_⟩
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 16448) hC
  · intro S m hu1 hm hN R hR w hw
    let M : ℂ → ℝ := fun u => (((m u : ℤ) : ℝ))
    change (∑ u ∈ S.filter (fun u => 1 < ‖w - u‖), M u * (R / (‖u‖ * ‖w - u‖))) ≤
        (16448 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1)
    set A : ℝ := Real.log (R + 2) + q + 2
    have hMm : ∀ u ∈ S, 0 ≤ M u := by
      intro u hu
      exact Int.cast_nonneg (hm u hu)
    have hlogR : 0 ≤ Real.log (R + 2) := by
      refine Real.log_nonneg ?_
      linarith
    have hApos : 0 ≤ A := by dsimp [A]; linarith
    have hGpos : 0 ≤ A ^ 2 + 1 := by positivity
    -- the three regime bounds
    have hLB := lowBound (q := q) (C := C) hq hC hu1 hm hN (R := R) hR
    have hMB := midBound (q := q) (C := C) hq hC hu1 hm hN (R := R) hR (w := w) hw
    have hFB := farBound (q := q) (C := C) hq hC hu1 hm hN (R := R) hR
    -- split T
    let g1 : ℂ → ℝ := fun u => if ‖u‖ ≤ R / 4 then M u * (4 / 3 / ‖u‖) else 0
    let g2 : ℂ → ℝ := fun u => if (‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖) then M u * (4 / ‖w - u‖) else 0
    let g3 : ℂ → ℝ := fun u => if 4 * R < ‖u‖ then M u * ((4 * R / 3) / ‖u‖ ^ 2) else 0
    have hRpos : 0 < R := by linarith only [hR]
    have htri1 (u : ℂ) : ‖w‖ - ‖u‖ ≤ ‖w - u‖ := by
      have htri' : ‖w‖ ≤ ‖w - u‖ + ‖u‖ := by
        calc ‖w‖ = ‖(w - u) + u‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - u‖ + ‖u‖ := norm_add_le (w - u) u
      linarith only [htri', hw]
    have htri2 (u : ℂ) : ‖u‖ - R ≤ ‖w - u‖ := by
      have htri' : ‖u‖ ≤ R + ‖u - w‖ := by
        have h1 : ‖w + (u - w)‖ = ‖u‖ := by rw [add_sub_cancel]
        have h2 : ‖w + (u - w)‖ ≤ ‖w‖ + ‖u - w‖ := norm_add_le w (u - w)
        calc
          ‖u‖ = ‖w + (u - w)‖ := h1.symm
          _ ≤ ‖w‖ + ‖u - w‖ := h2
          _ ≤ R + ‖u - w‖ := by rw [hw]
      have hu : ‖u‖ - R ≤ ‖u - w‖ := by linarith only [htri']
      simpa [norm_sub_rev] using hu
    have hg1ge0 : ∀ u ∈ S, 0 ≤ g1 u := by
      intro u hu
      by_cases h : ‖u‖ ≤ R / 4
      · have hh : g1 u = M u * (4 / 3 / ‖u‖) := by simp [g1, h]
        rw [hh]
        exact mul_nonneg (hMm u hu) (by
          have hupos : 0 < ‖u‖ := by
            have := hu1 u hu
            linarith only [this]
          positivity)
      · have hh : g1 u = 0 := by simp [g1, h]
        rw [hh]
    have hg2ge0 : ∀ u ∈ S, 0 ≤ g2 u := by
      intro u hu
      by_cases h : ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖
      · have hh : g2 u = M u * (4 / ‖w - u‖) := by simp [g2, h]
        rw [hh]
        exact mul_nonneg (hMm u hu) (by
          have hd : (0 : ℝ) < ‖w - u‖ := by
            have := h.2
            linarith only [this]
          positivity)
      · have hh : g2 u = 0 := by simp [g2, h]
        rw [hh]
    have hg3ge0 : ∀ u ∈ S, 0 ≤ g3 u := by
      intro u hu
      by_cases h : 4 * R < ‖u‖
      · have hh : g3 u = M u * ((4 * R / 3) / ‖u‖ ^ 2) := by simp [g3, h]
        rw [hh]
        exact mul_nonneg (hMm u hu) (by
          have hupos : 0 < ‖u‖ := by
            have := hu1 u hu
            linarith only [this]
          positivity)
      · have hh : g3 u = 0 := by simp [g3, h]
        rw [hh]
    have hterm : ∀ u ∈ S, 1 < ‖w - u‖ →
        M u * (R / (‖u‖ * ‖w - u‖)) ≤ g1 u + g2 u + g3 u := by
      intro u hu hd
      have hM0 : 0 ≤ M u := hMm u hu
      have hdpos : (0 : ℝ) < ‖w - u‖ := by linarith only [hd]
      have hdge1 : 1 ≤ ‖w - u‖ := le_of_lt hd
      have hwgt : R / (‖u‖ * ‖w - u‖) = R / (‖u‖ * ‖w - u‖) := rfl
      by_cases hlow : ‖u‖ ≤ R / 4
      · -- low
        have hg1 : g1 u = M u * (4 / 3 / ‖u‖) := by simp [g1, hlow]
        have hg23 : 0 ≤ g2 u + g3 u := add_nonneg (hg2ge0 u hu) (hg3ge0 u hu)
        have h3R4 : 3 * R / 4 ≤ ‖w - u‖ := by
          calc
            3 * R / 4 ≤ R - ‖u‖ := by linarith only [hlow]
            _ ≤ ‖w - u‖ := by
              calc R - ‖u‖ ≤ ‖w‖ - ‖u‖ := by rw [hw]
                _ ≤ ‖w - u‖ := htri1 u
        have hw := lowWeightBound (R := R) hRpos (hu1 u hu) hlow hdpos h3R4
        calc
          M u * (R / (‖u‖ * ‖w - u‖)) ≤ M u * (4 / 3 / ‖u‖) := mul_le_mul_of_nonneg_left hw hM0
          _ = g1 u := hg1.symm
          _ ≤ g1 u + (g2 u + g3 u) := by linarith only [hg23]
          _ = g1 u + g2 u + g3 u := by abel
      · have hnotlow : ¬ ‖u‖ ≤ R / 4 := hlow
        by_cases hmid : ‖u‖ ≤ 4 * R
        · -- middle
          have hg2 : g2 u = M u * (4 / ‖w - u‖) := by simp [g2, hmid, hd]
          have hg13 : 0 ≤ g1 u + g3 u := add_nonneg (hg1ge0 u hu) (hg3ge0 u hu)
          have hR4le : R / 4 ≤ ‖u‖ := le_of_not_ge hnotlow
          have hw := midWeightBound (R := R) hRpos hdpos hR4le
          calc
            M u * (R / (‖u‖ * ‖w - u‖)) ≤ M u * (4 / ‖w - u‖) := mul_le_mul_of_nonneg_left hw hM0
            _ = g2 u := hg2.symm
            _ ≤ g1 u + g2 u + g3 u := by linarith only [hg13]
        · have hnotmid : ¬ ‖u‖ ≤ 4 * R := hmid
          have hg3 : g3 u = M u * ((4 * R / 3) / ‖u‖ ^ 2) := by
            have hgt : 4 * R < ‖u‖ := lt_of_not_ge hnotmid
            dsimp [g3]
            exact if_pos hgt
          have hg12 : 0 ≤ g1 u + g2 u := add_nonneg (hg1ge0 u hu) (hg2ge0 u hu)
          have h4Rle : 4 * R < ‖u‖ := lt_of_not_ge hnotmid
          have hw := farWeightBound (R := R) hRpos hdpos (le_of_lt h4Rle) (htri2 u)
          calc
            M u * (R / (‖u‖ * ‖w - u‖)) ≤ M u * ((4 * R / 3) / ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hw hM0
            _ = g3 u := hg3.symm
            _ ≤ g1 u + g2 u + g3 u := by linarith only [hg12]
    have hsplit : (∑ u ∈ S.filter (fun u => 1 < ‖w - u‖), M u * (R / (‖u‖ * ‖w - u‖))) ≤
        ∑ u ∈ S, (g1 u + g2 u + g3 u) := by
      calc
        (∑ u ∈ S.filter (fun u => 1 < ‖w - u‖), M u * (R / (‖u‖ * ‖w - u‖)))
            ≤ ∑ u ∈ S.filter (fun u => 1 < ‖w - u‖), (g1 u + g2 u + g3 u) := Finset.sum_le_sum (by
                intro u hu
                exact hterm u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2)
        _ ≤ ∑ u ∈ S, (g1 u + g2 u + g3 u) := Finset.sum_le_sum_of_subset_of_nonneg (by intro u hu; exact (Finset.mem_filter.mp hu).1)
            (by intro u hu hu'; exact add_nonneg (add_nonneg (hg1ge0 u hu) (hg2ge0 u hu)) (hg3ge0 u hu))
    -- match g1+g2+g3 sums to the regime sums
    have hg1sum : (∑ u ∈ S, g1 u) =
        (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) := by
      rw [Finset.sum_filter]
    have hg2sum : (∑ u ∈ S, g2 u) =
        (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) := by
      rw [Finset.sum_filter]
    have hg3sum : (∑ u ∈ S, g3 u) =
        (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) := by
      rw [Finset.sum_filter]
    have hsum_reg : (∑ u ∈ S, (g1 u + g2 u + g3 u)) =
        (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) +
          (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) +
          (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) := by
      rw [← hg1sum, ← hg2sum, ← hg3sum]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- combine with the three regime bounds
    have hB1 : (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) ≤ (64 : ℝ) * C * (A ^ 2 + 1) := by
      simpa [M, A] using hLB
    have hB2 : (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) ≤
        (8192 : ℝ) * C * (A ^ 2 + 1) := by
      simpa [M, A] using hMB
    have hB3 : (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) ≤
        (8192 : ℝ) * C * (A ^ 2 + 1) := by
      simpa [M, A] using hFB
    have htotal : (∑ u ∈ S.filter (fun u => 1 < ‖w - u‖), M u * (R / (‖u‖ * ‖w - u‖))) ≤
        (16448 : ℝ) * C * (A ^ 2 + 1) := by
      calc
        (∑ u ∈ S.filter (fun u => 1 < ‖w - u‖), M u * (R / (‖u‖ * ‖w - u‖))) ≤
            ∑ u ∈ S, (g1 u + g2 u + g3 u) := hsplit
        _ = (∑ u ∈ S.filter (fun u => ‖u‖ ≤ R / 4), M u * (4 / 3 / ‖u‖)) +
              (∑ u ∈ S.filter (fun u => ‖u‖ ≤ 4 * R ∧ 1 < ‖w - u‖), M u * (4 / ‖w - u‖)) +
              (∑ u ∈ S.filter (fun u => 4 * R < ‖u‖), M u * ((4 * R / 3) / ‖u‖ ^ 2)) := hsum_reg
        _ ≤ (64 : ℝ) * C * (A ^ 2 + 1) + (8192 : ℝ) * C * (A ^ 2 + 1) + (8192 : ℝ) * C * (A ^ 2 + 1) := by
          have h1 := hB1
          have h2 := hB2
          have h3 := hB3
          linarith only [h1, h2, h3]
        _ = (16448 : ℝ) * C * (A ^ 2 + 1) := by ring
    have hG : (A ^ 2 + 1) = (Real.log (R + 2) + q + 2) ^ 2 + 1 := by dsimp [A]
    calc
      (∑ u ∈ S.filter (fun u => 1 < ‖w - u‖), M u * (R / (‖u‖ * ‖w - u‖))) ≤
          (16448 : ℝ) * C * (A ^ 2 + 1) := htotal
      _ = (16448 : ℝ) * C * ((Real.log (R + 2) + q + 2) ^ 2 + 1) := by rw [hG]

end Commons.NumberTheory.Linnik