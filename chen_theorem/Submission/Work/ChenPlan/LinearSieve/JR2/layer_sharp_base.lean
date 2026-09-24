import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.T_eq_zero_of_le
import Submission.Work.ChenPlan.LinearSieve.RI.tail_bound

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper

/-- The primes of the sieve problem are `≥ 2`, so `ν p ≥ 0` there. -/
private lemma nu_nonneg_of_mem (A : BoundingSieve) {p : ℕ}
    (hp : p ∈ A.prodPrimes.primeFactors) : 0 ≤ A.nu p :=
  le_of_lt (A.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.1)

/-- Unfolding of the first Rosser–Iwaniec layer sum. -/
private lemma T_one_eq (A : BoundingSieve) (D z : ℝ) :
    T A 1 D z = ∑ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < z ∧ D < (p : ℝ) ^ 3), A.nu p * VfR A (p : ℝ) := by
  rw [T.eq_2 A D z 0]
  simp only [T.eq_1]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by simpa [Tcond] using h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by simpa [Tcond] using h3⟩

/-- `errH` dominates `e^{-3}` on `[1,3]`. -/
private lemma exp_neg_three_le_errH {s : ℝ} (hs : s ≤ 3) : Real.exp (-3) ≤ errH s := by
  rcases le_or_gt s 2 with h2 | h2
  · rw [errH_of_le_two h2]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [errH_of_between h2 hs]
    exact Real.exp_le_exp.mpr (by linarith)

/-- The numerical input of the base case: `3/s ≤ 2000·errH s` for `1 ≤ s ≤ 3`. -/
private lemma three_div_le_2000_errH {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    3 / s ≤ 2000 * errH s := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hexp3 : Real.exp 3 < 27 := by
    have h : Real.exp 3 = Real.exp 1 ^ 3 := by
      simpa using Real.exp_nat_mul (1 : ℝ) 3
    rw [h]
    have h3 := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
      (show (3 : ℕ) ≠ 0 by norm_num)
    norm_num at h3 ⊢
    exact h3
  have hge : (27 : ℝ)⁻¹ ≤ Real.exp (-3) := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 27) (Real.exp_pos 3)).mpr hexp3.le
  have h27 : 3 ≤ 2000 * Real.exp (-3) := by
    have : (27 : ℝ)⁻¹ = 1 / 27 := by norm_num
    rw [this] at hge
    linarith
  have h1 : 3 / s ≤ 2000 * Real.exp (-3) := by
    rw [div_le_iff₀ hspos]
    nlinarith [h27, hs1]
  exact le_trans h1 (mul_le_mul_of_nonneg_left (exp_neg_three_le_errH hs3) (by norm_num))

/-- **Base case (`n = 1`) of the sharp Rosser–Iwaniec layer bound.**

`T_1(D,z) = Σ_{p ∣ P, p < z, D < p³} ν(p)·VfR(p) = VfR w - VfR z` where `w = max(D^{1/3},2)`
(telescoping via `Work.ChenPlan.LinearSieve.RI.sum_nu_VfR_eq`; the sum is empty when `z³ ≤ D`,
in which case both sides are nonnegative).  `SharpNorm` gives
`VfR w ≤ VfR z·(1+ε)·log z/log w` with `log w ≥ (log D)/3` (hence `log z/log w ≤ 3/s`,
`s = log D/log z`), so `VfR w/VfR z - 1 ≤ (1+ε)·3/s - 1 = (3-s)/s + 3ε/s`, and only `s < 3`
occurs (for `s ≥ 3` the sum is empty and `profC 0 s = 0`).  Finally `3ε/s ≤ 2000·ε·errH s`
because `s ≥ 1` and `errH s ≥ e^{-3}` for `s ≤ 3`, with `3 ≤ 2000·e^{-3}·s`.

A ready-made blueprint is the *proved* lemma
`Work.ChenPlan.LinearSieve.RIMain.base_layer_bound_sharp` (same proof, with
`IsLinearRange A z K` replaced by `SharpNorm A z ε` and the error `9K/(s log D)` by
`2000 ε errH s`). -/
theorem layer_sharp_base :
    ∀ {A : BoundingSieve} {ε D z : ℝ}, 0 ≤ ε → ε ≤ 1/100 → 2 ≤ z → 1 ≤ D →
      Work.ChenPlan.LinearSieve.JR2.SharpNorm A z ε →
      1 ≤ Real.log D / Real.log z →
      Work.ChenPlan.LinearSieve.T A 1 D z
        ≤ Work.ChenPlan.LinearSieve.VfR A z *
          (Work.NumberTheory.Chen.APSwitchUpper.profC 0 (Real.log D / Real.log z)
            + ε * 2000 * Work.NumberTheory.Chen.APSwitchUpper.errH (Real.log D / Real.log z)) := by
  intro A ε D z hε0 _hε1 hz hD hnorm hs
  set s : ℝ := Real.log D / Real.log z with hsdef
  have hzpos : 0 < Real.log z := Real.log_pos (by linarith)
  have hDpos : 0 < D := by linarith
  have hlogDpos : 0 < Real.log D := by
    have h : Real.log z ≤ Real.log D := by
      have h' := (le_div_iff₀ hzpos).mp hs
      simpa using h'
    exact lt_of_lt_of_le hzpos h
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hDs : Real.log D = s * Real.log z := by rw [hsdef]; field_simp
  have hVz : 0 ≤ VfR A z := VfR_nonneg A z
  by_cases hcase : z ^ 3 ≤ D
  · have hT0 : T A 1 D z = 0 := by
      refine RI.T_eq_zero_of_le (A := A) (D := D) (z := z) (n := 1) le_rfl ?_
      simpa using hcase
    rw [hT0]
    refine mul_nonneg hVz (add_nonneg (profC_nonneg 0 s) ?_)
    exact mul_nonneg (mul_nonneg hε0 (by norm_num)) (errH_nonneg s)
  · have hDlt : D < z ^ 3 := not_le.mp hcase
    have hs3 : s < 3 := by
      rw [hsdef, div_lt_iff₀ hzpos]
      have h' : Real.log D < Real.log (z ^ 3) := Real.log_lt_log hDpos hDlt
      rwa [Real.log_pow] at h'
    set y : ℝ := D ^ (1 / 3 : ℝ) with hydef
    set w : ℝ := max y 2 with hwdef
    have hypos : 0 < y := by rw [hydef]; exact Real.rpow_pos_of_pos hDpos _
    have hy3 : y ^ 3 = D := by
      rw [hydef, ← Real.rpow_natCast (D ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hDpos.le,
        show (1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have hyz : y ≤ z := by
      have h : y ^ 3 < z ^ 3 := by rw [hy3]; exact hDlt
      exact le_of_lt ((pow_lt_pow_iff_left₀ hypos.le (by linarith : (0 : ℝ) ≤ z)
        (by norm_num : (3 : ℕ) ≠ 0)).mp h)
    have hw2 : 2 ≤ w := by rw [hwdef]; exact le_max_right _ _
    have hwz : w ≤ z := by rw [hwdef]; exact max_le hyz hz
    have hsub : (A.prodPrimes.primeFactors.filter
          (fun p : ℕ => (p : ℝ) < z ∧ D < (p : ℝ) ^ 3))
        ⊆ (A.prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hpmem, hpz, hp3⟩ := hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hpmem)
      have hppos : (0 : ℝ) ≤ (p : ℝ) := by positivity
      have hp3r : ((p : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (p : ℝ) := by
        rw [← Real.rpow_natCast (p : ℝ) 3, ← Real.rpow_mul hppos,
          show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one]
      have hlt' : D ^ (1 / 3 : ℝ) < (p : ℝ) := by
        have h := Real.rpow_lt_rpow hDpos.le hp3 (show (0 : ℝ) < 1 / 3 by norm_num)
        rwa [hp3r] at h
      have hpy : y ≤ (p : ℝ) := by rw [hydef]; exact le_of_lt hlt'
      exact ⟨hpmem, max_le hpy hp2, hpz⟩
    have hsum_le : T A 1 D z ≤ VfR A w - VfR A z := by
      rw [T_one_eq, ← RI.sum_nu_VfR_eq A hwz]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p hp _
      exact mul_nonneg (nu_nonneg_of_mem A (Finset.mem_filter.mp hp).1) (VfR_nonneg A _)
    have hLD : Real.log D ≤ 3 * Real.log w := by
      rcases le_or_gt 2 y with hy2 | hy2
      · have hwy : w = y := by rw [hwdef]; exact max_eq_left hy2
        rw [hwy, hydef, Real.log_rpow hDpos]
        linarith
      · have hwy : w = 2 := by rw [hwdef]; exact max_eq_right (le_of_lt hy2)
        have hy3lt : y ^ 3 < (2 : ℝ) ^ 3 :=
          pow_lt_pow_left₀ hy2 hypos.le (by norm_num)
        have hDlt8 : D < 8 := by
          rw [hy3] at hy3lt
          norm_num at hy3lt
          exact hy3lt
        have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          norm_num
        have h := Real.log_lt_log hDpos hDlt8
        rw [hlog8] at h
        rw [hwy]; exact le_of_lt h
    have hLwpos : 0 < Real.log w := by linarith
    -- the sharp product comparison
    have hVW : VfR A w ≤ VfR A z * ((1 + ε) * (Real.log z / Real.log w)) :=
      VfR_le_of_sharpNorm hε0 hnorm hw2 hwz le_rfl
    have h2 : VfR A w - VfR A z
        ≤ VfR A z * ((1 + ε) * (Real.log z / Real.log w) - 1) := by
      have h := sub_le_sub_right hVW (VfR A z)
      have hrw : VfR A z * ((1 + ε) * (Real.log z / Real.log w)) - VfR A z
          = VfR A z * ((1 + ε) * (Real.log z / Real.log w) - 1) := by ring
      linarith [h, hrw]
    have hA : Real.log z / Real.log w ≤ 3 / s := by
      rw [div_le_div_iff₀ hLwpos hspos]
      have hLs : Real.log z * s = Real.log D := by rw [hDs]; ring
      rw [hLs]
      exact hLD
    have hthree : 3 / s ≤ 2000 * errH s :=
      three_div_le_2000_errH (by rw [hsdef]; exact hs) (le_of_lt hs3)
    have hεthree : ε * (3 / s) ≤ ε * (2000 * errH s) :=
      mul_le_mul_of_nonneg_left hthree hε0
    have harith : (1 + ε) * (Real.log z / Real.log w) - 1
        ≤ profC 0 s + ε * 2000 * errH s := by
      have hmul : (1 + ε) * (Real.log z / Real.log w) ≤ (1 + ε) * (3 / s) :=
        mul_le_mul_of_nonneg_left hA (by linarith)
      have hexp : (1 + ε) * (3 / s) = 3 / s + ε * (3 / s) := by ring
      have hprof : profC 0 s = (3 - s) / s := by
        rw [profC_zero, if_pos ⟨by rw [hsdef]; exact hs, le_of_lt hs3⟩]
      have hfrac : (3 - s) / s = 3 / s - 1 := by
        field_simp
      rw [hprof, hfrac]
      linarith [hmul, hexp, hεthree]
    calc T A 1 D z ≤ VfR A w - VfR A z := hsum_le
      _ ≤ VfR A z * ((1 + ε) * (Real.log z / Real.log w) - 1) := h2
      _ ≤ VfR A z * (profC 0 s + ε * 2000 * errH s) :=
          mul_le_mul_of_nonneg_left harith hVz

end

end Work.ChenPlan.LinearSieve.JR2
