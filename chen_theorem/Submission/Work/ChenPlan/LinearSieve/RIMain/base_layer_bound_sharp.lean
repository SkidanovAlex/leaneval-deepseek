import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.tail_bound
import Submission.Work.ChenPlan.LinearSieve.RI.T_eq_zero_of_le
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile

namespace Work.ChenPlan.LinearSieve.RIMain

open Finset
open scoped BigOperators

set_option autoImplicit false

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

/-- **The `V`-tail bound from the range axiom.**  For `2 ≤ w ≤ z`,
`V(w) - V(z) ≤ V(z)·((log z/log w)(1 + K/log w) - 1)`. -/
lemma VfR_tail_le_range (A : BoundingSieve) {z K w : ℝ} (hK : 0 ≤ K)
    (hlin : Submission.ChenPlan.IsLinearRange A z K) (hw : 2 ≤ w) (hwz : w ≤ z) :
    VfR A w - VfR A z
      ≤ VfR A z * ((Real.log z / Real.log w) * (1 + K / Real.log w) - 1) := by
  have hwpos : 0 < Real.log w := Real.log_pos (by linarith)
  rcases lt_or_eq_of_le hwz with hlt | heq
  · have hdec : VfR A z = VfR A w * ∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - A.nu p) :=
      RI.VfR_eq_VfR_mul_prod A (le_of_lt hlt)
    have hratio : VfR A w / VfR A z
        ≤ (Real.log z / Real.log w) * (1 + K / Real.log w) := by
      have hb := hlin w z hw hlt le_rfl
      have heq2 : VfR A w / VfR A z = ∏ p ∈ A.prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - A.nu p)⁻¹ := by
        rw [hdec, div_mul_eq_div_div, div_self (ne_of_gt (VfR_pos A w)), one_div,
          ← Finset.prod_inv_distrib]
      rw [heq2]; exact hb
    have hkey : VfR A w - VfR A z = VfR A z * (VfR A w / VfR A z - 1) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ (VfR A w) (ne_of_gt (VfR_pos A z))]
    rw [hkey]
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (VfR_pos A z))
  · rw [← heq, sub_self, div_self (ne_of_gt hwpos)]
    have hfin : 0 ≤ VfR A w * (1 * (1 + K / Real.log w) - 1) := by
      have h1 : (1 : ℝ) * (1 + K / Real.log w) - 1 = K / Real.log w := by ring
      rw [h1]
      exact mul_nonneg (VfR_nonneg A w) (div_nonneg hK hwpos.le)
    exact hfin

/-- **Base case of the Rosser–Iwaniec layer bound (sharp slack).**  For a linear sieve problem `A`
whose range-uniform axiom `IsLinearRange A z K` holds with constant `K ≥ 0`, a real level `D ≥ 1`
and sift limit `z ≥ 2` with `s = log D / log z ≥ 1`, the first layer sum
`T_1(D,z) = Σ_{p ∣ P, p < z, p³ > D} ν(p) V(p) = VfR A w - VfR A z` (`w` the least prime of `P`
above `D^{1/3}`; empty sum when `z³ ≤ D`) satisfies
`T_1(D,z) ≤ VfR A z · (profC 0 s + 9 K / (s · log D))`.
The error shape `9K/(s log D)` is the sharp one (`profC 0 s = (3-s)/s` on `[1,3]`, `0` for `s ≥ 3`,
and the sum is empty for `s ≥ 3`); the `K`-term comes from `V(w)/V(z) ≤ (log z/log w)(1+K/log w)`
with `log w ≥ (log D)/3`.-/
theorem base_layer_bound_sharp {A : BoundingSieve} {K D z : ℝ} (hK : 0 ≤ K) (hz : 2 ≤ z)
    (hD : 1 ≤ D) (hlin : Submission.ChenPlan.IsLinearRange A z K)
    (hs : 1 ≤ Real.log D / Real.log z) :
    Work.ChenPlan.LinearSieve.T A 1 D z ≤ Work.ChenPlan.LinearSieve.VfR A z *
      (Work.NumberTheory.Chen.APSwitchUpper.profC 0 (Real.log D / Real.log z)
        + 9 * K / (Real.log D / Real.log z * Real.log D)) := by
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
    exact div_nonneg (mul_nonneg (by norm_num) hK) (le_of_lt (mul_pos hspos hlogDpos))
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
    have hA : Real.log z / Real.log w ≤ 3 / s := by
      rw [div_le_div_iff₀ hLwpos hspos]
      have hLs : Real.log z * s = Real.log D := by rw [hDs]; ring
      rw [hLs]
      exact hLD
    have hB : 1 + K / Real.log w ≤ 1 + 3 * K / Real.log D := by
      have h : K / Real.log w ≤ 3 * K / Real.log D := by
        rw [div_le_div_iff₀ hLwpos hlogDpos]
        nlinarith [hLD, hK]
      linarith
    have hmul : Real.log z / Real.log w * (1 + K / Real.log w)
        ≤ (3 / s) * (1 + 3 * K / Real.log D) := by
      refine mul_le_mul hA hB ?_ ?_
      · have h1 : 0 ≤ K / Real.log w := div_nonneg hK hLwpos.le
        linarith
      · exact div_nonneg (by norm_num) hspos.le
    have hA2 : (3 / s) * (1 + 3 * K / Real.log D)
        = 3 / s + 9 * K / (s * Real.log D) := by
      field_simp
      ring
    have hB2 : (3 : ℝ) / s - 1 = (3 - s) / s := by
      field_simp
    have harith : Real.log z / Real.log w * (1 + K / Real.log w) - 1
        ≤ profC 0 s + 9 * K / (s * Real.log D) := by
      rw [profC_zero, if_pos ⟨hs, le_of_lt hs3⟩]
      linarith [hmul, hA2, hB2]
    calc T A 1 D z ≤ VfR A w - VfR A z := hsum_le
      _ ≤ VfR A z * (Real.log z / Real.log w * (1 + K / Real.log w) - 1) :=
          VfR_tail_le_range A hK hlin hw2 hwz
      _ ≤ VfR A z * (profC 0 s + 9 * K / (s * Real.log D)) :=
          mul_le_mul_of_nonneg_left harith hVz

end

end Work.ChenPlan.LinearSieve.RIMain
