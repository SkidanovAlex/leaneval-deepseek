import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Framework
import Submission.Work.ChenPlan.LinearSieve.SelbergBound
import Submission.Work.ChenPlan.LinearSieve.trivial_case
import Submission.Work.ChenPlan.LinearSieve.trivial_interface
import Submission.Work.ChenPlan.LinearSieve.Selberg.gsum_bound_dense

/-!
# The Selberg pair `(U, 1)` for the linear sieve

`selberg_pair` produces a function `U` which is a valid upper bound for the linear sieve
(`UpperValidAll K U 1`), is at most Selberg's sharp value `2e^γ/s` on the range `s ∈ [1,2]`, and is
`≥ 1` everywhere.

The content is the sharp Selberg/Ankeny–Onishi bound (`gSum A (√D) · Vf A Z ≥ s/(2e^γ) - η`,
delegated), combined with

* Mathlib's `Λ²` upper bound (`selberg_bound`): `S ≤ X / gSum A ξ + remSum A (ξ²)`, used with
  `ξ = √D` so that the remainder is exactly `remSum A D`;
* the trivial `D > prodPrimes` case (`siftedSum_le_trivial`);
* monotonicity of `gSum`, which reduces the range `s ≥ 2` to `s = 2` (the level `Z²` is admissible
  because `D ≥ Z ^ s ≥ Z²`).
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.Selberg

/-- `gSum` is monotone in the level `ξ`. -/
theorem gSum_mono (A : BoundingSieve) {ξ ξ' : ℝ} (h : ξ ≤ ξ') :
    Work.ChenPlan.LinearSieve.gSum A ξ ≤ Work.ChenPlan.LinearSieve.gSum A ξ' := by
  unfold Work.ChenPlan.LinearSieve.gSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, lt_of_lt_of_le hd.2 h⟩
  · intro d hd _
    exact le_of_lt (BoundingSieve.selbergTerms_pos
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1))

/-- The squarefree modulus `prodPrimes` is at most the product of all primes below `Z`, whenever all
its prime factors are below `Z`. -/
theorem prodPrimes_le_prod_primes (A : BoundingSieve) {Z : ℕ}
    (hZ : ∀ p ∈ A.prodPrimes.primeFactors, p < Z) :
    A.prodPrimes ≤ ∏ p ∈ (Finset.range Z).filter Nat.Prime, p := by
  have hprod : ∏ p ∈ A.prodPrimes.primeFactors, p = A.prodPrimes :=
    Nat.prod_primeFactors_of_squarefree A.prodPrimes_squarefree
  rw [← hprod]
  refine Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun p : ℕ => p) ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hZ p hp),
      Nat.prime_of_mem_primeFactors hp⟩
  · intro p _
    exact Nat.zero_le _
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

/-- The upper bound function of the Selberg pair. -/
noncomputable def selbergU (s : ℝ) : ℝ :=
  if s ≤ 2 then 2 * Real.exp Real.eulerMascheroniConstant / s
  else Real.exp Real.eulerMascheroniConstant

/-- `1 < e^γ < 3`. -/
theorem exp_gamma_bounds :
    (1 : ℝ) < Real.exp Real.eulerMascheroniConstant
      ∧ Real.exp Real.eulerMascheroniConstant < 3 := by
  constructor
  · rw [Real.one_lt_exp_iff]
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  · calc Real.exp Real.eulerMascheroniConstant < Real.exp (2 / 3 : ℝ) :=
        Real.exp_lt_exp.mpr Real.eulerMascheroniConstant_lt_two_thirds
      _ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
      _ < 3 := Real.exp_one_lt_three

theorem selbergU_le (s : ℝ) (hs : 1 ≤ s) (hs2 : s ≤ 2) :
    selbergU s ≤ 2 * Real.exp Real.eulerMascheroniConstant / s := by
  unfold selbergU
  rw [if_pos hs2]

theorem one_le_selbergU (s : ℝ) (hs : 1 ≤ s) : 1 ≤ selbergU s := by
  unfold selbergU
  by_cases h : s ≤ 2
  · rw [if_pos h]
    have h2 : (0 : ℝ) < s := by linarith
    rw [le_div_iff₀ h2]
    nlinarith [exp_gamma_bounds.1, hs, h]
  · rw [if_neg h]
    exact le_of_lt exp_gamma_bounds.1

/-- Core estimate for the sharp range `s ∈ [1,2]`. -/
theorem key_sharp (s η : ℝ) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hη : 0 < η) :
    1 ≤ (s / (2 * Real.exp Real.eulerMascheroniConstant) - min η 1 / 10 ^ 9) *
        (2 * Real.exp Real.eulerMascheroniConstant / s + η) := by
  obtain ⟨hE1, hE3⟩ := exp_gamma_bounds
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hs0 : 0 < s := by linarith
  have ha : (1 : ℝ) / 6 ≤ s / (2 * E) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hs1, hE3]
  have hb : 2 * E / s ≤ 6 := by
    rw [div_le_iff₀ hs0]
    nlinarith [hs1, hE3]
  have hkey : (min η 1 / 10 ^ 9) * (6 + η) ≤ η * ((1 : ℝ) / 6) := by
    by_cases h1 : η ≤ 1
    · rw [min_eq_left h1]
      nlinarith [hη, (by norm_num : (7 : ℝ) / 10 ^ 9 ≤ 1 / 6)]
    · push_neg at h1
      rw [min_eq_right h1.le]
      nlinarith [h1, (by norm_num : (1 : ℝ) / 10 ^ 9 ≤ 1 / 6)]
  have hstep : (min η 1 / 10 ^ 9) * (2 * E / s + η) ≤ η * (s / (2 * E)) := by
    have h1 : (min η 1 / 10 ^ 9) * (2 * E / s + η) ≤ (min η 1 / 10 ^ 9) * (6 + η) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : η * ((1 : ℝ) / 6) ≤ η * (s / (2 * E)) := mul_le_mul_of_nonneg_left ha hη.le
    linarith
  have hexp : (s / (2 * E) - min η 1 / 10 ^ 9) * (2 * E / s + η)
      = 1 + (η * (s / (2 * E)) - (min η 1 / 10 ^ 9) * (2 * E / s + η)) := by
    field_simp
    ring
  linarith [hstep, hexp]

/-- Core estimate for the range `s ≥ 2`, where `U` has been raised to the constant `e^γ`. -/
theorem key_beyond (η : ℝ) (hη : 0 < η) :
    1 ≤ ((Real.exp Real.eulerMascheroniConstant)⁻¹ - min η 1 / 10 ^ 9) *
        (Real.exp Real.eulerMascheroniConstant + η) := by
  obtain ⟨hE1, hE3⟩ := exp_gamma_bounds
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hinv : E⁻¹ * E = 1 := inv_mul_cancel₀ (ne_of_gt hE0)
  have hEinv : (1 : ℝ) / 3 ≤ E⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hE0 hE3.le
  have hkey : (min η 1 / 10 ^ 9) * (E + η) ≤ η * E⁻¹ := by
    by_cases h1 : η ≤ 1
    · rw [min_eq_left h1]
      have h2 : (η / 10 ^ 9) * (E + η) ≤ (η / 10 ^ 9) * 4 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h3 : η * ((1 : ℝ) / 3) ≤ η * E⁻¹ := mul_le_mul_of_nonneg_left hEinv hη.le
      nlinarith [h2, h3, hη, h1]
    · push_neg at h1
      rw [min_eq_right h1.le]
      have h2 : (1 / 10 ^ 9) * (E + η) ≤ (1 / 10 ^ 9) * (3 + η) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h3 : η * ((1 : ℝ) / 3) ≤ η * E⁻¹ := mul_le_mul_of_nonneg_left hEinv hη.le
      nlinarith [h2, h3, h1]
  have hexp : (E⁻¹ - min η 1 / 10 ^ 9) * (E + η)
      = 1 + (η * E⁻¹ - (min η 1 / 10 ^ 9) * (E + η)) := by
    field_simp
    ring
  linarith [hkey, hexp]


theorem upperValidAll_selbergU (K : ℝ) (hK : 0 ≤ K) :
    Work.ChenPlan.LinearSieve.UpperValidAll K selbergU 1 := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := gsum_bound_dense K hK (min η 1 / 10 ^ 9) (by positivity)
  set D₁ : ℝ := max D₀ 0 with hD₁
  have hD₁nn : 0 ≤ D₁ := le_max_right _ _
  set B : ℕ := ∏ p ∈ (Finset.range (⌊Real.sqrt D₁⌋₊ + 1)).filter Nat.Prime, p with hB
  refine ⟨max D₁ ((B : ℝ) + 1), ?_⟩
  intro A Z D hZ hD hlin hX hs
  obtain ⟨hprimes, hprod⟩ := hlin
  have hD_D1 : D₁ ≤ D := le_trans (le_max_left _ _) hD
  have hD_B : (B : ℝ) + 1 ≤ D := le_trans (le_max_right _ _) hD
  have hD_D0 : D₀ ≤ D := le_trans (le_max_left _ _) hD_D1
  have hZ2 : (2 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hlogD0 : 0 < Real.log D := by
    have h := (le_div_iff₀ hlogZ).mp hs
    linarith
  have hDge1 : (1 : ℝ) ≤ D := by
    have : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    linarith
  have hD1lt : (1 : ℝ) < D := by
    rcases lt_or_eq_of_le hDge1 with h | h
    · exact h
    · exfalso
      rw [← h, Real.log_one] at hlogD0
      exact lt_irrefl _ hlogD0
  have hDnn : (0 : ℝ) ≤ D := by linarith
  have hVpos : 0 < Submission.ChenPlan.sieveV A := Work.ChenPlan.LinearSieve.sieveV_pos A
  have hVnn : 0 ≤ Submission.ChenPlan.sieveV A := hVpos.le
  have hVf : Work.ChenPlan.LinearSieve.Vf A Z = Submission.ChenPlan.sieveV A :=
    Work.ChenPlan.LinearSieve.Vf_eq_sieveV A hprimes
  rw [Work.ChenPlan.LinearSieve.siftedSumLt_eq_siftedSum A hprimes, hVf]
  by_cases hs2 : Real.log D / Real.log Z ≤ 2
  · -- ================= sharp range `s ≤ 2` =================
    have hb := hD₀ A Z D hZ hD_D0 ⟨hprimes, hprod⟩ hs hs2
    have hsqrt1 : 1 < Real.sqrt D := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      simpa using hD1lt
    have hGpos : 0 < Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) :=
      Work.ChenPlan.LinearSieve.gSum_pos A hsqrt1
    have hsel := Work.ChenPlan.LinearSieve.selberg_bound A hsqrt1 hX
    rw [Real.sq_sqrt hDnn] at hsel
    have hUval : selbergU (Real.log D / Real.log Z) =
        2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) := by
      unfold selbergU
      rw [if_pos hs2]
    have hnum := key_sharp (Real.log D / Real.log Z) η hs hs2 hη
    have hkey : 1 ≤ Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) *
        Work.ChenPlan.LinearSieve.Vf A Z * (selbergU (Real.log D / Real.log Z) + η) := by
      rw [hUval]
      have hnonneg : (0 : ℝ) ≤
          2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) + η := by
        positivity
      have h := mul_le_mul_of_nonneg_right hb hnonneg
      linarith
    have hmain : A.totalMass / Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) ≤
        A.totalMass * Submission.ChenPlan.sieveV A *
          (selbergU (Real.log D / Real.log Z) + η) := by
      rw [div_le_iff₀ hGpos]
      calc A.totalMass = A.totalMass * 1 := (mul_one _).symm
        _ ≤ A.totalMass * (Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) *
              Work.ChenPlan.LinearSieve.Vf A Z *
              (selbergU (Real.log D / Real.log Z) + η)) :=
            mul_le_mul_of_nonneg_left hkey hX
        _ = A.totalMass * Submission.ChenPlan.sieveV A *
              (selbergU (Real.log D / Real.log Z) + η) *
              Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) := by
            rw [hVf]; ring
    linarith
  · -- ================= range `s ≥ 2` =================
    push_neg at hs2
    by_cases hDP : (A.prodPrimes : ℝ) < D
    · have htr := Work.ChenPlan.LinearSieve.siftedSum_le_trivial A hDP
      have h1 : (1 : ℝ) ≤ selbergU (Real.log D / Real.log Z) + η := by
        have := one_le_selbergU (Real.log D / Real.log Z) hs
        linarith
      have h0 : 0 ≤ A.totalMass * Submission.ChenPlan.sieveV A := mul_nonneg hX hVnn
      have h2 : A.totalMass * Submission.ChenPlan.sieveV A ≤
          A.totalMass * Submission.ChenPlan.sieveV A *
            (selbergU (Real.log D / Real.log Z) + η) := by nlinarith [h0, h1]
      linarith
    · push_neg at hDP
      -- the level `Z²` is at least `D₀`, so the sharp bound applies at `s = 2`
      have hZsqD0 : D₁ ≤ (Z : ℝ) ^ 2 := by
        by_contra hcon
        push_neg at hcon
        have hsqrt : (Z : ℝ) < Real.sqrt D₁ := by
          by_contra hc
          push_neg at hc
          have hle : (Real.sqrt D₁) ^ 2 ≤ (Z : ℝ) ^ 2 := by
            simpa [pow_two] using mul_self_le_mul_self (Real.sqrt_nonneg D₁) hc
          rw [Real.sq_sqrt hD₁nn] at hle
          linarith
        have hsub : A.prodPrimes ≤ B := by
          refine prodPrimes_le_prod_primes A (Z := ⌊Real.sqrt D₁⌋₊ + 1) ?_
          intro p hp
          have hpZ : p < Z := hprimes p hp
          have hp' : (p : ℝ) < Real.sqrt D₁ := by
            have h : (p : ℝ) < (Z : ℝ) := by exact_mod_cast hpZ
            linarith
          have h2 : p ≤ ⌊Real.sqrt D₁⌋₊ := Nat.le_floor hp'.le
          omega
        have hDB : (D : ℝ) ≤ (B : ℝ) := by
          have hpB : (A.prodPrimes : ℝ) ≤ (B : ℝ) := by exact_mod_cast hsub
          linarith
        linarith [hD_B]
      have hZpos : (0 : ℝ) < Z := by linarith
      have hlogZsq : Real.log ((Z : ℝ) ^ 2) / Real.log Z = 2 := by
        rw [Real.log_pow]
        norm_num
        field_simp
      have hb := hD₀ A Z ((Z : ℝ) ^ 2) hZ (le_trans (le_max_left D₀ 0) hZsqD0) ⟨hprimes, hprod⟩
        (by rw [hlogZsq]; norm_num) (by rw [hlogZsq])
      rw [Real.sqrt_sq hZpos.le, hlogZsq] at hb
      have hb' : Real.exp (-Real.eulerMascheroniConstant) - min η 1 / 10 ^ 9 ≤
          Work.ChenPlan.LinearSieve.gSum A Z * Work.ChenPlan.LinearSieve.Vf A Z := by
        have h2 : (2 : ℝ) / (2 * Real.exp Real.eulerMascheroniConstant) =
            Real.exp (-Real.eulerMascheroniConstant) := by
          rw [Real.exp_neg]
          field_simp
        linarith [hb, h2]
      have hZsqrt : (Z : ℝ) ≤ Real.sqrt D := by
        rw [Real.le_sqrt (by linarith : (0 : ℝ) ≤ Z) hDnn]
        have hlog2 : 2 * Real.log Z < Real.log D := (lt_div_iff₀ hlogZ).mp hs2
        have h1 : Real.log ((Z : ℝ) ^ 2) < Real.log D := by
          rw [Real.log_pow]
          simpa using hlog2
        exact le_of_lt ((Real.log_lt_log_iff (by positivity) (by linarith)).mp h1)
      have hGV : Real.exp (-Real.eulerMascheroniConstant) - min η 1 / 10 ^ 9 ≤
          Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) *
            Work.ChenPlan.LinearSieve.Vf A Z := by
        have hmono : Work.ChenPlan.LinearSieve.gSum A Z ≤
            Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) := gSum_mono A hZsqrt
        have hVfnn : 0 ≤ Work.ChenPlan.LinearSieve.Vf A Z :=
          (Work.ChenPlan.LinearSieve.Vf_pos A Z).le
        nlinarith [hb', hmono, hVfnn]
      have hsqrt1 : 1 < Real.sqrt D := by
        rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
        simpa using hD1lt
      have hGpos : 0 < Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) :=
        Work.ChenPlan.LinearSieve.gSum_pos A hsqrt1
      have hsel := Work.ChenPlan.LinearSieve.selberg_bound A hsqrt1 hX
      rw [Real.sq_sqrt hDnn] at hsel
      have hUval : selbergU (Real.log D / Real.log Z) =
          Real.exp Real.eulerMascheroniConstant := by
        unfold selbergU
        rw [if_neg (by linarith)]
      have hnum := key_beyond η hη
      rw [Real.exp_neg] at hGV
      have hkey : 1 ≤ Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) *
          Work.ChenPlan.LinearSieve.Vf A Z * (selbergU (Real.log D / Real.log Z) + η) := by
        rw [hUval]
        have hnonneg : (0 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant + η := by positivity
        have h := mul_le_mul_of_nonneg_right hGV hnonneg
        linarith
      have hmain : A.totalMass / Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) ≤
          A.totalMass * Submission.ChenPlan.sieveV A *
            (selbergU (Real.log D / Real.log Z) + η) := by
        rw [div_le_iff₀ hGpos]
        calc A.totalMass = A.totalMass * 1 := (mul_one _).symm
          _ ≤ A.totalMass * (Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) *
                Work.ChenPlan.LinearSieve.Vf A Z *
                (selbergU (Real.log D / Real.log Z) + η)) :=
              mul_le_mul_of_nonneg_left hkey hX
          _ = A.totalMass * Submission.ChenPlan.sieveV A *
                (selbergU (Real.log D / Real.log Z) + η) *
                Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) := by
              rw [hVf]; ring
      linarith

theorem selberg_pair (K : ℝ) (hK : 0 ≤ K) :
    ∃ U : ℝ → ℝ,
      Work.ChenPlan.LinearSieve.UpperValidAll K U 1
      ∧ (∀ s : ℝ, 1 ≤ s → s ≤ 2 → U s ≤ 2 * Real.exp Real.eulerMascheroniConstant / s)
      ∧ (∀ s : ℝ, 1 ≤ s → 1 ≤ U s) :=
  ⟨selbergU, upperValidAll_selbergU K hK, selbergU_le, one_le_selbergU⟩

end Work.ChenPlan.LinearSieve.Selberg
