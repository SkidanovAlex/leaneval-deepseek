import Submission.ZagierHoffmanProof.CarlitzAT

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial
open scoped BigOperators

/-!
# The Anderson–Thakur polynomial in the second block `q < n ≤ 2q - 2`

The Anderson–Thakur polynomial `α_n(t) = Γ_n * c_{n-1}(t)` (Dac §4.2, `CarlitzAT.lean`) is `1`
for `1 ≤ n ≤ q` (`atAlpha_eq_one_of_le`).  For `q < n ≤ 2q - 2` the base-`q` expansion of `n - 1`
has only two digits (`n - 1 = q + (n - 1 - q)`), so both the Carlitz arithmetic `Γ`-function and
the coefficient recursion `c_m = ∑_{j : q^j ≤ m} (γ_j/D_j) c_{m-q^j}` degenerate, and one gets the
explicit formula

  `α_n = (θ^q - θ) + (n - q)·(θ^q - t^q)`     (`q < n ≤ 2q - 2`).

This is the `H_n` (non-trivial `t`-motive) input of Dac §6: the paper's `H_n = α_n` with the two
variables exchanged, and it is exactly the range needed for `theorem_D`, where all entries of a
`𝒯'_w`-tuple (`w ≤ 2q - 2`) are `≤ 2q - 2`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `γ_1(t) = θ^q - t^q`. -/
lemma atGamma_one : atGamma F 1 = (atTheta F) ^ (Nat.card F) - (atT F) ^ (Nat.card F) := by
  rw [atGamma]
  simp

/-- `Γ n = D_1 = θ^q - θ` for `q < n ≤ 2q - 2`. -/
lemma carlitzGamma_second_block {n : ℕ} (hn1 : Nat.card F < n) (hn2 : n ≤ 2 * Nat.card F - 2) :
    carlitzGamma F n = carlitzFact F 1 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hsq : n - 1 < Nat.card F ^ 2 := by
    have h : 2 * Nat.card F ≤ Nat.card F ^ 2 := by nlinarith [hq2]
    omega
  rw [carlitzGamma]
  have hsub : Finset.range 2 ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hprod : (∏ j ∈ Finset.range 2,
        carlitzFact F j ^ ((n - 1) / Nat.card F ^ j % Nat.card F))
      = ∏ j ∈ Finset.range n,
        carlitzFact F j ^ ((n - 1) / Nat.card F ^ j % Nat.card F) := by
    refine Finset.prod_subset hsub (fun x hx hx2 => ?_)
    rw [Finset.mem_range] at hx
    rw [Finset.mem_range] at hx2
    have hx2' : 2 ≤ x := by omega
    have hdiv : (n - 1) / Nat.card F ^ x = 0 := by
      apply Nat.div_eq_of_lt
      have h2 : Nat.card F ^ 2 ≤ Nat.card F ^ x := Nat.pow_le_pow_right (by omega) hx2'
      omega
    rw [hdiv, Nat.zero_mod, pow_zero]
  rw [← hprod, Finset.prod_range_succ, Finset.prod_range_one, carlitzFact_zero, one_pow, one_mul]
  have h1 : ((n - 1) / Nat.card F ^ 1) % Nat.card F = 1 := by
    rw [pow_one,
      Nat.div_eq_of_lt_le (k := 1) (n := Nat.card F) (m := n - 1) (by omega) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, pow_one]

/-- The filter `{j : q^j ≤ m}` for `q ≤ m < q^2` is `{0,1}`. -/
lemma filter_pow_le_eq (m : ℕ) (hm1 : Nat.card F ≤ m) (hm2 : m < Nat.card F ^ 2) :
    (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m) = Finset.range 2 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_range]
    by_contra h
    have hj2 : 2 ≤ j := by omega
    have h2 : Nat.card F ^ 2 ≤ Nat.card F ^ j := Nat.pow_le_pow_right (by omega) hj2
    omega
  · have hsub : Finset.range 2 ⊆ (Finset.range (m + 1)).filter
        (fun j => Nat.card F ^ j ≤ m) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · rw [pow_zero]; omega
      · rw [pow_one]; exact hm1
    exact Finset.card_le_card hsub

/-- ★★ **The Anderson–Thakur coefficients in the second block**:
`c_m = 1 + (m + 1 - q)·(γ_1/D_1)` for `q - 1 ≤ m ≤ 2q - 3`. -/
lemma atCoeff_second_block : ∀ m, Nat.card F - 1 ≤ m → m ≤ 2 * Nat.card F - 3 →
    atCoeff F m = 1 + ((m + 1 - Nat.card F : ℕ) : atQ F)
      * (atGamma F 1 * (atD F 1)⁻¹) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h1 h2
    have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
    rcases lt_or_ge m (Nat.card F) with hm | hm
    · rw [atCoeff_eq_one_of_lt F hm]
      have hzero : m + 1 - Nat.card F = 0 := by omega
      rw [hzero]
      norm_num
    · have hmq2 : m < Nat.card F ^ 2 := by
        have h2q : 2 * Nat.card F ≤ Nat.card F ^ 2 := by nlinarith [hq2]
        have hm2 : m < 2 * Nat.card F := by omega
        exact lt_of_lt_of_le hm2 h2q
      have hm0 : m ≠ 0 := by omega
      rw [atCoeff_succ F hm0, filter_pow_le_eq F m hm hmq2]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have h0 : (atGamma F 0) * (atD F 0)⁻¹ * atCoeff F (m - Nat.card F ^ 0)
          = atCoeff F (m - 1) := by
        simp only [atGamma_zero, Nat.pow_zero, atD, carlitzFact_zero, map_one,
          inv_one, mul_one, one_mul]
      have h1' : (atGamma F 1) * (atD F 1)⁻¹ * atCoeff F (m - Nat.card F ^ 1)
          = atGamma F 1 * (atD F 1)⁻¹ := by
        rw [pow_one, atCoeff_eq_one_of_lt F (by omega), mul_one]
      rw [h0, h1']
      have hIH := ih (m - 1) (by omega) (by omega) (by omega)
      rw [hIH]
      have hnat : (m - 1) + 1 - Nat.card F = m - Nat.card F := by omega
      rw [hnat]
      have hcast : ((m + 1 - Nat.card F : ℕ) : atQ F)
          = ((m - Nat.card F : ℕ) : atQ F) + 1 := by
        rw [show m + 1 - Nat.card F = (m - Nat.card F) + 1 from by omega, Nat.cast_add,
          Nat.cast_one]
      rw [hcast]
      ring

/-- ★★★ **The Anderson–Thakur polynomial in the second block**:
`α_n = (θ^q - θ) + (n - q)·(θ^q - t^q)` for `q < n ≤ 2q - 2`. -/
theorem atAlpha_second_block {n : ℕ} (hn1 : Nat.card F < n) (hn2 : n ≤ 2 * Nat.card F - 2) :
    atAlpha F n = algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (carlitzFact F 1))
      + ((n - Nat.card F : ℕ) : atQ F)
        * ((atTheta F) ^ (Nat.card F) - (atT F) ^ (Nat.card F)) := by
  rw [atAlpha, carlitzGamma_second_block F hn1 hn2]
  have hc := atCoeff_second_block F (n - 1) (by omega) (by omega)
  have hnn : (n - 1) + 1 - Nat.card F = n - Nat.card F := by omega
  rw [hc, hnn, atGamma_one]
  simp only [atD]
  have hD : algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (carlitzFact F 1)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ((F[X])[X]) (atQ F))).mpr
      (Polynomial.C_ne_zero.mpr (carlitzFact_ne_zero F 1))
  field_simp

end ZagierHoffmanPositiveChar
