import ChallengeDeps
import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_large_values
import Submission.Commons.NumberTheory.DirichletPolynomial.large_values_halasz_huxley
import Submission.LargeValues.PowerComparisons

open LargeValueEstimates
open Asymptotics Complex
set_option autoImplicit false

/-!
# Unconditional reduction of Guth–Maynard Theorem 1.1 outside the middle regime

Combining the two classical inputs, both now in the shared commons,
 * (A) `Commons.NumberTheory.DirichletPolynomial.mv_large_values`:
       `R ≤ C·(N²V⁻² + T·N·V⁻²)`,
 * (B) `Commons.NumberTheory.DirichletPolynomial.large_values_halasz_huxley`:
       `R ≤ C·(N²V⁻² + T·N⁴V⁻⁶)` for `V ≥ N^{3/4}`,
with the real-power comparison lemmas of `Submission.LargeValues.PowerComparisons`,
we prove the pointwise target bound
`R ≤ C·bound N V T` in the three regimes
 * `T ≤ N` (Case 1),
 * `V ≤ 3·N^{7/10}` (Case 2),
 * `V ≥ N^{4/5}` (Case 3).
The remaining middle regime `N < T`, `3·N^{7/10} < V < N^{4/5}` is the genuinely new
part of the paper (KeyProp, Sections 4–11) and is handled elsewhere.
-/

namespace Submission.LargeValues

/-- The two classical large-value bounds (A) and (B) imply the pointwise target bound
in the three classical regimes. -/
theorem pointwise_bound_cases123 :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (N : ℕ) (V T : ℝ) (R : ℕ) (t : Fin R → ℝ),
        N > 0 → V > 0 → T > 1 →
        (∀ i j, i ≠ j → |t i - t j| ≥ 1) → (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ r, ‖∑ n ∈ Finset.Icc N (2 * N), b n * n ^ (I * t r)‖ ≥ V) →
        ((T ≤ (N : ℝ)) ∨ V ≤ 3 * (N : ℝ) ^ (7 / 10 : ℝ)
          ∨ (N : ℝ) ^ (4 / 5 : ℝ) ≤ V) →
        (R : ℝ) ≤ C * bound N V T := by
  obtain ⟨CA, hCA0, hA⟩ := Commons.NumberTheory.DirichletPolynomial.mv_large_values
  obtain ⟨CB, hCB0, hB⟩ :=
    Commons.NumberTheory.DirichletPolynomial.large_values_halasz_huxley
  set CC : ℝ := max (max (CA * 4) (CA * 20)) (2 * CB) + 1 with hCC
  have hCCpos : 0 < CC := by rw [hCC]; positivity
  refine ⟨CC, hCCpos, ?_⟩
  intro b hb N V T R t hN hV hT hsep hIcc hD hcase
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hVinv : 0 ≤ V ^ (-2 : ℤ) := by positivity
  have hVinv4 : 0 ≤ V ^ (-4 : ℤ) := by positivity
  have hb1 : (N : ℝ) ^ 2 * V ^ (-2 : ℤ) ≤ bound N V T := by
    unfold bound
    nlinarith [show (0:ℝ) ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) by positivity,
      show (0:ℝ) ≤ T * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) by positivity]
  have hb3 : T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ)) ≤ bound N V T := by
    unfold bound
    nlinarith [show (0:ℝ) ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) by positivity,
      show (0:ℝ) ≤ (N : ℝ) ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) by positivity]
  have hbound_nonneg : 0 ≤ bound N V T := le_trans (by positivity) hb1
  have key : (R : ℝ) ≤ CC * bound N V T := by
    rcases hcase with hcase1 | hcase2 | hcase3
    · -- Case 1: T ≤ N
      have h := hA b hb N V T R t hN hV (by linarith) hsep hIcc hD
      have hNV : T * ((N : ℝ) * V ^ (-2 : ℤ)) ≤ (N : ℝ) ^ 2 * V ^ (-2 : ℤ) := by
        have : T * (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
        calc T * ((N : ℝ) * V ^ (-2 : ℤ)) = (T * (N : ℝ)) * V ^ (-2 : ℤ) := by ring
          _ ≤ ((N : ℝ) ^ 2) * V ^ (-2 : ℤ) := mul_le_mul_of_nonneg_right this hVinv
      have h2 : (R : ℝ) ≤ CA * (2 * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ))) := by nlinarith [h, hNV]
      have h3 : CA * (2 * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ))) ≤ CA * (2 * bound N V T) :=
        mul_le_mul_of_nonneg_left (by linarith [hb1]) (le_of_lt hCA0)
      have h4 : CA * (2 * bound N V T) ≤ CC * bound N V T := by
        have hle : 2 * CA ≤ CC := by
          rw [hCC]
          have h5 : CA * 4 ≤ max (CA * 4) (CA * 20) := le_max_left _ _
          have h6 : max (CA * 4) (CA * 20) ≤ max (max (CA * 4) (CA * 20)) (2 * CB) :=
            le_max_left _ _
          nlinarith [le_trans h5 h6, hCA0]
        nlinarith [hbound_nonneg, hle]
      linarith [h2, h3, h4]
    · -- Case 2: V ≤ 3 N^{7/10}
      have h := hA b hb N V T R t hN hV (by linarith) hsep hIcc hD
      have hcomp := N_mul_V_neg_two_le (N : ℝ) V hN1 hV hcase2
      have hcomp' : T * ((N : ℝ) * V ^ (-2 : ℤ))
          ≤ T * (9 * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ))) := by
        have h0 : (0 : ℝ) ≤ T := by linarith
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcomp h0
      have hthird : T * (9 * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ)))
          = 9 * (T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ))) := by ring
      have hsum : (N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))
          ≤ 20 * bound N V T := by
        have h9 : 9 * (T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ))) ≤ 9 * bound N V T :=
          mul_le_mul_of_nonneg_left hb3 (by norm_num)
        have hchain : T * ((N : ℝ) * V ^ (-2 : ℤ)) ≤ 9 * bound N V T := by
          rw [hthird] at hcomp'
          exact le_trans hcomp' h9
        have := add_le_add hb1 hchain
        linarith
      have h2 : (R : ℝ) ≤ CA * (20 * bound N V T) := by
        calc (R : ℝ) ≤ CA * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))) := h
          _ ≤ CA * (20 * bound N V T) := mul_le_mul_of_nonneg_left hsum (le_of_lt hCA0)
      have h4 : CA * (20 * bound N V T) ≤ CC * bound N V T := by
        have hle : 20 * CA ≤ CC := by
          rw [hCC]
          have h5 : CA * 20 ≤ max (CA * 4) (CA * 20) := le_max_right _ _
          have h6 : max (CA * 4) (CA * 20) ≤ max (max (CA * 4) (CA * 20)) (2 * CB) :=
            le_max_left _ _
          nlinarith [le_trans h5 h6]
        nlinarith [hbound_nonneg, hle]
      linarith [h2, h4]
    · -- Case 3: V ≥ N^{4/5} ≥ N^{3/4}
      have hV34 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ V := by
        have h1 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        linarith
      have h := hB N V T R t b hN hV (by linarith) hb hV34 hIcc hsep hD
      have h : (R : ℝ) ≤ CB * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) ^ 4 * V ^ (-6 : ℤ))) := by
        rw [show T * (N : ℝ) ^ 4 * V ^ (-6 : ℤ) = T * ((N : ℝ) ^ 4 * V ^ (-6 : ℤ)) from by ring] at h
        exact h
      have hcomp := pow_four_mul_V_neg_six_le (N : ℝ) V hN1 hV hcase3
      have hcomp' : T * ((N : ℝ) ^ 4 * V ^ (-6 : ℤ))
          ≤ T * ((N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ)) :=
        mul_le_mul_of_nonneg_left hcomp (by linarith)
      have hsum : (N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) ^ 4 * V ^ (-6 : ℤ))
          ≤ 2 * bound N V T := by
        have hchain : T * ((N : ℝ) ^ 4 * V ^ (-6 : ℤ)) ≤ bound N V T := le_trans hcomp' hb3
        have := add_le_add hb1 hchain
        linarith
      have h2 : (R : ℝ) ≤ CB * (2 * bound N V T) := by
        calc (R : ℝ) ≤ CB * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) ^ 4 * V ^ (-6 : ℤ))) := h
          _ ≤ CB * (2 * bound N V T) := mul_le_mul_of_nonneg_left hsum (le_of_lt hCB0)
      have h4 : CB * (2 * bound N V T) ≤ CC * bound N V T := by
        have hle : 2 * CB ≤ CC := by
          rw [hCC]
          have h7 : 2 * CB ≤ max (max (CA * 4) (CA * 20)) (2 * CB) := le_max_right _ _
          linarith [h7]
        have h := mul_le_mul_of_nonneg_right hle hbound_nonneg
        simpa only [mul_assoc, mul_comm, mul_left_comm] using h
      linarith [h2, h4]
  exact key

end Submission.LargeValues
