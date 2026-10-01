import Mathlib
import Submission.Work.LinnikAreas.TwMass.invAddSqNatSumLe

namespace Work.LinnikAreas.TwMass

/-- Splitting a `ℤ`-indexed sum at the integer `k` into the two rays `k, k+1, k+2, …` and
`k-1, k-2, …`. -/
private theorem tsum_int_eq_nat_shift (f : ℤ → ℝ) (k : ℤ)
    (h₁ : Summable (fun j : ℕ => f (k + (j : ℤ))))
    (h₂ : Summable (fun j : ℕ => f (k - ((j : ℤ) + 1)))) :
    Summable f ∧
      (∑' n : ℤ, f n)
        = (∑' j : ℕ, f (k + (j : ℤ))) + (∑' j : ℕ, f (k - ((j : ℤ) + 1))) := by
  have h₁' : Summable (fun j : ℕ => (fun m : ℤ => f (m + k)) (j : ℤ)) := by
    refine h₁.congr (fun j => ?_)
    simp only
    congr 1
    ring
  have h₂' : Summable (fun j : ℕ => (fun m : ℤ => f (m + k)) (-((j : ℤ) + 1))) := by
    refine h₂.congr (fun j => ?_)
    simp only
    congr 1
    ring
  have hsum : Summable (fun m : ℤ => f (m + k)) := Summable.of_nat_of_neg_add_one h₁' h₂'
  have htsum : (∑' m : ℤ, f (m + k))
      = (∑' j : ℕ, f ((j : ℤ) + k)) + ∑' j : ℕ, f (-((j : ℤ) + 1) + k) :=
    tsum_of_nat_of_neg_add_one h₁' h₂'
  have htrans : (∑' m : ℤ, f (m + k)) = ∑' n : ℤ, f n := Equiv.tsum_eq (Equiv.addRight k) f
  refine ⟨?_, ?_⟩
  · exact (Equiv.summable_iff (Equiv.addRight k)).mp hsum
  · rw [← htrans, htsum]
    congr 1
    · exact tsum_congr (fun j => by congr 1; ring)
    · exact tsum_congr (fun j => by congr 1; ring)

/-- The lattice sum `∑_{n ∈ ℤ} 1/(A + (t - n h)²)` is bounded by `C (1/A + 1/(h √A))`
uniformly in the shift `t`. -/
theorem latticeInvSqSumLe : ∃ C : ℝ, 0 < C ∧
    ∀ (A t h : ℝ), 0 < A → 0 < h →
      Summable (fun n : ℤ => (1 : ℝ) / (A + (t - (n : ℝ) * h) ^ 2)) ∧
      (∑' n : ℤ, (1 : ℝ) / (A + (t - (n : ℝ) * h) ^ 2)) ≤ C * (1 / A + 1 / (h * Real.sqrt A)) := by
  refine ⟨7, by norm_num, ?_⟩
  intro A t h hA hh
  -- analytic input: the `ℕ`-sum over the multiples of `h`
  obtain ⟨hsumU0, hUle0⟩ := invAddSqNatSumLe A h hA hh
  set f : ℤ → ℝ := fun n => (1 : ℝ) / (A + (t - (n : ℝ) * h) ^ 2) with hf
  set u : ℕ → ℝ := fun j => (1 : ℝ) / (A + ((j : ℝ) * h) ^ 2) with hu
  have hsumU : Summable u := by rw [hu]; exact hsumU0
  have hUle : (∑' j : ℕ, u j) ≤ 3 * (1 / A + 1 / (h * Real.sqrt A)) := by
    rw [hu]; exact hUle0
  -- centre the lattice at the nearest multiple of `h` below `t`
  set k : ℤ := ⌊t / h⌋ with hk
  have hk_le : (k : ℝ) * h ≤ t := by
    rw [hk]
    have h2 : (((⌊t / h⌋ : ℤ)) : ℝ) ≤ t / h := Int.floor_le (t / h)
    have h3 : (((⌊t / h⌋ : ℤ)) : ℝ) * h ≤ (t / h) * h :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hh)
    have h4 : (t / h) * h = t := by field_simp
    linarith
  have hk_lt : t < (k : ℝ) * h + h := by
    rw [hk]
    have h2 : t / h < (((⌊t / h⌋ : ℤ)) : ℝ) + 1 := Int.lt_floor_add_one (t / h)
    have h3 : (t / h) * h < ((((⌊t / h⌋ : ℤ)) : ℝ) + 1) * h :=
      mul_lt_mul_of_pos_right h2 hh
    have h4 : (t / h) * h = t := by field_simp
    nlinarith
  have hfnn : ∀ n : ℤ, 0 ≤ f n := by
    intro n
    rw [hf]
    exact div_nonneg zero_le_one (by have := sq_nonneg (t - (n : ℝ) * h); linarith)
  -- the right ray `k, k+1, k+2, …` is dominated by `u`
  have hbound1s : ∀ j : ℕ, f (k + (((j + 1 : ℕ)) : ℤ)) ≤ u j := by
    intro j
    simp only [hf, hu]
    have hcast : (((k + ((j + 1 : ℕ) : ℤ)) : ℤ) : ℝ) = (k : ℝ) + ((j : ℝ) + 1) := by
      push_cast; ring
    rw [hcast]
    refine one_div_le_one_div_of_le (show (0 : ℝ) < A + ((j : ℝ) * h) ^ 2 by
      have := sq_nonneg ((j : ℝ) * h); linarith) ?_
    have hkey : ((j : ℝ) * h) ^ 2 ≤ (t - ((k : ℝ) + ((j : ℝ) + 1)) * h) ^ 2 := by
      have hle : (j : ℝ) * h ≤ - (t - ((k : ℝ) + ((j : ℝ) + 1)) * h) := by nlinarith [hk_lt]
      have hnn : (0 : ℝ) ≤ (j : ℝ) * h := by positivity
      have h1 := pow_le_pow_left₀ hnn hle 2
      have h2 : (-(t - ((k : ℝ) + ((j : ℝ) + 1)) * h)) ^ 2
          = (t - ((k : ℝ) + ((j : ℝ) + 1)) * h) ^ 2 := by ring
      rw [h2] at h1
      linarith
    linarith
  -- the left ray `k-1, k-2, …` is dominated by the shifted `u`
  have hbound2 : ∀ j : ℕ, f (k - ((j : ℤ) + 1)) ≤ u (j + 1) := by
    intro j
    simp only [hf, hu]
    have hcast : (((k - ((j : ℤ) + 1)) : ℤ) : ℝ) = (k : ℝ) - ((j : ℝ) + 1) := by
      push_cast; ring
    rw [hcast]
    have hcast2 : ((((j + 1 : ℕ)) : ℝ)) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast2]
    refine one_div_le_one_div_of_le (show (0 : ℝ) < A + (((j : ℝ) + 1) * h) ^ 2 by
      have := sq_nonneg (((j : ℝ) + 1) * h); linarith) ?_
    have hkey : (((j : ℝ) + 1) * h) ^ 2 ≤ (t - ((k : ℝ) - ((j : ℝ) + 1)) * h) ^ 2 := by
      have hle : ((j : ℝ) + 1) * h ≤ t - ((k : ℝ) - ((j : ℝ) + 1)) * h := by
        nlinarith [hk_le]
      have hnn : (0 : ℝ) ≤ ((j : ℝ) + 1) * h := by positivity
      exact pow_le_pow_left₀ hnn hle 2
    linarith
  have hsumUw : Summable (fun j : ℕ => u (j + 1)) := (summable_nat_add_iff 1).mpr hsumU
  have hsumRay1s : Summable (fun j : ℕ => f (k + (((j + 1 : ℕ)) : ℤ))) :=
    Summable.of_nonneg_of_le (fun j => hfnn (k + (((j + 1 : ℕ)) : ℤ)))
      (fun j => hbound1s j) hsumU
  have hsumRay2 : Summable (fun j : ℕ => f (k - ((j : ℤ) + 1))) :=
    Summable.of_nonneg_of_le (fun j => hfnn (k - ((j : ℤ) + 1)))
      (fun j => hbound2 j) hsumUw
  have hsumRay1 : Summable (fun j : ℕ => f (k + (j : ℤ))) := by
    apply (summable_nat_add_iff 1).mp
    exact hsumRay1s
  -- split the `ℤ`-sum into the two rays
  obtain ⟨hsumF, htsumF⟩ := tsum_int_eq_nat_shift f k hsumRay1 hsumRay2
  refine ⟨hsumF, ?_⟩
  have hray1le : (∑' j : ℕ, f (k + (j : ℤ))) ≤ 1 / A + ∑' j : ℕ, u j := by
    have hshiftle : (∑' n : ℕ, f (k + (((n + 1 : ℕ)) : ℤ))) ≤ ∑' n : ℕ, u n :=
      Summable.tsum_le_tsum (fun n => hbound1s n) hsumRay1s hsumU
    have hk0 : f (k + (((0 : ℕ)) : ℤ)) ≤ 1 / A := by
      simp only [Nat.cast_zero, add_zero]
      rw [hf]
      refine one_div_le_one_div_of_le hA ?_
      have := sq_nonneg (t - (k : ℝ) * h)
      linarith
    calc (∑' j : ℕ, f (k + (j : ℤ)))
        = f (k + (((0 : ℕ)) : ℤ)) + ∑' n : ℕ, f (k + (((n + 1 : ℕ)) : ℤ)) :=
          hsumRay1.tsum_eq_zero_add
      _ ≤ 1 / A + ∑' n : ℕ, u n := add_le_add hk0 hshiftle
  have hray2le : (∑' j : ℕ, f (k - ((j : ℤ) + 1))) ≤ ∑' j : ℕ, u j := by
    have hle1 : (∑' j : ℕ, f (k - ((j : ℤ) + 1))) ≤ ∑' j : ℕ, u (j + 1) :=
      Summable.tsum_le_tsum (fun j => hbound2 j) hsumRay2 hsumUw
    have hu0 : 0 ≤ u 0 := by
      rw [hu]
      have hA0 : (0 : ℝ) < A + (((0 : ℕ) : ℝ) * h) ^ 2 := by
        have := sq_nonneg (((0 : ℕ) : ℝ) * h); linarith
      exact le_of_lt (div_pos one_pos hA0)
    have htz := hsumU.tsum_eq_zero_add
    linarith
  have hspos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  calc (∑' n : ℤ, f n)
      = (∑' j : ℕ, f (k + (j : ℤ))) + ∑' j : ℕ, f (k - ((j : ℤ) + 1)) := htsumF
    _ ≤ (1 / A + ∑' j : ℕ, u j) + ∑' j : ℕ, u j := by linarith [hray1le, hray2le]
    _ = 1 / A + 2 * ∑' j : ℕ, u j := by ring
    _ ≤ 1 / A + 2 * (3 * (1 / A + 1 / (h * Real.sqrt A))) := by linarith [hUle]
    _ ≤ 7 * (1 / A + 1 / (h * Real.sqrt A)) := by
      have hs : 0 < h * Real.sqrt A := mul_pos hh hspos
      have hs' : 0 < 1 / (h * Real.sqrt A) := one_div_pos.mpr hs
      linarith

end Work.LinnikAreas.TwMass
