import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-! ### Elementary pieces for the one-dimensional lattice counting sums

The profile `24 j² + 2` is summed against `1`, `j⁻²` and `j⁻³` over `0 ≤ j ≤ J`; the last case
is routed through Mathlib's harmonic numbers (`harmonic_le_one_add_log`), which supplies the
logarithmic bound `H_J ≤ 1 + log J` without an explicit integral comparison.  All three
estimates hold with the constants `26`, `26` and `26` in place of the requested `30`. -/

/-- `Σ_{j ≤ J} (24 j² + 2) ≤ 30 (J+1)³`, by induction: the increment
`30 ((J+2)³ − (J+1)³) = 30 (3J² + 9J + 7)` dominates `24 (J+1)² + 2`. -/
lemma latSumOneDCount_quad (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2)) ≤ 30 * ((J : ℝ) + 1) ^ 3 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [ih]

/-- `Σ_{j ≤ J} (24 j² + 2)/j² ≤ 30 (J+1)`: every summand is at most `26`
(the summand at `j = 0` is `0` by the junk convention `1/0 = 0`). -/
lemma latSumOneDCount_sq (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 2)
      ≤ 30 * ((J : ℝ) + 1) := by
  have h : ∀ j : ℕ, (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 2 ≤ 26 := by
    intro j
    rcases Nat.eq_zero_or_pos j with h0 | hp
    · subst h0; norm_num
    · have h1 : (1 : ℝ) ≤ (j : ℝ) := by
        have : 1 ≤ j := hp
        exact_mod_cast this
      rw [div_le_iff₀ (pow_pos (by linarith) 2)]
      nlinarith
  calc (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 2)
      ≤ ∑ _j ∈ Finset.range (J + 1), (26 : ℝ) := Finset.sum_le_sum (fun j _ => h j)
    _ = 26 * ((J : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ 30 * ((J : ℝ) + 1) := by
        have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        linarith

/-- The inverse-sum identity behind the `(2,3)` case: the range sum of `j⁻¹` over `0 ≤ j ≤ J`
is Mathlib's harmonic number `H_J` (`0⁻¹ = 0` is discarded). -/
lemma sum_range_inv_eq_harmonic (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), ((j : ℝ))⁻¹) = ((harmonic J : ℚ) : ℝ) := by
  rw [harmonic, Finset.sum_range_succ']; simp [Rat.cast_sum]

/-- `H_J ≤ 1 + log (J+1)`: Mathlib's `harmonic_le_one_add_log` together with monotonicity of
`log` (separately at `J = 0`, where both sides are `1`). -/
lemma sum_range_inv_le_log (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), ((j : ℝ))⁻¹) ≤ 1 + Real.log ((J : ℝ) + 1) := by
  rw [sum_range_inv_eq_harmonic]
  refine (harmonic_le_one_add_log J).trans ?_
  by_cases hJ : J = 0
  · subst hJ; norm_num
  · have hJp : (0 : ℝ) < (J : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hJ
    have hlog : Real.log (J : ℝ) ≤ Real.log ((J : ℝ) + 1) := Real.log_le_log hJp (by linarith)
    linarith

/-- `Σ_{j ≤ J} (24 j² + 2)/j³ ≤ 30 (1 + log (J+1))`: every summand is at most `26/j`
(again the summand at `j = 0` is `0`), and the range sum of `j⁻¹` is at most `1 + log (J+1)`. -/
lemma latSumOneDCount_cube (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 3)
      ≤ 30 * (1 + Real.log ((J : ℝ) + 1)) := by
  have h : ∀ j : ℕ, (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 3 ≤ 26 * ((j : ℝ))⁻¹ := by
    intro j
    rcases Nat.eq_zero_or_pos j with h0 | hp
    · subst h0; norm_num
    · have hj : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hp
      have h1 : (1 : ℝ) ≤ (j : ℝ) := by
        have : 1 ≤ j := hp
        exact_mod_cast this
      have hjj : (j : ℝ)⁻¹ * (j : ℝ) ^ 3 = (j : ℝ) ^ 2 := by
        calc (j : ℝ)⁻¹ * (j : ℝ) ^ 3 = (j : ℝ) ^ 2 * ((j : ℝ)⁻¹ * (j : ℝ)) := by ring
          _ = (j : ℝ) ^ 2 := by rw [inv_mul_cancel₀ (ne_of_gt hj), mul_one]
      rw [div_le_iff₀ (pow_pos hj 3)]
      have hkey : (26 : ℝ) * (j : ℝ)⁻¹ * (j : ℝ) ^ 3 = 26 * (j : ℝ) ^ 2 := by
        rw [mul_assoc, hjj]
      rw [hkey]
      nlinarith
  calc (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 3)
      ≤ ∑ j ∈ Finset.range (J + 1), 26 * ((j : ℝ))⁻¹ := Finset.sum_le_sum (fun j _ => h j)
    _ = 26 * (∑ j ∈ Finset.range (J + 1), ((j : ℝ))⁻¹) := by rw [Finset.mul_sum]
    _ ≤ 26 * (1 + Real.log ((J : ℝ) + 1)) := by
        have := sum_range_inv_le_log J; linarith
    _ ≤ 30 * (1 + Real.log ((J : ℝ) + 1)) := by
        have hlog : (0 : ℝ) ≤ Real.log ((J : ℝ) + 1) :=
          Real.log_nonneg (by have : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J; linarith)
        linarith

/-- Elementary bounds for the three truncated lattice-shell profile sums appearing in the
lattice *counting* estimates: `Σ_{j ≤ J} (24j² + 2) ≤ 30 (J+1)³`,
`Σ_{j ≤ J} (24j² + 2)/j² ≤ 30 (J+1)`, and `Σ_{j ≤ J} (24j² + 2)/j³ ≤ 30 (1 + log (J+1))`
(terms at `j = 0` are `0` by the junk-value convention `1/0 = 0`). -/
theorem latSumOneDCount (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2)) ≤ 30 * ((J : ℝ) + 1) ^ 3 ∧
    (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 2) ≤ 30 * ((J : ℝ) + 1) ∧
    (∑ j ∈ Finset.range (J + 1), (24 * (j : ℝ) ^ 2 + 2) / (j : ℝ) ^ 3)
      ≤ 30 * (1 + Real.log ((J : ℝ) + 1)) :=
  ⟨latSumOneDCount_quad J, latSumOneDCount_sq J, latSumOneDCount_cube J⟩

end Work.BoseBogFS
