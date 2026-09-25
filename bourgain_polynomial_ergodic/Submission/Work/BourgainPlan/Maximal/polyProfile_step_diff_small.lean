import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le

/-!
# The profile does not move much between two dyadic scales

For `P ∈ ℤ[X]` of degree `d ≥ 2` and two dyadic scales `2 ^ k ≤ 2 ^ k'`,

  `‖Φ_{2^k'}(β) − Φ_{2^k}(β)‖ ≤ C · (|β| · (2^k')^d)`,

with `C = 8π (∑_i |c_i|) + 1`.  The proof is the triangle inequality around the value `1`
of the profile, using the elementary Lipschitz bound at the origin
(`polyProfile_sub_one_le`) at each of the two scales, together with
`(2^k)^d ≤ (2^k')^d`.

This is the "the profile barely changes along a dyadic step" estimate: in the regime
`|β| (2^k')^d ≲ 1` it is a genuine smallness statement, and it lets one replace the
profile at a coarser scale by the profile at the finest scale at a cost that is linear in
`|β| (2^k')^d`.
-/

namespace Work.BourgainPlan.Maximal

theorem polyProfile_step_diff_small (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k k' : ℕ), k ≤ k' → ∀ β : ℝ,
      ‖polyProfile P (2 ^ k') β - polyProfile P (2 ^ k) β‖
        ≤ C * (|β| * ((2 : ℝ) ^ k') ^ P.natDegree) := by
  refine ⟨8 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) + 1,
    ?_, ?_⟩
  · have hA0 : 0 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    nlinarith [Real.pi_pos, hA0]
  · intro k k' hkk' β
    set A : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| with hA
    set X : ℝ := |β| * ((2 : ℝ) ^ k) ^ P.natDegree with hX
    set X' : ℝ := |β| * ((2 : ℝ) ^ k') ^ P.natDegree with hX'
    have hA0 : 0 ≤ A := by rw [hA]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    have hX'0 : 0 ≤ X' := by rw [hX']; positivity
    have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k' := pow_le_pow_right₀ (by norm_num) hkk'
    have hdmono : ((2 : ℝ) ^ k) ^ P.natDegree ≤ ((2 : ℝ) ^ k') ^ P.natDegree :=
      pow_le_pow_left₀ (by positivity) hmono _
    have hXX' : X ≤ X' := by
      rw [hX, hX']
      exact mul_le_mul_of_nonneg_left hdmono (abs_nonneg β)
    have hfac0 : 0 ≤ 4 * Real.pi * A := by nlinarith [Real.pi_pos, hA0]
    have hN := polyProfile_sub_one_le P (2 ^ k') Nat.one_le_two_pow β
    have hM := polyProfile_sub_one_le P (2 ^ k) Nat.one_le_two_pow β
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hN hM
    rw [← hA, ← hX'] at hN
    rw [← hA, ← hX] at hM
    -- split the difference around the value `1` of the profile
    have hsum : ‖polyProfile P (2 ^ k') β - polyProfile P (2 ^ k) β‖
        ≤ 4 * Real.pi * A * X' + 4 * Real.pi * A * X := by
      have hEq : polyProfile P (2 ^ k') β - polyProfile P (2 ^ k) β
          = (polyProfile P (2 ^ k') β - 1) + (1 - polyProfile P (2 ^ k) β) := by ring
      have hM' : ‖1 - polyProfile P (2 ^ k) β‖ ≤ 4 * Real.pi * A * X := by
        rw [norm_sub_rev]
        exact hM
      rw [hEq]
      exact (norm_add_le _ _).trans (add_le_add hN hM')
    -- the two terms together are bounded by `8πA` times the larger scale
    refine hsum.trans ?_
    calc 4 * Real.pi * A * X' + 4 * Real.pi * A * X
        = 4 * Real.pi * A * (X' + X) := by ring
      _ ≤ 4 * Real.pi * A * (X' + X') :=
          mul_le_mul_of_nonneg_left (by linarith) hfac0
      _ = 8 * Real.pi * A * X' := by ring
      _ ≤ (8 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) + 1) * X' := by
          rw [← hA, add_mul, one_mul]
          linarith

end Work.BourgainPlan.Maximal
