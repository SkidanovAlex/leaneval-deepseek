import Mathlib
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le
import Submission.Work.BourgainPlan.Maximal.polyProfile_increment_sum_le
import Submission.Work.BourgainPlan.Maximal.l2_defs

/-!
# Bounded lacunary variation of the polynomial profile, for *every* polynomial

For `P : ℤ[X]` of degree `d ≥ 2` the oscillatory profile

  `Φ_N(β) = polyProfile P N β = ∫_0^1 e(β P(N s)) ds`

has bounded dyadic (lacunary `2`-)variation, uniformly in the frequency:

  `∑_{k<N} ‖Φ_{2^{k+1}}(β) − Φ_{2^k}(β)‖ ≤ C`,

with `C` depending only on `P`.

This is the statement `Work.BourgainPlan.Maximal.polyProfile_increment_sum_le`, which however is
phrased for polynomials with **positive leading coefficient**.  The present file removes that
restriction: the sign of the leading coefficient is irrelevant, because

  `polyProfile P N β = polyProfile (−P) N (−β)`

(the profile of `−P` is the profile of `P` at the reflected frequency), and norms are insensitive to
`β ↦ −β`.  Since the decay inputs (`polyProfile_decay_sharp`, `polyProfile_step_diff_small`) already
carry the absolute value `|lead P|`, the sign hypothesis was never used.

The frequency restriction `|β| ≤ 1/2` of the statement below is a fortiori, the bound being uniform
over all `β : ℝ`.
-/

namespace Work.BourgainPlan.Maximal

/-- The real polynomial attached to `-P` is the negative of the one attached to `P`. -/
lemma toRealPoly_neg (P : Polynomial ℤ) : toRealPoly (-P) = -toRealPoly P := by
  rw [toRealPoly, toRealPoly, Polynomial.map_neg]

/-- **Reflection of the profile under `P ↦ −P`**: `Φ^{−P}_N(β) = Φ^P_N(−β)`. -/
lemma polyProfile_neg (P : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    polyProfile P N β = polyProfile (-P) N (-β) := by
  unfold polyProfile
  rw [toRealPoly_neg]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Polynomial.eval_neg]
  push_cast
  ring_nf

theorem polyProfile_lacunary_sum_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ), |β| ≤ 1 / 2 → ∀ N : ℕ,
      ∑ k ∈ Finset.range N,
        ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ C := by
  have hPne : P ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  have hne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- negative leading coefficient: read the bound at `−P` through the reflection identity
    have hQpos : 0 < (-P).leadingCoeff := by
      rw [Polynomial.leadingCoeff_neg]; linarith
    have hQdeg : (-P).natDegree = P.natDegree := Polynomial.natDegree_neg P
    obtain ⟨C, hCpos, hC⟩ := polyProfile_increment_sum_le (-P) hQpos (by rw [hQdeg]; exact hd)
    refine ⟨C, hCpos, ?_⟩
    intro β _ N
    have hsum : (∑ k ∈ Finset.range N,
        ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖)
        = ∑ k ∈ Finset.range N,
        ‖polyProfile (-P) (2 ^ (k + 1)) (-β) - polyProfile (-P) (2 ^ k) (-β)‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [polyProfile_neg P (2 ^ (k + 1)) β, polyProfile_neg P (2 ^ k) β]
    rw [hsum]
    exact hC (-β) N
  · -- positive leading coefficient: the increment bound applies directly
    obtain ⟨C, hCpos, hC⟩ := polyProfile_increment_sum_le P hpos hd
    exact ⟨C, hCpos, fun β _ N => hC β N⟩

end Work.BourgainPlan.Maximal
