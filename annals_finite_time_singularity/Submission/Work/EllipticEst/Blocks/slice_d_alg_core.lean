import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Blocks

/-- **Pure-arithmetic core of the `∂_θ`-slice estimate.**  Put this declaration in namespace `Work.FTS.EllipticEst.Blocks` (i.e. between `namespace Work.FTS.EllipticEst.Blocks` and `end Work.FTS.EllipticEst.Blocks`), in the file `Submission/Work/FTS/EllipticEst/Blocks/slice_d_alg_core.lean` (module `Submission.Work.FTS.EllipticEst.Blocks.slice_d_alg_core`).  It needs only `import Mathlib`.

Let `σ ≥ 0`, `Cc, Cs, Φ ≥ 0` be reals, `j : ℕ`, and `c S Y : ℕ → ℝ` sequences satisfying, for every `a ∈ Finset.range (j+1)`,

* `|c a| ≤ Cc`,  * `|S a| ≤ Cs * σ`,  * `Y a ^ 2 * σ ^ (2 - γ) ≤ Φ`.

Then `(∑ a ∈ Finset.range (j+1), c a * S a * Y a) ^ 2 * σ ^ (-γ) ≤ Cc^2 * Cs^2 * ((j+1 : ℕ) : ℝ)^2 * Φ`.

Proof route: if `σ = 0` then `S a = 0` and both sides vanish.  If `σ > 0`, bound the sum with the triangle inequality by `Cc * Cs * σ * ∑ |Y a|`, use Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq` (`(∑ |Y a|)^2 ≤ (j+1) * ∑ Y a^2`), and then distribute `σ ^ (2 - γ) = σ^2 * σ^(-γ)` (`Real.rpow_add`) over the `j+1` terms, each of which is `≤ Φ` by the last hypothesis. -/
theorem slice_d_alg_core {j : ℕ} {σ γ Φ Cc Cs : ℝ} (hσ : 0 ≤ σ) (hCc : 0 ≤ Cc) (hCs : 0 ≤ Cs)
    (hΦ : 0 ≤ Φ) {c S Y : ℕ → ℝ}
    (hc : ∀ a ∈ Finset.range (j + 1), |c a| ≤ Cc)
    (hS : ∀ a ∈ Finset.range (j + 1), |S a| ≤ Cs * σ)
    (hY : ∀ a ∈ Finset.range (j + 1), (Y a) ^ 2 * σ ^ (2 - γ) ≤ Φ) :
    (∑ a ∈ Finset.range (j + 1), c a * S a * Y a) ^ 2 * σ ^ (-γ)
      ≤ Cc ^ 2 * Cs ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 2 * Φ := by
  by_cases hσ0 : σ = 0
  · -- Degenerate case `σ = 0`: every `S a` vanishes, so both sides are nonnegative
    -- and the left-hand side is `0`.
    subst hσ0
    have hS0 : ∀ a ∈ Finset.range (j + 1), S a = 0 := by
      intro a ha
      have h := hS a ha
      rw [mul_zero] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hsum0 : ∑ a ∈ Finset.range (j + 1), c a * S a * Y a = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hS0 a ha]
      ring
    rw [hsum0]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg Cc) (sq_nonneg Cs)) (sq_nonneg _)) hΦ
  · -- Genuine case `σ > 0`.
    have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
    -- Triangle inequality: `|T| ≤ Cc * Cs * σ * ∑ |Y a|`.
    have hterm : ∀ a ∈ Finset.range (j + 1), |c a * S a * Y a| ≤ Cc * Cs * σ * |Y a| := by
      intro a ha
      have h1 := hc a ha
      have h2 := hS a ha
      have key : |c a| * |S a| ≤ Cc * (Cs * σ) := mul_le_mul h1 h2 (abs_nonneg _) hCc
      calc |c a * S a * Y a| = |c a| * |S a| * |Y a| := by rw [abs_mul, abs_mul]
        _ ≤ Cc * (Cs * σ) * |Y a| := mul_le_mul_of_nonneg_right key (abs_nonneg _)
        _ = Cc * Cs * σ * |Y a| := by ring
    have habs : |∑ a ∈ Finset.range (j + 1), c a * S a * Y a|
        ≤ Cc * Cs * σ * ∑ a ∈ Finset.range (j + 1), |Y a| := by
      calc |∑ a ∈ Finset.range (j + 1), c a * S a * Y a|
          ≤ ∑ a ∈ Finset.range (j + 1), |c a * S a * Y a| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a ∈ Finset.range (j + 1), Cc * Cs * σ * |Y a| := Finset.sum_le_sum hterm
        _ = Cc * Cs * σ * ∑ a ∈ Finset.range (j + 1), |Y a| :=
            (Finset.mul_sum _ _ _).symm
    have hsq : (∑ a ∈ Finset.range (j + 1), c a * S a * Y a) ^ 2
        ≤ (Cc * Cs * σ * ∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 := by
      have h := pow_le_pow_left₀
        (abs_nonneg (∑ a ∈ Finset.range (j + 1), c a * S a * Y a)) habs 2
      rwa [sq_abs] at h
    have hsq' : (∑ a ∈ Finset.range (j + 1), c a * S a * Y a) ^ 2
        ≤ Cc ^ 2 * Cs ^ 2 * σ ^ 2 * (∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 := by
      calc (∑ a ∈ Finset.range (j + 1), c a * S a * Y a) ^ 2
          ≤ (Cc * Cs * σ * ∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 := hsq
        _ = Cc ^ 2 * Cs ^ 2 * σ ^ 2 * (∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 := by ring
    -- Cauchy–Schwarz bound on `(∑ |Y a|)^2`.
    have hcs : (∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2
        ≤ ((j + 1 : ℕ) : ℝ) * ∑ a ∈ Finset.range (j + 1), (Y a) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := fun a => |Y a|)
      rw [Finset.card_range] at h
      simpa only [sq_abs] using h
    have hAB1 : (∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 * σ ^ (2 - γ)
        ≤ (((j + 1 : ℕ) : ℝ) * ∑ a ∈ Finset.range (j + 1), (Y a) ^ 2) * σ ^ (2 - γ) :=
      mul_le_mul_of_nonneg_right hcs (Real.rpow_nonneg hσ _)
    -- Termwise bound `Y a ^ 2 * σ ^ (2 - γ) ≤ Φ`, summed over the `j + 1` indices.
    have hsumΦ : ∑ a ∈ Finset.range (j + 1), (Y a) ^ 2 * σ ^ (2 - γ) ≤ ((j + 1 : ℕ) : ℝ) * Φ := by
      have h1 : ∑ a ∈ Finset.range (j + 1), (Y a) ^ 2 * σ ^ (2 - γ)
          ≤ ∑ a ∈ Finset.range (j + 1), Φ := Finset.sum_le_sum hY
      have h2 : (∑ a ∈ Finset.range (j + 1), Φ) = ((j + 1 : ℕ) : ℝ) * Φ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact h1.trans_eq h2
    have hAB2 : (((j + 1 : ℕ) : ℝ) * ∑ a ∈ Finset.range (j + 1), (Y a) ^ 2) * σ ^ (2 - γ)
        ≤ ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) * Φ) := by
      have hrew : ∑ a ∈ Finset.range (j + 1), (Y a) ^ 2 * σ ^ (2 - γ)
          = (∑ a ∈ Finset.range (j + 1), (Y a) ^ 2) * σ ^ (2 - γ) :=
            (Finset.sum_mul _ _ _).symm
      rw [mul_assoc, ← hrew]
      exact mul_le_mul_of_nonneg_left hsumΦ (Nat.cast_nonneg _)
    have hAB : (∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 * σ ^ (2 - γ)
        ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * Φ := by
      calc (∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 * σ ^ (2 - γ)
          ≤ (((j + 1 : ℕ) : ℝ) * ∑ a ∈ Finset.range (j + 1), (Y a) ^ 2) * σ ^ (2 - γ) := hAB1
        _ ≤ ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) * Φ) := hAB2
        _ = ((j + 1 : ℕ) : ℝ) ^ 2 * Φ := by ring
    -- Distribute the real power: `σ ^ 2 * σ ^ (-γ) = σ ^ (2 - γ)`.
    have hpat : σ ^ 2 * σ ^ (-γ) = σ ^ (2 - γ) := by
      have h := Real.rpow_add hσpos (2 : ℝ) (-γ)
      rw [Real.rpow_two] at h
      rw [← h]
      rw [sub_eq_add_neg]
    have hCCCs : 0 ≤ Cc ^ 2 * Cs ^ 2 := mul_nonneg (sq_nonneg Cc) (sq_nonneg Cs)
    calc (∑ a ∈ Finset.range (j + 1), c a * S a * Y a) ^ 2 * σ ^ (-γ)
        ≤ (Cc ^ 2 * Cs ^ 2 * σ ^ 2 * (∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2) * σ ^ (-γ) :=
          mul_le_mul_of_nonneg_right hsq' (Real.rpow_nonneg hσ _)
      _ = Cc ^ 2 * Cs ^ 2 * ((∑ a ∈ Finset.range (j + 1), |Y a|) ^ 2 * σ ^ (2 - γ)) := by
          rw [← hpat]; ring
      _ ≤ Cc ^ 2 * Cs ^ 2 * (((j + 1 : ℕ) : ℝ) ^ 2 * Φ) := mul_le_mul_of_nonneg_left hAB hCCCs
      _ = Cc ^ 2 * Cs ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 2 * Φ := by ring

end Work.EllipticEst.Blocks
