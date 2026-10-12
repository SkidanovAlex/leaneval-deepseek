import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

lemma half_le_norm_of_coord_abs_ge {ℓ K δ : ℝ} (hℓ : 0 < ℓ) (hbig : 5 * K * δ ≤ ℓ) {x : EuclideanSpace ℝ (Fin 3)} (hx : ∀ j : Fin 3, ℓ / 2 - K * δ ≤ |x.ofLp j|) : ℓ / 2 ≤ ‖x‖ := by
  -- Every coordinate obeys `|x_j| ≥ ℓ/2 - Kδ`, and `5Kδ ≤ ℓ` gives `ℓ/2 - Kδ ≥ 3ℓ/10`.
  have hδ : K * δ ≤ ℓ / 5 := by linarith
  have hcoord : ∀ j : Fin 3, (3 * ℓ / 10) ^ 2 ≤ (x.ofLp j) ^ 2 := by
    intro j
    have h1 : 3 * ℓ / 10 ≤ |x.ofLp j| := by
      have := hx j
      linarith
    have h2 : (3 * ℓ / 10) ^ 2 ≤ |x.ofLp j| ^ 2 :=
      pow_le_pow_left₀ (by linarith) h1 2
    simpa [sq_abs] using h2
  -- Hence `‖x‖² = ∑ x_j² ≥ 3(3ℓ/10)² = 27ℓ²/100 ≥ (ℓ/2)²`.
  have hsum : 3 * (3 * ℓ / 10) ^ 2 ≤ ∑ j : Fin 3, (x.ofLp j) ^ 2 := by
    calc 3 * (3 * ℓ / 10) ^ 2 = ∑ _j : Fin 3, (3 * ℓ / 10) ^ 2 := by simp
      _ ≤ ∑ j : Fin 3, (x.ofLp j) ^ 2 := Finset.sum_le_sum (fun j _ => hcoord j)
  have hsq : (ℓ / 2) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    nlinarith [hsum, hℓ]
  -- Conclude from monotonicity of squaring on the nonnegative reals.
  have habs : |ℓ / 2| ≤ |‖x‖| := (sq_le_sq).mp hsq
  rwa [abs_of_nonneg (by linarith), abs_of_nonneg (norm_nonneg x)] at habs

end Work.BoseB1Cube
