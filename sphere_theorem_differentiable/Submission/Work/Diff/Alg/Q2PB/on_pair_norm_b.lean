import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pair `(ρ(e₁ + ε e₃), ρ(e₂ + δ e₄))` is orthonormal when `ρ² = 1/2`, `ε² = δ² = 1`

Given an orthonormal four-frame `e₁, e₂, e₃, e₄` of `ℝⁿ`, the two vectors
`ρ • (e₁ + ε • e₃)` and `ρ • (e₂ + δ • e₄)` are unit and orthogonal as soon as `ρ * ρ = 1/2`
and `ε * ε = δ * δ = 1`: the four vectors `(e₁ ± e₃)/√2`, `(e₂ ± e₄)/√2` form the orthonormal
frame of "diagonal" planes used in Berger's inequality (`Work.Diff.Alg.q2p_berger`), and this
lemma records that this diagonal frame is indeed orthonormal.

The proof is the bilinearity of the Euclidean pairing `dot` together with the orthogonality
relations of `IsON4`.
-/

namespace Work.Diff.Alg.Q2PB

open Submission.Diff.Alg Finset

/-! ## Bilinearity of `dot` -/

theorem dot_add_left {n : ℕ} (u u' v : Fin n → ℝ) : dot (u + u') v = dot u v + dot u' v := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {n : ℕ} (u v v' : Fin n → ℝ) : dot u (v + v') = dot u v + dot u v' := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_smul_left {n : ℕ} (t : ℝ) (u v : Fin n → ℝ) : dot (t • u) v = t * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

@[simp] theorem dot_smul_right {n : ℕ} (t : ℝ) (u v : Fin n → ℝ) : dot u (t • v) = t * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

theorem dot_comm {n : ℕ} (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem on_pair_norm_b {n : ℕ} {e1 e2 e3 e4 : Fin n → ℝ} (h : Work.Diff.Alg.Q2P.IsON4 e1 e2 e3 e4)
    (ρ ε δ : ℝ) (hρ : ρ * ρ = 1 / 2) (hε : ε * ε = 1) (hδ : δ * δ = 1) :
    Submission.Diff.Alg.IsONPair (ρ • (e1 + ε • e3)) (ρ • (e2 + δ • e4)) := by
  simp only [Work.Diff.Alg.Q2P.IsON4] at h
  obtain ⟨h11, h22, h33, h44, h12, h13, h14, h23, h24, h34⟩ := h
  have h31 : dot e3 e1 = 0 := by rw [dot_comm]; exact h13
  have h42 : dot e4 e2 = 0 := by rw [dot_comm]; exact h24
  have h32 : dot e3 e2 = 0 := by rw [dot_comm]; exact h23
  simp only [IsONPair]
  refine ⟨?_, ?_, ?_⟩
  · simp only [dot_smul_left, dot_smul_right, dot_add_left, dot_add_right]
    rw [h11, h33, h13, h31]
    nlinarith [hρ, hε]
  · simp only [dot_smul_left, dot_smul_right, dot_add_left, dot_add_right]
    rw [h22, h44, h24, h42]
    nlinarith [hρ, hδ]
  · simp only [dot_smul_left, dot_smul_right, dot_add_left, dot_add_right]
    rw [h12, h14, h32, h34]
    ring

end Work.Diff.Alg.Q2PB
