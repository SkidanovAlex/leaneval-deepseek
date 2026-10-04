import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Q2PB.on_pair_norm_b

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pair `(ρ(e₁ + ε e₄), ρ(e₂ + δ e₃))` is orthonormal when `ρ² = 1/2`, `ε² = δ² = 1`

Companion of `Work.Diff.Alg.Q2PB.on_pair_norm_b`: for an orthonormal four-frame `e₁, e₂, e₃, e₄`
of `ℝⁿ`, the "diagonal" vectors `ρ • (e₁ + ε • e₄)` and `ρ • (e₂ + δ • e₃)` are unit and
orthogonal whenever `ρ * ρ = 1/2` and `ε * ε = δ * δ = 1`. The proof is the bilinearity of the
Euclidean pairing `dot` together with the orthonormality relations of `IsON4`.
-/

namespace Work.Diff.Alg.Q2PB

open Submission.Diff.Alg Finset

theorem on_pair_norm_c {n : ℕ} {e1 e2 e3 e4 : Fin n → ℝ} (h : Work.Diff.Alg.Q2P.IsON4 e1 e2 e3 e4)
    (ρ ε δ : ℝ) (hρ : ρ * ρ = 1 / 2) (hε : ε * ε = 1) (hδ : δ * δ = 1) :
    Submission.Diff.Alg.IsONPair (ρ • (e1 + ε • e4)) (ρ • (e2 + δ • e3)) := by
  simp only [Work.Diff.Alg.Q2P.IsON4] at h
  obtain ⟨h11, h22, h33, h44, h12, h13, h14, h23, h24, h34⟩ := h
  have h41 : dot e4 e1 = 0 := by rw [dot_comm]; exact h14
  have h42 : dot e4 e2 = 0 := by rw [dot_comm]; exact h24
  have h43 : dot e4 e3 = 0 := by rw [dot_comm]; exact h34
  have h32 : dot e3 e2 = 0 := by rw [dot_comm]; exact h23
  simp only [IsONPair]
  refine ⟨?_, ?_, ?_⟩
  · simp only [dot_smul_left, dot_smul_right, dot_add_left, dot_add_right]
    rw [h11, h44, h14, h41]
    nlinarith [hρ, hε]
  · simp only [dot_smul_left, dot_smul_right, dot_add_left, dot_add_right]
    rw [h22, h33, h23, h32]
    nlinarith [hρ, hδ]
  · simp only [dot_smul_left, dot_smul_right, dot_add_left, dot_add_right]
    rw [h12, h13, h42, h43]
    ring

end Work.Diff.Alg.Q2PB
