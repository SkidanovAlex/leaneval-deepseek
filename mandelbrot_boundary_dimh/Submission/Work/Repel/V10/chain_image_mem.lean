import Mathlib
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.L62.chain
import Submission.Work.Repel.walk_of_sub

namespace Work.Repel

/-- **The chain iterate of a translated source point.**  If `u = w + k` with `w ∈ W j` and
`k : ℤ`, then the `j`-th iterate of `ĥ = R - β` differs from the iterate of `w` by the same
integer translation, and lands in `W 0` after removing the translation:
`ĥ^[j] u - k ∈ W 0`. -/
theorem chain_image_mem (V : Work.Repel.V10) {j : ℕ} {k : ℤ} {u : ℂ}
    (hu : u ∈ (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j) :
    (fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ) ∈ V.W 0 := by
  obtain ⟨w, hw, rfl⟩ := hu
  have hshift : (fun x : ℂ => V.R x - V.β)^[j] (w + ((k : ℤ) : ℂ))
      = (fun x : ℂ => V.R x - V.β)^[j] w + ((k : ℤ) : ℂ) :=
    chain_walk_add_int V.hIsChain V.hReq hw j le_rfl
  rw [hshift, add_sub_cancel_right]
  exact V.hIsChain.iterate_mem hw

end Work.Repel
