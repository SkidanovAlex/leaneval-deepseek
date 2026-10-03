import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_v9_diff
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.V10.SrcC_isConnected

namespace Work.Repel

theorem fN_lift_eq (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {N : ℕ}
    (hN : ∀ w ∈ V.SrcC j k n, V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w)) :
    ∀ u ∈ V.fib j k, V.f ^[N] (V.P₀.φ (V.lift j k n u)) =
      V.P₀.φ (V.wOf (((fun x : ℂ => V.R x - V.β)^[j] u) - ((k : ℤ) : ℂ))) := by
  intro u hu
  have hmem : V.lift j k n u ∈ V.SrcC j k n := by
    rw [V10.SrcC_eq_image_lift V hSm]
    exact ⟨u, hu, rfl⟩
  rw [hN (V.lift j k n u) hmem]
  congr 1
  have hpi : V.s * MandelDim.piExp (V.lift j k n u) = V.P₁.φ u := by
    rw [V.lift_piExp (n := n) hSm hu]
    exact mul_div_cancel₀ _ V.hs
  rw [V10.wOfCell, V10.uOfSrc, hpi, V.uOf_unique (hSm hu) rfl]

end Work.Repel
