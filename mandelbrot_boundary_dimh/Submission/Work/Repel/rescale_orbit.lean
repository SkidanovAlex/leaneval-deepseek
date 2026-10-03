import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open Work.Horn.MandelDim

noncomputable section

/-- A backward orbit `w` of the pushed-down horn map `pushdown d.E` which lies in the cylinder
domain for every positive index, after rescaling by `s = s₀ d`, is a backward orbit of the level-1
germ `g₀ = s₀ · pushdown d.E (·/s₀)` inside its domain `Dg0germ`, tending to `0`.  This is the
elementary verification that the rescaled inverse orbit of Shishikura §6 lives in the domain of the
level-1 germ. -/
theorem rescale_orbit {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (hd : MandelDim.HornData d)
    (s : ℂ) (hs : s = Work.Repel.s0 d) (w : ℕ → ℂ)
    (hw : ∀ j, w (j + 1) ∈ MandelDim.piExp '' (hd.Bu ∪ hd.Bl) ∧ MandelDim.pushdown d.E (w (j + 1)) = w j)
    (hwtend : Filter.Tendsto w Filter.atTop (nhds 0)) (hw0 : w 0 ≠ 0) :
    (∀ j, 1 ≤ j → s * w j ∈ Work.Repel.Dg0germ d hd) ∧
      (∀ j, Work.Repel.g0germ d (s * w (j + 1)) = s * w j) ∧
      Filter.Tendsto (fun j => s * w j) Filter.atTop (nhds 0) ∧ (∃ j, s * w j ≠ 0) := by
  have hs0d : Work.Repel.s0 d ≠ 0 := Work.Repel.s0_ne_zero d hd
  have hs0ne : s ≠ 0 := by rw [hs]; exact hs0d
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j = (j - 1) + 1 := (Nat.succ_pred_eq_of_pos hj).symm
    rw [hj']
    exact ⟨w ((j - 1) + 1), Or.inr (hw (j - 1)).1, by rw [hs]⟩
  · intro j
    show Work.Repel.s0 d * MandelDim.pushdown d.E (s * w (j + 1) / Work.Repel.s0 d) = s * w j
    have h1 : (s * w (j + 1)) / Work.Repel.s0 d = w (j + 1) := by
      rw [hs]; field_simp
    rw [h1, (hw j).2, hs]
  · simpa using hwtend.const_mul s
  · exact ⟨0, mul_ne_zero hs0ne hw0⟩

end

end Work.Repel
