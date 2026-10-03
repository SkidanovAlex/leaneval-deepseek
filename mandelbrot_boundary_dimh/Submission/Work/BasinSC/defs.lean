import Mathlib

/-!
# Definitions for the BasinSC area (Shishikura, Lemma 5.2)

Basic plane-topology objects shared by the lemmas of `Submission/Work/BasinSC/`.
-/

open Set Metric Filter Topology

namespace Work.BasinSC

/-- The punctured unit disc `𝔻* = {w : ℂ | w ≠ 0 ∧ ‖w‖ < 1}`. -/
def puncturedDisc : Set ℂ := {w : ℂ | w ≠ 0 ∧ ‖w‖ < 1}

theorem mem_puncturedDisc {w : ℂ} : w ∈ puncturedDisc ↔ w ≠ 0 ∧ ‖w‖ < 1 := Iff.rfl

/-- The unit disc. -/
def unitDisc : Set ℂ := {w : ℂ | ‖w‖ < 1}

theorem mem_unitDisc {w : ℂ} : w ∈ unitDisc ↔ ‖w‖ < 1 := Iff.rfl

end Work.BasinSC
