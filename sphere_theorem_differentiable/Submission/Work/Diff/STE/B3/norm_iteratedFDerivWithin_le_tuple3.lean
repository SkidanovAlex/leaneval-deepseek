import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

theorem norm_iteratedFDerivWithin_le_tuple3
    {E G₁ G₂ G₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [NormedAddCommGroup G₂] [NormedSpace ℝ G₂]
    [NormedAddCommGroup G₃] [NormedSpace ℝ G₃]
    {s : Set E} {F₁ : E → G₁} {F₂ : E → G₂} {F₃ : E → G₃} {x : E} {i : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hF : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun y => (F₁ y, F₂ y, F₃ y)) s x)
    (h₁ : ‖iteratedFDerivWithin ℝ i F₁ s x‖ ≤ A)
    (h₂ : ‖iteratedFDerivWithin ℝ i F₂ s x‖ ≤ A)
    (h₃ : ‖iteratedFDerivWithin ℝ i F₃ s x‖ ≤ A) :
    ‖iteratedFDerivWithin ℝ i (fun y => (F₁ y, F₂ y, F₃ y)) s x‖ ≤ A := by
  have h₁' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F₁ s x := hF.fst
  have h₂₃ : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun y => (F₂ y, F₃ y)) s x := hF.snd
  have h₂' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F₂ s x := h₂₃.fst
  have h₃' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F₃ s x := h₂₃.snd
  have hi : (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [iteratedFDerivWithin_prodMk h₁' h₂₃ hs hx hi,
      iteratedFDerivWithin_prodMk h₂' h₃' hs hx hi]
  simp only [ContinuousMultilinearMap.opNorm_prod]
  exact max_le h₁ (max_le h₂ h₃)

end Work.Diff.STE.B3
