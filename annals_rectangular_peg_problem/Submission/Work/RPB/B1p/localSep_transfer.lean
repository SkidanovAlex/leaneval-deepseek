import Mathlib
import Submission.Work.RPB.Port.Drive.SeparationBase

namespace Work.RPB.B1p

open Work.RPB.Port.Drive

/-- If `A ⊆ K` and `W ∩ K ⊆ A`, then `A` and `K` agree on `W`. -/
lemma inter_eq_of_subset {A K W : Set (ℝ × ℝ)} (hAK : A ⊆ K) (hWK : W ∩ K ⊆ A) :
    W ∩ A = W ∩ K := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, hAK hx.2⟩
  · intro hx
    exact ⟨hx.1, hWK hx⟩

/-- If `A ⊆ K` and `W ∩ K ⊆ A`, then the differences `W \ A` and `W \ K` coincide. -/
lemma diff_eq_of_inter_eq {A K W : Set (ℝ × ℝ)} (hAK : A ⊆ K) (hWK : W ∩ K ⊆ A) :
    W \ A = W \ K := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, fun hK => hx.2 (hWK ⟨hx.1, hK⟩)⟩
  · intro hx
    exact ⟨hx.1, fun hA => hx.2 (hAK hA)⟩

theorem localSep_transfer {A K W W₁ W₂ : Set (ℝ × ℝ)}
    (h : Work.RPB.Port.Drive.LocalSep A W W₁ W₂) (hAK : A ⊆ K) (hWK : W ∩ K ⊆ A) :
    Work.RPB.Port.Drive.LocalSep K W W₁ W₂ := by
  have hAW : W ∩ A = W ∩ K := inter_eq_of_subset hAK hWK
  have hdiff : W \ A = W \ K := diff_eq_of_inter_eq hAK hWK
  refine ⟨h.isOpen_U, h.isOpen₁, h.isOpen₂, h.pc₁, h.pc₂, h.disjoint, ?_, ?_, ?_⟩
  · rw [h.union, hdiff]
  · intro q hq
    exact h.acc₁ q (by rw [hAW]; exact hq)
  · intro q hq
    exact h.acc₂ q (by rw [hAW]; exact hq)

end Work.RPB.B1p
