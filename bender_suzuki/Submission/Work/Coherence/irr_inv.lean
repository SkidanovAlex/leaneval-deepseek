import Submission.Work.Coherence.irr_conj
import Submission.Work.Coherence.char_inv_eq_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Irr G` is closed under `g ↦ g⁻¹`

The contragredient (dual) representation is what makes both `irr_conj` (complex conjugation) and
this lemma true; the two are the same statement because for a finite group the eigenvalues of
`V.ρ g` are roots of unity, i.e. `χ (g⁻¹) = conj (χ g)` (`Work.Coherence.char_inv_eq_conj`).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

/-- The "dual" permutation of `Irr G`.  `Irr G` is closed under the map `g ↦ g⁻¹`. -/
theorem irr_inv {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    (fun g => χ g⁻¹) ∈ Irr G := by
  obtain ⟨V, hV, rfl⟩ := mem_Irr.mp hχ
  have h : (fun g => V.character g⁻¹) = fun g => starRingEnd ℂ (V.character g) :=
    funext fun g => char_inv_eq_conj V g
  rw [h]
  exact irr_conj (mem_Irr.mpr ⟨V, hV, rfl⟩)

end Work.Coherence
