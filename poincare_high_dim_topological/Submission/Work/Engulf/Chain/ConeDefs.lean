import Mathlib
import Submission.Work.Engulf.Basic

/-!
# A9 §12 (E3): the cone vocabulary

The cone step of Newman's Lemma 7 (`Submission/Work/NOTES_LEAD_poincare_engulf.md`, §12):
starting from a bad face `σ` of a complex `Γ` (with the `C1` hypotheses), one chooses a generic
apex `a` outside `⋃_{s ∈ Γ.faces} affineSpan (σ ∪ s)`, forms the *cone complex*
`Γ' = Γ ∪ a ∗ σ`, extends `f` over the cone, and applies the join lemma `L7` with
`τ₀ = {a}`, `τ₁ = σ`.

This module contains only the vocabulary (no proofs): the complex `Γ'` (`coneFaces`), the lateral
boundary `aσ̇` (`coneBd`) — which is the *floor* `floorOf {a} σ` of the join — and the
subcomplex `K` of the `L7` call (`coneK`).

Note that `{a}` is a vertex of `Γ'`: it is the cone over the empty face, and the faces of a
simplicial complex are closed under nonempty subsets.
-/

open Set Metric PL

namespace Work.Engulf.Chain

variable {N : ℕ}

/-- The lateral boundary `aσ̇ = ⋃_{w ∈ σ} simp (insert a (σ \ {w}))` of the cone on `σ` with
apex `a`.  It is the *floor* of the join `{a} ∪ σ`, i.e. `floorOf {a} σ`. -/
def coneBd (a : E N) (σ : Finset (E N)) : Set (E N) :=
  ⋃ w ∈ σ, simp ((insert a σ).erase w)

/-- The faces of the cone complex `Γ ∪ a ∗ σ`: the faces of `Γ`, together with the cones
`insert a s` over the faces `s ⊆ σ` (including `s = ∅`, which gives the apex `{a}`). -/
def coneFaces (Γ : Cx N) (σ : Finset (E N)) (a : E N) : Set (Finset (E N)) :=
  Γ.faces ∪ {t : Finset (E N) |
    ∃ s : Finset (E N), (s ∈ Γ.faces ∨ s = ∅) ∧ s ⊆ σ ∧ t = insert a s}

/-- The subcomplex `K = ⋃ {simp s | s ∈ Γ.faces, simp s ⊆ H, s ≠ σ} ∪ aσ̇` of `Γ'` used in the
`L7` call of §12. -/
def coneK (Γ : Cx N) (H : Set (E N)) (σ : Finset (E N)) (a : E N) : Set (E N) :=
  (⋃ s ∈ {s : Finset (E N) | s ∈ Γ.faces ∧ simp s ⊆ H ∧ s ≠ σ}, simp s) ∪ coneBd a σ

@[simp] theorem coneBd_eq_floorOf (a : E N) (σ : Finset (E N)) :
    coneBd a σ = floorOf {a} σ := by
  simp only [coneBd, floorOf, Finset.singleton_union]

@[simp] theorem coneBd_empty (a : E N) : coneBd a (∅ : Finset (E N)) = ∅ := by
  simp [coneBd]

end Work.Engulf.Chain
