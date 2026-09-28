import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.sat_span
import Submission.Work.Q44Geom.ratSpan_finrank
import Submission.Work.Q44Geom.vanish_ratSpan
import Submission.Work.Q44Geom.formOf_eval

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-- A lattice vector of `L` is a rational vector of `ratSpan L`. -/
lemma toRatLM_mem_ratSpan {L : Submodule ℤ (Fin 5 → ℤ)} {v : Fin 5 → ℤ} (hv : v ∈ L) :
    toRatLM v ∈ ratSpan L := by
  unfold ratSpan
  exact Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩

/-- `ratSpan` is injective on *primitive* lattices: a primitive lattice is determined by its
rational span, since it is exactly the set of integral vectors lying in that span. -/
lemma ratSpan_injective_of_isPrimLat {L₁ L₂ : Submodule ℤ (Fin 5 → ℤ)}
    (h₁ : Work.HP.IsPrimLat L₁) (h₂ : Work.HP.IsPrimLat L₂) (h : ratSpan L₁ = ratSpan L₂) :
    L₁ = L₂ := by
  refine le_antisymm ?_ ?_
  · intro v hv
    exact (sat_span L₂ h₂ v).mpr (h ▸ (sat_span L₁ h₁ v).mp hv)
  · intro v hv
    exact (sat_span L₁ h₁ v).mpr (h.symm ▸ (sat_span L₂ h₂ v).mp hv)

/-- The lattice `L ↦ ratSpan L` is injective on the primitive lattices `L ∈ Sset c s`, and the
image of any such `L` containing two integral vectors `b₁, b₂` is an isotropic `3`-plane through
`toRatLM b₁, toRatLM b₂`.  Hence the number of elements of any `T ⊆ Sset c s` whose members all
contain `b₁` and `b₂` is at most the number of those planes. -/
lemma ncard_le_planeSet_ncard (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ)
    (b₁ b₂ : Fin 5 → ℤ) (T : Set (Submodule ℤ (Fin 5 → ℤ)))
    (hT : T ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Work.Q44Geom.Sset c s ∧ b₁ ∈ L ∧ b₂ ∈ L})
    (hP : ({P : Submodule ℚ (Fin 5 → ℚ) | Module.finrank ℚ P = 3 ∧
        Work.Q44Geom.toRatLM b₁ ∈ P ∧ Work.Q44Geom.toRatLM b₂ ∈ P ∧
        ∀ x ∈ P, MvPolynomial.eval x (Work.Q44Geom.f44 c) = 0}).Finite) :
    T.ncard ≤ ({P : Submodule ℚ (Fin 5 → ℚ) | Module.finrank ℚ P = 3 ∧
        Work.Q44Geom.toRatLM b₁ ∈ P ∧ Work.Q44Geom.toRatLM b₂ ∈ P ∧
        ∀ x ∈ P, MvPolynomial.eval x (Work.Q44Geom.f44 c) = 0}).ncard := by
  -- count `T` through the injective map `L ↦ ratSpan L`, whose image consists of isotropic
  -- `3`-planes through `toRatLM b₁` and `toRatLM b₂`
  refine Set.ncard_le_ncard_of_injOn
    (t := {P : Submodule ℚ (Fin 5 → ℚ) | Module.finrank ℚ P = 3 ∧
      Work.Q44Geom.toRatLM b₁ ∈ P ∧ Work.Q44Geom.toRatLM b₂ ∈ P ∧
      ∀ x ∈ P, MvPolynomial.eval x (Work.Q44Geom.f44 c) = 0}) (fun L => ratSpan L) ?_ ?_ hP
  · -- every `L ∈ T` has `ratSpan L` in the plane set
    rintro L hL
    obtain ⟨hS, hb₁, hb₂⟩ := hT hL
    obtain ⟨hprim, hrk, hlam, hvanish⟩ := hS
    exact ⟨ratSpan_finrank L hrk, toRatLM_mem_ratSpan hb₁, toRatLM_mem_ratSpan hb₂,
      fun x hx => vanish_ratSpan c L hvanish hx⟩
  · -- `ratSpan` is injective on `T`, since the members of `T` are primitive
    rintro L₁ hL₁ L₂ hL₂ heq
    obtain ⟨hS₁, -, -⟩ := hT hL₁
    obtain ⟨hS₂, -, -⟩ := hT hL₂
    obtain ⟨hprim₁, -, -, -⟩ := hS₁
    obtain ⟨hprim₂, -, -, -⟩ := hS₂
    exact ratSpan_injective_of_isPrimLat hprim₁ hprim₂ heq

end Work.Q44Geom
