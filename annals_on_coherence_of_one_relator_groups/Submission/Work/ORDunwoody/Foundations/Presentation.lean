/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Turning `Group.IsFinitelyPresented` into concrete presentation data

The Dunwoody construction starts from a *finite presentation* of `G`.  Mathlib's
`Group.IsFinitelyPresented G` says `∃ n φ : FreeGroup (Fin n) →* G, Surjective φ ∧
φ.ker.IsFinitelyNormallyGenerated`, and `IsFinitelyNormallyGenerated N` says
`∃ S, S.Finite ∧ normalClosure S = N`.  This file repackages that into the data used by the
construction: a rank `n`, a surjection `π`, and a finite set of relators whose normal closure
is the whole kernel.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

/-- Concrete finite presentation data for a group `G`: a finite free group `F_n` mapping onto
`G` with a finite normally generating set for the kernel. -/
structure FinPresentation (G : Type u) [Group G] where
  /-- Number of generators. -/
  n : ℕ
  /-- The quotient map from the free group on `n` generators. -/
  π : FreeGroup (Fin n) →* G
  /-- It is surjective. -/
  surj : Function.Surjective π
  /-- The finite set of relators. -/
  rel : Finset (FreeGroup (Fin n))
  /-- Their normal closure is the kernel. -/
  ker_eq : MonoidHom.ker π = Subgroup.normalClosure (rel : Set (FreeGroup (Fin n)))

/-- **Concrete presentation data from `Group.IsFinitelyPresented`.** -/
theorem exists_finPresentation (G : Type u) [Group G] (h : Group.IsFinitelyPresented G) :
    Nonempty (FinPresentation G) := by
  obtain ⟨n, π, hsurj, S, hSfin, hS⟩ := h.out
  refine ⟨⟨n, π, hsurj, hSfin.toFinset, ?_⟩⟩
  rw [Set.Finite.coe_toFinset, hS]

end Work.ORDunwoody
