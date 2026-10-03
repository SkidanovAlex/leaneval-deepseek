/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Concrete data for the Cayley complex of a finite presentation

Given a finite presentation `P : FinPresentation G` and a cocompact `G`-tree `T`, the
Dunwoody resolution is built from the universal cover `X̃` of the presentation 2-complex,
subdivided along the geodesics of `T`.  This file collects the concrete data: a basepoint of
`T`, the images in `G` of the generators, and geodesics of `T` joining the basepoint to each
generator translate.
-/
import Mathlib
import Submission.Work.ORDunwoody.Foundations.Presentation
import Submission.Work.ORDunwoody.Tracks.Geodesic
import Submission.Work.ORDunwoody.Tracks.Barycentric

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

variable {G : Type u} [Group G]

/-- A basepoint of a nonempty tree. -/
noncomputable def basePt {V : Type u} {T : SimpleGraph V} (hT : T.IsTree) : V :=
  Classical.choice hT.connected.nonempty

/-- The image in `G` of the `i`-th generator of a finite presentation. -/
def FinPresentation.gen (P : FinPresentation G) (i : Fin P.n) : G := P.π (FreeGroup.of i)

/-- The generators generate. -/
theorem FinPresentation.closure_gen (P : FinPresentation G) :
    Subgroup.closure (Set.range P.gen) = ⊤ := by
  have hkey : Set.range P.gen = P.π '' (Set.range (FreeGroup.of (α := Fin P.n))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [hkey, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr P.surj

variable {V : Type u} [MulAction G V] (T : GTree G V)

/-- The geodesic of `T` joining `u` to `v`, enumerated as `x 0, …, x d`.  Wrapper around
`exists_geodesic` recording only what the subdivision needs. -/
theorem exists_Tgeodesic (u v : V) :
    ∃ (d : ℕ) (x : Fin (d + 1) → V),
      x 0 = u ∧ x (Fin.last d) = v ∧
      (∀ i : Fin d, T.Adj (x i.castSucc) (x i.succ)) ∧ Function.Injective x :=
  exists_geodesic T.graph T.isTree u v

end Work.ORDunwoody
