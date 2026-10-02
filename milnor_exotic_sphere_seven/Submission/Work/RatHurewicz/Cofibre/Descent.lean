import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Maps

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Descent along the cofibre quotient

`cofibre ι` is the quotient of `E ⊕ Cone F` by the gluing relation.  The open cover
`(cofibreU ι, cofibreV ι)` is the image of the two "pieces"

* `cofibreU ι` ← `(Sum.inl '' univ) ∪ (Sum.inr '' {h < 1/2})`,
* `cofibreV ι` ← `Sum.inr '' {0 < h}`,

which are unions of the **clopen** summands of `E ⊕ Cone F`.  This file records those
identifications (`preimage_cofibreU`, `preimage_cofibreV`) — the `hS` hypotheses of the descent
lemma for a piecewise map — together with the description of the two pieces themselves
(`cofibreU_eq_image`, `cofibreV_eq_image`), which is what makes the piecewise continuity check
tractable.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- The preimage of `cofibreV ι` in `E ⊕ Cone F` is the punctured cone. -/
theorem preimage_cofibreV (ι : C(F, E)) :
    (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι
      = Sum.inr '' {y : Work.Stems.Cone F | (0 : unitInterval) < coneHeight y} := by
  ext a
  constructor
  · intro ha
    rcases a with e | y
    · exfalso
      have h1 : cofibreIncl ι e ∈ cofibreV ι := ha
      rw [mem_cofibreV_iff, cofibreHeight_incl] at h1
      exact absurd h1 (not_lt.mpr le_rfl)
    · exact ⟨y, (mem_cofibreV_coneIncl_iff ι y).mp ha, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (mem_cofibreV_coneIncl_iff ι y).mpr hy

/-- The preimage of `cofibreU ι` in `E ⊕ Cone F` is `E` together with the half-open cone. -/
theorem preimage_cofibreU (ι : C(F, E)) :
    (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι
      = Sum.inl '' (Set.univ : Set E) ∪
        Sum.inr '' {y : Work.Stems.Cone F | coneHeight y < cofibreHalf} := by
  ext a
  constructor
  · intro ha
    rcases a with e | y
    · exact Or.inl ⟨e, trivial, rfl⟩
    · exact Or.inr ⟨y, (mem_cofibreU_coneIncl_iff ι y).mp ha, rfl⟩
  · rintro (⟨e, -, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact cofibreIncl_mem_cofibreU ι e
    · exact (mem_cofibreU_coneIncl_iff ι y).mpr hy

/-- `cofibreV ι` is the image of the punctured cone. -/
theorem cofibreV_eq_image (ι : C(F, E)) :
    cofibreV ι = cofibreInclCone ι '' {y : Work.Stems.Cone F | (0 : unitInterval) < coneHeight y} := by
  ext z
  constructor
  · intro hz
    induction z using Quotient.inductionOn with
    | h a =>
      rcases a with e | y
      · exfalso
        have h1 : cofibreIncl ι e ∈ cofibreV ι := hz
        rw [mem_cofibreV_iff, cofibreHeight_incl] at h1
        exact absurd h1 (not_lt.mpr le_rfl)
      · exact ⟨y, (mem_cofibreV_coneIncl_iff ι y).mp hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (mem_cofibreV_coneIncl_iff ι y).mpr hy

/-- `cofibreU ι` is the image of `E` together with the half-open cone. -/
theorem cofibreU_eq_image (ι : C(F, E)) :
    cofibreU ι = cofibreIncl ι '' (Set.univ : Set E) ∪
      cofibreInclCone ι '' {y : Work.Stems.Cone F | coneHeight y < cofibreHalf} := by
  ext z
  constructor
  · intro hz
    induction z using Quotient.inductionOn with
    | h a =>
      rcases a with e | y
      · exact Or.inl ⟨e, trivial, rfl⟩
      · exact Or.inr ⟨y, (mem_cofibreU_coneIncl_iff ι y).mp hz, rfl⟩
  · rintro (⟨e, -, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact cofibreIncl_mem_cofibreU ι e
    · exact (mem_cofibreU_coneIncl_iff ι y).mpr hy


/-! ## The two pieces of the preimage are open (indeed clopen) -/

theorem isOpen_sumInl_cofibre :
    IsOpen (Sum.inl '' (Set.univ : Set E) : Set (E ⊕ Work.Stems.Cone F)) := by
  rw [Set.image_univ]
  exact isOpen_range_inl

theorem isOpen_sumInr_cofibre {T : Set (Work.Stems.Cone F)} (hT : IsOpen T) :
    IsOpen (Sum.inr '' T : Set (E ⊕ Work.Stems.Cone F)) :=
  isOpenMap_inr T hT

end

end Work.RatHurewicz
