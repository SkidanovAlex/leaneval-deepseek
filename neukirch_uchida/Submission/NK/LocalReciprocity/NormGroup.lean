import Mathlib

/-!
# Norm groups of units of field extensions

For a field extension `E / F` we write `N_{E/F} Eˣ ⊆ Fˣ` for the image of the norm map
`Algebra.norm F : E →* F` on unit groups.  This file sets up this group, its basic API, and the
two structural properties that the local reciprocity theory needs:

* **transitivity** `N_{M/F} Mˣ = N_{E/F}(N_{M/E} Mˣ)` for a tower `F ⊆ E ⊆ M`
  (`normGroup_trans`), the first axiom of a class formation;
* **invariance under `F`-algebra isomorphisms** (`normGroup_eq_of_algEquiv`), which makes the
  norm group of an abstract local extension well defined.

The norm group is the basic object of local class field theory: the local reciprocity law says that
the canonical (Frobenius-normalised) Artin map induces an isomorphism
`Fˣ ⧸ N_{E/F} Eˣ ≃* Gal(E/F)` for `E/F` finite abelian.  Everything in
`Submission/Work/LocalReciprocity/` is phrased in terms of `normGroup`.
-/

namespace NK.LocalReciprocity

universe u

noncomputable section

variable {F E M F' : Type*}

section Basic

variable [Field F] [Field E] [Algebra F E]

/-- **The norm group** `N_{E/F} Eˣ`, the image of the norm map on units.  For `E/F` finite Galois
its quotient `Fˣ ⧸ N_{E/F} Eˣ` is dual to the abelianised Galois group by local class field
theory. -/
def normGroup (F E : Type*) [Field F] [Field E] [Algebra F E] : Subgroup Fˣ :=
  (Units.map (Algebra.norm F : E →* F)).range

@[simp]
theorem normGroup_eq_range :
    normGroup F E = (Units.map (Algebra.norm F : E →* F)).range := rfl

theorem mem_normGroup_iff (x : Fˣ) :
    x ∈ normGroup F E ↔ ∃ y : Eˣ, Algebra.norm F (y : E) = (x : F) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [← hy, Units.coe_map]⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Units.ext hy⟩

/-- Norms from above are norms from below: `N_{M/F} Mˣ ≤ N_{E/F} Eˣ` for a tower
`F ⊆ E ⊆ M` (the inclusion behind the first class-formation axiom). -/
theorem normGroup_le_of_tower [Field M] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] : normGroup F M ≤ normGroup F E := by
  intro x hx
  rw [mem_normGroup_iff] at hx ⊢
  obtain ⟨z, hz⟩ := hx
  refine ⟨Units.map (Algebra.norm E : M →* E) z, ?_⟩
  rw [← hz, Units.coe_map]
  have hfree₁ := Module.Free.of_divisionRing F E
  have hfree₂ := Module.Free.of_divisionRing E M
  exact Algebra.norm_norm (R := F) (S := E) (A := M) (a := (z : M))

end Basic

section Trans

variable [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]

/-- **Transitivity of the norm group** (the first axiom of a class formation):

  `N_{M/F} Mˣ = N_{E/F}(N_{M/E} Mˣ)`

for a tower of fields `F ⊆ E ⊆ M`.  (No finiteness hypothesis is needed: the identity is the
transitivity `Algebra.norm F ∘ Algebra.norm E = Algebra.norm F` of the norm map, in the form
`Algebra.norm_norm`.) -/
theorem normGroup_trans :
    normGroup F M = (normGroup E M).map (Units.map (Algebra.norm F : E →* F)) := by
  haveI := Module.Free.of_divisionRing F E
  haveI := Module.Free.of_divisionRing E M
  have hcomp : (Algebra.norm F : M →* F) =
      (Algebra.norm F : E →* F).comp (Algebra.norm E : M →* E) :=
    MonoidHom.ext fun x =>
      (Algebra.norm_norm (R := F) (S := E) (A := M) (a := x)).symm
  rw [normGroup, normGroup, hcomp, Units.map_comp, MonoidHom.range_comp]

end Trans

section AlgEquiv

variable [Field F] [Field E] [Field F'] [Algebra F E] [Algebra F F']

/-- **Invariance of the norm group under an `F`-algebra isomorphism.**  If `e : E ≃ₐ[F] F'` then
the norms from `E` and from `F'` have the same image in `Fˣ`. -/
theorem normGroup_eq_of_algEquiv (e : E ≃ₐ[F] F') :
    normGroup F E = normGroup F F' := by
  rw [normGroup, normGroup]
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    refine ⟨Units.mapEquiv e.toRingEquiv y, ?_⟩
    refine Units.ext ?_
    rw [Units.coe_map, Units.coe_mapEquiv, Units.coe_map]
    exact Algebra.norm_eq_of_algEquiv e (y : E)
  · rintro x ⟨y, rfl⟩
    refine ⟨Units.mapEquiv e.symm.toRingEquiv y, ?_⟩
    refine Units.ext ?_
    rw [Units.coe_map, Units.coe_mapEquiv, Units.coe_map]
    exact Algebra.norm_eq_of_algEquiv e.symm (y : F')

end AlgEquiv

end

end NK.LocalReciprocity
