import Mathlib

/-!
# Cycles whose homology class vanishes are boundaries

In a chain complex of `ℤ`-modules, the kernel of the canonical map from cycles to homology
(`homologyπ`) is exactly the image of the "boundary" map `toCycles`.  Concretely: a cycle `ζ`
in degree `j + 1` whose homology class is zero is the boundary `toCycles w` of some chain
`w` in degree `j + 2`.

The proof is the corresponding statement about short complexes: the homology of a short complex
`S` is the cokernel of `S.toCycles : S.X₁ ⟶ S.cycles`, and in `ModuleCat ℤ` the kernel of a
cokernel projection is the range of the map.  We use `HomologicalComplex.homologyIsCokernel`
to identify the homology of `C` in degree `j + 1` with the cokernel of
`C.toCycles (j + 2) (j + 1) : C.X (j + 2) ⟶ C.cycles (j + 1)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Compact.Noncompact

universe u

/-- In the category of `ℤ`-modules, the kernel of the cokernel projection of `f` is the range
of `f`. -/
lemma cokernel_π_eq_zero_iff {M N : ModuleCat.{u} ℤ} (f : M ⟶ N) (x : N) :
    cokernel.π f x = 0 ↔ x ∈ LinearMap.range f.hom := by
  constructor
  · intro hx
    rw [← Submodule.Quotient.mk_eq_zero,
      ← ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply f x, hx, map_zero]
  · rintro ⟨w, rfl⟩
    have : (f ≫ cokernel.π f) w = 0 := by rw [cokernel.condition]; rfl
    rwa [ConcreteCategory.comp_apply] at this

/-- If `g : N ⟶ P` is a cokernel of `f : M ⟶ N` (witnessed by any colimit cokernel cofork),
then the kernel of `g` is the range of `f`. -/
lemma cokernelπ_eq_zero_iff_range {M N P : ModuleCat.{u} ℤ} {f : M ⟶ N} {g : N ⟶ P}
    (h : f ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g h)) (x : N) :
    g x = 0 ↔ x ∈ LinearMap.range f.hom := by
  constructor
  · intro hx
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hc (cokernel.π f) (cokernel.condition f)
    rw [CokernelCofork.π_ofπ] at hl
    have h2 : cokernel.π f x = 0 := by
      rw [← hl, ConcreteCategory.comp_apply, hx, map_zero]
    exact (cokernel_π_eq_zero_iff f x).mp h2
  · rintro ⟨w, rfl⟩
    have : (f ≫ g) w = 0 := by rw [h]; rfl
    rwa [ConcreteCategory.comp_apply] at this

theorem exists_toCycles_eq_of_homologypi_eq_zero {C : ChainComplex (ModuleCat ℤ) ℕ} (j : ℕ)
    (ζ : C.cycles (j + 1)) (h : C.homologyπ (j + 1) ζ = 0) :
    ∃ w : C.X (j + 2), C.toCycles (j + 2) (j + 1) w = ζ := by
  have hprev : (ComplexShape.down ℕ).prev (j + 1) = j + 2 := by simp [ChainComplex.prev]
  have hc := C.homologyIsCokernel (i := j + 2) (j := j + 1) hprev
  obtain ⟨w, hw⟩ :=
    (cokernelπ_eq_zero_iff_range (C.toCycles_comp_homologyπ (j + 2) (j + 1)) hc ζ).mp h
  exact ⟨w, hw⟩

end Work.Compact.Noncompact
