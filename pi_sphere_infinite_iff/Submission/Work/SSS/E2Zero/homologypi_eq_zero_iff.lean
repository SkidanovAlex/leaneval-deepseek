import Mathlib

namespace Work.SSS.E2Zero

open CategoryTheory CategoryTheory.Limits

section

universe v

/-- In `ModuleCat ℤ`, the projection onto the cokernel of a morphism `f` vanishes at an
element `x` of the target exactly when `x` lies in the range of `f`. -/
lemma cokernel_π_eq_zero_iff {G H : ModuleCat.{v} ℤ} (f : G ⟶ H) (x : H) :
    cokernel.π f x = 0 ↔ ∃ g : G, f g = x := by
  have hinj : Function.Injective (ConcreteCategory.hom (ModuleCat.cokernelIsoRangeQuotient f).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  rw [← hinj.eq_iff, map_zero]
  rw [ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply]
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]

end

/-- A cycle `z` of a chain complex of `ℤ`-modules in degree `i` has zero homology class in `K.homology i` if and only if it is a boundary: `K.d (i+1) i w = K.iCycles i z` for some `w`.
Roadmap: `K.homology i` is the cokernel of `K.toCycles (i+1) i : K.X (i+1) ⟶ K.cycles i` (`HomologicalComplex.homologyIsCokernel`, with `prev i = i+1` from `ComplexShape.prev_eq'`), so the kernel of `K.homologyπ i` is the range of `K.toCycles (i+1) i`; the range is computed elementwise with `HomologicalComplex.toCycles_i : K.toCycles i j ≫ K.iCycles j = K.d i j` and the monomorphism instance for `K.iCycles i`. The reverse implication is `HomologicalComplex.toCycles_comp_homologyπ`. Useful: `ShortComplex.moduleCatLeftHomologyData_π_hom`, `ShortComplex.moduleCatCyclesIso_inv_π`, `ShortComplex.moduleCatCyclesIso_inv_iCycles`. -/
theorem homologypi_eq_zero_iff {K : ChainComplex (ModuleCat ℤ) ℕ} (i : ℕ) (z : K.cycles i) :
    K.homologyπ i z = 0 ↔ ∃ w : K.X (i + 1), K.d (i + 1) i w = K.iCycles i z := by
  -- `K.homologyπ i` and `cokernel.π (K.toCycles (i+1) i)` are two cokernels of the same map
  have hcoker : K.homologyπ i z = 0 ↔ cokernel.π (K.toCycles (i + 1) i) z = 0 := by
    have hi : (ComplexShape.down ℕ).prev i = i + 1 := ChainComplex.prev ℕ i
    let φ : K.homology i ⟶ cokernel (K.toCycles (i + 1) i) :=
      (K.homologyIsCokernel (i + 1) i hi).desc
        (CokernelCofork.ofπ (cokernel.π (K.toCycles (i + 1) i)) (cokernel.condition _))
    have hφ : K.homologyπ i ≫ φ = cokernel.π (K.toCycles (i + 1) i) :=
      Cofork.IsColimit.π_desc (K.homologyIsCokernel (i + 1) i hi)
    let ψ : cokernel (K.toCycles (i + 1) i) ⟶ K.homology i :=
      cokernel.desc (K.toCycles (i + 1) i) (K.homologyπ i) (K.toCycles_comp_homologyπ (i + 1) i)
    have hψ : cokernel.π (K.toCycles (i + 1) i) ≫ ψ = K.homologyπ i :=
      cokernel.π_desc _ _ _
    constructor
    · intro hz
      have h := congrArg (fun (g : K.cycles i ⟶ cokernel (K.toCycles (i + 1) i)) => g z) hφ
      simp only [ConcreteCategory.comp_apply] at h
      rw [hz, map_zero] at h
      exact h.symm
    · intro hz
      have h := congrArg (fun (g : K.cycles i ⟶ K.homology i) => g z) hψ
      simp only [ConcreteCategory.comp_apply] at h
      rw [hz, map_zero] at h
      exact h.symm
  -- `K.toCycles (i+1) i w = z` iff `K.d (i+1) i w = K.iCycles i z`, since `iCycles` is mono
  have hkey : (∃ w : K.X (i + 1), K.toCycles (i + 1) i w = z) ↔
      ∃ w : K.X (i + 1), K.d (i + 1) i w = K.iCycles i z := by
    have hinj : Function.Injective (ConcreteCategory.hom (K.iCycles i)) :=
      (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    have hti : ∀ w : K.X (i + 1), K.iCycles i (K.toCycles (i + 1) i w) = K.d (i + 1) i w := by
      intro w
      have h := congrArg (fun (g : K.X (i + 1) ⟶ K.X i) => (ConcreteCategory.hom g) w)
        (HomologicalComplex.toCycles_i K (i + 1) i)
      simp only [ConcreteCategory.comp_apply] at h
      exact h
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by rw [← hti w, hw]⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, hinj (by rw [hti w, hw])⟩
  exact hcoker.trans ((cokernel_π_eq_zero_iff (K.toCycles (i + 1) i) z).trans hkey)

end Work.SSS.E2Zero
