import Mathlib
import Submission.Work.CFTLib.Basic

/-!
# `conjSup` of a finite Galois extension is finite and Galois over the base field

Let `F` be a number field, `K'/F` a finite Galois extension inside an algebraic closure `A`, and
`L'/K'` a finite Galois extension.  `Work.CFTLib.conjSup p K' L'` is the compositum, inside `A`,
of the conjugates `σ(L')` for `σ : Gal(K'/F)` (each lifted to an `F`-automorphism of `A` by
`AlgEquiv.liftNormal`).

The main point of this file is that this compositum is exactly the normal closure of `L'` over
`F`:
* every `F`-embedding `L' →ₐ[F] A` lands inside one of the chosen conjugates
  (`fieldRange_le_conjSup`), because restricting it to `K'` and using the normality of `K'/F`
  exhibits it as a conjugate of a chosen lift along a `K'`-automorphism, which lands inside `L'`
  by normality of `L'/K'`;
* conversely each conjugate is contained in the normal closure by definition.

Consequently `conjSup p K' L'` is finite dimensional and Galois over `F`, being a normal closure
of a finite extension of a number field.
-/

set_option linter.style.haveILetI false

open IntermediateField

namespace Work.CFTLib.ConjSup

/-- Every `F`-embedding of `L'` into the algebraic closure lands in one of the conjugate fields
occurring in `conjSup p K' L'`. -/
theorem fieldRange_le_conjSup (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    (hLgal : IsGalois ↥K' L')
    (f : ↥(L'.restrictScalars F) →ₐ[F] AlgebraicClosure F) :
    f.fieldRange ≤ conjSup p K' L' := by
  -- `K'` is contained in `L'`
  have hKL : K' ≤ L'.restrictScalars F := by
    intro x hx
    simpa using L'.algebraMap_mem (⟨x, hx⟩ : ↥K')
  let incl : ↥K' →ₐ[F] ↥(L'.restrictScalars F) := IntermediateField.inclusion hKL
  -- the restriction of `f` to `K'`
  let rho : ↥K' →ₐ[F] AlgebraicClosure F := f.comp incl
  have hrho : rho.fieldRange = K' := AlgHom.fieldRange_of_normal rho
  -- the corresponding element of `Gal(K'/F)`, and a chosen lift to `Gal(A/F)`
  let σ : ↥K' ≃ₐ[F] ↥K' := rho.restrictNormal' ↥K'
  let g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ.liftNormal (AlgebraicClosure F)
  have hσk : ∀ k : ↥K', σ k = (rho.restrictNormal ↥K') k := fun k => rfl
  have hσ : ∀ k : ↥K', g (algebraMap ↥K' (AlgebraicClosure F) k) = rho k := by
    intro k
    have h1 := AlgEquiv.liftNormal_commutes σ (AlgebraicClosure F) k
    have h2 := AlgHom.restrictNormal_commutes rho ↥K' k
    rw [show algebraMap ↥K' ↥K' k = k from rfl] at h2
    rw [h1, hσk k]
    exact h2
  -- `g⁻¹ ∘ f` fixes `K'` pointwise
  let h0 : ↥(L'.restrictScalars F) →ₐ[F] AlgebraicClosure F := g.symm.toAlgHom.comp f
  have hlin : ∀ k : ↥K', h0 (algebraMap ↥K' ↥L' k) = algebraMap ↥K' (AlgebraicClosure F) k := by
    intro k
    have hk : (algebraMap ↥K' ↥L' k : ↥(L'.restrictScalars F)) = incl k := Subtype.ext rfl
    rw [hk]
    change g.symm (f (incl k)) = algebraMap ↥K' (AlgebraicClosure F) k
    have hf : f (incl k) = rho k := rfl
    rw [hf, ← hσ k]
    exact g.symm_apply_apply _
  -- hence it is an `↥K'`-algebra homomorphism, whose range is contained in `L'` by normality
  let h' : ↥L' →ₐ[↥K'] AlgebraicClosure F :=
    { toFun := ⇑h0
      map_one' := map_one h0
      map_mul' := map_mul h0
      map_zero' := map_zero h0
      map_add' := map_add h0
      commutes' := fun k => hlin k }
  have h'fr : h'.fieldRange = L' := AlgHom.fieldRange_of_normal h'
  -- consequently `f = g ∘ h'` lands in the image of the chosen lift `g`
  refine le_trans ?_ (le_iSup (fun σ' : ↥K' ≃ₐ[F] ↥K' =>
    (L'.restrictScalars F).map (σ'.liftNormal (AlgebraicClosure F)).toAlgHom) σ)
  intro y hy
  obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
  have hxmem : (h' x : AlgebraicClosure F) ∈ L' := by
    have : h' x ∈ h'.fieldRange := Set.mem_range_self x
    rwa [h'fr] at this
  rw [mem_map]
  refine ⟨(h0 x : AlgebraicClosure F), hxmem, ?_⟩
  show g (h0 x) = f x
  exact g.apply_symm_apply (f x)

/-- The compositum of the conjugates of a finite Galois `L'/K'` over a finite Galois `K'/F` is
finite dimensional and Galois over `F`. -/
theorem finiteDimensional_isGalois (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] [IsGalois F K']
    (L' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L']
    (hLgal : IsGalois ↥K' L') :
    FiniteDimensional F ↥(conjSup p K' L') ∧ IsGalois F ↥(conjSup p K' L') := by
  have hfd : FiniteDimensional F ↥L' := Module.Finite.trans ↥K' ↥L'
  haveI : FiniteDimensional F ↥(L'.restrictScalars F) := hfd
  -- `conjSup` is the normal closure of `L'` over `F`
  have heq : conjSup p K' L'
      = normalClosure F ↥(L'.restrictScalars F) (AlgebraicClosure F) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun σ => ?_
      intro y hy
      rw [mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact AlgHom.fieldRange_le_normalClosure
        (((σ.liftNormal (AlgebraicClosure F)).toAlgHom).comp (L'.restrictScalars F).val)
        ⟨⟨x, hx⟩, rfl⟩
    · refine (normalClosure_le_iff (F := F) (K := ↥(L'.restrictScalars F))
        (L := AlgebraicClosure F) (K' := conjSup p K' L')).mpr ?_
      intro f
      exact fieldRange_le_conjSup F p K' L' hLgal f
  rw [heq]
  exact ⟨normalClosure.is_finiteDimensional F ↥(L'.restrictScalars F) (AlgebraicClosure F),
    IsGalois.normalClosure F ↥(L'.restrictScalars F) (AlgebraicClosure F)⟩

end Work.CFTLib.ConjSup
