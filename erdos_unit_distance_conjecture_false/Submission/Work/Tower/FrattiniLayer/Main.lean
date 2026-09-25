import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.baseChange_unramified
import Submission.Work.Tower.FrattiniLayer.sup_left_injective
import Submission.Work.Tower.FrattiniLayer.finite_cubeIdealSubgroup_quotient
import Submission.Work.Tower.FrattiniLayer.finite_cubicUnramifiedSet_of_zeta_of_finite_quotient
import Submission.Work.Tower.FrattiniLayer.finite_cubicUnramifiedSet_of_le
import Submission.Work.Tower.FrattiniLayer.exists_primitiveRoot_three_of_isAlgClosed
import Submission.Work.Tower.FrattiniLayer.adjoin_primitiveRoot_three
import Submission.Work.Tower.FrattiniLayer.dvd_discr_of_isPrimitiveRoot_mem
import Submission.Work.Tower.FrattiniLayer.frattiniLayer_properties
import Submission.Work.Tower.FrattiniLayer.frattiniLayer_galoisGroup
import Submission.Work.Tower.FrattiniLayer.frattiniLayer_universal
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom

/-!
# The Frattini layer of the unramified pro-3 group of a number field

This is the main file of the subproject.  For a number field `F`, the **Frattini layer** is the
compositum (computed in a fixed extension field `Ω`)
`frattiniLayer F Ω = ⨆ M ∈ cubicUnramifiedSet F Ω, M`
of all cubic everywhere unramified Galois extensions of `F` inside `Ω`.  It is the fixed field of
the Frattini subgroup of `Gal(F^{ur,3}/F)`, i.e. the maximal everywhere unramified elementary
abelian `3`-extension of `F`.

The mathematical content, all of it formalized here, is

1. `Work.Tower.FrattiniLayer.finite_cubicUnramifiedSet` (Kummer theory over `F⟮ζ₃⟯`, Dirichlet's
   unit theorem, finiteness of the class group): there are only **finitely many** cubic everywhere
   unramified Galois extensions of `F`;
2. `Work.Tower.FrattiniLayer.frattiniLayer_properties`: the compositum is a finite, Galois,
   everywhere unramified extension of `F`;
3. `Work.Tower.FrattiniLayer.frattiniLayer_galoisGroup`: `Gal(Frattini layer/F)` is an elementary
   abelian `3`-group;
4. `Work.Tower.FrattiniLayer.frattiniLayer_universal`: every finite everywhere unramified
   elementary abelian `3`-extension of `F` embeds into the Frattini layer over `F`;
5. `Work.Tower.exists_frattini_layer`: the deliverable theorem;
6. `Work.Tower.FrattiniLayer.splitsCompletelyIn_frattiniLayer`: a prime splitting completely in
   the Frattini layer splits completely in every finite everywhere unramified elementary abelian
   `3`-extension of `F`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace FrattiniLayer

/-- **Finiteness of the cubic everywhere unramified layer.**  If `Ω` is any field containing a
primitive cube root of unity `ζ` which does not already lie in `F`, then there are only finitely
many intermediate fields `M ⊆ Ω` of `F` which are Galois of degree `3` over `F` and unramified at
every finite prime. -/
theorem finite_cubicUnramifiedSet {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ 3 ∧ ζ ∉ (⊥ : IntermediateField F Ω)) :
    (cubicUnramifiedSet F Ω).Finite := by
  obtain ⟨ζ, hζp, hζnf⟩ := hζ
  obtain ⟨hgal, hfr, hpr⟩ := adjoin_primitiveRoot_three ζ hζp hζnf
  haveI : IsGalois F (IntermediateField.adjoin F {ζ}) := hgal
  refine finite_cubicUnramifiedSet_of_le (Z := IntermediateField.adjoin F {ζ}) hfr hpr ?_
  haveI : Module.Finite F ↥(IntermediateField.adjoin F {ζ}) :=
    Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  haveI : NumberField ↥(IntermediateField.adjoin F {ζ}) :=
    NumberField.of_module_finite F ↥(IntermediateField.adjoin F {ζ})
  exact finite_cubicUnramifiedSet_of_zeta_of_finite_quotient hpr
    (finite_cubeIdealSubgroup_quotient ↥(IntermediateField.adjoin F {ζ}))

/-- **Finiteness of the cubic everywhere unramified layer, unconditional form.**  If `Ω`
contains *any* primitive cube root of unity (which it need not, but which is the case for `Ω`
algebraically closed), then the set of cubic everywhere unramified Galois extensions of `F`
inside `Ω` is finite.  This strengthens `finite_cubicUnramifiedSet` by not requiring the cube
root of unity to be outside `F`. -/
theorem finite_cubicUnramifiedSet_of_zeta {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ 3) :
    (cubicUnramifiedSet F Ω).Finite := by
  by_cases h : ∃ ζ : Ω, IsPrimitiveRoot ζ 3 ∧ ζ ∉ (⊥ : IntermediateField F Ω)
  · exact finite_cubicUnramifiedSet h
  · -- Every primitive cube root of unity in `Ω` lies in `F`; then `F` itself contains one and the
    -- Kummer counting applies directly over `F`.
    obtain ⟨ζ, hζp⟩ := hζ
    have hmem : ζ ∈ (⊥ : IntermediateField F Ω) := by
      by_contra hcon
      exact h ⟨ζ, hζp, hcon⟩
    obtain ⟨f, hf⟩ := IntermediateField.mem_bot.mp hmem
    have hf' : IsPrimitiveRoot f 3 :=
      (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap F Ω)
        (FaithfulSMul.algebraMap_injective F Ω)).mp (hf ▸ hζp)
    have hpr : (primitiveRoots 3 F).Nonempty :=
      ⟨f, (mem_primitiveRoots (by norm_num)).mpr hf'⟩
    exact finite_cubicUnramifiedSet_of_zeta_of_finite_quotient (L := F) (Ω := Ω) hpr
      (finite_cubeIdealSubgroup_quotient F)

/-- **A primitive cube root of unity is not rational over `F` when `3 ∤ disc F`.** -/
theorem not_mem_bot_of_isPrimitiveRoot {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (h3 : ¬ (3 : ℤ) ∣ NumberField.discr F) {ζ : Ω} (hζ : IsPrimitiveRoot ζ 3) :
    ζ ∉ (⊥ : IntermediateField F Ω) := by
  intro hmem
  obtain ⟨f, hf⟩ := IntermediateField.mem_bot.mp hmem
  have hf' : IsPrimitiveRoot f 3 :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap F Ω)
      (FaithfulSMul.algebraMap_injective F Ω)).mp (hf ▸ hζ)
  exact h3 (dvd_discr_of_isPrimitiveRoot_mem F f hf')

end FrattiniLayer

open FrattiniLayer

/-- **The Frattini layer exists** (Erdős unit-distance paper, Section 3).  For a number field `F`
with `3 ∤ disc F` there is a finite everywhere unramified elementary abelian `3`-extension `E/F`
into which *every* finite everywhere unramified elementary abelian `3`-extension of `F` embeds
over `F`.  Concretely, `E` is the compositum of all cubic everywhere unramified Galois extensions
of `F`, computed inside an algebraic closure of `F`. -/
theorem exists_frattini_layer (F : Type) [Field F] [NumberField F]
    (h3 : ¬ (3 : ℤ) ∣ NumberField.discr F) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
      (_ : FiniteDimensional F E) (_ : IsGalois F E),
      Work.Tower.IsUnramifiedExtension F E ∧ IsPGroup 3 (Gal(E/F)) ∧
      IsAbelianGalois F E ∧ (∀ σ : Gal(E/F), σ ^ 3 = 1) ∧
      (∀ (E' : Type) [Field E'] [NumberField E'] [Algebra F E']
         [FiniteDimensional F E'] [IsGalois F E'],
         Work.Tower.IsUnramifiedExtension F E' → IsPGroup 3 (Gal(E'/F)) →
         IsAbelianGalois F E' → (∀ σ : Gal(E'/F), σ ^ 3 = 1) →
         ∃ (φ : E' →ₐ[F] E), True) := by
  classical
  haveI hΩc : IsAlgClosed (AlgebraicClosure F) := inferInstance
  haveI hΩa : Algebra.IsAlgebraic F (AlgebraicClosure F) := inferInstance
  obtain ⟨ζ, hζp⟩ := exists_primitiveRoot_three_of_isAlgClosed (AlgebraicClosure F)
  have hζnf : ζ ∉ (⊥ : IntermediateField F (AlgebraicClosure F)) :=
    not_mem_bot_of_isPrimitiveRoot h3 hζp
  have hS : (cubicUnramifiedSet F (AlgebraicClosure F)).Finite :=
    finite_cubicUnramifiedSet ⟨ζ, hζp, hζnf⟩
  obtain ⟨hfin, hgal, hunr⟩ := frattiniLayer_properties hS
  obtain ⟨hpg, hab, hexp⟩ := frattiniLayer_galoisGroup (F := F) (Ω := AlgebraicClosure F)
  haveI : Module.Finite F ↥(frattiniLayer F (AlgebraicClosure F)) := hfin
  haveI : IsGalois F ↥(frattiniLayer F (AlgebraicClosure F)) := hgal
  haveI : NumberField ↥(frattiniLayer F (AlgebraicClosure F)) :=
    NumberField.of_module_finite F ↥(frattiniLayer F (AlgebraicClosure F))
  refine ⟨↥(frattiniLayer F (AlgebraicClosure F)), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, hpg, hab, hexp, ?_⟩
  · exact (isUnramifiedExtension_iff (F := F) (L := ↥(frattiniLayer F (AlgebraicClosure F)))).mpr
      hunr
  · intro E' _ _ _ _ _ hunr' hpg' hab' hexp'
    have hunr'' : IsUnramifiedOver F E' :=
      (isUnramifiedExtension_iff (F := F) (L := E')).mp hunr'
    obtain ⟨φ⟩ := frattiniLayer_universal (Ω := AlgebraicClosure F) E' hunr'' hab' hexp'
    exact ⟨φ, trivial⟩

/-- **Complete splitting in the Frattini layer** implies complete splitting in every finite
everywhere unramified elementary abelian `3`-extension of `F`: such an `E'` embeds into the
Frattini layer over `F` (by `frattiniLayer_universal`), and complete splitting is preserved by
injective `F`-algebra maps. -/
theorem splitsCompletelyIn_frattiniLayer {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
    (hS : (cubicUnramifiedSet F Ω).Finite)
    (E' : Type*) [Field E'] [NumberField E'] [Algebra F E'] [FiniteDimensional F E']
    [IsGalois F E'] (hunr : IsUnramifiedOver F E') (hab : IsAbelianGalois F E')
    (hexp : ∀ σ : E' ≃ₐ[F] E', σ ^ 3 = 1) (𝔭 : Ideal (𝓞 F))
    (h : Work.Tower.SplitsCompletelyIn F ↥(frattiniLayer F Ω) 𝔭) :
    Work.Tower.SplitsCompletelyIn F E' 𝔭 := by
  obtain ⟨hfin, hgal, -⟩ := frattiniLayer_properties hS
  haveI : Module.Finite F ↥(frattiniLayer F Ω) := hfin
  haveI : IsGalois F ↥(frattiniLayer F Ω) := hgal
  haveI : NumberField ↥(frattiniLayer F Ω) :=
    NumberField.of_module_finite F ↥(frattiniLayer F Ω)
  obtain ⟨φ⟩ := frattiniLayer_universal (Ω := Ω) E' hunr hab hexp
  exact splitsCompletelyIn_of_algHom 𝔭 φ h

end Tower
end Work
