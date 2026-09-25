import Mathlib
import Submission.Work.TameArithmetic.Defs

/-!
# Existence of the maximal tame pro-`2` extension of `ℚ` (for `S = primesS`)

`Work.TameArithmetic.exists_maximalTamePro2`: there is a field `K` (with `Field`, `Algebra ℚ`,
`IsGalois ℚ` instances) which is a **maximal tame pro-`2` extension of `ℚ`** in the sense of
`Work.TameArithmetic.IsMaximalTamePro2`, i.e. `Algebra.IsAlgebraic ℚ K`, `TameUnivClause K` and
`TameSubClause K`.

The construction is the sup-construction of `Submission.NumberField.MaximalProPOutsideS`
specialised to `F = ℚ`, `p = 2`, `S = primesS`: inside the algebraic closure of `ℚ` take the sup
`K` of all finite Galois pro-`2` subextensions whose relative different is supported on `S` and
which are unramified at the infinite places.  No class field theory is used.  The extra content
here over `exists_maximal_proP_field_unramifiedOutside_inf` is that we keep hold of the
*concrete* field `K` (an intermediate field of the algebraic closure), so that the algebraicity
`Algebra.IsAlgebraic ℚ K` -- part of the interface `IsMaximalTamePro2`, needed later to make
`Gal(K/ℚ)` residually finite -- is available; and that the two clauses are converted into the
abstract forms `TameUnivClause`/`TameSubClause`, which are stated for an arbitrary field type and
a `ℚ`-algebra homomorphism into `K` rather than for `IntermediateField`s of `K`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Classical
open scoped NumberField
open IntermediateField

noncomputable section

namespace Work.TameArithmetic

/-- **The maximal tame pro-`2` extension of `ℚ`** (for `S = primesS`) exists: the sup of all
finite Galois pro-`2` extensions of `ℚ` with `S`-supported different which are unramified at the
infinite places.  Its universal property is `TameUnivClause`, its maximality is `TameSubClause`,
and it is algebraic over `ℚ`. -/
theorem exists_isMaximalTamePro2_sup :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
      Algebra.IsAlgebraic ℚ K ∧ TameUnivClause K ∧ TameSubClause K := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let Ω := AlgebraicClosure ℚ
  let ι := Submission.NumberField.SupportedPFieldInf ℚ 2 primesS
  let f : ι → IntermediateField ℚ Ω := fun i => i.L
  let K : IntermediateField ℚ Ω := ⨆ i, f i
  have hfd_f : ∀ i : ι, FiniteDimensional ℚ ↥(f i) := fun i => i.hfd
  have hgal_f : ∀ i : ι, IsGalois ℚ ↥(f i) := fun i => i.hgal
  have hnum_f : ∀ i : ι, NumberField ↥(f i) := fun i => i.hnum
  have hpg_f : ∀ i : ι, IsPGroup 2 (↥(f i) ≃ₐ[ℚ] ↥(f i)) := fun i => i.hpg
  have hsupp_f : ∀ i : ι, ∀ (P : Ideal (NumberField.RingOfIntegers ↥(f i))), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers ↥(f i)) →
        ∃ q ∈ primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := fun i => i.hsupp
  have hinr_f : ∀ i : ι, IsUnramifiedAtInfinitePlaces ℚ ↥(f i) := fun i => i.hunrInf
  haveI hgal_fI : ∀ i : ι, IsGalois ℚ ↥(f i) := hgal_f
  haveI hfd_fI : ∀ i : ι, FiniteDimensional ℚ ↥(f i) := hfd_f
  haveI hnum_fI : ∀ i : ι, NumberField ↥(f i) := hnum_f
  have hgalK : IsGalois ℚ ↥K := by
    dsimp [K, f]
    exact Commons.FieldTheory.Galois.isGalois_iSup_of_charZero (F := ℚ) (K := Ω) (E := f)
  refine ⟨↥K, inferInstance, inferInstance, hgalK, ?_, ?_, ?_⟩
  · -- `K` is algebraic over `ℚ`: it is an intermediate field of `AlgebraicClosure ℚ`
    infer_instance
  · -- the universal property
    intro M _ _ _ _ hpg hsupp hinf
    let e : M →ₐ[ℚ] Ω := IsAlgClosed.lift (R := ℚ) (S := M) (M := Ω)
    let eeq : M ≃ₐ[ℚ] e.fieldRange := AlgEquiv.ofInjectiveField e
    haveI hfdL : FiniteDimensional ℚ ↥(e.fieldRange) := eeq.toLinearEquiv.finiteDimensional
    haveI hgalL : IsGalois ℚ ↥(e.fieldRange) := IsGalois.of_algEquiv eeq
    haveI hnumL : NumberField ↥(e.fieldRange) :=
      NumberField.of_module_finite ℚ ↥(e.fieldRange)
    have hpgL : IsPGroup 2 (↥(e.fieldRange) ≃ₐ[ℚ] ↥(e.fieldRange)) :=
      hpg.of_equiv (AlgEquiv.autCongr eeq)
    have hsuppL : ∀ (P : Ideal (NumberField.RingOfIntegers ↥(e.fieldRange))), P.IsPrime →
        P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers ℚ)
          (NumberField.RingOfIntegers ↥(e.fieldRange)) →
          ∃ q ∈ primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Submission.NumberField.differentIdeal_supp_of_algEquiv (F := ℚ) primesS eeq hsupp
    have hinrL : IsUnramifiedAtInfinitePlaces ℚ ↥(e.fieldRange) :=
      Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv (e := eeq) hinf
    have hle : e.fieldRange ≤ K := by
      exact le_iSup f
        { L := e.fieldRange, hfd := hfdL, hgal := hgalL, hnum := hnumL,
          hpg := hpgL, hsupp := hsuppL, hunrInf := hinrL }
    refine ⟨(IntermediateField.inclusion hle).comp eeq.toAlgHom, trivial⟩
  · -- the maximality clause
    intro L _ _ _ _ _ φ hinj
    let eL : L →ₐ[ℚ] Ω := (IntermediateField.val K).comp φ
    let L' : IntermediateField ℚ Ω := eL.fieldRange
    let eeqL : L ≃ₐ[ℚ] ↥L' := AlgEquiv.ofInjectiveField eL
    haveI hfdL' : FiniteDimensional ℚ ↥L' := eeqL.toLinearEquiv.finiteDimensional
    haveI hgalL' : IsGalois ℚ ↥L' := IsGalois.of_algEquiv eeqL
    haveI hnumL' : NumberField ↥L' := NumberField.of_module_finite ℚ ↥L'
    have hL'K : L' ≤ K := by
      intro x hx
      rcases hx with ⟨y, rfl⟩
      exact (φ y).2
    have hpgL' : IsPGroup 2 (↥L' ≃ₐ[ℚ] ↥L') :=
      Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
        (F := ℚ) (K := Ω) (p := 2) (f := f) hfd_f hgal_f hpg_f hL'K
    have hsuppL' : ∀ (P : Ideal (NumberField.RingOfIntegers ↥L')), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers ↥L') →
          ∃ q ∈ primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset (F := ℚ) primesS
        hfd_f hgal_f hsupp_f hL'K
    have hinrL' : IsUnramifiedAtInfinitePlaces ℚ ↥L' :=
      Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_le_iSup_finset
        (F := ℚ) (f := f) hgal_f hinr_f hL'K
    have hpgL : IsPGroup 2 (L ≃ₐ[ℚ] L) := hpgL'.of_equiv (AlgEquiv.autCongr eeqL).symm
    have hsuppL : ∀ (P : Ideal (NumberField.RingOfIntegers L)), P.IsPrime → P ≠ ⊥ →
        P ∣ differentIdeal (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers L) →
          ∃ q ∈ primesS, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Submission.NumberField.differentIdeal_supp_of_algEquiv (F := ℚ) primesS eeqL.symm hsuppL'
    have hinrL : IsUnramifiedAtInfinitePlaces ℚ L :=
      Commons.NumberTheory.NumberField.isUnramifiedAtInfinitePlaces_of_algEquiv
        (e := eeqL.symm) hinrL'
    exact ⟨hpgL, hsuppL, hinrL⟩

theorem exists_maximalTamePro2 :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
      Work.TameArithmetic.IsMaximalTamePro2 K :=
  exists_isMaximalTamePro2_sup

end Work.TameArithmetic
