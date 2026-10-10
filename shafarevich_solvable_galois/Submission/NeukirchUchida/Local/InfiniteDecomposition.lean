import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Decomposition subgroups of valuation subrings, and their restriction to finite levels

Let `K' / K` be a Galois extension of fields, not necessarily finite, and let `A` be a valuation
subring of `K'` (for instance the valuation ring of a place of `K'` lying over a place of `K`).
The *decomposition subgroup* of `A` is the stabiliser

`MulAction.stabilizer (K' ≃ₐ[K] K') A`

of `A` under the natural action of `Gal(K'/K) = K' ≃ₐ[K] K'` on valuation subrings.

The main result of this file, `mem_stabilizer_valuationSubring_iff_forall_restrict`, says that `σ`
lies in the decomposition subgroup of `A` if and only if, for *every* normal intermediate field
`L/K`, the restriction `σ|_L` lies in the decomposition subgroup of the restricted valuation
subring `A ∩ L`.  This exhibits the decomposition subgroup as the projective limit of its
finite-level counterparts, which is the structural input for identifying it with the Galois group
of the corresponding local extension (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
Chapter II and XII §1).

## Main definitions and results

* `restrictValuationSubring A L` : the intersection `A ∩ L`, as a valuation subring of `L`;
* `mem_stabilizer_valuationSubring_iff` : elementwise description of the stabiliser of `A`;
* `mem_stabilizer_valuationSubring_iff_forall_restrict` : the stabiliser of `A` is the
  intersection of the preimages of the stabilisers of the `A ∩ L`;
* `restrictValuationSubring_comap` : compatibility of the restrictions along a tower of
  intermediate fields;
* `mem_stabilizer_valuationSubring_iff_forall_finite_restrict` : the same description with `L`
  ranging over the finite normal intermediate fields;
* `isClosed_stabilizer_valuationSubring` : the stabiliser is closed in the Krull topology.
-/

open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.NeukirchUchida.Local

/-! ## Restricting a valuation subring to an intermediate field -/

/-- The restriction of a valuation subring `A` of `K'` to an intermediate field `L`, i.e. the
intersection `A ∩ L` regarded as a valuation subring of `L`. -/
noncomputable def restrictValuationSubring {K : Type*} [Field K] {K' : Type*} [Field K']
    [Algebra K K'] (A : ValuationSubring K') (L : IntermediateField K K') : ValuationSubring L :=
  A.comap (algebraMap L K')

@[simp]
theorem mem_restrictValuationSubring {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    {A : ValuationSubring K'} {L : IntermediateField K K'} {x : L} :
    x ∈ restrictValuationSubring A L ↔ algebraMap L K' x ∈ A := Iff.rfl

@[simp]
theorem coe_restrictValuationSubring {K : Type*} [Field K] {K' : Type*} [Field K']
    [Algebra K K'] (A : ValuationSubring K') (L : IntermediateField K K') :
    (restrictValuationSubring A L : Set L) = (algebraMap L K') ⁻¹' (A : Set K') := rfl

/-- Restrictions of a valuation subring to a tower of intermediate fields are compatible. -/
theorem restrictValuationSubring_comap {K : Type*} [Field K] {K' : Type*} [Field K']
    [Algebra K K'] (A : ValuationSubring K') {L M : IntermediateField K K'} (h : L ≤ M) :
    (restrictValuationSubring A M).comap (IntermediateField.inclusion h : L →+* M) =
      restrictValuationSubring A L := by
  refine SetLike.ext fun x => ?_
  show algebraMap M K' ((IntermediateField.inclusion h) x) ∈ A ↔ algebraMap L K' x ∈ A
  rfl

/-! ## The stabiliser of a valuation subring -/

section Stabilizer

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **Elementwise description of the stabiliser of a valuation subring**: `σ` stabilises `A` if and
only if `σ x ∈ A ↔ x ∈ A` for every `x`. -/
theorem mem_stabilizer_valuationSubring_iff (A : ValuationSubring E) (σ : E ≃ₐ[F] E) :
    σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) A ↔ ∀ x : E, (x ∈ A ↔ σ x ∈ A) := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    have h2 : σ x ∈ σ • A ↔ σ x ∈ A := SetLike.ext_iff.mp h (σ x)
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h2
    simpa using h2
  · intro h
    refine SetLike.ext fun x => ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    show σ⁻¹ x ∈ A ↔ x ∈ A
    rw [h (σ⁻¹ x)]
    simp

end Stabilizer

/-! ## The stabiliser as an intersection of finite-level stabilisers -/

section Galois

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] [IsGalois K K']

/-- The restriction of an element of `Gal(K'/K)` to a normal intermediate field, applied to an
element of `K'` that already lies in `L`. -/
theorem restrictNormalHom_apply_algebraMap (L : IntermediateField K K') [Normal K L]
    (σ : K' ≃ₐ[K] K') (x : L) :
    algebraMap L K' (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ x) =
      σ (algebraMap L K' x) := by
  rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) x = (σ.restrictNormal L) x
      from rfl,
    AlgEquiv.restrictNormal_commutes]

/-- **The decomposition subgroup of a valuation subring of a Galois extension is the intersection
of the decomposition subgroups of its restrictions to the normal intermediate fields.**

This is the projective-limit description of the decomposition group: an element of `Gal(K'/K)`
fixes the valuation subring `A` if and only if each of its finite-level restrictions fixes
`A ∩ L`. -/
theorem mem_stabilizer_valuationSubring_iff_forall_restrict (A : ValuationSubring K')
    (σ : K' ≃ₐ[K] K') :
    σ ∈ MulAction.stabilizer (K' ≃ₐ[K] K') A ↔
      ∀ (L : IntermediateField K K') [Normal K L],
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ ∈
          MulAction.stabilizer (L ≃ₐ[K] L) (restrictValuationSubring A L) := by
  rw [mem_stabilizer_valuationSubring_iff]
  constructor
  · intro h L _
    rw [mem_stabilizer_valuationSubring_iff]
    intro x
    rw [mem_restrictValuationSubring, mem_restrictValuationSubring,
      restrictNormalHom_apply_algebraMap]
    exact h (algebraMap L K' x)
  · intro h x
    have hx : IsIntegral K x :=
      isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic x)
    set L₀ := IntermediateField.adjoin K ({x} : Set K') with hL₀
    haveI : FiniteDimensional K L₀ := IntermediateField.adjoin.finiteDimensional hx
    set L := IntermediateField.normalClosure K L₀ K' with hL
    haveI : Normal K L := inferInstance
    have hxL₀ : x ∈ L₀ :=
      IntermediateField.subset_adjoin K ({x} : Set K') (Set.mem_singleton x)
    have hxL : x ∈ L := IntermediateField.le_normalClosure L₀ hxL₀
    have hy := h L
    rw [mem_stabilizer_valuationSubring_iff] at hy
    have hy' := hy (⟨x, hxL⟩ : L)
    rw [mem_restrictValuationSubring, mem_restrictValuationSubring,
      restrictNormalHom_apply_algebraMap] at hy'
    simpa using hy'

end Galois

end Submission.NeukirchUchida.Local
