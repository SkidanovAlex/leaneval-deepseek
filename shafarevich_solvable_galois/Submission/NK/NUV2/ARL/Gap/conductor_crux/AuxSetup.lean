import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.NUV2.ARL.Gap.conductor_crux.AuxCyclotomic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.NUV2.ARL.Gap.conductor_crux

/-! ## The objects -/

/-- The image of `L` in `Ω = CyclotomicField M L` (as an intermediate field over `K`). -/
def AuxA (K L : Type) [Field K] [Field L] [Algebra K L] (M : ℕ) :
    IntermediateField K (CyclotomicField M L) :=
  (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K

/-- The cyclotomic subfield `K(ζ_M) ⊆ Ω`. -/
def AuxB (K L : Type) [Field K] [Field L] [CharZero L] [Algebra K L] (M : ℕ) [NeZero M] :
    IntermediateField K (CyclotomicField M L) :=
  IntermediateField.adjoin K
    ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))

/-- The chosen primitive `M`-th root of unity of `Ω = CyclotomicField M L`. -/
def AuxZeta (L : Type) [Field L] [CharZero L] (M : ℕ) [NeZero M] : CyclotomicField M L :=
  IsCyclotomicExtension.zeta M L (CyclotomicField M L)

lemma AuxZeta_isPrimitiveRoot (L : Type) [Field L] [CharZero L] (M : ℕ) [NeZero M] :
    IsPrimitiveRoot (AuxZeta L M) M :=
  IsCyclotomicExtension.zeta_spec M L (CyclotomicField M L)

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] (M : ℕ) [NeZero M]

/-! ## The image of `L` and its Galois theory -/

/-- The `K`-algebra isomorphism `L ≃ ↥A`, from the canonical identification of `L` with
its image in `Ω`. -/
noncomputable def AuxA_algEquiv :
    L ≃ₐ[K] ↥(AuxA K L M) :=
  ((IntermediateField.botEquiv L (CyclotomicField M L)).symm.restrictScalars K)

lemma AuxA_isGalois : IsGalois K ↥(AuxA K L M) :=
  IsGalois.of_algEquiv (AuxA_algEquiv M)

lemma AuxA_finiteDimensional : FiniteDimensional K ↥(AuxA K L M) :=
  (AuxA_algEquiv M).toLinearEquiv.finiteDimensional

lemma AuxA_normal : Normal K ↥(AuxA K L M) :=
  Normal.of_algEquiv (AuxA_algEquiv M)

lemma AuxA_finrank : Module.finrank K ↥(AuxA K L M) = Module.finrank K L :=
  (AuxA_algEquiv (K := K) (L := L) M).toLinearEquiv.finrank_eq.symm

lemma AuxB_isCyclotomic : IsCyclotomicExtension {M} K ↥(AuxB K L M) :=
  (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M K
    (CyclotomicField M L) (AuxB K L M) (AuxZeta_isPrimitiveRoot L M)).mpr rfl

lemma AuxB_isGalois : IsGalois K ↥(AuxB K L M) := by
  haveI := AuxB_isCyclotomic (K := K) (L := L) M
  exact IsCyclotomicExtension.isGalois {M} K ↥(AuxB K L M)

lemma AuxB_finiteDimensional : FiniteDimensional K ↥(AuxB K L M) := by
  haveI := AuxB_isCyclotomic (K := K) (L := L) M
  exact IsCyclotomicExtension.finiteDimensional {M} K ↥(AuxB K L M)

/-- The two subfields generate `Ω = L(ζ_M)`. -/
lemma AuxA_sup_AuxB_eq_top : AuxA K L M ⊔ AuxB K L M = ⊤ :=
  Aux_sup_restrictScalars_adjoin_zeta_eq_top K L M

/-- The two subfields meet in `K`, provided no prime divisor of `M` divides `disc L`. -/
lemma AuxA_inf_AuxB_eq_bot
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    AuxA K L M ⊓ AuxB K L M = ⊥ := by
  rw [← disjoint_iff]
  rw [AuxA, AuxB]
  exact NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta M hM

end NK.NUV2.ARL.Gap.conductor_crux
