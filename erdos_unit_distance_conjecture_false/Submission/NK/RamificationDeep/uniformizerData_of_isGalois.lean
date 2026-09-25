import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.RamificationDeep.Defs
import Submission.NK.RamificationDeep.InertiaField
import Submission.NK.RamificationDeep.residueField_inertiaField_eq
import Submission.NK.RamificationDeep.monogenic_of_residueRep
import Submission.NK.Ramification.ramificationSubgroup_succ_eq_of_uniformizer

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

section Main

variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)]
variable [PerfectField (IsLocalRing.ResidueField A)]

/-- **The residue field of the inertia field is the residue field of `A`.**

Concretely: every residue class of `A` modulo its maximal ideal is represented by an element of
`A ∩ E`, where `E` is the inertia field.  This is the classical statement that the inertia field
has the same residue field (Serre, *Local Fields*, IV §2; Zariski--Samuel, *Commutative Algebra*
II, Ch. VII §11).  The perfectness of the residue field of `A` is what makes the residue extension
`κ_A / κ_{A ∩ E}` separable; without it the statement fails on purely inseparable examples. -/
theorem exists_residue_rep (hA : A.decompositionSubgroup K = ⊤) :
    ∀ x : A, ∃ b : ↥(restrictRing A (inertiaField (K := K) A)),
      restrictRingToA A (inertiaField (K := K) A) b - x ∈ IsLocalRing.maximalIdeal A :=
  residueField_inertiaField_eq A hA

/-- **Monogeneity of `A` over `A ∩ E`** for `E` the inertia field: every element of `A` is a
polynomial in a uniformizer `π` with coefficients in `A ∩ E`.

This is the second hypothesis of Serre's uniformizer criterion (Serre, *Local Fields*, IV §2
Prop. 4).  The proof is the classical one: the residue equality (`exists_residue_rep`) gives
`A = (A ∩ E) + πA`; since `A` is a finite module over `A ∩ E` (the integral closure of a
Noetherian integrally closed domain in a finite separable extension is finite), a determinant /
Nakayama argument gives `A = (A ∩ E)[π]`. -/
theorem polynomial_rep (hA : A.decompositionSubgroup K = ⊤) (π : A)
    (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) :
    ∀ x : A, ∃ p : Polynomial ↥(inertiaField (K := K) A),
      (∀ j, ((p.coeff j : ↥(inertiaField (K := K) A)) : L) ∈ A) ∧
      p.eval₂ (algebraMap ↥(inertiaField (K := K) A) L) (π : L) = (x : L) :=
  monogenic_of_residueRep A hA π hπ (exists_residue_rep A hA)

end Main

/-- **The data of the uniformizer criterion is available for a Galois-stable valuation ring of a
finite Galois extension with perfect residue field.**

`E` is the inertia field (`NK.RamificationDeep.inertiaField`) and `π` a uniformizer of `A`.
The two nontrivial inputs are the residue equality (`exists_residue_rep`) and the monogeneity
(`polynomial_rep`).  The hypothesis `A.decompositionSubgroup K = ⊤` says that `A` is stable under
the whole Galois group `Gal(L/K)` (so in particular under `Gal(L/E)`, which makes `A` the unique
extension of `A ∩ E` to `L`). -/
theorem uniformizerData_of_isGalois {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤)
    [PerfectField (IsLocalRing.ResidueField A)] :
    ∃ (π : A) (E : IntermediateField K L),
      NK.RamificationDeep.UniformizerData (K := K) A π E := by
  let E : IntermediateField K L := inertiaField (K := K) A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {π} := hπ.maximalIdeal_eq
  refine ⟨π, E, ⟨hmax, ?_, ?_⟩⟩
  · -- `E` is fixed pointwise by the inertia subgroup
    intro σ hσ x
    have hσ' : σ ∈ A.inertiaSubgroup K := by
      rw [← NK.Ramification.ramificationSubgroup_zero (K := K) A]
      exact hσ
    have hmem : (σ : L ≃ₐ[K] L) ∈ inertiaImage (K := K) A := ⟨σ, hσ', rfl⟩
    exact (IntermediateField.mem_fixedField_iff (inertiaImage (K := K) A) (x : L)).mp
      (inertiaField_eq_fixedField_inertiaImage (K := K) A ▸ x.2) (σ : L ≃ₐ[K] L) hmem
  · exact polynomial_rep A hA π hmax

end NK.RamificationDeep
