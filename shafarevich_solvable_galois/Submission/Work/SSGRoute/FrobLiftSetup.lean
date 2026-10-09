import Mathlib
import Submission.Work.SSGRoute.InertiaDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Setup for the Frobenius lift at a finite place

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω`, write
`D = decomp k A` and `I = inertiaSub k Ω A`.  This file fixes the family of *open* subgroups of
`D` (containing `I`) that the construction of the Frobenius lift uses, and the subsets of `D` of
elements that generate the corresponding finite cyclic quotient.

Concretely, for a finite normal intermediate field `L ⊆ Ω` we put

* `frobV A L = I ⊔ L.fixingSubgroup ≤ G_k` — an *open* subgroup containing `I` (it contains the
  open fixing subgroup of `L`);
* `frobK A L = D ⊓ (frobV A L)`, viewed as a subgroup of `↥D`;
* `frobS A L ⊆ ↥D` — the elements of `D` whose image generates `D ⧸ frobK A L`.

The family `frobV A L` is cofinal among the open subgroups of `G_k` containing `I`
(`exists_finiteDimensional_normal_fixingSubgroup_le`), and `frobK A L` is normal and open in `↥D`.
Nothing here is `sorry`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The index set of the construction: the finite normal intermediate fields `L ⊆ Ω`. -/
abbrev FrobIndex (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] :=
  {L : IntermediateField k Ω // FiniteDimensional k L ∧ Normal k L}

/-- The open subgroup `frobV A L = I_A ⊔ G_L ≤ G_k`. -/
noncomputable def frobV (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    Subgroup (Ω ≃ₐ[k] Ω) :=
  inertiaSub k Ω A ⊔ i.1.fixingSubgroup

/-- `frobK A L = D_A ⊓ frobV A L`, as a subgroup of the decomposition group `↥D_A`. -/
noncomputable def frobK (A : ValuationSubring Ω) (i : FrobIndex k Ω) :
    Subgroup ↥(decomp k A) :=
  (frobV A i).subgroupOf (decomp k A)

/-- `frobS A L ⊆ ↥D_A`: the elements generating the quotient `D_A ⧸ frobK A L`. -/
noncomputable def frobS (A : ValuationSubring Ω) (i : FrobIndex k Ω) : Set ↥(decomp k A) :=
  {x | ∀ δ : ↥(decomp k A), ∃ m : ℤ, δ⁻¹ * x ^ m ∈ frobK A i}

/-- The (componentwise) supremum of two indices, used to make the family directed. -/
noncomputable def frobSup (i j : FrobIndex k Ω) : FrobIndex k Ω :=
  ⟨i.1 ⊔ j.1,
    by
      haveI := i.2.1
      haveI := j.2.1
      exact IntermediateField.finiteDimensional_sup i.1 j.1,
    by
      haveI := i.2.2
      haveI := j.2.2
      exact IntermediateField.normal_sup k Ω i.1 j.1⟩

lemma frobV_le_frobV_of_le (A : ValuationSubring Ω) {i j : FrobIndex k Ω} (h : i.1 ≤ j.1) :
    frobV A j ≤ frobV A i := by
  unfold frobV
  exact sup_le_sup_left (IntermediateField.fixingSubgroup_antitone h) _

lemma frobK_le_frobK_of_le (A : ValuationSubring Ω) {i j : FrobIndex k Ω} (h : i.1 ≤ j.1) :
    frobK A j ≤ frobK A i :=
  Subgroup.comap_mono (frobV_le_frobV_of_le A h)

lemma frobK_frobSup_le_left (A : ValuationSubring Ω) (i j : FrobIndex k Ω) :
    frobK A (frobSup i j) ≤ frobK A i :=
  frobK_le_frobK_of_le A (le_sup_left : i.1 ≤ i.1 ⊔ j.1)

lemma frobK_frobSup_le_right (A : ValuationSubring Ω) (i j : FrobIndex k Ω) :
    frobK A (frobSup i j) ≤ frobK A j :=
  frobK_le_frobK_of_le A (le_sup_right : j.1 ≤ i.1 ⊔ j.1)

lemma frobS_mono (A : ValuationSubring Ω) {i j : FrobIndex k Ω} (h : frobK A i ≤ frobK A j) :
    frobS A i ⊆ frobS A j := by
  intro x hx δ
  obtain ⟨m, hm⟩ := hx δ
  exact ⟨m, h hm⟩

lemma frobS_frobSup_subset (A : ValuationSubring Ω) (i j : FrobIndex k Ω) :
    frobS A (frobSup i j) ⊆ frobS A i ∩ frobS A j :=
  Set.subset_inter (frobS_mono A (frobK_frobSup_le_left A i j))
    (frobS_mono A (frobK_frobSup_le_right A i j))

end Work.SSGRoute
