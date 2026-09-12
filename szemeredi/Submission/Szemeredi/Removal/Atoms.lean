import Mathlib
import Submission.Szemeredi.Removal.Defs

/-!
# Atom tuples for joins of σ-algebras

Infrastructure for the counting lemma: the product of the indicators of a tuple of
atoms, and the fact that summing that product over all tuples gives `1`.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- The intersection of a tuple of sets indexed by a finset (`⊤ = univ`). -/
noncomputable def inter (s : Finset ι) (A : ι → Finset Ω) : Finset Ω := s.inf A

theorem mem_inter {s : Finset ι} {A : ι → Finset Ω} {x : Ω} :
    x ∈ inter s A ↔ ∀ i ∈ s, x ∈ A i := by
  rw [inter, Finset.mem_inf]

theorem inter_eq_iInf_block (P : ι → SigAlg Ω) (s : Finset ι) (x : Ω) :
    inter s (fun i => (P i).block x) = (SigAlg.iInf P s).block x := by
  rw [inter, SigAlg.iInf_block]

/-- The product of the indicators of a tuple of sets is the indicator of the
intersection. -/
theorem prod_indicator_eq (s : Finset ι) (A : ι → Finset Ω) (x : Ω) :
    (∏ i ∈ s, SigAlg.indicator (A i) x) = SigAlg.indicator (inter s A) x := by
  show (∏ i ∈ s, (if x ∈ A i then (1 : ℝ) else 0))
      = (if x ∈ inter s A then (1 : ℝ) else 0)
  by_cases h : x ∈ inter s A
  · rw [if_pos h]
    refine Finset.prod_eq_one (fun i hi => ?_)
    rw [if_pos ((mem_inter.mp h) i hi)]
  · rw [if_neg h]
    rw [mem_inter] at h
    push_neg at h
    obtain ⟨i, hi, hxi⟩ := h
    exact Finset.prod_eq_zero hi (by rw [if_neg hxi])

/-- The unique atom of `P` containing `x`; summed over all atoms it gives `1`. -/
theorem sum_indicator_atoms (P : SigAlg Ω) (x : Ω) :
    (∑ A ∈ P.atoms, SigAlg.indicator A x) = 1 := by
  rw [Finset.sum_eq_single (P.block x)]
  · show (if x ∈ P.block x then (1 : ℝ) else 0) = 1
    rw [if_pos (P.mem_block x)]
  · intro A hA hne
    show (if x ∈ A then (1 : ℝ) else 0) = 0
    rw [if_neg]
    intro hx
    exact hne (SigAlg.eq_of_mem_atoms hA hx).symm
  · intro h
    exact absurd (SigAlg.block_mem_atoms P x) h

/-- A tuple of atoms of the partitions `P i`, `i ∈ s`. -/
abbrev AtomTuple (P : ι → SigAlg Ω) (s : Finset ι) :=
  (i : {i : ι // i ∈ s}) → {A : Finset Ω // A ∈ (P i.val).atoms}

/-- The pointwise atom tuple of `x`. -/
noncomputable def atomTupleOf (P : ι → SigAlg Ω) (s : Finset ι) (x : Ω) : AtomTuple P s :=
  fun i => ⟨(P i.val).block x, SigAlg.block_mem_atoms (P i.val) x⟩

/-- The product of the indicators of a tuple of atoms. -/
noncomputable def prodAtoms (P : ι → SigAlg Ω) (s : Finset ι) (A : AtomTuple P s) (x : Ω) : ℝ :=
  ∏ i, SigAlg.indicator (A i).val x

theorem prodAtoms_nonneg (P : ι → SigAlg Ω) (s : Finset ι) (A : AtomTuple P s) (x : Ω) :
    0 ≤ prodAtoms P s A x :=
  Finset.prod_nonneg (fun i _ => SigAlg.indicator_nonneg _ x)

theorem prodAtoms_le_one (P : ι → SigAlg Ω) (s : Finset ι) (A : AtomTuple P s) (x : Ω) :
    prodAtoms P s A x ≤ 1 :=
  Finset.prod_le_one (fun i _ => SigAlg.indicator_nonneg _ x)
    (fun i _ => SigAlg.indicator_le_one _ x)

theorem prodAtoms_atomTupleOf (P : ι → SigAlg Ω) (s : Finset ι) (x : Ω) :
    prodAtoms P s (atomTupleOf P s x) x = 1 := by
  unfold prodAtoms
  refine Finset.prod_eq_one (fun i _ => ?_)
  show (if x ∈ (P i.val).block x then (1 : ℝ) else 0) = 1
  rw [if_pos ((P i.val).mem_block x)]

theorem prodAtoms_eq_zero_of_ne (P : ι → SigAlg Ω) (s : Finset ι) (A : AtomTuple P s) (x : Ω)
    (h : A ≠ atomTupleOf P s x) : prodAtoms P s A x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, A i ≠ atomTupleOf P s x i := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  unfold prodAtoms
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  show (if x ∈ (A i).val then (1 : ℝ) else 0) = 0
  rw [if_neg]
  intro hx
  apply hi
  refine Subtype.ext ?_
  show (A i).val = (P i.val).block x
  exact (SigAlg.eq_of_mem_atoms (A i).2 hx).symm

/-- Summing the product of the indicators of a tuple of atoms over all tuples
gives `1`. -/
theorem sum_prodAtoms (P : ι → SigAlg Ω) (s : Finset ι) (x : Ω) :
    (∑ A : AtomTuple P s, prodAtoms P s A x) = 1 := by
  rw [Finset.sum_eq_single (atomTupleOf P s x)]
  · exact prodAtoms_atomTupleOf P s x
  · intro A _ hne
    exact prodAtoms_eq_zero_of_ne P s A x hne
  · intro h
    exact absurd (Finset.mem_univ (atomTupleOf P s x)) h

/-- The product of the indicators of a tuple of atoms, integrated over the whole
space, sums to `1` over all tuples. -/
theorem avg_sum {κ : Type*} [Fintype κ] (g : κ → Ω → ℝ) :
    avg (fun x => ∑ i, g i x) = ∑ i, avg (g i) := by
  unfold avg
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset κ))
    (f := fun (x : Ω) (i : κ) => g i x)

theorem sum_avg_prodAtoms (P : ι → SigAlg Ω) (s : Finset ι) :
    (∑ A : AtomTuple P s, avg (fun x => prodAtoms P s A x)) = 1 := by
  rw [← avg_sum]
  rw [show (fun x => ∑ A : AtomTuple P s, prodAtoms P s A x) = fun _ => (1 : ℝ)
      from funext (sum_prodAtoms P s)]
  exact avg_const 1

end Szemeredi.Removal
