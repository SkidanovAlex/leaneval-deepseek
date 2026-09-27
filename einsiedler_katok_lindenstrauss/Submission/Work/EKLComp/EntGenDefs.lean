import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.entropy_prod_le
import Submission.Work.EKLComp.partSigma_eq_unions_atoms
import Submission.Work.EKLComp.exists_measurable_approx
import Submission.Work.EKLComp.partSigma_mono_iterate
import Submission.Work.EKLComp.shannon

/-!
# Helpers for the generating-sequence theorem (`Work.EKLComp.ent_generating`)

Definitions and elementary API for the conditional entropy of partition families, the pullback
of a finite partition along an iterate of `T`, and the index equivalence underlying the recursion
for the `N`-fold joins.
-/

open MeasureTheory
open scoped ENNReal BigOperators symmDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

/-- The product-indexed join of two partition families. -/
def joinFam {ι κ : Type*} (A : ι → Set X) (B : κ → Set X) : ι × κ → Set X :=
  fun q => A q.1 ∩ B q.2

@[simp] theorem joinFam_apply {ι κ : Type*} (A : ι → Set X) (B : κ → Set X) (q : ι × κ) :
    joinFam A B q = A q.1 ∩ B q.2 := rfl

theorem Hfam_congr {ι : Type*} [Fintype ι] (μ : Measure X) {P Q : ι → Set X} (h : P = Q) :
    Hfam μ P = Hfam μ Q := by rw [h]

/-- The product join of two measurable partitions is a measurable partition. -/
theorem isMPart_joinFam {ι κ : Type*} [Fintype ι] [Fintype κ] {A : ι → Set X} {B : κ → Set X}
    (hA : Core.IsMPart A) (hB : Core.IsMPart B) : Core.IsMPart (joinFam A B) := by
  refine ⟨fun q => (hA.measurable q.1).inter (hB.measurable q.2), ?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    rcases eq_or_ne i i' with h | h
    · subst h
      have hjj' : j ≠ j' := fun h' => hne (by rw [h'])
      exact (hB.disjoint hjj').mono Set.inter_subset_right Set.inter_subset_right
    · exact (hA.disjoint h).mono Set.inter_subset_left Set.inter_subset_left
  · ext x
    constructor
    · intro _; trivial
    · intro _
      simp only [Set.mem_iUnion]
      obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by
        have : x ∈ ⋃ i, A i := by rw [hA.cover]; trivial
        simpa only [Set.mem_iUnion] using this
      obtain ⟨j, hj⟩ : ∃ j, x ∈ B j := by
        have : x ∈ ⋃ j, B j := by rw [hB.cover]; trivial
        simpa only [Set.mem_iUnion] using this
      exact ⟨(i, j), hi, hj⟩

/-- A `FinPart` viewed as a `Core.IsMPart` family. -/
theorem isMPart_parts (P : FinPart X) : Core.IsMPart P.parts :=
  ⟨P.measurable, P.disjoint, P.cover⟩

/-- Conditional entropy of the partition family `B` given the partition family `A`. -/
def CH {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : Measure X) (A : ι → Set X)
    (B : κ → Set X) : ℝ :=
  Hfam μ (joinFam A B) - Hfam μ A

/-- `CH` written with the join unfolding. -/
theorem CH_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : Measure X) (A : ι → Set X)
    (B : κ → Set X) : CH μ A B = Hfam μ (fun q : ι × κ => A q.1 ∩ B q.2) - Hfam μ A := rfl

/-- Conditional entropy of two `FinPart`s. -/
def CHp (μ : Measure X) (A B : FinPart X) : ℝ :=
  CH μ A.parts B.parts

theorem CHp_eq (μ : Measure X) (A B : FinPart X) :
    CHp μ A B = Hfam μ (joinFam A.parts B.parts) - Hfam μ A.parts := rfl

/-- The `Hfam` of a partition family is at most the `Hfam` of its product join with any other
partition family. -/
theorem Hfam_le_Hfam_joinFam {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X}
    (hA : Core.IsMPart A) (hB : Core.IsMPart B) : Hfam μ B ≤ Hfam μ (joinFam A B) :=
  Core.Hfam_mono μ hB (isMPart_joinFam hA hB) Prod.snd fun _ => Set.inter_subset_right

/-- `0 ≤ CH μ A B`. -/
theorem CH_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X}
    (hA : Core.IsMPart A) (hB : Core.IsMPart B) : 0 ≤ CH μ A B :=
  sub_nonneg.mpr (Core.Hfam_mono μ hA (isMPart_joinFam hA hB) Prod.fst fun _ => Set.inter_subset_left)

/-- `Hfam B ≤ Hfam A + CH μ A B`. -/
theorem Hfam_le_Hfam_add_CH {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : Measure X)
    [IsProbabilityMeasure μ] {A : ι → Set X} {B : κ → Set X}
    (hA : Core.IsMPart A) (hB : Core.IsMPart B) : Hfam μ B ≤ Hfam μ A + CH μ A B := by
  have h : Hfam μ B ≤ Hfam μ (fun q : ι × κ => A q.1 ∩ B q.2) := Hfam_le_Hfam_joinFam μ hA hB
  rw [CH_eq]
  linarith

/-- The pullback of a finite partition along `T^[N]`. -/
def vpart (T : X → X) (N : ℕ) (P : FinPart X) : Fin P.n → Set X :=
  fun i => T^[N] ⁻¹' P.parts i

@[simp] theorem vpart_apply (T : X → X) (N : ℕ) (P : FinPart X) (i : Fin P.n) :
    vpart T N P i = T^[N] ⁻¹' P.parts i := rfl

theorem isMPart_vpart {T : X → X} (hT : Measurable T) (N : ℕ) (P : FinPart X) :
    Core.IsMPart (vpart T N P) := by
  refine ⟨fun i => (P.measurable i).preimage (hT.iterate N), ?_, ?_⟩
  · intro i j hij
    exact (P.disjoint hij).preimage _
  · ext x
    simp only [vpart, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · intro _; trivial
    · intro _
      have : T^[N] x ∈ (⋃ i, P.parts i) := by rw [P.cover]; trivial
      simpa only [Set.mem_iUnion] using this

/-- `(Fin N → Fin P.n) × Fin P.n ≃ (Fin (N+1) → Fin P.n)`, the index equivalence underlying
the recursion `⋁_{k<N+1} T^{-k}P = (⋁_{k<N}T^{-k}P) ∨ T^{-N}P`. -/
def joinEquiv (N : ℕ) (P : FinPart X) :
    ((Fin N → Fin P.n) × Fin P.n) ≃ (Fin (N + 1) → Fin P.n) where
  toFun q := Fin.append q.1 (fun _ => q.2)
  invFun w := (fun i => w (Fin.castAdd 1 i), w (Fin.natAdd N 0))
  left_inv q := by
    refine Prod.ext ?_ ?_
    · funext i
      change Fin.append q.1 (fun _ => q.2) (Fin.castAdd 1 i) = q.1 i
      rw [Fin.append_left]
    · change Fin.append q.1 (fun _ => q.2) (Fin.natAdd N 0) = q.2
      rw [Fin.append_right]
  right_inv w := by
    funext k
    refine Fin.addCases (m := N) (n := 1) (fun i => ?_) (fun i => ?_) k
    · change Fin.append (fun i => w (Fin.castAdd 1 i)) (fun _ => w (Fin.natAdd N 0))
        (Fin.castAdd 1 i) = w (Fin.castAdd 1 i)
      rw [Fin.append_left]
    · have hlast : Fin.natAdd N i = Fin.natAdd N (0 : Fin 1) :=
        congrArg (Fin.natAdd N) (Subsingleton.elim i 0)
      change Fin.append (fun i => w (Fin.castAdd 1 i)) (fun _ => w (Fin.natAdd N 0))
        (Fin.natAdd N i) = w (Fin.natAdd N i)
      rw [Fin.append_right, hlast]

@[simp] theorem joinEquiv_apply (N : ℕ) (P : FinPart X)
    (q : (Fin N → Fin P.n) × Fin P.n) :
    joinEquiv N P q = Fin.append q.1 (fun _ => q.2) := rfl

@[simp] theorem joinEquiv_symm_apply (N : ℕ) (P : FinPart X) (w : Fin (N + 1) → Fin P.n) :
    (joinEquiv N P).symm w = (fun i => w (Fin.castAdd 1 i), w (Fin.natAdd N 0)) := rfl

/-- The reindexing equivalence for the pair of joins. -/
def joinEquiv₂ (N : ℕ) (P Q : FinPart X) :
    ((Fin N → Fin P.n) × Fin P.n) × ((Fin N → Fin Q.n) × Fin Q.n) ≃
      (Fin (N + 1) → Fin P.n) × (Fin (N + 1) → Fin Q.n) where
  toFun q := (joinEquiv N P q.1, joinEquiv N Q q.2)
  invFun w := ((joinEquiv N P).symm w.1, (joinEquiv N Q).symm w.2)
  left_inv q := by
    simp only [Equiv.symm_apply_apply]
  right_inv w := by
    simp only [Equiv.apply_symm_apply]

@[simp] theorem joinEquiv₂_apply (N : ℕ) (P Q : FinPart X)
    (q : ((Fin N → Fin P.n) × Fin P.n) × ((Fin N → Fin Q.n) × Fin Q.n)) :
    joinEquiv₂ N P Q q = (joinEquiv N P q.1, joinEquiv N Q q.2) := rfl



/-! ## Swapping the factors of a product index -/

/-- Swapping the two factors of `ρ × ι`. -/
def swapEquiv (ι ρ : Type*) : ρ × ι ≃ ι × ρ where
  toFun q := (q.2, q.1)
  invFun q := (q.2, q.1)
  left_inv q := by rcases q with ⟨a, b⟩; rfl
  right_inv q := by rcases q with ⟨a, b⟩; rfl

@[simp] theorem swapEquiv_apply (ι ρ : Type*) (q : ρ × ι) :
    swapEquiv ι ρ q = (q.2, q.1) := rfl

/-- Swapping the two factors inside the first component of `(ρ × ι) × κ`. -/
def swap₂ (ι ρ κ : Type*) : (ρ × ι) × κ ≃ (ι × ρ) × κ where
  toFun q := ((q.1.2, q.1.1), q.2)
  invFun q := ((q.1.2, q.1.1), q.2)
  left_inv q := by rcases q with ⟨⟨a, b⟩, c⟩; rfl
  right_inv q := by rcases q with ⟨⟨a, b⟩, c⟩; rfl

@[simp] theorem swap₂_apply (ι ρ κ : Type*) (q : (ρ × ι) × κ) :
    swap₂ ι ρ κ q = ((q.1.2, q.1.1), q.2) := rfl

/-! ## Unions of atoms -/

/-- The union of the atoms of the partition `R` indexed by the set `J`. -/
def unionAtoms (R : FinPart X) (J : Set (Fin R.n)) : Set X := ⋃ j ∈ J, R.parts j

theorem unionAtoms_measurable (R : FinPart X) (J : Set (Fin R.n)) :
    MeasurableSet (unionAtoms R J) := by
  have h : (⋃ j ∈ J, R.parts j) = ⋃ j : J, R.parts j.1 := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨⟨j, hj⟩, hx⟩
    · rintro ⟨j, hx⟩
      exact ⟨j.1, j.2, hx⟩
  rw [unionAtoms, h]
  exact MeasurableSet.iUnion fun j : J => R.measurable j.1

theorem mem_unionAtoms {R : FinPart X} {J : Set (Fin R.n)} {x : X} :
    x ∈ unionAtoms R J ↔ ∃ j ∈ J, x ∈ R.parts j := by
  simp [unionAtoms]

theorem parts_subset_unionAtoms (R : FinPart X) {J : Set (Fin R.n)} {j : Fin R.n} (hj : j ∈ J) :
    R.parts j ⊆ unionAtoms R J :=
  fun _ hx => mem_unionAtoms.mpr ⟨j, hj, hx⟩

theorem inter_unionAtoms_eq_empty (R : FinPart X) {J : Set (Fin R.n)} {j : Fin R.n}
    (hj : j ∉ J) : R.parts j ∩ unionAtoms R J = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨j', hj', hx'⟩ := mem_unionAtoms.mp hx2
  rcases eq_or_ne j j' with h | h
  · exact hj (h ▸ hj')
  · exact (Set.disjoint_left.mp (R.disjoint h) hx1 hx')

end Work.EKLComp
