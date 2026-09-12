import Mathlib
import Submission.MagicVector

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators

namespace Submission.NetInvariance

open Submission.MagicVector
open Submission.Sec3

/-!
# Permutation invariance of the slab weights and the slope condition

The net argument of Section 5e permutes the coordinates of a lattice vector so
that it falls into the admissible family `Acoord`.  The two conditions used to
define the good set `Dset` (`cfP ≥ LAC/N` and the small-ball slope condition)
are invariant under coordinate permutations; this module proves the
combinatorial part (the slope condition) for the local definitions.
-/

/-- Sums of a permuted integer vector. -/
lemma sum_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (y : Fin n → ℤ) :
    (∑ i : Fin n, y (σ i)) = ∑ i : Fin n, y i :=
  Equiv.sum_comp σ y

/-- Sums of a permuted real vector. -/
lemma sum_comp_perm_real {n : ℕ} (σ : Equiv.Perm (Fin n)) (y : Fin n → ℝ) :
    (∑ i : Fin n, y (σ i)) = ∑ i : Fin n, y i :=
  Equiv.sum_comp σ y

/-- The subset-sum of a permuted vector is the subset-sum over the permuted
subset. -/
lemma rSub_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (y : Fin n → ℝ) (B : Finset (Fin n)) :
    rSub (fun i : Fin n => y (σ i)) B = rSub y (B.image σ) := by
  unfold rSub
  exact (Finset.sum_image (f := y) (g := σ) (s := B)
    (fun a _ b _ hab => σ.injective hab)).symm

/-- an image of a subset under a permutation has the same cardinality. -/
lemma card_image_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (B : Finset (Fin n)) :
    (B.image σ).card = B.card := Finset.card_image_of_injective B σ.injective

/-- membership in `slabB` in terms of the subset-sum condition. -/
lemma mem_slabB {n : ℕ} {z : Fin n → ℝ} {lam R : ℝ} {B : Finset (Fin n)} :
    B ∈ slabB z lam R ↔ |rSub z B - lam| ≤ R := by
  unfold slabB
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ B), h⟩

/-- the cardinality-only form of the Bernoulli weight. -/
lemma wB_card_eq {n : ℕ} (p : unitInterval) {B C : Finset (Fin n)} (h : B.card = C.card) :
    wB n p B = wB n p C := by
  unfold wB
  rw [h]

/-- The image of the permutation acting on subsets is injective. -/
lemma image_symm_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun C : Finset (Fin n) => C.image σ.symm) := by
  intro C D hCD
  have h := congrArg (fun E : Finset (Fin n) => E.image σ) hCD
  simpa [Finset.image_image] using h

/-- the slab family of a permuted vector. -/
lemma slabB_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (y : Fin n → ℝ) (lam R : ℝ) :
    slabB (fun i : Fin n => y (σ i)) lam R
      = (slabB y lam R).image (fun C : Finset (Fin n) => C.image σ.symm) := by
  ext B
  rw [mem_slabB, Finset.mem_image]
  constructor
  · intro hB
    refine ⟨B.image σ, ?_, ?_⟩
    · rw [mem_slabB, ← rSub_comp_perm σ y B]
      exact hB
    · rw [Finset.image_image]
      have h : (⇑(Equiv.symm σ) ∘ ⇑σ) = id := funext fun x => σ.symm_apply_apply x
      rw [h, Finset.image_id]
  · rintro ⟨C, hC, hCB⟩
    have hCmem : |rSub y C - lam| ≤ R := mem_slabB.mp hC
    rw [← hCB]
    have h : (⇑σ ∘ ⇑(Equiv.symm σ)) = id := funext fun x => σ.apply_symm_apply x
    simpa [rSub_comp_perm σ y (C.image σ.symm), Finset.image_image, h] using hCmem

/-- permutation invariance of the Bernoulli mass of a slab family. -/
lemma bMass_slabB_comp_perm {n : ℕ} (p : unitInterval) (σ : Equiv.Perm (Fin n))
    (y : Fin n → ℝ) (lam R : ℝ) :
    bMass p (slabB (fun i : Fin n => y (σ i)) lam R) = bMass p (slabB y lam R) := by
  classical
  unfold bMass
  rw [slabB_comp_perm σ y lam R]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro C _
    exact wB_card_eq p (card_image_perm σ.symm C)
  · exact fun a _ b _ hab => image_symm_injective σ hab

end Submission.NetInvariance
