import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs

/-!
# Shared definitions for the diagonal bound (`Work.HP.diag_bound`)

This file collects the definitions and elementary plumbing lemmas used by the proof of
`Work.HP.diag_bound` and by the auxiliary lemmas delegated for it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Filter Finset

namespace Work.HP

/-- The single-vector version of the paper's `μ`: `μ(x) = n ‖x‖ / 𝔡₂(x)`, where `𝔡₂(x)` is the
least determinant of a rank-two sublattice of `ℤ^{n+1}` containing `x`. -/
def mu1 (d n : ℕ) (x : Fin (n + 1) → ℤ) : ℝ := n * eNorm x / dmin 2 {x}

variable {ι : Type*} [Fintype ι]

/-- Each coordinate of an integer vector is bounded by its Euclidean norm. -/
lemma abs_coord_le_eNorm (v : ι → ℤ) (i : ι) : |((v i : ℤ) : ℝ)| ≤ eNorm v := by
  rw [eNorm, ← Real.sqrt_sq (abs_nonneg _), sq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (f := fun j => ((v j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i))

end Work.HP

namespace Work.HP

open Filter Finset

variable {α β : Type*} {M : Type*} [AddCommMonoid M]

/-- A finsum over a finite set is the corresponding `Finset` sum. -/
lemma finsum_mem_of_finite (s : Set α) (hs : s.Finite) (f : α → M) :
    (∑ᶠ a ∈ s, f a) = ∑ a ∈ hs.toFinset, f a := by
  rw [finsum_mem_def]
  have hsupp : Function.support (s.indicator f) ⊆ ↑hs.toFinset := by
    intro a ha
    rw [Function.mem_support] at ha
    by_contra h
    have ha' : a ∉ s := fun has => h (hs.mem_toFinset.mpr has)
    rw [Set.indicator_of_notMem ha'] at ha
    exact ha rfl
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Set.indicator_of_mem (hs.mem_toFinset.mp ha)]

/-- Swapping the order of two finsums over finite sets. -/
lemma finsum_mem_comm (s : Set α) (t : Set β) (hs : s.Finite) (ht : t.Finite)
    (f : α → β → M) :
    (∑ᶠ a ∈ s, ∑ᶠ b ∈ t, f a b) = ∑ᶠ b ∈ t, ∑ᶠ a ∈ s, f a b := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite t ht]
  have h1 : (∑ a ∈ hs.toFinset, ∑ᶠ b ∈ t, f a b)
      = ∑ a ∈ hs.toFinset, ∑ b ∈ ht.toFinset, f a b :=
    Finset.sum_congr rfl fun a _ => finsum_mem_of_finite t ht (f a)
  have h2 : (∑ b ∈ ht.toFinset, ∑ᶠ a ∈ s, f a b)
      = ∑ b ∈ ht.toFinset, ∑ a ∈ hs.toFinset, f a b :=
    Finset.sum_congr rfl fun b _ => finsum_mem_of_finite s hs (fun a => f a b)
  rw [h1, h2, Finset.sum_comm]

/-- The set `Ξ_{d,n}(B)` is finite. -/
lemma Xi_finite (d n : ℕ) (B : ℝ) : (Xi d n B).Finite := by
  have hbox : (Set.univ.pi (fun _ : Fin (n + 1) =>
      Set.Icc (-⌈B ^ (1 / ((n : ℝ) + 1 - d))⌉) ⌈B ^ (1 / ((n : ℝ) + 1 - d))⌉)).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine hbox.subset ?_
  intro x hx
  rw [Set.mem_univ_pi]
  intro i
  rw [Set.mem_Icc]
  have h1 : |((x i : ℤ) : ℝ)| ≤ eNorm x := abs_coord_le_eNorm x i
  have h2 : eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := hx.2
  have h3 : ((x i : ℤ) : ℝ) ≤ ((⌈B ^ (1 / ((n : ℝ) + 1 - d))⌉ : ℤ) : ℝ) :=
    le_trans (le_trans (le_abs_self ((x i : ℤ) : ℝ)) (le_trans h1 h2)) (Int.le_ceil _)
  have h4 : (((-⌈B ^ (1 / ((n : ℝ) + 1 - d))⌉ : ℤ)) : ℝ) ≤ ((x i : ℤ) : ℝ) := by
    push_cast
    exact le_trans (le_trans (neg_le_neg (Int.le_ceil _)) (neg_le_neg h2))
      (le_trans (neg_le_neg h1) (neg_abs_le ((x i : ℤ) : ℝ)))
  exact ⟨Int.cast_le.mp h4, Int.cast_le.mp h3⟩

/-- The set of primitive coefficient vectors of height `≤ A` satisfying `P` is finite. -/
lemma primSet_finite (d n : ℕ) (A : ℝ) (P : (Mon d n → ℤ) → Prop) :
    (primSet d n A P).Finite := by
  have hbox : (Set.univ.pi (fun _ : Mon d n => Set.Icc (-⌈A⌉) ⌈A⌉)).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine hbox.subset ?_
  intro a ha
  rw [Set.mem_univ_pi]
  intro i
  rw [Set.mem_Icc]
  have h1 : |((a i : ℤ) : ℝ)| ≤ eNorm a := abs_coord_le_eNorm a i
  have h2 : eNorm a ≤ A := ha.2.1
  have h3 : ((a i : ℤ) : ℝ) ≤ ((⌈A⌉ : ℤ) : ℝ) :=
    le_trans (le_trans (le_abs_self ((a i : ℤ) : ℝ)) (le_trans h1 h2)) (Int.le_ceil A)
  have h4 : (((-⌈A⌉ : ℤ)) : ℝ) ≤ ((a i : ℤ) : ℝ) := by
    push_cast
    exact le_trans (le_trans (neg_le_neg (Int.le_ceil A)) (neg_le_neg h2))
      (le_trans (neg_le_neg h1) (neg_abs_le ((a i : ℤ) : ℝ)))
  exact ⟨Int.cast_le.mp h4, Int.cast_le.mp h3⟩

end Work.HP
