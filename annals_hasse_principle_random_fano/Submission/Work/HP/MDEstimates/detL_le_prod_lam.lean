import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.detL_span_gram
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.numaux.det_le_prod_diag
import Submission.Work.HP.numaux.detL_le_of_le
import Submission.Work.HP.numaux.detL_span_le_prod
import Submission.Work.HP.det_gam_gen

/-!
# `detL L ≤ λ₁(L)···λ_n(L)`

For an integral lattice `L ⊆ ℤ^ι` of rank `n`, the covolume `Work.HP.detL L` is at most the
product `λ₁(L)···λ_n(L)` of its successive minima (`Work.HP.lam`), the elementary half of
Minkowski's second theorem.

The proof is the classical one.

* `exists_linIndep_le_lam` produces `ℤ`-linearly independent vectors `v_1, …, v_n ∈ L` with
  `‖v_j‖ ≤ λ_j`: each successive minimum is attained (`Q44Child.lamAttained_aux`), and one
  appends the vectors one at a time to a family of independent vectors
  (`Q44Child.lamAttained_snoc`).
* The `ℤ`-span `L' = ℤv_1 + ⋯ + ℤv_n` is a sublattice of `L` of the same rank, so
  `detL L ≤ detL L'` (`Work.HP.DGG.detL_le_of_le`, the index formula for equal-rank inclusions).
* Hadamard's inequality bounds `detL L' ≤ ∏ ‖v_j‖ ≤ ∏ λ_j`
  (`detL_span_le_prod` below, the universe-polymorphic form of
  `Work.HP.numaux.detL_span_le_prod`).

Everything is universe-polymorphic in `ι`; the corresponding lemmas of `Work.HP.numaux` and
`Work.HP.FM.minkowski_lower` are stated for `{ι : Type}`, so the two inputs that are only
available there in universe `0` are reproduced here in the generality needed by the statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.MDEstimates

/-- The successive minima are met index by index: for `m ≤ rk L` there are `m` `ℤ`-linearly
independent vectors of `L` whose `j`-th one has norm at most the `(j+1)`-st successive minimum
`lam L (j+1)`. -/
lemma exists_linIndep_le_lam {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) {m : ℕ} (hm : m ≤ Work.HP.rk L) :
    ∃ f : Fin m → (ι → ℤ), (∀ i, f i ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ i, Work.HP.eNorm (f i) ≤ Work.HP.lam L (i.1 + 1) := by
  have key : ∀ m : ℕ, m ≤ Work.HP.rk L → ∃ f : Fin m → (ι → ℤ), (∀ i, f i ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ i, Work.HP.eNorm (f i) ≤ Work.HP.lam L (i.1 + 1) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨fun i => i.elim0, fun i => i.elim0, linearIndependent_empty_type,
        fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfI, hfb⟩ := ih (by omega)
      obtain ⟨g, hgL, hgI, hgb⟩ :=
        Work.HP.Q44Child.lamAttained_aux (i := k + 1) L (by omega)
      obtain ⟨t, ht⟩ := Work.HP.Q44Child.lamAttained_snoc hfI hgI
      refine ⟨Fin.snoc f (g t), ?_, ht, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨m, rfl⟩ | rfl
        · simpa using hfL m
        · simpa using hgL t
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨m, rfl⟩ | rfl
        · simpa using hfb m
        · simpa using hgb t
  exact key m hm

/-- **Hadamard's inequality for the covolume of a lattice spanned by an independent family.**
`detL` of the `ℤ`-span of `ℤ`-linearly independent vectors `b j` is at most the product of their
Euclidean norms.  (Universe-polymorphic form of `Work.HP.numaux.detL_span_le_prod`.) -/
theorem detL_span_le_prod {ι : Type*} [Fintype ι] {r : ℕ} {b : Fin r → (ι → ℤ)}
    (hb : LinearIndependent ℤ b) :
    Work.HP.detL (Submodule.span ℤ (Set.range b)) ≤ ∏ j : Fin r, Work.HP.eNorm (b j) := by
  -- Hadamard for the Gram determinant of the real vectors underlying `b`.
  have h2 : Matrix.det (Matrix.of fun i j => ∑ a, (b i a : ℝ) * (b j a : ℝ))
      ≤ ∏ i, (Work.HP.eNorm (b i)) ^ 2 := by
    refine (Work.HP.numaux.det_gram_le_prod_sq (ι := ι) (fun i a => (b i a : ℝ))).trans (le_of_eq ?_)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Work.HP.eNorm, Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)]
  -- `detL` of the span is the square root of that Gram determinant.
  rw [Work.HP.Lat.detL_span_gram r b hb]
  refine Real.sqrt_le_iff.mpr ⟨Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _, ?_⟩
  rw [← Finset.prod_pow Finset.univ 2 (fun j => Work.HP.eNorm (b j))]
  exact h2

theorem detL_le_prod_lam {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) :
    Work.HP.detL L ≤ ∏ i ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (i + 1) := by
  obtain ⟨f, hfL, hfI, hfb⟩ := exists_linIndep_le_lam L (m := Work.HP.rk L) le_rfl
  -- The `ℤ`-span of the family: a sublattice of `L` of the same rank.
  have hPL : Submodule.span ℤ (Set.range f) ≤ L :=
    Submodule.span_le.mpr (by rintro x ⟨j, rfl⟩; exact hfL j)
  have hrk : Work.HP.rk (Submodule.span ℤ (Set.range f)) = Work.HP.rk L := by
    rw [Work.HP.rk, Module.finrank_eq_card_basis (Module.Basis.span hfI)]
    simp
  -- `detL` is antitone for inclusions of equal rank.
  have h1 : Work.HP.detL L ≤ Work.HP.detL (Submodule.span ℤ (Set.range f)) :=
    Work.HP.DGG.detL_le_of_le hPL hrk
  -- Hadamard's inequality for the covolume of the span.
  have h2 : Work.HP.detL (Submodule.span ℤ (Set.range f))
      ≤ ∏ j : Fin (Work.HP.rk L), Work.HP.eNorm (f j) :=
    detL_span_le_prod hfI
  have h3 : (∏ j : Fin (Work.HP.rk L), Work.HP.eNorm (f j))
      ≤ ∏ j : Fin (Work.HP.rk L), Work.HP.lam L (j.1 + 1) :=
    Finset.prod_le_prod₀ (fun _ _ => Work.HP.eNorm_nonneg _) fun j _ => hfb j
  have h4 : (∏ j : Fin (Work.HP.rk L), Work.HP.lam L (j.1 + 1))
      = ∏ i ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (i + 1) :=
    Fin.prod_univ_eq_prod_range (fun i => Work.HP.lam L (i + 1)) (Work.HP.rk L)
  calc Work.HP.detL L ≤ Work.HP.detL (Submodule.span ℤ (Set.range f)) := h1
    _ ≤ ∏ j : Fin (Work.HP.rk L), Work.HP.eNorm (f j) := h2
    _ ≤ ∏ j : Fin (Work.HP.rk L), Work.HP.lam L (j.1 + 1) := h3
    _ = ∏ i ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (i + 1) := h4

end Work.HP.MDEstimates
