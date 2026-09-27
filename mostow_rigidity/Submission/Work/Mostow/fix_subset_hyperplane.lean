import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Hyper

/-!
# A nontrivial element of `PO(n,1)` fixes only a set lying in a hyperplane

For `A : O(n,1)` with `A ≠ ±1` on the hyperboloid one has
`hlift (actO A u) = tsign A • (mat A *ᵥ hlift u)`, so a chart point `u` fixed by `A` satisfies
`mat A *ᵥ hlift u = tsign A • hlift u`: its lift lies in the eigenspace of `mat A` for the
eigenvalue `tsign A`. Since `A ∉ {±1}`, that eigenspace is a proper subspace of `ℝ^{Fin n ⊕ Fin 1}`
(if it were everything, `A` would act as the identity on `ℍⁿ`, hence `A = 1` in `PO(n,1)`), so a
nonzero linear functional `l` vanishes on it. The functional can be taken to be a nonzero *row*
`l s = M r s` of the matrix `M = mat A − tsign A • 1`, because `ker M ⊆ ker (row r)`.

This is the lemma used to see that the fixed set of a nontrivial isometry of `ℍⁿ` is a null set
(it is contained in the level set `{u : ∑ i, l i * hlift u i = 0}` of a nonzero affine functional).

Main result: `Work.Mostow.fix_subset_hyperplane`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-- The eigenvalue-`tsign A` eigenspace of `mat A` is a proper subspace whenever `A` is not the
identity of `PO(n,1)`: if `mat A = tsign A • 1` then `A` acts trivially on `ℍⁿ`. -/
lemma mat_sub_tsign_smul_one_ne_zero (hA : POActionProp n) (A : O1 n)
    (hA1 : (A : PO n 1) ≠ 1) :
    mat A - tsign A • (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) ≠ 0 := by
  intro hM
  have hMA : mat A = tsign A • (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
    sub_eq_zero.mp hM
  have hfix : ∀ u : E n, (A : PO n 1) • u = u := by
    intro u
    rw [hA.2.1 A u]
    apply hlift_injective
    rw [Submission.Mostow.Hyper.hlift_actO A u, hMA, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, tsign_sq, one_smul]
  exact hA1 (hA.2.2.2.2.2.1 (A : PO n 1) hfix)

/-- A chart point fixed by `A` has its hyperboloid lift in the eigenspace of `mat A` for the
eigenvalue `tsign A`. -/
lemma mulVec_hlift_eq_tsign_smul (hA : POActionProp n) (A : O1 n) {u : E n}
    (hu : (A : PO n 1) • u = u) :
    mat A *ᵥ hlift u = tsign A • hlift u := by
  have h2 : actO A u = u := by rw [← hA.2.1 A u]; exact hu
  have h3 := Submission.Mostow.Hyper.hlift_actO A u
  rw [h2] at h3
  have h4 := congrArg (fun w : Fin n ⊕ Fin 1 → ℝ => tsign A • w) h3
  rw [smul_smul, tsign_sq, one_smul] at h4
  exact h4.symm

/-- **A nontrivial element of `PO(n,1)` fixes only points lying in a hyperplane**: there is a
nonzero linear functional `l` on `ℝ^{Fin n ⊕ Fin 1}` such that every fixed point `u` of `g`
satisfies `∑ i, l i * hlift u i = 0`. -/
theorem fix_subset_hyperplane (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hg : g ≠ 1) :
    ∃ l : Fin n ⊕ Fin 1 → ℝ, l ≠ 0 ∧ ∀ u : Submission.Mostow.E n,
      g • u = u → (∑ i, l i * Submission.Mostow.hlift u i) = 0 := by
  set A : O1 n := rep g with hAdef
  have hAg : (A : PO n 1) = g := by rw [hAdef]; exact Quotient.out_eq g
  set M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    mat A - tsign A • (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) with hMdef
  have hMne : M ≠ 0 := by
    rw [hMdef]
    exact mat_sub_tsign_smul_one_ne_zero hA A (by rw [hAg]; exact hg)
  obtain ⟨r, c, hrc⟩ : ∃ r c : Fin n ⊕ Fin 1, M r c ≠ 0 := by
    by_contra h
    push Not at h
    exact hMne (by ext r c; simpa using h r c)
  refine ⟨fun s => M r s, ?_, ?_⟩
  · intro hl
    exact hrc (by simpa using congrFun hl c)
  · intro u hu
    have hmv : M *ᵥ hlift u = 0 := by
      have h1 : mat A *ᵥ hlift u = tsign A • hlift u :=
        mulVec_hlift_eq_tsign_smul hA A (by rw [hAg]; exact hu)
      rw [hMdef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, sub_self]
    have hrow : (M *ᵥ hlift u) r = 0 := by rw [hmv]; rfl
    simpa [Matrix.mulVec, dotProduct] using hrow

end

end Work.Mostow
