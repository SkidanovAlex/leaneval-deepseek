/-
  WilC4 — the fibre formula of a `rexp`-existential family.

  Every `RExpExist` set `Y ⊆ ℝ^{k+1}` is the realization set of a single `LRc`-formula `φ`
  whose free variables are indexed by `Fin k ⊕ Fin 1`, in the coordinate convention of
  `WilkiesDesign.CG.UnifFiniteRExp`: the variable `Sum.inr 0` is the *fibre* coordinate `t`
  and `Sum.inl i` is the parameter `c i`, so that

      φ.Realize (Sum.elim c (fun _ => t))  ↔  Fin.cons t c ∈ Y.

  The mathematical content is the already-proved bridge `Work.WilC1.exists_existential_formula`
  (`REx` sets are the realization sets of existential `LRc`-formulas); what is added here is the
  change of variables that splits the ambient indexing `Fin (k+1)` into `Fin k ⊕ Fin 1` with the
  fibre coordinate coming first, i.e. the identification of
  `(Sum.elim c (fun _ => t)) ∘ fibreSplit k` with `Fin.cons t c`.
-/
import Mathlib
import Submission.Work.WilC4.UnifDefs
import Submission.Work.WilC1.Core
import Submission.Work.WilC1.exists_term_of_poly
import Submission.Work.WilC1.IsQF_isExistential_iExs
import Submission.Work.WilC1.REx_iff_RExpExist

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- The coordinate split `Fin (k+1) → Fin k ⊕ Fin 1` which puts the last coordinate first:
`0 ↦ Sum.inr 0` (the fibre coordinate) and `i.succ ↦ Sum.inl i` (the `i`-th parameter).  Its
inverse is `Sum.elim Fin.succ (fun _ => 0)`. -/
def fibreSplit (k : ℕ) : Fin (k + 1) → Fin k ⊕ Fin 1 :=
  Fin.cons (Sum.inr 0) (fun i => Sum.inl i)

@[simp] theorem fibreSplit_zero (k : ℕ) : fibreSplit k 0 = Sum.inr 0 :=
  Fin.cons_zero ..

@[simp] theorem fibreSplit_succ (k : ℕ) (i : Fin k) : fibreSplit k i.succ = Sum.inl i :=
  Fin.cons_succ ..

/-- Relabelling the split assignment along `fibreSplit` recovers the convention `Fin.cons t c`. -/
theorem elim_comp_fibreSplit {k : ℕ} (c : Fin k → ℝ) (t : ℝ) :
    (Sum.elim c (fun _ : Fin 1 => t)) ∘ fibreSplit k = Fin.cons t c := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp

theorem rexExist_fibre_formula {k : ℕ} (Y : Set (Fin (k + 1) → ℝ)) (hY : WilkiesDesign.RExpExist Y) :
    ∃ φ : WilkiesDesign.CG.LRc.Formula (Fin k ⊕ Fin 1), ∀ (c : Fin k → ℝ) (t : ℝ),
      (φ.Realize (Sum.elim c (fun _ => t)) ↔ Fin.cons t c ∈ Y) := by
  have hREx : Work.WilC1.REx (Fin (k + 1)) Y := (Work.WilC1.REx_iff_RExpExist Y).mpr hY
  obtain ⟨ψ, -, hψ⟩ := Work.WilC1.exists_existential_formula
    Work.WilC1.exists_term_of_poly
    (Work.WilC1.IsQF_isExistential_iExs (L := LRc))
    Y hREx
  refine ⟨ψ.relabel (fibreSplit k), ?_⟩
  intro c t
  rw [Formula.realize_relabel, hψ, elim_comp_fibreSplit]

end Work.WilC4
