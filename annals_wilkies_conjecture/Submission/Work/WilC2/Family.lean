/-
  Area C2 (WilC2): the family of subsets of `ℝ^{n+1}` attached to a parametric formula
  `φ : LRc.Formula (Fin n ⊕ Fin 1)`, in the coordinate convention of `UnifFiniteRExp`
  (fibre coordinate fist, then the parameters).
-/
import Submission.Work.WilC2.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- The graph family of `φ`: `z ∈ familyOf φ` iff `φ` holds at `(z 1, …, z n)` for the point
`z 0`.  This matches the fibre convention `{t | Fin.cons t c ∈ Y}` of `UnifFiniteRExp`. -/
def familyOf {n : ℕ} (φ : ParamFormula n) : Set (Fin (n + 1) → ℝ) :=
  {z | φ.Realize (Sum.elim (fun i : Fin n => z i.succ) (fun _ : Fin 1 => z 0))}

/-- The fibres of `familyOf φ` are the fibres of `φ`. -/
theorem familyOf_fibre {n : ℕ} (φ : ParamFormula n) (c : Fin n → ℝ) (t : ℝ) :
    Fin.cons t c ∈ familyOf φ ↔ φ.Realize (Sum.elim c (fun _ => t)) := by
  simp only [familyOf, Set.mem_ofPred_eq, Fin.cons_zero, Fin.cons_succ]

/-- `familyOf φ` is definable in `LRc` without parameters. -/
theorem familyOf_definable {n : ℕ} (φ : ParamFormula n) :
    (∅ : Set ℝ).Definable LRc (familyOf φ) := by
  rw [Set.empty_definable_iff]
  refine ⟨Formula.relabel
    (Sum.elim (fun i : Fin n => (Fin.succ i : Fin (n + 1))) (fun _ : Fin 1 => (0 : Fin (n + 1))))
    φ, ?_⟩
  ext z
  simp only [Set.mem_ofPred_eq, familyOf, Formula.realize_relabel]
  have h : (z ∘ Sum.elim (fun i : Fin n => (Fin.succ i : Fin (n + 1))) (fun _ : Fin 1 => 0))
      = Sum.elim (fun i : Fin n => z i.succ) (fun _ : Fin 1 => z 0) := by
    funext a
    rcases a with i | k <;> simp [Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
  rw [h]

end Work.WilC2
