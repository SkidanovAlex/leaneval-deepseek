import Mathlib
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.REx_preimage
import Submission.Work.WilC1.REx_inter
import Submission.Work.WilC1.REx_proj
import Submission.Work.WilC1.REx_union

set_option autoImplicit false
set_option linter.style.haveILetI false

open Classical FirstOrder FirstOrder.Language

namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-! ## The graph of `tRexp t` from the graph of `t`

`GraphSet (tRexp t) ⊆ ℝ^{ι ⊕ Fin 1}` is the graph of `x ↦ rexp (⟦t⟧ x)`.  To present it as a
projection of a zero set we introduce one extra witness coordinate `w : Fin 1 → ℝ` whose value is
`⟦t⟧ x`, and impose the two conditions

* `w` is the value of `t` on the `ι`-coordinates of `x` (i.e. the point `x` with its last
  coordinate replaced by `w 0` lies in `GraphSet t`), and
* the last coordinate of `x` equals `rexp (w 0)`.

Both conditions are `REx` (`REx_preimage` for the first, a zero set for the second), so their
intersection is `REx`, and projecting the witness block `Fin 1` away gives `GraphSet (tRexp t)`.
-/

/-- The embedding that realises the above bookkeeping: it carries the `ι`-coordinates into the
left block (which will carry `GraphSet t`) and the last coordinate to the new witness. -/
def rexpEmb {ι : Type*} : (ι ⊕ Fin 1) → ((ι ⊕ Fin 1) ⊕ Fin 1) :=
  Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun j => Sum.inr j)

/-- Splitting a point of the enlarged space into the graph part and the witness. -/
theorem sumElim_comp_rexpEmb {ι : Type*} (x : (ι ⊕ Fin 1) → ℝ) (w : Fin 1 → ℝ) :
    Sum.elim x w ∘ rexpEmb = Sum.elim (x ∘ Sum.inl) w := by
  funext q
  rcases q with i | j <;> rfl

/-- A point `Sum.elim (x ∘ Sum.inl) w` lies in `GraphSet t` exactly when the witness `w 0` is the
value of `t` on the coordinates `x ∘ Sum.inl`. -/
theorem sumElim_mem_GraphSet_iff {ι : Type*} {t : LRc.Term ι}
    (x : (ι ⊕ Fin 1) → ℝ) (w : Fin 1 → ℝ) :
    Sum.elim (x ∘ Sum.inl) w ∈ GraphSet t ↔ w 0 = Term.realize (x ∘ Sum.inl) t := by
  simp only [GraphSet, Set.mem_ofPred_eq, Sum.elim_inr, Sum.elim_comp_inl]

/-- The `rexp`-link condition, spelled out on the components. -/
theorem sumElim_mem_rexpLink_iff {ι : Type*} (x : (ι ⊕ Fin 1) → ℝ) (w : Fin 1 → ℝ) :
    Sum.elim x w (Sum.inl (Sum.inr (0 : Fin 1))) = rexp (Sum.elim x w (Sum.inr (0 : Fin 1)))
      ↔ x (Sum.inr 0) = rexp (w 0) := by
  simp only [Sum.elim_inl, Sum.elim_inr]

theorem REx_graph_tRexp {ι : Type*} {t : WilkiesDesign.CG.LRc.Term ι}
    (h : REx (ι ⊕ Fin 1) (GraphSet t)) : REx (ι ⊕ Fin 1) (GraphSet (tRexp t)) := by
  -- the graph condition, pulled back along `rexpEmb`
  have hA : REx ((ι ⊕ Fin 1) ⊕ Fin 1)
      {u : ((ι ⊕ Fin 1) ⊕ Fin 1) → ℝ | u ∘ rexpEmb ∈ GraphSet t} :=
    REx_preimage (rexpEmb (ι := ι)) h
  -- the link `last coordinate = rexp (witness)`
  have hB : REx ((ι ⊕ Fin 1) ⊕ Fin 1)
      {u : ((ι ⊕ Fin 1) ⊕ Fin 1) → ℝ |
        u (Sum.inl (Sum.inr (0 : Fin 1))) = rexp (u (Sum.inr (0 : Fin 1)))} := by
    refine (REx.zeroSet (ι := (ι ⊕ Fin 1) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
       MvPolynomial.X (Sum.inr (Sum.inr (0 : Fin 1))))).congr ?_
    ext u
    simp only [Set.mem_ofPred_eq, rexpEval_sub, rexpEval_X_inl, rexpEval_X_inr, sub_eq_zero]
  -- project the witness block `Fin 1` away
  refine REx.congr ?_ (REx_proj 1 (REx_inter hA hB))
  ext x
  constructor
  · rintro ⟨w, hwA, hwB⟩
    simp only [Set.mem_ofPred_eq] at hwA hwB
    have hw1 : w 0 = Term.realize (x ∘ Sum.inl) t := by
      rw [sumElim_comp_rexpEmb] at hwA
      exact (sumElim_mem_GraphSet_iff x w).mp hwA
    have hw2 : x (Sum.inr 0) = rexp (w 0) := (sumElim_mem_rexpLink_iff x w).mp hwB
    have hiff : x ∈ GraphSet (tRexp t) ↔
        x (Sum.inr 0) = rexp (Term.realize (x ∘ Sum.inl) t) := by
      simp only [GraphSet, Set.mem_ofPred_eq, realize_tRexp]
    rw [hiff, hw2, hw1]
  · intro hx
    have hiff : x ∈ GraphSet (tRexp t) ↔
        x (Sum.inr 0) = rexp (Term.realize (x ∘ Sum.inl) t) := by
      simp only [GraphSet, Set.mem_ofPred_eq, realize_tRexp]
    have hxR := hiff.mp hx
    refine ⟨fun _ => Term.realize (x ∘ Sum.inl) t, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [sumElim_comp_rexpEmb]
      exact (sumElim_mem_GraphSet_iff x (fun _ => Term.realize (x ∘ Sum.inl) t)).mpr rfl
    · simp only [Set.mem_ofPred_eq]
      exact (sumElim_mem_rexpLink_iff x (fun _ => Term.realize (x ∘ Sum.inl) t)).mpr hxR

end Work.WilC1
