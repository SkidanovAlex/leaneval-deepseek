import Submission.Work.WilkiesB.Formula

/-!
# Area B (syntax) — the area theorem

`WilkiesDesign.B_syntax_proved` is the frozen hole `B_syntax` of `Submission/Work/Wilkies/Holes`,
proved here from the development in this directory: an index-generic version `ExpExistI` of
`ExpExist`, its closure properties, the flattening of nested `exp`-terms into one exp-polynomial
with auxiliary variables, and the induction on first-order formulas.  The only non-syntactic input
is Wilkie's theorem of the complement `hW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

open Classical
open FirstOrder FirstOrder.Language

namespace WilkiesDesign

open WilkiesConjecture

/-- **Area B (syntax, mechanical).** Flatten nested `exp` terms, push the Mathlib
`BoundedFormula` through ∧, ∨, ¬, ∃ and ∀. Complements are the hypothesis `hW`. -/
theorem B_syntax_proved
    (hW : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), ExpExist X → ExpExist Xᶜ)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : IsRExpDefinable X) : ExpExist X := by
  obtain ⟨φ, hφ⟩ := (Set.definable_iff_exists_formula_sum).mp h
  let c : ↥(Set.univ : Set ℝ) → ℝ := Subtype.val
  have hφ' : X = {v | φ.Realize (Sum.elim c v)} := hφ
  have hS : Work.WilkiesB.ExpExistI (Work.WilkiesB.Sof (A := ↥(Set.univ : Set ℝ)) c n φ) :=
    Work.WilkiesB.expExistI_Sof c n hW 0 φ
  have hpull : Work.WilkiesB.ExpExistI
      {z : Fin n → ℝ |
        z ∘ (Sum.elim id (Fin.elim0 : Fin 0 → Fin n)) ∈
          Work.WilkiesB.Sof (A := ↥(Set.univ : Set ℝ)) c n φ} :=
    Work.WilkiesB.ExpExistI.pullback (Sum.elim id (Fin.elim0 : Fin 0 → Fin n)) hS
  refine (Work.WilkiesB.expExist_iff_expExistI X).mpr ?_
  refine hpull.of_eq ?_
  rw [hφ']
  ext v
  simp only [Set.mem_ofPred_eq, Work.WilkiesB.Sof]
  have h1 : Sum.elim c ((v ∘ (Sum.elim id (Fin.elim0 : Fin 0 → Fin n))) ∘ Sum.inl)
      = Sum.elim c v := by
    funext q
    rcases q with a | i <;> rfl
  rw [h1]
  refine iff_of_eq ?_
  simp only [Formula.Realize]
  congr 1
  exact Subsingleton.elim _ _

end WilkiesDesign
