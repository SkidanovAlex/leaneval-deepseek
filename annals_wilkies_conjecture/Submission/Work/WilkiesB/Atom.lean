import Submission.Work.WilkiesB.Closure
import Submission.Work.WilkiesB.eval_canonical
import Submission.Work.WilkiesB.expEval_csq_any

/-!
# Area B (syntax) — atomic formulas

The set of points where two terms of the language `ring ⊕ exp` take the same value is
existentially definable: flatten both terms with `valPoly`, combine the two value polynomials and
the `exp`-node equations into one sum of squares, and use `ExpElementI.term_eq`'s two ingredients
`eval_canonical` (the canonical witness satisfies the equations and computes the value) and
`expEval_csq_any` (any witness satisfying the equations computes the value).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open FirstOrder FirstOrder.Language
open MvPolynomial

namespace Work.WilkiesB

variable {A ι : Type*}

/-- **Atomic formulas.** For two terms `t₁ t₂` of `ring ⊕ exp`, the set of ambient points where
they agree is existentially definable. -/
theorem ExpExistI.term_eq (c : A → ℝ) (t₁ t₂ : Lexp.Term (A ⊕ ι)) :
    ExpExistI {u : ι → ℝ | t₁.realize (Sum.elim c u) = t₂.realize (Sum.elim c u)} := by
  let M : ℕ := numExp t₁ + numExp t₂
  have h₁ : 0 + numExp t₁ ≤ M := by omega
  have h₂ : numExp t₁ + numExp t₂ ≤ M := by omega
  let P : MvPolynomial ((ι ⊕ Fin M) ⊕ (ι ⊕ Fin M)) ℝ :=
    (valPoly c M t₁ 0 h₁ - valPoly c M t₂ (numExp t₁) h₂) ^ 2 +
      csq c M t₁ 0 h₁ + csq c M t₂ (numExp t₁) h₂
  refine ⟨Fin M, inferInstance, P, ?_⟩
  ext u
  constructor
  · intro hu
    have hu' : t₁.realize (Sum.elim c u) = t₂.realize (Sum.elim c u) := hu
    let y : Fin M → ℝ := Fin.append (nodeVals c u t₁) (nodeVals c u t₂)
    have hshift₁ : ∀ j : Fin (numExp t₁), shiftFin h₁ j = Fin.castAdd (numExp t₂) j := by
      intro j
      ext
      simp [shiftFin]
    have hshift₂ : ∀ j : Fin (numExp t₂), shiftFin h₂ j = Fin.natAdd (numExp t₁) j := by
      intro j
      ext
      simp [shiftFin, Fin.natAdd]
    have hy₁ : ∀ j : Fin (numExp t₁), y (shiftFin h₁ j) = nodeVals c u t₁ j := by
      intro j
      show Fin.append (nodeVals c u t₁) (nodeVals c u t₂) (shiftFin h₁ j) = nodeVals c u t₁ j
      rw [hshift₁ j]
      exact Fin.append_left _ _ j
    have hy₂ : ∀ j : Fin (numExp t₂), y (shiftFin h₂ j) = nodeVals c u t₂ j := by
      intro j
      show Fin.append (nodeVals c u t₁) (nodeVals c u t₂) (shiftFin h₂ j) = nodeVals c u t₂ j
      rw [hshift₂ j]
      exact Fin.append_right _ _ j
    obtain ⟨hc1, hv1⟩ := eval_canonical c u M t₁ 0 h₁ y hy₁
    obtain ⟨hc2, hv2⟩ := eval_canonical c u M t₂ (numExp t₁) h₂ y hy₂
    show ∃ y' : Fin M → ℝ, expEval (Sum.elim u y') P = 0
    refine ⟨y, ?_⟩
    simp only [P, expEval_add, expEval_pow, expEval_sub, hc1, hc2, hv1, hv2, hu']
    ring
  · intro hy
    obtain ⟨y, hy⟩ := hy
    obtain ⟨hn1, he1⟩ := expEval_csq_any c u M t₁ 0 h₁ y
    obtain ⟨hn2, he2⟩ := expEval_csq_any c u M t₂ (numExp t₁) h₂ y
    have hD : (expEval (Sum.elim u y) (valPoly c M t₁ 0 h₁) -
          expEval (Sum.elim u y) (valPoly c M t₂ (numExp t₁) h₂)) ^ 2 +
        expEval (Sum.elim u y) (csq c M t₁ 0 h₁) +
        expEval (Sum.elim u y) (csq c M t₂ (numExp t₁) h₂) = 0 := by
      rw [← hy]
      simp only [P, expEval_add, expEval_pow, expEval_sub]
    have hc1 : expEval (Sum.elim u y) (csq c M t₁ 0 h₁) = 0 := by
      linarith [sq_nonneg (expEval (Sum.elim u y) (valPoly c M t₁ 0 h₁) -
        expEval (Sum.elim u y) (valPoly c M t₂ (numExp t₁) h₂)), hn1, hn2, hD]
    have hc2 : expEval (Sum.elim u y) (csq c M t₂ (numExp t₁) h₂) = 0 := by
      linarith [sq_nonneg (expEval (Sum.elim u y) (valPoly c M t₁ 0 h₁) -
        expEval (Sum.elim u y) (valPoly c M t₂ (numExp t₁) h₂)), hn1, hn2, hD]
    have hab : expEval (Sum.elim u y) (valPoly c M t₁ 0 h₁) =
        expEval (Sum.elim u y) (valPoly c M t₂ (numExp t₁) h₂) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp (by
        linarith [sq_nonneg (expEval (Sum.elim u y) (valPoly c M t₁ 0 h₁) -
          expEval (Sum.elim u y) (valPoly c M t₂ (numExp t₁) h₂)), hn1, hn2, hD]))
    show t₁.realize (Sum.elim c u) = t₂.realize (Sum.elim c u)
    calc t₁.realize (Sum.elim c u)
        = expEval (Sum.elim u y) (valPoly c M t₁ 0 h₁) := (he1 hc1).symm
      _ = expEval (Sum.elim u y) (valPoly c M t₂ (numExp t₁) h₂) := hab
      _ = t₂.realize (Sum.elim c u) := he2 hc2

end Work.WilkiesB
