import Submission.Work.WilkiesB.Closure
import Submission.Work.WilkiesB.Atom

/-!
# Area B (syntax) — pushing a first-order formula into `ExpExistI`

For a bounded formula `φ` of the language `ring ⊕ exp` with free variables `A ⊕ Fin n` (the `A`
part is the constant real parameter `c`) and `k` bound variables, `Sof c n φ` is the set of
`(Fin n ⊕ Fin k)`-tuples satisfying `φ`.  The main theorem `expExistI_Sof` shows, by induction on
the formula, that `Sof c n φ` is always existentially definable, using the closure properties of
`ExpExistI` (`Closure.lean`) and the atomic case (`Atom.lean`).

Complements are the hypothesis `hW` (Wilkie's complement theorem for `ℝ_exp`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

open FirstOrder FirstOrder.Language
open MvPolynomial

namespace Work.WilkiesB

variable {A : Type*}

/-- The set of `(Fin n ⊕ Fin k)`-tuples satisfying the bounded formula `φ`, whose free variables
are `A ⊕ Fin n` with the `A`-part fixed to the parameter `c`, and which has `k` bound variables. -/
def Sof (c : A → ℝ) (n : ℕ) {k : ℕ} (φ : Lexp.BoundedFormula (A ⊕ Fin n) k) :
    Set ((Fin n ⊕ Fin k) → ℝ) :=
  {u | φ.Realize (Sum.elim c (u ∘ Sum.inl)) (u ∘ Sum.inr)}

/-- The parameter assignment on `(A ⊕ Fin n) ⊕ Fin k` corresponding to a point `u`. -/
theorem sumElim_comp_sumAssoc_fin {n k : ℕ} (c : A → ℝ) (u : (Fin n ⊕ Fin k) → ℝ) :
    (Sum.elim c u) ∘ ⇑(Equiv.sumAssoc A (Fin n) (Fin k))
      = Sum.elim (Sum.elim c (u ∘ Sum.inl)) (u ∘ Sum.inr) := by
  funext q
  rcases q with (a | i) | j <;> rfl

theorem comp_snocEquiv_inl {n k : ℕ} (u : (Fin n ⊕ Fin k) → ℝ) (t : Fin 1 → ℝ) :
    ((Sum.elim u t) ∘ ⇑(sumFinSnocEquiv (Fin n) k)) ∘ Sum.inl = u ∘ Sum.inl := by
  funext i
  simp

theorem comp_snocEquiv_inr {n k : ℕ} (u : (Fin n ⊕ Fin k) → ℝ) (t : Fin 1 → ℝ) :
    ((Sum.elim u t) ∘ ⇑(sumFinSnocEquiv (Fin n) k)) ∘ Sum.inr
      = snocReal (u ∘ Sum.inr) (t 0) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- The set-theoretic identity behind the universal-quantifier step. -/
theorem Sof_all_eq {n k : ℕ} (c : A → ℝ) (ψ : Lexp.BoundedFormula (A ⊕ Fin n) (k + 1)) :
    Sof c n (.all ψ) =
      ({u : (Fin n ⊕ Fin k) → ℝ | ∃ t : Fin 1 → ℝ,
        Sum.elim u t ∈ {z : ((Fin n ⊕ Fin k) ⊕ Fin 1) → ℝ |
          z ∘ ⇑(sumFinSnocEquiv (Fin n) k) ∈ (Sof c n ψ)ᶜ}})ᶜ := by
  ext u
  simp only [Sof, Set.mem_ofPred_eq, Set.mem_compl_iff, BoundedFormula.realize_all]
  constructor
  · rintro h ⟨t, ht⟩
    rw [comp_snocEquiv_inl, comp_snocEquiv_inr] at ht
    exact ht (h (t 0))
  · intro h s
    by_contra hs
    refine h ⟨fun _ => s, ?_⟩
    rw [comp_snocEquiv_inl, comp_snocEquiv_inr]
    simpa [snocReal] using hs

/-- **The syntax induction.** Every bounded formula of `ring ⊕ exp` (with real parameters and
arbitrary quantifiers) defines an existentially definable set, assuming Wilkie's complement
theorem `hW`. -/
theorem expExistI_Sof (c : A → ℝ) (n : ℕ)
    (hW : ∀ (m : ℕ) (X : Set (Fin m → ℝ)), WilkiesDesign.ExpExist X → WilkiesDesign.ExpExist Xᶜ) :
    (k : ℕ) → (φ : Lexp.BoundedFormula (A ⊕ Fin n) k) → ExpExistI (Sof c n φ)
  | _, .falsum => ExpExistI_empty
  | k, .equal t₁ t₂ =>
      have hterm := ExpExistI.term_eq c (t₁.relabel ⇑(Equiv.sumAssoc A (Fin n) (Fin k)))
        (t₂.relabel ⇑(Equiv.sumAssoc A (Fin n) (Fin k)))
      hterm.of_eq (by
        ext u
        simp only [Sof, Set.mem_ofPred_eq]
        rw [Term.realize_relabel, Term.realize_relabel, sumElim_comp_sumAssoc_fin]
        exact Iff.rfl)
  | _, .rel R _ => Sum.elim (fun h => h.elim) (fun h => h.elim) R
  | k, .imp ψ₁ ψ₂ =>
      (ExpExistI.union ((expExistI_Sof c n hW k ψ₁).compl hW)
        (expExistI_Sof c n hW k ψ₂)).of_eq (by
          ext u
          simp only [Sof, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
            BoundedFormula.realize_imp]
          exact imp_iff_not_or.symm)
  | k, .all ψ =>
      (ExpExistI.compl hW (ExpExistI.existsBlock (μ := Fin 1)
        (ExpExistI.pullback ⇑(sumFinSnocEquiv (Fin n) k)
          (ExpExistI.compl hW (expExistI_Sof c n hW (k + 1) ψ))))).of_eq
        (Sof_all_eq c ψ).symm

end Work.WilkiesB
