import Mathlib
import Submission.Work.WilE10.SubPfRexp.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10.SubPfRexp

open WilkiesDesign WilkiesDesign.E
open Work.WilC0

/-! ## Evaluating a substituted polynomial

The substitution `subst c L` sends the variable `Sum.inl i` of an EA polynomial to the
`rexp`-polynomial `X (Sum.inl (coordIdx i))` and the variable `Sum.inr j` to
`X (Sum.inr (Wit.tIdx j)) ^ L j`. Evaluating the result with `rexpEval p` therefore just asks
that the assignment `q ↦ rexpEval p (substVar c L q)` is the assignment
`Sum.elim z (fun j => exp (c.ell j z))` used by `eaEval`. The next lemma is the generic fact
that evaluating a substituted polynomial is evaluating the original one at the substituted
values. -/

/-- Evaluating a polynomial whose variables have been substituted by rexp-polynomials is the same
as evaluating the original polynomial at the substituted values. -/
theorem rexpEval_eval₂Hom {κ σ : Type} (h : σ → MvPolynomial (κ ⊕ κ) ℝ) (p : κ → ℝ)
    (f : MvPolynomial σ ℝ) :
    rexpEval p (MvPolynomial.eval₂Hom (algebraMap ℝ (MvPolynomial (κ ⊕ κ) ℝ)) h f)
      = MvPolynomial.eval (fun q => rexpEval p (h q)) f := by
  have h1 : (MvPolynomial.eval (Sum.elim p fun i => rexp (p i))).comp
      (algebraMap ℝ (MvPolynomial (κ ⊕ κ) ℝ)) = RingHom.id ℝ :=
    RingHom.ext fun r => MvPolynomial.eval_C (f := Sum.elim p fun i => rexp (p i)) r
  have key := MvPolynomial.map_eval₂Hom (algebraMap ℝ (MvPolynomial (κ ⊕ κ) ℝ)) h
    (MvPolynomial.eval (Sum.elim p fun i => rexp (p i))) f
  rw [h1] at key
  exact key

theorem reexpEval_subst {n m r P : ℕ} (c : WilkiesDesign.E.EAChain (n + m) r) (L : Fin r → ℕ)
    (f : WilkiesDesign.E.EAPoly (n + m) r) (p : Fin n ⊕ Work.WilE10.SubPfRexp.Wit n m r P → ℝ)
    (z : Fin (n + m) → ℝ)
    (hz : ∀ i, p (Work.WilE10.SubPfRexp.coordIdx (P := P) i) = z i)
    (ht : ∀ j, WilkiesDesign.rexp (p (Sum.inr (Work.WilE10.SubPfRexp.Wit.tIdx j))) ^ (L j)
        = Real.exp (c.ell j z)) :
    Work.WilC0.rexpEval p (Work.WilE10.SubPfRexp.subst c L f) = WilkiesDesign.E.eaEval c f z := by
  -- the two values of the substituted variable assignment
  have hXinl : ∀ i : Fin (n + m), rexpEval p (substVar c L (Sum.inl i)) = z i := by
    intro i
    simp only [substVar, Xc, rexpEval_X_inl]
    exact hz i
  have hXinr : ∀ j : Fin r, rexpEval p (substVar c L (Sum.inr j)) = Real.exp (c.ell j z) := by
    intro j
    simp only [substVar, Xr, rexpEval_pow, rexpEval_X_inr]
    exact ht j
  have hassign : (fun q => rexpEval p (substVar c L q))
      = Sum.elim z (fun j => Real.exp (c.ell j z)) := by
    funext q
    rcases q with i | j
    · rw [Sum.elim_inl]
      exact hXinl i
    · rw [Sum.elim_inr]
      exact hXinr j
  rw [show rexpEval p (subst c L f)
      = rexpEval p (MvPolynomial.eval₂Hom (algebraMap ℝ _) (substVar c L) f) from rfl,
    rexpEval_eval₂Hom (substVar c L) p f, hassign]
  rfl

end Work.WilE10.SubPfRexp
