/-
  WilE7, fiber finiteness: specialization of a semi-Pfaffian set at a base point.

  The target lemma `Work.WilE7.fiber_finite_of_good_full_rank` (in
  `Submission/Work/WilE7/fiber_finite_of_good_full_rank.lean`) shows that a `Good` stratum with
  `S.j = q` has finite fibres.  Its route is:

  * the fibre `{y | Fin.append x y ∈ X.set}` of a semi-Pfaffian set `X ⊆ ℝ^{p+q}` is *itself* the
    set of a semi-Pfaffian set in `ℝ^q` — the *specialization* of `X` at the base point `x`;
  * `E2_components` bounds the number of connected components of that set;
  * a stratum with `S.j = q` is `q`-dimensional in the fibre direction (`Good` says its fibrewise
    Jacobian is invertible), so its fibre is *discrete*: each connected component is a point.

  This file contains the specialization (`speChainAt`, `spePolyAt`, `speBasicAt`, `speSemiPfAt`)
  and the identity computing the evaluated substituted polynomial,
  `eaEval_speAt : eaEval (speChainAt x c) (spePolyAt x Q) y = eaEval c Q (Fin.append x y)`.
  The set-level statement `(speSemiPfAt x X).set = fiber X.set x` is proved separately.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Specializing an EA chain at a base point -/

/-- The chain of `X` specialized at the base point `x`: the `p` base coordinates are dropped
(their contribution is moved into the constants, where the chain functions are `exp (c'.ell j y)`)
and the `q` fibre coordinates are kept. -/
def speChainAt {p q r : ℕ} (x : Fin p → ℝ) (c : EAChain (p + q) r) : EAChain q r :=
  ⟨fun j l => c.a j (Fin.natAdd p l),
   fun j => c.b j + ∑ i : Fin p, c.a j (Fin.castAdd q i) * x i⟩

/-- The defining identity of the specialized chain: `c'.ell j y = c.ell j (x, y)`. -/
theorem speChainAt_ell {p q r : ℕ} (x : Fin p → ℝ) (c : EAChain (p + q) r) (j : Fin r)
    (y : Fin q → ℝ) : (speChainAt x c).ell j y = c.ell j (Fin.append x y) := by
  unfold EAChain.ell speChainAt
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

/-! ## The variable substitution -/

/-- The variable substitution underlying `speChainAt`: the `p` base variables become the constants
`x i`, and the `q` fibre variables and the `r` chain variables keep their names. -/
def speVarAt {p q r : ℕ} (x : Fin p → ℝ) :
    Fin (p + q) ⊕ Fin r → MvPolynomial (Fin q ⊕ Fin r) ℝ :=
  Sum.elim (Fin.addCases (fun i : Fin p => MvPolynomial.C (x i))
      (fun l : Fin q => MvPolynomial.X (Sum.inl l)))
    (fun j : Fin r => MvPolynomial.X (Sum.inr j))

/-- Substitution of polynomials along `speVarAt`. -/
def spePolyAt {p q r : ℕ} (x : Fin p → ℝ) (Q : EAPoly (p + q) r) : EAPoly q r :=
  MvPolynomial.eval₂Hom MvPolynomial.C (speVarAt (q := q) (r := r) x) Q

/-- The substitution computes evaluation at the glued point: for every `y`,
`eaEval (speChainAt x c) (spePolyAt x Q) y = eaEval c Q (Fin.append x y)`. -/
theorem eaEval_speAt {p q r : ℕ} (x : Fin p → ℝ) (c : EAChain (p + q) r)
    (Q : EAPoly (p + q) r) (y : Fin q → ℝ) :
    eaEval (speChainAt x c) (spePolyAt (q := q) x Q) y = eaEval c Q (Fin.append x y) := by
  have key :
      ((MvPolynomial.eval (Sum.elim y (fun j => Real.exp ((speChainAt x c).ell j y))) :
            MvPolynomial (Fin q ⊕ Fin r) ℝ →+* ℝ).comp
          (MvPolynomial.eval₂Hom MvPolynomial.C (speVarAt (q := q) (r := r) x)))
        = MvPolynomial.eval
            (Sum.elim (Fin.append x y) (fun j => Real.exp (c.ell j (Fin.append x y)))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun v => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
    · rcases v with i | j
      · refine Fin.addCases (motive := fun i =>
            (MvPolynomial.eval (Sum.elim y (fun j => Real.exp ((speChainAt x c).ell j y))) :
                MvPolynomial (Fin q ⊕ Fin r) ℝ →+* ℝ)
              ((MvPolynomial.eval₂Hom MvPolynomial.C (speVarAt (q := q) (r := r) x))
                (MvPolynomial.X (Sum.inl i)))
            = MvPolynomial.eval (Sum.elim (Fin.append x y)
                (fun j => Real.exp (c.ell j (Fin.append x y)))) (MvPolynomial.X (Sum.inl i)))
          (fun i₀ => ?_) (fun l => ?_) i
        · simp only [MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, speVarAt, Sum.elim_inl,
            Fin.addCases_left, MvPolynomial.eval_C, Fin.append_left]
        · simp only [MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, speVarAt, Sum.elim_inl,
            Fin.addCases_right, Fin.append_right]
      · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X,
          speVarAt, Sum.elim_inr, speChainAt_ell]
  exact RingHom.congr_fun key Q

/-! ## The specialized basic set and semi-Pfaffian set -/

/-- The basic condition of `X` seen at the base point `x`. -/
def speBasicAt {p q r : ℕ} (x : Fin p → ℝ) (B : Basic (p + q) r) : Basic q r :=
  ⟨B.eqs.map (spePolyAt (q := q) x), B.pos.map (spePolyAt (q := q) x)⟩

/-- The semi-Pfaffian set `X` seen at the base point `x`.  Its set is the fibre of `X.set` over
`x` (`Work.WilE7.speAt_set`). -/
def speSemiPfAt {p q : ℕ} (x : Fin p → ℝ) (X : SemiPf (p + q)) : SemiPf q :=
  ⟨X.r, speChainAt x X.c, X.basics.map (speBasicAt (q := q) x)⟩

end Work.WilE7
