import Mathlib
import Submission.Work.WilC0.Basic
import Submission.Work.Wilkies.CG.Spec

namespace Work.WilC0

set_option autoImplicit false
open FirstOrder FirstOrder.Language
open scoped FirstOrder
open WilkiesDesign (rexp)
open WilkiesDesign.CG

-- We may reduce `def`-unfoldings (`Language.ring`, `Language.sum`, `Language.withConstants`, …)
-- freely while rewriting the concrete function symbols of `LRc`; without this the `rw`/`simp`
-- unifiers refuse to see that `ring.Functions n` and `ringFunc n` are the same type.
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## `RExpExistI` from polynomial equations

Each of the following states that a set of tuples defined by a single polynomial equation in the
ambient coordinates is existentially definable in `ℝ_rexp` (with no existential witnesses). They are
immediate from `RExpExistI.rexPoly`. -/

variable {ι : Type} {κ : Type}

theorem rexExistI_eq_const (o : κ) (c : ℝ) : RExpExistI {z : κ → ℝ | z o = c} :=
  RExpExistI.of_eq (by
    ext z
    simp only [Set.mem_ofPred_eq, mem_RExPoly, rexpEval_sub, rexpEval_X_inl, rexpEval_C, sub_eq_zero])
    (RExpExistI.rexPoly (MvPolynomial.X (Sum.inl o) - MvPolynomial.C c))

theorem rexExistI_eq_var (o a : κ) : RExpExistI {z : κ → ℝ | z o = z a} :=
  RExpExistI.of_eq (by
    ext z
    simp only [Set.mem_ofPred_eq, mem_RExPoly, rexpEval_sub, rexpEval_X_inl, sub_eq_zero])
    (RExpExistI.rexPoly (MvPolynomial.X (Sum.inl o) - MvPolynomial.X (Sum.inl a)))

theorem rexExistI_eq_zero (o : κ) : RExpExistI {z : κ → ℝ | z o = 0} :=
  rexExistI_eq_const o 0

theorem rexExistI_eq_one (o : κ) : RExpExistI {z : κ → ℝ | z o = 1} :=
  rexExistI_eq_const o 1

theorem rexExistI_eq_add (o a b : κ) : RExpExistI {z : κ → ℝ | z o = z a + z b} :=
  RExpExistI.of_eq (by
    ext z
    simp only [Set.mem_ofPred_eq, mem_RExPoly, rexpEval_sub, rexpEval_X_inl, sub_eq_zero]
    constructor <;> intro h <;> linarith)
    (RExpExistI.rexPoly
      (MvPolynomial.X (Sum.inl o) - MvPolynomial.X (Sum.inl a) - MvPolynomial.X (Sum.inl b)))

theorem rexExistI_eq_mul (o a b : κ) : RExpExistI {z : κ → ℝ | z o = z a * z b} :=
  RExpExistI.of_eq (by
    ext z
    simp only [Set.mem_ofPred_eq, mem_RExPoly, rexpEval_sub, rexpEval_mul, rexpEval_X_inl, sub_eq_zero])
    (RExpExistI.rexPoly
      (MvPolynomial.X (Sum.inl o) - MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inl b)))

theorem rexExistI_eq_neg (o a : κ) : RExpExistI {z : κ → ℝ | z o = - z a} :=
  RExpExistI.of_eq (by
    ext z
    simp only [Set.mem_ofPred_eq, mem_RExPoly, rexpEval_add, rexpEval_X_inl, add_eq_zero_iff_eq_neg])
    (RExpExistI.rexPoly (MvPolynomial.X (Sum.inl o) + MvPolynomial.X (Sum.inl a)))

theorem rexExistI_eq_rexp (o a : κ) : RExpExistI {z : κ → ℝ | z o = rexp (z a)} :=
  RExpExistI.of_eq (by
    ext z
    simp only [Set.mem_ofPred_eq, mem_RExPoly, rexpEval_sub, rexpEval_X_inl, rexpEval_X_inr, sub_eq_zero])
    (RExpExistI.rexPoly (MvPolynomial.X (Sum.inl o) - MvPolynomial.X (Sum.inr a)))

/-! ## The graph of a term

We prove the stronger statement `TermGraph t`: for *any* index type `κ` of ambient variables, any
map `g : ι → κ` identifying the free variables of `t` and any output coordinate `o : κ`, the graph
`{z : κ → ℝ | z o = t.realize (z ∘ g)}` is existentially definable in `ℝ_rexp`. -/

/-- `TermGraph t` is the graph of the term `t`, with the free variables of `t` embedded into an
arbitrary ambient index type `κ` at an arbitrary output coordinate `o`. -/
def TermGraph (t : LRc.Term ι) : Prop :=
  ∀ {κ : Type} (g : ι → κ) (o : κ), RExpExistI {z : κ → ℝ | z o = t.realize (z ∘ g)}

/-- Every `LRc`-term has existentially definable graph.  The proof is the syntax induction: at a
function symbol we introduce one fresh witness block (`Fin 1` or `Fin 2`) holding the values of the
subterms, intersect the (existentially definable) graphs of the subterms with the polynomial
equation relating them to the output, and project the witnesses away again. -/
theorem termGraph (t : LRc.Term ι) : TermGraph t := by
  apply Term.rec (motive := TermGraph)
  · intro i κ g o
    exact (rexExistI_eq_var o (g i)).of_eq (by
      ext z; simp only [Set.mem_ofPred_eq, Function.comp_apply, Term.realize_var])
  · intro n f ts ih κ g o
    match n, f with
    | 0, Sum.inr c =>
      have hc : ∀ z : κ → ℝ, Term.realize (z ∘ g) (Term.func (Sum.inr c) ts) = c :=
        fun _ => rfl
      exact (rexExistI_eq_const o c).of_eq (by
        ext z; simp only [Set.mem_ofPred_eq]; rw [hc z])
    | _ + 1, Sum.inr c => nomatch c
    | _, Sum.inl (Sum.inl .zero) =>
      have hz : ∀ z : κ → ℝ,
          Term.realize (z ∘ g) (Term.func (Sum.inl (Sum.inl Ring.zeroFunc)) ts) = 0 :=
        fun _ => rfl
      exact (rexExistI_eq_zero o).of_eq (by
        ext z; simp only [Set.mem_ofPred_eq]; rw [hz z])
    | _, Sum.inl (Sum.inl .one) =>
      have hz : ∀ z : κ → ℝ,
          Term.realize (z ∘ g) (Term.func (Sum.inl (Sum.inl Ring.oneFunc)) ts) = 1 :=
        fun _ => rfl
      exact (rexExistI_eq_one o).of_eq (by
        ext z; simp only [Set.mem_ofPred_eq]; rw [hz z])
    | _, Sum.inl (Sum.inl .neg) =>
      have hz : ∀ z : κ → ℝ,
          Term.realize (z ∘ g) (Term.func (Sum.inl (Sum.inl Ring.negFunc)) ts)
            = - (ts 0).realize (z ∘ g) := fun _ => rfl
      have hA := ih 0 (fun i => Sum.inl (g i)) (Sum.inr (0 : Fin 1))
      have hC := rexExistI_eq_neg (κ := κ ⊕ Fin 1) (Sum.inl o) (Sum.inr (0 : Fin 1))
      refine ((hA.inter hC).existsBlock (μ := Fin 1)).of_eq ?_
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨u, huA, huC⟩
        have huA' : u 0 = (ts 0).realize (z ∘ g) := huA
        have huC' : z o = - u 0 := huC
        rw [hz z, ← huA']
        exact huC'
      · intro hzo
        rw [hz z] at hzo
        refine ⟨![(ts 0).realize (z ∘ g)], ?_, ?_⟩
        · exact rfl
        · simpa using hzo
    | _, Sum.inl (Sum.inl .add) =>
      have hz : ∀ z : κ → ℝ,
          Term.realize (z ∘ g) (Term.func (Sum.inl (Sum.inl Ring.addFunc)) ts)
            = (ts 0).realize (z ∘ g) + (ts 1).realize (z ∘ g) := fun _ => rfl
      have hA := ih 0 (fun i => Sum.inl (g i)) (Sum.inr (0 : Fin 2))
      have hB := ih 1 (fun i => Sum.inl (g i)) (Sum.inr (1 : Fin 2))
      have hC := rexExistI_eq_add (κ := κ ⊕ Fin 2) (Sum.inl o) (Sum.inr (0 : Fin 2))
        (Sum.inr (1 : Fin 2))
      refine ((hA.inter (hB.inter hC)).existsBlock (μ := Fin 2)).of_eq ?_
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨u, huA, huB, huC⟩
        have huA' : u 0 = (ts 0).realize (z ∘ g) := huA
        have huB' : u 1 = (ts 1).realize (z ∘ g) := huB
        have huC' : z o = u 0 + u 1 := huC
        rw [hz z, ← huA', ← huB']
        exact huC'
      · intro hzo
        rw [hz z] at hzo
        refine ⟨![(ts 0).realize (z ∘ g), (ts 1).realize (z ∘ g)], ?_, ?_, ?_⟩
        · exact rfl
        · exact rfl
        · simpa using hzo
    | _, Sum.inl (Sum.inl .mul) =>
      have hz : ∀ z : κ → ℝ,
          Term.realize (z ∘ g) (Term.func (Sum.inl (Sum.inl Ring.mulFunc)) ts)
            = (ts 0).realize (z ∘ g) * (ts 1).realize (z ∘ g) := fun _ => rfl
      have hA := ih 0 (fun i => Sum.inl (g i)) (Sum.inr (0 : Fin 2))
      have hB := ih 1 (fun i => Sum.inl (g i)) (Sum.inr (1 : Fin 2))
      have hC := rexExistI_eq_mul (κ := κ ⊕ Fin 2) (Sum.inl o) (Sum.inr (0 : Fin 2))
        (Sum.inr (1 : Fin 2))
      refine ((hA.inter (hB.inter hC)).existsBlock (μ := Fin 2)).of_eq ?_
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨u, huA, huB, huC⟩
        have huA' : u 0 = (ts 0).realize (z ∘ g) := huA
        have huB' : u 1 = (ts 1).realize (z ∘ g) := huB
        have huC' : z o = u 0 * u 1 := huC
        rw [hz z, ← huA', ← huB']
        exact huC'
      · intro hzo
        rw [hz z] at hzo
        refine ⟨![(ts 0).realize (z ∘ g), (ts 1).realize (z ∘ g)], ?_, ?_, ?_⟩
        · exact rfl
        · exact rfl
        · simpa using hzo
    | _, Sum.inl (Sum.inr .rexp) =>
      have hz : ∀ z : κ → ℝ,
          Term.realize (z ∘ g) (Term.func (Sum.inl (Sum.inr rexpFunc.rexp)) ts)
            = rexp ((ts 0).realize (z ∘ g)) := fun _ => rfl
      have hA := ih 0 (fun i => Sum.inl (g i)) (Sum.inr (0 : Fin 1))
      have hC := rexExistI_eq_rexp (κ := κ ⊕ Fin 1) (Sum.inl o) (Sum.inr (0 : Fin 1))
      refine ((hA.inter hC).existsBlock (μ := Fin 1)).of_eq ?_
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨u, huA, huC⟩
        have huA' : u 0 = (ts 0).realize (z ∘ g) := huA
        have huC' : z o = rexp (u 0) := huC
        rw [hz z, ← huA']
        exact huC'
      · intro hzo
        rw [hz z] at hzo
        refine ⟨![(ts 0).realize (z ∘ g)], ?_, ?_⟩
        · exact rfl
        · simpa using hzo

/-- For every first-order term `t` of the language `LRc` (ordered rings + the restricted
exponential + a constant for every real), the graph of `z ↦ t.realize z` is existentially
definable in `ℝ_rexp` (`Work.WilC0.RExpExistI`, defined in `Submission.Work.WilC0.Basic`):
if `z : ι ⊕ Fin 1 → ℝ` has `z (Sum.inr 0) = t.realize (z ∘ Sum.inl)` then the tuple `z` lies in
a projection of a zero set of one rexp-polynomial.

Terms are built from the ring operations `+,-,*,0,1` (polynomial equations), the constant symbols
of `LRc` (again polynomial equations in the coordinates) and the unary symbol `rexp`. Note for
`rexp` that the polynomial may use the second copy `Sum.inr i` of a variable, which evaluates to
`rexp (z i)`; so `z (inr 0) = rexp (z (inl a))` is the polynomial equation
`X (inl (inr 0)) - X (inr (inl a)) = 0`. -/
theorem termGraph_rex {ι : Type} (t : WilkiesDesign.CG.LRc.Term ι) :
    Work.WilC0.RExpExistI
      {z : (ι ⊕ Fin 1) → ℝ | z (Sum.inr (0 : Fin 1)) = t.realize (z ∘ Sum.inl)} :=
  termGraph t (Sum.inl) (Sum.inr 0)

end

end Work.WilC0
