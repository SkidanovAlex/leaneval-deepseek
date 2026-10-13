/-
  WilE5 / Strat — the state invariant of the fibrewise stratification recursion.

  `Work.WilE5.Strat.Inv X σ` bundles the four bookkeeping invariants of a state `σ` of the
  recursion `Work.WilE5.level`:
  * some disjunct `A ∈ X.basics` has all its conditions among the state's conditions and all its
    equations among the flatness sources;
  * `σ.Φ = σ.Ξ` as sets (flatness sources = accumulated vanishing conditions);
  * the cube bookkeeping of the face pattern;
  * the full pivot minor of `σ` is nonzero on the state's set.

  It is stated with exactly the bracketing of the goal of
  `Work.WilE5.Strat.state_invariants`, so that the two are definitionally equal.
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Basic
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-- The invariant of a state of the recursion: disjunct bookkeeping, `Φ = Ξ`, the cube
bookkeeping of the face pattern, and non-vanishing of the full pivot minor. -/
def Inv {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (σ : Work.WilE5.St p q X.r) : Prop :=
  (∃ A ∈ X.basics,
      (∀ f ∈ A.eqs, f ∈ (Work.WilE5.stCond σ).eqs) ∧
      (∀ g ∈ A.pos, g ∈ (Work.WilE5.stCond σ).pos) ∧
      (∀ f ∈ A.eqs, f ∈ σ.Φ)) ∧
    (∀ ψ ∈ σ.Φ, ψ ∈ σ.Ξ) ∧
    (∀ ψ ∈ σ.Ξ, ψ ∈ σ.Φ) ∧
    (∀ l : Fin q,
        Work.WilE5.intPoly (p := p) (r := X.r) l ∈ σ.ν ∨
          ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
            Work.WilE5.facePoly (p := p) (r := X.r) l c ∈ σ.B.map Prod.fst) ∧
    (∀ z ∈ (Work.WilE5.stSemiPf X σ).set,
      (Matrix.of fun (a : Fin σ.B.length) (b : Fin σ.B.length) =>
        WilkiesDesign.E.eaEval X.c (WilkiesDesign.E.eaD X.c (Work.WilE5.pivFun σ.B b)
          (Work.WilE5.hFun σ.B a)) z).det ≠ 0)

end Work.WilE5.Strat
