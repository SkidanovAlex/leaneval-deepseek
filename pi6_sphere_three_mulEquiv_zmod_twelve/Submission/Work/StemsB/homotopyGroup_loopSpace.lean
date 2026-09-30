import Mathlib
import Submission.Work.StemsB.LoopSpaceCurrying

/-!
# `π_{k+2}(X, x) ≅ π_{k+1}(Ω X, refl)`: the loop-space shift

The `(k+2)`-dimensional homotopy group of a space `X` at `x` is the `(k+1)`-dimensional homotopy
group of its loop space `Ω X = Path x x` at the constant loop.  This is the special case of the
path–loop fibration `ΩX → PX → X` that is used in the route-B development
(`Submission/Work/StemsB/`, see `CONTRACTS.md` §A2).

The proof is the currying bijection of cubes: an `(k+2)`-cube `v` of `X` based at `x` is
reinterpreted as the `(k+1)`-cube `t ↦ (s ↦ v (Fin.cons s t))` of loops at `x`.  The underlying
homeomorphism of generalized loop spaces and its compatibility with homotopies and with the
concatenation `GenLoop.transAt` are in `Submission/Work/StemsB/LoopSpaceCurrying.lean`; here they
are assembled into the group isomorphism.
-/

namespace Work.StemsB

open scoped Topology Topology.Homotopy unitInterval

section
variable {X : Type*} [TopologicalSpace X] {x : X}

set_option backward.isDefEq.respectTransparency false in
theorem stepMulEquiv_mul (k : ℕ) (a b : HomotopyGroup (Fin (k+2)) X x) :
    stepEquivGroup (k+1) (a * b)
      = stepEquivGroup (k+1) a * stepEquivGroup (k+1) b := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  simp only [HomotopyGroup.mul_spec (i := Fin.succ (0 : Fin (k+1))) (p := p) (q := q)]
  simp only [stepEquivGroup_mk]
  simp only [HomotopyGroup.mul_spec (i := (0 : Fin (k+1)))
    (p := Faux (k+1) p) (q := Faux (k+1) q)]
  rw [Faux_transAt k p q]

/-- The currying isomorphism of homotopy groups `π_{k+2}(X, x) ≃* π_{k+1}(Ω X, refl)`. -/
noncomputable def stepMulEquiv (k : ℕ) :
    HomotopyGroup (Fin (k+2)) X x ≃* HomotopyGroup (Fin (k+1)) (Path x x) (Path.refl x) where
  toEquiv := stepEquivGroup (k+1)
  map_mul' := stepMulEquiv_mul k

end

theorem homotopyGroup_loopSpace {X : Type*} [TopologicalSpace X] (k : ℕ) (x : X) :
    Nonempty (HomotopyGroup (Fin (k + 2)) X x ≃*
      HomotopyGroup (Fin (k + 1)) (Path x x) (Path.refl x)) :=
  ⟨stepMulEquiv (X := X) (x := x) k⟩

end Work.StemsB
