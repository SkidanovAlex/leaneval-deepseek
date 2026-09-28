import Mathlib
import Submission.Work.StemsB.LoopSpaceCurrying
import Submission.Work.StemsB.homotopyGroup_loopSpace

/-!
# The loop-space shift in the shifted index shape

Mathlib/the route-B currying chapter provides the loop-space shift in the shape
`π_{k+2}(X,x) ≃* π_{k+1}(ΩX, refl)` (`Work.StemsB.stepMulEquiv`, `homotopyGroup_loopSpace`):
the index of the source is `Fin (k+2)`, i.e. the multiplicativity proof uses the *successor* group
structure.  For the loop-space form of the crux (`Submission/Work/StemsB/SphLoopCrux.lean`) one
needs the same statement with the source index written as `m + 1` and the target index as `m`,
which is *not* an instance of the former (the `Nat` expressions `k + 2` and `m + 1` cannot be
unified, and the two sides are only propositionally, not definitionally, equal).

This file re-proves the two ingredients (`Faux_transAt` and the multiplicativity of the currying
bijection) with `m` in place of `k + 1`, giving

* `Work.StemsB.Faux_transAt'`,
* `Work.StemsB.stepEquivGroup_mul'`,
* `Work.StemsB.stepMulEquivShifted` and **`Work.StemsB.homotopyGroup_succ_mulEquiv_loop'`**:
  `π_{m+1}(X,x) ≃* π_m(ΩX, refl)` for `[Nonempty (Fin m)]`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.StemsB

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- `Faux_transAt` with `Fin (m+1)` in place of `Fin (k+2)`. -/
theorem Faux_transAt' (m : ℕ) (hm : 1 ≤ m) (p q : GenLoop (Fin (m+1)) X x) :
    Faux m (GenLoop.transAt (Fin.succ (⟨0, hm⟩ : Fin m)) q p) =
      GenLoop.transAt (⟨0, hm⟩ : Fin m) (Faux m q) (Faux m p) := by
  apply GenLoop.ext
  intro t
  apply Path.ext
  funext s
  rw [Faux_apply]
  simp only [GenLoop.transAt, GenLoop.coe_copy, path_ite_apply, Faux_apply, Fin.cons_succ]
  simp only [← Fin.cons_update]

/-- The currying bijection `stepEquivGroup m` is multiplicative, with the source indexed by
`Fin (m+1)` and the target by `Fin m`. -/
theorem stepEquivGroup_mul' (m : ℕ) (hm : 1 ≤ m) [Nonempty (Fin m)]
    (a b : HomotopyGroup (Fin (m+1)) X x) :
    stepEquivGroup m (a * b) = stepEquivGroup m a * stepEquivGroup m b := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  simp only [HomotopyGroup.mul_spec (i := Fin.succ (⟨0, hm⟩ : Fin m)) (p := p) (q := q)]
  simp only [stepEquivGroup_mk]
  simp only [HomotopyGroup.mul_spec (i := (⟨0, hm⟩ : Fin m)) (p := Faux m p) (q := Faux m q)]
  rw [Faux_transAt' m hm p q]

/-- The loop-space shift as a multiplicative equivalence, with the source indexed by `Fin (m+1)`
and the target by `Fin m`. -/
noncomputable def stepMulEquivShifted (m : ℕ) (hm : 1 ≤ m) [Nonempty (Fin m)]
    [Nonempty (Fin (m+1))] :
    HomotopyGroup (Fin (m+1)) X x ≃* HomotopyGroup (Fin m) (Path x x) (Path.refl x) where
  toEquiv := stepEquivGroup m
  map_mul' := stepEquivGroup_mul' m hm

/-- **The loop-space shift `π_{m+1}(X,x) ≃* π_m(ΩX, refl)`** in the shifted index shape. -/
theorem homotopyGroup_succ_mulEquiv_loop' (X : Type*) [TopologicalSpace X] (x : X) (m : ℕ)
    (hm : 1 ≤ m) [Nonempty (Fin m)] [Nonempty (Fin (m+1))] :
    Nonempty (HomotopyGroup (Fin (m + 1)) X x ≃*
      HomotopyGroup (Fin m) (Path x x) (Path.refl x)) :=
  ⟨stepMulEquivShifted (X := X) (x := x) m hm⟩

end Work.StemsB
