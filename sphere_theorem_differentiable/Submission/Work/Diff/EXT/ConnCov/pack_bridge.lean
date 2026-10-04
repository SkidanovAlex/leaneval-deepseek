import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ConnCov.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bridge between the curried (`Op3`) tower and the packed (`Fam`) tower

`Work.Diff.EXT.ConnCov.pack_bridge` identifies the *curried* recursion of
`Work.Diff.EXT.ATower` (`ATower.step`, `Work.Diff.EXT.ConnCov.insAll`) with the *packed*
recursion of `Work.Diff.EXT.ConnCov.AMB` (`AMB.pD`, `AMB.Ins`) under the packing
`AMB.pack`:

* `pack (step cov τ) = pD cov (pack τ)`  — one recursion step commutes with packing;
* `pack (insAll δ τ) = Ins δ (pack τ)`   — the total insertion of the connection difference
  commutes with packing.

The content is index bookkeeping.  A packed tuple `F : Fin (k+3) → TF` is split by
`Fin.sum_univ_add` into the `Fin k` part (the derivative slots, re-indexed by `Fin.castAdd 3`)
and the `Fin 3` part (the three value slots, re-indexed by `Fin.natAdd k`).  The two lemmas
`pack_update_castAdd` and `pack_update_natAdd` describe how `Function.update` behaves under
`AMB.pack`, using `Function.update_comp_eq_of_injective'` (resp.
`Function.update_comp_eq_of_forall_ne'` + `Function.update_apply_of_injective`) together with the
disjointness of the two index maps `Fin.castAdd 3` and `Fin.natAdd k`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

namespace AMB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- `Fin.castAdd 3` and `Fin.natAdd k` never collide: the first lands strictly below `k`, the
second at or above `k`. -/
lemma castAdd_ne_natAdd {k : ℕ} (i : Fin k) (j : Fin 3) :
    Fin.castAdd 3 i ≠ Fin.natAdd k j := by
  intro h
  have h1 : (Fin.castAdd 3 i : ℕ) = (Fin.natAdd k j : ℕ) := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := i.isLt
  omega

/-- **Unpacking `AMB.pack` after an update in a derivative slot.**  The update of the packed
`(k+3)`-tuple in the slot `Fin.castAdd 3 i` is the update of the `k`-tuple of derivative slots in
the slot `i`; the three value slots are untouched. -/
lemma pack_update_castAdd {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I:=I) (M:=M) k)
    (u : Fin (k+3) → TF (I:=I) (M:=M)) (i : Fin k) (W : TF (I:=I) (M:=M)) :
    pack τ (Function.update u (Fin.castAdd 3 i) W)
      = τ (Function.update (fun i' : Fin k => u (Fin.castAdd 3 i')) i W)
          (u (Fin.natAdd k 0)) (u (Fin.natAdd k 1)) (u (Fin.natAdd k 2)) := by
  funext x
  simp only [pack]
  rw [Function.update_comp_eq_of_injective' u (Fin.castAdd_injective k 3) i W,
    Function.update_of_ne (castAdd_ne_natAdd i 0).symm W u,
    Function.update_of_ne (castAdd_ne_natAdd i 1).symm W u,
    Function.update_of_ne (castAdd_ne_natAdd i 2).symm W u]

/-- **Unpacking `AMB.pack` after an update in a value slot.**  The update of the packed
`(k+3)`-tuple in the slot `Fin.natAdd k j` (`j : Fin 3`) is the corresponding update of the
`3`-tuple of value slots; the `k` derivative slots are untouched. -/
lemma pack_update_natAdd {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I:=I) (M:=M) k)
    (u : Fin (k+3) → TF (I:=I) (M:=M)) (j : Fin 3) (W : TF (I:=I) (M:=M)) :
    pack τ (Function.update u (Fin.natAdd k j) W)
      = τ (fun i' : Fin k => u (Fin.castAdd 3 i'))
          (Function.update (fun j' : Fin 3 => u (Fin.natAdd k j')) j W 0)
          (Function.update (fun j' : Fin 3 => u (Fin.natAdd k j')) j W 1)
          (Function.update (fun j' : Fin 3 => u (Fin.natAdd k j')) j W 2) := by
  funext x
  simp only [pack]
  rw [Function.update_comp_eq_of_forall_ne' u W (fun i => castAdd_ne_natAdd i j),
    Function.update_apply_of_injective u (Fin.natAdd_injective 3 k) j W 0,
    Function.update_apply_of_injective u (Fin.natAdd_injective 3 k) j W 1,
    Function.update_apply_of_injective u (Fin.natAdd_injective 3 k) j W 2]

/-- The successor of the `i`-th derivative index, read in the packed `(k+1+3)`-tuple. -/
lemma succ_castAdd_three {k : ℕ} (i : Fin k) :
    (Fin.castAdd 3 i).succ = (Fin.castAdd 3 i.succ : Fin (k+1+3)) := rfl

/-- The successor of the `j`-th value index, read in the packed `(k+1+3)`-tuple. -/
lemma succ_natAdd_three {k : ℕ} (j : Fin 3) :
    (Fin.natAdd k j).succ = (Fin.natAdd (k+1) j : Fin (k+1+3)) := by
  ext
  simp only [Fin.val_succ, Fin.val_natAdd]
  omega

/-- The `0`-th derivative slot of the packed `(k+1+3)`-tuple is the direction slot `0`. -/
lemma castAdd_three_zero {k : ℕ} :
    (Fin.castAdd 3 (0 : Fin (k+1)) : Fin (k+3+1)) = 0 := rfl

/-- **Packing the `succ`-shifted tuple.**  `AMB.pack` applied to the tail tuple
`fun j : Fin (k+3) => F j.succ` is the curried operator evaluated at the derivative slots
`F (castAdd 3 i.succ)`, the direction slot `F 0` being dropped, and the three value slots
`F (natAdd (k+1) j)`. -/
lemma pack_succ {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I:=I) (M:=M) k)
    (F : Fin (k+3+1) → TF (I:=I) (M:=M)) :
    pack τ (fun j : Fin (k+3) => F j.succ)
      = fun y => τ (fun i : Fin k => F (Fin.castAdd 3 i.succ))
          (F (Fin.natAdd (k+1) (0:Fin 3))) (F (Fin.natAdd (k+1) (1:Fin 3)))
          (F (Fin.natAdd (k+1) (2:Fin 3))) y := by
  funext y
  simp only [pack]
  rfl

/-- **One recursion step, packed**: `AMB.pack` intertwines the curried step
`Work.Diff.EXT.ATower.step` with the packed derivative `AMB.pD`. -/
lemma pack_step_apply {k : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (τ : Work.Diff.EXT.ATower.Op3 (I:=I) (M:=M) k)
    (F : Fin (k+3+1) → TF (I:=I) (M:=M)) (x : M) :
    pack (Work.Diff.EXT.ATower.step cov τ) F x = pD cov (pack τ) F x := by
  rw [pack_apply]
  simp only [Work.Diff.EXT.ATower.step, pD]
  rw [pack_succ]
  conv_rhs => rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_three]
  simp only [pack_update_castAdd, pack_update_natAdd]
  simp only [succ_castAdd_three, succ_natAdd_three, castAdd_three_zero, Function.update_self]
  rw [Function.update_of_ne (show (1:Fin 3) ≠ 0 by decide),
    Function.update_of_ne (show (2:Fin 3) ≠ 0 by decide),
    Function.update_of_ne (show (0:Fin 3) ≠ 1 by decide),
    Function.update_of_ne (show (2:Fin 3) ≠ 1 by decide),
    Function.update_of_ne (show (0:Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (1:Fin 3) ≠ 2 by decide)]
  ring

/-- **The total insertion, packed**: `AMB.pack` intertwines the curried insertion operator
`Work.Diff.EXT.ConnCov.insAll` with the packed insertion `AMB.Ins`. -/
lemma pack_insAll_apply {k : ℕ}
    (δ : TF (I:=I) (M:=M) → TF (I:=I) (M:=M) → TF (I:=I) (M:=M))
    (τ : Work.Diff.EXT.ATower.Op3 (I:=I) (M:=M) k)
    (F : Fin (k+3+1) → TF (I:=I) (M:=M)) (x : M) :
    pack (Work.Diff.EXT.ConnCov.insAll δ τ) F x = Ins δ (pack τ) F x := by
  rw [Ins]
  conv_lhs => rw [pack_apply]
  simp only [Work.Diff.EXT.ConnCov.insAll, Pi.add_apply, Finset.sum_apply]
  simp only [Work.Diff.EXT.ATower.insD, Work.Diff.EXT.ATower.insA, Work.Diff.EXT.ATower.insB,
    Work.Diff.EXT.ATower.insC]
  conv_rhs => rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_three]
  simp only [pack_update_castAdd, pack_update_natAdd]
  conv_rhs => rw [← add_assoc, ← add_assoc]
  rfl

end AMB

theorem pack_bridge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k)
    (δ : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    (Work.Diff.EXT.ConnCov.AMB.pack (Work.Diff.EXT.ATower.step cov τ)
        = Work.Diff.EXT.ConnCov.AMB.pD cov (Work.Diff.EXT.ConnCov.AMB.pack τ))
      ∧ (Work.Diff.EXT.ConnCov.AMB.pack (Work.Diff.EXT.ConnCov.insAll δ τ)
        = Work.Diff.EXT.ConnCov.AMB.Ins δ (Work.Diff.EXT.ConnCov.AMB.pack τ)) := by
  constructor
  · funext F y
    exact AMB.pack_step_apply cov τ F y
  · funext F y
    exact AMB.pack_insAll_apply δ τ F y

end Work.Diff.EXT.ConnCov
