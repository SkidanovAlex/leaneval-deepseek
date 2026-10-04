import Mathlib
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.EXT.ATens.Kit
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The recursion of `pkTower` (the unpacked twin of the packed tower `packTower`)

`Work.Diff.EXT.ConnCov.RicFlip.pkTower g base k F` is `tower (lcOf g) base k` evaluated on the `k`
direction slots and the three value slots read off from the packed tuple `F : Fin (k+3) → TF`
(direction slots `F (Fin.castAdd 3 ·)`, value slots `F (Fin.natAdd k 0/1/2)`).

This module proves that it satisfies the recursion of the packed tower:

`pkTower g base (k+1) F = packStep g (pkTower g base k) F`,

which is the bridge `packTower = pkTower` used in `towerSlotAddSmValDep.lean`.

The proof is the direct analogue of the PROVED `Work.Diff.EXT.cktA_mkT3_eq` of
`Submission/Work/Diff/EXT/ATens/Defs.lean` (the specialisation to `base = aOf G t` and the
connection `lcOf (G 0)`): after `funext y` and the unfolding of the packed recursion and of
`tower`'s recursion step, the sum over `Fin (k+3)` is split with `Fin.sum_univ_add` into the sum
over `Fin k` (`Fin.castAdd 3 ·`) and the three value slots (`Fin.sum_univ_three`), and the
(un)packing identities `mkT3_comp_succ`, `mkT3_castAdd`, `mkT3_natAdd`, `update_castAdd_mkT3`,
`update_natAdd_mkT3`, `pkTower_mkT3` (and the `Fin` identities `succ_castAdd_three`,
`succ_natAdd_three`) match the two sides term by term; `ring` closes the arithmetic.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- `dirFA` written as the raw field `y ↦ lcOf g X y (v0 y)`. -/
theorem dirFA_apply {g : Submission.Diff.SMet I M} (X v0 : Π y : M, TangentSpace I y) :
    Work.Diff.EXT.dirFA g X v0 = fun y : M => (Submission.Diff.lcOf g X y) (v0 y) := by
  funext y; rfl

/-- The value of a packed tuple at its slot `0` (the differentiation direction). -/
theorem mkT3_zero_apply {k : ℕ} (v : Fin (k + 1) → (Π y : M, TangentSpace I y))
    (B : Fin 3 → (Π y : M, TangentSpace I y)) :
    Work.Diff.EXT.mkT3 v B (0 : Fin (k + 1 + 3)) = v 0 := by
  rw [show (0 : Fin (k + 1 + 3)) = Fin.castAdd 3 (0 : Fin (k + 1)) from rfl,
    Work.Diff.EXT.mkT3_castAdd]

/-- Updating the first value slot of `trip3 A B C`. -/
theorem update_trip3_zero' (A A' B C : Π y : M, TangentSpace I y) :
    Function.update (Work.Diff.EXT.trip3 A B C) (0 : Fin 3) A'
      = Work.Diff.EXT.trip3 A' B C := by
  funext p; fin_cases p <;> simp [Function.update, Work.Diff.EXT.trip3]

/-- Updating the second value slot of `trip3 A B C`. -/
theorem update_trip3_one' (A B B' C : Π y : M, TangentSpace I y) :
    Function.update (Work.Diff.EXT.trip3 A B C) (1 : Fin 3) B'
      = Work.Diff.EXT.trip3 A B' C := by
  funext p; fin_cases p <;> simp [Function.update, Work.Diff.EXT.trip3]

/-- Updating the third value slot of `trip3 A B C`. -/
theorem update_trip3_two' (A B C C' : Π y : M, TangentSpace I y) :
    Function.update (Work.Diff.EXT.trip3 A B C) (2 : Fin 3) C'
      = Work.Diff.EXT.trip3 A B C' := by
  funext p; fin_cases p <;> simp [Function.update, Work.Diff.EXT.trip3]

/-- **The recursion of `pkTower`, on the unpacked tuple `mkT3 v (trip3 A B C)`.** -/
theorem pkTower_succ_mkT3 (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (v : Fin (k + 1) → (Π y : M, TangentSpace I y))
    (A B C : Π y : M, TangentSpace I y) :
    pkTower g base (k + 1) (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
      = packStep g (pkTower g base k) (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) := by
  funext y
  simp only [packStep, Work.Diff.EXT.ATower.tower, Work.Diff.EXT.ATower.step,
    Work.Diff.EXT.mkT3_castAdd, Work.Diff.EXT.mkT3_natAdd,
    Work.Diff.EXT.trip3_zero, Work.Diff.EXT.trip3_one, Work.Diff.EXT.trip3_two,
    Work.Diff.EXT.mkT3_comp_succ, mkT3_zero_apply, dirFA_apply,
    Work.Diff.EXT.succ_castAdd_three, Work.Diff.EXT.succ_natAdd_three,
    Fin.sum_univ_add, Fin.sum_univ_three,
    Work.Diff.EXT.update_castAdd_mkT3, Work.Diff.EXT.update_natAdd_mkT3,
    pkTower_mkT3,
    update_trip3_zero', update_trip3_one', update_trip3_two',
    Function.update_self, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  ring

/-- **The recursion of `pkTower`** (`packStep`-form), for an arbitrary packed tuple. -/
theorem pkTower_succ_rec_alt (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (F : Fin (k + 4) → (Π y : M, TangentSpace I y)) :
    pkTower g base (k + 1) F = packStep g (pkTower g base k) F := by
  have hF : F = Work.Diff.EXT.mkT3 (fun j : Fin (k + 1) => F (Fin.castAdd 3 j))
      (Work.Diff.EXT.trip3 (F (Fin.natAdd (k + 1) (0 : Fin 3)))
        (F (Fin.natAdd (k + 1) (1 : Fin 3))) (F (Fin.natAdd (k + 1) (2 : Fin 3)))) := by
    funext s
    refine Fin.addCases (m := k + 1) (n := 3) ?_ ?_ s
    · intro j
      simp only [Work.Diff.EXT.mkT3_castAdd]
    · intro p
      rw [Work.Diff.EXT.mkT3_natAdd]
      fin_cases p <;> rfl
  rw [hF]
  exact pkTower_succ_mkT3 g base k _ _ _ _

end Work.Diff.EXT.ConnCov.RicFlip
