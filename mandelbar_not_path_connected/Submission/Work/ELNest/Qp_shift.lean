/-
# `Qp_shift`: the level-`(n+1)` pair of the `z₁`-nest is mapped to the level-`n` pair

The nest `Qp n` of the equator-leak argument at the parabolic point `z₁` is a sequence of
co-landing pairs of rays whose angles are `bAng' n` and `bAng n + 1`; the level-`(n+1)` pair is
the pull-back of the level-`n` pair under the holomorphic degree-`1024` map
`F c = (T_c)^{10} = (Tantibar c)^[10]`, and this holds already at the landing points:

    F c ((Qp (n+1)).y) = (Qp n).y.

The proof has three ingredients, all of which are already in the workspace.

* **Landing is equivariant under `T_c`** (`Work.ELTop.landsN_map`): if the ray of angle `θ`
  lands at `y`, then the ray of angle `T θ = -2θ mod 1` lands at `T_c y`.  Iterating ten times
  (`landsN_iterate`, the ray-point identity `rayPt_iterate` of `Work.ELRig` read on the
  landing relation) gives: the ray of angle `T^[10] θ` lands at `(Tantibar c)^[10] y = F c y`.
* **The angle arithmetic** (`T_iterate_bAng`, pure integer arithmetic on the nest angles):
  `T^[10] (bAng' (n+1)) = bAng' n`.
* **Uniqueness of the landing point** (`landsN_unique`): a ray lands at at most one point, so
  the point `F c ((Qp (n+1)).y)` is the landing point of the ray of angle `bAng' n`, which is
  `(Qp n).y` by definition of the pair `Qp n` (`Qpa`).

Note that only the *first* angle of the pair is used: the co-landing field `lands_a` of
`Qp n` together with `Qpa` pins `(Qp n).y` down.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.T_iterate_bAng
import Submission.Work.ELTop.landsN_map

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Two elementary facts about landing -/

/-- **A ray lands at at most one point.**  `LandsN hN θ y` is a `Tendsto` statement, so two
landing points of the same ray are limits of the same filter, which is `NeBot` because
`(1, ∞)` accumulates at `1` from above. -/
theorem landsN_unique {hN : DynB c φ} {θ : ℝ} {y y' : ℂ}
    (h : LandsN hN θ y) (h' : LandsN hN θ y') : y = y' := by
  have hne : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique h h'

/-- **Landing is equivariant under the iterates of `T_c`.**  If the ray of angle `θ` lands at
`y`, then the ray of angle `T^[k] θ` lands at `(Tantibar c)^[k] y`; the one-step case is
`Work.ELTop.landsN_map`. -/
theorem landsN_iterate (hN : DynB c φ) (hB : Work.ParamRays.IsDynBottcher c φ) (k : ℕ)
    {θ : ℝ} {y : ℂ} (h : LandsN hN θ y) :
    LandsN hN (T^[k] θ) ((Tantibar c)^[k] y) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Work.ELTop.landsN_map hN hB ih

/-- The tenth iterate of the equivariance, in the form used by the nests: the ray of angle
`T^[10] θ` lands at the image of the landing point under `F c = (Tantibar c)^[10]`. -/
theorem landsN_iterate_F (hN : DynB c φ) (hB : Work.ParamRays.IsDynBottcher c φ)
    {θ : ℝ} {y : ℂ} (h : LandsN hN θ y) :
    LandsN hN (T^[10] θ) (F c y) := by
  have h10 := landsN_iterate hN hB 10 h
  rwa [F_eq_tantibar]

/-! ## The shift of the nest -/

theorem Qp_shift {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) :
    Work.ELNest.F c ((S.Qp (n + 1)).y) = (S.Qp n).y := by
  -- the ray of the first angle of the level-`(n+1)` pair, pushed forward by `F`
  have hlan := landsN_iterate_F S.d.hN S.d.bottcher (S.Qpa (n + 1) ▸ (S.Qp (n + 1)).lands_a)
  -- its angle is `T^[10] (bAng' (n+1)) = bAng' n`
  rw [(T_iterate_bAng n).2] at hlan
  -- the defining property of `(Qp n).y`: it is the landing point of the same ray
  have h2 : LandsN S.d.hN (bAng' n) (S.Qp n).y := S.Qpa n ▸ (S.Qp n).lands_a
  exact (landsN_unique h2 hlan).symm

end Work.ELNest
