import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELAssembly.curveF_of_alphaPair
import Submission.Work.ELPull.nearArcsCover_Q

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- **`T^[10]` is `1`-periodic.**  A single step of the angle-doubling map absorbs the
integer `-2` produced by the shift `θ ↦ θ + 1` (`Int.fract_add_intCast`); ten steps
absorb `1024`.  The `+ 1` of the boundary angle `βₙ + 1` is therefore inert.

(One step is genuinely needed: `T^[0] (θ + 1) ≠ T^[0] θ`.  This is why the lemma is stated
for the iterate `10` and not for a general `k`.) -/
theorem T_ten_add_one (θ : ℝ) : (Work.EL.T^[10]) (θ + 1) = (Work.EL.T^[10]) θ := by
  rw [Work.ELNest.T_iterate_ten, Work.ELNest.T_iterate_ten]
  rw [show 1024 * (θ + 1) = 1024 * θ + ((1024 : ℤ) : ℝ) by ring]
  exact Int.fract_add_intCast _ _

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **The boundary angles of the level-`(n+1)` `z₁`-polygon map to boundary angles of the
level-`n` polygon** (exact rational arithmetic; `T^[10] = θ ↦ fract (1024 θ)`).  The `+1` in
`βₙ + 1` is inert because `T` is `1`-periodic, so the image of the high boundary angle
`β_{n+1} + 1` is the *low* representative `βₙ` of the target pair's second angle.  The last two
conjuncts are `T_ten_alpha1`/`T_ten_alpha2` of `Submission/Work/ELAssembly/curveF_of_alphaPair.lean`. -/
theorem pullQ_pair (n : ℕ) :
    ((Work.EL.T)^[10] (Work.ELNest.bAng' (n + 1)) = Work.ELNest.bAng' n) ∧
    ((Work.EL.T)^[10] (Work.ELNest.bAng (n + 1) + 1) = Work.ELNest.bAng n) ∧
    ((Work.EL.T)^[10] Work.EL.alpha1 = Work.EL.alpha1) ∧
    ((Work.EL.T)^[10] Work.EL.alpha2 = Work.EL.alpha2) := by
  -- conjunct 1: the level-`(n+1)` low angle `β'_{n+1}` maps to `β'_n` (`T_iterate_bAng`);
  -- conjunct 2: the same for the high angle `β_{n+1} + 1`, the shift by `1` being inert;
  -- conjuncts 3, 4: the two root angles `α₁`, `α₂` are fixed by `T^[10]`.
  refine ⟨(Work.ELNest.T_iterate_bAng n).2, ?_, T_ten_alpha1, T_ten_alpha2⟩
  rw [T_ten_add_one, (Work.ELNest.T_iterate_bAng n).1]

end Work.ELAssembly
