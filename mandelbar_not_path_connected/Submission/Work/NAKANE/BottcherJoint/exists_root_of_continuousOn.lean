import Mathlib
import Submission.Work.NAKANE.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.BottcherJoint

/-- **A continuous `m`-th root on a nonempty convex domain.**  If `U ⊆ ℂ × ℂ` is open, convex and
nonempty (in particular simply connected), `W : ℂ × ℂ → ℂ` is continuous and nonvanishing on `U`,
and `m > 0`, then `W` has a continuous `m`-th root on `U`.

This is a direct application of Mathlib's branch-of-the-root theorem
`Complex.exists_continuousOn_pow_eq` (`Mathlib/Analysis/Complex/BranchLogRoot.lean`), whose
hypothesis `IsSimplyConnected U` is supplied by convexity plus nonemptiness: a nonempty convex
subset of the real vector space `ℂ × ℂ` is contractible (`Convex.contractibleSpace`), hence simply
connected (`SimplyConnectedSpace.ofContractible`, an instance).  The nonemptiness hypothesis cannot
be dropped: for `U = ∅` all hypotheses are vacuous but the conclusion would demand a *global* `m`-th
root of an arbitrary `W` (e.g. `W = fun p => p.1`, `m = 2`). -/
theorem exists_root_of_continuousOn {U : Set (ℂ × ℂ)} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUne : U.Nonempty) {W : ℂ × ℂ → ℂ} (hW : ContinuousOn W U) (hne : ∀ p ∈ U, W p ≠ 0)
    {m : ℕ} (hm : 0 < m) :
    ∃ σ : ℂ × ℂ → ℂ, ContinuousOn σ U ∧ ∀ p, σ p ^ m = W p := by
  -- A nonempty convex subset of `ℂ × ℂ` is contractible, hence simply connected.
  have hsc : IsSimplyConnected U :=
    @SimplyConnectedSpace.ofContractible U _ (hUc.contractibleSpace hUne)
  -- `W` does not vanish on `U`.
  have hU₀ : 0 ∉ W '' U := by
    rintro ⟨p, hp, hpw⟩
    exact hne p hp hpw
  -- Mathlib's branch-of-the-root theorem, with `X = ℂ × ℂ`.
  exact Complex.exists_continuousOn_pow_eq hsc hUo hW hU₀ (Nat.pos_iff_ne_zero.mp hm)

end Work.NAKANE.BottcherJoint
