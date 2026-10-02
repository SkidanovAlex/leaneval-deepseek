/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Ledger item 5 — the Snail lemma isolated from the elementary part of the dichotomy

`Work.LANDCL.SnailDichotomy` says: a periodic dynamic ray whose landing point `z` is not
attracting lands at a repelling or parabolic point.  Unfolding the definitions, the statement has
two halves:

* the **elementary** half: `¬ IsAttracting` means `‖multiplier2 c k z‖ ≥ 1` (the "attracting"
  alternative is exactly `‖·‖ < 1`, and the periodicity of `z` is automatic from the landing,
  `Work.Landing.landsAt_periodic`);
* the **Snail-lemma** half: no Ray can land at a point whose second-return multiplier is neutral
  *non-parabolic*, i.e. `‖λ‖ = 1` forces `λ = 1`.

Here the first half is proved and the second is isolated as the single `Prop`
`Work.LandLeaves.NoNeutralLanding`, so that the open content of ledger item 5 is exactly one
statement about the dynamics of the return map (the Snail lemma, Milnor 18.10) rather than the
dichotomy as a whole.  The classical argument for `NoNeutralLanding`: the ray at the periodic
angle `θ` is invariant under `(T_c)^[k]` (`Work.LandLeaves.rayAccum_iterate_image`) and
accumulates at `z`; if `λ` were a root of unity different from `1`, the `q`-th iterate
(`λ^q = 1`) would be a parabolic-type germ whose local dynamics ("snail" / Leau–Fatou flower)
spirals along finitely many petals and admits no invariant ray; if `|λ| = 1` with `λ` not a root
of unity, the germ is linearisable in a disk by the Kœnigs/Siegel theory and the ray cannot
spiral on a circle.

The special case `Odd k` is *proved* below (`noNeutralLanding_of_odd`) from the realness of the
second-return multiplier of an odd-period point
(`Work.Landing.Family.deriv_tsq_iterate_odd_real`), which is what the workspace's existing
`Work.Landing.landsAt_repelling_or_parabolic` uses.  For even `k` the multiplier is genuinely
non-real (an exact `T`-period-`4` point of `c = -1` has `deriv (Tsq)^[4] = -523 - 731i`), so
realness is not available and the Snail lemma is needed.
-/
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.attractingCyclesInner
import Submission.Work.LANDCL.Defs
import Submission.Work.Landing.Family.deriv_tsq_iterate_odd_real

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The Snail lemma in the form used by the landing theorem**: a dynamic ray cannot land at a
*neutral non-parabolic* periodic point, i.e. at a periodic point of period `k` whose second-return
multiplier has modulus `1` but is not `1`.

This is the whole open content of ledger item 5: everything else in `Work.LANDCL.SnailDichotomy`
is elementary (see `snailDichotomy_of_noNeutralLanding`). -/
def NoNeutralLanding : Prop :=
  ∀ (c : ℂ) (θ : ℝ) (k : ℕ) (z : ℂ), 0 < k → Work.Landing.PeriodicAngle θ k →
    Work.Landing.landsAt c θ z → ‖Work.Landing.multiplier2 c k z‖ = 1 →
    Work.Landing.multiplier2 c k z = 1

/-- **The Snail dichotomy from the Snail lemma.**  `NoNeutralLanding` (the Snail lemma) implies
`Work.LANDCL.SnailDichotomy`: the only other ingredient is `‖multiplier2‖ ≥ 1`, which is the
negation of `IsAttracting` together with the periodicity of the landing point. -/
theorem snailDichotomy_of_noNeutralLanding (h : NoNeutralLanding) :
    Work.LANDCL.SnailDichotomy := by
  intro c θ k z hk hper hland hnotattr
  have hfix : (Tantibar c)^[k] z = z := Work.Landing.landsAt_periodic hland hper
  have hpp : Work.Landing.PeriodicPoint (Tantibar c) k z := ⟨hk, hfix⟩
  have hge : 1 ≤ ‖Work.Landing.multiplier2 c k z‖ := by
    by_contra hlt
    exact hnotattr ⟨hpp, lt_of_not_ge hlt⟩
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact Or.inl ⟨hpp, hlt⟩
  · exact Or.inr ⟨hpp, h (c := c) (θ := θ) (k := k) (z := z) hk hper hland heq.symm⟩

/-- **The Snail lemma for odd periods, proved.**  For odd `k` the second-return multiplier of a
periodic point is a *nonnegative real* (`Work.Landing.Family.deriv_tsq_iterate_odd_real`), so
`‖λ‖ = 1` forces `λ = 1`; this is the case that the workspace already had, here in the
vocabulary of `NoNeutralLanding`. -/
theorem noNeutralLanding_of_odd (c : ℂ) (θ : ℝ) {k : ℕ} (z : ℂ) (hodd : Odd k) (_hk : 0 < k)
    (hper : Work.Landing.PeriodicAngle θ k) (hland : Work.Landing.landsAt c θ z)
    (hnorm : ‖Work.Landing.multiplier2 c k z‖ = 1) :
    Work.Landing.multiplier2 c k z = 1 := by
  obtain ⟨r, hr, hrmul⟩ :=
    Work.Landing.Family.deriv_tsq_iterate_odd_real c hodd (Work.Landing.landsAt_periodic hland hper)
  have hmul : Work.Landing.multiplier2 c k z = (r : ℂ) := hrmul
  have hnormr : ‖Work.Landing.multiplier2 c k z‖ = r := by
    rw [hmul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  rw [hnormr] at hnorm
  rw [hmul, hnorm]
  norm_num

/-- **`Work.LANDCL.SnailDichotomy` restricted to odd periods**: the elementary half of the ledger's
item 5, with the Snail input replaced by the realness of the multiplier.  This is the statement
that `Work.Landing.landsAt_repelling_or_parabolic` proves, in the vocabulary of the ledger. -/
theorem snailDichotomy_odd :
    ∀ (c : ℂ) (θ : ℝ) (k : ℕ) (z : ℂ), Odd k → 0 < k → Work.Landing.PeriodicAngle θ k →
      Work.Landing.landsAt c θ z → ¬ Work.Landing.IsAttracting c k z →
      Work.Landing.IsRepelling c k z ∨ Work.Landing.IsParabolic c k z := by
  intro c θ k z hodd hk hper hland hnotattr
  have hfix : (Tantibar c)^[k] z = z := Work.Landing.landsAt_periodic hland hper
  have hpp : Work.Landing.PeriodicPoint (Tantibar c) k z := ⟨hk, hfix⟩
  obtain ⟨r, hr, hrmul⟩ := Work.Landing.Family.deriv_tsq_iterate_odd_real c hodd hfix
  have hmul : Work.Landing.multiplier2 c k z = (r : ℂ) := hrmul
  have hnormr : ‖Work.Landing.multiplier2 c k z‖ = r := by
    rw [hmul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hge : 1 ≤ r := by
    by_contra hlt
    exact hnotattr ⟨hpp, by rw [hnormr]; exact lt_of_not_ge hlt⟩
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact Or.inl ⟨hpp, by rw [hnormr]; exact hlt⟩
  · exact Or.inr ⟨hpp, by rw [hmul, ← heq]; norm_num⟩

end Work.LandLeaves
