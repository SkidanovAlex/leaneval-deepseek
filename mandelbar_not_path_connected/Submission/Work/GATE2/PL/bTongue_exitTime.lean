import Mathlib
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.PARIMPL.Transit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Metric

namespace Work.GATE2.PL

/-- **The exit time at a tongue parameter is as large as we like.**  Let `e` be a parameter of the
implosion side near `c₀` whose transit coordinate `transU P M.nIn` lies within `r/2` of the leak
lattice `y₀ + ℤ` (the `b`-tongue `Work.GATE.bTongue`).  Then the tongue integer can be chosen
below `M.nIn - N`, i.e. the exit time `m := M.nIn - k` is at least `N + 1`, on a radius `ρ > 0`
depending only on `N`, `y₀`, `r` and the data.

Proof: the *theorem* `Work.PARIMPL.TransitData.blowup` (not the `blowup` field, which is stated at
frontier points) applies at `a := c₀`, because `P.a2₀ : P.a2 c₀ = 0` and `c₀ ∈ ball c₀ P.ρ₀`; it
gives `Tendsto (fun c => (transU P M.nIn c).re) (𝓝[P.Nm] c₀) atBot`.  For `e` close enough to `c₀`
the real part of `transU` is below `y₀ + (M.nIn - N) - r/2 - 1`; then any `k : ℤ` with
`dist (transU e) (y₀ + k) < r/2` satisfies `k ≤ Re (transU e) - y₀ + r/2 < M.nIn - N`. -/
theorem bTongue_exitTime {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M} {y₀ r : ℝ} (N : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ e ∈ P.Nm ∩ Metric.ball c₀ ρ,
      Work.GATE.bTongue (fun c => Work.PARIMPL.transU P M.nIn c) y₀ r e →
        ∃ k : ℤ, dist (Work.PARIMPL.transU P M.nIn e) (((y₀ + (k : ℝ)) : ℝ) : ℂ) < r / 2 ∧
          (N : ℤ) ≤ (M.nIn : ℤ) - k := by
  -- The phase blow-up at the parabolic locus: `Re (transU) → −∞`.
  have hblow : Filter.Tendsto (fun c => (Work.PARIMPL.transU P M.nIn c).re)
      (nhdsWithin c₀ P.Nm) Filter.atBot :=
    T.blowup c₀ P.a2₀ (by rw [Metric.mem_ball, dist_self]; exact P.hρ₀)
  -- On a `nhdsWithin`-neighbourhood of `c₀` in `Nm`, `Re (transU)` is below the threshold
  -- `y₀ + (nIn − N) − r/2 − 1`, so that every tongue integer is `< nIn − N`.
  have hev : ∀ᶠ c in nhdsWithin c₀ P.Nm,
      (Work.PARIMPL.transU P M.nIn c).re ≤
        y₀ + (((M.nIn : ℤ) - (N : ℤ) : ℤ) : ℝ) - r / 2 - 1 :=
    (Filter.tendsto_atBot.mp hblow) _
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨ρ, hρpos, hρsub⟩ := hev
  refine ⟨ρ, hρpos, ?_⟩
  intro e he ht
  obtain ⟨k, hk⟩ := ht
  refine ⟨k, hk, ?_⟩
  have hbnd : (Work.PARIMPL.transU P M.nIn e).re ≤
      y₀ + (((M.nIn : ℤ) - (N : ℤ) : ℤ) : ℝ) - r / 2 - 1 :=
    hρsub ⟨he.2, he.1⟩
  -- The real part of the tongue point differs from the real part of the lattice point by less
  -- than `r/2`.
  have h1 : |(Work.PARIMPL.transU P M.nIn e).re - (y₀ + (k : ℝ))| ≤
      dist (Work.PARIMPL.transU P M.nIn e) (((y₀ + (k : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.dist_eq]
    calc |(Work.PARIMPL.transU P M.nIn e).re - (y₀ + (k : ℝ))|
        = |((Work.PARIMPL.transU P M.nIn e) - (((y₀ + (k : ℝ)) : ℝ) : ℂ)).re| := by
          rw [Complex.sub_re, Complex.ofReal_re]
      _ ≤ ‖(Work.PARIMPL.transU P M.nIn e) - (((y₀ + (k : ℝ)) : ℝ) : ℂ)‖ :=
          Complex.abs_re_le_norm _
  have hlt : - (r / 2) < (Work.PARIMPL.transU P M.nIn e).re - (y₀ + (k : ℝ)) :=
    (abs_lt.mp (lt_of_le_of_lt h1 hk)).1
  -- Hence `k < nIn − N`, and both sides are integers.
  have hklt : (k : ℝ) < (((M.nIn : ℤ) - (N : ℤ) : ℤ) : ℝ) := by linarith
  have hkz : k < (M.nIn : ℤ) - (N : ℤ) := by exact_mod_cast hklt
  omega

end Work.GATE2.PL
