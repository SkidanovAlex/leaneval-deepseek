/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.Split` — the splitting datum

The parabolic fixed point `z₁` of the second return map `Work.EL.F c₀ = (T_{c₀})^[10]` is simple
(`d.mult`, `d.simple`); for `c` near `c₀` it splits into two simple fixed points.  This module
fixes the *shape* of that datum (`SplitData`), so that the lemmas which consume it (the
`swap`/`fix` dichotomy, the multiplier conjugacy, the bounds, the assembly of `ParNormal d`)
can be stated independently of the way the datum is produced.

The producing theorem is `Work.PARIMPL.ParSplit.split_exists`.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

variable {c₀ : ℂ}

/-- **The splitting datum** at a root-parabolic parameter: a ball `ball c₀ ρ`, a disc
`ball z₁ R`, and continuous `m E` with `m c₀ = z₁`, `E c₀ = 0`, such that for every `c` in the
ball the two points `m c ± E c/2` are fixed by the second return map `Work.EL.F c`, and the
fixed point set of `Work.EL.F c` inside `ball z₁ R` is exactly that pair. -/
structure SplitData (d : Work.EL.RootParabolic c₀) where
  /-- radius of the parameter ball. -/
  ρ : ℝ
  hρ : 0 < ρ
  /-- radius of the dynamical disc. -/
  R : ℝ
  hR : 0 < R
  /-- the midpoint of the two split fixed points. -/
  m : ℂ → ℂ
  /-- the difference of the two split fixed points. -/
  E : ℂ → ℂ
  cont_m : ContinuousOn m (ball c₀ ρ)
  cont_E : ContinuousOn E (ball c₀ ρ)
  m₀ : m c₀ = d.z₁
  E₀ : E c₀ = 0
  fixed_add : ∀ c ∈ ball c₀ ρ, Work.EL.F c (m c + E c / 2) = m c + E c / 2
  fixed_sub : ∀ c ∈ ball c₀ ρ, Work.EL.F c (m c - E c / 2) = m c - E c / 2
  /-- **uniqueness**: inside `ball z₁ R` these two are the only fixed points. -/
  unique : ∀ c ∈ ball c₀ ρ, ∀ z ∈ ball d.z₁ R,
    (Work.EL.F c z = z ↔ z = m c + E c / 2 ∨ z = m c - E c / 2)

namespace SplitData

variable {d : Work.EL.RootParabolic c₀} (S : SplitData d)

/-- The two split fixed points are within `‖E c‖/2` of the midpoint, so they lie in the
dynamical disc as soon as the midpoint is far enough from its boundary. -/
theorem fixed_add_mem {c : ℂ} (h : dist (S.m c) d.z₁ + ‖S.E c‖ / 2 < S.R) :
    S.m c + S.E c / 2 ∈ ball d.z₁ S.R := by
  rw [mem_ball, dist_eq_norm]
  have h1 : ‖S.m c + S.E c / 2 - d.z₁‖ ≤ ‖S.m c - d.z₁‖ + ‖S.E c / 2‖ := by
    calc ‖S.m c + S.E c / 2 - d.z₁‖ = ‖(S.m c - d.z₁) + S.E c / 2‖ := by ring_nf
      _ ≤ ‖S.m c - d.z₁‖ + ‖S.E c / 2‖ := norm_add_le _ _
  have h2 : ‖S.E c / 2‖ = ‖S.E c‖ / 2 := by rw [norm_div]; norm_num
  have h3 : ‖S.m c - d.z₁‖ = dist (S.m c) d.z₁ := by rw [dist_eq_norm]
  rw [h2, h3] at h1
  linarith [h1, h]

theorem fixed_sub_mem {c : ℂ} (h : dist (S.m c) d.z₁ + ‖S.E c‖ / 2 < S.R) :
    S.m c - S.E c / 2 ∈ ball d.z₁ S.R := by
  rw [mem_ball, dist_eq_norm]
  have h1 : ‖S.m c - S.E c / 2 - d.z₁‖ ≤ ‖S.m c - d.z₁‖ + ‖S.E c / 2‖ := by
    calc ‖S.m c - S.E c / 2 - d.z₁‖ = ‖(S.m c - d.z₁) - S.E c / 2‖ := by ring_nf
      _ ≤ ‖S.m c - d.z₁‖ + ‖S.E c / 2‖ :=
            norm_sub_le (S.m c - d.z₁) (S.E c / 2)
  have h2 : ‖S.E c / 2‖ = ‖S.E c‖ / 2 := by rw [norm_div]; norm_num
  have h3 : ‖S.m c - d.z₁‖ = dist (S.m c) d.z₁ := by rw [dist_eq_norm]
  rw [h2, h3] at h1
  linarith [h1, h]

/-- `E c = 0` exactly when the two split fixed points coincide, i.e. at the parabolic
parameters of the ball. -/
theorem E_eq_zero_iff {c : ℂ} : S.E c = 0 ↔ S.m c + S.E c / 2 = S.m c - S.E c / 2 := by
  constructor
  · intro h; rw [h]; ring
  · intro h
    have : S.E c / 2 = 0 := by linear_combination h / 2
    simpa using this

/-- **The `swap`/`fix` dichotomy.**  The antiholomorphic square root `g = (T_c)^[5]` of
`Work.EL.F c = g ∘ g` permutes the fixed points of `Work.EL.F c`.  Hence, as soon as
`g (m c + E c/2)` stays inside the disc `ball z₁ R` where the fixed points are classified by
`SplitData.unique`, it must be one of the two split fixed points. -/
theorem swap_or_fix_of_split {d : Work.EL.RootParabolic c₀} (S : SplitData d) {c : ℂ}
    (hc : c ∈ ball c₀ S.ρ) (hmem : gtc c (S.m c + S.E c / 2) ∈ ball d.z₁ S.R) :
    gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 ∨
      gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 := by
  have hcomm : ∀ w : ℂ, gtc c (Work.EL.F c w) = Work.EL.F c (gtc c w) := by
    intro w
    have h : Work.EL.F c = fun v : ℂ => gtc c (gtc c v) := Ft_eq_g_comp c
    rw [h]
  have hfix : Work.EL.F c (gtc c (S.m c + S.E c / 2)) = gtc c (S.m c + S.E c / 2) := by
    rw [← hcomm (S.m c + S.E c / 2), S.fixed_add c hc]
  exact (S.unique c hc _ hmem).mp hfix

end SplitData

end Work.PARIMPL.ParSplit
