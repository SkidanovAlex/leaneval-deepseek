/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.PackSplit` — `SplitData` from (H1) and the wall factorization (H2)

This module composes the two proved halves:

* `ParSplit.Sqrt.exists_continuousOn_sq_eq_mul_of_real` (a real factorization `G = A·h` with `h`
  nowhere zero on a simply connected ball gives a continuous `Δ` with `Δ² = G`), and
* `ParSplit.BuildSplit.nonempty_splitData_of_char` (`(H1) + Δ ⟹ SplitData d`),

into the single statement

  `(H1) + (H2) ⟹ Nonempty (SplitData d)`,

which is the exact form in which `ParSplit.splitPair_exists` and `ParSplit.wall_factorization`
deliver their conclusions.  Together with `ParSplit.parNormal_of_splitData` this reduces
`Work.PARIMPL.exists_parNormal` to importing four lemmas and composing them
(see `ParSplit/NOTES.md` §6).
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Sqrt
import Submission.Work.PARIMPL.ParSplit.BuildSplit
import Submission.Work.PARIMPL.ParSplit.splitPair_exists
import Submission.Work.PARIMPL.ParSplit.wall_factorization

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

/-- **(H1) + (H2) give the split datum.**  With `m`, `G` as produced by
`ParSplit.splitPair_exists` and a real wall function `A` and a nowhere zero `h` with `G = A·h` as
produced by `ParSplit.wall_factorization`, the structure `SplitData d` exists.

The continuous square root is `Δ := √A · √h`; the chart scale of the normal form is `√h` and the
half-difference is `Δ`, so `S.E = 2Δ`. -/
theorem nonempty_splitData_of_wall {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) {m G : ℂ → ℂ}
    (hm : ContinuousOn m (Metric.ball c₀ ρ)) (hG : ContinuousOn G (Metric.ball c₀ ρ))
    (hm₀ : m c₀ = d.z₁) (hG₀ : G c₀ = 0)
    (hchar : ∀ c ∈ Metric.ball c₀ ρ, ∀ z ∈ Metric.ball d.z₁ R,
      (Work.EL.F c z = z ↔ (z - m c) ^ 2 = G c))
    {A : ℂ → ℝ} (hA : ContinuousOn A (Metric.ball c₀ ρ))
    {hw : ℂ → ℂ} (hhw : ContinuousOn hw (Metric.ball c₀ ρ))
    (hhw0 : ∀ c ∈ Metric.ball c₀ ρ, hw c ≠ 0)
    (hfac : ∀ c ∈ Metric.ball c₀ ρ, G c = (A c : ℂ) * hw c) :
    Nonempty (SplitData d) := by
  -- a continuous square root of `hw`, hence `Δ := realSqrt A · √hw` with `Δ² = G`
  obtain ⟨s, hs, hspow⟩ := exists_continuousOn_sq_eq_ball hρ hhw hhw0
  set Δ : ℂ → ℂ := fun c => realSqrt (A c) * s c with hΔdef
  have hΔcont : ContinuousOn Δ (Metric.ball c₀ ρ) :=
    (continuousOn_realSqrt_comp hA).mul hs
  have hΔsq : ∀ c ∈ Metric.ball c₀ ρ, Δ c ^ 2 = G c := by
    intro c hc
    rw [hΔdef, mul_pow, realSqrt_sq, hspow c, hfac c hc]
  -- the split pair lies in the disc on a smaller ball
  have hΔ₀ : Δ c₀ = 0 := by
    have h1 : Δ c₀ ^ 2 = (0 : ℂ) := by rw [hΔsq c₀ (mem_ball_self hρ), hG₀]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  obtain ⟨ρ', hρ', hρ'ρ, hsmall⟩ :=
    exists_small_ball_of_continuous (z₁ := d.z₁) hρ hR hm hΔcont hm₀ hΔ₀
  refine nonempty_splitData_of_char d hρ' hR (hm.mono (ball_subset_ball hρ'ρ))
    (hG.mono (ball_subset_ball hρ'ρ)) hm₀ hG₀
    (hΔcont.mono (ball_subset_ball hρ'ρ)) ?_ ?_ hρ' le_rfl ?_
  · intro c hc
    exact hΔsq c (ball_subset_ball hρ'ρ hc)
  · intro c hc
    exact hchar c (ball_subset_ball hρ'ρ hc)
  · intro c hc
    exact hsmall c hc

/-- **The split datum exists.**  Composing the proved halves (H1) `ParSplit.splitPair_exists` and
(H2) `ParSplit.wall_factorization` through `nonempty_splitData_of_wall`.  This is the last step
before the assembly `ParSplit.parNormal_of_splitData`, which yields `ParNormal d`. -/
theorem nonempty_splitData {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    Nonempty (SplitData d) := by
  obtain ⟨ρ, hρ, R, hR, m, G, hm, hG, hm₀, hG₀, hchar⟩ := splitPair_exists d
  obtain ⟨ρ', hρ', hρ'ρ, A, hA, _hA0, hw, hhw, hhw0, hfac⟩ :=
    wall_factorization d hρ hR hm hG hm₀ hG₀ hchar
  exact nonempty_splitData_of_wall (ρ := ρ') (R := R) d hρ' hR
    (hm.mono (ball_subset_ball hρ'ρ)) (hG.mono (ball_subset_ball hρ'ρ)) hm₀ hG₀
    (fun c hc => hchar c (ball_subset_ball hρ'ρ hc)) hA hhw hhw0 hfac

end Work.PARIMPL.ParSplit
