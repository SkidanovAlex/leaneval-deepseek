import Mathlib
import Submission.Work.Profiles.Basic
import Submission.Work.Profiles.Eta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Profiles

open scoped ContDiff
/-- In this Mathlib pin `ContDiff ℝ ⊤ = ContDiff ℝ ω` is *analytic* (see
`contDiff_omega_iff_analyticOnNhd`), and an analytic function is rigid: it is determined by its
germ at any point.  Hence a function that equals the identity on `(-∞, 1/2]` must equal the
identity on all of `ℝ`, so it cannot equal `C * exp` on `[3, ∞)`.

This is the reason a filling profile must be stated with `ContDiff ℝ ∞` (smooth) rather than
`ContDiff ℝ ⊤` (analytic): see `Work.Profiles.FillProfile`. -/
theorem no_analytic_profile :
    ¬ ∃ (C : ℝ) (f : ℝ → ℝ), ContDiff ℝ ⊤ f ∧ (∀ r ≤ 1/2, f r = r) ∧
      (∀ r ≥ 3, f r = C * Real.exp r) := by
  rintro ⟨C, f, hf, hcore, hcusp⟩
  -- `f` is analytic, and so is the identity.
  have han : AnalyticOnNhd ℝ f Set.univ := contDiff_omega_iff_analyticOnNhd.mp hf
  have hid : AnalyticOnNhd ℝ (fun x : ℝ => x) Set.univ := analyticOnNhd_id
  -- `f` coincides with the identity on a neighbourhood of `0` (any point of `(-∞, 1/2]`).
  have hmem : Set.Iio (1/2 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
  have hev : f =ᶠ[nhds (0:ℝ)] (fun x => x) :=
    Filter.eventually_of_mem hmem (fun x hx => hcore x hx.le)
  -- Identity theorem: `f = id` on the preconnected set `univ`.
  have heq : Set.EqOn f (fun x : ℝ => x) Set.univ :=
    han.eqOn_of_preconnected_of_eventuallyEq hid isPreconnected_univ (Set.mem_univ 0) hev
  have hf3 : f 3 = 3 := heq (Set.mem_univ 3)
  have hf4 : f 4 = 4 := heq (Set.mem_univ 4)
  -- Cusp values.
  have h3 : C * Real.exp 3 = 3 := (hcusp 3 le_rfl).symm.trans hf3
  have h4 : C * Real.exp 4 = 4 := (hcusp 4 (by norm_num)).symm.trans hf4
  -- Dividing the two relations gives `exp 1 = 4/3`, contradicting `2 < exp 1`.
  have hexp4 : Real.exp 4 = Real.exp 3 * Real.exp 1 := by
    rw [show (4:ℝ) = 3 + 1 by norm_num, Real.exp_add]
  have h : 4 = 3 * Real.exp 1 := by
    have hh : C * Real.exp 4 = C * Real.exp 3 * Real.exp 1 := by rw [hexp4]; ring
    rw [h4, h3] at hh
    exact hh
  have h1 : Real.exp 1 = 4/3 := by linarith
  linarith [Real.exp_one_gt_two, h1]

end Work.Profiles
