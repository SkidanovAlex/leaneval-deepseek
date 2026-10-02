/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.LavaursA.pa_bounded` — the attracting petal is bounded

The wide attracting petal `Pa` of the Leau–Fatou flower of the simple parabolic point `z₁` of
`Ft c₀ = (T_c₀)^[10]` is a **bounded** subset of `ℂ`: it is contained in the filled Julia set of
the quadratic antipolynomial `T_c₀(z) = z̄² + c₀`, hence in the closed disc of radius `max 2 ‖c₀‖`.

The mathematics is the escape criterion.  A point `y ∈ Pa` has an `Ft c₀`-orbit converging to
`z₁` (`ParabolicFlower.tendsto_Pa`), in particular a bounded one, say `‖(Ft c₀)^[q] y‖ ≤ B` for
all `q`.  Since `Ft c₀ = (T_c₀)^[10]`, every `T_c₀`-iterate of `y` has the form
`(T_c₀)^[r] ((Ft c₀)^[q] y)` with `r ≤ 9`, and the nine remaining iterates do not increase the
bound beyond the explicit recursion `x ↦ x² + ‖c₀‖` started at `B` (`orbitBound`).  Hence the
`T_c₀`-orbit of `y` is bounded, i.e. `y` lies in `K c₀ = {z | BoundedOrbit c₀ z}`
(`Work.ParamRays.BoundedOrbit`); the escape criterion `Work.ParamRays.norm_le_max_of_bounded`
then gives `‖y‖ ≤ max 2 ‖c₀‖`, which is the asserted uniform bound.
-/
import Mathlib
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.PARIMPL.Basic
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Filter Function Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.LavaursA

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The nine-iterate recursion

The `T_c`-orbit of a point of norm `≤ B` is bounded by the explicit recursion
`orbitBound c B`, whose first `10` values majorise the first `10` iterates and which is monotone.
Only the values `orbitBound c B r` for `r ≤ 9` are ever used. -/

/-- An explicit bound for the `r`-th iterate of a point of norm `≤ B` under `T_c`: the recursion
`x ↦ x² + ‖c‖` started at `max B 1`. -/
private def orbitBound (c : ℂ) (B : ℝ) : ℕ → ℝ
  | 0 => max B 1
  | (r + 1) => (orbitBound c B r) ^ 2 + ‖c‖

private theorem orbitBound_one_le (c : ℂ) (B : ℝ) : ∀ r, 1 ≤ orbitBound c B r := by
  intro r
  induction r with
  | zero => exact le_max_right B 1
  | succ r ih =>
      have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
      show (1 : ℝ) ≤ (orbitBound c B r) ^ 2 + ‖c‖
      nlinarith [sq_nonneg (orbitBound c B r)]

private theorem orbitBound_step_le (c : ℂ) (B : ℝ) (r : ℕ) :
    orbitBound c B r ≤ orbitBound c B (r + 1) := by
  have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : 1 ≤ orbitBound c B r := orbitBound_one_le c B r
  show orbitBound c B r ≤ (orbitBound c B r) ^ 2 + ‖c‖
  nlinarith

private theorem orbitBound_mono (c : ℂ) (B : ℝ) : Monotone (orbitBound c B) := by
  intro r s hrs
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih => exact le_trans ih (orbitBound_step_le c B s)

private theorem norm_iterate_le_orbitBound (c : ℂ) (w : ℂ) {B : ℝ} (hB : ‖w‖ ≤ B) :
    ∀ r, ‖(Tantibar c)^[r] w‖ ≤ orbitBound c B r := by
  intro r
  induction r with
  | zero => exact le_trans hB (le_max_left B 1)
  | succ r ih =>
      have hstep : ‖(Tantibar c)^[r + 1] w‖ ≤ ‖(Tantibar c)^[r] w‖ ^ 2 + ‖c‖ := by
        rw [Function.iterate_succ_apply']
        exact Work.ParamRays.norm_Tantibar_le c _
      have hmono : ‖(Tantibar c)^[r] w‖ ^ 2 ≤ (orbitBound c B r) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ih 2
      show ‖(Tantibar c)^[r + 1] w‖ ≤ (orbitBound c B r) ^ 2 + ‖c‖
      linarith

/-! ## The petal is bounded -/

/-- **The attracting petal of the parabolic flower is bounded.**

A point of `Pa` has a convergent `Ft c₀ = (T_c₀)^[10]`-orbit, hence a bounded `T_c₀`-orbit, so it
lies in the filled Julia set of `T_c₀` and therefore in the closed disc of radius `max 2 ‖c₀‖`. -/
theorem pa_bounded {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ y ∈ fl.Pa, ‖y‖ ≤ R₀ := by
  refine ⟨max 2 ‖c₀‖, lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c₀‖), fun y hy => ?_⟩
  -- the `Ft c₀`-orbit of `y` converges, hence is bounded
  have hconv : Tendsto (fun q : ℕ => (Work.PARIMPL.Ft c₀)^[q] y) atTop (nhds d.z₁) :=
    fl.tendsto_Pa y hy
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ q : ℕ, ‖(Work.PARIMPL.Ft c₀)^[q] y‖ ≤ B := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto
      (fun q : ℕ => (Work.PARIMPL.Ft c₀)^[q] y) hconv).subset_closedBall (0 : ℂ)
    refine ⟨R, fun q => ?_⟩
    have h1 := hR (Set.mem_range_self q)
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
  -- hence the `T_c₀`-orbit of `y` is bounded: the iterates split as `n = r + 10 * q`, `r ≤ 9`
  have hbd : Work.ParamRays.BoundedOrbit c₀ y := by
    refine ⟨orbitBound c₀ B 9, fun n => ?_⟩
    show ‖(Tantibar c₀)^[n] y‖ ≤ orbitBound c₀ B 9
    set q := n / 10 with hq
    set r := n % 10 with hr
    have hr10 : r ≤ 9 := by omega
    have hn : n = r + 10 * q := by omega
    have hkey : (Tantibar c₀)^[n] y = (Tantibar c₀)^[r] ((Work.PARIMPL.Ft c₀)^[q] y) := by
      rw [hn, Function.iterate_add_apply, Function.iterate_mul, ← Work.PARIMPL.Ft_eq_tantibar]
    rw [hkey]
    exact le_trans (norm_iterate_le_orbitBound c₀ _ (hB q) r) (orbitBound_mono c₀ B hr10)
  -- the escape criterion gives the norm bound
  exact Work.ParamRays.norm_le_max_of_bounded c₀ y hbd

end Work.PARIMPL2.LavaursA
