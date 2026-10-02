/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# The FSeed API for `Work.EL.RootParabolic`

The structure `Work.EL.RootParabolic` itself is declared in `Submission/Work/ELTop/Defs.lean`
(§6 of the contracts, with the extra Böttcher fields `φ`, `bottcher`, `hN` needed by the EL
areas).  `Submission/Work/FSeed/Classify.lean` *produces* it from the classical input bundle
`Work.FSeed.RootParabolicInput`; this file collects the API of that structure in the form the
downstream areas (ELNest, ELRig, FQC, FBif, the Top glue) consume it.

## Main results

* `Work.FSeed.root_period_half`, `root_ne_per`, `root_mult`, `root_simple` — the fields;
* `Work.FSeed.root_landsAt_α₁`, `root_landsAt_α₂`, `root_coLands`, `root_rootRaysLand` — the rays;
* `Work.FSeed.root_periodicPoint`, `root_isParabolic`, `root_isRepellingOrParabolic`,
  `root_multiplier2_eq_deriv` — the parabolic structure;
* `Work.FSeed.root_tendsto_critOrbit`, `root_critOrbit_ne`, `root_mem_filledJulia`,
  `root_mem_Mandelbar` — the dynamics of the critical orbit;
* `Work.FSeed.root_landsAt_portrait` — the `L`-portrait: the pair `{T^j α₁, T^j α₂}` lands at the
  `j`-th point of the parabolic cycle.
-/
import Submission.Work.FSeed.Defs
import Submission.Work.ELTop.Defs
import Submission.Work.Landing.Land.Landing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function
open scoped Topology

noncomputable section

namespace Work.FSeed

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Fields of `Work.EL.RootParabolic` -/

/-- The period-`5` condition. -/
theorem root_period_half {c : ℂ} (d : Work.EL.RootParabolic c) : (Tantibar c)^[5] d.z₁ = d.z₁ :=
  d.per_half

/-- `z₁` has no smaller period. -/
theorem root_ne_per {c : ℂ} (d : Work.EL.RootParabolic c) :
    ∀ j ∈ Finset.Ioo 0 5, (Tantibar c)^[j] d.z₁ ≠ d.z₁ := d.ne_per

/-- The parabolic condition. -/
theorem root_mult {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.multiplier2 c 5 d.z₁ = 1 := d.mult

/-- `z₁` is not a cusp. -/
theorem root_simple {c : ℂ} (d : Work.EL.RootParabolic c) :
    iteratedDeriv 2 (F c) d.z₁ ≠ 0 := d.simple

/-- The first root ray lands at `z₁`. -/
theorem root_landsAt_α₁ {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.landsAt c α₁ d.z₁ := d.rays.1

/-- The second root ray lands at `z₁`. -/
theorem root_landsAt_α₂ {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.landsAt c α₂ d.z₁ := d.rays.2

/-- The two root rays co-land. -/
theorem root_coLands {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.coLands c α₁ α₂ := ⟨d.z₁, d.rays.1, d.rays.2⟩

/-- The root rays of the period-`5` component land at `z₁` (`Work.Landing.RootRaysLand`). -/
theorem root_rootRaysLand {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.RootRaysLand c d.z₁ := d.rays

/-- `z₁` is a periodic point of period `5`. -/
theorem root_periodicPoint {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.PeriodicPoint (Tantibar c) 5 d.z₁ := ⟨by norm_num, d.per_half⟩

/-- `z₁` is a parabolic point of odd period `5`. -/
theorem root_isParabolic {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.IsParabolic c 5 d.z₁ := ⟨root_periodicPoint d, d.mult⟩

/-- `z₁` is repelling or parabolic (the conclusion of the landing theorem). -/
theorem root_isRepellingOrParabolic {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.IsRepellingOrParabolic c 5 d.z₁ := Or.inr (root_isParabolic d)

/-- The multiplier is the derivative of `F c`. -/
theorem root_multiplier2_eq_deriv {c : ℂ} (d : Work.EL.RootParabolic c) :
    Work.Landing.multiplier2 c 5 d.z₁ = deriv (F c) d.z₁ := rfl

/-- The critical orbit converges to `z₁`. -/
theorem root_tendsto_critOrbit {c : ℂ} (d : Work.EL.RootParabolic c) :
    Tendsto (fun n : ℕ => (F c)^[n] c) atTop (nhds d.z₁) := d.crit.1

/-- The critical orbit never hits `z₁`. -/
theorem root_critOrbit_ne {c : ℂ} (d : Work.EL.RootParabolic c) :
    ∀ n : ℕ, (F c)^[n] c ≠ d.z₁ := d.crit.2

/-- The critical value lies in the wake side of the level-`0` pair (`k = 1` of the wake
condition). -/
theorem root_critValue_mem_wakeSide {c : ℂ} (d : Work.EL.RootParabolic c) :
    c ∈ Work.EL.wakeSide d.hN d.z₁ 0 := by
  have h := d.wake 1 le_rfl
  simpa using h

/-- The wake condition for every `k ≥ 1`. -/
theorem root_critOrbit_mem_wakeSide {c : ℂ} (d : Work.EL.RootParabolic c) (k : ℕ) (hk : 1 ≤ k) :
    (Tantibar c)^[k] 0 ∈ Work.EL.wakeSide d.hN d.z₁ ((k - 1) % 5) := d.wake k hk

/-- The index of the wake side lies in `{0,1,2,3,4}`. -/
theorem root_wakeSide_index_lt (k : ℕ) : (k - 1) % 5 < 5 := Nat.mod_lt _ (by norm_num)

/-- `z₁` lies in the filled Julia set `K_c`: it is periodic, hence its orbit is bounded. -/
theorem root_mem_filledJulia {c : ℂ} (d : Work.EL.RootParabolic c) :
    d.z₁ ∈ Work.ParamRays.filledJulia c := by
  change Work.ParamRays.BoundedOrbit c d.z₁
  change ∃ M : ℝ, ∀ n : ℕ, ‖Work.ParamRays.orbit c d.z₁ n‖ ≤ M
  refine ⟨‖d.z₁‖ + ‖Work.ParamRays.orbit c d.z₁ 1‖ + ‖Work.ParamRays.orbit c d.z₁ 2‖
    + ‖Work.ParamRays.orbit c d.z₁ 3‖ + ‖Work.ParamRays.orbit c d.z₁ 4‖, fun n => ?_⟩
  have hfix : ((Tantibar c)^[5]) d.z₁ = d.z₁ := d.per_half
  have hper : ∀ m : ℕ, Work.ParamRays.orbit c d.z₁ (5 * m) = d.z₁ := by
    intro m
    rw [Work.ParamRays.orbit, Function.iterate_mul]
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hn : Work.ParamRays.orbit c d.z₁ n = Work.ParamRays.orbit c d.z₁ (n % 5) := by
    conv_lhs => rw [← Nat.div_add_mod n 5]
    rw [Work.ParamRays.orbit_add, hper (n / 5)]
  rw [hn]
  have h5 : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have nz := norm_nonneg d.z₁
  have n0 := norm_nonneg (Work.ParamRays.orbit c d.z₁ 1)
  have n1 := norm_nonneg (Work.ParamRays.orbit c d.z₁ 2)
  have n2 := norm_nonneg (Work.ParamRays.orbit c d.z₁ 3)
  have n3 := norm_nonneg (Work.ParamRays.orbit c d.z₁ 4)
  interval_cases h : n % 5 <;> simp <;> linarith

/-! ## The orbit portrait of a root-parabolic parameter -/

/-- **The `L`-portrait at a root-parabolic parameter**: the level-`j` pair of portrait angles
lands at the `j`-th point of the parabolic cycle. -/
theorem root_landsAt_portrait {c : ℂ} (d : Work.EL.RootParabolic c) (j : ℕ) :
    Work.Landing.landsAt c (pairRay₁ j) ((Tantibar c)^[j] d.z₁) ∧
      Work.Landing.landsAt c (pairRay₂ j) ((Tantibar c)^[j] d.z₁) :=
  ⟨Work.Landing.landsAt_iterate d.rays.1 j, Work.Landing.landsAt_iterate d.rays.2 j⟩

end Work.FSeed

end
