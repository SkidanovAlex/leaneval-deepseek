/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# `QuarterParabolicIsFixed`

This module proves `Work.LANDCL.QuarterParabolicIsFixed`: every parabolic point of the cusp map
`T_{1/4}(z) = z̄² + 1/4` is *fixed*.

## The argument

The statement is the special case `c = 1/4` of `Work.LANDCL.ParabolicCycleIsOmegaLimit`
(`Work.FatouParabolic.parabolicCycleInOmegaLimit`) together with the elementary real dynamics of
the critical orbit of `T_{1/4}`: `(T_{1/4})^[n] (1/4) → 1/2`, proved in
`Work.FatouParabolic.tendsto_quarter_criticalOrbit` (the orbit of `1/4` is `1/2 + a_n` with
`a_{n+1} = a_n + a_n²`, `a_0 = -1/4`, an increasing sequence in `[-1/2, 0]`, whose limit `L`
satisfies `L = L + L²`, hence `L = 0`).

Given both, let `z` be parabolic of period `m` for `T_{1/4}`.  Fatou's theorem puts `z` in the
closure of `range (n ↦ (T_{1/4})^[n] (1/4))`, which is contained in that range together with its
limit `1/2` (the elementary `closure_range_subset_range_union_singleton_of_tendsto` of
`Work.LANDCL.ParamAngle`).  If `z = (T_{1/4})^[n] (1/4)` is a term of the orbit, then the
subsequence `t ↦ (T_{1/4})^[n + t m] (1/4)` is constantly `z` by periodicity, but also converges
to `1/2`; hence `z = 1/2`.  And `1/2` is fixed: `T_{1/4}(1/2) = 1/4 + 1/4 = 1/2`.
-/
import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FatouParabolic.Reduction
import Submission.Work.FatouParabolic.Quarter.tendsto_quarter_criticalOrbit
import Submission.Work.LANDCL.ParamAngle.onlyParabolicIsCycleOf_of_critOrbit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.FatouParabolic

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- `1/2` is a fixed point of `T_{1/4}` (the cusp of the period-`1` hyperbolic component). -/
theorem quarter_fixed_half : Tantibar (1 / 4 : ℂ) (1 / 2 : ℂ) = 1 / 2 := by
  norm_num [Tantibar, map_ofNat]

/-- The sequence `t ↦ n + t * m` tends to infinity when `0 < m`. -/
theorem tendsto_add_mul_atTop {n m : ℕ} (hm : 0 < m) :
    Tendsto (fun t : ℕ => n + t * m) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun t ht => ?_⟩
  have h1 : t ≤ t * m := Nat.le_mul_of_pos_right t hm
  omega

/-- **The elementary core of the `1/4` argument.**  If every parabolic point of `T_c` lies in
the closure of the critical orbit and the critical orbit converges to `ζ`, then every parabolic
point of `T_c` equals `ζ`. -/
theorem eq_of_isParabolic_of_tendsto_criticalOrbit {c ζ : ℂ}
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c)
    (hconv : Tendsto (fun n : ℕ => (Tantibar c)^[n] c) atTop (𝓝 ζ))
    {z : ℂ} (hz : ∃ m : ℕ, Work.Landing.IsParabolic c m z) : z = ζ := by
  obtain ⟨m, hmpar⟩ := hz
  have hmpos : 0 < m := hmpar.1.1
  have hmfix : (Tantibar c)^[m] z = z := hmpar.1.2
  have hcl : z ∈ closure (Set.range (fun n : ℕ => (Tantibar c)^[n] c)) := homega z ⟨m, hmpar⟩
  rcases Work.LANDCL.ParamAngle.closure_range_subset_range_union_singleton_of_tendsto hconv hcl
    with ⟨n, hn⟩ | hζ
  · -- `z` is a term of the critical orbit: the periodicity of `z` makes a subsequence constant
    have hconst : ∀ t : ℕ, (Tantibar c)^[n + t * m] c = z := by
      intro t
      induction t with
      | zero => simpa using hn
      | succ t ih =>
        rw [show n + (t + 1) * m = m + (n + t * m) from by ring, Function.iterate_add_apply,
          ih, hmfix]
    have htend1 : Tendsto (fun t : ℕ => (Tantibar c)^[n + t * m] c) atTop (𝓝 z) :=
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun t => (hconst t).symm)
    have htend2 : Tendsto (fun t : ℕ => (Tantibar c)^[n + t * m] c) atTop (𝓝 ζ) :=
      hconv.comp (tendsto_add_mul_atTop hmpos)
    exact tendsto_nhds_unique htend1 htend2
  · simpa [Set.mem_singleton_iff] using hζ

/-- **`QuarterParabolicIsFixed` from Fatou's theorem and the real dynamics of `T_{1/4}`.** -/
theorem quarterParabolicIsFixed_of (homega : Work.LANDCL.ParabolicCycleInOmegaLimit (1 / 4 : ℂ))
    (hconv : Tendsto (fun n : ℕ => (Tantibar (1 / 4 : ℂ))^[n] (1 / 4 : ℂ)) atTop (𝓝 (1 / 2 : ℂ))) :
    Work.LANDCL.QuarterParabolicIsFixed := by
  intro z hz
  rw [eq_of_isParabolic_of_tendsto_criticalOrbit homega hconv hz]
  exact quarter_fixed_half

/-- **`QuarterParabolicIsFixed`**, from the primitive classical input of the area. -/
theorem quarterParabolicIsFixed (hFatou : FatouParabolicInput) :
    Work.LANDCL.QuarterParabolicIsFixed :=
  quarterParabolicIsFixed_of (parabolicCycleInOmegaLimit hFatou (1 / 4))
    Work.FatouParabolic.Quarter.tendsto_quarter_criticalOrbit

end

end Work.FatouParabolic
