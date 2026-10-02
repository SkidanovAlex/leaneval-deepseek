/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# Every parameter ray accumulates on the connectedness locus

This file proves **step 1** of the FSeed route
(`NOTES_LEAD_mandelbar_EL_F_contracts.md` §7.3, row `FSeed`): the parameter ray at angle `θ`
has a limit point `c₁` which lies on the mandelbar and *not* on the ray,

  `∃ c ∈ Mb, c ∈ closure (paramRay θ) ∧ c ∉ paramRay θ`,

i.e. the ray lands on / accumulates at the connectedness locus.

The proof is unconditional in `Work.Top.NakaneData Mb Φ` (Nakane's parameter Böttcher
coordinate as an abstract homeomorphism with a continuous potential tending to `+∞` at infinity):
the points of the ray at level `1 + 1/(n+1)` lie in the compact sublevel set
`{potential ≤ log 2}`, so a subsequence converges to some `c`; the potential of the limit is the
limit of the potentials, namely `0`, whence `c ∈ Mb`; being in `Mb`, `c` is not on the ray.

Applied to `Mb = Work.ParamRays.Mb`, `Φ = Work.ParamRays.Phi` and `θ = α₁ = 371/1023`, this is
the parameter `c₁` of the FSeed route.
-/
import Submission.Work.Top.Defs
import Submission.Work.ParamRays.MbDefs
import Submission.Work.FSeed.Defs

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

/-- **Every parameter ray accumulates on the connectedness locus**: for every angle `θ` there is
a parameter `c ∈ Mb` that is a limit point of the parameter ray `R(θ)` but is not on it. -/
theorem exists_paramRay_limit {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    (θ : ℝ) :
    ∃ c : ℂ, c ∈ Mb ∧ c ∈ closure (Work.Top.NakaneData.paramRay hN θ) ∧
      c ∉ Work.Top.NakaneData.paramRay hN θ := by
  -- the point of the ray at level `1 + 1/(n+1)`
  set x : ℕ → ℂ := fun n => hN.rayPt θ (1 + 1 / ((n : ℝ) + 1)) with hxdef
  have ht : ∀ n : ℕ, 1 < 1 + 1 / ((n : ℝ) + 1) := by
    intro n
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr h
    linarith
  -- all these points lie in the compact sublevel set `{potential ≤ log 2}`
  have hxmem : ∀ n : ℕ, x n ∈ {c : ℂ | Work.Top.potential Mb Φ c ≤ Real.log 2} := by
    intro n
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one h]; linarith
    have h2 : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr h
    rw [Set.mem_setOf_eq, hN.potential_rayPt (ht n)]
    exact Real.log_le_log (by linarith) (by linarith)
  obtain ⟨c, _hc_mem, φ, hφ, hlim⟩ :=
    (hN.isCompact_le_potential (Real.log 2)).tendsto_subseq hxmem
  -- the potential of the limit is `0`, so `c ∈ Mb`
  have hpot_x : ∀ n : ℕ, Work.Top.potential Mb Φ (x n) = Real.log (1 + 1 / ((n : ℝ) + 1)) :=
    fun n => hN.potential_rayPt (ht n)
  have hlim1 : Tendsto (fun n : ℕ => Real.log (1 + 1 / ((φ n : ℝ) + 1))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have hbase' : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using hbase
    have hcomp : Tendsto (fun n : ℕ => 1 + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 1) :=
      hbase'.comp hφ.tendsto_atTop
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hcomp
    rw [Real.log_one] at hlog
    exact hlog
  have hlim2 : Tendsto (fun n : ℕ => Work.Top.potential Mb Φ (x (φ n))) atTop (𝓝 0) := by
    have hfun : (fun n : ℕ => Work.Top.potential Mb Φ (x (φ n))) =
        fun n : ℕ => Real.log (1 + 1 / ((φ n : ℝ) + 1)) := by
      funext n
      exact hpot_x (φ n)
    rw [hfun]
    exact hlim1
  have hlim3 : Tendsto (fun n : ℕ => Work.Top.potential Mb Φ (x (φ n))) atTop
      (𝓝 (Work.Top.potential Mb Φ c)) :=
    hN.continuous_potential.continuousAt.tendsto.comp hlim
  have hzero : Work.Top.potential Mb Φ c = 0 := tendsto_nhds_unique hlim3 hlim2
  have hcMb : c ∈ Mb := (hN.potential_eq_zero_iff c).mp hzero
  have hmem : ∀ n : ℕ, x (φ n) ∈ Work.Top.NakaneData.paramRay hN θ := by
    intro n
    exact (hN.mem_paramRay_iff).mpr
      ⟨hN.rayPt_notMem (ht (φ n)), 1 + 1 / ((φ n : ℝ) + 1), ht (φ n), hN.Phi_rayPt (ht (φ n))⟩
  refine ⟨c, hcMb, ?_, ?_⟩
  · have h1 : c ∈ closure (Set.range fun n : ℕ => x (φ n)) :=
      mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun n => Set.mem_range_self _)
    exact closure_mono (fun z hz => by obtain ⟨n, rfl⟩ := hz; exact hmem n) h1
  · exact fun hc => hN.paramRay_subset_compl θ hc hcMb

/-- **Step 1 of the FSeed route**: the parameter ray at the root angle `α₁ = 371/1023` has a
limit point on the mandelbar which is not on the ray. -/
theorem exists_paramRay_limit_α₁ (hN : Work.Top.NakaneData Work.ParamRays.Mb Work.ParamRays.Phi) :
    ∃ c : ℂ, c ∈ Work.ParamRays.Mb ∧
      c ∈ closure (Work.Top.NakaneData.paramRay hN α₁) ∧
      c ∉ Work.Top.NakaneData.paramRay hN α₁ :=
  exists_paramRay_limit hN α₁

/-! ## The parameter plane of the tricorn -/

/-- The `Φ`-value of a point of the parameter ray at angle `θ` and level `t` is the same in the
abstract interface `Work.Top` and in the parameter-ray area. -/
theorem rayPoint_eq_rayDir (θ t : ℝ) :
    Work.Top.NakaneData.rayPoint θ t = (t : ℂ) * Work.ParamRays.rayDir θ := by
  rw [Work.Top.NakaneData.rayPoint, Work.ParamRays.rayDir]
  congr 1
  push_cast
  ring

/-- The parameter ray of the abstract interface `Work.Top` is the parameter ray of
`Work.ParamRays`, for the tricorn's own Böttcher coordinate. -/
theorem paramRay_eq (hN : Work.Top.NakaneData Work.ParamRays.Mb Work.ParamRays.Phi) (θ : ℝ) :
    Work.Top.NakaneData.paramRay hN θ = Work.ParamRays.paramRay θ := by
  ext c
  rw [Work.Top.NakaneData.mem_paramRay_iff, Work.ParamRays.mem_paramRay]
  constructor
  · rintro ⟨hc, t, ht, h⟩
    exact ⟨hc, t, ht, by rw [← rayPoint_eq_rayDir]; exact h⟩
  · rintro ⟨hc, t, ht, h⟩
    exact ⟨hc, t, ht, by rw [rayPoint_eq_rayDir]; exact h⟩

/-- **Step 1 of the FSeed route**, in the form of the contract: the parameter ray
`R(371/1023)` has a limit point on the mandelbar which is not on the ray. -/
theorem exists_paramRay_limit_α₁_paramRay
    (hN : Work.Top.NakaneData Work.ParamRays.Mb Work.ParamRays.Phi) :
    ∃ c : ℂ, c ∈ Work.ParamRays.Mb ∧ c ∈ closure (Work.ParamRays.paramRay α₁) ∧
      c ∉ Work.ParamRays.paramRay α₁ := by
  obtain ⟨c, hc, hcl, hnc⟩ := exists_paramRay_limit_α₁ hN
  exact ⟨c, hc, by rwa [paramRay_eq hN α₁] at hcl, by rwa [paramRay_eq hN α₁] at hnc⟩

end Work.FSeed

end
