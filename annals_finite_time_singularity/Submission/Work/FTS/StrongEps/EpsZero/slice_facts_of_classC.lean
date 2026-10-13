import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS_RegExport.RXB.tendsto_nhdsGT_zero_of_radial_trace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Slice facts for the class-`C` datum of the `L₁₂` zero-mode chapter

This file proves `Work.FTS.StrongEps.EpsZero.slice_facts_of_classC`: for a datum `f` which is
`C^∞` on the *open* quadrant (`Work.FTS.EllipticEst.SmoothOpen f`), whose weighted boundary
traces vanish (`Work.FTS.Nonlin.BdryTraces α 6 f`) and which vanishes off the open quadrant
(`hzero`), the radial slices `z ↦ f z θ` are

* differentiable on `(0,∞)` with derivative `Work.Spaces.pz f z θ` (`= ∂_z f`),
* continuous on `[0,∞)`, and
* vanishing at `z → +∞`,

**for every** `θ ∈ Work.Spaces.Iθ = [0,π/2]`, including the endpoints `θ = 0`, `π/2`.

At the endpoints the slice is identically zero by `hzero` (so all three clauses are immediate);
at an interior angle `θ ∈ (0,π/2)` the first clause is the open-quadrant smoothness `SmoothOpen`,
the third is the `z → +∞` clause of `BdryTraces` (via
`Work.FTS_RegExport.RXB.tendsto_nhdsGT_zero_of_radial_trace` and the `atTop` analogue proved
below), and the second combines the same two facts with `f 0 θ = 0` (again `hzero`) and the
elementary observation that a function with a limit along `𝓝[>] 0` attaining that limit at `0`
is continuous within `[0,∞)` at `0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero

set_option autoImplicit false

/-! ## Two elementary limit bridges -/

/-- A function with a limit along the *punctured* right neighbourhood `𝓝[>] a`, whose value at `a`
is that limit, has the same limit along the closed right neighbourhood `𝓝[≥] a`.  (The
`𝓝[>]`-filter is finer than `𝓝[≥]`, so the implication needs the explicit value at `a`; we go
through the bases `Ioo a u` resp. `Ico a u`.) -/
theorem tendsto_Ici_of_tendsto_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Filter.Tendsto F (𝓝[>] a) (𝓝 b)) (hb : F a = b) :
    Filter.Tendsto F (𝓝[≥] a) (𝓝 b) := by
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩

/-- A function which is continuous on the *open* right half-line, vanishes at `0` and tends to `0`
at `0⁺` is continuous on the closed half-line `[0,∞)`. -/
theorem continuousOn_Ici_of_continuousOn_Ioi_of_tendsto {u : ℝ → ℝ}
    (h : ContinuousOn u (Set.Ioi (0 : ℝ)))
    (hu0 : u 0 = 0)
    (h0 : Filter.Tendsto u (𝓝[≥] (0 : ℝ)) (𝓝 0)) :
    ContinuousOn u (Set.Ici (0 : ℝ)) := by
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  rcases eq_or_lt_of_le hx' with hx0 | hx0
  · rw [← hx0]
    change Filter.Tendsto u (𝓝[≥] (0 : ℝ)) (𝓝 (u 0))
    rw [hu0]
    exact h0
  · exact ((h.continuousWithinAt hx0).continuousAt
      (isOpen_Ioi.mem_nhds hx0)).continuousWithinAt

/-- The `z → +∞` member of the `BdryTraces` pair: if `z·(u z·w z)² → 0` at `+∞` then `u → 0`.
This uses `w z ≥ 1` for `z ≥ 1`, so that `(u z)² ≤ z·(u z·w z)²` there. -/
theorem tendsto_atTop_zero_of_radial_trace {u : ℝ → ℝ}
    (h : Filter.Tendsto (fun z => z * (u z * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto u Filter.atTop (𝓝 0) := by
  have hw1 : ∀ z : ℝ, 1 ≤ z → (1 : ℝ) ≤ Work.Spaces.w z := by
    intro z hz
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith
  have hsq : Filter.Tendsto (fun z : ℝ => (u z) ^ 2) Filter.atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun z => sq_nonneg _) ?_ h
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    have hw := hw1 z hz
    have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have huz : (0 : ℝ) ≤ (u z) ^ 2 := sq_nonneg _
    have hA : (0 : ℝ) ≤ (u z) ^ 2 * (Work.Spaces.w z) ^ 2 := mul_nonneg huz (sq_nonneg _)
    have h1 : (u z) ^ 2 ≤ (u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by nlinarith
    have h2 : (u z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ z * ((u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa using mul_le_mul_of_nonneg_right hz hA
    have h3 : z * ((u z) ^ 2 * (Work.Spaces.w z) ^ 2) = z * (u z * Work.Spaces.w z) ^ 2 := by
      ring
    linarith [h1, h2, h3.le]
  have habs : Filter.Tendsto (fun z => |u z|) Filter.atTop (𝓝 0) := by
    have hcomp : Filter.Tendsto (fun z => Real.sqrt ((u z) ^ 2)) Filter.atTop
        (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Real.sqrt_zero] at hcomp
    convert hcomp using 1
    funext z
    rw [Real.sqrt_sq_eq_abs]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

/-- An identically vanishing slice is differentiable, with derivative `0 = pz f z θ`. -/
theorem hasDerivAt_of_slice_eq_zero {f : ℝ → ℝ → ℝ} {θ z : ℝ} (h0 : ∀ s : ℝ, f s θ = 0) :
    HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z := by
  have hfun : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) := funext h0
  have hpz : Work.Spaces.pz f z θ = 0 := by
    simp only [Work.Spaces.pz]
    rw [hfun]
    exact deriv_const z (0 : ℝ)
  rw [hpz, hfun]
  exact hasDerivAt_const z 0

/-! ## The target -/

theorem slice_facts_of_classC {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hb : Work.FTS.Nonlin.BdryTraces α 6 f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → f z θ = 0) :
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => f s θ) (Set.Ici 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0)) := by
  -- `hzero`, in the form we use it: a slice outside the open angle interval vanishes identically.
  have hz0 : ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → ∀ z : ℝ, f z θ = 0 :=
    fun θ hθ z => hzero z θ (fun hc => hθ hc.2)
  -- the value at `z = 0` of every slice
  have hf0 : ∀ θ : ℝ, f 0 θ = 0 :=
    fun θ => hzero 0 θ (fun hc => (lt_irrefl (0 : ℝ)) hc.1)
  -- the two radial clauses of `BdryTraces` at the slot `(a,b) = (0,0)`
  have hbdry0 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := fun θ hθ => by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using
      (hb 0 0 (by norm_num)).1 θ hθ |>.1
  have hbdryTop : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) := fun θ hθ => by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using
      (hb 0 0 (by norm_num)).1 θ hθ |>.2
  refine ⟨?_, ?_, ?_⟩
  · intro θ hθ z hz
    by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · exact hsm.hasDerivAt_slice h hz
    · exact hasDerivAt_of_slice_eq_zero (hz0 θ h)
  · intro θ hθ
    by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · refine continuousOn_Ici_of_continuousOn_Ioi_of_tendsto
        ((hsm.curry_z h).continuousOn) (hf0 θ) ?_
      refine tendsto_Ici_of_tendsto_Ioi (F := fun s : ℝ => f s θ) (a := 0) (b := 0) ?_ (hf0 θ)
      exact Work.FTS_RegExport.RXB.tendsto_nhdsGT_zero_of_radial_trace (hbdry0 θ h)
    · have hfun : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) := funext (hz0 θ h)
      rw [hfun]
      exact continuousOn_const
  · intro θ hθ
    by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · exact tendsto_atTop_zero_of_radial_trace (hbdryTop θ h)
    · have hfun : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) := funext (hz0 θ h)
      rw [hfun]
      exact tendsto_const_nhds

end Work.FTS.StrongEps.EpsZero
