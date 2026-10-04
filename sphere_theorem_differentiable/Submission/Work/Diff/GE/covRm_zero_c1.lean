import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.BoundaryPlans
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.GE.EvolB.covRmSliceSmooth
import Submission.Work.Diff.GE.covRm_fixed_evol_cont
import Submission.Work.Diff.GE.hasDerivWithinAt_of_tendsto_deriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `C^1`-continuity at the initial time of `∇Rm` along a Ricci flow

For a Ricci flow `G` on `[0,T)` and fixed vectors `v a b c d` at a point `x`, the component
`s ↦ covRm (G s) x v a b c d` is continuous at `0` within `[0,T)`, and so is its one-sided time
derivative.

**Route.**  `s ↦ covRm (G s) x v a b c d` is the composition of the *time reparametrisation*
`τ ↦ τ²` with the slice `sl τ = covRm (G (τ²)) x v a b c d` of a family jointly smooth on the *open*
interval `(-√T, √T)` (`Work.Diff.GE.jointSmooth_sqFlow_sqrt` +
`Work.Diff.GE.EvolB.covRmSliceSmooth`).  Since `sl` is `C^∞` at `0` and *even*, it has a
second-order expansion at `0`, `deriv sl 0 = 0`, and
`Work.Diff.GE.hasDerivWithinAt_sum_sqrt` (with one summand) produces both the one-sided derivative
of `s ↦ sl (√s)` at `0` — of value `deriv (deriv sl) 0 / 2` — and the convergence of its derivative
along `s ↓ 0` to that value.  On `(0,T)` the function `s ↦ sl (√s)` *is* the component and its
`derivWithin` is its ordinary derivative, and at `0` the two one-sided derivatives agree
(`UniqueDiffWithinAt`), which gives the continuity of the one-sided derivative at `0`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

theorem covRm_zero_c1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
        ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.covRm (G s) x v a b c d)
          (Set.Ico 0 T) 0 ∧
        ContinuousWithinAt
          (fun s : ℝ ↦ derivWithin (fun σ : ℝ ↦ Submission.Diff.covRm (G σ) x v a b c d)
            (Set.Ico 0 T) s) (Set.Ico 0 T) 0 := by
  intro G T hflow x v a b c d
  by_cases hT : T ≤ 0
  · have hempty : Set.Ico (0 : ℝ) T = ∅ := Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)
    refine ⟨?_, ?_⟩ <;>
      · rw [hempty]
        simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    -- the reparametrised flow is jointly smooth on the *open* interval `(-√T, √T)`
    have hJsm : Submission.Diff.JointSmooth (cfq_sqFlow G)
        (Set.Ioo (-(Real.sqrt T)) (Real.sqrt T)) :=
      jointSmooth_sqFlow_sqrt hTpos hflow.1
    have hsqrtT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
    have h0 : (0 : ℝ) ∈ Set.Ioo (-(Real.sqrt T)) (Real.sqrt T) :=
      ⟨by linarith, hsqrtT⟩
    -- the reparametrised slice `sl` and the component `f`
    set sl : ℝ → ℝ := fun τ ↦ Submission.Diff.covRm (cfq_sqFlow G τ) x v a b c d with hsldef
    set f : ℝ → ℝ := fun s ↦ Submission.Diff.covRm (G s) x v a b c d with hfdef
    have hsl_smooth : ∀ u ∈ Set.Ioo (-(Real.sqrt T)) (Real.sqrt T),
        ContDiffAt ℝ (⊤ : ℕ∞)
          (fun τ : ℝ ↦ Submission.Diff.covRm (cfq_sqFlow G τ) x v a b c d) u :=
      fun u hu => Work.Diff.GE.EvolB.covRmSliceSmooth hLC isOpen_Ioo hJsm hu x v a b c d
    have hslsm : ContDiffAt ℝ (⊤ : ℕ∞) sl 0 := by
      rw [hsldef]; exact hsl_smooth 0 h0
    have hsl_diff : ∀ u ∈ Set.Ioo 0 (Real.sqrt T), DifferentiableAt ℝ sl u := by
      intro u hu
      refine (hsl_smooth u ⟨by linarith [hu.1, Real.sqrt_nonneg T], hu.2⟩).differentiableAt ?_
      simp
    have heven : ∀ τ : ℝ, sl (-τ) = sl τ := by
      intro τ; simp only [hsldef, cfq_sqFlow, neg_sq]
    -- the component is continuous at `0` from the right: this is part 1
    have hfeq : ∀ s ∈ Set.Ico 0 T, f s = sl (Real.sqrt s) := by
      intro s hs
      simp only [hfdef, hsldef, cfq_sqFlow, Real.sq_sqrt hs.1]
    have hcontf : ContinuousWithinAt f (Set.Ico 0 T) 0 := by
      refine cfq_continuousWithinAt_of_continuousAt_comp_sq (f := f) hTpos hslsm.continuousAt ?_
      intro s hs
      show Submission.Diff.covRm (G s) x v a b c d
        = Submission.Diff.covRm (cfq_sqFlow G (Real.sqrt s)) x v a b c d
      rw [show cfq_sqFlow G (Real.sqrt s) = G s from by
        rw [cfq_sqFlow, Real.sq_sqrt hs.1]]
    refine ⟨hcontf, ?_⟩
    -- part 2: the one-sided derivative of the component and its continuity at `0`
    set L : ℝ := deriv (deriv sl) 0 / 2 with hLdef
    have hmain := hasDerivWithinAt_sum_sqrt (n := 1) (c := fun _ : Fin 1 ↦ sl) hTpos
      (fun _ ↦ hslsm) (fun _ ↦ hsl_diff) (fun _ τ ↦ heven τ)
    have hhas_sl : HasDerivWithinAt (fun s : ℝ ↦ sl (Real.sqrt s)) L (Set.Ico 0 T) 0 := by
      rw [hLdef]; simpa using hmain.1 0
    have hhas : HasDerivWithinAt f L (Set.Ico 0 T) 0 := by
      refine hhas_sl.congr (fun y hy ↦ ?_) ?_
      · exact hfeq y hy
      · rw [hfeq 0 ⟨le_refl 0, hTpos⟩]
    have hval : derivWithin f (Set.Ico 0 T) 0 = L :=
      hhas.derivWithin (uniqueDiffWithinAt_Ico hTpos)
    -- the derivative of the component on the interior, and its limit at `0`
    have hderiv_eq : (fun s : ℝ ↦ derivWithin f (Set.Ico 0 T) s) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ sl (Real.sqrt s')) s) := by
      filter_upwards [Ioo_mem_nhdsGT hTpos] with s hs
      have hmem : Set.Ico (0 : ℝ) T ∈ 𝓝 s :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) Set.Ioo_subset_Ico_self
      rw [derivWithin_of_mem_nhds hmem]
      have hagree : f =ᶠ[𝓝 s] (fun s' : ℝ ↦ sl (Real.sqrt s')) := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
        exact hfeq s' ⟨le_of_lt hs'.1, hs'.2⟩
      exact hagree.deriv_eq
    have hlim : Filter.Tendsto (fun s : ℝ ↦ derivWithin f (Set.Ico 0 T) s)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
      have h2 : Filter.Tendsto (fun s : ℝ ↦ deriv (fun s' : ℝ ↦ sl (Real.sqrt s')) s)
          (𝓝[>] (0 : ℝ)) (𝓝 L) := by
        rw [hLdef]; simpa using hmain.2 0
      exact h2.congr' hderiv_eq.symm
    have hlim' := tendsto_nhdsWithin_Ico_of_tendsto_gt hTpos hlim hval
    show ContinuousWithinAt (fun s : ℝ ↦ derivWithin f (Set.Ico 0 T) s) (Set.Ico 0 T) 0
    rw [ContinuousWithinAt, hval]
    exact hlim'

end Work.Diff.GE
