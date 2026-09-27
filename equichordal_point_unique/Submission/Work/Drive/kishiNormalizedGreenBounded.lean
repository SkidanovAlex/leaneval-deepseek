import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Drive.WeakGreenAt
import Submission.Work.Drive.greenExhaustion_locallyBounded
import Submission.Work.Drive.normalizedGreenExhaustion_locallyBounded
import Submission.GreenFunction
import Submission.MaxPrincipleRegion
import Submission.RiemannSurface

namespace Work.Drive

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Filter Set
open scoped _root_.Topology Manifold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The chart sphere of a chart ball whose closed ball lies in the target is compact. -/
theorem isCompact_chartSphere' {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    IsCompact (Submission.chartSphere c a ρ) := by
  have hfront : frontier (Submission.chartBall c a ρ) = Submission.chartSphere c a ρ := by
    rw [IsOpen.frontier_eq (Submission.chartBall_isOpen c a ρ),
      Submission.closure_chartBall_eq_chartClosedBall hρ hsub,
      Submission.chartClosedBall_diff_chartBall]
  rw [← hfront]
  exact IsCompact.of_isClosed_subset (Submission.isCompact_closure_chartBall hsub)
    isClosed_frontier frontier_subset_closure

/-- The chart sphere of a chart ball whose closed ball lies in the target is nonempty. -/
theorem chartSphere_nonempty' {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    (Submission.chartSphere c a ρ).Nonempty := by
  have hmem : a + (ρ : ℂ) ∈ Metric.closedBall a ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ]
  refine ⟨c.symm (a + (ρ : ℂ)), ?_⟩
  rw [Submission.mem_chartSphere]
  refine ⟨c.map_target (hsub hmem), ?_⟩
  rw [c.right_inv (hsub hmem), Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]

/-- **The maximum principle on a chart ball.**  If `u` is harmonic on the chart ball of radius
`2ρ` around `A` and `|u| ≤ C` on the chart sphere of radius `ρ`, then `|u| ≤ C` on the whole chart
ball of radius `ρ`. -/
theorem abs_le_of_harmonicOnX_chartBall {c : OpenPartialHomeomorph X ℂ} {A : ℂ} {ρ C : ℝ}
    (hρ : 0 < ρ) (hsub1 : Metric.closedBall A ρ ⊆ c.target)
    (hsub2 : Metric.closedBall A (2 * ρ) ⊆ c.target)
    {u : X → ℝ} (hu : Submission.HarmonicOnX u (Submission.chartBall c A (2 * ρ)))
    (hC : ∀ ξ ∈ Submission.chartSphere c A ρ, |u ξ| ≤ C) :
    ∀ x ∈ Submission.chartBall c A ρ, |u x| ≤ C := by
  have hfront : frontier (Submission.chartBall c A ρ) = Submission.chartSphere c A ρ := by
    rw [IsOpen.frontier_eq (Submission.chartBall_isOpen c A ρ),
      Submission.closure_chartBall_eq_chartClosedBall hρ hsub1,
      Submission.chartClosedBall_diff_chartBall]
  have hsmall : Submission.chartBall c A ρ ⊆ Submission.chartBall c A (2 * ρ) := by
    intro y hy
    rw [Submission.mem_chartBall, Metric.mem_ball, dist_eq_norm] at hy ⊢
    exact ⟨hy.1, by linarith [hy.2]⟩
  have hbig : ∀ ξ ∈ Submission.chartSphere c A ρ, ξ ∈ Submission.chartBall c A (2 * ρ) := by
    intro ξ hξ
    rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hξ
    rw [Submission.mem_chartBall, Metric.mem_ball, dist_eq_norm]
    exact ⟨hξ.1, by linarith [hξ.2]⟩
  have hsub : Submission.SubharmonicOnX u (Submission.chartBall c A ρ) :=
    ⟨fun y hy => ((hu y (hsmall hy)).continuousAt).continuousWithinAt,
      fun y hy => (hu y (hsmall hy)).subharmonic⟩
  have hsub_neg : Submission.SubharmonicOnX (fun y => -u y) (Submission.chartBall c A ρ) :=
    ⟨fun y hy => ((hu y (hsmall hy)).continuousAt).neg.continuousWithinAt,
      fun y hy => (hu y (hsmall hy)).superharmonic.neg⟩
  have hne : (frontier (Submission.chartBall c A ρ)).Nonempty := by
    rw [hfront]; exact chartSphere_nonempty' hρ hsub1
  have hcomp : IsCompact (closure (Submission.chartBall c A ρ)) :=
    Submission.isCompact_closure_chartBall hsub1
  have key : ∀ (v : X → ℝ), Submission.SubharmonicOnX v (Submission.chartBall c A ρ) →
      (∀ ξ ∈ frontier (Submission.chartBall c A ρ), ∀ ε : ℝ, 0 < ε →
        ∀ᶠ z in 𝓝[Submission.chartBall c A ρ] ξ, v z ≤ C + ε) →
      ∀ y ∈ Submission.chartBall c A ρ, v y ≤ C :=
    fun v hv hlim => Submission.SubharmonicOnX.le_of_frontier_limsup
      (Submission.chartBall_isOpen c A ρ) hv hcomp hne hlim
  have hlim : ∀ ξ ∈ frontier (Submission.chartBall c A ρ), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[Submission.chartBall c A ρ] ξ, u z ≤ C + ε := by
    intro ξ hξ ε hε
    have hξsph : ξ ∈ Submission.chartSphere c A ρ := by rwa [hfront] at hξ
    have hle : u ξ ≤ C := le_trans (le_abs_self (u ξ)) (hC ξ hξsph)
    have hlt : u ξ < C + ε := by linarith
    have hcont : ContinuousAt u ξ := (hu ξ (hbig ξ hξsph)).continuousAt
    exact hcont.continuousWithinAt.eventually (eventually_le_nhds hlt)
  have hlim_neg : ∀ ξ ∈ frontier (Submission.chartBall c A ρ), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[Submission.chartBall c A ρ] ξ, -u z ≤ C + ε := by
    intro ξ hξ ε hε
    have hξsph : ξ ∈ Submission.chartSphere c A ρ := by rwa [hfront] at hξ
    have hle : -u ξ ≤ C := by have h := (abs_le.mp (hC ξ hξsph)).1; linarith
    have hlt : -u ξ < C + ε := by linarith
    have hcont : ContinuousAt (fun y => -u y) ξ := (hu ξ (hbig ξ hξsph)).continuousAt.neg
    exact hcont.continuousWithinAt.eventually (eventually_le_nhds hlt)
  intro x hx
  exact abs_le.mpr ⟨by linarith [key _ hsub_neg hlim_neg x hx], key _ hsub hlim x hx⟩

/-- **From clause 1 to clause 2.**  Given an exhaustion with Green functions whose normalized
versions are locally bounded off the pole, the normalized versions are uniformly comparable with
the unit logarithmic pole on a chart ball around the pole.

The proof is the maximum principle on a chart ball: for each `n`, the function
`G n · + log ‖ζ_a · - ζ_a a‖ - G n x₁` is harmonic in a punctured chart ball around `a` and bounded
there (pole clause of `IsGreenOn`), hence extends harmonically across `a`; its values on the
boundary sphere are controlled by clause 1, and the maximum principle bounds it inside. -/
theorem kishiLogPoleBound {a x₁ : X} (hx₁ : x₁ ≠ a)
    {Ω : ℕ → Set X} {G : ℕ → X → ℝ}
    (hΩopen₀ : IsOpen (Ω 0)) (hΩmono : ∀ n, Ω n ⊆ Ω (n + 1))
    (ha : a ∈ Ω 0) (hx : x₁ ∈ Ω 0)
    (hgreen : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n))
    (hbdd : ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
        |G n x - G n x₁| ≤ C) :
    ∃ C s : ℝ, 0 < s ∧ Metric.closedBall ((chartAt ℂ a) a) s ⊆ (chartAt ℂ a).target ∧
      ∀ n : ℕ, ∀ x : X, x ≠ a → x ∈ (chartAt ℂ a).source →
        ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ < s →
        |G n x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ - G n x₁| ≤ C := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ a with hc
  -- ### Step 1: a chart radius `ρ` with the closed `2ρ`-ball in the target and in `Ω 0`.
  have hsrc : a ∈ c.source := mem_chart_source ℂ a
  have hmem : c a ∈ c.target := c.map_source hsrc
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp
    (c.image_mem_nhds hsrc (Filter.inter_mem (hΩopen₀.mem_nhds ha) (c.open_source.mem_nhds hsrc)))
  obtain ⟨ε₂, hε₂, hε₂sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hmem)
  set ρ : ℝ := min ε₁ ε₂ / 4 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have h4 : 2 * ρ = min ε₁ ε₂ / 2 := by rw [hρdef]; ring
  have hlt₁ : 2 * ρ < ε₁ := by rw [h4]; linarith [min_le_left ε₁ ε₂, hε₁]
  have hlt₂ : 2 * ρ < ε₂ := by rw [h4]; linarith [min_le_right ε₁ ε₂, hε₂]
  have htarget2 : Metric.closedBall (c a) (2 * ρ) ⊆ c.target :=
    (Metric.closedBall_subset_ball hlt₂).trans hε₂sub
  have htarget : Metric.closedBall (c a) ρ ⊆ c.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans htarget2
  have hΩ0 : Submission.chartClosedBall c (c a) (2 * ρ) ⊆ Ω 0 := by
    intro y hy
    rw [Submission.mem_chartClosedBall, Metric.mem_closedBall, dist_eq_norm] at hy
    have hyball : c y ∈ Metric.ball (c a) ε₁ := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hy.2, hlt₁]
    obtain ⟨z, hz, hzy⟩ := hε₁sub hyball
    have hzy' : z = y := by
      rw [← c.left_inv hz.2, hzy, c.left_inv hy.1]
    rw [← hzy']
    exact hz.1
  have hmonoT : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hΩmono _)
  -- ### Step 2: the bound on the chart sphere of radius `ρ`.
  obtain ⟨C₁, hC₁⟩ := hbdd (Submission.chartSphere c (c a) ρ)
    (isCompact_chartSphere' hρpos htarget)
    (by
      intro y hy
      rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hy
      refine ⟨mem_univ y, fun hya => ?_⟩
      rw [hya, sub_self, norm_zero] at hy
      exact absurd hy.2.symm hρpos.ne')
  -- ### Step 3: the maximum principle on the chart ball of radius `ρ`.
  refine ⟨C₁ + |Real.log ρ|, ρ, hρpos, htarget, ?_⟩
  intro n x hxane hxsrc hxlt
  -- the big chart ball is inside `Ω n`
  have hbigΩ : Submission.chartBall c (c a) (2 * ρ) ⊆ Ω n := by
    intro y hy
    rw [Submission.mem_chartBall, Metric.mem_ball, dist_eq_norm] at hy
    refine hmonoT 0 n (Nat.zero_le n) (hΩ0 ?_)
    rw [Submission.mem_chartClosedBall, Metric.mem_closedBall, dist_eq_norm]
    exact ⟨hy.1, le_of_lt hy.2⟩
  -- the auxilliary function `H`
  set H : X → ℝ := fun y => G n y + Real.log ‖c y - c a‖ - G n x₁ with hHdef
  have hHval : ∀ y : X, H y = G n y + Real.log ‖c y - c a‖ - G n x₁ := fun y => by rw [hHdef]
  have hharm_punct : Submission.HarmonicOnX H (Submission.chartBall c (c a) (2 * ρ) \ {a}) := by
    intro y hy
    obtain ⟨hyball, hya⟩ := hy
    have hysrc : y ∈ c.source := (Submission.mem_chartBall.mp hyball).1
    have hyne : c y ≠ c a := by
      intro h
      have hy_eq : y = a := by rw [← c.left_inv hysrc, h, c.left_inv (mem_chart_source ℂ a)]
      exact hya hy_eq
    have hG : Submission.HarmonicOnXAt (G n) y :=
      (hgreen n).2.1 y ⟨hbigΩ hyball, hya⟩
    have hL : Submission.HarmonicOnXAt (fun y => Real.log ‖c y - c a‖) y := by
      have h := Submission.harmonicOnXAt_log_norm_chartAt (z₀ := a) (x := y)
        (by simpa [hc] using hysrc) (by simpa [hc] using hyne)
      simpa [hc] using h
    have : Submission.HarmonicOnXAt (fun y => G n y + Real.log ‖c y - c a‖ - G n x₁) y :=
      (hG.add hL).sub (Submission.harmonicOnXAt_const (G n x₁))
    simpa only [hHdef] using this
  -- the removable singularity at the pole
  obtain ⟨Cg, Vn, hVn, hVb⟩ := (hgreen n).2.2.2
  set V : Set X := Vn ∩ Submission.chartBall c (c a) (2 * ρ) with hVdef
  have hVnhds : V ∈ 𝓝 a := by
    rw [hVdef]
    exact Filter.inter_mem hVn ((Submission.chartBall_isOpen c (c a) (2 * ρ)).mem_nhds
      (Submission.mem_chartBall.mpr ⟨hsrc, by rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; linarith [hρpos]⟩))
  have hVbdd : ∃ M : ℝ, ∀ y ∈ V, y ≠ a → |H y| ≤ M := by
    refine ⟨Cg + |G n x₁|, fun y hy hyane => ?_⟩
    obtain ⟨hyV, hyball⟩ := hy
    have hGlog : |G n y + Real.log ‖c y - c a‖| ≤ Cg := hVb y hyV (hbigΩ hyball) hyane
    rw [hHval y, abs_sub_le_iff]
    exact ⟨by linarith [(abs_le.mp hGlog).2, neg_le_abs (G n x₁)],
      by linarith [(abs_le.mp hGlog).1, le_abs_self (G n x₁)]⟩
  obtain ⟨A, hA⟩ := Work.Drive.exists_update_harmonicOnXAt_of_bounded_punctured
    (q := a) (u := H) (V := V) hVnhds
    (fun y hy => hharm_punct y ⟨hy.1.2, hy.2⟩) hVbdd
  set H' : X → ℝ := Function.update H a A with hH'def
  have hharm_big : Submission.HarmonicOnX H' (Submission.chartBall c (c a) (2 * ρ)) := by
    intro y hy
    by_cases hya : y = a
    · rw [hya, hH'def]; exact hA
    · have hev : H' =ᶠ[𝓝 y] H := by
        filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hya)] with z hz
        rw [hH'def, Function.update_of_ne hz]
      exact Work.Drive.harmonicOnXAt_of_eventuallyEq hev (hharm_punct y ⟨hy, hya⟩)
  -- the sphere bound for `H'`
  have hsphere : ∀ ξ ∈ Submission.chartSphere c (c a) ρ, |H' ξ| ≤ C₁ + |Real.log ρ| := by
    intro ξ hξ
    have hξ' := hξ
    rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hξ'
    have hξa : ξ ≠ a := by
      intro h
      rw [h, sub_self, norm_zero] at hξ'
      exact absurd hξ'.2.symm hρpos.ne'
    have hupd : H' ξ = H ξ := by rw [hH'def, Function.update_of_ne hξa]
    have hlog : Real.log ‖c ξ - c a‖ = Real.log ρ := by rw [hξ'.2]
    have hHb : |G n ξ - G n x₁| ≤ C₁ := hC₁ n ξ (by rw [Submission.mem_chartSphere]; exact hξ)
    rw [hupd, hHval, hlog]
    have hkey : G n ξ + Real.log ρ - G n x₁ = (G n ξ - G n x₁) + Real.log ρ := by ring
    rw [hkey]
    calc |(G n ξ - G n x₁) + Real.log ρ| ≤ |G n ξ - G n x₁| + |Real.log ρ| := abs_add_le _ _
      _ ≤ C₁ + |Real.log ρ| := by linarith [hHb]
  have hmain := abs_le_of_harmonicOnX_chartBall (c := c) (A := c a) (ρ := ρ)
    (C := C₁ + |Real.log ρ|) hρpos htarget htarget2 hharm_big hsphere
  have hxball : x ∈ Submission.chartBall c (c a) ρ := by
    rw [Submission.mem_chartBall, Metric.mem_ball, dist_eq_norm]
    exact ⟨hxsrc, hxlt⟩
  have hxa : x ≠ a := hxane
  have hfin : |H' x| ≤ C₁ + |Real.log ρ| := hmain x hxball
  rw [hH'def, Function.update_of_ne hxa, hHval] at hfin
  simpa only [hc] using hfin

/-- **Kishi's local boundedness of the normalized Green functions of an exhaustion.**

On a connected, second countable, non-compact `ℂ`-charted surface `X` and points `a ≠ x₁` there is
an exhaustion `Ω : ℕ → Set X` by nested relatively compact open sets covering `X`, together with
Green functions `G n` of `Ω n` with pole `a` (`Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n)`,
extended by `0` outside `Ω n`), such that

* for every compact `K ⊆ X ∖ {a}` the *normalized* Green functions `G n · - G n x₁` are uniformly
  bounded on `K`: `|G n x - G n x₁| ≤ C` for all `n` and all `x ∈ K`; and
* there are `C` and `s > 0` with `closedBall (ζ_a a) s ⊆ target` and
  `|G n x + log ‖ζ_a x - ζ_a a‖ - G n x₁| ≤ C` for all `n` and all `x ≠ a` with
  `‖ζ_a x - ζ_a a‖ < s`.

Both are the classical convergence result of Kishi for normalized Green functions (equivalently
`G n - R n` converges locally uniformly on `X ∖ {a}`, where
`R n = lim_{x→a}(G n x + log ‖ζ_a x - ζ_a a‖)` is the Robin constant).  The second clause follows
from the first: given clause 1 and `IsGreenOn`, the function
`G n · + log ‖ζ_a · - ζ_a a‖ - G n x₁` extends harmonically across `a` (removable singularity, from
the pole clause of `IsGreenOn`) and the maximum principle on a chart ball inside `Ω 0` bounds it by
its values on the sphere, where clause 1 applies. -/
theorem kishiNormalizedGreenBounded {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (a x₁ : X) (hx₁ : x₁ ≠ a) :
    ∃ (Ω : ℕ → Set X) (G : ℕ → X → ℝ),
      (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, Ω n ⊆ Ω (n + 1)) ∧ (⋃ n, Ω n) = Set.univ ∧
      (∀ n, a ∈ Ω n) ∧ (∀ n, x₁ ∈ Ω n) ∧
      (∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n)) ∧
      (∀ n, ∀ x, x ∉ Ω n → G n x = 0) ∧
      (∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
        |G n x - G n x₁| ≤ C) ∧
      (∃ C s : ℝ, 0 < s ∧ Metric.closedBall ((chartAt ℂ a) a) s ⊆ (chartAt ℂ a).target ∧
        ∀ n : ℕ, ∀ x : X, x ≠ a → x ∈ (chartAt ℂ a).source →
          ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ < s →
          |G n x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ - G n x₁| ≤ C) := by
  obtain ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8⟩ := greenExhaustion_data (X := X) hX a x₁
  have h9 : ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
      |G n x - G n x₁| ≤ C :=
    normalizedGreenExhaustion_locallyBounded (X := X) hx₁ h1 h2 h3 h4 h7 h8
  obtain ⟨C, s, hs, hsub, hbd⟩ :=
    kishiLogPoleBound (X := X) (a := a) (x₁ := x₁) hx₁ (h1 0) h3 (h5 0) (h6 0) h7 h9
  exact ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8, h9, C, s, hs, hsub, hbd⟩

end Work.Drive
