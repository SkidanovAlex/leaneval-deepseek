import Mathlib
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness

namespace Commons.Analysis.Complex.ChartedSpace

open Filter Metric Set
open scoped Topology

/-- **Rigidity lemma, open-set version.**  Let `X` be a `ℂ`-charted space, `U ⊆ X`, and
`F : ℕ → X → ℂ` a family which in the preferred chart at each point of `U` is analytic at the image
of that point.  If, for one point `x` and one `u` in the target of `chartAt ℂ x` with
`p := (chartAt ℂ x).symm u ∈ U`, the function `F n₀ ∘ (chartAt ℂ x).symm` is analytic at `u` with
non-vanishing derivative (`u` is a regular point of that particular member of the family), then
**every** member of the family is analytic at `u` in that chart.

This is the `U`-local form of `analyticAt_comp_chart_symm_of_witness`: the hypothesis `hF` is only
needed at the single point `p = (chartAt ℂ x).symm u ∈ U`. -/
theorem analyticAt_comp_chart_symm_of_witness_of_isOpen {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {U : Set X} {F : ℕ → X → ℂ}
    (hF : ∀ n, ∀ x ∈ U, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    {x : X} {u : ℂ} (hu : u ∈ (chartAt ℂ x).target) (hxu : (chartAt ℂ x).symm u ∈ U) {n₀ : ℕ}
    (hw : AnalyticAt ℂ (F n₀ ∘ (chartAt ℂ x).symm) u)
    (hwd : deriv (F n₀ ∘ (chartAt ℂ x).symm) u ≠ 0) :
    ∀ m, AnalyticAt ℂ (F m ∘ (chartAt ℂ x).symm) u := by
  intro m
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let p : X := e.symm u
  let f : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := f p
  let Tinv : ℂ → ℂ := fun z => e (f.symm z)
  let T : ℂ → ℂ := fun z => f (e.symm z)
  have hp : p ∈ e.source := e.map_target hu
  have hpu : e p = u := e.right_inv hu
  have hpU : p ∈ U := hxu
  have hpf : p ∈ f.source := mem_chart_source ℂ p
  have hc : c ∈ f.target := f.map_source hpf
  have hfs_c : f.symm c = p := f.left_inv hpf
  have hTinv_c : Tinv c = u := by
    show e (f.symm (f p)) = u
    rw [f.left_inv hpf, hpu]
  have hT_u : T u = c := rfl
  have hTinv_cont : ContinuousAt Tinv c := by
    have h1 : ContinuousAt f.symm c := f.continuousAt_symm hc
    have h2 : ContinuousAt e (f.symm c) := e.continuousAt (hfs_c ▸ hp)
    exact h2.comp h1
  have hT_cont : ContinuousAt T u := by
    have h1 : ContinuousAt e.symm u := e.continuousAt_symm hu
    have h2 : ContinuousAt f (e.symm u) := f.continuousAt hpf
    exact h2.comp h1
  -- Step 1: `Tinv` is analytic at `c`.
  have heq1 : (F n₀ ∘ f.symm) =ᶠ[𝓝 c] ((F n₀ ∘ e.symm) ∘ Tinv) := by
    have hmem : ∀ᶠ z in 𝓝 c, f.symm z ∈ e.source :=
      (f.continuousAt_symm hc).eventually (e.open_source.mem_nhds (hfs_c.symm ▸ hp))
    filter_upwards [hmem] with z hz
    simp only [Function.comp_apply, Tinv]
    rw [e.left_inv hz]
  have hcomp1 : AnalyticAt ℂ ((F n₀ ∘ e.symm) ∘ Tinv) c := (hF n₀ p hpU).congr heq1
  have hTinv_ana : AnalyticAt ℂ Tinv c :=
    analyticAt_of_comp_of_deriv_ne_zero hw hwd hTinv_cont hTinv_c hcomp1
  -- Step 2: `deriv Tinv c ≠ 0` via injectivity on a small ball.
  obtain ⟨r1, hr1pos, hr1⟩ := Metric.isOpen_iff.mp f.open_target c hc
  have hnhds : f.symm ⁻¹' e.source ∈ 𝓝 c :=
    (f.continuousAt_symm hc).preimage_mem_nhds (e.open_source.mem_nhds (hfs_c.symm ▸ hp))
  obtain ⟨r2, hr2pos, hr2⟩ := Metric.mem_nhds_iff.mp hnhds
  have hrpos : 0 < min r1 r2 := lt_min hr1pos hr2pos
  have hinj : Set.InjOn Tinv (Metric.ball c (min r1 r2)) := by
    intro z hz w hw hzw
    have hzd : dist z c < min r1 r2 := Metric.mem_ball.mp hz
    have hwd' : dist w c < min r1 r2 := Metric.mem_ball.mp hw
    have hz1 : z ∈ Metric.ball c r1 := Metric.mem_ball.mpr (lt_of_lt_of_le hzd (min_le_left _ _))
    have hw1 : w ∈ Metric.ball c r1 := Metric.mem_ball.mpr (lt_of_lt_of_le hwd' (min_le_left _ _))
    have hz2 : z ∈ Metric.ball c r2 := Metric.mem_ball.mpr (lt_of_lt_of_le hzd (min_le_right _ _))
    have hw2 : w ∈ Metric.ball c r2 := Metric.mem_ball.mpr (lt_of_lt_of_le hwd' (min_le_right _ _))
    have hzt : z ∈ f.target := hr1 hz1
    have hwt : w ∈ f.target := hr1 hw1
    have hzsrc : f.symm z ∈ e.source := hr2 hz2
    have hwsrc : f.symm w ∈ e.source := hr2 hw2
    have h1 : e (f.symm z) = e (f.symm w) := hzw
    have h2 : f.symm z = f.symm w := by
      have hh := congrArg e.symm h1
      rwa [e.left_inv hzsrc, e.left_inv hwsrc] at hh
    calc z = f (f.symm z) := (f.right_inv hzt).symm
      _ = f (f.symm w) := by rw [h2]
      _ = w := f.right_inv hwt
  have hderiv : deriv Tinv c ≠ 0 :=
    Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hrpos hTinv_ana hinj
  -- Step 3: `T` is analytic at `u`.
  have heq2 : (Tinv ∘ T) =ᶠ[𝓝 u] id := by
    have hmem1 : ∀ᶠ z in 𝓝 u, z ∈ e.target := e.open_target.mem_nhds hu
    have hmem2 : ∀ᶠ z in 𝓝 u, e.symm z ∈ f.source :=
      (e.continuousAt_symm hu).eventually (f.open_source.mem_nhds hpf)
    filter_upwards [hmem1, hmem2] with z hz1 hz2
    simp only [Function.comp_apply, Tinv, T, id_eq]
    rw [f.left_inv hz2, e.right_inv hz1]
  have hcomp2 : AnalyticAt ℂ (Tinv ∘ T) u := analyticAt_id.congr heq2.symm
  have hT_ana : AnalyticAt ℂ T u :=
    analyticAt_of_comp_of_deriv_ne_zero hTinv_ana hderiv hT_cont hT_u hcomp2
  -- Step 4: transfer analyticity back to `F m ∘ e.symm`.
  have hFm : AnalyticAt ℂ (F m ∘ f.symm) (T u) := by
    rw [hT_u]; exact hF m p hpU
  have hcompm : AnalyticAt ℂ ((F m ∘ f.symm) ∘ T) u := hFm.comp hT_ana
  have heqm : (F m ∘ e.symm) =ᶠ[𝓝 u] ((F m ∘ f.symm) ∘ T) := by
    have hmem2 : ∀ᶠ z in 𝓝 u, e.symm z ∈ f.source :=
      (e.continuousAt_symm hu).eventually (f.open_source.mem_nhds hpf)
    filter_upwards [hmem2] with z hz
    simp only [Function.comp_apply, T]
    rw [f.left_inv hz]
  exact hcompm.congr heqm.symm

end Commons.Analysis.Complex.ChartedSpace
