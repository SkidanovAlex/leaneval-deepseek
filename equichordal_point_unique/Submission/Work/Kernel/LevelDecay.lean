import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.RiemannSurface
import Submission.Work.Analysis.RiemannSurface.chartBall_open

/-!
# The uniform decay of one Green function on the level regions of another

`Work.Kernel.sup_lt_of_level_lt`: for two Green functions `gA` (pole `a`) and `gB` (pole `b`) of
`Ω`, every `ε > 0` admits `δ > 0` with `gB x < ε` for all `x ∈ Ω ∖ {a, b}` such that `gA x ≤ δ`.

This is the elementary half of the "the outer boundary term vanishes" step in the classical proof of
the symmetry `gA b = gB a`: the level curves `{gA = δ}` (for small `δ`) lie in the region where `gB`
is uniformly small.

Proof: `{gB ≥ ε}` is contained in a compact `K ⊆ Ω` (level completeness of `gB`); `gA > 1` on a chart
ball `D ∋ a` (logarithmic pole); the compact remainder `K ∖ D` misses the pole `a`, so `gA` has a
positive minimum `m` there; `δ := min (m/2) (1/2)` works.
-/

open Filter Set
open scoped Topology Manifold

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Uniform decay on the level regions.** -/
theorem sup_lt_of_level_lt {Ω : Set X} {a b : X} {gA gB : X → ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ω, x ≠ a → x ≠ b → gA x ≤ δ → gB x < ε := by
  classical
  obtain ⟨hposA, hharmA, -, hpoleA⟩ := hgA
  obtain ⟨K, hKc, hKΩ, hKlt⟩ := hgB.2.2.1 ε hε
  obtain ⟨C, V, hV, hVb⟩ := hpoleA
  -- a chart ball `D ∋ a`, contained in `V`, of chart radius `≤ exp (-(C+1))`
  obtain ⟨ρ, hρ0, hρV, hρexp⟩ : ∃ ρ : ℝ, 0 < ρ ∧
      Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) ρ ⊆ V ∧
      ρ ≤ Real.exp (-(C + 1)) := by
    obtain ⟨U, hUsub, hUopen, haU⟩ := mem_nhds_iff.mp hV
    have hmap : (chartAt ℂ a) a ∈ (chartAt ℂ a).target :=
      (chartAt ℂ a).map_source (mem_chart_source ℂ a)
    have hU' : (chartAt ℂ a).symm ⁻¹' U ∈ 𝓝 ((chartAt ℂ a) a) :=
      ((chartAt ℂ a).continuousAt_symm hmap).preimage_mem_nhds (by
        rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
        exact hUopen.mem_nhds haU)
    obtain ⟨r, hr0, hrsub⟩ := Metric.mem_nhds_iff.mp hU'
    refine ⟨min r (Real.exp (-(C + 1))) / 2, half_pos (lt_min hr0 (Real.exp_pos _)), ?_, ?_⟩
    · intro x hx
      obtain ⟨hxs, hxc⟩ := hx
      have h1 : (chartAt ℂ a) x ∈ Metric.ball ((chartAt ℂ a) a) r :=
        Metric.ball_subset_ball (by have h := min_le_left r (Real.exp (-(C + 1))); linarith) hxc
      have h2 : (chartAt ℂ a).symm ((chartAt ℂ a) x) ∈ U := hrsub h1
      rw [(chartAt ℂ a).left_inv hxs] at h2
      exact hUsub h2
    · have h1 : min r (Real.exp (-(C + 1))) ≤ Real.exp (-(C + 1)) :=
        min_le_right r _
      have h2 : 0 < Real.exp (-(C + 1)) := Real.exp_pos _
      linarith
  set D : Set X := Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) ρ with hDdef
  have hDopen : IsOpen D := Work.Analysis.RiemannSurface.isOpen_chartBall _ _ _
  have haD : a ∈ D := by
    refine ⟨mem_chart_source ℂ a, ?_⟩
    refine Metric.mem_ball.mpr ?_
    rw [dist_self]
    exact hρ0
  have hDge : ∀ x ∈ D, x ∈ Ω → x ≠ a → 1 ≤ gA x := by
    intro x hxD hxΩ hxa
    have hb := hVb x (hρV hxD) hxΩ hxa
    have hlt : ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ < Real.exp (-(C + 1)) := by
      have h1 : dist ((chartAt ℂ a) x) ((chartAt ℂ a) a) < ρ := Metric.mem_ball.mp hxD.2
      rw [dist_eq_norm] at h1
      exact lt_of_lt_of_le h1 hρexp
    have hne : (chartAt ℂ a) x ≠ (chartAt ℂ a) a := by
      intro h
      refine hxa ?_
      have hxsrc : x ∈ (chartAt ℂ a).source := hxD.1
      have hasrc : a ∈ (chartAt ℂ a).source := mem_chart_source ℂ a
      calc x = (chartAt ℂ a).symm ((chartAt ℂ a) x) := ((chartAt ℂ a).left_inv hxsrc).symm
        _ = (chartAt ℂ a).symm ((chartAt ℂ a) a) := by rw [h]
        _ = a := (chartAt ℂ a).left_inv hasrc
    have hpos : 0 < ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hne
    have hlog : Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ < -(C + 1) := by
      calc Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖
            < Real.log (Real.exp (-(C + 1))) := Real.log_lt_log hpos hlt
        _ = -(C + 1) := Real.log_exp _
    have h1 : -C ≤ gA x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ := (abs_le.mp hb).1
    linarith
  -- the positive minimum of `gA` on the compact remainder
  obtain ⟨m, hmpos, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K \ D, m ≤ gA x := by
    rcases (K \ D).eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun x hx => absurd (by rwa [hemp] at hx) (Set.notMem_empty x)⟩
    · have hcont : ContinuousOn gA (K \ D) := fun x hx =>
        ((hharmA x ⟨hKΩ hx.1, fun h => hx.2 (h ▸ haD)⟩).continuousAt).continuousWithinAt
      obtain ⟨x₀, hx₀, hx₀min⟩ := (hKc.diff hDopen).exists_isMinOn hne hcont
      exact ⟨gA x₀, hposA x₀ (hKΩ hx₀.1) (fun h => hx₀.2 (h ▸ haD)), fun x hx => hx₀min hx⟩
  refine ⟨min (m / 2) (1 / 2), lt_min (half_pos hmpos) (by norm_num),
    fun x hxΩ hxa hxb hle => hKlt x hxΩ ?_⟩
  intro hxK
  by_cases hxD : x ∈ D
  · have := hDge x hxD hxΩ hxa
    have := (le_min_iff.mp hle).2
    linarith
  · have := hm x ⟨hxK, hxD⟩
    have := (le_min_iff.mp hle).1
    linarith

/-- **Uniform decay on the level regions, symmetric form.**  The roles of the two functions in
`sup_lt_of_level_lt` are interchanged: on the small superlevel set of `gB` the function `gA` is small.
This is the form used (together with the collar identity `∫_{f < t} |∇f|² = 2π t`) by the estimate
that closes the "outer gap" of the energy route. -/
theorem sup_lt_of_level_lt_symm {Ω : Set X} {a b : X} {gA gB : X → ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ω, x ≠ b → x ≠ a → gB x ≤ δ → gA x < ε :=
  sup_lt_of_level_lt hgB hgA hε


end Work.Kernel
