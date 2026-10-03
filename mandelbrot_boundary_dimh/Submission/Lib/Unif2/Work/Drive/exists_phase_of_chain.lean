import Mathlib
import Submission.Lib.Unif2.Work.Drive.phaseChainDefs
import Submission.Lib.Unif2.Work.Drive.tendsto_gPhi_at_pivot
import Submission.Lib.Unif2.Work.Drive.tendsto_gPhi_mul_star_phase

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

theorem exists_radialFactor (z₀ : X) :
    ∃ m : X → ℝ, Continuous m ∧ m z₀ = 0 ∧ (∀ x : X, x ≠ z₀ → 0 < m x) ∧
      ∀ᶠ x in 𝓝 z₀, m x = ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ := by
  classical
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (chart_target_mem_nhds ℂ z₀)
  set r : ℝ := ε / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrlt : r < ε := by rw [hrdef]; linarith
  set A : Set X := (chartAt ℂ z₀).symm '' Metric.closedBall ((chartAt ℂ z₀) z₀) r with hAdef
  have hAsub : A ⊆ (chartAt ℂ z₀).source := by
    rintro x ⟨w, hw, rfl⟩
    exact (chartAt ℂ z₀).map_target (hεsub (Metric.closedBall_subset_ball hrlt hw))
  have hAcomp : IsCompact A := by
    rw [hAdef]
    exact IsCompact.image_of_continuousOn (isCompact_closedBall _ _)
      ((chartAt ℂ z₀).continuousOn_symm.mono
        (fun w hw => hεsub (Metric.closedBall_subset_ball hrlt hw)))
  have hAclosed : IsClosed A := hAcomp.isClosed
  refine ⟨fun x => if x ∈ (chartAt ℂ z₀).source then
      min ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ r else r, ?_, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ (chartAt ℂ z₀).source
    · have hv : ContinuousAt (fun y : X => min ‖(chartAt ℂ z₀) y - (chartAt ℂ z₀) z₀‖ r) x :=
        (((chartAt ℂ z₀).continuousAt hx).sub continuousAt_const).norm.min continuousAt_const
      refine hv.congr_of_eventuallyEq ?_
      filter_upwards [(chartAt ℂ z₀).open_source.mem_nhds hx] with y hy
      simp only [if_pos hy]
    · have hxnA : x ∉ A := fun hh => hx (hAsub hh)
      have hev : ∀ᶠ y in 𝓝 x, (if y ∈ (chartAt ℂ z₀).source then
          min ‖(chartAt ℂ z₀) y - (chartAt ℂ z₀) z₀‖ r else r) = r := by
        filter_upwards [hAclosed.isOpen_compl.mem_nhds hxnA] with y hy
        by_cases hy' : y ∈ (chartAt ℂ z₀).source
        · rw [if_pos hy']
          have hynA : (chartAt ℂ z₀) y ∉ Metric.closedBall ((chartAt ℂ z₀) z₀) r :=
            fun hw => hy ⟨(chartAt ℂ z₀) y, hw, (chartAt ℂ z₀).left_inv hy'⟩
          rw [Metric.mem_closedBall, dist_eq_norm] at hynA
          exact min_eq_right (le_of_lt (not_le.mp hynA))
        · rw [if_neg hy']
      have hone : ContinuousAt (fun _ : X => r) x := continuousAt_const
      exact hone.congr_of_eventuallyEq hev
  · show (if z₀ ∈ (chartAt ℂ z₀).source then
      min ‖(chartAt ℂ z₀) z₀ - (chartAt ℂ z₀) z₀‖ r else r) = 0
    rw [if_pos (mem_chart_source ℂ z₀)]
    simp only [sub_self, norm_zero]
    exact min_eq_left (le_of_lt hrpos)
  · intro x hx
    show 0 < (if x ∈ (chartAt ℂ z₀).source then
      min ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ r else r)
    by_cases hxsrc : x ∈ (chartAt ℂ z₀).source
    · rw [if_pos hxsrc]
      have hdpos : 0 < ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ := by
        rw [norm_pos_iff]
        exact sub_ne_zero.mpr
          (fun h => hx ((chartAt ℂ z₀).injOn hxsrc (mem_chart_source ℂ z₀) h))
      exact lt_min hdpos hrpos
    · rw [if_neg hxsrc]
      exact hrpos
  · have hcont : ContinuousAt (fun y : X => ‖(chartAt ℂ z₀) y - (chartAt ℂ z₀) z₀‖) z₀ :=
      (((chartAt ℂ z₀).continuousAt (mem_chart_source ℂ z₀)).sub continuousAt_const).norm
    have hev : ∀ᶠ y in 𝓝 z₀, ‖(chartAt ℂ z₀) y - (chartAt ℂ z₀) z₀‖ < r :=
      hcont.tendsto.eventually (isOpen_Iio.mem_nhds (by simpa using hrpos))
    filter_upwards [(chartAt ℂ z₀).open_source.mem_nhds (mem_chart_source ℂ z₀), hev]
      with x hxsrc hxlt
    show (if x ∈ (chartAt ℂ z₀).source then
      min ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ r else r)
      = ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖
    rw [if_pos hxsrc, min_eq_left (le_of_lt hxlt)]

theorem exists_phase_of_chain {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (z₀ : X) (a : ℕ → X) (ρ : ℕ → ℝ)
    (ha0 : a 0 = z₀)
    (hρ : ∀ i : ℕ, 0 < ρ i)
    (hstep : ∀ i : ℕ, a (i + 1) ∈ {x : X | x ∈ (chartAt ℂ (a i)).source ∧
      (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (ρ i)})
    (hwell : ∀ i : ℕ, closure {x : X | x ∈ (chartAt ℂ (a i)).source ∧
      (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (8 * ρ i)}
        ⊆ (chartAt ℂ (a i)).source)
    (hlf : ∀ A : Set X, IsCompact A →
      {i : ℕ | (A ∩ {x : X | x ∈ (chartAt ℂ (a i)).source ∧
        (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (8 * ρ i)}).Nonempty}.Finite)
    (hinj : Function.Injective a) :
    ∃ Θ : X → ℂ, Continuous Θ ∧ (∀ x : X, x ≠ z₀ → Θ x ≠ 0) ∧
      ∃ (u : X → ℂ) (V : Set X), V ∈ nhds z₀ ∧ ContinuousOn u V ∧ (∀ x ∈ V, u x ≠ 0) ∧
        ∀ x ∈ V, Θ x = ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀) * u x := by
  classical
  haveI : Nonempty X := ⟨z₀⟩
  haveI : Nontrivial X := ⟨a 0, a 1, fun h => Nat.zero_ne_one (hinj h)⟩
  haveI : PerfectSpace X := inferInstance
  obtain ⟨m, hmcont, hmz0, hmpos, hmnear⟩ := exists_radialFactor (X := X) z₀
  have hmcontC : Continuous (fun x : X => (m x : ℂ)) := Complex.continuous_ofReal.comp hmcont
  set Ψ : X → ℂ := fun x => (m x : ℂ) * gPhi a ρ x with hΨdef
  -- the limit of `Ψ` at the base point is zero
  have hΨz0 : Tendsto Ψ (𝓝[≠] z₀) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hm0 : Tendsto (fun x : X => m x) (𝓝[≠] z₀) (𝓝 0) := by
      have h := hmcont.tendsto z₀
      rw [hmz0] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨W, hWmem, hWsub⟩ := exists_nhds_inter_range_subset_singleton hρ hlf z₀
    refine Tendsto.congr' ?_ hm0
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds hWmem]
      with x hxne hxW
    have hxr : x ∉ Set.range a := fun hyr => hxne (by simpa using hWsub ⟨hxW, hyr⟩)
    have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
    rw [hΨdef]
    simp only [norm_mul, norm_ofReal_complex,
      norm_gPhi_eq_one_of_notMem_range hρ hstep hlf hxnot, mul_one]
    exact (abs_of_nonneg (le_of_lt (hmpos x hxne))).symm
  -- the limit of `Ψ` at every pivot
  have hlimAt : ∀ p : X, p ∈ Set.range a → ∃ L : ℂ, Tendsto Ψ (𝓝[≠] p) (𝓝 L) := by
    intro p hp
    obtain ⟨j, rfl⟩ := hp
    rcases Nat.eq_zero_or_pos j with hj0 | hj
    · subst hj0
      rw [ha0]
      exact ⟨0, hΨz0⟩
    · obtain ⟨c, hcne, hc⟩ := tendsto_gPhi_at_pivot (a := a) (ρ := ρ) hρ hinj hstep hwell hlf hj
      refine ⟨(m (a j) : ℂ) * c, ?_⟩
      have hm : Tendsto (fun x : X => (m x : ℂ)) (𝓝[≠] (a j)) (𝓝 ((m (a j) : ℂ))) :=
        (hmcontC.tendsto (a j)).mono_left nhdsWithin_le_nhds
      simpa only [hΨdef] using hm.mul hc
  -- the global phase
  set Θ : X → ℂ := fun x => if h : x ∈ Set.range a then limUnder (𝓝[≠] x) Ψ else Ψ x with hΘdef
  have hΘpos : ∀ p : X, (hp : p ∈ Set.range a) → Θ p = limUnder (𝓝[≠] p) Ψ := by
    intro p hp
    change dite (p ∈ Set.range a) (fun _ => limUnder (𝓝[≠] p) Ψ) (fun _ => Ψ p) =
      limUnder (𝓝[≠] p) Ψ
    exact dif_pos hp
  have hΘneg : ∀ p : X, (hp : p ∉ Set.range a) → Θ p = Ψ p := by
    intro p hp
    change dite (p ∈ Set.range a) (fun _ => limUnder (𝓝[≠] p) Ψ) (fun _ => Ψ p) = Ψ p
    exact dif_neg hp
  have hΘcont : Continuous Θ := by
    rw [continuous_iff_continuousAt]
    intro p
    obtain ⟨W, hWmem, hWsub⟩ := exists_nhds_inter_range_subset_singleton hρ hlf p
    have hWrange : ∀ y ∈ W, y ∈ Set.range a → y = p := fun y hy hyr => hWsub ⟨hy, hyr⟩
    by_cases hp : p ∈ Set.range a
    · obtain ⟨L, hL⟩ := hlimAt p hp
      have hΘp : Θ p = L := (hΘpos p hp).trans hL.limUnder_eq
      have heq : Θ =ᶠ[𝓝 p] fun y : X => if y = p then L else Ψ y := by
        filter_upwards [hWmem] with y hy
        by_cases hyp : y = p
        · have hyr : y ∈ Set.range a := by rw [hyp]; exact hp
          have h1 : Θ y = limUnder (𝓝[≠] p) Ψ := by rw [hΘpos y hyr, hyp]
          have h2 : limUnder (𝓝[≠] p) Ψ = L := (hΘpos p hp).symm.trans hΘp
          rw [h1, h2, hyp, if_pos rfl]
        · have hyr : y ∉ Set.range a := fun hh => hyp (hWrange y hy hh)
          rw [hΘneg y hyr, if_neg hyp]
      exact (continuousAt_ite_of_tendsto_nhdsNE hL).congr_of_eventuallyEq heq
    · have hΘeq : Θ =ᶠ[𝓝 p] Ψ := by
        filter_upwards [hWmem] with y hy
        have hyr : y ∉ Set.range a := by
          intro hh
          exact hp (by rw [← hWrange y hy hh]; exact hh)
        rw [hΘneg y hyr]
      have hΨcont : ContinuousAt Ψ p := by
        rw [hΨdef]
        exact (hmcontC.continuousAt).mul
          (continuousAt_gPhi_of_notMem_range hρ hstep hwell hlf
            (fun i hi => hp ⟨i, hi.symm⟩))
      exact hΨcont.congr_of_eventuallyEq hΘeq
  have hΘne : ∀ x : X, x ≠ z₀ → Θ x ≠ 0 := by
    intro x hx
    by_cases hxr : x ∈ Set.range a
    · obtain ⟨j, rfl⟩ := hxr
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · exact absurd (show a j = z₀ by rw [h]; exact ha0) hx
        · exact h
      obtain ⟨c, hcne, hc⟩ := tendsto_gPhi_at_pivot (a := a) (ρ := ρ) hρ hinj hstep hwell hlf hj
      have hΨlim : Tendsto Ψ (𝓝[≠] (a j)) (𝓝 ((m (a j) : ℂ) * c)) := by
        have hm : Tendsto (fun x : X => (m x : ℂ)) (𝓝[≠] (a j)) (𝓝 ((m (a j) : ℂ))) :=
          (hmcontC.tendsto (a j)).mono_left nhdsWithin_le_nhds
        simpa only [hΨdef] using hm.mul hc
      have hval : Θ (a j) = (m (a j) : ℂ) * c :=
        (hΘpos (a j) ⟨j, rfl⟩).trans hΨlim.limUnder_eq
      rw [hval]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hmpos (a j) hx))) hcne
    · have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
      rw [hΘneg x hxr, hΨdef]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hmpos x hx)))
        (gPhi_ne_zero_of_notMem_range hρ hstep hlf hxnot)
  -- the local description at the base point
  obtain ⟨u₀, hu₀ne, hu₀⟩ := tendsto_gPhi_mul_star_phase (a := a) (ρ := ρ)
    ha0 hρ hinj hstep hwell hlf
  set d : X → ℂ := fun x => (chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀ with hddef
  obtain ⟨W₀, hW₀mem, hW₀sub⟩ := exists_nhds_inter_range_subset_singleton hρ hlf z₀
  have hW₀range : ∀ y ∈ W₀, y ∈ Set.range a → y = z₀ := fun y hy hyr => hW₀sub ⟨hy, hyr⟩
  set V : Set X := W₀ ∩ (chartAt ℂ z₀).source ∩ {x : X | m x = ‖d x‖} with hVdef
  set u : X → ℂ := fun x => if x = z₀ then u₀ else gPhi a ρ x * star (phase (d x)) with hudef
  have hVmem : V ∈ 𝓝 z₀ := by
    rw [hVdef]
    refine Filter.inter_mem (Filter.inter_mem hW₀mem ?_) ?_
    · exact (chartAt ℂ z₀).open_source.mem_nhds (mem_chart_source ℂ z₀)
    · filter_upwards [hmnear] with x hx
      simpa only [hddef] using hx
  have hVsub : ∀ x ∈ V, x ∈ W₀ ∧ x ∈ (chartAt ℂ z₀).source ∧ m x = ‖d x‖ := by
    intro x hx
    rw [hVdef] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  have hcont_u : ContinuousOn u V := by
    intro x hxV
    obtain ⟨hxW₀, hxsrc, hxmd⟩ := hVsub x hxV
    by_cases hxz : x = z₀
    · subst hxz
      exact (continuousAt_ite_of_tendsto_nhdsNE hu₀).continuousWithinAt
    · have hxr : x ∉ Set.range a := fun hh => hxz (hW₀range x hxW₀ hh)
      have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
      have hcd : ContinuousAt d x := by
        rw [hddef]
        exact ((chartAt ℂ z₀).continuousAt hxsrc).sub continuousAt_const
      have hdx_ne : d x ≠ 0 := by
        rw [hddef]
        exact sub_ne_zero.mpr (fun h => hxz ((chartAt ℂ z₀).injOn hxsrc
          (mem_chart_source ℂ z₀) h))
      have hcontΦ : ContinuousAt (gPhi a ρ) x :=
        continuousAt_gPhi_of_notMem_range hρ hstep hwell hlf hxnot
      have hcontphase : ContinuousAt (fun y : X => star (phase (d y))) x :=
        continuous_star.continuousAt.comp ((continuousAt_phase hdx_ne).comp hcd)
      refine ((hcontΦ.mul hcontphase).congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [eventually_ne_nhds hxz] with y hy
      rw [hudef]
      simp only [if_neg hy, Pi.mul_apply]
  have hne_u : ∀ x ∈ V, u x ≠ 0 := by
    intro x hxV
    obtain ⟨hxW₀, hxsrc, hxmd⟩ := hVsub x hxV
    by_cases hxz : x = z₀
    · simp only [hudef, if_pos hxz]
      exact hu₀ne
    · have hxr : x ∉ Set.range a := fun hh => hxz (hW₀range x hxW₀ hh)
      have hxnot : ∀ i : ℕ, x ≠ a i := fun i hi => hxr ⟨i, hi.symm⟩
      simp only [hudef, if_neg hxz]
      refine mul_ne_zero (gPhi_ne_zero_of_notMem_range hρ hstep hlf hxnot) ?_
      intro h
      have hdx_ne : d x ≠ 0 := by
        rw [hddef]
        exact sub_ne_zero.mpr (fun hh => hxz ((chartAt ℂ z₀).injOn hxsrc
          (mem_chart_source ℂ z₀) hh))
      refine phase_ne_zero hdx_ne ?_
      have := congrArg star h
      simpa using this
  have hform : ∀ x ∈ V, Θ x = d x * u x := by
    intro x hxV
    obtain ⟨hxW₀, hxsrc, hxmd⟩ := hVsub x hxV
    by_cases hxz : x = z₀
    · have hΘz : Θ z₀ = 0 := (hΘpos z₀ ⟨0, ha0⟩).trans hΨz0.limUnder_eq
      rw [hxz, hΘz, hudef, hddef]
      simp
    · have hxr : x ∉ Set.range a := fun hh => hxz (hW₀range x hxW₀ hh)
      have hΘx : Θ x = Ψ x := hΘneg x hxr
      rw [hΘx, hΨdef, hudef]
      simp only [if_neg hxz]
      rw [hxmd, ← mul_star_phase (d x)]
      ring
  exact ⟨Θ, hΘcont, hΘne, u, V, hVmem, hcont_u, hne_u, hform⟩

end Work.Drive
