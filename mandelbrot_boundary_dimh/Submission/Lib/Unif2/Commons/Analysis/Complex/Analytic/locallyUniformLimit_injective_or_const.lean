import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst
import Submission.Lib.Unif2.Commons.Analysis.Complex.ChartedSpace.exists_chartBall_analyticAt
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_ne_zero
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_of_center_factor
import Submission.Lib.Unif2.Commons.Analysis.Complex.tendsto_circleIntegral_logDeriv_of_tendstoLocallyUniformlyOn
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero

namespace Commons.Analysis.Complex.Analytic

open Filter Metric Set
open scoped Topology

private lemma eventually_exists_preimage_in_nhds {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : ℕ → X → ℂ} {g : X → ℂ}
    (hf : ∀ n x, AnalyticAt ℂ (f n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hg : ∀ x, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hconv : TendstoLocallyUniformlyOn f g Filter.atTop Set.univ)
    (p : X) {U : Set X} (hUo : IsOpen U) (hpU : p ∈ U)
    (hnotloc : ¬ ∀ᶠ y in 𝓝 p, g y = g p) :
    ∀ᶠ n in Filter.atTop, ∃ y ∈ U, f n y = g p := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hpsrc : p ∈ e.source := mem_chart_source ℂ p
  have hctgt : c ∈ e.target := e.map_source hpsrc
  obtain ⟨ρf, hρf, hρftgt, hρfana⟩ :=
    Commons.Analysis.Complex.ChartedSpace.exists_chartBall_analyticAt hf p
  obtain ⟨ρg, hρg, hgana⟩ := (hg p).exists_ball_analyticOnNhd
  have hsc : e.symm c = p := by
    change e.symm (e p) = p
    exact e.left_inv hpsrc
  have hUne : e.symm ⁻¹' U ∈ 𝓝 c :=
    (e.continuousAt_symm hctgt).preimage_mem_nhds (hUo.mem_nhds (by rw [hsc]; exact hpU))
  obtain ⟨ρU, hρU, hρUsub⟩ := Metric.mem_nhds_iff.mp hUne
  let ρ : ℝ := min ρf (min ρg ρU)
  have hρpos : 0 < ρ := lt_min hρf (lt_min hρg hρU)
  have hρlef : ρ ≤ ρf := min_le_left _ _
  have hρleg' : ρ ≤ ρg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρleU : ρ ≤ ρU := le_trans (min_le_right _ _) (min_le_right _ _)
  set w : ℂ := g p with hw
  let H : ℂ → ℂ := fun z => (g ∘ e.symm) z - w
  have hHana : AnalyticAt ℂ H c := (hg p).sub analyticAt_const
  have hHc : H c = 0 := by
    change g (e.symm c) - w = 0
    rw [hsc]
    simp [w]
  have hHnc : ¬ Filter.Eventually (fun z => H z = 0) (nhds c) := by
    intro hh
    apply hnotloc
    have hh' : ∀ᶠ z in 𝓝 c, g (e.symm z) = g p := by
      filter_upwards [hh] with z hz
      have : g (e.symm z) - w = 0 := hz
      simpa [w] using sub_eq_zero.mp this
    have hh'' : ∀ᶠ y in 𝓝 p, g (e.symm (e y)) = g p :=
      (e.continuousAt hpsrc).eventually hh'
    filter_upwards [hh'', e.open_source.mem_nhds hpsrc] with y hy hysrc
    rwa [e.left_inv hysrc] at hy
  obtain ⟨R0, k, ψ, hR0pos, hR0lt, hk1, hψana, hψne, hfac⟩ :=
    Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero hρpos hHana hHc hHnc
  let R : ℝ := R0 / 2
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRR0 : R < R0 := by dsimp [R]; linarith
  have hRltρ : R < ρ := lt_trans hRR0 hR0lt
  have hR0leρ : R0 ≤ ρ := le_of_lt hR0lt
  have hHana_ball : ∀ z ∈ Metric.ball c R0, AnalyticAt ℂ H z := by
    intro z hz
    exact (hgana z (Metric.ball_subset_ball (le_trans hR0leρ hρleg') hz)).sub analyticAt_const
  have hψne_closed : ∀ z ∈ Metric.closedBall c R, ψ z ≠ 0 :=
    fun z hz => hψne z (Metric.closedBall_subset_ball hRR0 hz)
  have hIntegralH : (∮ z in C(c, R), logDeriv H z) = (2 * Real.pi * Complex.I) * (k : ℂ) :=
    Commons.Analysis.Complex.circleIntegral_logDeriv_eq_of_center_factor hRpos hRR0 hk1
      hHana_ball hψana hfac hψne_closed
  have hne_val : (2 * Real.pi * Complex.I) * (k : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hk1)
  have hcont_symm : ContinuousOn e.symm (Metric.ball c ρ) :=
    e.continuousOn_symm.mono (fun z hz => hρftgt (Metric.ball_subset_ball hρlef hz))
  have hconv' : TendstoLocallyUniformlyOn (fun n => f n ∘ e.symm) (g ∘ e.symm) Filter.atTop
      (Metric.ball c ρ) :=
    hconv.comp e.symm (mapsTo_univ _ _) hcont_symm
  have hconstLU : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => w) (fun _ : ℂ => w)
      Filter.atTop (Metric.ball c ρ) :=
    (tendsto_const_nhds.tendstoUniformlyOn_const (Metric.ball c ρ)).tendstoLocallyUniformlyOn
  have hρconv : TendstoLocallyUniformlyOn (fun n z => f n (e.symm z) - w)
      H Filter.atTop (Metric.ball c ρ) :=
    hconv'.sub hconstLU
  have hFana : ∀ n, ∀ z ∈ Metric.ball c ρ, AnalyticAt ℂ (fun z => f n (e.symm z) - w) z := by
    intro n z hz
    exact (hρfana n z (Metric.ball_subset_ball hρlef hz)).sub analyticAt_const
  have hHana2 : ∀ z ∈ Metric.ball c ρ, AnalyticAt ℂ H z := by
    intro z hz
    exact (hgana z (Metric.ball_subset_ball hρleg' hz)).sub analyticAt_const
  have hsphere_sub : Metric.sphere c R ⊆ Metric.ball c R0 := fun z hz => by
    rw [Metric.mem_ball, Metric.mem_sphere.mp hz]; exact hRR0
  have hne_sphere : ∀ z ∈ Metric.sphere c R, H z ≠ 0 := by
    intro z hz
    have hz0 : z ∈ Metric.ball c R0 := hsphere_sub hz
    rw [hfac z hz0]
    refine mul_ne_zero (pow_ne_zero k ?_) (hψne z hz0)
    exact sub_ne_zero.mpr (by rw [← dist_pos, Metric.mem_sphere.mp hz]; exact hRpos)
  have htend := Commons.Analysis.Complex.tendsto_circleIntegral_logDeriv_of_tendstoLocallyUniformlyOn
    hRpos hRltρ hFana hHana2 hne_sphere hρconv
  rw [hIntegralH] at htend
  have hA : ∀ᶠ n in Filter.atTop,
      (∮ z in C(c, R), logDeriv (fun z => f n (e.symm z) - w) z) ≠ 0 :=
    htend.eventually ((isOpen_ne (x := (0 : ℂ))).mem_nhds hne_val)
  have hsubρ : Metric.sphere c R ⊆ Metric.ball c ρ := fun z hz => by
    rw [Metric.mem_ball, Metric.mem_sphere.mp hz]; exact hRltρ
  have hUnif : TendstoUniformlyOn (fun n z => f n (e.symm z) - w) H Filter.atTop
      (Metric.sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mp hρconv
      (Metric.sphere c R) hsubρ (isCompact_sphere c R)
  have hHcont : ContinuousOn H (Metric.sphere c R) :=
    ((hgana.continuousOn).mono (fun z hz => Metric.ball_subset_ball hρleg' (hsubρ hz))).sub
      continuousOn_const
  have hsphere_ne : (Metric.sphere c R).Nonempty :=
    ⟨c + (R : ℂ), by
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]⟩
  obtain ⟨z0, hz0mem, hmin⟩ := (isCompact_sphere c R).exists_isMinOn hsphere_ne (f := fun z => ‖H z‖) hHcont.norm
  have hmpos : 0 < ‖H z0‖ := norm_pos_iff.mpr (hne_sphere z0 hz0mem)
  have hB : ∀ᶠ n in Filter.atTop, ∀ z ∈ Metric.sphere c R, (fun z => f n (e.symm z) - w) z ≠ 0 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUnif) ‖H z0‖ hmpos] with n hn
    intro z hz hzF
    have hlt := hn z hz
    simp only [hzF, dist_eq_norm, sub_zero] at hlt
    exact absurd hlt (not_lt.mpr (hmin hz))
  have hC : ∀ᶠ n in Filter.atTop,
      ∃ z ∈ Metric.ball c R, (fun z => f n (e.symm z) - w) z = 0 := by
    filter_upwards [hA, hB] with n hAn hBn
    by_contra hz
    push Not at hz
    have hclosed : ∀ z ∈ Metric.closedBall c R, (fun z => f n (e.symm z) - w) z ≠ 0 := by
      intro z hzcl
      rcases (Metric.mem_closedBall.mp hzcl).lt_or_eq with hlt | heq
      · exact hz z (Metric.mem_ball.mpr hlt)
      · exact hBn z (Metric.mem_sphere.mpr heq)
    exact hAn (Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_ne_zero hRpos
      (fun z hz' => hFana n z (Metric.closedBall_subset_ball hRltρ hz')) hclosed)
  exact hC.mono fun n ⟨z, hz, hz0⟩ => ⟨e.symm z,
    hρUsub (Metric.ball_subset_ball (le_of_lt (lt_of_lt_of_le hRltρ hρleU)) hz), by
      have : f n (e.symm z) - w = 0 := hz0
      simpa [w] using sub_eq_zero.mp this⟩

theorem locallyUniformLimit_injective_or_const {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] {f : ℕ → X → ℂ} {g : X → ℂ}
    (hf : ∀ n x, AnalyticAt ℂ (f n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hg : ∀ x, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hconv : TendstoLocallyUniformlyOn f g Filter.atTop Set.univ)
    (hinj : ∀ n, Function.Injective (f n)) :
    Function.Injective g ∨ ∃ c : ℂ, ∀ x, g x = c := by
  by_cases hconst : ∃ c : ℂ, ∀ x, g x = c
  · exact Or.inr hconst
  · left
    have hloc : ∀ x, ¬ ∀ᶠ y in 𝓝 x, g y = g x := by
      intro x hx
      apply hconst
      set S : Set X := {y : X | ∀ᶠ z in 𝓝 y, g z = g y} with hSdef
      have hSc : IsClopen S := by
        rw [hSdef]
        exact Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst hg
      have hxS : x ∈ S := by rw [hSdef]; exact hx
      have huniv : S = Set.univ := by
        rcases (isClopen_iff.mp hSc) with h | h
        · exfalso
          rw [h] at hxS
          exact hxS
        · exact h
      have hLC : IsLocallyConstant g := (IsLocallyConstant.iff_eventually_eq g).mpr fun y => by
        have hyS : y ∈ S := by rw [huniv]; exact Set.mem_univ y
        rw [hSdef] at hyS
        exact hyS
      exact ⟨g x, fun y => (hLC.apply_eq_of_preconnectedSpace x y).symm⟩
    intro a b hab
    by_contra hne
    obtain ⟨U, V, hUo, hVo, haU, hbV, hUV⟩ := t2_separation hne
    have h1 := eventually_exists_preimage_in_nhds hf hg hconv a hUo haU (hloc a)
    have h2 := eventually_exists_preimage_in_nhds hf hg hconv b hVo hbV (hloc b)
    obtain ⟨n, ⟨ya, hyaU, hya⟩, ⟨yb, hybV, hyb⟩⟩ := (h1.and h2).exists
    have hne' : ya ≠ yb := by
      intro h
      have : ya ∈ U ∩ V := ⟨hyaU, h ▸ hybV⟩
      rw [Set.disjoint_iff_inter_eq_empty.mp hUV] at this
      exact this
    exact hne' (hinj n (hya.trans (hab.trans hyb.symm)))

end Commons.Analysis.Complex.Analytic
