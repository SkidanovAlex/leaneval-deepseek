import Mathlib
import Submission.Lib.Unif2.Work.Kernel.greenCoverPairingAux
import Submission.Lib.Unif2.Work.Kernel.GreenCover
import Submission.Lib.Unif2.Work.Drive.chartPoleIdentity
import Submission.Lib.Unif2.Work.Drive.tendsto_chart_transition_slope
import Submission.Lib.Unif2.Work.Drive.deriv_chart_transition_ne_zero
import Submission.Lib.Unif2.Work.Potential.removable_singularity_bounded_harmonic

/-!
# Growth bound for the pairing integrand at a pole

This file proves `Work.Kernel.growth_bound_pole`: for a chart of the cover whose source contains the
pole `c` of a Green function `gC` of `Ω`, the chartwise pairing integrand

`z ↦ inner (∇ (gC ∘ c.symm)) (∇ (Φ ∘ c.symm)) z`

is continuous off the pole `(chartAt ℂ y) c` inside the `σ`-ball and grows at most like the inverse
distance to that pole.

The analytic content is that the *correction* `gC ∘ c.symm + log ‖· - (chartAt ℂ y) c‖` is
harmonic across the pole in *any* chart through the pole (the logarithmic singularity has
coefficient one in every chart, since chart transitions have non-vanishing derivative), which is the
logarithmic expansion hypothesis of `Work.Drive.exists_norm_gradient_le_of_logExpansion`.
-/

open Set Metric MeasureTheory Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The logarithmic singular part transfers between charts.**  If `c` lies in the source of the
chart at `y`, then near `c` the two coordinate distances `‖y-coordinate - y-coordinate of c‖` and
`‖c-coordinate - c-coordinate of c‖` differ by a bounded factor, so their logarithms differ by a
bounded amount.  This is the statement that chart transitions have non-vanishing derivative, read
as a bound rather than as a limit. -/
theorem exists_log_dist_bound {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {c y : X}
    (hy : c ∈ (chartAt ℂ y).source) :
    ∃ U : Set X, U ∈ 𝓝 c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ U, x ∈ (chartAt ℂ c).source → x ∈ (chartAt ℂ y).source → x ≠ c →
        |Real.log ‖(chartAt ℂ y) x - (chartAt ℂ y) c‖
          - Real.log ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖| ≤ K := by
  have htel := Work.Drive.tendsto_chart_transition_slope (x := y) (y := c) hy
  have hAne : deriv ((chartAt ℂ y).symm.trans (chartAt ℂ c)) ((chartAt ℂ y) c) ≠ 0 :=
    Work.Drive.deriv_chart_transition_ne_zero (x := y) (y := c) hy
  set A : ℂ := deriv ((chartAt ℂ y).symm.trans (chartAt ℂ c)) ((chartAt ℂ y) c) with hA
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hAne
  set ρ : X → ℂ := fun z => ((chartAt ℂ c) z - (chartAt ℂ c) c) /
    ((chartAt ℂ y) z - (chartAt ℂ y) c) with hρdef
  have hev1 : ∀ᶠ z in 𝓝[≠] c, ‖ρ z - A‖ < ‖A‖ / 2 := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp htel) (‖A‖ / 2) (by positivity)
  have hev2 : ∀ᶠ z in 𝓝[≠] c, (‖A‖ / 2 ≤ ‖ρ z‖ ∧ ‖ρ z‖ ≤ 2 * ‖A‖) := by
    filter_upwards [hev1] with z hz
    have h1 : ‖ρ z - A‖ < ‖A‖ / 2 := hz
    constructor
    · have h2 : ‖A‖ ≤ ‖ρ z‖ + ‖ρ z - A‖ := by
        calc ‖A‖ = ‖ρ z - (ρ z - A)‖ := by ring_nf
          _ ≤ ‖ρ z‖ + ‖ρ z - A‖ := norm_sub_le _ _
      linarith
    · have h4 := norm_add_le A (ρ z - A)
      rw [show A + (ρ z - A) = ρ z by ring] at h4
      linarith
  refine ⟨{z : X | z ∈ ({c}ᶜ : Set X) → (‖A‖ / 2 ≤ ‖ρ z‖ ∧ ‖ρ z‖ ≤ 2 * ‖A‖)},
    eventually_nhdsWithin_iff.mp hev2, max |Real.log (2 / ‖A‖)| |Real.log (1 / (2 * ‖A‖))|,
    le_trans (abs_nonneg _) (le_max_left _ _), ?_⟩
  intro x hxU hxsrc hysrc hxne
  have hP := hxU hxne
  have hbpos : 0 < ‖(chartAt ℂ y) x - (chartAt ℂ y) c‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun hcon => hxne ((chartAt ℂ y).injOn hysrc hy hcon)
  have hapos : 0 < ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun hcon => hxne ((chartAt ℂ c).injOn hxsrc (mem_chart_source ℂ c) hcon)
  have hratio : ‖ρ x‖ = ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖ /
      ‖(chartAt ℂ y) x - (chartAt ℂ y) c‖ := norm_div _ _
  set b : ℝ := ‖(chartAt ℂ y) x - (chartAt ℂ y) c‖ with hbdef
  set a : ℝ := ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖ with hadef
  have haeq : a = ‖ρ x‖ * b := by
    rw [hratio, div_mul_cancel₀ a hbpos.ne']
  have hlb : (‖A‖ / 2) * b ≤ a := by
    calc (‖A‖ / 2) * b ≤ ‖ρ x‖ * b := mul_le_mul_of_nonneg_right hP.1 (norm_nonneg _)
      _ = a := haeq.symm
  have hub : a ≤ (2 * ‖A‖) * b := by
    calc a = ‖ρ x‖ * b := haeq
      _ ≤ (2 * ‖A‖) * b := mul_le_mul_of_nonneg_right hP.2 (norm_nonneg _)
  have hb1 : b ≤ (2 / ‖A‖) * a := by
    have h2 := mul_le_mul_of_nonneg_left hlb (by positivity : (0:ℝ) ≤ 2 / ‖A‖)
    have h3 : (2 / ‖A‖) * ((‖A‖ / 2) * b) = b := by field_simp
    linarith [h2, h3.le, h3.ge]
  have hb2 : (1 / (2 * ‖A‖)) * a ≤ b := by
    have h2 := mul_le_mul_of_nonneg_left hub (by positivity : (0:ℝ) ≤ 1 / (2 * ‖A‖))
    have h3 : (1 / (2 * ‖A‖)) * ((2 * ‖A‖) * b) = b := by field_simp
    linarith [h2, h3.le, h3.ge]
  have hd1 : b / a ≤ 2 / ‖A‖ := (div_le_iff₀ hapos).mpr hb1
  have hd2 : 1 / (2 * ‖A‖) ≤ b / a := (le_div_iff₀ hapos).mpr hb2
  have hlogeq : Real.log b - Real.log a = Real.log (b / a) :=
    (Real.log_div hbpos.ne' hapos.ne').symm
  have hupp : Real.log (b / a) ≤ Real.log (2 / ‖A‖) := Real.log_le_log (by positivity) hd1
  have hlow : Real.log (1 / (2 * ‖A‖)) ≤ Real.log (b / a) := Real.log_le_log (by positivity) hd2
  rw [hlogeq]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h1 : -(|Real.log (1 / (2 * ‖A‖))|) ≤ Real.log (1 / (2 * ‖A‖)) := neg_abs_le _
    have h2 : -(max |Real.log (2 / ‖A‖)| |Real.log (1 / (2 * ‖A‖))|) ≤
        -(|Real.log (1 / (2 * ‖A‖))|) := neg_le_neg (le_max_right _ _)
    linarith
  · have h1 : Real.log (2 / ‖A‖) ≤ |Real.log (2 / ‖A‖)| := le_abs_self _
    have h2 : |Real.log (2 / ‖A‖)| ≤ max |Real.log (2 / ‖A‖)| |Real.log (1 / (2 * ‖A‖))| :=
      le_max_left _ _
    linarith

/-- **The logarithmic expansion of a Green function in an arbitrary chart through the pole.**  If
`gC` is a Green function of `Ω` with pole `c` and `c` lies in the source of the chart at `y`, then in
that chart `gC ∘ y.symm` differs from `-log ‖· - y c‖` by a function harmonic across the pole.  The
coefficient of the logarithm is one in *every* chart, because the transition has non-vanishing
derivative; the boundedness of the difference is `exists_log_dist_bound` and the harmonic extension
is the removable-singularity theorem. -/
theorem poleExpansion_chart_of_green {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {c y : X} {gC : X → ℝ}
    (hΩo : IsOpen Ω) (hcΩ : c ∈ Ω)
    (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    (hy : c ∈ (chartAt ℂ y).source) :
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℝ,
      Metric.ball ((chartAt ℂ y) c) r ⊆ (chartAt ℂ y).target ∧
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ y) c) r) ∧
      (∀ z ∈ Metric.ball ((chartAt ℂ y) c) r, z ≠ (chartAt ℂ y) c →
        gC ((chartAt ℂ y).symm z) = -Real.log ‖z - (chartAt ℂ y) c‖ + H z) := by
  obtain ⟨C, V, hVnhds, hVbound⟩ := hgC.2.2.2
  obtain ⟨U, hUnhds, K, hK, hUK⟩ := exists_log_dist_bound (c := c) (y := y) hy
  obtain ⟨V', hV'sub, hV'open, hcV'⟩ := mem_nhds_iff.mp hVnhds
  obtain ⟨U', hU'sub, hU'open, hcU'⟩ := mem_nhds_iff.mp hUnhds
  set W : Set X := V' ∩ U' ∩ Ω ∩ (chartAt ℂ c).source ∩ (chartAt ℂ y).source with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact (((hV'open.inter hU'open).inter hΩo).inter (chartAt ℂ c).open_source).inter
      (chartAt ℂ y).open_source
  have hcW : c ∈ W := by
    rw [hWdef]
    exact ⟨⟨⟨⟨hcV', hcU'⟩, hcΩ⟩, mem_chart_source ℂ c⟩, hy⟩
  have hWtgt : IsOpen ((chartAt ℂ y) '' W) :=
    (chartAt ℂ y).isOpen_image_of_subset_source hWopen inter_subset_right
  have hpim : (chartAt ℂ y) c ∈ (chartAt ℂ y) '' W := ⟨c, hcW, rfl⟩
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hWtgt _ hpim
  obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.mp (chartAt ℂ y).open_target _
    ((chartAt ℂ y).map_source hy)
  set p : ℂ := (chartAt ℂ y) c with hp
  set r : ℝ := min r₁ r₂ / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]; exact div_pos (lt_min hr₁ hr₂) two_pos
  have hr₁le : Metric.ball p r ⊆ Metric.ball p r₁ :=
    Metric.ball_subset_ball (by rw [hrdef]; linarith [min_le_left r₁ r₂])
  have hr₂le : Metric.ball p r ⊆ Metric.ball p r₂ :=
    Metric.ball_subset_ball (by rw [hrdef]; linarith [min_le_right r₁ r₂])
  have hdata : ∀ z : ℂ, z ∈ Metric.ball p r →
      ∃ x : X, x ∈ V' ∧ x ∈ U' ∧ x ∈ Ω ∧ x ∈ (chartAt ℂ c).source ∧
        x ∈ (chartAt ℂ y).source ∧ (chartAt ℂ y) x = z ∧ (chartAt ℂ y).symm z = x := by
    intro z hz
    obtain ⟨x, hxW, hxeq⟩ := hr₁sub (hr₁le hz)
    rw [hWdef] at hxW
    obtain ⟨⟨⟨⟨hxV', hxU'⟩, hxΩ⟩, hxcsrc⟩, hxysrc⟩ := hxW
    have hsymm : (chartAt ℂ y).symm z = x := by
      rw [← hxeq]; exact (chartAt ℂ y).left_inv hxysrc
    exact ⟨x, hxV', hxU', hxΩ, hxcsrc, hxysrc, hxeq, hsymm⟩
  have htgt : Metric.ball p r ⊆ (chartAt ℂ y).target := hr₂le.trans hr₂sub
  have hu_harm : ∀ z : ℂ, ‖z - p‖ < r → z ≠ p →
      InnerProductSpace.HarmonicAt (fun z : ℂ => gC ((chartAt ℂ y).symm z) + Real.log ‖z - p‖) z := by
    intro z hzr hzne
    have hzball : z ∈ Metric.ball p r := by rwa [Metric.mem_ball, dist_eq_norm]
    obtain ⟨x, hxV', hxU', hxΩ, hxcsrc, hxysrc, hxeq, hsymm⟩ := hdata z hzball
    have hxc : x ≠ c := by
      intro hcon
      exact hzne (by rw [← hxeq, hcon])
    have hharmX : Submission.HarmonicOnXAt gC x := hgC.2.1 x ⟨hxΩ, by simpa using hxc⟩
    have hharm : InnerProductSpace.HarmonicAt (fun z : ℂ => gC ((chartAt ℂ y).symm z)) z := by
      have h := (Submission.HarmonicOnXAt_iff_chart (u := gC) (x := x) (y := y) hxysrc).mp hharmX
      rw [hxeq] at h
      exact h
    have hlog : InnerProductSpace.HarmonicAt (fun z : ℂ => Real.log ‖z - p‖) z :=
      AnalyticAt.harmonicAt_log_norm (f := fun z : ℂ => z - p)
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzne)
    exact hharm.add hlog
  have hu_bdd : ∀ z : ℂ, ‖z - p‖ < r → z ≠ p →
      |gC ((chartAt ℂ y).symm z) + Real.log ‖z - p‖| ≤ C + K := by
    intro z hzr hzne
    have hzball : z ∈ Metric.ball p r := by rwa [Metric.mem_ball, dist_eq_norm]
    obtain ⟨x, hxV', hxU', hxΩ, hxcsrc, hxysrc, hxeq, hsymm⟩ := hdata z hzball
    have hxc : x ≠ c := by
      intro hcon
      exact hzne (by rw [← hxeq, hcon])
    have h1 : |gC x + Real.log ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖| ≤ C :=
      hVbound x (hV'sub hxV') hxΩ hxc
    have h2 : |Real.log ‖(chartAt ℂ y) x - (chartAt ℂ y) c‖
        - Real.log ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖| ≤ K :=
      hUK x (hU'sub hxU') hxcsrc hxysrc hxc
    have hzpx : ‖z - p‖ = ‖(chartAt ℂ y) x - (chartAt ℂ y) c‖ := by rw [← hxeq]
    rw [hsymm]
    calc |gC x + Real.log ‖z - p‖|
        = |(gC x + Real.log ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖)
            + (Real.log ‖z - p‖ - Real.log ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖)| := by
          ring_nf
      _ ≤ |gC x + Real.log ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖|
            + |Real.log ‖z - p‖ - Real.log ‖(chartAt ℂ c) x - (chartAt ℂ c) c‖| :=
          abs_add_le _ _
      _ ≤ C + K := add_le_add h1 (by rw [hzpx]; exact h2)
  obtain ⟨H, hHharm, hHeq⟩ := Work.Potential.removable_singularity_ball_center
    (u := fun z : ℂ => gC ((chartAt ℂ y).symm z) + Real.log ‖z - p‖) (a := p) (R := r)
    (M := C + K) hrpos hu_harm hu_bdd
  refine ⟨r / 2, by linarith, H, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (by linarith)).trans htgt
  · intro z hz
    exact hHharm z (by rwa [Metric.mem_ball, dist_eq_norm] at hz)
  · intro z hz hzne
    have hz' : ‖z - p‖ < r / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h := hHeq z hz' hzne
    linarith [h]

/-- **Continuity of the gradient of a chart pullback of a harmonic function off the pole.** -/
lemma continuousAt_gradient_chartPull_of_ne_pole {Ω : Set X} {c y : X} {gC : X → ℝ} {ρ : ℝ}
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (hharm : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x)
    {z : ℂ} (hzρ : z ∈ Metric.ball ((chartAt ℂ y) y) ρ)
    (hzc : (chartAt ℂ y).symm z ≠ c) :
    ContinuousAt (fun z : ℂ => gradient (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z) z := by
  have hzsrc : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
    (chartAt ℂ y).map_target (htgt hzρ)
  have hright : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z :=
    (chartAt ℂ y).right_inv (htgt hzρ)
  have hzΩ : (chartAt ℂ y).symm z ∈ Ω :=
    hΩ ⟨hzsrc, by rw [Set.mem_preimage, hright]; exact hzρ⟩
  have hharmz : InnerProductSpace.HarmonicAt (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z := by
    have h := (Submission.HarmonicOnXAt_iff_chart (u := gC) (x := (chartAt ℂ y).symm z)
      (y := y) hzsrc).mp (hharm _ hzΩ hzc)
    rwa [hright] at h
  have h1 : ContinuousAt
      (fun w : ℂ => fderiv ℝ (fun u : ℂ => gC ((chartAt ℂ y).symm u)) w) z :=
    hharmz.1.continuousAt_fderiv (by norm_num)
  have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => gC ((chartAt ℂ y).symm u)) w) z := by
    simpa only [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
  exact h2

/-- **The gradient of the chart pullback of a Green function blows up at most like the inverse
distance to the pole.**  Given the logarithmic expansion of `gC ∘ c.symm` around the pole
`(chartAt ℂ y) c` (which is supplied in an arbitrary chart by
`Work.Kernel.poleExpansion_chart`), the gradient is bounded by `C / ‖z - (chartAt ℂ y) c‖` on the
whole `σ`-ball: near the pole by the expansion, away from it by compactness. -/
theorem gradient_chartPull_le_invDist_of_pole {Ω : Set X} {c y : X} {gC : X → ℝ} {ρ σ : ℝ}
    (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (hharm : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x)
    (hexp : ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℝ,
      Metric.ball ((chartAt ℂ y) c) r ⊆ (chartAt ℂ y).target ∧
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ y) c) r) ∧
      (∀ z ∈ Metric.ball ((chartAt ℂ y) c) r, z ≠ (chartAt ℂ y) c →
        gC ((chartAt ℂ y).symm z) = -Real.log ‖z - (chartAt ℂ y) c‖ + H z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball ((chartAt ℂ y) y) σ, z ≠ (chartAt ℂ y) c →
      ‖gradient (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z‖ ≤ C / ‖z - (chartAt ℂ y) c‖ := by
  obtain ⟨r, hr, H, _hHtgt, hHharm, hexpeq⟩ := hexp
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.Drive.exists_norm_gradient_le_of_logExpansion
    (p := (chartAt ℂ y) c) (ρ := r) hr hHharm hexpeq
  set ctr : ℂ := (chartAt ℂ y) y with hctr
  set p : ℂ := (chartAt ℂ y) c with hp
  have hK : IsCompact (Metric.closedBall ctr σ \ Metric.ball p (r / 2)) := by
    rw [Set.sdiff_eq]
    exact (isCompact_closedBall ctr σ).inter_right Metric.isOpen_ball.isClosed_compl
  have hcont : ContinuousOn
      (fun z : ℂ => gradient (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z * (z - p))
      (Metric.closedBall ctr σ \ Metric.ball p (r / 2)) := by
    intro z hz
    obtain ⟨hzcl, hznot⟩ := hz
    have hzσ : ‖z - ctr‖ ≤ σ := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hzcl
    have hzρ : z ∈ Metric.ball ctr ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith
    have hzp : z ≠ p := by
      intro hcon
      exact hznot (by rw [hcon]; exact Metric.mem_ball_self (by linarith))
    have hzc : (chartAt ℂ y).symm z ≠ c := by
      intro hcon
      have hright : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z :=
        (chartAt ℂ y).right_inv (htgt hzρ)
      exact hzp (by rw [← hright, hcon])
    exact (((continuousAt_gradient_chartPull_of_ne_pole (ρ := ρ) htgt hΩ hharm hzρ hzc).mul
      (continuousAt_id.sub continuousAt_const))).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ (max C₂ 0) + 1, by positivity, fun z hz hzp => ?_⟩
  have hCp : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  by_cases hzr : z ∈ Metric.ball p (r / 2)
  · have h := hC₁ z hzr hzp
    rw [le_div_iff₀ hCp] at h
    rw [le_div_iff₀ hCp]
    exact le_trans h (le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one))
  · have hzK : z ∈ Metric.closedBall ctr σ \ Metric.ball p (r / 2) :=
      ⟨Metric.ball_subset_closedBall hz, hzr⟩
    have h := hC₂ z hzK
    have h2 : ‖gradient (fun w : ℂ => gC ((chartAt ℂ y).symm w)) z‖ * ‖z - p‖ ≤ C₂ := by
      rw [← norm_mul]; exact h
    rw [le_div_iff₀ hCp]
    refine le_trans h2 ?_
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one))


/-- **Growth bound for the pairing integrand in the pole chart.**  `Work.Kernel.growth_bound_pole`:
the chartwise pairing integrand of a Green function `gC` with pole `c` against a chartwise `C¹`
function `Φ` is continuous off the pole inside the `σ`-ball and is bounded by `C₂ / ‖z - pole‖`. -/
theorem growth_bound_pole {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω K : Set X} {a b c : X} {N : ℕ} (E : Work.Kernel.GreenCover (Fin N) Ω K a b)
    (i₀ : Fin N) (hΩo : IsOpen Ω) (hcΩ : c ∈ Ω) {gC : X → ℝ}
    (hgC : Work.SimplyConnected.ABS.IsGreenOn Ω c gC)
    (hi₀mem : c ∈ (chartAt ℂ (E.y i₀)).source)
    {Φ : X → ℝ} (hΦc1 : ∀ x ∈ (chartAt ℂ (E.y i₀)).source,
      ContDiffAt ℝ 1 (Φ ∘ (chartAt ℂ (E.y i₀)).symm) ((chartAt ℂ (E.y i₀)) x)) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ContinuousOn (fun z : ℂ => inner (𝕜 := ℝ)
        (gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i₀)).symm w)) z)
        (gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i₀)).symm w)) z))
        (Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.σ i₀)
          ∩ {(chartAt ℂ (E.y i₀)) c}ᶜ) ∧
      ∀ z ∈ Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.σ i₀),
        z ≠ (chartAt ℂ (E.y i₀)) c →
        ‖inner (𝕜 := ℝ) (gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i₀)).symm w)) z)
          (gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i₀)).symm w)) z)‖
          ≤ C₂ / ‖z - (chartAt ℂ (E.y i₀)) c‖ := by
  have hharmG : ∀ x ∈ Ω, x ≠ c → Submission.HarmonicOnXAt gC x :=
    fun x hx hxc => hgC.2.1 x ⟨hx, by simpa using hxc⟩
  obtain ⟨CΦ, hCΦ, hCΦb⟩ := gradient_clampedPullback_le (y := E.y i₀) (ρ := E.ρ i₀)
    (σ := E.σ i₀) (Φ := Φ) (E.hσρ i₀) (E.htgt i₀) hΦc1
  obtain ⟨Cg, hCgpos, hCgb⟩ := gradient_chartPull_le_invDist_of_pole (c := c) (y := E.y i₀)
    (ρ := E.ρ i₀) (σ := E.σ i₀) (E.hσρ i₀) (E.htgt i₀) (E.hballΩ i₀) hharmG
    (poleExpansion_chart_of_green hΩo hcΩ hgC hi₀mem)
  refine ⟨Cg * CΦ, mul_nonneg hCgpos.le hCΦ, ?_, ?_⟩
  · have hG : ContinuousOn
        (fun z : ℂ => gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i₀)).symm w)) z)
        (Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.σ i₀)
          ∩ {(chartAt ℂ (E.y i₀)) c}ᶜ) := by
      intro z hz
      obtain ⟨hzσ, hzp⟩ := hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hzp
      have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.ρ i₀) :=
        Metric.ball_subset_ball (le_of_lt (E.hσρ i₀)) hzσ
      have hzc : (chartAt ℂ (E.y i₀)).symm z ≠ c := by
        intro hcon
        have hright : (chartAt ℂ (E.y i₀)) ((chartAt ℂ (E.y i₀)).symm z) = z :=
          (chartAt ℂ (E.y i₀)).right_inv (E.htgt i₀ hzρ)
        exact hzp (by rw [← hright, hcon])
      exact (continuousAt_gradient_chartPull_of_ne_pole (ρ := E.ρ i₀) (E.htgt i₀)
        (E.hballΩ i₀) hharmG hzρ hzc).continuousWithinAt
    have hF : ContinuousOn
        (fun z : ℂ => gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i₀)).symm w)) z)
        (Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.σ i₀)
          ∩ {(chartAt ℂ (E.y i₀)) c}ᶜ) := by
      intro z hz
      have hzσ := hz.1
      have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.ρ i₀) :=
        Metric.ball_subset_ball (le_of_lt (E.hσρ i₀)) hzσ
      have hzsrc : (chartAt ℂ (E.y i₀)).symm z ∈ (chartAt ℂ (E.y i₀)).source :=
        (chartAt ℂ (E.y i₀)).map_target (E.htgt i₀ hzρ)
      have h := hΦc1 _ hzsrc
      rw [(chartAt ℂ (E.y i₀)).right_inv (E.htgt i₀ hzρ)] at h
      have h1 := h.continuousAt_fderiv (by norm_num)
      have h2 : ContinuousAt
          (fun w : ℂ => gradient (fun u : ℂ => Φ ((chartAt ℂ (E.y i₀)).symm u)) w) z := by
        simpa only [gradient, Function.comp_def] using
          (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
      exact h2.continuousWithinAt
    exact hG.inner hF
  · intro z hz hzp
    have hzρ : z ∈ Metric.ball ((chartAt ℂ (E.y i₀)) (E.y i₀)) (E.ρ i₀) :=
      Metric.ball_subset_ball (le_of_lt (E.hσρ i₀)) hz
    have hclamp : gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i₀)).symm w)) z
        = gradient (Work.Drive.clampedPullback (E.y i₀) (E.ρ i₀) Φ) z :=
      (Filter.EventuallyEq.gradient_eq (by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzρ] with w hw
        rw [Work.Drive.clampedPullback_apply_of_mem hw])).symm
    have h1 : ‖gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i₀)).symm w)) z‖
        ≤ Cg / ‖z - (chartAt ℂ (E.y i₀)) c‖ := hCgb z hz hzp
    have h2 : ‖gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i₀)).symm w)) z‖ ≤ CΦ := by
      rw [hclamp]; exact hCΦb z hz
    have h3 : ‖inner (𝕜 := ℝ) (gradient (fun w : ℂ => gC ((chartAt ℂ (E.y i₀)).symm w)) z)
        (gradient (fun w : ℂ => Φ ((chartAt ℂ (E.y i₀)).symm w)) z)‖
        ≤ (Cg / ‖z - (chartAt ℂ (E.y i₀)) c‖) * CΦ :=
      (norm_inner_le_norm _ _).trans
        (mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1))
    have h4 : (Cg / ‖z - (chartAt ℂ (E.y i₀)) c‖) * CΦ
        = (Cg * CΦ) / ‖z - (chartAt ℂ (E.y i₀)) c‖ := by ring
    rw [← h4]
    exact h3

end Work.Kernel
