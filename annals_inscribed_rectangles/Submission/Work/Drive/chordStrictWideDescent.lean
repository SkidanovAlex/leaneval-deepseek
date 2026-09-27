import Mathlib
import Submission.Work.Drive.chordWideAnnulusDescent
import Submission.Work.Drive.bandData
import Submission.Work.Drive.Neutral.dataChord_spec
import Submission.Work.Drive.Neutral.StripDiskAux

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff
open Set Filter
open scoped Topology

noncomputable section

/-- The radial cut-off of the correction: `0` below `1/8`, `1` above `1/4`. -/
private def wideChi : ℂ → ℂ := fun x => ((pStep (1 / 8) (1 / 4) ‖x‖ : ℝ) : ℂ)

private lemma contDiff_wideChi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wideChi :=
  Complex.ofRealCLM.contDiff.comp (contDiff_pStep_norm (by norm_num) (by norm_num))

private lemma wideChi_eq_zero {x : ℂ} (h : ‖x‖ ≤ 1 / 8) : wideChi x = 0 := by
  have h' : ((1 : ℝ) / 8) < 1 / 4 := by norm_num
  simp only [wideChi, pStep_eq_zero h' h, Complex.ofReal_zero]

private lemma wideChi_eq_one {x : ℂ} (h : 1 / 4 ≤ ‖x‖) : wideChi x = 1 := by
  have h' : ((1 : ℝ) / 8) < 1 / 4 := by norm_num
  simp only [wideChi, pStep_eq_one h' h, Complex.ofReal_one]

/-- **The descended chord data, with the strict band estimate on the annulus `1/4 ≤ ‖x‖ ≤ 2`.**

This is the strict strengthening of the band clause of `Work.Drive.chordWideAnnulusDescent` (and of
`Work.Drive.chordAnnulusDescent`): instead of `‖M (x,τ)‖² ≥ 2 * |τ| * ‖W (x,τ)‖²` one gets

> `4 * |τ| * ‖W (x,τ)‖² < ‖M (x,τ)‖²`  for `1/4 ≤ ‖x‖ ≤ 2`, `-c ≤ τ < 0`,

i.e. the *strict* inequality with the *larger* constant `4`; the value clauses on the unit circle and
the two non-vanishing clauses at `τ = 0` are as in the sibling lemma.

Both changes are absorbed by the very same compactness argument.  The quantity whose positivity is
propagated is `F_K p = ‖M p‖² - K * |p.2| * ‖W p‖²` for the constant `K = 4`, and on the diagonal
`S = {1/4 ≤ ‖x‖ ≤ 2, τ = 0}` it collapses to `‖M (x,0)‖² > 0`, *independently of `K`*: indeed
`M (x,0) = dataMid γ x 0 = curvePtAt γ x 0` is non-zero because `γ x ≠ 0` (`hγne`).  Hence `F_K > 0` and
`W ≠ 0` hold on all of `S`, the set `{F_K > 0} ∩ {W ≠ 0}` is *open* (`W` is smooth, `F_K` continuous
and strictly positive), and a thickening of the compact `S` by `δ > 0` lies inside it; the conclusion
follows with `c = δ/2`, since `dist ((x,τ), (x,0)) = |τ|`.

The construction of `M` and `W` is the `τ`-independent correction of `Work.Drive.chordAnnulusDescent`
already used by the sibling: with `χ` the cut-off above — `0` below `‖x‖ = 1/8`, `1` above `1/4` — set

> `M (x,τ) = M₀ (x,τ) + χ x * (A x - M₀ (x,0))`,  `A x = χ x * dataMid γ x 0 + (1 - χ x) * 1`,

and analogously for `W` with `dchW γ x 0` and `B`.  On `1/4 ≤ ‖x‖` the bracket is
`dataMid γ x 0 - M₀ (x,0)`, which *vanishes for `1/2 ≤ ‖x‖`* because there the `bandMu`-blend is
inactive and `M₀ (·,0)` already is the diagonal data; so the value clauses on the circle survive
verbatim, while on `1/4 ≤ ‖x‖ ≤ 1/2` the correction *replaces* `M₀ (·,0)` by `symmC (γ (x/‖x‖))`, which
is non-zero — here the obstruction of the disk form of the statement is absent, the loop being free to
leak onto the inner boundary `‖x‖ = 1/4`.  Below `1/8` the correction is switched off by the cut-off,
which keeps it smooth across the origin. -/
theorem chordStrictWideDescent (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    ∃ M W : ℂ × ℝ → ℂ, ∃ c : ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
      0 < c ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
        4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0) ∧
      (∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0) ∧
      (∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0) := by
  classical
  obtain ⟨M₀, W₀, c₀, hM₀sm, hW₀sm, hc₀, hM₀val, hW₀val, hband₀, hW₀ne, hM₀ne⟩ :=
    chordAnnulusDescent γ hγ hγne
  -- ## the two aligned diagonal functions (smooth: the cut-off kills a neighbourhood of the origin)
  set A : ℂ → ℂ := fun x => wideChi x * Neutral.dataMid γ x 0 + (1 - wideChi x) * 1 with hA
  set B : ℂ → ℂ := fun x => wideChi x * Neutral.dchW γ (x, 0) + (1 - wideChi x) * 1 with hB
  have hmidsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => Neutral.dataMid γ x 0) {x : ℂ | x ≠ 0} :=
    (Neutral.contDiffOn_dataMid_of_ne (γ := γ) hγ).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => hx)
  have hdchsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => Neutral.dchW γ (x, 0)) {x : ℂ | x ≠ 0} :=
    (Neutral.contDiffOn_dchW (γ := γ) hγ).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => hx)
  have hAsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℂ => wideChi x * Neutral.dataMid γ x 0) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x = 0
      · subst hx
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1 / 8)] with y hy
        have hy' : ‖y‖ ≤ 1 / 8 := by
          rw [Metric.mem_ball, dist_zero_right] at hy
          exact le_of_lt hy
        rw [wideChi_eq_zero hy', zero_mul]
      · have hop : {y : ℂ | y ≠ 0} ∈ 𝓝 x := isOpen_ne.mem_nhds hx
        exact contDiff_wideChi.contDiffAt.mul ((hmidsm.contDiffAt hop))
    exact h1.add (((contDiff_const.sub contDiff_wideChi).mul contDiff_const))
  have hBsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℂ => wideChi x * Neutral.dchW γ (x, 0)) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x = 0
      · subst hx
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1 / 8)] with y hy
        have hy' : ‖y‖ ≤ 1 / 8 := by
          rw [Metric.mem_ball, dist_zero_right] at hy
          exact le_of_lt hy
        rw [wideChi_eq_zero hy', zero_mul]
      · have hop : {y : ℂ | y ≠ 0} ∈ 𝓝 x := isOpen_ne.mem_nhds hx
        exact contDiff_wideChi.contDiffAt.mul ((hdchsm.contDiffAt hop))
    exact h1.add (((contDiff_const.sub contDiff_wideChi).mul contDiff_const))
  have hAval : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → A x = Neutral.dataMid γ x 0 := by
    intro x hx
    simp only [hA, wideChi_eq_one hx, one_mul, sub_self, zero_mul, add_zero]
  have hBval : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → B x = Neutral.dchW γ (x, 0) := by
    intro x hx
    simp only [hB, wideChi_eq_one hx, one_mul, sub_self, zero_mul, add_zero]
  -- ## the corrected data
  set M : ℂ × ℝ → ℂ := fun p => M₀ p + wideChi p.1 * (A p.1 - M₀ (p.1, 0)) with hM
  set W : ℂ × ℝ → ℂ := fun p => W₀ p + wideChi p.1 * (B p.1 - W₀ (p.1, 0)) with hW
  have hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℂ × ℝ => wideChi p.1 * (A p.1 - M₀ (p.1, 0))) :=
      ((contDiff_wideChi.comp contDiff_fst).mul
        (((hAsm.comp contDiff_fst).sub (hM₀sm.comp (contDiff_fst.prodMk contDiff_const)))))
    exact hM₀sm.add h1
  have hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℂ × ℝ => wideChi p.1 * (B p.1 - W₀ (p.1, 0))) :=
      ((contDiff_wideChi.comp contDiff_fst).mul
        (((hBsm.comp contDiff_fst).sub (hW₀sm.comp (contDiff_fst.prodMk contDiff_const)))))
    exact hW₀sm.add h1
  -- ## the values at τ = 0 on the annulus 1/4 ≤ ‖x‖ ≤ 1
  have hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → M (x, 0) = Neutral.dataMid γ x 0 := by
    intro x hx
    have h := hM₀val x 0 le_rfl
    rw [Real.sqrt_zero] at h
    simp only [hM, h, hAval x hx, wideChi_eq_one hx]
    ring
  have hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → W (x, 0) = Neutral.dchW γ (x, 0) := by
    intro x hx
    have h := hW₀val x 0 le_rfl
    rw [Real.sqrt_zero] at h
    simp only [hW, h, hBval x hx, wideChi_eq_one hx]
    ring
  -- the diagonal chord midpoint is non-zero
  have hmid_ne : ∀ x : ℂ, x ≠ 0 → Neutral.dataMid γ x 0 ≠ 0 := by
    intro x hx0 h
    have hpt : Neutral.dataMid γ x 0 = Neutral.curvePtAt γ x 0 := by
      simp only [Neutral.dataMid, Neutral.endPlus, Neutral.endMinus, neg_zero,
        add_self_div_two]
    rw [hpt] at h
    have hθ : (Circle.exp (Complex.arg x) : ℂ) = x / (‖x‖ : ℂ) := by
      rw [← Neutral.toCirc_eq_exp_arg x hx0, Neutral.toCirc_coe]
    rw [Neutral.curvePtAt_eq_exp γ x hx0 hθ 0] at h
    have hsc : Neutral.sClamp (0 : ℝ) = 0 :=
      Neutral.sClamp_eq_self (by rw [abs_zero]; positivity)
    rw [hsc, add_zero] at h
    exact hγne (Circle.exp (Complex.arg x)) (Neutral.symmC_eq_zero_iff.mp h)
  -- ## the compactness argument on the annulus at τ = 0
  set S : Set (ℂ × ℝ) := {p : ℂ × ℝ | 1 / 4 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ 2 ∧ p.2 = 0} with hSdef
  have hScompact : IsCompact S := by
    have hsub : S ⊆ Metric.closedBall (0 : ℂ × ℝ) 3 := by
      intro q hq
      rw [hSdef] at hq
      obtain ⟨h1, h2, h3⟩ := hq
      rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, norm_zero, max_le_iff]
      exact ⟨by simpa only [Real.norm_eq_abs] using (show ‖q.1‖ ≤ 3 by linarith),
        by rw [h3]; norm_num⟩
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ × ℝ) 3) ?_ hsub
    exact (isClosed_le continuous_const (continuous_norm.comp continuous_fst)).inter
      ((isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
        (isClosed_eq continuous_snd continuous_const))
  have hcont : Continuous fun p : ℂ × ℝ => ‖M p‖ ^ 2 - 4 * |p.2| * ‖W p‖ ^ 2 :=
    (hMsm.continuous.norm.pow 2).sub
      ((continuous_const.mul continuous_snd.abs).mul (hWsm.continuous.norm.pow 2))
  have hSopen : IsOpen {p : ℂ × ℝ | 0 < ‖M p‖ ^ 2 - 4 * |p.2| * ‖W p‖ ^ 2 ∧ W p ≠ 0} :=
    (isOpen_lt continuous_const hcont).inter (isOpen_ne.preimage hWsm.continuous)
  have hSsub : S ⊆ {p : ℂ × ℝ | 0 < ‖M p‖ ^ 2 - 4 * |p.2| * ‖W p‖ ^ 2 ∧ W p ≠ 0} := by
    intro q hq
    rw [hSdef] at hq
    obtain ⟨x, τ⟩ := q
    obtain ⟨h1, h2, h3⟩ := hq
    subst h3
    have hx0 : x ≠ 0 := by intro hz; rw [hz, norm_zero] at h1; norm_num at h1
    -- `M (x,0) = dataMid γ x 0 ≠ 0` and `W (x,0) = dchW γ (x,0) ≠ 0`
    have hMe : M (x, 0) = Neutral.dataMid γ x 0 := hM0 x h1
    have hWe : W (x, 0) = Neutral.dchW γ (x, 0) := hW0 x h1
    have hMne : M (x, 0) ≠ 0 := by
      rw [hMe]
      exact hmid_ne x hx0
    have hWne : W (x, 0) ≠ 0 := by
      rw [hWe]
      exact (Neutral.stripDiskChordNe γ hγ).2 x hx0 0
    refine ⟨?_, hWne⟩
    have hpos : 0 < ‖M (x, 0)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hMne) 2
    simpa using hpos
  obtain ⟨δ, hδpos, hδ⟩ := hScompact.exists_thickening_subset_open hSopen hSsub
  have hdist : ∀ (x : ℂ) (τ : ℝ), dist ((x, τ) : ℂ × ℝ) (x, (0 : ℝ)) = |τ| := by
    intro x τ
    rw [dist_eq_norm, Prod.norm_def]
    simp
  refine ⟨M, W, δ / 2, hMsm, hWsm, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x τ hτ hx
    have hx1 : 1 / 4 ≤ ‖x‖ := by rw [hx]; norm_num
    have h := hM₀val x τ hτ hx
    have h0 := hM₀val x 0 le_rfl hx
    rw [Real.sqrt_zero] at h0
    show M₀ (x, τ) + wideChi x * (A x - M₀ (x, 0)) = Neutral.dataMid γ x (Real.sqrt τ)
    rw [hAval x hx1, h, h0]
    ring
  · intro x τ hτ hx
    have hx1 : 1 / 4 ≤ ‖x‖ := by rw [hx]; norm_num
    have h := hW₀val x τ hτ hx
    have h0 := hW₀val x 0 le_rfl hx
    rw [Real.sqrt_zero] at h0
    show W₀ (x, τ) + wideChi x * (B x - W₀ (x, 0)) = Neutral.dchW γ (x, Real.sqrt τ)
    rw [hBval x hx1, h, h0]
    ring
  · intro x τ h1 h2 h3 h4
    have hmem : (x, τ) ∈ Metric.thickening δ S :=
      Metric.mem_thickening_iff.mpr ⟨(x, 0), ⟨h1, h2, rfl⟩, by
        rw [hdist]; rw [abs_of_neg h4]; linarith⟩
    have := (hδ hmem).1
    linarith [this]
  · intro x τ h1 h2 h3 h4
    refine (hδ ?_).2
    exact Metric.mem_thickening_iff.mpr ⟨(x, 0), ⟨h1, h2, rfl⟩, by
      rw [hdist]; rw [abs_of_neg h4]; linarith⟩
  · intro x h1 h2
    have hx0 : x ≠ 0 := by intro hz; rw [hz, norm_zero] at h1; norm_num at h1
    rw [hM0 x h1]
    exact hmid_ne x hx0
  · intro x h1 h2
    have hx0 : x ≠ 0 := by intro hz; rw [hz, norm_zero] at h1; norm_num at h1
    rw [hW0 x h1]
    exact (Neutral.stripDiskChordNe γ hγ).2 x hx0 0

end

end Work.Drive
