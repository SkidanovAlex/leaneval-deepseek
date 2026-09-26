import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.HalfDiscAux
import Submission.Work.Drive.Mono.sphereArc_extension
import Submission.Work.Drive.Mono.gaugeRadial_spec

/-!
# A convex body with a flat boundary segment is a half-disc, compatibly with the segment

This is the construction of `Work.Drive.Mono.halfDisc_map_of_segment` (that module does not
compile: it times out at `maxHeartbeats`; its definitions live on, unchanged, in
`Work.Drive.Mono.HalfDiscAux`), with two extra conclusions: the map is globally continuous, and
it carries the closed semicircle onto `frontier A` minus the open segment `[m₁,m₂]°`.

The map is `f = gaugeRadialInv A pA ∘ coneDisc G ∘ gaugeRadial upperHalfDisc (I/2)`, where `G`
is obtained from `Work.Drive.Mono.sphereArc_extension` applied to the two arcs.
-/

namespace Work.Drive.Mono

open Set
open scoped Pointwise

noncomputable section

private lemma norm_ofReal_eq (t : ℝ) : ‖(t : ℂ)‖ = |t| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- A point of the interior of a set is not a frontier point. -/
private lemma not_mem_frontier_of_mem_interior {U : Set ℂ} {z : ℂ} (hz : z ∈ interior U) :
    z ∉ frontier U := by
  rw [← closure_sdiff_interior]
  exact fun h => h.2 hz

/-- A point of the closed upper half-disc of norm `1` is a frontier point. -/
private lemma mem_frontier_upperHalfDisc_of_norm_eq_one {z : ℂ} (hz : z ∈ upperHalfDisc)
    (hn : ‖z‖ = 1) : z ∈ frontier upperHalfDisc := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure hz, ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(1 + ε / 2) • z, ?_, ?_⟩
  · intro hmem
    have h2 : ‖(1 + ε / 2) • z‖ = 1 + ε / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith), hn, mul_one]
    have := hmem.1
    rw [h2] at this
    linarith
  · rw [dist_eq_norm]
    have h1 : z - (1 + ε / 2) • z = (-(ε / 2)) • z := by module
    rw [h1, norm_smul, norm_neg, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ ε / 2), hn, mul_one]
    linarith

/-- An interior point of the closed upper half-disc has norm `< 1` and positive imaginary part. -/
private lemma mem_interior_upperHalfDisc {z : ℂ} (h1 : ‖z‖ < 1) (h2 : 0 < z.im) :
    z ∈ interior upperHalfDisc := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min ((1 - ‖z‖) / 2) (z.im / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hw1 : ‖w‖ ≤ 1 := by
    have hle : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    have h3 : ‖w - z‖ < (1 - ‖z‖) / 2 := lt_of_lt_of_le hw (min_le_left _ _)
    linarith
  have hw2 : 0 ≤ w.im := by
    have hle : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    have h3 : ‖w - z‖ < z.im / 2 := lt_of_lt_of_le hw (min_le_right _ _)
    have h4 : -(z.im / 2) < w.im - z.im := by
      have := (abs_lt.mp (lt_of_le_of_lt hle h3)).1
      rw [Complex.sub_im] at this
      linarith
    linarith
  exact ⟨hw1, hw2⟩

/-- `1` is in the closed upper half-disc. -/
private lemma one_mem_upperHalfDisc : (((1 : ℝ)) : ℂ) ∈ upperHalfDisc := by
  refine ⟨?_, by simp⟩
  rw [norm_ofReal_eq]
  norm_num

/-- `-1` is in the closed upper half-disc. -/
private lemma neg_one_mem_upperHalfDisc : ((((-1 : ℝ))) : ℂ) ∈ upperHalfDisc := by
  refine ⟨?_, by simp⟩
  rw [norm_ofReal_eq]
  norm_num

/-- The affine parametrisation of a segment: `[m₁,m₂]` is the image of `[-1,1]` under
`t ↦ ((1-t)/2) • m₁ + ((1+t)/2) • m₂`. -/
private lemma image_sigma_Icc (m₁ m₂ : ℂ) :
    (fun t : ℝ => ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂) '' Set.Icc (-1 : ℝ) 1
      = segment ℝ m₁ m₂ := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    rw [segment]
    exact ⟨(1 - t) / 2, (1 + t) / 2, by linarith [ht.2], by linarith [ht.1], by ring, rfl⟩
  · rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b - a, ⟨by linarith, by linarith⟩, ?_⟩
    change ((1 - (b - a)) / 2) • m₁ + ((1 + (b - a)) / 2) • m₂ = a • m₁ + b • m₂
    rw [show (1 - (b - a)) / 2 = a by linarith, show (1 + (b - a)) / 2 = b by linarith]

set_option maxHeartbeats 8000000 in
theorem upperHalfDisc_map_of_segment_frontier (A : Set ℂ)
    (hAc : Convex ℝ A) (hAcl : IsClosed A) (hAb : Bornology.IsBounded A)
    (hAne : (interior A).Nonempty)
    {m₁ m₂ : ℂ} (hm : m₁ ≠ m₂) (hseg : segment ℝ m₁ m₂ ⊆ frontier A)
    (pA : ℂ) (hpA : pA ∈ interior A) :
    ∃ f : ℂ → ℂ, Continuous f ∧ Set.InjOn f upperHalfDisc ∧ f '' upperHalfDisc = A ∧
      (∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
        f (t : ℂ) = ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂) ∧
      f '' (upperHalfDisc ∩ {z : ℂ | ‖z‖ = 1}) =
        frontier A \ (segment ℝ m₁ m₂ \ {m₁, m₂}) := by
  classical
  have hAne' : (interior A).Nonempty := hAne
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  -- ## the gauge-rescale homeomorphism of `A` from `pA`
  obtain ⟨hgcont, hginvcont, hgmemA, hgmemF, hginv_g, hg_invinv, hginv_memA, hginv_memF⟩ :=
    gaugeRadial_spec hAc hAcl hAb hpA
  have hginv_inj : Function.Injective (gaugeRadialInv A pA) := by
    intro x y h
    have := congrArg (gaugeRadial A pA) h
    simpa [hg_invinv] using this
  have hg_inj : Function.Injective (gaugeRadial A pA) := by
    intro x y h
    have := congrArg (gaugeRadialInv A pA) h
    simpa [hginv_g] using this
  -- ## the gauge-rescale homeomorphism of the closed upper half-disc
  obtain ⟨hhcont, hhinvcont, hhmemA, hhmemF, hhinv_h, hh_invinv, _, _⟩ :=
    gaugeRadial_spec convex_upperHalfDisc isClosed_upperHalfDisc isBounded_upperHalfDisc
      I_div_two_mem_interior_upperHalfDisc
  have hh_inj : Function.Injective (gaugeRadial upperHalfDisc (Complex.I / 2)) := by
    intro x y h
    have := congrArg (gaugeRadialInv upperHalfDisc (Complex.I / 2)) h
    simpa [hhinv_h] using this
  -- ## the affine parametrisation of the segment `[m₁,m₂]`
  let σ : ℝ → ℂ := fun t => ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂
  have hσcont : Continuous σ := by
    change Continuous (fun t : ℝ => ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂)
    continuity
  have hσseg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, σ t ∈ segment ℝ m₁ m₂ := by
    intro t ht
    rw [segment]
    exact ⟨(1 - t) / 2, (1 + t) / 2, by linarith [ht.2], by linarith [ht.1], by ring, rfl⟩
  have hσinj : Set.InjOn σ (Set.Icc (-1 : ℝ) 1) := by
    intro s _ t _ hst
    have hs : σ s = m₁ + ((1 + s) / 2) • (m₂ - m₁) := by
      change ((1 - s) / 2) • m₁ + ((1 + s) / 2) • m₂ = m₁ + ((1 + s) / 2) • (m₂ - m₁)
      rw [smul_sub]
      module
    have ht' : σ t = m₁ + ((1 + t) / 2) • (m₂ - m₁) := by
      change ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂ = m₁ + ((1 + t) / 2) • (m₂ - m₁)
      rw [smul_sub]
      module
    rw [hs, ht'] at hst
    have hab : ((1 + s) / 2) • (m₂ - m₁) = ((1 + t) / 2) • (m₂ - m₁) :=
      add_left_cancel hst
    have h0 : (((1 + s) / 2) - ((1 + t) / 2)) • (m₂ - m₁) = 0 := by
      rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hm)
  -- ## the two boundary arcs, extended to `ℝ` by the nearest-point projection `[-1,1]`
  have hmemA : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      gaugeRadial A pA (σ t) ∈ Metric.sphere (0 : ℂ) 1 :=
    fun t ht => (hgmemF (σ t)).mpr (hseg (hσseg t ht))
  have hmemU : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      gaugeRadial upperHalfDisc (Complex.I / 2) (t : ℂ) ∈ Metric.sphere (0 : ℂ) 1 :=
    fun t ht => (hhmemF (t : ℂ)).mpr (ofReal_mem_frontier_upperHalfDisc ht)
  let P : ℝ → Set.Icc (-1 : ℝ) 1 := Set.projIcc (-1 : ℝ) 1 hle
  have hPval : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (P t : ℝ) = t :=
    fun t ht => congrArg Subtype.val (Set.projIcc_of_mem hle ht)
  have hPcont : Continuous P := continuous_projIcc
  let u : ℝ → Metric.sphere (0 : ℂ) 1 :=
    fun t => ⟨gaugeRadial upperHalfDisc (Complex.I / 2) (((P t : ℝ)) : ℂ),
      hmemU (P t : ℝ) (P t).2⟩
  let v : ℝ → Metric.sphere (0 : ℂ) 1 :=
    fun t => ⟨gaugeRadial A pA (σ (P t : ℝ)), hmemA (P t : ℝ) (P t).2⟩
  have hucont : Continuous u := by
    apply Continuous.subtype_mk
    exact hhcont.comp (Complex.continuous_ofReal.comp (continuous_subtype_val.comp hPcont))
  have hvcont : Continuous v := by
    apply Continuous.subtype_mk
    exact hgcont.comp (hσcont.comp (continuous_subtype_val.comp hPcont))
  have huInj : Set.InjOn u (Set.Icc (-1 : ℝ) 1) := by
    intro s hs t ht hst
    have h1 : gaugeRadial upperHalfDisc (Complex.I / 2) (((P s : ℝ)) : ℂ)
        = gaugeRadial upperHalfDisc (Complex.I / 2) (((P t : ℝ)) : ℂ) :=
      congrArg (fun x : Metric.sphere (0 : ℂ) 1 => (x : ℂ)) hst
    have h2 : (P s : ℝ) = (P t : ℝ) := Complex.ofReal_injective (hh_inj h1)
    rw [hPval s hs, hPval t ht] at h2
    exact h2
  have hvInj : Set.InjOn v (Set.Icc (-1 : ℝ) 1) := by
    intro s hs t ht hst
    have h1 : gaugeRadial A pA (σ (P s : ℝ)) = gaugeRadial A pA (σ (P t : ℝ)) :=
      congrArg (fun x : Metric.sphere (0 : ℂ) 1 => (x : ℂ)) hst
    have h2 : σ (P s : ℝ) = σ (P t : ℝ) := hg_inj h1
    have h3 : (P s : ℝ) = (P t : ℝ) := hσinj (P s).2 (P t).2 h2
    rw [hPval s hs, hPval t ht] at h3
    exact h3
  -- ## matching the two arcs by a homeomorphism of the circle
  obtain ⟨G, hG⟩ := sphereArc_extension hucont hvcont huInj hvInj
  -- ## the map of the half-disc and the map of `A`
  let Φ : ℂ → ℂ := fun z => coneDisc G (gaugeRadial upperHalfDisc (Complex.I / 2) z)
  let f : ℂ → ℂ := fun z => gaugeRadialInv A pA (Φ z)
  have hΦdiam : ∀ t ∈ Set.Icc (-1 : ℝ) 1, Φ (t : ℂ) = gaugeRadial A pA (σ t) := by
    intro t ht
    have hu_eq : u t = ⟨gaugeRadial upperHalfDisc (Complex.I / 2) (t : ℂ), hmemU t ht⟩ := by
      apply Subtype.ext
      show gaugeRadial upperHalfDisc (Complex.I / 2) (((P t : ℝ)) : ℂ)
        = gaugeRadial upperHalfDisc (Complex.I / 2) ((t : ℝ) : ℂ)
      rw [hPval t ht]
    have hv_eq : v t = ⟨gaugeRadial A pA (σ t), hmemA t ht⟩ := by
      apply Subtype.ext
      show gaugeRadial A pA (σ (P t : ℝ)) = gaugeRadial A pA (σ (t : ℝ))
      rw [hPval t ht]
    have hGt : G ⟨gaugeRadial upperHalfDisc (Complex.I / 2) (t : ℂ), hmemU t ht⟩
        = ⟨gaugeRadial A pA (σ t), hmemA t ht⟩ := by
      rw [← hu_eq, ← hv_eq]
      exact hG t ht
    change coneDisc G (gaugeRadial upperHalfDisc (Complex.I / 2) (t : ℂ)) = gaugeRadial A pA (σ t)
    rw [coneDisc_eq_of_mem_sphere G (hmemU t ht), hGt]
  have hΦ_image : Φ '' upperHalfDisc = Metric.closedBall (0 : ℂ) 1 := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : gaugeRadial upperHalfDisc (Complex.I / 2) z ∈ Metric.closedBall (0 : ℂ) 1 :=
        (hhmemA z).mpr hz
      rw [Metric.mem_closedBall, dist_zero_right, norm_coneDisc]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz'
    · intro hw
      obtain ⟨y, hy, hyw⟩ := coneDisc_surjOn G w hw
      refine ⟨gaugeRadialInv upperHalfDisc (Complex.I / 2) y, ?_, ?_⟩
      · exact (hhmemA _).mp (by rw [hh_invinv y]; exact hy)
      · change coneDisc G (gaugeRadial upperHalfDisc (Complex.I / 2)
          (gaugeRadialInv upperHalfDisc (Complex.I / 2) y)) = w
        rw [hh_invinv y, hyw]
  have hΦinj : Set.InjOn Φ upperHalfDisc := by
    intro z hz z' hz' h
    have h1 : gaugeRadial upperHalfDisc (Complex.I / 2) z
        = gaugeRadial upperHalfDisc (Complex.I / 2) z' :=
      injOn_coneDisc G ((hhmemA z).mpr hz) ((hhmemA z').mpr hz') h
    exact hh_inj h1
  have hΦcont : Continuous Φ := (continuous_coneDisc G).comp hhcont
  have hf_cont : ContinuousOn f upperHalfDisc :=
    hginvcont.comp_continuousOn hΦcont.continuousOn
  have hf_inj : Set.InjOn f upperHalfDisc := by
    intro z hz z' hz' h
    exact hΦinj hz hz' (hginv_inj h)
  have hf_image : f '' upperHalfDisc = A := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine hginv_memA (Φ z) ?_
      have hz' : Φ z ∈ Metric.closedBall (0 : ℂ) 1 := by
        rw [← hΦ_image]; exact ⟨z, hz, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right] at hz'
    · intro hw
      have hgw : gaugeRadial A pA w ∈ Metric.closedBall (0 : ℂ) 1 := (hgmemA w).mpr hw
      rw [← hΦ_image] at hgw
      obtain ⟨z, hz, hz'⟩ := hgw
      refine ⟨z, hz, ?_⟩
      change gaugeRadialInv A pA (Φ z) = w
      rw [hz', hginv_g w]
  have hf_diam : ∀ t : ℝ, (t : ℂ) ∈ upperHalfDisc → f (t : ℂ) = σ t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      have h1 : ‖(t : ℂ)‖ ≤ 1 := ht.1
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs] at h1
      exact abs_le.mp h1
    change gaugeRadialInv A pA (Φ (t : ℂ)) = σ t
    rw [hΦdiam t htIcc, hginv_g (σ t)]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · show Continuous f
    exact hginvcont.comp hΦcont
  · exact hf_inj
  · exact hf_image
  · intro t ht
    have htU : (t : ℂ) ∈ upperHalfDisc := by
      refine ⟨?_, by simp⟩
      rw [norm_ofReal_eq]
      exact abs_le.mpr ⟨ht.1, ht.2⟩
    exact hf_diam t htU
  · -- the frontier identity
    have hσ1 : σ 1 = m₂ := by
      change ((1 - (1:ℝ)) / 2) • m₁ + ((1 + (1:ℝ)) / 2) • m₂ = m₂
      simp
    have hσm1 : σ (-1) = m₁ := by
      change ((1 - (-1:ℝ)) / 2) • m₁ + ((1 + (-1:ℝ)) / 2) • m₂ = m₁
      simp
    have hσinj' : Function.Injective σ := by
      intro s t hst
      have h1 : σ s = m₁ + ((1 + s) / 2) • (m₂ - m₁) := by
        change ((1 - s) / 2) • m₁ + ((1 + s) / 2) • m₂ = m₁ + ((1 + s) / 2) • (m₂ - m₁)
        rw [smul_sub]; module
      have h2 : σ t = m₁ + ((1 + t) / 2) • (m₂ - m₁) := by
        change ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂ = m₁ + ((1 + t) / 2) • (m₂ - m₁)
        rw [smul_sub]; module
      rw [h1, h2] at hst
      have h3 : ((1 + s) / 2) • (m₂ - m₁) = ((1 + t) / 2) • (m₂ - m₁) := add_left_cancel hst
      have h4 : (((1 + s) / 2) - ((1 + t) / 2)) • (m₂ - m₁) = 0 := by rw [sub_smul, h3, sub_self]
      rcases smul_eq_zero.mp h4 with h | h
      · linarith
      · exact absurd (sub_eq_zero.mp h) (Ne.symm hm)
    have hsegσ : σ '' Set.Icc (-1 : ℝ) 1 = segment ℝ m₁ m₂ := by
      change (fun t : ℝ => ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂) '' Set.Icc (-1 : ℝ) 1
        = segment ℝ m₁ m₂
      exact image_sigma_Icc m₁ m₂
    apply Set.Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      obtain ⟨hzU, hzn⟩ := hz
      refine ⟨?_, ?_⟩
      · have hzfr : z ∈ frontier upperHalfDisc :=
          mem_frontier_upperHalfDisc_of_norm_eq_one hzU hzn
        have h1 : gaugeRadial upperHalfDisc (Complex.I / 2) z ∈ Metric.sphere (0 : ℂ) 1 :=
          (hhmemF z).mpr hzfr
        rw [Metric.mem_sphere, dist_zero_right] at h1
        have h2 : ‖Φ z‖ = 1 := by
          change ‖coneDisc G (gaugeRadial upperHalfDisc (Complex.I / 2) z)‖ = 1
          rw [norm_coneDisc, h1]
        exact hginv_memF (Φ z) h2
      · intro hcon
        have hconS : f z ∈ segment ℝ m₁ m₂ := hcon.1
        rw [← hsegσ] at hconS
        obtain ⟨t, ht, hteq⟩ := hconS
        have htU : (t : ℂ) ∈ upperHalfDisc := by
          refine ⟨?_, by simp⟩
          rw [norm_ofReal_eq]
          exact abs_le.mpr ⟨ht.1, ht.2⟩
        have hzt : z = (t : ℂ) := hf_inj hzU htU (by rw [hf_diam t htU, hteq])
        have hnz : ‖(t : ℂ)‖ = 1 := by rw [← hzt]; exact hzn
        rw [norm_ofReal_eq] at hnz
        rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hnz with h1 | h1
        · have : f z = m₂ := by
            rw [hzt, h1, hf_diam 1 one_mem_upperHalfDisc, hσ1]
          exact hcon.2 (Or.inr this)
        · have : f z = m₁ := by
            rw [hzt, h1, hf_diam (-1) neg_one_mem_upperHalfDisc, hσm1]
          exact hcon.2 (Or.inl this)
    · intro w hw
      obtain ⟨hwfr, hwdeg⟩ := hw
      have hwA : w ∈ A := by
        have h1 : w ∈ closure A := frontier_subset_closure hwfr
        rwa [hAcl.closure_eq] at h1
      rw [← hf_image] at hwA
      obtain ⟨z, hzU, hzw⟩ := hwA
      refine ⟨z, ⟨hzU, ?_⟩, hzw⟩
      by_contra hzne
      have hzlt : ‖z‖ < 1 := lt_of_le_of_ne hzU.1 hzne
      rcases lt_or_eq_of_le hzU.2 with him | him
      · have hzint : z ∈ interior upperHalfDisc := mem_interior_upperHalfDisc hzlt him
        have hΦlt : ‖Φ z‖ < 1 := by
          have h1 : ‖gaugeRadial upperHalfDisc (Complex.I / 2) z‖ < 1 := by
            refine lt_of_le_of_ne ?_ ?_
            · have h2 := (hhmemA z).mpr hzU
              rw [Metric.mem_closedBall, dist_zero_right] at h2
              exact h2
            · intro hcon2
              have h2 : gaugeRadial upperHalfDisc (Complex.I / 2) z ∈ Metric.sphere (0 : ℂ) 1 := by
                rwa [Metric.mem_sphere, dist_zero_right]
              exact not_mem_frontier_of_mem_interior hzint ((hhmemF z).mp h2)
          change ‖coneDisc G (gaugeRadial upperHalfDisc (Complex.I / 2) z)‖ < 1
          rw [norm_coneDisc]
          exact h1
        have hwintA : w ∈ interior A := by
          have h2 : w ∈ A := by rw [← hzw]; exact hginv_memA (Φ z) hΦlt.le
          have h3 : w ∉ frontier A := by
            intro hcon2
            have h4 : gaugeRadial A pA w ∈ Metric.sphere (0 : ℂ) 1 := (hgmemF w).mpr hcon2
            rw [← hzw] at h4
            rw [hg_invinv (Φ z), Metric.mem_sphere, dist_zero_right] at h4
            exact absurd h4 hΦlt.ne
          have h6 : frontier A = A \ interior A := hAcl.frontier_eq
          rcases (show w ∈ interior A ∪ frontier A from by
            rw [h6]
            by_cases hwint : w ∈ interior A
            · exact Or.inl hwint
            · exact Or.inr ⟨h2, hwint⟩) with h | h
          · exact h
          · exact absurd h h3
        exact not_mem_frontier_of_mem_interior hwintA hwfr
      · have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
        have hzreabs : |z.re| < 1 := by
          have h1 : ‖z‖ = |z.re| := by
            conv_lhs => rw [hzre]
            exact norm_ofReal_eq z.re
          linarith
        have hzre_lt : z.re < 1 := (abs_lt.mp hzreabs).2
        have hzre_gt : -1 < z.re := (abs_lt.mp hzreabs).1
        have htIcc : z.re ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt hzre_gt, le_of_lt hzre_lt⟩
        have hUre : (((z.re : ℝ)) : ℂ) ∈ upperHalfDisc := by
          refine ⟨?_, by simp⟩
          rw [norm_ofReal_eq]
          exact le_of_lt hzreabs
        have hweq : w = σ (z.re) := by
          rw [← hzw]
          conv_lhs => rw [hzre]
          exact hf_diam z.re hUre
        have hne1 : σ (z.re) ≠ m₁ := by
          intro hcon2
          have h' : σ (z.re) = σ (-1) := by rw [hcon2, hσm1]
          have h2 : z.re = -1 := hσinj' h'
          linarith
        have hne2 : σ (z.re) ≠ m₂ := by
          intro hcon2
          have h' : σ (z.re) = σ 1 := by rw [hcon2, hσ1]
          have h2 : z.re = 1 := hσinj' h'
          linarith
        rw [hweq] at hwdeg
        exact hwdeg ⟨hσseg z.re htIcc, by
          intro hcon3
          rcases hcon3 with h | h
          · exact hne1 h
          · exact hne2 h⟩

end

end Work.Drive.Mono
