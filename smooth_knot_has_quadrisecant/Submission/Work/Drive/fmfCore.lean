import Mathlib
import Submission.Work.Drive.fmfDefs
import Submission.Work.Drive.closure_liftedTrisecant_eq_or_tangent
import Submission.Work.Drive.local_uniqueness_of_partialsBM_independent
import Submission.Work.Drive.shortSecantsFree_of_noInflection
import Submission.TorusCollinearity

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 1200000

lemma exists_coe_eq_real (x : KnotParam) : ∃ t : ℝ, (t : KnotParam) = x :=
  let ⟨t, _, ht⟩ := AddCircle.eq_coe_Ico x
  ⟨t, ht⟩

/-- `cross3 w w = 0`. -/
lemma cross3_self_eq_zero (w : Space) : cross3 w w = 0 := by
  rw [cross3_eq_zero_iff_smul_local]
  exact Or.inr ⟨1, by simp⟩

/-- Points of the closed segment give collinear triples. -/
lemma cross3_eq_zero_of_mem_segment {u v w : Space} (hw : w ∈ segment ℝ u v) :
    cross3 (u - v) (u - w) = 0 := by
  rcases hw with ⟨a, b, ha, hb, hab, rfl⟩
  have h1 : u - (a • u + b • v) = b • (u - v) := by
    have ha' : a = 1 - b := by linarith
    rw [ha']; module
  rw [h1, cross3_smul_right, cross3_self_eq_zero, smul_zero]

/-- **Core implication.**  If the vertical trace of the lifted trisecant locus over the meridian
`ξ` is infinite, then `ξ` is the column of a tangent chord or of a hinge-degenerate trisecant. -/
theorem fmf_coreImplication {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (ξ : ℝ)
    (hinf : ¬ (liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ}).Finite) :
    ξ ∈ TangentColumns r ∪ CriticalColumns r := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := shortSecantsFree_of_noInflection hr hinfl
  set T : Set ℝ := {y : ℝ | (ξ, y) ∈ liftedTrisecant r} with hTdef
  have hTinf : T.Infinite := by
    have h1 : (fun y : ℝ => ((ξ, y) : ℝ × ℝ)) '' T
        = liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ} := by
      ext q; constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨hy, rfl⟩
      · rintro ⟨hqA, hq1⟩
        refine ⟨q.2, ?_, ?_⟩
        · show (ξ, q.2) ∈ liftedTrisecant r
          rw [← hq1]; exact hqA
        · exact Prod.ext hq1.symm rfl
    exact Set.Infinite.of_image (f := fun y : ℝ => ((ξ, y) : ℝ × ℝ)) (by rw [h1]; exact Set.not_finite.mpr hinf)
  have hTK : T ⊆ Set.Icc δ (period - δ) := fun y hy => hδ (ξ, y) hy
  obtain ⟨y₀, hy₀K, hy₀acc⟩ := hTinf.exists_accPt_of_subset_isCompact isCompact_Icc hTK
  have hy₀0 : 0 < y₀ := lt_of_lt_of_le hδpos hy₀K.1
  have hy₀lt : y₀ < period := by linarith [hy₀K.2]
  have hy₀acc' : ∃ᶠ y in 𝓝 y₀, y ≠ y₀ ∧ y ∈ T := accPt_iff_frequently.mp hy₀acc
  have hex : ∀ n : ℕ, ∃ y : ℝ, y ∈ T ∧ y ≠ y₀ ∧ |y - y₀| < 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : ∀ᶠ y in 𝓝 y₀, |y - y₀| < 1 / ((n : ℝ) + 1) := by
      filter_upwards [Metric.ball_mem_nhds y₀ (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1))]
        with z hz
      rw [Metric.mem_ball, Real.dist_eq] at hz
      exact lt_of_lt_of_le hz le_rfl
    obtain ⟨y, h⟩ := (hy₀acc'.and_eventually h1).exists
    exact ⟨y, h.1.2, h.1.1, h.2⟩
  choose y hyT hyne hylim using hex
  have hytend : Tendsto y atTop (𝓝 y₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]
    exact le_of_lt (hylim n)
  have hmid : ∀ n : ℕ, ∃ m : KnotParam, IsMiddleOnChord r (ξ : KnotParam)
      (((ξ + y n : ℝ)) : KnotParam) m :=
    fun n => exists_middle_of_mem_liftedTrisecant (hyT n)
  choose mc hmc using hmid
  obtain ⟨m₀, -, φ, hφ, hmφ⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set KnotParam)).tendsto_subseq (x := mc)
      (fun n => Set.mem_univ _)
  have hlif : ∀ k : ℕ, ∃ t : ℝ, t ∈ Set.Ico 0 period ∧ (t : KnotParam) = mc (φ k) :=
    fun k => AddCircle.eq_coe_Ico (mc (φ k))
  choose mr hmrwin hmrcoe using hlif
  obtain ⟨m₀R, hm₀Rwin, ψ, hψ, hmψ⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) period)).tendsto_subseq (x := mr)
      (fun k => ⟨(hmrwin k).1, (hmrwin k).2.le⟩)
  -- the class of the limit of the real lifts
  have hm₀coe : ((m₀R : ℝ) : KnotParam) = m₀ := by
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have h1 : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop
        (𝓝 ((m₀R : ℝ) : KnotParam)) := (hcoe.tendsto m₀R).comp hmψ
    have h2 : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop (𝓝 m₀) := by
      have h3 : (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) = fun k : ℕ => mc (φ (ψ k)) :=
        funext fun k => hmrcoe (ψ k)
      rw [h3]
      exact hmφ.comp hψ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hyt : Tendsto (fun k : ℕ => y (φ (ψ k))) atTop (𝓝 y₀) :=
    hytend.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  -- the limit is on the closed chord
  have hclosed : IsMiddleOnClosedChord r (ξ : KnotParam) (((ξ + y₀ : ℝ)) : KnotParam) m₀ := by
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have hsec : Tendsto (fun k : ℕ => (((ξ + y (φ (ψ k)) : ℝ)) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) :=
      (hcoe.tendsto (ξ + y₀)).comp (tendsto_const_nhds.add hyt)
    have hmc' : Tendsto (fun k : ℕ => mc (φ (ψ k))) atTop (𝓝 m₀) := hmφ.comp hψ.tendsto_atTop
    have hseq : Tendsto (fun k : ℕ => ((ξ : KnotParam), ((((ξ + y (φ (ψ k)) : ℝ)) : KnotParam),
        mc (φ (ψ k))))) atTop (𝓝 ((ξ : KnotParam), ((((ξ + y₀ : ℝ)) : KnotParam), m₀))) :=
      Tendsto.prodMk_nhds tendsto_const_nhds (Tendsto.prodMk_nhds hsec hmc')
    refine (isClosed_closedMiddleData hr).mem_of_tendsto hseq ?_
    filter_upwards with k
    exact openMiddleData_subset_closedMiddleData r (by
      change IsMiddleOnOpenChord r (ξ : KnotParam) (((ξ + y (φ (ψ k)) : ℝ)) : KnotParam)
        (mc (φ (ψ k)))
      simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hmc (φ (ψ k)))
  have hseg : r m₀R ∈ segment ℝ (r ξ) (r (ξ + y₀)) := by
    have h := hclosed
    rw [IsMiddleOnClosedChord, knotMap_eq_r hr ξ, knotMap_eq_r hr (ξ + y₀),
      show knotMap r m₀ = r m₀R from by rw [← hm₀coe, knotMap_eq_r hr m₀R]] at h
    exact h
  have hmidreal : ∀ k : ℕ, r (mr (ψ k)) ∈ openSegment ℝ (r ξ) (r (ξ + y (φ (ψ k)))) := by
    intro k
    have h1 : IsMiddleOnChord r (ξ : KnotParam) (((ξ + y (φ (ψ k)) : ℝ)) : KnotParam)
        ((mr (ψ k) : ℝ) : KnotParam) := by
      rw [hmrcoe (ψ k)]; exact hmc (φ (ψ k))
    exact (IsMiddleOnChord_iff_real hr ξ (ξ + y (φ (ψ k))) (mr (ψ k))).mp h1
  have hAne : r ξ ≠ r (ξ + y₀) := by
    intro hk
    have hk' : ((ξ : ℝ) : KnotParam) = (((ξ + y₀ : ℝ)) : KnotParam) :=
      (knotMap_inj_iff hr).mp (by rw [knotMap_eq_r hr ξ, knotMap_eq_r hr (ξ + y₀)]; exact hk)
    exact coe_ne_coe_of_lt hy₀0 hy₀lt hk'
  rcases eq_or_ne (r m₀R) (r ξ) with h1 | h1
  · left
    refine ⟨y₀, hy₀0, hy₀lt, Or.inl ?_⟩
    have hcls : ((m₀R : ℝ) : KnotParam) = ((ξ : ℝ) : KnotParam) :=
      (knotMap_inj_iff hr).mp (by rw [knotMap_eq_r hr m₀R, knotMap_eq_r hr ξ]; exact h1)
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have hu : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop (𝓝 ((ξ : ℝ) : KnotParam)) := by
      rw [← hcls]
      exact (hcoe.tendsto m₀R).comp hmψ
    have hb : Tendsto (fun k : ℕ => (((ξ + y (φ (ψ k)) : ℝ)) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) :=
      (hcoe.tendsto (ξ + y₀)).comp (tendsto_const_nhds.add hyt)
    have hstr : ∀ᶠ k in atTop, IsMiddleOnChord r (ξ : KnotParam)
        (((ξ + y (φ (ψ k)) : ℝ)) : KnotParam) ((mr (ψ k) : ℝ) : KnotParam) := by
      filter_upwards with k
      rw [hmrcoe (ψ k)]; exact hmc (φ (ψ k))
    exact cross_zero_of_tendsto_middle_endpoint_a hr hAne tendsto_const_nhds hb hu hstr
  rcases eq_or_ne (r m₀R) (r (ξ + y₀)) with h2 | h2
  · left
    refine ⟨y₀, hy₀0, hy₀lt, Or.inr ?_⟩
    have hcls : ((m₀R : ℝ) : KnotParam) = (((ξ + y₀ : ℝ)) : KnotParam) :=
      (knotMap_inj_iff hr).mp (by rw [knotMap_eq_r hr m₀R, knotMap_eq_r hr (ξ + y₀)]; exact h2)
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have hu : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) := by
      rw [← hcls]
      exact (hcoe.tendsto m₀R).comp hmψ
    have hb : Tendsto (fun k : ℕ => (((ξ + y (φ (ψ k)) : ℝ)) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) :=
      (hcoe.tendsto (ξ + y₀)).comp (tendsto_const_nhds.add hyt)
    have hstr : ∀ᶠ k in atTop, IsMiddleOnChord r (ξ : KnotParam)
        (((ξ + y (φ (ψ k)) : ℝ)) : KnotParam) ((mr (ψ k) : ℝ) : KnotParam) := by
      filter_upwards with k
      rw [hmrcoe (ψ k)]; exact hmc (φ (ψ k))
    exact cross_zero_of_tendsto_middle_endpoint_b hr hAne tendsto_const_nhds hb hu hstr
  · right
    have hopen : r m₀R ∈ openSegment ℝ (r ξ) (r (ξ + y₀)) :=
      segment_mem_openSegment_of_ne hseg h1 h2
    have hcol : collinearityValue r ξ (ξ + y₀) m₀R = 0 := by
      simpa [collinearityValue, collinearityMap] using cross3_eq_zero_of_mem_segment hseg
    by_cases hLI : LinearIndependent ℝ ![collPartialB r ξ (ξ + y₀) m₀R,
        collPartialM r ξ (ξ + y₀) m₀R]
    · exfalso
      obtain ⟨ε, hεpos, huniq⟩ := local_uniqueness_of_partialsBM_independent hr hcol hLI
      obtain ⟨k, hk⟩ : ∃ k : ℕ, |y (φ (ψ k)) - y₀| < ε ∧ |mr (ψ k) - m₀R| < ε := by
        have hev : ∀ᶠ k in atTop, |y (φ (ψ k)) - y₀| < ε ∧ |mr (ψ k) - m₀R| < ε := by
          filter_upwards [hyt.eventually (Metric.ball_mem_nhds y₀ hεpos),
            hmψ.eventually (Metric.ball_mem_nhds m₀R hεpos)] with k hk1 hk2
          rw [Real.dist_eq] at hk1 hk2
          exact ⟨hk1, hk2⟩
        exact hev.exists
      have hcolk : collinearityValue r ξ (ξ + y (φ (ψ k))) (mr (ψ k)) = 0 := by
        simpa [collinearityValue, collinearityMap] using mem_openSegment_cross3 (hmidreal k)
      have hres := huniq (y (φ (ψ k))) (mr (ψ k)) (by simpa using hk.1) hk.2 hcolk
      exact hyne (φ (ψ k)) (by simpa using hres.1)
    · exact ⟨ξ + y₀, m₀R, by linarith, by linarith, hcol, hopen, hLI⟩

end

end Work.Drive
