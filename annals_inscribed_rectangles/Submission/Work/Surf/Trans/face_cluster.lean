import Mathlib
import Submission.Work.Surf.transfer_defs

/-!
# The face-ray set is the limit of the `δ`-neighbourhood of the closed ray

`Work.Surf.Trans.face_cluster` is the elementary compactness statement behind the persistence of the
boundary ray-meeting data of `Work.Surf.Trans.face_persist`: for a `C¹` map `F` which does not vanish
on the boundary of the unit square and a direction `v ≠ 0`, the parameters `t` of the `i`-th face at
which `F (facePt i t)` is within `δ` of the closed ray `{r • v : 0 ≤ r}` are within `ε` of a parameter
at which `F (facePt i t)` lies on the *open* ray `{r • v : 0 < r}`, as soon as `δ` is small.

The reason is that `F` is bounded below in norm on the boundary of the square, so the hypothesis
forces the *direction* `F (facePt i t)/‖F (facePt i t)‖` to be close to `v/‖v‖`, and the parameters
where the direction equals `v/‖v‖` are exactly the ray-meeting parameters.
-/

namespace Work.Surf.Trans

open Set Metric
open scoped Topology

noncomputable section

/-- A strictly positive continuous function on a compact set has a positive lower bound; this is the
`ContinuousOn` version of `exists_pos_le_of_isCompact_of_pos`. -/
lemma exists_pos_le_of_isCompact_of_continuousOn_pos {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} {K : Set α} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x, hpos x hxK, fun t ht => hxmin ht⟩

/-- **The angular estimate.**  If `w` has norm at least `m > 0` and its determinant against `v` is at
most `δ` while its inner product with `v` is at least `-δ`, then the unit vectors `w/‖w‖` and
`v/‖v‖` differ by at most `2 δ/(m ‖v‖)`. -/
lemma norm_unit_smul_sub_le (w v : E2) {m δ : ℝ} (hm : 0 < m) (hv : v ≠ 0) (hδ : 0 ≤ δ)
    (hw : m ≤ ‖w‖) (hs : δ / (m * ‖v‖) ≤ 1 / 2)
    (he : |Work.Drive.det2 w v| ≤ δ) (hc : -δ ≤ inner ℝ w v) :
    ‖(‖w‖)⁻¹ • w - (‖v‖)⁻¹ • v‖ ≤ 2 * (δ / (m * ‖v‖)) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hm hw
  have hmvpos : 0 < m * ‖v‖ := mul_pos hm hvpos
  set s : ℝ := δ / (m * ‖v‖) with hsdef
  have hspos : 0 ≤ s := div_nonneg hδ hmvpos.le
  have hs_le : s ≤ 1 / 2 := by rw [hsdef]; exact hs
  have hs2le : s ^ 2 ≤ 1 / 4 := by
    have h := mul_le_mul hs_le hs_le hspos (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith [h]
  set u : E2 := (‖w‖)⁻¹ • w with hudef
  set z : E2 := (‖v‖)⁻¹ • v with hzdef
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos),
      inv_mul_cancel₀ hwpos.ne']
  have hznorm : ‖z‖ = 1 := by
    rw [hzdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos),
      inv_mul_cancel₀ hvpos.ne']
  have hident : inner ℝ u z ^ 2 + Work.Drive.det2 u z ^ 2 = 1 := by
    have h := inner_sq_add_det2_sq u z
    rw [hunorm, hznorm] at h
    simpa using h
  have hdet_abs : |Work.Drive.det2 u z| ≤ s := by
    have hdetu : Work.Drive.det2 u z = (‖w‖)⁻¹ * (‖v‖)⁻¹ * Work.Drive.det2 w v := by
      rw [hudef, hzdef]
      simp only [Work.Drive.det2, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hdetu, hsdef]
    have heabs : (‖w‖)⁻¹ * (‖v‖)⁻¹ * |Work.Drive.det2 w v| ≤ (‖w‖)⁻¹ * (‖v‖)⁻¹ * δ :=
      mul_le_mul_of_nonneg_left he (by positivity)
    have h2 : (‖w‖)⁻¹ ≤ m⁻¹ := inv_anti₀ hm hw
    have h3 : (‖w‖)⁻¹ * (‖v‖)⁻¹ * δ ≤ m⁻¹ * (‖v‖)⁻¹ * δ := by
      have ha := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (‖v‖)⁻¹)
      nlinarith [ha]
    have h4 : m⁻¹ * (‖v‖)⁻¹ * δ = δ / (m * ‖v‖) := by
      field_simp
    calc |(‖w‖)⁻¹ * (‖v‖)⁻¹ * Work.Drive.det2 w v|
        = (‖w‖)⁻¹ * (‖v‖)⁻¹ * |Work.Drive.det2 w v| := by
          rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hwpos), abs_of_pos (inv_pos.mpr hvpos)]
      _ ≤ (‖w‖)⁻¹ * (‖v‖)⁻¹ * δ := heabs
      _ ≤ m⁻¹ * (‖v‖)⁻¹ * δ := h3
      _ = δ / (m * ‖v‖) := h4
  have hinner_lb : -s ≤ inner ℝ u z := by
    have hinneru : inner ℝ u z = (‖w‖)⁻¹ * (‖v‖)⁻¹ * inner ℝ w v := by
      rw [hudef, hzdef, inner_smul_left, inner_smul_right]
      simp only [RCLike.conj_to_real]
      ring
    rw [hinneru, hsdef]
    have h2 : (‖w‖)⁻¹ ≤ m⁻¹ := inv_anti₀ hm hw
    have h6 : (‖w‖)⁻¹ * (‖v‖)⁻¹ * (-δ) ≤ (‖w‖)⁻¹ * (‖v‖)⁻¹ * inner ℝ w v :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have h7 : m⁻¹ * (‖v‖)⁻¹ * (-δ) ≤ (‖w‖)⁻¹ * (‖v‖)⁻¹ * (-δ) := by
      have ha := mul_le_mul_of_nonpos_right h2 (by linarith : -δ ≤ 0)
      have hb := mul_le_mul_of_nonneg_right ha (by positivity : (0 : ℝ) ≤ (‖v‖)⁻¹)
      calc m⁻¹ * (‖v‖)⁻¹ * (-δ) = (m⁻¹ * (-δ)) * (‖v‖)⁻¹ := by ring
        _ ≤ ((‖w‖)⁻¹ * (-δ)) * (‖v‖)⁻¹ := hb
        _ = (‖w‖)⁻¹ * (‖v‖)⁻¹ * (-δ) := by ring
    have h8 : m⁻¹ * (‖v‖)⁻¹ * (-δ) = -(δ / (m * ‖v‖)) := by
      field_simp
    linarith
  have hkey : ‖u - z‖ ≤ 2 * s := by
    have he_sq : Work.Drive.det2 u z ^ 2 ≤ s ^ 2 := by
      have h1 : |Work.Drive.det2 u z| ≤ |s| := by
        rw [abs_of_nonneg hspos]; exact hdet_abs
      exact (sq_le_sq).mpr h1
    have ha_sq : 1 - s ^ 2 ≤ inner ℝ u z ^ 2 := by nlinarith [hident]
    have hnn : 0 ≤ 1 - s ^ 2 := by nlinarith [hs2le]
    have ha_nonneg : 0 ≤ inner ℝ u z := by
      by_contra h
      push_neg at h
      have h2 : inner ℝ u z ^ 2 ≤ s ^ 2 := by
        have h3 : |inner ℝ u z| ≤ |s| := by
          rw [abs_of_neg h, abs_of_nonneg hspos]
          linarith [hinner_lb]
        exact (sq_le_sq).mpr h3
      nlinarith [ha_sq, h2, hs2le]
    have ha_ge : 1 - 2 * s ^ 2 ≤ inner ℝ u z := by
      have hsqrt : Real.sqrt (1 - s ^ 2) ≤ inner ℝ u z := by
        have h1 : (Real.sqrt (1 - s ^ 2)) ^ 2 ≤ inner ℝ u z ^ 2 := by
          rw [Real.sq_sqrt hnn]; exact ha_sq
        have h2 := (sq_le_sq).mp h1
        rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg ha_nonneg] at h2
      have h3 : 1 - s ^ 2 ≤ Real.sqrt (1 - s ^ 2) := by
        refine (Real.le_sqrt hnn hnn).mpr ?_
        have h4 : 1 - s ^ 2 ≤ 1 := by linarith [sq_nonneg s]
        have h5 : (1 - s ^ 2) * (1 - s ^ 2) ≤ 1 * (1 - s ^ 2) :=
          mul_le_mul_of_nonneg_right h4 hnn
        nlinarith [h5]
      linarith [h3, hsqrt, sq_nonneg s]
    have hnorm_sq : ‖u - z‖ ^ 2 = 2 - 2 * inner ℝ u z := by
      rw [norm_sub_sq_real, hunorm, hznorm]
      ring
    have hfin : ‖u - z‖ ^ 2 ≤ (2 * s) ^ 2 := by
      rw [hnorm_sq]; nlinarith [ha_ge]
    calc ‖u - z‖ = Real.sqrt (‖u - z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((2 * s) ^ 2) := Real.sqrt_le_sqrt hfin
      _ = 2 * s := Real.sqrt_sq (by linarith [hspos])
  simpa [hudef, hzdef, hsdef] using hkey

theorem face_cluster (F : E2 → E2) (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ sqBdry, F x ≠ 0) {v : E2} (hv : v ≠ 0) (i : Fin 4)
    (hfin : (FaceRaySet F v i).Finite) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc 0 1, |Work.Drive.det2 (F (facePt i t)) v| ≤ δ →
      -δ ≤ inner ℝ (F (facePt i t)) v → ∃ p ∈ FaceRaySet F v i, |t - p| < ε := by
  intro ε hε
  have hFc : Continuous F := hF.continuous
  -- The boundary of the square is compact.
  have hsqBdry_eq : sqBdry = ⋃ i : Fin 4, facePt i '' Set.Icc 0 1 := by
    refine Subset.antisymm sqBdry_subset_iUnion_face ?_
    refine iUnion_subset fun i => image_subset_iff.mpr fun t ht => facePt_mem_sqBdry i ht
  have hcomp : IsCompact sqBdry := by
    rw [hsqBdry_eq]
    exact isCompact_iUnion fun i => isCompact_Icc.image (continuous_facePt i)
  obtain ⟨m, hmpos, hm⟩ := exists_pos_le_of_isCompact_of_continuousOn_pos hcomp
    hFc.continuousOn.norm (fun x hx => norm_pos_iff.mpr (hbdry x hx))
  have hmface : ∀ t ∈ Set.Icc 0 1, m ≤ ‖F (facePt i t)‖ :=
    fun t ht => hm _ (facePt_mem_sqBdry i ht)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set S : Set ℝ := FaceRaySet F v i with hSdef
  set U : Set ℝ := ⋃ p ∈ S, Metric.ball p ε with hUdef
  have hUopen : IsOpen U := isOpen_biUnion fun p _ => Metric.isOpen_ball
  have hKcomp : IsCompact (Set.Icc 0 1 \ U) := isCompact_Icc.diff hUopen
  have hw_cont : ContinuousOn (fun t : ℝ => F (facePt i t)) (Set.Icc 0 1) :=
    (hFc.comp (continuous_facePt i)).continuousOn
  have hnorm_cont : ContinuousOn (fun t : ℝ => ‖F (facePt i t)‖) (Set.Icc 0 1) := hw_cont.norm
  have hnorm_ne : ∀ t ∈ Set.Icc 0 1, ‖F (facePt i t)‖ ≠ 0 :=
    fun t ht => norm_ne_zero_iff.mpr (hbdry _ (facePt_mem_sqBdry i ht))
  have hunit_cont : ContinuousOn (fun t : ℝ => (‖F (facePt i t)‖)⁻¹ • F (facePt i t))
      (Set.Icc 0 1) := (hnorm_cont.inv₀ hnorm_ne).smul hw_cont
  have hd_cont : ContinuousOn
      (fun t : ℝ => ‖(‖F (facePt i t)‖)⁻¹ • F (facePt i t) - (‖v‖)⁻¹ • v‖) (Set.Icc 0 1) :=
    (hunit_cont.sub continuousOn_const).norm
  have hd_eq : ∀ t ∈ Set.Icc 0 1,
      ‖(‖F (facePt i t)‖)⁻¹ • F (facePt i t) - (‖v‖)⁻¹ • v‖ = 0 ↔ t ∈ S := by
    intro t ht
    constructor
    · intro h0
      have h1 : (‖F (facePt i t)‖)⁻¹ • F (facePt i t) = (‖v‖)⁻¹ • v :=
        sub_eq_zero.mp (norm_eq_zero.mp h0)
      have h2 : F (facePt i t) = (‖F (facePt i t)‖ * (‖v‖)⁻¹) • v := by
        have h := congrArg (fun z : E2 => ‖F (facePt i t)‖ • z) h1
        rw [smul_smul, mul_inv_cancel₀ (hnorm_ne t ht), one_smul] at h
        rw [smul_smul] at h
        exact h
      rw [hSdef]
      exact ⟨ht, ‖F (facePt i t)‖ * (‖v‖)⁻¹,
        mul_pos (norm_pos_iff.mpr (hbdry _ (facePt_mem_sqBdry i ht))) (inv_pos.mpr hvpos), h2⟩
    · intro htS
      rw [hSdef] at htS
      obtain ⟨-, r, hr, hrEq⟩ := htS
      have hnormr : ‖F (facePt i t)‖ = r * ‖v‖ := by
        rw [hrEq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have hcoef : (r * ‖v‖)⁻¹ * r = (‖v‖)⁻¹ := by
        field_simp
      rw [hnormr, hrEq, smul_smul, hcoef, sub_self, norm_zero]
  have hKpos : ∀ t ∈ Set.Icc 0 1 \ U,
      0 < ‖(‖F (facePt i t)‖)⁻¹ • F (facePt i t) - (‖v‖)⁻¹ • v‖ := by
    intro t ht
    obtain ⟨htIcc, htU⟩ := ht
    rcases (norm_nonneg ((‖F (facePt i t)‖)⁻¹ • F (facePt i t) - (‖v‖)⁻¹ • v)).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have hzero : ‖(‖F (facePt i t)‖)⁻¹ • F (facePt i t) - (‖v‖)⁻¹ • v‖ = 0 := h.symm
      have htS : t ∈ S := (hd_eq t htIcc).mp hzero
      exact htU (mem_iUnion₂.mpr ⟨t, htS, Metric.mem_ball_self hε⟩)
  obtain ⟨s', hs'pos, hs'le⟩ := exists_pos_le_of_isCompact_of_continuousOn_pos hKcomp
    (hd_cont.mono fun t ht => ht.1) hKpos
  have hmin : 0 < min (s' / 3) (1 / 4) := lt_min (by linarith) (by norm_num)
  have hδpos : 0 < m * ‖v‖ * min (s' / 3) (1 / 4) := mul_pos (mul_pos hmpos hvpos) hmin
  refine ⟨m * ‖v‖ * min (s' / 3) (1 / 4), hδpos, ?_⟩
  intro t htIcc hdet hinn
  by_contra hcon
  push_neg at hcon
  have hquot : m * ‖v‖ * min (s' / 3) (1 / 4) / (m * ‖v‖) = min (s' / 3) (1 / 4) := by
    field_simp
  have hsbound : m * ‖v‖ * min (s' / 3) (1 / 4) / (m * ‖v‖) ≤ 1 / 2 := by
    rw [hquot]
    linarith [min_le_right (s' / 3) (1 / 4)]
  have hle := norm_unit_smul_sub_le (F (facePt i t)) v hmpos hv hδpos.le (hmface t htIcc)
    hsbound hdet hinn
  have htwo : 2 * (m * ‖v‖ * min (s' / 3) (1 / 4) / (m * ‖v‖)) < s' := by
    rw [hquot]
    linarith [min_le_left (s' / 3) (1 / 4)]
  have htK : t ∈ Set.Icc 0 1 \ U := by
    refine ⟨htIcc, ?_⟩
    intro htU
    obtain ⟨p, hpS, hpb⟩ := mem_iUnion₂.mp htU
    have hdist : dist t p < ε := Metric.mem_ball.mp hpb
    rw [dist_eq_norm, Real.norm_eq_abs] at hdist
    exact absurd hdist (not_lt.mpr (hcon p hpS))
  have hlb : s' ≤ ‖(‖F (facePt i t)‖)⁻¹ • F (facePt i t) - (‖v‖)⁻¹ • v‖ := hs'le t htK
  linarith [hlb, hle, htwo]

end

end Work.Surf.Trans
