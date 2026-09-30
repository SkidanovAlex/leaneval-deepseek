import Mathlib
import Submission.Work.BW.vaalerAvgBox
import Submission.Work.BW.vaalerInner_measurable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Filter
open scoped Topology Pointwise symmDiff

noncomputable section

/-- The closed cube `[-1/2, 1/2]^N` in `ℝ^N`. -/
def cube (N : ℕ) : Set (Fin N → ℝ) := Set.Icc (fun _ => -(1/2 : ℝ)) (fun _ => (1/2 : ℝ))

lemma mem_cube {N : ℕ} {w : Fin N → ℝ} : w ∈ cube N ↔ ∀ i, |w i| ≤ 1/2 := by
  simp only [cube, Set.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact abs_le.mpr ⟨h1 i, h2 i⟩
  · intro h
    exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

lemma isClosed_cube (N : ℕ) : IsClosed (cube N) := isClosed_Icc

lemma measurableSet_cube (N : ℕ) : MeasurableSet (cube N) := (isClosed_cube N).measurableSet

lemma isCompact_cube (N : ℕ) : IsCompact (cube N) := isCompact_Icc

lemma smul_cube_subset {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : r • cube N ⊆ cube N := by
  intro w hw
  rw [Set.mem_smul_set] at hw
  obtain ⟨c, hc, rfl⟩ := hw
  rw [mem_cube] at hc ⊢
  intro i
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr0]
  calc r * |c i| ≤ 1 * (1 / 2) := mul_le_mul hr1 (hc i) (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := by norm_num

lemma cube_add_closedBall_subset {N : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    cube N + Metric.closedBall 0 r ⊆ (1 + 2 * r) • cube N := by
  have hpos : (0 : ℝ) < 1 + 2 * r := by linarith
  intro u hu
  rw [Set.mem_add] at hu
  obtain ⟨c, hc, b, hb, rfl⟩ := hu
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hb
  rw [Set.mem_smul_set]
  refine ⟨(1 + 2 * r)⁻¹ • (c + b), ?_, ?_⟩
  · rw [mem_cube]
    intro i
    have h1 : |c i| ≤ 1 / 2 := (mem_cube.mp hc) i
    have h2 : |b i| ≤ r := by
      have h3 := norm_le_pi_norm b i
      rw [Real.norm_eq_abs] at h3
      linarith
    have hsum : |c i + b i| ≤ 1 / 2 + r := by
      calc |c i + b i| ≤ |c i| + |b i| := by simpa only [Real.norm_eq_abs] using norm_add_le (c i) (b i)
        _ ≤ 1 / 2 + r := by linarith
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    calc (1 + 2 * r)⁻¹ * |c i + b i| ≤ (1 + 2 * r)⁻¹ * (1 / 2 + r) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)
      _ = 1 / 2 := by
          have hh : (1 / 2 + r) = (1 + 2 * r) * (1 / 2) := by ring
          rw [hh, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]

lemma mulVec_smul {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (r : ℝ) (x : Fin k → ℝ) :
    B.mulVec (r • x) = r • B.mulVec x := by
  rw [← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply, map_smul]

lemma continuous_mulVec {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) :
    Continuous (fun x : Fin k → ℝ => B.mulVec x) := by
  rw [show (fun x : Fin k → ℝ => B.mulVec x) = fun x => Matrix.mulVecLin B x from by
        ext x; rw [Matrix.mulVecLin_apply]]
  exact (Matrix.mulVecLin B).continuous_of_finiteDimensional

lemma preimage_smul_cube {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) {r : ℝ} (hr : 0 < r) :
    B.mulVec ⁻¹' (r • cube n) = r • (B.mulVec ⁻¹' cube n) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set]
  constructor
  · rintro ⟨c, hc, hxc⟩
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · rw [mulVec_smul, ← hxc, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
      exact hc
    · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  · rintro ⟨y, hy, hry⟩
    exact ⟨B.mulVec y, hy, by rw [← hry, mulVec_smul]⟩

lemma measureReal_smul {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (s : Set (Fin k → ℝ)) :
    (volume : Measure (Fin k → ℝ)).real (r • s) = r^k * (volume : Measure (Fin k → ℝ)).real s := by
  rw [Measure.real_def, Measure.real_def]
  rw [Measure.addHaar_smul_of_nonneg (volume : Measure (Fin k → ℝ)) hr]
  have hfr : Module.finrank ℝ (Fin k → ℝ) = k := by simp
  rw [hfr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr k)]

lemma measure_preimage_lt_top {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (hB : B.transpose * B = 1)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    (volume : Measure (Fin k → ℝ)) (B.mulVec ⁻¹' K) ≠ ⊤ := by
  have hsub : B.mulVec ⁻¹' K ⊆ B.transpose.mulVec '' K := by
    intro x hx
    exact ⟨B.mulVec x, hx, by rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]⟩
  have hcomp : IsCompact (B.transpose.mulVec '' K) := hK.image (continuous_mulVec B.transpose)
  exact ne_top_of_le_ne_top hcomp.measure_lt_top.ne (measure_mono hsub)

lemma isCompact_shift_cube {N : ℕ} (z : Fin N → ℝ) :
    IsCompact {u : Fin N → ℝ | u + z ∈ cube N} := by
  have h : {u : Fin N → ℝ | u + z ∈ cube N} = (fun v : Fin N → ℝ => v - z) '' cube N := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hu; exact ⟨u + z, hu, by simp⟩
    · rintro ⟨v, hv, rfl⟩; simpa using hv
  rw [h]
  exact (isCompact_cube N).image (by continuity)

lemma symmDiff_shift_cube_subset {N : ℕ} {z : Fin N → ℝ} (hz : 0 < ‖z‖) (hz4 : ‖z‖ < 1/4) :
    {u : Fin N → ℝ | u + z ∈ cube N} ∆ cube N
      ⊆ (cube N + Metric.closedBall 0 ‖z‖) \ ((1 - 4 * ‖z‖) • cube N) := by
  intro u hu
  rw [Set.mem_symmDiff] at hu
  simp only [Set.mem_setOf_eq] at hu
  obtain (⟨huSh, huc⟩ | ⟨huc, huSh⟩) := hu
  · refine ⟨?_, ?_⟩
    · rw [Set.mem_add]
      exact ⟨u + z, huSh, -z, by rw [Metric.mem_closedBall, dist_eq_norm]; simp, by simp⟩
    · intro hQ
      exact huc (smul_cube_subset (by linarith [hz4]) (by linarith [hz]) hQ)
  · refine ⟨?_, ?_⟩
    · rw [Set.mem_add]
      exact ⟨u, huc, 0, by rw [Metric.mem_closedBall]; simp, by simp⟩
    · intro hQ
      apply huSh
      rw [Set.mem_smul_set] at hQ
      obtain ⟨c, hc, hcu⟩ := hQ
      rw [mem_cube]
      intro i
      have h4 : 0 ≤ 1 - 4 * ‖z‖ := by linarith [hz4]
      have h1 : |u i| ≤ 1 / 2 - 2 * ‖z‖ := by
        rw [← hcu, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg h4]
        calc (1 - 4 * ‖z‖) * |c i| ≤ (1 - 4 * ‖z‖) * (1 / 2) :=
              mul_le_mul_of_nonneg_left ((mem_cube.mp hc) i) h4
          _ = 1 / 2 - 2 * ‖z‖ := by ring
      have h2 : |z i| ≤ ‖z‖ := by
        have h3 := norm_le_pi_norm z i
        rwa [Real.norm_eq_abs] at h3
      calc |(u + z) i| = |u i + z i| := by rw [Pi.add_apply]
        _ ≤ |u i| + |z i| := by simpa only [Real.norm_eq_abs] using norm_add_le (u i) (z i)
        _ ≤ (1 / 2 - 2 * ‖z‖) + ‖z‖ := by linarith
        _ = 1 / 2 - ‖z‖ := by ring
        _ ≤ 1 / 2 := by linarith [hz]

lemma preimage_symmDiff_bound {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (hB : B.transpose * B = 1) {z : Fin n → ℝ} (hz : ‖z‖ < 1/4) :
    (volume : Measure (Fin k → ℝ)).real
        (symmDiff (B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n}) (B.mulVec ⁻¹' cube n))
      ≤ ((1 + 2 * ‖z‖)^k - (1 - 4 * ‖z‖)^k) *
        (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' cube n) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · have hset : B.mulVec ⁻¹' {u : Fin n → ℝ | u + 0 ∈ cube n} = B.mulVec ⁻¹' cube n := by
      simp only [add_zero, Set.setOf_mem_eq]
    rw [hset, symmDiff_self]
    simp [Measure.real_def]
  · have hzw : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hsub : {u : Fin n → ℝ | u + z ∈ cube n} ∆ cube n ⊆
        (cube n + Metric.closedBall 0 ‖z‖) \ ((1 - 4 * ‖z‖) • cube n) :=
      symmDiff_shift_cube_subset hzw hz
    have hPcomp : IsCompact (cube n + Metric.closedBall 0 ‖z‖) :=
      (isCompact_cube n).add (isCompact_closedBall (0 : Fin n → ℝ) ‖z‖)
    have hPfin : (volume : Measure (Fin k → ℝ))
        (B.mulVec ⁻¹' (cube n + Metric.closedBall 0 ‖z‖)) ≠ ⊤ :=
      measure_preimage_lt_top B hB hPcomp
    have hQclosed : IsClosed ((1 - 4 * ‖z‖) • cube n) :=
      (isCompact_cube n).smul _ |>.isClosed
    have hQsubP : (1 - 4 * ‖z‖) • cube n ⊆ cube n + Metric.closedBall 0 ‖z‖ :=
      (fun u hu => by
        rw [Set.mem_add]
        exact ⟨u, smul_cube_subset (r := 1 - 4 * ‖z‖) (by linarith [hz]) (by linarith [norm_nonneg z]) hu, 0, by simp [Metric.mem_closedBall],
          by simp⟩)
    have hPbound : (volume : Measure (Fin k → ℝ)).real
          (B.mulVec ⁻¹' (cube n + Metric.closedBall 0 ‖z‖))
        ≤ (1 + 2 * ‖z‖)^k * (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' cube n) := by
      have h1 : (volume : Measure (Fin k → ℝ)).real
            (B.mulVec ⁻¹' (cube n + Metric.closedBall 0 ‖z‖))
          ≤ (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' ((1 + 2 * ‖z‖) • cube n)) :=
        measureReal_mono (Set.preimage_mono (cube_add_closedBall_subset (norm_nonneg z)))
          (measure_preimage_lt_top B hB ((isCompact_cube n).smul _))
      rw [preimage_smul_cube B (by positivity : (0:ℝ) < 1 + 2*‖z‖),
          measureReal_smul (by positivity : (0:ℝ) ≤ 1 + 2*‖z‖)] at h1
      exact h1
    have hQeq : (volume : Measure (Fin k → ℝ)).real
          (B.mulVec ⁻¹' ((1 - 4 * ‖z‖) • cube n))
        = (1 - 4 * ‖z‖)^k * (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' cube n) := by
      rw [preimage_smul_cube B (by linarith : (0:ℝ) < 1 - 4*‖z‖),
          measureReal_smul (by linarith : (0:ℝ) ≤ 1 - 4*‖z‖)]
    calc (volume : Measure (Fin k → ℝ)).real
            (symmDiff (B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n}) (B.mulVec ⁻¹' cube n))
        ≤ (volume : Measure (Fin k → ℝ)).real
            (B.mulVec ⁻¹' ((cube n + Metric.closedBall 0 ‖z‖) \ ((1 - 4 * ‖z‖) • cube n))) :=
          measureReal_mono (Set.preimage_mono hsub)
            (ne_top_of_le_ne_top hPfin (measure_mono (Set.preimage_mono Set.sdiff_subset)))
      _ = (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' (cube n + Metric.closedBall 0 ‖z‖))
            - (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' ((1 - 4 * ‖z‖) • cube n)) := by
          rw [Set.preimage_sdiff,
            measureReal_sdiff (Set.preimage_mono hQsubP)
              (hQclosed.preimage (continuous_mulVec B)).measurableSet hPfin]
      _ ≤ (1 + 2 * ‖z‖)^k * (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' cube n)
            - (1 - 4 * ‖z‖)^k * (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' cube n) := by
          rw [hQeq]
          exact sub_le_sub_right hPbound _
      _ = ((1 + 2 * ‖z‖)^k - (1 - 4 * ‖z‖)^k) *
            (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' cube n) := by ring

/-- `|μ.real s - μ.real t|` is bounded by the measure of the symmetric difference. -/
lemma abs_real_sub_le_real_symmDiff {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hsf : μ s ≠ ⊤) (htf : μ t ≠ ⊤) :
    |μ.real s - μ.real t| ≤ μ.real (symmDiff s t) := by
  have h1 : μ.real s = μ.real (s ∩ t) + μ.real (s \ t) :=
    (measureReal_inter_add_sdiff ht hsf).symm
  have h2 : μ.real t = μ.real (s ∩ t) + μ.real (t \ s) := by
    have h : μ.real (t ∩ s) + μ.real (t \ s) = μ.real t := measureReal_inter_add_sdiff hs htf
    exact (Set.inter_comm t s ▸ h).symm
  have hd : symmDiff s t = (s \ t) ∪ (t \ s) := by
    ext x
    rw [Set.mem_symmDiff, Set.mem_union, Set.mem_sdiff, Set.mem_sdiff]
  have hdisj : Disjoint (s \ t) (t \ s) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => hx1.2 hx2.1)
  have h3 : μ.real (symmDiff s t) = μ.real (s \ t) + μ.real (t \ s) := by
    rw [hd, measureReal_union hdisj (ht.diff hs)
      (ne_top_of_le_ne_top hsf (measure_mono Set.sdiff_subset))
      (ne_top_of_le_ne_top htf (measure_mono Set.sdiff_subset))]
  have ha : 0 ≤ μ.real (s \ t) := measureReal_nonneg
  have hb : 0 ≤ μ.real (t \ s) := measureReal_nonneg
  rw [h1, h2, h3, abs_le]
  constructor <;> linarith

/-- The inner integral is the measure of the corresponding slice. -/
lemma integral_indicator_cube {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (z : Fin n → ℝ) :
    (∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + z) i| ≤ 1/2) then (1:ℝ) else 0))
      = (volume : Measure (Fin k → ℝ)).real
          (B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n}) := by
  classical
  have hmeas : MeasurableSet (B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n}) := by
    have hc : Continuous (fun x : Fin k → ℝ => B.mulVec x + z) :=
      (continuous_mulVec B).add continuous_const
    exact ((isClosed_cube n).preimage hc).measurableSet
  rw [← MeasureTheory.integral_indicator_one hmeas]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [Set.indicator_apply]
  by_cases h : (∀ i, |(B.mulVec x + z) i| ≤ 1/2)
  · have hx : x ∈ B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n} :=
      Set.mem_preimage.mpr (mem_cube.mpr h)
    rw [if_pos h, if_pos hx]
    rfl
  · have hx : x ∉ B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n} :=
      fun hc => h (mem_cube.mp (Set.mem_preimage.mp hc))
    rw [if_neg h, if_neg hx]

/-- The inner Vaaler count is continuous at `z = 0`. -/
lemma inner_continuousAt_zero {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (hB : B.transpose * B = 1) :
    ContinuousAt (fun z : Fin n → ℝ =>
      ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + z) i| ≤ 1/2) then (1:ℝ) else 0)) 0 := by
  set F : (Fin n → ℝ) → ℝ := fun z =>
      ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + z) i| ≤ 1/2) then (1:ℝ) else 0) with hF
  change ContinuousAt F 0
  rw [Metric.continuousAt_iff]
  intro ε hε
  set V : ℝ := (volume : Measure (Fin k → ℝ)).real (B.mulVec ⁻¹' cube n) with hV
  have hFz : ∀ z, F z = (volume : Measure (Fin k → ℝ)).real
      (B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n}) := by
    intro z
    rw [hF]
    exact integral_indicator_cube B z
  have hF0 : F 0 = V := by
    have hset : B.mulVec ⁻¹' {u : Fin n → ℝ | u + 0 ∈ cube n} = B.mulVec ⁻¹' cube n := by
      simp only [add_zero, Set.ofPred_mem_eq]
    rw [hFz 0, hset]
  have hlim : Tendsto (fun w : ℝ => ((1 + 2*w)^k - (1 - 4*w)^k) * V) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun w : ℝ => ((1 + 2*w)^k - (1 - 4*w)^k) * V) := by continuity
    simpa using hc.tendsto 0
  rw [Metric.tendsto_nhds] at hlim
  have hev : ∀ᶠ w : ℝ in 𝓝 0, ((1 + 2*w)^k - (1 - 4*w)^k) * V < ε := by
    filter_upwards [hlim ε hε] with w hw
    rw [Real.dist_eq, sub_zero] at hw
    exact lt_of_le_of_lt (le_abs_self _) hw
  obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min η (1/8), by positivity, ?_⟩
  intro z hz
  rw [dist_eq_norm, sub_zero] at hz
  have hzn : ‖z‖ < η := lt_of_lt_of_le hz (min_le_left _ _)
  have hz4 : ‖z‖ < 1/4 :=
    lt_of_lt_of_le (lt_of_lt_of_le hz (min_le_right _ _)) (by norm_num)
  have hmeas1 : MeasurableSet (B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n}) := by
    have hc : Continuous (fun x : Fin k → ℝ => B.mulVec x + z) :=
      (continuous_mulVec B).add continuous_const
    exact ((isClosed_cube n).preimage hc).measurableSet
  have hmeas2 : MeasurableSet (B.mulVec ⁻¹' cube n) :=
    ((isClosed_cube n).preimage (continuous_mulVec B)).measurableSet
  have hfin1 : (volume : Measure (Fin k → ℝ))
      (B.mulVec ⁻¹' {u : Fin n → ℝ | u + z ∈ cube n}) ≠ ⊤ :=
    measure_preimage_lt_top B hB (isCompact_shift_cube z)
  have hfin2 : (volume : Measure (Fin k → ℝ)) (B.mulVec ⁻¹' cube n) ≠ ⊤ :=
    measure_preimage_lt_top B hB (isCompact_cube n)
  have hbound : |F z - F 0| ≤ ((1 + 2*‖z‖)^k - (1 - 4*‖z‖)^k) * V := by
    rw [hFz z, hF0, hV]
    exact (abs_real_sub_le_real_symmDiff hmeas1 hmeas2 hfin1 hfin2).trans
      (preimage_symmDiff_bound B hB hz4)
  have hlt : ((1 + 2*‖z‖)^k - (1 - 4*‖z‖)^k) * V < ε := by
    apply hη
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg z)]
    exact hzn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hbound hlt

theorem vaalerTubeLimit {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (hB : B.transpose * B = 1)
    (Bp : Matrix (Fin n) (Fin (n-k)) ℝ) (hBp : Bp.transpose * Bp = 1) (hBBp : B.transpose * Bp = 0)
    (hk : k ≤ n) :
    Filter.Tendsto
      (fun δ : ℝ => (1/δ^(n-k)) * ∫ y in Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)),
        ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x) i| ≤ 1/2) then (1:ℝ) else 0))) := by
  have hmeas : Measurable (fun y : Fin (n-k) → ℝ =>
      ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0)) :=
    vaalerInner_measurable B Bp
  have hcont : ContinuousAt (fun y : Fin (n-k) → ℝ =>
      ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0)) 0 := by
    have hg : ContinuousAt (fun z : Fin n → ℝ =>
        ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + z) i| ≤ 1/2) then (1:ℝ) else 0)) 0 :=
      inner_continuousAt_zero B hB
    have hg' : ContinuousAt (fun z : Fin n → ℝ =>
        ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + z) i| ≤ 1/2) then (1:ℝ) else 0))
        ((fun y : Fin (n-k) → ℝ => Bp.mulVec y) 0) := by
      simpa only [Matrix.mulVec_zero] using hg
    exact hg'.comp (continuous_mulVec Bp).continuousAt
  have hRHS : (∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x) i| ≤ 1/2) then (1:ℝ) else 0))
      = (fun y : Fin (n-k) → ℝ =>
          ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0)) 0 := by
    simp [Matrix.mulVec_zero]
  rw [hRHS]
  exact vaalerAvgBox _ hcont hmeas

end

end Work.BW
