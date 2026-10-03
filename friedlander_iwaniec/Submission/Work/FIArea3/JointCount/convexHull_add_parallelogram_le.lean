import Mathlib
import Submission.Work.FIArea3.JointCount.sharp_defs
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count
import Submission.Work.FIArea3.JointCount.diam_annSector_le
import Submission.Work.FIArea3.JointCount.sweep_defs
import Submission.Work.FIArea3.JointCount.convex_sweep_volume

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. Linearity of `wid` -/

lemma wid_add (z a b : ℂ) : wid z (a + b) = wid z a + wid z b := by
  simp only [wid, Complex.add_re, Complex.add_im]
  ring

lemma wid_smul (z : ℂ) (t : ℝ) (a : ℂ) : wid z (t • a) = t * wid z a := by
  simp only [wid, Complex.smul_re, Complex.smul_im]
  ring

/-- `wid z` as an `ℝ`-linear functional. -/
def widLin (z : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun := wid z
  map_add' a b := wid_add z a b
  map_smul' t a := by rw [wid_smul]; rfl

/-! ## 2. The segment `segz` -/

lemma convex_segz (z : ℂ) : Convex ℝ (segz z) := by
  rw [segz]
  intro x hx y hy a b ha hb hab
  obtain ⟨tx, htx, rfl⟩ := hx
  obtain ⟨ty, hty, rfl⟩ := hy
  refine ⟨a * tx + b * ty, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [mul_nonneg ha htx.1, mul_nonneg hb hty.1]
  · nlinarith [mul_le_mul_of_nonneg_left htx.2 ha, mul_le_mul_of_nonneg_left hty.2 hb]
  · rw [smul_smul, smul_smul, ← add_smul]

lemma isBounded_segz (z : ℂ) : Bornology.IsBounded (segz z) := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr ⟨‖z‖, ?_⟩
  rintro w ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs]
  calc |t| * ‖z‖ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) (norm_nonneg z)
    _ = ‖z‖ := one_mul _

/-- A point of the segment from `0` to `a`, pushed forward by the linear functional `wid z`,
lands in the segment from `0` to `wid z a`. -/
lemma wid_smul_mem_uIcc (z a : ℂ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    wid z (t • a) ∈ Set.uIcc 0 (wid z a) := by
  rw [wid_smul, Set.mem_uIcc]
  by_cases h : 0 ≤ wid z a
  · exact Or.inl ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · push_neg at h
    exact Or.inr ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

/-! ## 3. The fundamental parallelogram of `Llc g₁ g₂` -/

lemma Llc_uCell_subset_tsh (g₁ g₂ : ℂ) :
    Llc g₁ g₂ '' uCell ⊆
      tsh (-(g₁ + g₂) / 2) (Set.image2 (· + ·) (segz g₁) (segz g₂)) := by
  intro w hw
  obtain ⟨q, hq, rfl⟩ := hw
  obtain ⟨h1, h2, h3, h4⟩ := (mem_uCell q).mp hq
  rw [mem_tsh]
  refine ⟨(q.re + 1 / 2) • g₁ + (q.im + 1 / 2) • g₂, ?_, ?_⟩
  · refine ⟨(q.re + 1 / 2) • g₁, ?_, (q.im + 1 / 2) • g₂, ?_, rfl⟩
    · exact ⟨q.re + 1 / 2, ⟨by linarith, by linarith⟩, rfl⟩
    · exact ⟨q.im + 1 / 2, ⟨by linarith, by linarith⟩, rfl⟩
  · rw [Llc_apply]
    simp only [Complex.real_smul]
    push_cast
    ring

/-! ## 4. Sweeping a convex set by a segment -/

/-- The exact volume of the Minkowski sum of a bounded convex set with a segment. -/
theorem sweep_image2_eq (K : Set ℂ) (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) (z : ℂ) :
    volume (Set.image2 (· + ·) K (segz z)) = volume K + volume (wid z '' K) := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    have hseg : segz 0 = {0} := by
      ext w
      constructor
      · rintro ⟨t, ht, rfl⟩
        simp
      · intro hw
        exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simpa using hw⟩
    have hK0 : Set.image2 (· + ·) K (segz 0) = K := by
      rw [hseg]
      ext x
      constructor
      · rintro ⟨k, hk, e, rfl, rfl⟩
        simpa using hk
      · intro hx
        exact ⟨x, hx, 0, rfl, by simp⟩
    have hwid : wid 0 '' K ⊆ {0} := by
      rintro v ⟨w, hw, rfl⟩
      simp [wid]
    have hwid0 : volume (wid 0 '' K) = 0 := measure_mono_null hwid (by simp)
    rw [hK0, hwid0, add_zero]
  · have hZK_conv : Convex ℝ (hmap z '' K) := hK.linear_image (hmap z)
    have hZK_bd : Bornology.IsBounded (hmap z '' K) := isBounded_hmap z hKb
    have himg : Complex.im '' (hmap z '' K) = wid z '' K := by
      rw [Set.image_image]
      exact congrArg (fun f : ℂ → ℝ => f '' K) (funext fun v => hmap_im z v)
    calc volume (Set.image2 (· + ·) K (segz z))
        = volume (K + segz z) := rfl
      _ = volume (hmap z '' (K + segz z)) := (volume_image_hmap z hz (K + segz z)).symm
      _ = volume (hmap z '' K + hmap z '' segz z) := by rw [image_add_linear]
      _ = volume (hmap z '' K + unitSeg) := by rw [hmap_image_segz z hz]
      _ = volume (hmap z '' K) + volume (Complex.im '' (hmap z '' K)) :=
          volume_add_unitSeg _ hZK_conv hZK_bd
      _ = volume K + volume (wid z '' K) := by rw [himg, volume_image_hmap z hz K]

/-! ## 5. The volume of the projection of `K` onto the direction `z * I` -/

lemma wid_image_volume_le_aux (K : Set ℂ) (hKb : Bornology.IsBounded K) (z : ℂ) :
    volume (wid z '' K) ≤ ENNReal.ofReal (‖z‖ * Metric.diam K) := by
  have hediam : Metric.ediam K = ENNReal.ofReal (Metric.diam K) := by
    rw [Metric.diam, ENNReal.ofReal_toReal hKb.ediam_ne_top]
  calc volume (wid z '' K) ≤ Metric.ediam (wid z '' K) := Real.volume_le_diam _
    _ ≤ (‖z‖₊ : ℝ≥0∞) * Metric.ediam K := (lipschitz_wid z).ediam_image_le K
    _ = ENNReal.ofReal (‖z‖ * Metric.diam K) := by
        rw [hediam, ← ENNReal.ofReal_coe_nnreal (p := ‖z‖₊),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (↑(‖z‖₊) : ℝ) from by positivity)]
        congr 1

/-! ## 6. Adding a segment to an interval of `ℝ` -/

lemma uIcc_bounds {b c : ℝ} (h : b ∈ Set.uIcc 0 c) : min 0 c ≤ b ∧ b ≤ max 0 c := by
  rw [Set.mem_uIcc] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_left _ _)⟩

lemma interval_add_segment_volume_le_aux (I : Set ℝ) (hI : Convex ℝ I)
    (hIb : Bornology.IsBounded I) (c : ℝ) :
    volume (Set.image2 (· + ·) I (Set.uIcc 0 c)) ≤ volume I + ENNReal.ofReal |c| := by
  rcases Set.eq_empty_or_nonempty I with h | hne
  · subst h
    simp
  · have hsub : Set.image2 (· + ·) I (Set.uIcc 0 c)
        ⊆ Set.Icc (sInf I + min 0 c) (sSup I + max 0 c) := by
      rintro x ⟨a, ha, b, hb, rfl⟩
      obtain ⟨hb1, hb2⟩ := uIcc_bounds hb
      rw [Set.mem_Icc]
      exact ⟨add_le_add (csInf_le hIb.bddBelow ha) hb1, add_le_add (le_csSup hIb.bddAbove ha) hb2⟩
    have hle : sInf I ≤ sSup I :=
      le_trans (csInf_le hIb.bddBelow hne.some_mem) (le_csSup hIb.bddAbove hne.some_mem)
    have hminmax : sSup I + max 0 c - (sInf I + min 0 c) = (sSup I - sInf I) + |c| := by
      by_cases hc : 0 ≤ c
      · rw [min_eq_left hc, max_eq_right hc, abs_of_nonneg hc]; ring
      · push_neg at hc
        rw [min_eq_right hc.le, max_eq_left hc.le, abs_of_neg hc]; ring
    calc volume (Set.image2 (· + ·) I (Set.uIcc 0 c))
        ≤ volume (Set.Icc (sInf I + min 0 c) (sSup I + max 0 c)) := measure_mono hsub
      _ = ENNReal.ofReal (sSup I + max 0 c - (sInf I + min 0 c)) := Real.volume_Icc
      _ = ENNReal.ofReal ((sSup I - sInf I) + |c|) := by rw [hminmax]
      _ = ENNReal.ofReal (sSup I - sInf I) + ENNReal.ofReal |c| :=
          ENNReal.ofReal_add (sub_nonneg.mpr hle) (abs_nonneg c)
      _ = volume I + ENNReal.ofReal |c| := by rw [convex_volume_eq I hI hne hIb]

/-! ## 7. Adding a parallelogram -/

lemma add_reassoc (a b c d : ENNReal) : (a + b) + (c + d) = a + ((b + c) + d) := by
  simp only [add_assoc, add_left_comm, add_comm]

theorem add_parallelogram_volume_le_aux (K : Set ℂ) (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (g₁ g₂ : ℂ) :
    volume (Set.image2 (· + ·) K (Llc g₁ g₂ '' uCell))
      ≤ volume K + ENNReal.ofReal (Metric.diam K * (‖g₁‖ + ‖g₂‖)
          + |g₁.re * g₂.im - g₁.im * g₂.re|) := by
  have hSconv : Convex ℝ (Set.image2 (· + ·) K (segz g₁)) := hK.add (convex_segz g₁)
  have hSbd : Bornology.IsBounded (Set.image2 (· + ·) K (segz g₁)) := hKb.add (isBounded_segz g₁)
  have hinc : Set.image2 (· + ·) K (Llc g₁ g₂ '' uCell)
      ⊆ tsh (-(g₁ + g₂) / 2)
          (Set.image2 (· + ·) (Set.image2 (· + ·) K (segz g₁)) (segz g₂)) := by
    intro x hx
    obtain ⟨k, hk, p, hp, rfl⟩ := hx
    have hp' : p ∈ tsh (-(g₁ + g₂) / 2) (Set.image2 (· + ·) (segz g₁) (segz g₂)) :=
      Llc_uCell_subset_tsh g₁ g₂ hp
    rw [mem_tsh] at hp' ⊢
    obtain ⟨a, ⟨a₁, ha₁, a₂, ha₂, rfl⟩, hpa⟩ := hp'
    refine ⟨k + (a₁ + a₂), ⟨k + a₁, ⟨k, hk, a₁, ha₁, rfl⟩, a₂, ha₂, ?_⟩, ?_⟩
    · ring
    · rw [← hpa]
      ring
  have hPle : volume (Set.image2 (· + ·) K (Llc g₁ g₂ '' uCell))
      ≤ volume (Set.image2 (· + ·) (Set.image2 (· + ·) K (segz g₁)) (segz g₂)) := by
    calc volume (Set.image2 (· + ·) K (Llc g₁ g₂ '' uCell))
        ≤ volume (tsh (-(g₁ + g₂) / 2)
            (Set.image2 (· + ·) (Set.image2 (· + ·) K (segz g₁)) (segz g₂))) := measure_mono hinc
      _ = volume (Set.image2 (· + ·) (Set.image2 (· + ·) K (segz g₁)) (segz g₂)) :=
            volume_tsh _ _
  have hsw1 : volume (Set.image2 (· + ·) K (segz g₁)) = volume K + volume (wid g₁ '' K) :=
    sweep_image2_eq K hK hKb g₁
  have hsw2 : volume (Set.image2 (· + ·) (Set.image2 (· + ·) K (segz g₁)) (segz g₂))
      = volume (Set.image2 (· + ·) K (segz g₁))
        + volume (wid g₂ '' (Set.image2 (· + ·) K (segz g₁))) :=
    sweep_image2_eq _ hSconv hSbd g₂
  have hΔ : wid g₂ g₁ = -(g₁.re * g₂.im - g₁.im * g₂.re) := by
    simp only [wid, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_one, mul_zero, add_zero]
    ring
  have hwid2 : volume (wid g₂ '' (Set.image2 (· + ·) K (segz g₁)))
      ≤ volume (wid g₂ '' K) + ENNReal.ofReal |g₁.re * g₂.im - g₁.im * g₂.re| := by
    have hsub : wid g₂ '' (Set.image2 (· + ·) K (segz g₁))
        ⊆ Set.image2 (· + ·) (wid g₂ '' K) (Set.uIcc 0 (wid g₂ g₁)) := by
      rintro v ⟨w, ⟨k, hk, a, ha, rfl⟩, rfl⟩
      obtain ⟨t, ht, rfl⟩ := ha
      exact ⟨wid g₂ k, ⟨k, hk, rfl⟩, wid g₂ (t • g₁), wid_smul_mem_uIcc g₂ g₁ ht,
        by rw [wid_add]⟩
    have hIconv : Convex ℝ (wid g₂ '' K) := by
      rw [convex_iff_add_mem]
      intro x hx y hy p q hp hq hpq
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      refine ⟨p • u + q • v, hK hu hv hp hq hpq, ?_⟩
      rw [wid_add, wid_smul, wid_smul, smul_eq_mul, smul_eq_mul]
    have hIbd : Bornology.IsBounded (wid g₂ '' K) := isBounded_wid_image g₂ hKb
    calc volume (wid g₂ '' (Set.image2 (· + ·) K (segz g₁)))
        ≤ volume (Set.image2 (· + ·) (wid g₂ '' K) (Set.uIcc 0 (wid g₂ g₁))) :=
          measure_mono hsub
      _ ≤ volume (wid g₂ '' K) + ENNReal.ofReal |wid g₂ g₁| :=
          interval_add_segment_volume_le_aux _ hIconv hIbd _
      _ = volume (wid g₂ '' K) + ENNReal.ofReal |g₁.re * g₂.im - g₁.im * g₂.re| := by
            rw [hΔ, abs_neg]
  have hw1 := wid_image_volume_le_aux K hKb g₁
  have hw2 := wid_image_volume_le_aux K hKb g₂
  have hcombine : (volume K + ENNReal.ofReal (‖g₁‖ * Metric.diam K))
        + (ENNReal.ofReal (‖g₂‖ * Metric.diam K) + ENNReal.ofReal |g₁.re * g₂.im - g₁.im * g₂.re|)
      = volume K + ENNReal.ofReal (Metric.diam K * (‖g₁‖ + ‖g₂‖)
          + |g₁.re * g₂.im - g₁.im * g₂.re|) := by
    have h1 : (ENNReal.ofReal (‖g₁‖ * Metric.diam K) + ENNReal.ofReal (‖g₂‖ * Metric.diam K))
          + ENNReal.ofReal |g₁.re * g₂.im - g₁.im * g₂.re|
        = ENNReal.ofReal (Metric.diam K * (‖g₁‖ + ‖g₂‖)
          + |g₁.re * g₂.im - g₁.im * g₂.re|) := by
      rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ ‖g₁‖ * Metric.diam K)
            (by positivity : (0:ℝ) ≤ ‖g₂‖ * Metric.diam K),
          ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
      congr 1
      ring
    rw [add_reassoc]
    exact congrArg (fun t => volume K + t) h1
  calc volume (Set.image2 (· + ·) K (Llc g₁ g₂ '' uCell))
      ≤ volume (Set.image2 (· + ·) (Set.image2 (· + ·) K (segz g₁)) (segz g₂)) := hPle
    _ = volume (Set.image2 (· + ·) K (segz g₁))
          + volume (wid g₂ '' (Set.image2 (· + ·) K (segz g₁))) := hsw2
    _ = (volume K + volume (wid g₁ '' K))
          + volume (wid g₂ '' (Set.image2 (· + ·) K (segz g₁))) := by rw [hsw1]
    _ ≤ (volume K + ENNReal.ofReal (‖g₁‖ * Metric.diam K))
          + (volume (wid g₂ '' K) + ENNReal.ofReal |g₁.re * g₂.im - g₁.im * g₂.re|) :=
        add_le_add (add_le_add le_rfl hw1) hwid2
    _ ≤ (volume K + ENNReal.ofReal (‖g₁‖ * Metric.diam K))
          + (ENNReal.ofReal (‖g₂‖ * Metric.diam K)
              + ENNReal.ofReal |g₁.re * g₂.im - g₁.im * g₂.re|) :=
        add_le_add le_rfl (add_le_add hw2 le_rfl)
    _ = volume K + ENNReal.ofReal (Metric.diam K * (‖g₁‖ + ‖g₂‖)
          + |g₁.re * g₂.im - g₁.im * g₂.re|) := hcombine

/-! ## 8. The target -/

theorem convexHull_add_parallelogram_le (a θ φ : ℝ) (g₁ g₂ : ℂ) (ha : 0 < a) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (MeasureTheory.volume (Set.image2 (· + ·)
        (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
        (Work.FIArea3.JointCount.Llc g₁ g₂ '' Work.FIArea3.JointCount.uCell))).toReal
      ≤ (MeasureTheory.volume (convexHull ℝ
          (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ)))).toReal
        + 8 * θ * a * (‖g₁‖ + ‖g₂‖) + |g₁.re * g₂.im - g₁.im * g₂.re| := by
  set R : Set ℂ := annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ) with hR
  have hRball : R ⊆ Metric.closedBall (0 : ℂ) (a * Real.sqrt (1 + θ)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz.2.1
  have hconvbd : Bornology.IsBounded (convexHull ℝ R) :=
    (Metric.isBounded_closedBall).subset (convexHull_min hRball (convex_closedBall 0 _))
  have hconvfin : volume (convexHull ℝ R) ≠ ⊤ := hconvbd.measure_lt_top.ne
  have hdiam : Metric.diam (convexHull ℝ R) ≤ 8 * θ * a := by
    rw [convexHull_diam]
    exact diam_annSector_le a θ φ ha hθ0 hθ1
  have hmain : volume (Set.image2 (· + ·) R (Llc g₁ g₂ '' uCell))
      ≤ volume (convexHull ℝ R)
        + ENNReal.ofReal (8 * θ * a * (‖g₁‖ + ‖g₂‖)
            + |g₁.re * g₂.im - g₁.im * g₂.re|) := by
    calc volume (Set.image2 (· + ·) R (Llc g₁ g₂ '' uCell))
        ≤ volume (Set.image2 (· + ·) (convexHull ℝ R) (Llc g₁ g₂ '' uCell)) :=
          measure_mono (Set.image2_subset_right (subset_convexHull ℝ R))
      _ ≤ volume (convexHull ℝ R)
            + ENNReal.ofReal (Metric.diam (convexHull ℝ R) * (‖g₁‖ + ‖g₂‖)
                + |g₁.re * g₂.im - g₁.im * g₂.re|) :=
          add_parallelogram_volume_le_aux (convexHull ℝ R) (convex_convexHull ℝ R) hconvbd g₁ g₂
      _ ≤ volume (convexHull ℝ R)
            + ENNReal.ofReal (8 * θ * a * (‖g₁‖ + ‖g₂‖)
                + |g₁.re * g₂.im - g₁.im * g₂.re|) := by
          refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have hn : 0 ≤ ‖g₁‖ + ‖g₂‖ := by positivity
          nlinarith [hdiam, hn]
  have hto := ENNReal.toReal_mono (by
    rw [ENNReal.add_ne_top]
    exact ⟨hconvfin, ENNReal.ofReal_ne_top⟩) hmain
  calc (volume (Set.image2 (· + ·) R (Llc g₁ g₂ '' uCell))).toReal
      ≤ (volume (convexHull ℝ R) + ENNReal.ofReal (8 * θ * a * (‖g₁‖ + ‖g₂‖)
          + |g₁.re * g₂.im - g₁.im * g₂.re|)).toReal := hto
    _ = (volume (convexHull ℝ R)).toReal + (8 * θ * a * (‖g₁‖ + ‖g₂‖)
          + |g₁.re * g₂.im - g₁.im * g₂.re|) := by
        rw [ENNReal.toReal_add hconvfin ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (by positivity)]
    _ = (volume (convexHull ℝ R)).toReal + 8 * θ * a * (‖g₁‖ + ‖g₂‖)
          + |g₁.re * g₂.im - g₁.im * g₂.re| := by ring

end

end Work.FIArea3.JointCount
