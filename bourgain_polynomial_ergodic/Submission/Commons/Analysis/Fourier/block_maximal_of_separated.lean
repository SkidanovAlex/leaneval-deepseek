import Mathlib
import Submission.Commons.Analysis.Fourier.bandOp_dilation_identity

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators ENNReal FourierTransform

noncomputable section

namespace BourgainBlock

def hj (j : ℕ) : ℝ := (2:ℝ) ^ (-(j:ℝ) - 1)

/-- Change of variables `y ↦ σ y` for a Bochner integral on `ℝ`. -/
lemma integral_eq_smul_integral_comp_mul_left {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : ℝ → F) {σ : ℝ} (hσ : 0 < σ) :
    (∫ y, g y) = σ • ∫ x, g (σ * x) := by
  have h := Measure.integral_comp_mul_left g σ
  rw [abs_of_pos (inv_pos.mpr hσ)] at h
  rw [h, smul_smul, mul_inv_cancel₀ (ne_of_gt hσ), one_smul]

lemma band_integral_scale (σ z : ℝ) (hσ : 0 < σ) (a b : ℝ) :
    (∫ θ in a..b, Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = σ⁻¹ * ∫ ψ in (σ*a)..(σ*b),
          Complex.exp (-(Complex.I * (((z/σ : ℝ)) : ℂ) * (ψ : ℂ))) := by
  have hne : (σ⁻¹ : ℝ) ≠ 0 := ne_of_gt (inv_pos.mpr hσ)
  have key := intervalIntegral.integral_comp_mul_left (a := σ*a) (b := σ*b)
    (f := fun x : ℝ => Complex.exp (-(Complex.I * (z:ℂ) * (x:ℂ)))) hne
  have ha : σ⁻¹ * (σ * a) = a := by field_simp
  have hb : σ⁻¹ * (σ * b) = b := by field_simp
  rw [ha, hb, inv_inv] at key
  rw [Complex.real_smul] at key
  have hcongr : (∫ ψ in σ*a..σ*b, Complex.exp (-(Complex.I * ((z/σ : ℝ):ℂ) * (ψ:ℂ))))
      = ∫ ψ in σ*a..σ*b, Complex.exp (-(Complex.I * (z:ℂ) * (((σ⁻¹ * ψ : ℝ)):ℂ))) := by
    apply intervalIntegral.integral_congr; intro ψ _
    congr 1
    push_cast
    field_simp
  rw [hcongr, key]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hσ),
    Complex.ofReal_one, one_mul]

def bandOpR {N : ℕ} (mu : Fin N → ℝ) (r : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f y * (∑ k : Fin N, ∫ θ in (mu k - r)..(mu k + r),
      Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))

/-- **Dilation of the band-pass operator.** -/
lemma bandOpR_scale {N : ℕ} (mu : Fin N → ℝ) (r : ℝ) (f : ℝ → ℂ) (σ X : ℝ) (hσ : 0 < σ) :
    bandOpR mu r f (σ * X) = bandOpR (fun k => σ * mu k) (σ * r) (fun Y => f (σ * Y)) X := by
  unfold bandOpR
  have hstep1 : (∫ y, f y * (∑ k : Fin N, ∫ θ in (mu k - r)..(mu k + r),
        Complex.exp (-(Complex.I * (((σ * X - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = (σ : ℂ) * ∫ Y, f (σ * Y) * (∑ k : Fin N, ∫ θ in (mu k - r)..(mu k + r),
        Complex.exp (-(Complex.I * (((σ * X - σ * Y : ℝ) : ℂ)) * (θ : ℂ)))) := by
    have h := integral_eq_smul_integral_comp_mul_left (fun y : ℝ => f y * (∑ k : Fin N,
        ∫ θ in (mu k - r)..(mu k + r),
          Complex.exp (-(Complex.I * (((σ * X - y : ℝ) : ℂ)) * (θ : ℂ))))) hσ
    rw [h, Complex.real_smul]
  rw [hstep1]
  have hstep2 : (∫ Y, f (σ * Y) * (∑ k : Fin N, ∫ θ in (mu k - r)..(mu k + r),
        Complex.exp (-(Complex.I * (((σ * (X - Y) : ℝ) : ℂ)) * (θ : ℂ)))))
      = (((σ)⁻¹ : ℝ) : ℂ) * ∫ Y, f (σ * Y) * (∑ k : Fin N,
        ∫ ψ in ((σ * mu k) - σ * r)..((σ * mu k) + σ * r),
          Complex.exp (-(Complex.I * (((X - Y : ℝ) : ℂ)) * (ψ : ℂ)))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with Y
    have hkey : ∀ k : Fin N, (∫ θ in (mu k - r)..(mu k + r),
          Complex.exp (-(Complex.I * (((σ * (X - Y) : ℝ) : ℂ)) * (θ : ℂ))))
        = σ⁻¹ * ∫ ψ in ((σ * mu k) - σ * r)..((σ * mu k) + σ * r),
            Complex.exp (-(Complex.I * (((X - Y : ℝ) : ℂ)) * (ψ : ℂ))) := by
      intro k
      have hk := band_integral_scale σ (σ * (X - Y)) hσ (mu k - r) (mu k + r)
      have hzx : ((σ * (X - Y)) / σ : ℝ) = X - Y := by field_simp
      rw [hzx] at hk
      have e1 : σ * (mu k - r) = (σ * mu k) - σ * r := by ring
      have e2 : σ * (mu k + r) = (σ * mu k) + σ * r := by ring
      rw [e1, e2] at hk
      exact hk
    have hsum : (∑ k : Fin N, ∫ θ in (mu k - r)..(mu k + r),
          Complex.exp (-(Complex.I * (((σ * (X - Y) : ℝ) : ℂ)) * (θ : ℂ))))
        = σ⁻¹ * ∑ k : Fin N, ∫ ψ in ((σ * mu k) - σ * r)..((σ * mu k) + σ * r),
            Complex.exp (-(Complex.I * (((X - Y : ℝ) : ℂ)) * (ψ : ℂ))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => hkey k)
    rw [hsum]
    ring
  have hstep3 : (∫ Y, f (σ * Y) * (∑ k : Fin N, ∫ θ in (mu k - r)..(mu k + r),
        Complex.exp (-(Complex.I * (((σ * X - σ * Y : ℝ) : ℂ)) * (θ : ℂ)))))
      = (∫ Y, f (σ * Y) * (∑ k : Fin N, ∫ θ in (mu k - r)..(mu k + r),
        Complex.exp (-(Complex.I * (((σ * (X - Y) : ℝ) : ℂ)) * (θ : ℂ))))) := by
    apply integral_congr_ae
    filter_upwards with Y
    congr 2 with k
    congr 1
    ring_nf
  rw [hstep3, hstep2]
  rw [← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt hσ), Complex.ofReal_one, one_mul]


/-- **Splitting a finite union of separated bands.** -/
lemma indicator_neighborhood_integral {N : ℕ} (mu : Fin N → ℝ) {δ r C : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin N, i ≠ j → δ ≤ |mu i - mu j|) (hr : 2*r ≤ δ) (hr0 : 0 ≤ r)
    (G : ℝ → ℂ) (hG : MeasureTheory.AEStronglyMeasurable G (volume : Measure ℝ))
    (hGb : ∀ θ, ‖G θ‖ ≤ C) :
    (∫ θ in {θ : ℝ | ∃ s : Fin N, |θ - mu s| ≤ r}, G θ)
      = ∑ s : Fin N, ∫ θ in (mu s - r)..(mu s + r), G θ := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun s : Fin N => Set.Ioc (mu s - r) (mu s + r)) := by
    intro i _ j _ hij
    change Disjoint (Set.Ioc (mu i - r) (mu i + r)) (Set.Ioc (mu j - r) (mu j + r))
    rw [Set.disjoint_left]
    intro θ hθi hθj
    simp only [Set.mem_Ioc] at hθi hθj
    have hsepij := hsep i j hij
    have hne : mu i ≠ mu j := by
      intro h; rw [h, sub_self, abs_zero] at hsepij; linarith
    rcases lt_or_gt_of_ne hne with h | h
    · have habs : |mu i - mu j| = mu j - mu i := by
        rw [abs_of_neg (by linarith : mu i - mu j < 0)]; ring
      rw [habs] at hsepij
      linarith [hθi.2, hθj.1]
    · have habs : |mu i - mu j| = mu i - mu j := abs_of_pos (by linarith)
      rw [habs] at hsepij
      linarith [hθj.2, hθi.1]
  have hfin : (⋃ s : Fin N, ({(mu s - r), (mu s + r)} : Set ℝ)).Finite :=
    Set.finite_iUnion (fun s : Fin N =>
      (Set.finite_singleton (mu s + r)).insert (mu s - r))
  have hae : {θ : ℝ | ∃ s : Fin N, |θ - mu s| ≤ r}
      =ᵐ[volume] (⋃ s ∈ (Finset.univ : Finset (Fin N)), Set.Ioc (mu s - r) (mu s + r)) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · apply measure_mono_null _ (Set.Finite.measure_zero hfin volume)
      intro θ hθ
      rw [Set.mem_sdiff] at hθ
      obtain ⟨hS, hnot⟩ := hθ
      obtain ⟨s, hs⟩ := hS
      refine Set.mem_iUnion.mpr ⟨s, ?_⟩
      have hle : θ ≤ mu s + r := by
        have := le_trans (le_abs_self (θ - mu s)) hs; linarith
      have hge : mu s - r ≤ θ := by
        have := le_trans (neg_le_abs (θ - mu s)) hs; linarith
      have hnots : θ ∉ Set.Ioc (mu s - r) (mu s + r) := fun hc =>
        hnot (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨Finset.mem_univ s, hc⟩⟩)
      by_cases hcase : θ = mu s - r
      · left; exact hcase
      · right
        by_contra hc
        exact hnots ⟨lt_of_le_of_ne hge (Ne.symm hcase), hle⟩
    · apply measure_mono_null _ (Set.Finite.measure_zero hfin volume)
      intro θ hθ
      rw [Set.mem_sdiff] at hθ
      obtain ⟨hU, hS⟩ := hθ
      rw [Set.mem_iUnion] at hU
      obtain ⟨s, hs⟩ := hU
      rw [Set.mem_iUnion] at hs
      obtain ⟨_, hs⟩ := hs
      refine absurd ⟨s, ?_⟩ hS
      rw [abs_le]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmeas : ∀ s ∈ (Finset.univ : Finset (Fin N)),
      MeasurableSet (Set.Ioc (mu s - r) (mu s + r)) := fun s _ => measurableSet_Ioc
  have hIntOn : ∀ s ∈ (Finset.univ : Finset (Fin N)),
      IntegrableOn G (Set.Ioc (mu s - r) (mu s + r)) volume := by
    intro s _
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := C) ?_ hG ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · filter_upwards with θ; exact hGb θ
  rw [MeasureTheory.setIntegral_congr_set hae]
  rw [integral_biUnion_finset (Finset.univ : Finset (Fin N)) hmeas hdisj hIntOn]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [intervalIntegral.integral_of_le (by linarith : mu s - r ≤ mu s + r)]

lemma norm_exp_neg_I_mul (a θ : ℝ) : ‖Complex.exp (-(Complex.I * (a:ℂ) * (θ:ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (-(Complex.I * (a:ℂ) * (θ:ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [hre, Real.exp_zero]

/-- The band-pass operator in the "union of frequency neighbourhoods" form of the target. -/
def bandOpInd {K : ℕ} (lam : Fin K → ℝ) (r : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f y * (∫ θ : ℝ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
      (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)

/-- When the radius is at most half the separation of the frequencies, the union-of-neighbourhoods
operator equals the sum-of-bands operator. -/
lemma bandOpInd_eq_bandOpR_of_range {K N : ℕ} (lam : Fin K → ℝ) (mu : Fin N → ℝ)
    (hrange : Set.range mu = Set.range lam) {δ r : ℝ} (hδ : 0 < δ) (hr0 : 0 ≤ r)
    (hsep : ∀ i j : Fin N, i ≠ j → δ ≤ |mu i - mu j|) (hr : 2*r ≤ δ)
    (f : ℝ → ℂ) (x : ℝ) :
    bandOpInd lam r f x = bandOpR mu r f x := by
  have hset : {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
      = {θ : ℝ | ∃ s : Fin N, |θ - mu s| ≤ r} := by
    ext θ; constructor
    · rintro ⟨k, hk⟩
      have : lam k ∈ Set.range mu := by rw [hrange]; exact ⟨k, rfl⟩
      obtain ⟨s, hs⟩ := this
      exact ⟨s, by rw [hs]; exact hk⟩
    · rintro ⟨s, hs⟩
      have : mu s ∈ Set.range lam := by rw [← hrange]; exact ⟨s, rfl⟩
      obtain ⟨k, hk⟩ := this
      exact ⟨k, by rw [hk]; exact hs⟩
  unfold bandOpInd bandOpR
  congr 1 with y
  rw [hset]
  have hG : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
      (volume : Measure ℝ) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have key := indicator_neighborhood_integral mu hδ hsep hr hr0
    (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) hG
    (C := 1) (fun θ => by rw [norm_exp_neg_I_mul])
  have hmeas : MeasurableSet {θ : ℝ | ∃ s : Fin N, |θ - mu s| ≤ r} := by
    have hset' : {θ : ℝ | ∃ s : Fin N, |θ - mu s| ≤ r}
        = ⋃ s : Fin N, {θ : ℝ | |θ - mu s| ≤ r} := by
      ext θ; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [hset']
    exact MeasurableSet.iUnion (fun s => measurableSet_le (by fun_prop) measurable_const)
  rw [integral_indicator (s := {θ : ℝ | ∃ s : Fin N, |θ - mu s| ≤ r}) hmeas, key]

/-- The band-pass operator is a.e. strongly measurable. -/
lemma aestronglyMeasurable_bandOpInd {K : ℕ} (lam : Fin K → ℝ) (r : ℝ) (f : ℝ → ℂ)
    (hf : MeasureTheory.AEStronglyMeasurable f (volume : Measure ℝ)) :
    MeasureTheory.AEStronglyMeasurable (bandOpInd lam r f) (volume : Measure ℝ) := by
  have hS : MeasurableSet {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r} := by
    have hset' : {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
        = ⋃ k : Fin K, {θ : ℝ | |θ - lam k| ≤ r} := by
      ext θ; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [hset']
    exact MeasurableSet.iUnion (fun k => measurableSet_le (by fun_prop) measurable_const)
  have hbase : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(Complex.I * (((q.1.1 - q.1.2) : ℝ) : ℂ) * ((q.2 : ℝ) : ℂ)))) := by fun_prop
  have hS2 : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.2 ∈ {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}} :=
    hS.preimage measurable_snd
  have hjoint : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
        (fun θ => Complex.exp (-(Complex.I * (((q.1.1 - q.1.2) : ℝ) : ℂ) * (θ : ℂ)))) q.2) := by
    have heq : (fun q : (ℝ × ℝ) × ℝ => Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
        (fun θ => Complex.exp (-(Complex.I * (((q.1.1 - q.1.2) : ℝ) : ℂ) * (θ : ℂ)))) q.2)
        = ({q : (ℝ × ℝ) × ℝ | q.2 ∈ {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}}).indicator
          (fun q => Complex.exp (-(Complex.I * (((q.1.1 - q.1.2) : ℝ) : ℂ) * ((q.2 : ℝ) : ℂ)))) := by
      funext q
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [heq]
    exact hbase.indicator hS2
  have hjointA : MeasureTheory.AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × ℝ => Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
        (fun θ => Complex.exp (-(Complex.I * (((q.1.1 - q.1.2) : ℝ) : ℂ) * (θ : ℂ)))) q.2)
      (((volume : Measure ℝ).prod volume).prod volume) := hjoint.aestronglyMeasurable
  have hinner : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ∫ θ : ℝ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
        (fun θ => Complex.exp (-(Complex.I * (((p.1 - p.2) : ℝ) : ℂ) * (θ : ℂ)))) θ)
      ((volume : Measure ℝ).prod volume) :=
    hjointA.integral_prod_right' (ν := (volume : Measure ℝ))
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => f p.2 * (∫ θ : ℝ,
        Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ r}
          (fun θ => Complex.exp (-(Complex.I * (((p.1 - p.2) : ℝ) : ℂ) * (θ : ℂ)))) θ))
      ((volume : Measure ℝ).prod volume) :=
    (hf.comp_snd).mul hinner
  have hout := hprod.integral_prod_right' (ν := (volume : Measure ℝ))
  exact hout

/-- Basic properties of the dyadic radii. -/
lemma hj_eq (j : ℕ) : hj j = 2⁻¹ * (2⁻¹)^j := by
  unfold hj
  have h : -( (j:ℝ)) - 1 = -(1:ℝ) + (-1) * (j:ℝ) := by ring
  rw [h, Real.rpow_add (by norm_num), ← Real.rpow_natCast, Real.rpow_neg_one]
  simp [inv_pow]

lemma hj_pos (j : ℕ) : 0 < hj j := Real.rpow_pos_of_pos (by norm_num) _

lemma hj_antitone : Antitone hj := by
  intro i j hij
  rw [hj_eq, hj_eq]
  have h2 : (2⁻¹:ℝ) ≤ 1 := by norm_num
  have h3 : (2⁻¹:ℝ)^j ≤ (2⁻¹)^i := pow_le_pow_of_le_one (by norm_num) h2 hij
  nlinarith [hj_pos i, hj_pos j]

lemma lintegral_eq_ofReal_mul_lintegral_comp_mul_left (F : ℝ → ℝ≥0∞)
    (hF : AEMeasurable F (volume : Measure ℝ)) {σ : ℝ} (hσ : 0 < σ) :
    (∫⁻ x, F x) = ENNReal.ofReal σ * ∫⁻ X, F (σ * X) := by
  set F' := AEMeasurable.mk F hF with hF'def
  have hF'm : Measurable F' := AEMeasurable.measurable_mk hF
  have hF' : F =ᵐ[volume] F' := AEMeasurable.ae_eq_mk hF
  have hg : Measurable fun X : ℝ => σ * X := by fun_prop
  have hmap : Measure.map (fun X : ℝ => σ * X) volume = ENNReal.ofReal σ⁻¹ • volume := by
    rw [Real.map_volume_mul_left (ne_of_gt hσ), abs_of_pos (inv_pos.mpr hσ)]
  have key : (∫⁻ x, F' x) = ENNReal.ofReal σ * ∫⁻ X, F' (σ * X) := by
    have h1 : (∫⁻ x, F' x ∂Measure.map (fun X : ℝ => σ * X) volume)
        = ∫⁻ X, F' (σ * X) ∂volume := lintegral_map hF'm hg
    rw [hmap, lintegral_smul_measure] at h1
    rw [← h1, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hσ),
      mul_inv_cancel₀ (ne_of_gt hσ), ENNReal.ofReal_one, one_mul]
  have hcomp : (fun X : ℝ => F (σ * X)) =ᵐ[volume] (fun X : ℝ => F' (σ * X)) := by
    have h1 : F =ᵐ[Measure.map (fun X : ℝ => σ * X) volume] F' := by
      rw [hmap]
      exact Measure.AbsolutelyContinuous.ae_eq Measure.smul_absolutelyContinuous hF'
    exact MeasureTheory.ae_eq_comp (f := fun X : ℝ => σ * X)
      (g := F) (g' := F') (hg.aemeasurable) h1
  rw [lintegral_congr_ae hF', lintegral_congr_ae hcomp, key]

lemma iSup_subtype_fine {jf : ℕ} (u : ℕ → ℝ≥0∞) :
    (⨆ j : ℕ, ⨆ (_ : jf ≤ j), u (j - jf)) = ⨆ j' : ℕ, u j' := by
  apply le_antisymm
  · apply iSup_le; intro j
    apply iSup_le; intro _
    exact le_iSup u (j - jf)
  · apply iSup_le; intro j'
    have h1 : u j' ≤ u ((jf + j') - jf) := by rw [Nat.add_sub_cancel_left]
    have h2 : u ((jf + j') - jf) ≤ ⨆ (_ : jf ≤ jf + j'), u ((jf + j') - jf) :=
      le_iSup (fun _ : jf ≤ jf + j' => u ((jf + j') - jf)) (Nat.le_add_right jf j')
    have h3 : (⨆ (_ : jf ≤ jf + j'), u ((jf + j') - jf))
        ≤ ⨆ j : ℕ, ⨆ (_ : jf ≤ j), u (j - jf) :=
      le_iSup (fun j : ℕ => ⨆ (_ : jf ≤ j), u (j - jf)) (jf + j')
    exact h1.trans (h2.trans h3)

/-- **The fine-scale part of the reduction.** -/
lemma fine_scales_bound
    (Ct : ℝ) (hCt : 0 < Ct)
    (hsep : ∀ (N : ℕ) (mu : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → 1 ≤ |mu i - mu j|) →
      ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume),
        ∫⁻ x, (⨆ j : ℕ, ‖bandOpR mu (hj j) f x‖ₑ) ^ (2:ℝ)
            ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume)
    (K : ℕ) (lam : Fin K → ℝ) (N : ℕ) (mu : Fin N → ℝ)
    (hrange : Set.range mu = Set.range lam)
    {δ : ℝ} (hδ : 0 < δ) (hsepδ : ∀ i j : Fin N, i ≠ j → δ ≤ |mu i - mu j|)
    (jf : ℕ) (hjf : 2 * hj jf ≤ δ)
    (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
    ∫⁻ x, (⨆ j : ℕ, ⨆ (_ : jf ≤ j), ‖bandOpInd lam (hj j) f x‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.volume
      ≤ ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2)
        * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume := by
  set σ : ℝ := (2:ℝ) ^ jf with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hσ_ne : σ ≠ 0 := ne_of_gt hσpos
  have hσδ : 1 ≤ σ * δ := by
    have h1 : σ * (2 * hj jf) ≤ σ * δ :=
      mul_le_mul_of_nonneg_left hjf (le_of_lt hσpos)
    have h2 : σ * (2 * hj jf) = 1 := by
      rw [hσdef, hj_eq]
      have hpow : ((2:ℝ) ^ jf) * (((2:ℝ) ^ jf)⁻¹) = 1 :=
        mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
      have hexp : (2:ℝ) ^ jf * (2 * (2⁻¹ * (2⁻¹) ^ jf))
          = 2⁻¹ * ((2:ℝ) ^ jf * ((2:ℝ) ^ jf)⁻¹) + 2⁻¹ * ((2:ℝ) ^ jf * ((2:ℝ) ^ jf)⁻¹) := by
        rw [inv_pow]; ring
      rw [hexp, hpow]; norm_num
    linarith
  have hsep1 : ∀ i j : Fin N, i ≠ j → 1 ≤ |σ * mu i - σ * mu j| := by
    intro i j hij
    rw [← mul_sub, abs_mul, abs_of_pos hσpos]
    calc (1:ℝ) ≤ σ * δ := hσδ
      _ ≤ σ * |mu i - mu j| := mul_le_mul_of_nonneg_left (hsepδ i j hij) (le_of_lt hσpos)
  have hσhj : ∀ j : ℕ, jf ≤ j → σ * hj j = hj (j - jf) := by
    intro j hj'
    have hpow : (2:ℝ)^j = (2:ℝ)^jf * (2:ℝ)^(j - jf) := by
      rw [← pow_add, Nat.add_sub_cancel' hj']
    have h1 : (2⁻¹:ℝ)^j = ((2:ℝ)^j)⁻¹ := by rw [inv_pow]
    have h2 : (2⁻¹:ℝ)^(j-jf) = ((2:ℝ)^(j-jf))⁻¹ := by rw [inv_pow]
    rw [hσdef, hj_eq, hj_eq, h1, h2, hpow]
    field_simp
  have hfine : ∀ j : ℕ, jf ≤ j → ∀ x : ℝ, bandOpInd lam (hj j) f x = bandOpR mu (hj j) f x := by
    intro j hj' x
    refine bandOpInd_eq_bandOpR_of_range lam mu hrange hδ (le_of_lt (hj_pos j)) hsepδ ?_ f x
    have h2 : hj j ≤ hj jf := hj_antitone hj'
    linarith
  have hFmeas : AEMeasurable
      (fun x : ℝ => (⨆ j : ℕ, ⨆ (_ : jf ≤ j), ‖bandOpInd lam (hj j) f x‖ₑ) ^ (2:ℝ))
      (volume : Measure ℝ) := by
    apply AEMeasurable.pow_const
    apply AEMeasurable.iSup
    intro j
    apply AEMeasurable.iSup
    intro _
    exact (aestronglyMeasurable_bandOpInd lam (hj j) f hf.aestronglyMeasurable).enorm
  rw [lintegral_eq_ofReal_mul_lintegral_comp_mul_left _ hFmeas hσpos]
  have hpt : ∀ X : ℝ, (⨆ j : ℕ, ⨆ (_ : jf ≤ j), ‖bandOpInd lam (hj j) f (σ * X)‖ₑ)
      = (⨆ j' : ℕ, ‖bandOpR (fun i => σ * mu i) (hj j') (fun Y => f (σ * Y)) X‖ₑ) := by
    intro X
    set F : ℕ → ℝ≥0∞ :=
      fun j => ‖bandOpR (fun i => σ * mu i) (hj j) (fun Y => f (σ * Y)) X‖ₑ with hFdef
    have h1 : (⨆ j : ℕ, ⨆ (_ : jf ≤ j), ‖bandOpInd lam (hj j) f (σ * X)‖ₑ)
        = (⨆ j : ℕ, ⨆ (_ : jf ≤ j), F (j - jf)) := by
      apply iSup_congr; intro j
      apply iSup_congr; intro hj'
      rw [hFdef, hfine j hj' (σ * X), bandOpR_scale mu (hj j) f σ X hσpos, hσhj j hj']
    rw [h1, iSup_subtype_fine F, hFdef]
  rw [lintegral_congr (fun X => by rw [hpt X])]
  have hg : MeasureTheory.MemLp (fun Y : ℝ => f (σ * Y)) 2 (volume : Measure ℝ) := by
    have hmp : MeasureTheory.MeasurePreserving (fun Y : ℝ => σ * Y)
        (volume : Measure ℝ) (ENNReal.ofReal σ⁻¹ • volume) :=
      ⟨by fun_prop, by
        rw [Real.map_volume_mul_left hσ_ne, abs_of_pos (inv_pos.mpr hσpos)]⟩
    exact (hf.smul_measure (by simp)).comp_measurePreserving hmp
  have hone : ENNReal.ofReal σ * ENNReal.ofReal σ⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hσpos), mul_inv_cancel₀ (ne_of_gt hσpos),
      ENNReal.ofReal_one]
  have hone' : ENNReal.ofReal σ⁻¹ * ENNReal.ofReal σ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hσpos)), inv_mul_cancel₀ (ne_of_gt hσpos),
      ENNReal.ofReal_one]
  have hgval : (∫⁻ X, ‖(fun Y : ℝ => f (σ * Y)) X‖ₑ ^ (2:ℝ) ∂volume)
      = ENNReal.ofReal σ⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    have h1 := lintegral_eq_ofReal_mul_lintegral_comp_mul_left
      (fun x : ℝ => ‖f x‖ₑ ^ (2:ℝ)) (hf.aemeasurable.enorm.pow_const 2) hσpos
    rw [h1, ← mul_assoc, hone', one_mul]
  have hkey := hsep N (fun i => σ * mu i) hsep1 (fun Y : ℝ => f (σ * Y)) hg
  rw [hgval] at hkey
  calc ENNReal.ofReal σ * ∫⁻ X, (⨆ j' : ℕ, ‖bandOpR (fun i => σ * mu i) (hj j') (fun Y => f (σ * Y)) X‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal σ * (ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2)
          * (ENNReal.ofReal σ⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))) :=
        mul_le_mul_of_nonneg_left hkey bot_le
    _ = ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
        rw [← mul_assoc (ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2)) (ENNReal.ofReal σ⁻¹)
              (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)),
          mul_comm (ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2)) (ENNReal.ofReal σ⁻¹),
          mul_assoc (ENNReal.ofReal σ⁻¹) (ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2))
            (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)),
          ← mul_assoc (ENNReal.ofReal σ) (ENNReal.ofReal σ⁻¹)
            (ENNReal.ofReal ((Ct * (Real.log ((N:ℝ)+2))^2)^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)),
          hone, one_mul]

/-- `2 * hj j = hj (j-1)` for `j ≥ 1`. -/
lemma two_mul_hj (j : ℕ) (hj1 : 1 ≤ j) : 2 * hj j = hj (j - 1) := by
  unfold hj
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj1]; norm_num
  rw [hcast]
  rw [show (-((j : ℝ) - 1) - 1) = (-(j : ℝ) - 1) + 1 from by ring]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
  ring

/-- The goal's band operator (union of `Icc` intervals) equals `bandOpInd`. -/
lemma goal_op_eq {K : ℕ} (A : Fin K → ℝ) (r : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    (∫ y, f y * (∫ θ, Set.indicator (⋃ a : Fin K, Set.Icc (A a - r) (A a + r))
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = bandOpInd A r f x := by
  have hST : (⋃ a : Fin K, Set.Icc (A a - r) (A a + r))
      = {θ : ℝ | ∃ a : Fin K, |θ - A a| ≤ r} := by
    ext θ
    simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, h1, h2⟩
      exact ⟨a, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · rintro ⟨a, ha⟩
      obtain ⟨h1, h2⟩ := abs_le.mp ha
      exact ⟨a, by linarith, by linarith⟩
  unfold bandOpInd
  rw [hST]

end BourgainBlock

theorem block_maximal_of_separated
    (hsep : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (mu : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → 1 ≤ |mu i - mu j|) →
      ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∑ k : Fin N,
              ∫ θ in (mu k - (2:ℝ)^(-(j:ℝ)-1))..(mu k + (2:ℝ)^(-(j:ℝ)-1)),
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * (Real.log ((N:ℝ)+2))^2)^2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (s : ℕ) (A : Fin s → ℝ) (c d : ℕ),
      (∀ i l : Fin s, i ≠ l → (2:ℝ)^(-(c:ℝ)-1) < |A i - A l|) →
      c + 3 ≤ d →
      ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
        ∫⁻ x, (⨆ j ∈ Finset.Icc (c+3) d, ‖∫ y : ℝ, f y *
            (∫ θ : ℝ, Set.indicator
              (⋃ a : Fin s, Set.Icc (A a - 2 * (2:ℝ)^(-(j:ℝ)-1)) (A a + 2 * (2:ℝ)^(-(j:ℝ)-1)))
              (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C' * (Real.log ((s:ℝ)+2))^2)^2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume := by
  obtain ⟨C, hCpos, hC⟩ := hsep
  refine ⟨C, hCpos, ?_⟩
  intro s A c d hA hcd f hf
  have hsep' : ∀ (N : ℕ) (mu : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → 1 ≤ |mu i - mu j|) →
      ∀ (g : ℝ → ℂ) (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
        ∫⁻ x, (⨆ j : ℕ, ‖BourgainBlock.bandOpR mu (BourgainBlock.hj j) g x‖ₑ) ^ (2:ℝ)
            ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * (Real.log ((N:ℝ)+2))^2)^2)
          * ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume := by
    intro N mu hN g hg
    have h := hC N mu hN g hg
    simpa only [BourgainBlock.bandOpR, BourgainBlock.hj] using h
  have hδpos : 0 < (2:ℝ)^(-(c:ℝ)-1) := by positivity
  have hsepδ : ∀ i l : Fin s, i ≠ l → (2:ℝ)^(-(c:ℝ)-1) ≤ |A i - A l| :=
    fun i l hil => le_of_lt (hA i l hil)
  have hjf_le : 2 * BourgainBlock.hj (c+1) ≤ (2:ℝ)^(-(c:ℝ)-1) := by
    rw [BourgainBlock.two_mul_hj (c+1) (by omega : 1 ≤ c+1), BourgainBlock.hj,
        show (c+1) - 1 = c from by omega]
  have hfsb := BourgainBlock.fine_scales_bound C hCpos hsep' s A s A rfl hδpos hsepδ
      (c+1) hjf_le f hf
  refine le_trans ?_ hfsb
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply iSup_le; intro j
  apply iSup_le; intro hjmem
  obtain ⟨hj_ge, hj_le⟩ := Finset.mem_Icc.mp hjmem
  have hj1 : 1 ≤ j := by omega
  have hT : (∫ y : ℝ, f y * (∫ θ : ℝ, Set.indicator
        (⋃ a : Fin s, Set.Icc (A a - 2 * (2:ℝ)^(-(j:ℝ)-1)) (A a + 2 * (2:ℝ)^(-(j:ℝ)-1)))
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = BourgainBlock.bandOpInd A (BourgainBlock.hj (j-1)) f x := by
    have h1 := BourgainBlock.goal_op_eq A (2 * BourgainBlock.hj j) f x
    have h2 : BourgainBlock.bandOpInd A (2 * BourgainBlock.hj j) f x
        = BourgainBlock.bandOpInd A (BourgainBlock.hj (j-1)) f x := by
      rw [BourgainBlock.two_mul_hj j hj1]
    rw [← h2]
    simpa only [BourgainBlock.hj] using h1
  rw [hT]
  refine le_trans ?_ (le_iSup (fun m : ℕ => ⨆ (_ : c+1 ≤ m),
      ‖BourgainBlock.bandOpInd A (BourgainBlock.hj m) f x‖ₑ) (j-1))
  exact le_iSup (fun _ : c + 1 ≤ j - 1 =>
      ‖BourgainBlock.bandOpInd A (BourgainBlock.hj (j-1)) f x‖ₑ) (by omega)

end
end Commons.Analysis.Fourier
