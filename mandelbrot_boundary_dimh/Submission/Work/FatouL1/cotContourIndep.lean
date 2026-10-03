import Mathlib
import Submission.Work.FatouL1.existsNormCotPiLe
import Submission.Work.FatouL1.existsSeqTendstoZero
import Submission.Work.FatouL1.horizDefs
import Submission.Work.FatouL1.hcRectCot

/-!
# FATOU-L1: independence of the cotangent contour integral of the line

For `h` holomorphic on the strip `{a < Re < b}` with bounded line masses and `z` with
`c₁, c₂ ∈ (z.re - 1, z.re)`, the Cauchy-type integral

  `c ↦ ∫_y h (c + y*I) * cot (π (c + y*I - z))`

does not depend on `c`: the difference of the two line integrals is the limit of the
horizontal contributions of the rectangle `[c₁,c₂] × [-Y,Y]`, whose contour integral vanishes
(Cauchy, since the closed rectangle contains no pole of `cot (π (· - z))`, the poles being the
translates of `z` by the integers, of real part `z.re + k ∉ [c₁,c₂]`).  The horizontal
contributions vanish along a sequence of heights `Y → ∞`: their `‖h‖`-mass is `L¹` in the height
by Tonelli, hence small along a sequence, while `cot (π (· - z))` is bounded on the
corresponding strip.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Work.FatouL1

noncomputable section

/-! ## Elementary arithmetic lemmas -/

/-- An integer is never an element of the open interval `(-1, 0)`. -/
lemma intCast_ne_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 0) (k : ℤ) :
    (k : ℝ) ≠ x := by
  intro hk
  subst hk
  have h1 : ((-1 : ℤ) : ℝ) < (k : ℝ) := by simpa using hx.1
  have h2 : (k : ℝ) < ((0 : ℤ) : ℝ) := by simpa using hx.2
  have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
  have h2' : k < 0 := by exact_mod_cast h2
  omega

/-- `Complex.cot` is differentiable wherever `sin ≠ 0`. -/
lemma differentiableAt_cot_of_sin_ne {w : ℂ} (hw : Complex.sin w ≠ 0) :
    DifferentiableAt ℂ Complex.cot w := by
  change DifferentiableAt ℂ (fun z : ℂ => Complex.cos z / Complex.sin z) w
  exact Complex.differentiableAt_cos.div Complex.differentiableAt_sin hw

/-- `Complex.cot` is continuous wherever `sin ≠ 0`. -/
lemma continuousAt_cot_of_sin_ne {w : ℂ} (hw : Complex.sin w ≠ 0) :
    ContinuousAt Complex.cot w :=
  (differentiableAt_cot_of_sin_ne hw).continuousAt

/-- If `sin (π w) ≠ 0` then `cot (π ·)` is differentiable at `w`. -/
lemma differentiableAt_cot_pi_of_sin_ne {w : ℂ} (hw : Complex.sin (Real.pi * w) ≠ 0) :
    DifferentiableAt ℂ (fun v : ℂ => Complex.cot (Real.pi * v)) w := by
  have h1 : DifferentiableAt ℂ (fun v : ℂ => Real.pi * v) w :=
    differentiableAt_const _ |>.mul differentiableAt_id
  exact (differentiableAt_cot_of_sin_ne hw).comp w h1

/-! ## The horizontal-slice mass machinery (copied from `exists_small_horizontal`) -/

private lemma re_add_mul_I' (t y : ℝ) : ((t : ℂ) + y * Complex.I).re = t := by
  simp [Complex.add_re, Complex.mul_re]

private lemma mem_strip_of_mem_Ioc' {a b x₁ x₂ : ℝ}
    (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) {t : ℝ} (ht : t ∈ Set.Ioc x₁ x₂) :
    a < t ∧ t < b :=
  ⟨lt_trans h₁.1 ht.1, lt_of_le_of_lt ht.2 h₂.2⟩

private lemma continuousOn_pair_comp' {a b x₁ x₂ : ℝ} {g : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ g {w : ℂ | a < w.re ∧ w.re < b})
    (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) :
    ContinuousOn (fun p : ℝ × ℝ => g ((p.1 : ℂ) + p.2 * Complex.I))
      (Set.Ioc x₁ x₂ ×ˢ (Set.univ : Set ℝ)) := by
  refine hhol.continuousOn.comp ?_ ?_
  · fun_prop
  · intro p hp
    simp only [Set.mem_ofPred_eq]
    rw [re_add_mul_I']
    exact mem_strip_of_mem_Ioc' h₁ h₂ hp.1

private lemma continuousOn_line_comp' {a b x₁ x₂ : ℝ} {g : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ g {w : ℂ | a < w.re ∧ w.re < b})
    (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) (y : ℝ) :
    ContinuousOn (fun t : ℝ => g ((t : ℂ) + y * Complex.I)) (Set.Ioc x₁ x₂) := by
  refine hhol.continuousOn.comp ?_ ?_
  · fun_prop
  · intro t ht
    simp only [Set.mem_ofPred_eq]
    rw [re_add_mul_I']
    exact mem_strip_of_mem_Ioc' h₁ h₂ ht

private theorem intervalIntegral_eq_toReal_lintegral' {x₁ x₂ : ℝ} (h12 : x₁ < x₂) {F : ℝ → ℂ}
    (hF : ContinuousOn F (Set.Ioc x₁ x₂)) :
    (∫ t in x₁..x₂, ‖F t‖)
      = (∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal ‖F t‖).toReal := by
  have hAESM : AEStronglyMeasurable (fun t : ℝ => ‖F t‖) (volume.restrict (Set.Ioc x₁ x₂)) :=
    hF.norm.aestronglyMeasurable measurableSet_Ioc
  rw [intervalIntegral.integral_of_le h12.le]
  exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun t => norm_nonneg _)) hAESM

private theorem horizMass_aemeasurable' {a b : ℝ} {g : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ g {w : ℂ | a < w.re ∧ w.re < b})
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) :
    AEMeasurable (horizMass g x₁ x₂) (volume) := by
  have hnorm : ContinuousOn
      (fun p : ℝ × ℝ => ENNReal.ofReal ‖g ((p.1 : ℂ) + p.2 * Complex.I)‖)
      (Set.Ioc x₁ x₂ ×ˢ (Set.univ : Set ℝ)) :=
    ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_pair_comp' hhol h₁ h₂).norm
  have hprod : (volume.restrict (Set.Ioc x₁ x₂)).prod volume
      = (volume.prod volume).restrict (Set.Ioc x₁ x₂ ×ˢ (Set.univ : Set ℝ)) := by
    rw [← Measure.prod_restrict (s := Set.Ioc x₁ x₂) (t := (Set.univ : Set ℝ))
      (μ := volume) (ν := volume), Measure.restrict_univ]
  have hae : AEMeasurable
      (Function.uncurry (fun t y : ℝ => ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖))
      ((volume.restrict (Set.Ioc x₁ x₂)).prod volume) := by
    rw [hprod]
    exact hnorm.aemeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  have hmain := AEMeasurable.lintegral_prod_left hae
  change AEMeasurable
    (fun y : ℝ => ∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖) volume
  exact hmain

private theorem horizMass_le' {a b m : ℝ} (_hab : a < b) {g : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ g {w : ℂ | a < w.re ∧ w.re < b})
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖g ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) (h12 : x₁ < x₂) :
    ∫⁻ y : ℝ, horizMass g x₁ x₂ y ≤ ENNReal.ofReal ((x₂ - x₁) * max m 0) := by
  have hnorm : ContinuousOn
      (fun p : ℝ × ℝ => ENNReal.ofReal ‖g ((p.1 : ℂ) + p.2 * Complex.I)‖)
      (Set.Ioc x₁ x₂ ×ˢ (Set.univ : Set ℝ)) :=
    ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_pair_comp' hhol h₁ h₂).norm
  have hae : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal ‖g ((p.1 : ℂ) + p.2 * Complex.I)‖)
      ((volume.prod volume).restrict (Set.Ioc x₁ x₂ ×ˢ (Set.univ : Set ℝ))) :=
    hnorm.aemeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  calc ∫⁻ y : ℝ, horizMass g x₁ x₂ y
      = ∫⁻ y in (Set.univ : Set ℝ), ∫⁻ t in Set.Ioc x₁ x₂,
          ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖ := by
        simp only [horizMass, Measure.restrict_univ]
    _ = ∫⁻ z in Set.Ioc x₁ x₂ ×ˢ (Set.univ : Set ℝ),
          ENNReal.ofReal ‖g ((z.1 : ℂ) + z.2 * Complex.I)‖ :=
        (MeasureTheory.setLIntegral_prod_symm
          (fun p : ℝ × ℝ => ENNReal.ofReal ‖g ((p.1 : ℂ) + p.2 * Complex.I)‖) hae).symm
    _ = ∫⁻ t in Set.Ioc x₁ x₂, ∫⁻ y in (Set.univ : Set ℝ),
          ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖ :=
        MeasureTheory.setLIntegral_prod _ hae
    _ ≤ ∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal (max m 0) := by
        rw [← lintegral_indicator measurableSet_Ioc
              (fun t : ℝ => ∫⁻ y in (Set.univ : Set ℝ),
                ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖),
            ← lintegral_indicator measurableSet_Ioc (fun _ : ℝ => ENNReal.ofReal (max m 0))]
        apply lintegral_mono
        intro t
        by_cases ht : t ∈ Set.Ioc x₁ x₂
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          have ht' := mem_strip_of_mem_Ioc' h₁ h₂ ht
          calc ∫⁻ y in (Set.univ : Set ℝ), ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖
              = ∫⁻ y : ℝ, ENNReal.ofReal ‖g ((t : ℂ) + y * Complex.I)‖ := by simp
            _ ≤ ENNReal.ofReal m := hmass t ht'
            _ ≤ ENNReal.ofReal (max m 0) := ENNReal.ofReal_le_ofReal (le_max_left m 0)
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
    _ = ENNReal.ofReal (max m 0) * volume (Set.Ioc x₁ x₂) :=
        MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal ((x₂ - x₁) * max m 0) := by
        rw [Real.volume_Ioc, ENNReal.ofReal_mul (le_of_lt (sub_pos.mpr h12))]
        exact mul_comm _ _

/-! ## Elementary complex-analysis facts about `cot (π ·)` -/

/-- `sin (π w) ≠ 0` when the real part of `w` lies in `(-1, 0)`. -/
private lemma sin_pi_ne_zero_of_re_mem {w : ℂ} (hw : w.re ∈ Set.Ioo (-1 : ℝ) 0) :
    Complex.sin (Real.pi * w) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have h2 : Real.pi * w.re = (k : ℝ) * Real.pi := by
    have h' : ((Real.pi : ℂ) * w).re = (((k : ℤ) : ℂ) * (Real.pi : ℂ)).re := by rw [hk]
    simpa using h'
  have h3 : w.re = (k : ℝ) := by
    have h2' : Real.pi * w.re = Real.pi * (k : ℝ) := by rw [h2]; ring
    exact mul_left_cancel₀ Real.pi_ne_zero h2'
  exact intCast_ne_of_mem_Ioo hw k h3.symm

/-- Continuity of `cot (π (φ ·))` at a point where `sin` does not vanish. -/
private lemma continuousAt_cot_pi_comp {φ : ℝ → ℂ} (hφ : Continuous φ) {t : ℝ}
    (hre : (φ t).re ∈ Set.Ioo (-1 : ℝ) 0) :
    ContinuousAt (fun s : ℝ => Complex.cot (Real.pi * (φ s))) t := by
  have h1 : ContinuousAt (fun x : ℂ => Complex.cot (Real.pi * x)) (φ t) :=
    ContinuousAt.comp (continuousAt_cot_of_sin_ne (sin_pi_ne_zero_of_re_mem hre))
      (continuousAt_const.mul continuousAt_id)
  exact h1.comp hφ.continuousAt

/-- Continuity of `cot (π (· - z))` along a horizontal line `t ↦ t + u*I` with `t ∈ [p,q]`,
where `[p,q]` lies in `(z.re - 1, z.re)` (so that no pole is met). -/
private lemma continuousOn_cot_pi_horiz {p q : ℝ} {z : ℂ} {u : ℝ}
    (hz₁ : z.re - 1 < p) (hz₂ : q < z.re) :
    ContinuousOn (fun t : ℝ => Complex.cot (Real.pi * ((t : ℂ) + u * Complex.I - z)))
      (Set.Icc p q) := by
  intro t ht
  refine (continuousAt_cot_pi_comp (φ := fun t : ℝ => (t : ℂ) + u * Complex.I - z)
    (by continuity) ?_).continuousWithinAt
  have hre : ((t : ℂ) + u * Complex.I - z).re = t - z.re := by simp
  rw [hre]
  exact ⟨by linarith [ht.1, hz₁], by linarith [ht.2, hz₂]⟩

/-! ## A sequence of heights along which a slice mass is small -/

/-- A function on `ℝ` with finite lintegral is small at arbitrarily large heights, on both
sides simultaneously. -/
private lemma exists_seq_mass_small {mass : ℝ → ENNReal} (hmeas : AEMeasurable mass volume)
    (hfin : ∫⁻ y : ℝ, mass y < ⊤) :
    ∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧ (∀ n : ℕ, (n : ℝ) < u n) ∧
      (∀ n : ℕ, (mass (u n)).toReal ≤ ((n : ℝ) + 1)⁻¹) ∧
      (∀ n : ℕ, (mass (-(u n))).toReal ≤ ((n : ℝ) + 1)⁻¹) := by
  have haefin : ∀ᵐ y ∂(volume : Measure ℝ), mass y < ⊤ := ae_lt_top' hmeas hfin.ne
  have hlin : ∫⁻ y : ℝ, ENNReal.ofReal ((mass y).toReal) = ∫⁻ y : ℝ, mass y := by
    refine lintegral_congr_ae ?_
    filter_upwards [haefin] with y hy
    exact ENNReal.ofReal_toReal hy.ne
  have hfint : Integrable (fun y : ℝ => (mass y).toReal) := by
    refine ⟨hmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ y : ℝ, ENNReal.ofReal ‖(mass y).toReal‖
        = ∫⁻ y : ℝ, ENNReal.ofReal ((mass y).toReal) := by
          refine lintegral_congr_ae (Eventually.of_forall (fun y => ?_))
          show ENNReal.ofReal ‖(mass y).toReal‖ = ENNReal.ofReal ((mass y).toReal)
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      _ = ∫⁻ y : ℝ, mass y := hlin
      _ < ⊤ := hfin
  have hgint : Integrable (fun y : ℝ => (mass y).toReal + (mass (-y)).toReal) :=
    hfint.add (hfint.comp_neg)
  have hkey : ∀ n : ℕ, ∃ x : ℝ, (n : ℝ) < x ∧
      (mass x).toReal + (mass (-x)).toReal < ((n : ℝ) + 1)⁻¹ := by
    intro n
    obtain ⟨x, hx1, hx2⟩ := exists_gt_abs_lt hgint (n : ℝ) (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)
    refine ⟨x, hx1, ?_⟩
    rw [abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] at hx2
    exact hx2
  choose u hu1 hu2 using hkey
  have hsum : ∀ n : ℕ, (mass (u n)).toReal + (mass (-(u n))).toReal < ((n : ℝ) + 1)⁻¹ :=
    fun n => hu2 n
  refine ⟨u, tendsto_atTop_mono (fun n => le_of_lt (hu1 n)) tendsto_natCast_atTop_atTop, hu1, ?_, ?_⟩
  · intro n
    have h1 : (mass (u n)).toReal ≤ (mass (u n)).toReal + (mass (-(u n))).toReal :=
      le_add_of_nonneg_right ENNReal.toReal_nonneg
    linarith [hsum n]
  · intro n
    have h1 : (mass (-(u n))).toReal ≤ (mass (u n)).toReal + (mass (-(u n))).toReal :=
      le_add_of_nonneg_left ENNReal.toReal_nonneg
    linarith [hsum n]

/-- The horizontal slice mass of a holomorphic function on a strip is finite. -/
private lemma horizMass_ne_top {a b : ℝ} {g : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ g {w : ℂ | a < w.re ∧ w.re < b})
    {x₁ x₂ Y : ℝ} (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) (h12 : x₁ < x₂) :
    horizMass g x₁ x₂ Y ≠ ⊤ := by
  have hcont : ContinuousOn (fun t : ℝ => g ((t : ℂ) + Y * Complex.I)) (Set.Icc x₁ x₂) := by
    refine hhol.continuousOn.comp ?_ ?_
    · fun_prop
    · intro t ht
      simp only [Set.mem_ofPred_eq]
      rw [re_add_mul_I']
      exact ⟨lt_of_lt_of_le h₁.1 ht.1, lt_of_le_of_lt ht.2 h₂.2⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmono : horizMass g x₁ x₂ Y
      ≤ ∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal (max M 0) := by
    rw [horizMass,
      ← lintegral_indicator measurableSet_Ioc (fun t : ℝ => ENNReal.ofReal ‖g ((t : ℂ) + Y * Complex.I)‖),
      ← lintegral_indicator measurableSet_Ioc (fun _ : ℝ => ENNReal.ofReal (max M 0))]
    apply lintegral_mono
    intro t
    by_cases ht : t ∈ Set.Ioc x₁ x₂
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      refine ENNReal.ofReal_le_ofReal (le_trans (hM t (Set.Ioc_subset_Icc_self ht)) ?_)
      exact le_max_left M 0
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  refine ne_of_lt (lt_of_le_of_lt hmono ?_)
  rw [setLIntegral_const, Real.volume_Ioc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-! ## The horizontal contributions vanish along a sequence -/

/-- **The horizontal contributions of the cotangent contour integral vanish along a sequence.**
For `h` holomorphic on a strip with bounded line masses, if `cot (π ·)` is bounded on the
rectangle spanned by `[x₁,x₂]` (which is the case when the rectangle avoids the poles, i.e.
`[x₁ - z.re, x₂ - z.re] ⊂ (-1,0)`) then the horizontal segments `t ↦ t + v n * I`, `t ∈ [x₁,x₂]`,
contribute nothing in the limit, provided the `‖h‖`-mass of the horizontal segment at height
`v n` tends to zero. -/
private lemma horiz_tendsto_zero {a b m : ℝ} {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {w : ℂ | a < w.re ∧ w.re < b})
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) (h12 : x₁ < x₂)
    {z : ℂ} (hz₁ : z.re - 1 < x₁) (hz₂ : x₂ < z.re) {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ s : ℂ, s.re ∈ Set.Icc (x₁ - z.re) (x₂ - z.re) → ‖Complex.cot (Real.pi * s)‖ ≤ C)
    {v : ℕ → ℝ} (hv : ∀ n : ℕ, (horizMass h x₁ x₂ (v n)).toReal ≤ ((n : ℝ) + 1)⁻¹) :
    Tendsto (fun n : ℕ => ∫ t : ℝ in x₁..x₂, h ((t : ℂ) + (v n) * Complex.I) *
      Complex.cot (Real.pi * ((t : ℂ) + (v n) * Complex.I - z))) atTop (nhds 0) := by
  have hab : a < b := lt_trans h₁.1 (lt_trans h12 h₂.2)
  -- bound the horizontal integral by the slice mass
  have hbound : ∀ (Y r : ℝ), (horizMass h x₁ x₂ Y).toReal ≤ r →
      ‖∫ t : ℝ in x₁..x₂, h ((t : ℂ) + Y * Complex.I) *
        Complex.cot (Real.pi * ((t : ℂ) + Y * Complex.I - z))‖ ≤ C * r := by
    intro Y r hr
    set F : ℝ → ℂ := fun t => h ((t : ℂ) + Y * Complex.I) *
        Complex.cot (Real.pi * ((t : ℂ) + Y * Complex.I - z)) with hF
    have hcotcont : ContinuousOn
        (fun t : ℝ => Complex.cot (Real.pi * ((t : ℂ) + Y * Complex.I - z))) (Set.Icc x₁ x₂) :=
      continuousOn_cot_pi_horiz hz₁ hz₂
    have hFcont : ContinuousOn F (Set.Ioc x₁ x₂) := by
      rw [hF]
      exact (continuousOn_line_comp' hhol h₁ h₂ Y).mul (hcotcont.mono Set.Ioc_subset_Icc_self)
    have hpt : ∀ t ∈ Set.Ioc x₁ x₂, ‖F t‖ ≤ C * ‖h ((t : ℂ) + Y * Complex.I)‖ := by
      intro t ht
      have htI : t ∈ Set.Icc x₁ x₂ := Set.Ioc_subset_Icc_self ht
      have hre : (((t : ℂ) + Y * Complex.I - z)).re = t - z.re := by simp
      have hb := hCb ((t : ℂ) + Y * Complex.I - z)
        (by rw [hre]; exact ⟨by linarith [htI.1, hz₁], by linarith [htI.2, hz₂]⟩)
      rw [hF]
      rw [norm_mul]
      calc ‖h ((t : ℂ) + Y * Complex.I)‖ * ‖Complex.cot (Real.pi * ((t : ℂ) + Y * Complex.I - z))‖
          ≤ ‖h ((t : ℂ) + Y * Complex.I)‖ * C :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = C * ‖h ((t : ℂ) + Y * Complex.I)‖ := by ring
    have hlin : ∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal ‖F t‖
        ≤ ENNReal.ofReal C * horizMass h x₁ x₂ Y := by
      calc ∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal ‖F t‖
          ≤ ∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal (C * ‖h ((t : ℂ) + Y * Complex.I)‖) := by
            rw [← lintegral_indicator measurableSet_Ioc (fun t : ℝ => ENNReal.ofReal ‖F t‖),
              ← lintegral_indicator measurableSet_Ioc
                (fun t : ℝ => ENNReal.ofReal (C * ‖h ((t : ℂ) + Y * Complex.I)‖))]
            apply lintegral_mono
            intro t
            by_cases ht : t ∈ Set.Ioc x₁ x₂
            · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
              exact ENNReal.ofReal_le_ofReal (hpt t ht)
            · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
        _ = ENNReal.ofReal C * ∫⁻ t in Set.Ioc x₁ x₂,
              ENNReal.ofReal ‖h ((t : ℂ) + Y * Complex.I)‖ := by
            rw [lintegral_congr (fun t => ENNReal.ofReal_mul hC)]
            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal C * horizMass h x₁ x₂ Y := rfl
    have hfin' : ENNReal.ofReal C * horizMass h x₁ x₂ Y ≠ ⊤ :=
      ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_top_iff_ne_top.mpr (horizMass_ne_top hhol h₁ h₂ h12)))
    calc ‖∫ t : ℝ in x₁..x₂, F t‖ ≤ ∫ t : ℝ in x₁..x₂, ‖F t‖ :=
          intervalIntegral.norm_integral_le_integral_norm h12.le
      _ = (∫⁻ t in Set.Ioc x₁ x₂, ENNReal.ofReal ‖F t‖).toReal :=
          intervalIntegral_eq_toReal_lintegral' h12 hFcont
      _ ≤ (ENNReal.ofReal C * horizMass h x₁ x₂ Y).toReal :=
          ENNReal.toReal_mono hfin' hlin
      _ = C * (horizMass h x₁ x₂ Y).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
      _ ≤ C * r := mul_le_mul_of_nonneg_left hr hC
  have hlim : Tendsto (fun n : ℕ => C * ((n : ℝ) + 1)⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).const_mul C
  have hb : ∀ᶠ n in atTop, ‖∫ t : ℝ in x₁..x₂, h ((t : ℂ) + (v n) * Complex.I) *
        Complex.cot (Real.pi * ((t : ℂ) + (v n) * Complex.I - z))‖ ≤ C * ((n : ℝ) + 1)⁻¹ :=
    Eventually.of_forall (fun n => hbound (v n) ((n : ℝ) + 1)⁻¹ (hv n))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) hb hlim)

/-! ## Integrability along a vertical line -/

/-- Along a vertical line `x + i·y` of the strip on which `g` is holomorphic, avoiding the poles of
`cot (π (· - z))`, the function `y ↦ g (x + i y) * cot (π (x + i y - z))` is integrable as soon as
the line mass of `‖g‖` is finite. -/
private lemma integrableLineCot {a b m x C : ℝ} {q : ℂ → ℂ} {z : ℂ}
    (hC : 0 ≤ C) (hx : x ∈ Set.Ioo a b) (hxz : x - z.re ∈ Set.Ioo (-1 : ℝ) 0)
    (hhol : DifferentiableOn ℂ q {w : ℂ | a < w.re ∧ w.re < b})
    (hmass : ∫⁻ y : ℝ, ENNReal.ofReal ‖q ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    (hCb : ∀ y : ℝ, ‖Complex.cot (Real.pi * ((x : ℂ) + y * Complex.I - z))‖ ≤ C) :
    MeasureTheory.Integrable (fun y : ℝ => q ((x : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((x : ℂ) + y * Complex.I - z))) := by
  have hstrip : ∀ y : ℝ, (x : ℂ) + y * Complex.I ∈ {w : ℂ | a < w.re ∧ w.re < b} := by
    intro y
    have hre : ((x : ℂ) + y * Complex.I).re = x := by simp
    simpa [hre] using hx
  have hcontq : Continuous fun y : ℝ => q ((x : ℂ) + y * Complex.I) :=
    hhol.continuousOn.comp_continuous (by continuity) hstrip
  have hcontcot : Continuous fun y : ℝ => Complex.cot (Real.pi * ((x : ℂ) + y * Complex.I - z)) := by
    rw [continuous_iff_continuousAt]
    intro y
    refine continuousAt_cot_pi_comp (φ := fun y : ℝ => (x : ℂ) + y * Complex.I - z)
      (by continuity) ?_
    have hre : ((x : ℂ) + y * Complex.I - z).re = x - z.re := by simp
    rwa [hre]
  have hint : MeasureTheory.Integrable fun y : ℝ => q ((x : ℂ) + y * Complex.I) :=
    ⟨hcontq.aestronglyMeasurable, by
      rw [MeasureTheory.hasFiniteIntegral_iff_norm]
      exact lt_of_le_of_lt hmass ENNReal.ofReal_lt_top⟩
  refine MeasureTheory.Integrable.mono'
    (g := fun y : ℝ => C * ‖q ((x : ℂ) + y * Complex.I)‖) (hint.norm.const_mul C) ?_ ?_
  · exact (hcontq.mul hcontcot).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    calc ‖q ((x : ℂ) + y * Complex.I)‖ * ‖Complex.cot (Real.pi * ((x : ℂ) + y * Complex.I - z))‖
        ≤ ‖q ((x : ℂ) + y * Complex.I)‖ * C :=
          mul_le_mul_of_nonneg_left (hCb y) (norm_nonneg _)
      _ = C * ‖q ((x : ℂ) + y * Complex.I)‖ := by ring

/-! ## Holomorphy of the integrand on a pole-free rectangle -/

/-- `ζ ↦ h ζ * (I/2 * cot (π (ζ - z)))` is holomorphic on the rectangle `[c₁,c₂] × [-Y,Y]` when
that rectangle lies in the strip and strictly between the poles `z - k` and `z` of the kernel. -/
private lemma cotContourRectHolo {a b c₁ c₂ Y : ℝ} {h : ℂ → ℂ} {z : ℂ}
    (hhol : DifferentiableOn ℂ h {w : ℂ | a < w.re ∧ w.re < b})
    (hc₁ : c₁ ∈ Set.Ioo a b) (hc₂ : c₂ ∈ Set.Ioo a b) (h₁₂ : c₁ < c₂)
    (hz₁ : z.re - 1 < c₁) (hz₂ : c₂ < z.re) :
    DifferentiableOn ℂ (fun ζ : ℂ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))))
      (Set.uIcc c₁ c₂ ×ℂ Set.uIcc (-Y) Y) := by
  intro ζ hζ
  rw [Complex.mem_reProdIm] at hζ
  have hζ1 : c₁ ≤ ζ.re := by
    have h := hζ.1
    rw [Set.uIcc_of_le h₁₂.le, Set.mem_Icc] at h
    exact h.1
  have hζ2 : ζ.re ≤ c₂ := by
    have h := hζ.1
    rw [Set.uIcc_of_le h₁₂.le, Set.mem_Icc] at h
    exact h.2
  have hζstrip : ζ ∈ {w : ℂ | a < w.re ∧ w.re < b} :=
    ⟨lt_of_lt_of_le hc₁.1 hζ1, lt_of_le_of_lt hζ2 hc₂.2⟩
  have hdiffh : DifferentiableAt ℂ h ζ := hhol.differentiableAt
    (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hζstrip)
  have hre : (ζ - z).re ∈ Set.Ioo (-1 : ℝ) 0 := by
    have h1 : (ζ - z).re = ζ.re - z.re := by simp
    rw [h1]
    exact ⟨by linarith, by linarith⟩
  have hdiffc : DifferentiableAt ℂ (fun v : ℂ => Complex.cot (Real.pi * (v - z))) ζ :=
    (differentiableAt_cot_pi_of_sin_ne (w := ζ - z) (sin_pi_ne_zero_of_re_mem hre)).comp ζ
      (differentiableAt_id.sub_const z)
  exact (hdiffh.mul (differentiableAt_const (Complex.I / 2) |>.mul hdiffc)).differentiableWithinAt

/-! ## The main theorem -/

/-- **Independence of the cotangent contour integral of the line.**  For `h` holomorphic on the
strip `{a < Re < b}` with bounded masses on the vertical lines, the Cauchy-type integral
`c ↦ ∫_y h (c + y*I) cot (π (c + y*I - z))` does not depend on the line `c ∈ (z.re - 1, z.re)`
(the two horizontal sides of the rectangle `[c₁,c₂] × [-Y,Y]` have vanishing `‖h‖`-mass along a
suitable sequence of heights and the closed rectangle contains no pole of the kernel). -/
theorem cotContourIndep {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {c₁ c₂ : ℝ} (hc₁ : c₁ ∈ Set.Ioo a b) (hc₂ : c₂ ∈ Set.Ioo a b) (h₁₂ : c₁ < c₂)
    {z : ℂ} (hz₁ : z.re - 1 < c₁) (hz₂ : c₂ < z.re) :
    (∫ y : ℝ, h ((c₁ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z))) =
      (∫ y : ℝ, h ((c₂ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z))) := by
  obtain ⟨C₀, hC₀⟩ := existsNormCotPiLe (p := c₁ - z.re) (q := c₂ - z.re) (by linarith)
    (by linarith)
  set C : ℝ := max C₀ 1 with hCdef
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hCb : ∀ s : ℂ, s.re ∈ Set.Icc (c₁ - z.re) (c₂ - z.re) → ‖Complex.cot (Real.pi * s)‖ ≤ C :=
    fun s hs => le_trans (hC₀ s hs) (le_max_left _ _)
  have hre₁ : c₁ - z.re ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
  have hre₂ : c₂ - z.re ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
  have hre_eq₁ : ∀ y : ℝ, (((c₁ : ℂ) + y * Complex.I - z)).re = c₁ - z.re := fun y => by simp
  have hre_eq₂ : ∀ y : ℝ, (((c₂ : ℂ) + y * Complex.I - z)).re = c₂ - z.re := fun y => by simp
  have hCb₁ : ∀ y : ℝ, ‖Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z))‖ ≤ C := fun y =>
    hCb _ (by rw [hre_eq₁ y]; exact ⟨le_refl _, by linarith⟩)
  have hCb₂ : ∀ y : ℝ, ‖Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z))‖ ≤ C := fun y =>
    hCb _ (by rw [hre_eq₂ y]; exact ⟨by linarith, le_refl _⟩)
  -- integrability of the two line integrands
  have hI₁ : MeasureTheory.Integrable (fun y : ℝ => h ((c₁ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z))) :=
    integrableLineCot hC hc₁ hre₁ hhol (hmass c₁ hc₁) hCb₁
  have hI₂ : MeasureTheory.Integrable (fun y : ℝ => h ((c₂ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z))) :=
    integrableLineCot hC hc₂ hre₂ hhol (hmass c₂ hc₂) hCb₂
  have ht₁ : Tendsto (fun Y : ℝ => ∫ y : ℝ in (-Y)..Y, h ((c₁ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z))) atTop
      (nhds (∫ y : ℝ, h ((c₁ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z)))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hI₁ tendsto_neg_atTop_atBot tendsto_id
  have ht₂ : Tendsto (fun Y : ℝ => ∫ y : ℝ in (-Y)..Y, h ((c₂ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z))) atTop
      (nhds (∫ y : ℝ, h ((c₂ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z)))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hI₂ tendsto_neg_atTop_atBot tendsto_id
  -- the sequence of heights
  have hmeasH : AEMeasurable (horizMass h c₁ c₂) volume := horizMass_aemeasurable' hhol hc₁ hc₂
  have hfinH : ∫⁻ y : ℝ, horizMass h c₁ c₂ y < ⊤ :=
    lt_of_le_of_lt (horizMass_le' hab hhol hmass hc₁ hc₂ h₁₂) ENNReal.ofReal_lt_top
  obtain ⟨u, hutop, hu0, hu1, hu2⟩ := exists_seq_mass_small hmeasH hfinH
  set w : ℕ → ℝ := fun n => -(u n) with hw
  have hA : Tendsto (fun n : ℕ => ∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (u n) * Complex.I) *
      Complex.cot (Real.pi * ((t : ℂ) + (u n) * Complex.I - z))) atTop (nhds 0) :=
    horiz_tendsto_zero hhol hmass hc₁ hc₂ h₁₂ hz₁ hz₂ hC hCb hu1
  have hB : Tendsto (fun n : ℕ => ∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (w n) * Complex.I) *
      Complex.cot (Real.pi * ((t : ℂ) + (w n) * Complex.I - z))) atTop (nhds 0) :=
    horiz_tendsto_zero hhol hmass hc₁ hc₂ h₁₂ hz₁ hz₂ hC hCb (v := w) (fun n => hu2 n)
  have hB' : Tendsto (fun n : ℕ => ∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (-(u n)) * Complex.I) *
      Complex.cot (Real.pi * ((t : ℂ) + (-(u n)) * Complex.I - z))) atTop (nhds 0) := by
    refine hB.congr' (Eventually.of_forall (fun n => ?_))
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [hw, Complex.ofReal_neg]
  -- the rectangle identity
  set F : ℂ → ℂ := fun ζ => h ζ * (Complex.I / 2 * Complex.cot (Real.pi * (ζ - z))) with hF
  have hFbot : ∀ Y : ℝ, (∫ x : ℝ in c₁..c₂, F ((x : ℂ) + (-Y) * Complex.I)) =
      (Complex.I / 2) * (∫ x : ℝ in c₁..c₂, h ((x : ℂ) + (-Y) * Complex.I) *
        Complex.cot (Real.pi * ((x : ℂ) + (-Y) * Complex.I - z))) := by
    intro Y
    have hpt : ∀ x : ℝ, F ((x : ℂ) + (-Y) * Complex.I) =
        (Complex.I / 2) * (h ((x : ℂ) + (-Y) * Complex.I) *
          Complex.cot (Real.pi * ((x : ℂ) + (-Y) * Complex.I - z))) := by
      intro x; simp only [hF]; ring
    rw [show (∫ x : ℝ in c₁..c₂, F ((x : ℂ) + (-Y) * Complex.I)) =
        (∫ x : ℝ in c₁..c₂, (Complex.I / 2) * (h ((x : ℂ) + (-Y) * Complex.I) *
          Complex.cot (Real.pi * ((x : ℂ) + (-Y) * Complex.I - z)))) from
      intervalIntegral.integral_congr (fun x _ => hpt x)]
    exact intervalIntegral.integral_const_mul _ _
  have hFtop : ∀ Y : ℝ, (∫ x : ℝ in c₁..c₂, F ((x : ℂ) + Y * Complex.I)) =
      (Complex.I / 2) * (∫ x : ℝ in c₁..c₂, h ((x : ℂ) + Y * Complex.I) *
        Complex.cot (Real.pi * ((x : ℂ) + Y * Complex.I - z))) := by
    intro Y
    have hpt : ∀ x : ℝ, F ((x : ℂ) + Y * Complex.I) =
        (Complex.I / 2) * (h ((x : ℂ) + Y * Complex.I) *
          Complex.cot (Real.pi * ((x : ℂ) + Y * Complex.I - z))) := by
      intro x; simp only [hF]; ring
    rw [show (∫ x : ℝ in c₁..c₂, F ((x : ℂ) + Y * Complex.I)) =
        (∫ x : ℝ in c₁..c₂, (Complex.I / 2) * (h ((x : ℂ) + Y * Complex.I) *
          Complex.cot (Real.pi * ((x : ℂ) + Y * Complex.I - z)))) from
      intervalIntegral.integral_congr (fun x _ => hpt x)]
    exact intervalIntegral.integral_const_mul _ _
  have hFvert : ∀ (c Y : ℝ), (∫ y : ℝ in (-Y)..Y, F ((c : ℂ) + y * Complex.I)) =
      (Complex.I / 2) * (∫ y : ℝ in (-Y)..Y, h ((c : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + y * Complex.I - z))) := by
    intro c Y
    have hpt : ∀ y : ℝ, F ((c : ℂ) + y * Complex.I) =
        (Complex.I / 2) * (h ((c : ℂ) + y * Complex.I) *
          Complex.cot (Real.pi * ((c : ℂ) + y * Complex.I - z))) := by
      intro y; simp only [hF]; ring
    rw [show (∫ y : ℝ in (-Y)..Y, F ((c : ℂ) + y * Complex.I)) =
        (∫ y : ℝ in (-Y)..Y, (Complex.I / 2) * (h ((c : ℂ) + y * Complex.I) *
          Complex.cot (Real.pi * ((c : ℂ) + y * Complex.I - z)))) from
      intervalIntegral.integral_congr (fun y _ => hpt y)]
    exact intervalIntegral.integral_const_mul _ _
  have hrect : ∀ n : ℕ, (Complex.I / 2) * (∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (-(u n)) * Complex.I) *
        Complex.cot (Real.pi * ((t : ℂ) + (-(u n)) * Complex.I - z)))
      - (Complex.I / 2) * (∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (u n) * Complex.I) *
        Complex.cot (Real.pi * ((t : ℂ) + (u n) * Complex.I - z)))
      + Complex.I * ((Complex.I / 2) * (∫ y : ℝ in (-(u n))..(u n),
          h ((c₂ : ℂ) + y * Complex.I) * Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z))))
      - Complex.I * ((Complex.I / 2) * (∫ y : ℝ in (-(u n))..(u n),
          h ((c₁ : ℂ) + y * Complex.I) * Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z))))
      = 0 := by
    intro n
    have hYpos : -(u n) < u n := by
      have h := hu0 n
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h0 : rectB c₁ c₂ (u n) F = 0 :=
      rectB_eq_zero_of_differentiableOn h₁₂ hYpos
        (cotContourRectHolo hhol hc₁ hc₂ h₁₂ hz₁ hz₂)
    rw [rectB, hFbot (u n), hFtop (u n), hFvert c₂ (u n), hFvert c₁ (u n)] at h0
    exact h0
  have halg : ∀ n : ℕ,
      (∫ y : ℝ in (-(u n))..(u n), h ((c₂ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z)))
      - (∫ y : ℝ in (-(u n))..(u n), h ((c₁ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z)))
      = Complex.I * ((∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (-(u n)) * Complex.I) *
        Complex.cot (Real.pi * ((t : ℂ) + (-(u n)) * Complex.I - z)))
        - (∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (u n) * Complex.I) *
        Complex.cot (Real.pi * ((t : ℂ) + (u n) * Complex.I - z)))) := by
    intro n
    set A : ℂ := ∫ y : ℝ in (-(u n))..(u n), h ((c₂ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z)) with hAdef
    set B : ℂ := ∫ y : ℝ in (-(u n))..(u n), h ((c₁ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z)) with hBdef
    set Cc : ℂ := ∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (-(u n)) * Complex.I) *
      Complex.cot (Real.pi * ((t : ℂ) + (-(u n)) * Complex.I - z)) with hCdef
    set D : ℂ := ∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (u n) * Complex.I) *
      Complex.cot (Real.pi * ((t : ℂ) + (u n) * Complex.I - z)) with hDdef
    have hII : ∀ V : ℂ, Complex.I * (Complex.I / 2 * V) = -(1 / 2) * V := by
      intro V
      have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc Complex.I * (Complex.I / 2 * V) = (Complex.I * Complex.I) * (1 / 2) * V := by ring
        _ = -(1 / 2) * V := by rw [h]; ring
    have h0 : (Complex.I / 2) * Cc - (Complex.I / 2) * D - (1 / 2) * A + (1 / 2) * B = 0 := by
      have h := hrect n
      rw [← hAdef, ← hBdef, ← hCdef, ← hDdef] at h
      rw [hII A, hII B] at h
      linear_combination h
    have h2 : (A - B) - Complex.I * (Cc - D) = 0 := by
      linear_combination (-2 : ℂ) * h0
    exact sub_eq_zero.mp h2
  -- limits
  have hV₂ : Tendsto (fun n : ℕ => ∫ y : ℝ in (-(u n))..(u n), h ((c₂ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z))) atTop
      (nhds (∫ y : ℝ, h ((c₂ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z)))) :=
    ht₂.comp hutop
  have hV₁ : Tendsto (fun n : ℕ => ∫ y : ℝ in (-(u n))..(u n), h ((c₁ : ℂ) + y * Complex.I) *
      Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z))) atTop
      (nhds (∫ y : ℝ, h ((c₁ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z)))) :=
    ht₁.comp hutop
  have hzero : Tendsto (fun n : ℕ => (∫ y : ℝ in (-(u n))..(u n), h ((c₂ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z)))
      - (∫ y : ℝ in (-(u n))..(u n), h ((c₁ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z)))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => Complex.I * ((∫ t : ℝ in c₁..c₂,
          h ((t : ℂ) + (-(u n)) * Complex.I) *
          Complex.cot (Real.pi * ((t : ℂ) + (-(u n)) * Complex.I - z)))
        - (∫ t : ℝ in c₁..c₂, h ((t : ℂ) + (u n) * Complex.I) *
          Complex.cot (Real.pi * ((t : ℂ) + (u n) * Complex.I - z))))) atTop (nhds 0) := by
      simpa using (hB'.sub hA).const_mul Complex.I
    exact h1.congr' (Eventually.of_forall (fun n => (halg n).symm))
  have hlim : (∫ y : ℝ, h ((c₂ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₂ : ℂ) + y * Complex.I - z)))
      - (∫ y : ℝ, h ((c₁ : ℂ) + y * Complex.I) *
        Complex.cot (Real.pi * ((c₁ : ℂ) + y * Complex.I - z))) = 0 :=
    tendsto_nhds_unique (hV₂.sub hV₁) hzero
  exact (sub_eq_zero.mp hlim).symm

end

end Work.FatouL1
