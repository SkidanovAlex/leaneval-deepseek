import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.KfrU_pairing_eplus
import Submission.Work.BoseBoxFock.PCFU.aQ_aP_sq_integral_le
import Submission.Work.BoseBoxFock.PCFU.chBimg_state_le
import Submission.Work.BoseBoxFock.PCFU.chCimg_imgMass_le
import Submission.Work.BoseBoxFock.PCFU.chiScale_lowKer_image_le
import Submission.Work.BoseBoxFock.PCFU.fibre_update_sq_le
import Submission.Work.BoseBoxFock.PCFU.lowKer_abs_integral_le
import Submission.Work.BoseBoxFock.W1fun_L1_le
import Submission.Work.BoseBoxFock.lintegral_tsum_translate_boxL_le
import Submission.Work.BoseBoxFock.uvSmear_L1_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory

set_option maxHeartbeats 8000000

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The objects

`imgSumC` is the lattice-image sum of the low-momentum kernel in the `u + w` normalisation of
`chCimg`; `chCimgInt` is the integrand of `chCimg`. -/

/-- The lattice-image sum of the low-momentum kernel (`d ≠ 0` images) at the tied cutoff
`κ = 1/(d²ℓ)`, in the normalisation used by the `(C)`-channel lattice-image slot. -/
private noncomputable def imgSumC (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (u w : E3) : ℂ :=
  ∑' e : Fin 3 → ℤ, (if e = 0 then (0 : ℂ)
    else ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))

/-- The integrand of the `(C)`-channel lattice-image slot `chCimg`. -/
private noncomputable def chCimgInt {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) : ℂ :=
  ((Θ x : ℝ) : ℂ)
    * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
    * (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * KfrU v h μ fu N (x i + w)
        * (∫ u in Submission.BoseGases.acube (ellH v μ),
            imgSumC fc (chKappa v μ) (ellH v μ) u w
              * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ)))

/-- `chCimg` is the integral of its integrand. -/
private theorem chCimg_eq_integral {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) :
    chCimg v h fc fu μ N i j Θ
      = ∫ x : Submission.BoseGases.X n, chCimgInt v h fc fu μ N i j Θ x := rfl

/-- The integrand of `chCimg` vanishes off the box `abox n (sideAt μ (a v))` (it carries the box
restriction of the state). -/
private theorem chCimgInt_support {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) {x : Submission.BoseGases.X n}
    (hx : x ∉ Submission.BoseGases.abox n (ellH v μ)) :
    chCimgInt v h fc fu μ N i j (Work.BoseBoxFock.boxRestrictR (ellH v μ) Φ) x = 0 := by
  have h0 : Work.BoseBoxFock.boxRestrictR (ellH v μ) Φ x = 0 := by
    rw [Work.BoseBoxFock.boxRestrictR]
    rw [Set.indicator_of_notMem hx, mul_zero]
  rw [chCimgInt, h0]
  simp

/-! ## 2. The `χ`-weighted lattice-image bound in the `chCimg` normalisation -/

/-- The `corpusBox` bump is the corpus bump. -/
private theorem chiLam_eq_chiScale (ℓ : ℝ) :
    Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl

/-- **The `χ`-weighted lattice-image bound**, in the `u + w` (plus-shifted) form used by
`chCimg`: this is `chiScale_lowKer_image_le` with `b := -w` and the evenness of `χ_ℓ`. -/
private theorem chiLam_imageSum_le (fc : Work.BoseBoxFix.LowCut) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ d ℓ : ℝ}, 0 < d → 0 < ℓ → κ = 1 / (d ^ 2 * ℓ) →
      ∀ (w u : E3), u ∈ Submission.BoseGases.acube ℓ →
        ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
          * imgSumC fc κ ℓ u w‖ ≤ C * d ^ (2 * M) / ℓ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := chiScale_lowKer_image_le fc M
  refine ⟨C, hC0, ?_⟩
  intro κ d ℓ hd hℓ hκ w u hu
  have hχ : Submission.BoseGases.chiScale ℓ (-w) = Work.BoseK15.corpusBox.chiLam ℓ w := by
    rw [chiLam_eq_chiScale]
    exact Work.BoseB4.BoxData.chiLam_even Work.BoseK15.corpusBox ℓ w
  have hsum : imgSumC fc κ ℓ u w
      = ∑' e : Fin 3 → ℤ, if e = 0 then 0
          else ((lowKer fc κ (u - (-w) + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) := by
    refine tsum_congr fun e => ?_
    by_cases he : e = 0
    · rw [if_pos he, if_pos he]
    · rw [if_neg he, if_neg he, sub_neg_eq_add]
  have h := hC hd hℓ hκ (-w) u hu
  rw [hsum, ← hχ]
  exact h

/-- **The `u`-`L¹` mass of the lattice-image sum is uniformly bounded.**  This is
`chCimg_imgMass_le` (the tiling identity) combined with `lowKer_abs_integral_le`. -/
private theorem acube_imageSum_L1_le (fc : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ ℓ : ℝ}, 0 < κ → 0 < ℓ → ∀ w : E3,
      (∫ u in Submission.BoseGases.acube ℓ, ‖imgSumC fc κ ℓ u w‖) ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := chCimg_imgMass_le fc
  obtain ⟨C₂, hC₂0, hC₂⟩ := lowKer_abs_integral_le fc
  refine ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, ?_⟩
  intro κ ℓ hκ hℓ w
  have h1 : (∫ u in Submission.BoseGases.acube ℓ, ‖imgSumC fc κ ℓ u w‖)
      ≤ C₁ * ∫ z : E3, |lowKer fc κ z| := hC₁ hℓ hκ w
  have h2 : (∫ z : E3, |lowKer fc κ z|) ≤ C₂ := hC₂ hκ
  calc (∫ u in Submission.BoseGases.acube ℓ, ‖imgSumC fc κ ℓ u w‖)
      ≤ C₁ * (∫ z : E3, |lowKer fc κ z|) := h1
    _ ≤ C₁ * C₂ := mul_le_mul_of_nonneg_left h2 hC₁0

/-! ## 3. The uniform sup bound of the frame -/

/-- The frame is dominated by the sum of the absolute values of its weights. -/
private theorem KfrU_norm_le_sum {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : E3) :
    ‖KfrU v h μ fu N z‖ ≤ ∑ k : Lab N, |Work.BoseBoxFock.W1h v h μ fu N k| := by
  rw [KfrU]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have h2 : ‖Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))‖ ≤ 1 := by
    rw [mul_comm Complex.I ((inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  calc ‖((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))‖
      = ‖((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)‖
          * ‖Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))‖ :=
        norm_mul _ _
    _ ≤ ‖((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = |Work.BoseBoxFock.W1h v h μ fu N k| := by
        rw [mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The frame is bounded by the number of labels times the `L¹` mass of `W1fun`. -/
private theorem KfrU_norm_le {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : E3) :
    ‖KfrU v h μ fu N z‖ ≤ (Fintype.card (Lab N) : ℝ)
      * (∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|) := by
  refine (KfrU_norm_le_sum h μ fu N z).trans ?_
  calc ∑ k : Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|
      ≤ ∑ _k : Lab N, (∫ x : E3,
          |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|) :=
        Finset.sum_le_sum fun k _ => KfrU_aux_W1h_abs_le h μ fu N k
    _ = (Fintype.card (Lab N) : ℝ)
          * (∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 4. The `Ksfr`-form of the lattice-image sum

The raw lattice-image sum `imgSumC` is a `tsum` and has no usable measurability in Mathlib.  At the
tied cutoff `κ = 1/(d²ℓ)` it is, however, *equal* to the explicitly continuous function
`imgSumK = (Ksfr(·+w) + 1)/ℓ³ − Κ(·+w)` (`Ksfr_eq_lowKer` + the point removal in the `d`-sum),
provided the (free) lattice size `N'` is large enough.  This is the measurability input of the
whole chapter: it is what makes the `x`-integrand of `chCimg` a.e. strongly measurable, hence the
box-restriction `IntegrableOn`, hence the Fubini/peel reduction available. -/

/-- A universal bound on the box bump `χ_ℓ` (`χ ≤ (∫χ²)^{-1/2}`). -/
private noncomputable def chiBound : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹

private theorem chiBound_nonneg : 0 ≤ chiBound := by
  rw [chiBound]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)

private theorem chiLam_le_chiBound (ℓ : ℝ) (y : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ y ≤ chiBound := by
  rw [chiBound]
  exact Submission.BoseGases.chi_le_sqrt_inv ((ℓ⁻¹ : ℝ) • y)

private theorem latVec_zero_eq : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
  ext m
  simp [Work.BoseBoxFock.latVec]

/-- The lattice translates of `lowKer` are summable (the kernel decays like `(1+‖z‖)^{-4}`). -/
private theorem lowKer_lattice_summable' (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (z : E3) :
    Summable (fun d : Fin 3 → ℤ => lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d)) := by
  obtain ⟨C, hC0, hC⟩ := lowKer_decay fc hκ 2
  have hdec : ∀ q : E3, ‖((lowKer fc κ q : ℝ) : ℂ)‖ ≤ C * (1 + ‖q‖) ^ (-(4 : ℤ)) := by
    intro q
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hz := hC q
    rw [Real.norm_eq_abs] at hz
    have hpos : (0 : ℝ) < (1 + ‖q‖) ^ 4 := by positivity
    calc |lowKer fc κ q| = ((1 + ‖q‖) ^ 4)⁻¹ * ((1 + ‖q‖) ^ 4 * |lowKer fc κ q|) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      _ ≤ ((1 + ‖q‖) ^ 4)⁻¹ * C := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = C * (1 + ‖q‖) ^ (-(4 : ℤ)) := by
          rw [zpow_neg]
          exact mul_comm _ _
  have hs := Work.BoseBoxFock.summable_shift_latVec (Φ := fun q : E3 => ((lowKer fc κ q : ℝ) : ℂ))
    hC0 hdec hℓ z
  exact Complex.summable_ofReal.mp hs

/-- The `Ksfr`-form of the lattice-image sum: an explicitly continuous function of `(u,w)`. -/
private noncomputable def imgSumK (v : E3 → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N' : ℕ) (u w : E3) : ℂ :=
  (Ksfr v fc μ N' (u + w) + 1) / ((ellH v μ : ℂ) ^ 3)
    - ((lowKer fc (chKappa v μ) (u + w) : ℝ) : ℂ)

/-- **The `Ksfr`-evaluation of `imgSumC`.** -/
private theorem imgSumC_eq_imgSumK {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N' : ℕ}
    (hℓ : 0 < ellH v μ) (hκ : 0 < chKappa v μ)
    (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ)) (u w : E3) :
    imgSumC fc (chKappa v μ) (ellH v μ) u w = imgSumK v fc μ N' u w := by
  have hsum := lowKer_lattice_summable' fc hκ hℓ (u + w)
  have hsumC : Summable (fun d : Fin 3 → ℤ =>
      ((lowKer fc (chKappa v μ) ((u + w) + (ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hsum
  have hkey : (∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℂ)
        else ((lowKer fc (chKappa v μ) ((u + w) + (ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))
      = (∑' d : Fin 3 → ℤ,
          ((lowKer fc (chKappa v μ) ((u + w) + (ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        - ((lowKer fc (chKappa v μ) (u + w) : ℝ) : ℂ) := by
    have hs := hsumC.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
    rw [show ((u + w) + (ellH v μ) • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ))
        = u + w from by rw [latVec_zero_eq, smul_zero, add_zero]] at hs
    rw [hs]
    ring
  have hks := Ksfr_eq_lowKer (v := v) (fc := fc) (μ := μ) (N := N') (z := u + w) hℓ
    (show 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ from hκ)
    (show 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ) from hN')
  have hS : (∑' d : Fin 3 → ℤ,
        ((lowKer fc (chKappa v μ) ((u + w) + (ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = (Ksfr v fc μ N' (u + w) + 1) / ((ellH v μ : ℂ) ^ 3) := by
    have h1 : (∑' d : Fin 3 → ℤ,
          ((lowKer fc (chKappa v μ) ((u + w) + (ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        = (∑' d : Fin 3 → ℤ,
            ((lowKer fc ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹
              ((u + w) + (ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) :=
      tsum_congr fun d => by congr 2
    have hne3 : (((ellH v μ : ℝ)) : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 (by
      rw [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hℓ)
    rw [eq_div_iff hne3, h1, hks]
    ring
  rw [imgSumC, imgSumK, hkey, hS]

/-- **Measurability of the `Ksfr`-form.** -/
private theorem measurable_imgSumK {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N' : ℕ}
    (hκ : 0 < chKappa v μ) :
    Measurable (fun p : E3 × E3 => imgSumK v fc μ N' p.1 p.2) := by
  have h1 : Continuous (fun p : E3 × E3 => Ksfr v fc μ N' (p.1 + p.2)) :=
    (Work.BoseBoxFock.PCFU.continuous_Ksfr (v := v) (fc := fc) (μ := μ) (N := N')).comp
      (by fun_prop)
  have h2 : Continuous (fun p : E3 × E3 => lowKer fc (chKappa v μ) (p.1 + p.2)) :=
    ((lowKer_regular fc hκ).1).comp (by fun_prop)
  exact (((h1.add continuous_const).div_const _).sub
    (Complex.continuous_ofReal.comp h2)).measurable

/-- **Measurability of the lattice-image sum** (via the `Ksfr`-form). -/
private theorem aeStronglyMeasurable_imgSumC {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ}
    {N' : ℕ} (hℓ : 0 < ellH v μ) (hκ : 0 < chKappa v μ)
    (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ)) :
    AEStronglyMeasurable
      (fun p : E3 × E3 => imgSumC fc (chKappa v μ) (ellH v μ) p.1 p.2) volume := by
  have hcongr : (fun p : E3 × E3 => imgSumC fc (chKappa v μ) (ellH v μ) p.1 p.2)
      = fun p : E3 × E3 => imgSumK v fc μ N' p.1 p.2 := by
    funext p
    exact imgSumC_eq_imgSumK hℓ hκ hN' p.1 p.2
  rw [hcongr]
  exact (measurable_imgSumK (v := v) (fc := fc) (μ := μ) (N' := N') hκ).aestronglyMeasurable

/-! ## 5. Bounds on the state factors and the inner slot integral -/

/-- The `aP`-mean of a globally bounded configuration function is bounded by the same constant. -/
private theorem aP_abs_le_bounded {n : ℕ} {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘb : ∀ x, |Θ x| ≤ B) (i : Fin n)
    (x : Submission.BoseGases.X n) :
    |Submission.BoseGases.aP ℓ i Θ x| ≤ B := by
  have hvol : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Bornology.IsBounded.measure_lt_top (Submission.BoseGases.acube_isBounded ℓ hℓ.le)
  rw [Submission.BoseGases.aP, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ℓ ^ 3)]
  have h1 : |∫ y in Submission.BoseGases.acube ℓ, Θ (Function.update x i y)|
      ≤ ∫ y in Submission.BoseGases.acube ℓ, |Θ (Function.update x i y)| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun y : E3 => Θ (Function.update x i y)))
  have h2 : ∫ y in Submission.BoseGases.acube ℓ, |Θ (Function.update x i y)|
      ≤ ∫ y in Submission.BoseGases.acube ℓ, B := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      ?_ (Filter.Eventually.of_forall (fun y => hΘb _))
    refine IntegrableOn.of_bound hvol aestronglyMeasurable_const B
      (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg hB]
  have h4 : (volume : Measure E3).real (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def]
    have h := Submission.BoseGases.real_volume_acube ℓ hℓ.le
    rw [Measure.real_def, Measure.restrict_apply_univ] at h
    exact h
  have h3 : ∫ y in Submission.BoseGases.acube ℓ, B = B * ℓ ^ 3 := by
    rw [setIntegral_const, smul_eq_mul, h4, mul_comm]
  calc (1 / ℓ ^ 3) * |∫ y in Submission.BoseGases.acube ℓ, Θ (Function.update x i y)|
      ≤ (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, |Θ (Function.update x i y)| :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (1 / ℓ ^ 3) * (B * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left (le_trans h2 h3.le) (by positivity)
    _ = B := by field_simp

/-- The fibre deviation `aQ_j ∘aP_i` of a globally bounded function is bounded by twice the
bound. -/
private theorem aQ_aP_abs_le_bounded {n : ℕ} {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘb : ∀ x, |Θ x| ≤ B) (i j : Fin n)
    (x : Submission.BoseGases.X n) :
    |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ 2 * B := by
  have h1 : ∀ y, |Submission.BoseGases.aP ℓ i Θ y| ≤ B :=
    fun y => aP_abs_le_bounded hℓ hB hΘb i y
  have h2 : |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ B :=
    aP_abs_le_bounded hℓ hB h1 j x
  rw [Submission.BoseGases.aQ]
  calc |Submission.BoseGases.aP ℓ i Θ x
        - Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x|
      = |Submission.BoseGases.aP ℓ i Θ x
          + -(Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x)| := by ring_nf
    _ ≤ |Submission.BoseGases.aP ℓ i Θ x|
          + |-(Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x)| := abs_add_le _ _
    _ = |Submission.BoseGases.aP ℓ i Θ x|
          + |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x| := by rw [abs_neg]
    _ ≤ B + B := add_le_add (h1 x) h2
    _ = 2 * B := by ring

/-- **The inner slot integral.**  The `χ`-weighted lattice-image sum paired with the fibre
deviation is bounded by the image constant times the fibre `L¹`-mass of the deviation. -/
private theorem chCimg_inner_le {m : ℕ} {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ}
    (hℓ : 0 < ellH v μ) {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {B : ℝ}
    (hB : 0 ≤ B) (hΘb : ∀ x, |Θ x| ≤ B) (i j : Fin (m + 1)) {Cimg : ℝ}
    (himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖ ≤ Cimg)
    (w : E3) (x : Submission.BoseGases.X (m + 1)) :
    ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (∫ u in Submission.BoseGases.acube (ellH v μ),
            imgSumC fc (chKappa v μ) (ellH v μ) u w
              * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ))‖
      ≤ Cimg * ∫ u in Submission.BoseGases.acube (ellH v μ),
          |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
            (Function.update x j u)| := by
  have hvol : (volume : Measure E3) (Submission.BoseGases.acube (ellH v μ)) < ⊤ :=
    Bornology.IsBounded.measure_lt_top (Submission.BoseGases.acube_isBounded _ hℓ.le)
  set Q : E3 → ℝ := fun u => Submission.BoseGases.aQ (ellH v μ) j
    (Submission.BoseGases.aP (ellH v μ) i Θ) (Function.update x j u) with hQ
  have hQb : ∀ u, |Q u| ≤ 2 * B := fun u => aQ_aP_abs_le_bounded hℓ hB hΘb i j _
  have hQm : Measurable Q := by
    rw [hQ]
    exact (Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)).comp
      (by fun_prop : Measurable fun u : E3 => Function.update x j u)
  have hMint : Integrable (fun u => Cimg * |Q u|)
      ((volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ))) := by
    refine Integrable.const_mul ?_ Cimg
    refine IntegrableOn.of_bound hvol (hQm.abs.aestronglyMeasurable) (2 * B)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hQb u
  have hF : (fun u : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (imgSumC fc (chKappa v μ) (ellH v μ) u w * ((Q u : ℝ) : ℂ)))
      = (fun u : E3 => (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * imgSumC fc (chKappa v μ) (ellH v μ) u w) * ((Q u : ℝ) : ℂ)) := by
    funext u
    ring
  have hpt : ∀ᵐ u ∂((volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ))),
      ‖(((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * imgSumC fc (chKappa v μ) (ellH v μ) u w) * ((Q u : ℝ) : ℂ)‖ ≤ Cimg * |Q u| := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.acube_measurable _)]
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (himg w u hu) (abs_nonneg _)
  have hstep1 : ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (∫ u in Submission.BoseGases.acube (ellH v μ),
            imgSumC fc (chKappa v μ) (ellH v μ) u w * ((Q u : ℝ) : ℂ))‖
      = ‖∫ u in Submission.BoseGases.acube (ellH v μ),
          ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
            * (imgSumC fc (chKappa v μ) (ellH v μ) u w * ((Q u : ℝ) : ℂ))‖ := by
    rw [MeasureTheory.integral_const_mul]
  rw [hstep1, hF]
  refine le_trans (norm_integral_le_integral_norm
    (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ)))
    (f := fun u : E3 => (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * imgSumC fc (chKappa v μ) (ellH v μ) u w) * ((Q u : ℝ) : ℂ))) ?_
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
    hMint hpt) ?_
  rw [MeasureTheory.integral_const_mul]

/-! ## 6. Measurability and integrability of the integrand -/

/-- The box-restriction measure on `X m`. -/
private noncomputable def boxMeas (m : ℕ) (ℓ : ℝ) : Measure (Submission.BoseGases.X m) :=
  (volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ)

/-- The fibre integrand `(x,w,u) ↦ imgSumC(u,w)·Ψ(x[j↦u])` of the `chCimg` slot. -/
private noncomputable def fibreJoint {m : ℕ} (v : E3 → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ)
    (q : (Submission.BoseGases.X (m + 1) × E3) × E3) : ℂ :=
  imgSumC fc (chKappa v μ) (ellH v μ) q.2 q.1.2
    * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
        (Function.update q.1.1 j q.2) : ℝ) : ℂ)

/-- The `u`-integral of the fibre integrand: the state factor of the `(C)`-slot. -/
private noncomputable def fibreInt {m : ℕ} (v : E3 → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ)
    (p : Submission.BoseGases.X (m + 1) × E3) : ℂ :=
  ∫ u in Submission.BoseGases.acube (ellH v μ), fibreJoint v fc μ i j Θ (p, u)

/-- The `w`-integrand of the `(C)`-slot. -/
private noncomputable def chCimgW {m : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin (m + 1))
    (Θ : Submission.BoseGases.X (m + 1) → ℝ) (p : Submission.BoseGases.X (m + 1) × E3) : ℂ :=
  ((Work.BoseK15.corpusBox.chiLam (ellH v μ) p.2 : ℝ) : ℂ)
    * KfrU v h μ fu N (p.1 i + p.2) * fibreInt v fc μ i j Θ p

/-- The lattice-image sum is measurable as a function of `(u,w)` (via its `Ksfr`-form). -/
private theorem measurable_imgSumC {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N' : ℕ}
    (hℓ : 0 < ellH v μ) (hκ : 0 < chKappa v μ)
    (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ)) :
    Measurable (fun p : E3 × E3 => imgSumC fc (chKappa v μ) (ellH v μ) p.1 p.2) := by
  have hcongr : (fun p : E3 × E3 => imgSumC fc (chKappa v μ) (ellH v μ) p.1 p.2)
      = fun p : E3 × E3 => imgSumK v fc μ N' p.1 p.2 := by
    funext p
    exact imgSumC_eq_imgSumK hℓ hκ hN' p.1 p.2
  rw [hcongr]
  exact measurable_imgSumK hκ

/-- **Measurability of the fibre integrand.** -/
private theorem measurable_fibreJoint {m : ℕ} {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut}
    {μ : ℝ} {N' : ℕ} (hℓ : 0 < ellH v μ) (hκ : 0 < chKappa v μ)
    (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i j : Fin (m + 1)) :
    Measurable (fibreJoint v fc μ i j Θ) := by
  unfold fibreJoint
  exact ((measurable_imgSumC hℓ hκ hN').comp
      (by fun_prop : Measurable fun q : (Submission.BoseGases.X (m + 1) × E3) × E3 =>
        (q.2, q.1.2))).mul
    (Complex.measurable_ofReal.comp ((Work.BoseBoxFock.Weak.aQ_measurable j
      (Work.BoseBoxFock.Weak.aP_measurable i hΘm)).comp
        (by fun_prop : Measurable fun q : (Submission.BoseGases.X (m + 1) × E3) × E3 =>
          Function.update q.1.1 j q.2)))

/-- **A.e. strong measurability of the fibre integral** in `(x,w)`. -/
private theorem aestronglyMeasurable_fibreInt {m : ℕ} {v : E3 → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N' : ℕ} (hℓ : 0 < ellH v μ) (hκ : 0 < chKappa v μ)
    (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i j : Fin (m + 1)) :
    AEStronglyMeasurable (fibreInt v fc μ i j Θ)
      ((boxMeas (m + 1) (ellH v μ)).prod (volume : Measure E3)) :=
  AEStronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ)))
    (measurable_fibreJoint hℓ hκ hN' hΘm i j).aestronglyMeasurable

/-- **A.e. strong measurability of the `w`-integrand.** -/
private theorem aestronglyMeasurable_chCimgW {m : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {N' : ℕ} (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ) (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i j : Fin (m + 1)) :
    AEStronglyMeasurable (chCimgW v h fc fu μ N i j Θ)
      ((boxMeas (m + 1) (ellH v μ)).prod (volume : Measure E3)) := by
  have hfib := aestronglyMeasurable_fibreInt (m := m) (v := v) (fc := fc) (μ := μ)
    (N' := N') hℓ hκ hN' hΘm i j
  have hχc : Measurable fun w : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox (ellH v μ)).measurable
  have hKc : Measurable fun p : Submission.BoseGases.X (m + 1) × E3 =>
      KfrU v h μ fu N (p.1 i + p.2) :=
    (continuous_KfrU v h μ fu N).measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).add measurable_snd)
  exact ((hχc.comp measurable_snd).aestronglyMeasurable.mul hKc.aestronglyMeasurable).mul hfib

/-- **A.e. strong measurability of the `chCimg` integrand** on the box. -/
private theorem aestronglyMeasurable_chCimgInt {m : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N N' : ℕ} (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ) (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i j : Fin (m + 1)) :
    AEStronglyMeasurable (chCimgInt v h fc fu μ N i j Θ) (boxMeas (m + 1) (ellH v μ)) := by
  have hw := AEStronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
    (aestronglyMeasurable_chCimgW (m := m) (v := v) (h := h) (fc := fc) (fu := fu)
      (μ := μ) (N := N) (N' := N') hℓ hκ hN' hΘm i j)
  have hχc : Measurable fun w : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox (ellH v μ)).measurable
  have hpref : AEStronglyMeasurable (fun x : Submission.BoseGases.X (m + 1) =>
      ((Θ x : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ))
      (boxMeas (m + 1) (ellH v μ)) :=
    ((Complex.measurable_ofReal.comp hΘm).mul
      (hχc.comp (measurable_pi_apply i))).aestronglyMeasurable
  refine (hpref.mul hw).congr (Filter.Eventually.of_forall fun x => ?_)
  simpa only [chCimgInt, chCimgW, fibreInt, fibreJoint, Pi.mul_apply]

/-! ## 7. The pointwise bound and the integrability of the integrand on the box -/

/-- `chCimgInt` as the pre-factor times the `w`-integral of `chCimgW`. -/
private theorem chCimgInt_eq {m : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (i j : Fin (m + 1))
    (Θ : Submission.BoseGases.X (m + 1) → ℝ) (x : Submission.BoseGases.X (m + 1)) :
    chCimgInt v h fc fu μ N i j Θ x
      = ((Θ x : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
        * (∫ w : E3, chCimgW v h fc fu μ N i j Θ (x, w)) := by
  simp only [chCimgInt, chCimgW, fibreInt, fibreJoint]

/-- **The pointwise bound on the `chCimg` integrand.** -/
private theorem chCimgInt_le {m : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} (hℓ : 0 < ellH v μ) {N : ℕ}
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {M : ℝ} (hM0 : 0 ≤ M)
    (hΘb : ∀ x, |Θ x| ≤ M) (i j : Fin (m + 1)) {Cimg : ℝ} (hCimg0 : 0 ≤ Cimg)
    (himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖ ≤ Cimg)
    (x : Submission.BoseGases.X (m + 1)) :
    ‖chCimgInt v h fc fu μ N i j Θ x‖
      ≤ chiBound * Cimg * (Fintype.card (Lab N) : ℝ)
          * (∫ y : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) y|)
          * (ellH v μ) ^ 3
          * (|Θ x| * ∫ u in Submission.BoseGases.acube (ellH v μ),
              |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
                (Function.update x j u)|) := by
  set A : ℝ := ∫ u in Submission.BoseGases.acube (ellH v μ),
      |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
        (Function.update x j u)| with hA
  set CW : ℝ := ∫ y : E3,
      |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) y| with hCW
  set card : ℝ := (Fintype.card (Lab N) : ℝ) with hcard
  have hA0 : 0 ≤ A := integral_nonneg fun u => abs_nonneg _
  have hCW0 : 0 ≤ CW := integral_nonneg fun y => abs_nonneg _
  have hcard0 : 0 ≤ card := by positivity
  have hχnn : ∀ w : E3, 0 ≤ Work.BoseK15.corpusBox.chiLam (ellH v μ) w :=
    fun w => Work.BoseB4.BoxData.chiLam_nonneg _ _ w
  have hχb : ∀ w : E3, |Work.BoseK15.corpusBox.chiLam (ellH v μ) w| ≤ chiBound := fun w => by
    rw [abs_of_nonneg (hχnn w)]
    exact chiLam_le_chiBound _ w
  have hinner : ∀ w : E3, ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
      * (∫ u in Submission.BoseGases.acube (ellH v μ),
          imgSumC fc (chKappa v μ) (ellH v μ) u w
            * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
                (Function.update x j u) : ℝ) : ℂ))‖ ≤ Cimg * A :=
    fun w => chCimg_inner_le hℓ hΘm hM0 hΘb i j himg w x
  have hG : ∀ w : E3, |Work.BoseK15.corpusBox.chiLam (ellH v μ) w|
      * ‖(∫ u in Submission.BoseGases.acube (ellH v μ),
          imgSumC fc (chKappa v μ) (ellH v μ) u w
            * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
                (Function.update x j u) : ℝ) : ℂ))‖ ≤ Cimg * A := by
    intro w
    have h := hinner w
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
  have hWb : ∀ w : E3, ‖chCimgW v h fc fu μ N i j Θ (x, w)‖
      ≤ Cimg * A * card * CW
          * (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1 : ℝ)) w := by
    intro w
    by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · rw [Set.indicator_of_mem hw, mul_one]
      have h1 : ‖chCimgW v h fc fu μ N i j Θ (x, w)‖
          = |Work.BoseK15.corpusBox.chiLam (ellH v μ) w| * ‖KfrU v h μ fu N (x i + w)‖
            * ‖(∫ u in Submission.BoseGases.acube (ellH v μ),
                imgSumC fc (chKappa v μ) (ellH v μ) u w
                  * ((Submission.BoseGases.aQ (ellH v μ) j
                      (Submission.BoseGases.aP (ellH v μ) i Θ)
                      (Function.update x j u) : ℝ) : ℂ))‖ := by
        simp only [chCimgW, fibreInt, fibreJoint, Pi.mul_apply, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
      rw [h1]
      calc |Work.BoseK15.corpusBox.chiLam (ellH v μ) w| * ‖KfrU v h μ fu N (x i + w)‖
            * ‖(∫ u in Submission.BoseGases.acube (ellH v μ),
                imgSumC fc (chKappa v μ) (ellH v μ) u w
                  * ((Submission.BoseGases.aQ (ellH v μ) j
                      (Submission.BoseGases.aP (ellH v μ) i Θ)
                      (Function.update x j u) : ℝ) : ℂ))‖
          = (|Work.BoseK15.corpusBox.chiLam (ellH v μ) w|
              * ‖(∫ u in Submission.BoseGases.acube (ellH v μ),
                  imgSumC fc (chKappa v μ) (ellH v μ) u w
                    * ((Submission.BoseGases.aQ (ellH v μ) j
                        (Submission.BoseGases.aP (ellH v μ) i Θ)
                        (Function.update x j u) : ℝ) : ℂ))‖)
              * ‖KfrU v h μ fu N (x i + w)‖ := by ring
        _ ≤ (Cimg * A) * (card * CW) := by
            refine mul_le_mul (hG w) ?_ (norm_nonneg _) (mul_nonneg hCimg0 hA0)
            simpa only [hcard, hCW] using KfrU_norm_le h μ fu N (x i + w)
        _ = Cimg * A * card * CW := by ring
    · rw [Set.indicator_of_notMem hw]
      have hz : Work.BoseK15.corpusBox.chiLam (ellH v μ) w = 0 := by
        by_contra hne
        exact hw (Work.BoseB4.BoxData.chiLam_supp _ hℓ (Function.mem_support.mpr hne))
      have h0 : chCimgW v h fc fu μ N i j Θ (x, w) = 0 := by
        simp only [chCimgW, hz, Complex.ofReal_zero, zero_mul]
      rw [h0, norm_zero]
      simp
  have hmaj : Integrable (fun w : E3 => Cimg * A * card * CW
      * (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (fun _ => (1 : ℝ)) w) volume := by
    refine Integrable.const_mul ?_ _
    rw [MeasureTheory.integrable_indicator_iff (Work.BoseB4.BoxData.boxL_measurableSet _ _)]
    refine IntegrableOn.of_bound ?_ aestronglyMeasurable_const 1
      (Filter.Eventually.of_forall fun w => by simp)
    rw [Work.BoseB4.BoxData.volume_boxL _ hℓ]
    exact ENNReal.ofReal_lt_top
  have hWint : ‖∫ w : E3, chCimgW v h fc fu μ N i j Θ (x, w)‖
      ≤ Cimg * A * card * CW * (ellH v μ) ^ 3 := by
    refine le_trans (norm_integral_le_integral_norm
      (f := fun w : E3 => chCimgW v h fc fu μ N i j Θ (x, w))) ?_
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
      hmaj (Filter.Eventually.of_forall hWb)) ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator (Work.BoseB4.BoxData.boxL_measurableSet _ _),
      MeasureTheory.setIntegral_const, Measure.real_def,
      Work.BoseB4.BoxData.volume_boxL _ hℓ, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    exact le_of_eq (by ring)
  rw [chCimgInt_eq]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |Θ x| * |Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i)|
        * ‖∫ w : E3, chCimgW v h fc fu μ N i j Θ (x, w)‖
      ≤ |Θ x| * chiBound * (Cimg * A * card * CW * (ellH v μ) ^ 3) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hχb (x i)) (abs_nonneg _)) hWint
          (norm_nonneg _) (mul_nonneg (abs_nonneg _) chiBound_nonneg)
    _ = chiBound * Cimg * card * CW * (ellH v μ) ^ 3 * (|Θ x| * A) := by ring

/-! ## 8. Integrability on the box and the peeling identity -/

/-- **The integrand is integrable on the box** (dominated by `|Θ|` times the fibre `L¹`-mass of
the deviation, which is integrable by `chBimg_state_le`). -/
private theorem integrableOn_chCimgInt {m : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} (hℓ : 0 < ellH v μ) {N N' : ℕ}
    (hκ : 0 < chKappa v μ) (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {M : ℝ} (hM0 : 0 ≤ M)
    (hΘb : ∀ x, |Θ x| ≤ M) (i j : Fin (m + 1)) {Cimg : ℝ} (hCimg0 : 0 ≤ Cimg)
    (himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖ ≤ Cimg)
    (hIntA : Integrable (fun x : Submission.BoseGases.X (m + 1) =>
      |Θ x| * ∫ u in Submission.BoseGases.acube (ellH v μ),
        |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
          (Function.update x j u)|) volume) :
    IntegrableOn (chCimgInt v h fc fu μ N i j Θ)
      (Submission.BoseGases.abox (m + 1) (ellH v μ)) volume := by
  refine ((hIntA.const_mul (chiBound * Cimg * (Fintype.card (Lab N) : ℝ)
      * (∫ y : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) y|)
      * (ellH v μ) ^ 3)).restrict).mono' ?_ ?_
  · exact aestronglyMeasurable_chCimgInt (N := N) (N' := N') hℓ hκ hN' hΘm i j
  · filter_upwards with x
    exact chCimgInt_le hℓ hΘm hM0 hΘb i j hCimg0 himg x

/-- **The peeling of the `i`-th slot.** -/
private theorem chCimg_eq_peel {m : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} (hℓ : 0 < ellH v μ) {N N' : ℕ}
    (hκ : 0 < chKappa v μ) (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {M : ℝ} (hM0 : 0 ≤ M)
    (hΘb : ∀ x, |Θ x| ≤ M) (i j : Fin (m + 1)) {Cimg : ℝ} (hCimg0 : 0 ≤ Cimg)
    (himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖ ≤ Cimg)
    (hΘsupp : ∀ x, x ∉ Submission.BoseGases.abox (m + 1) (ellH v μ) → Θ x = 0)
    (hIntA : Integrable (fun x : Submission.BoseGases.X (m + 1) =>
      |Θ x| * ∫ u in Submission.BoseGases.acube (ellH v μ),
        |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
          (Function.update x j u)|) volume) :
    chCimg v h fc fu μ N i j Θ
      = ∫ r in Submission.BoseGases.abox m (ellH v μ),
          ∫ y in Submission.BoseGases.acube (ellH v μ),
            chCimgInt v h fc fu μ N i j Θ (Submission.BoseGases.kcInsN m i (y, r)) := by
  have hFint := integrableOn_chCimgInt (m := m) (v := v) (h := h) (fc := fc) (fu := fu)
    (μ := μ) (N := N) (N' := N') (Θ := Θ) hℓ hκ hN' hΘm hM0 hΘb i j hCimg0 himg hIntA
  rw [chCimg_eq_integral]
  rw [show (∫ x : Submission.BoseGases.X (m + 1), chCimgInt v h fc fu μ N i j Θ x)
      = ∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ),
          chCimgInt v h fc fu μ N i j Θ x from ?_]
  · exact Work.BoseBoxFock.abox_integral_peel_complex (n := m) (ℓ := ellH v μ) i
      (chCimgInt v h fc fu μ N i j Θ) hFint
  · rw [← MeasureTheory.integral_indicator
      (Submission.BoseGases.abox_measurable (m + 1) (ellH v μ))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Submission.BoseGases.abox (m + 1) (ellH v μ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have h0 : chCimgInt v h fc fu μ N i j Θ x = 0 := by
        simp only [chCimgInt, hΘsupp x hx, Complex.ofReal_zero, zero_mul]
      exact h0

/-! ## 9. The peeled pair `(f_r, g_r)` of the pairing step -/

/-- Updating the `j = i.succAbove j'`-slot of an inserted configuration. -/
private theorem update_kcInsN_succAbove {m : ℕ} (i : Fin (m + 1)) (j' : Fin m) (y : E3)
    (r : Submission.BoseGases.X m) (u : E3) :
    Function.update (Submission.BoseGases.kcInsN m i (y, r)) (i.succAbove j') u
      = Submission.BoseGases.kcInsN m i (y, Function.update r j' u) := by
  funext k
  by_cases hk : k = i
  · rw [hk, Function.update_apply, if_neg (Fin.succAbove_ne i j').symm,
      Submission.BoseGases.kc_insN_apply_same, Submission.BoseGases.kc_insN_apply_same]
  · obtain ⟨j'', hj''⟩ := Fin.exists_succAbove_eq hk
    rw [← hj'']
    by_cases hjj : j'' = j'
    · rw [hjj, Function.update_apply, if_pos rfl, Submission.BoseGases.kc_insN_apply_succ,
        Function.update_apply, if_pos rfl]
    · rw [Function.update_apply, if_neg (fun h => hjj (i.succAbove_right_injective h))]
      simp only [Submission.BoseGases.kc_insN_apply_succ, Function.update_apply, if_neg hjj]

/-- The fibre deviation `Ψ = Q_jP_iΘ` is independent of the first slot of an inserted
configuration: this is what makes the peeled pair well defined. -/
private theorem psi_ins_update {m : ℕ} (i : Fin (m + 1)) (j' : Fin m) (ℓ : ℝ)
    (Θ : Submission.BoseGases.X (m + 1) → ℝ) (y : E3) (r : Submission.BoseGases.X m) (u : E3) :
    Submission.BoseGases.aQ ℓ (i.succAbove j') (Submission.BoseGases.aP ℓ i Θ)
        (Function.update (Submission.BoseGases.kcInsN m i (y, r)) (i.succAbove j') u)
      = Submission.BoseGases.aQ ℓ (i.succAbove j') (Submission.BoseGases.aP ℓ i Θ)
        (Submission.BoseGases.kcInsN m i (0, Function.update r j' u)) := by
  rw [update_kcInsN_succAbove i j' y r u, Submission.BoseGases.kcInsN_update_zero]
  exact Work.BoseBoxFock.PCFU.aQ_aP_update_invariant (i := i) (j := i.succAbove j')
    (Fin.succAbove_ne i j').symm _ y

/-- The `w`-function of the peeled pairing at fixed rest `r`. -/
private noncomputable def pairF {m : ℕ} (v : E3 → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ) (j' : Fin m)
    (p : Submission.BoseGases.X m × E3) : ℂ :=
  ((Work.BoseK15.corpusBox.chiLam (ellH v μ) p.2 : ℝ) : ℂ)
    * (∫ u in Submission.BoseGases.acube (ellH v μ),
        imgSumC fc (chKappa v μ) (ellH v μ) u p.2
          * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
              (Submission.BoseGases.kcInsN m i (0, Function.update p.1 j' u)) : ℝ) : ℂ))

/-- The `y`-function of the peeled pairing at fixed rest `r`. -/
private noncomputable def pairG {m : ℕ} (v : E3 → ℝ) (μ : ℝ) (i : Fin (m + 1))
    (Θ : Submission.BoseGases.X (m + 1) → ℝ) (p : Submission.BoseGases.X m × E3) : ℂ :=
  ((Work.BoseK15.corpusBox.chiLam (ellH v μ) p.2 : ℝ) : ℂ)
    * (((Θ (Submission.BoseGases.kcInsN m i (p.2, p.1)) : ℝ)) : ℂ)

/-- The support of the box bump is contained in the box `boxL ℓ`. -/
private theorem tsupport_chiLam_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    tsupport (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ))
      ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  have h1 : Function.support (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ))
      = Function.support (fun z : E3 => Work.BoseK15.corpusBox.chiLam ℓ z) := by
    ext z
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  rw [tsupport, h1]
  exact closure_minimal (Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ)
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed

/-- **The peeled integrand is the pairing** of `pairG` and `pairF`. -/
private theorem chCimgInt_ins_eq {m : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (i : Fin (m + 1)) (j' : Fin m)
    (r : Submission.BoseGases.X m) (y : E3) :
    chCimgInt v h fc fu μ N i (i.succAbove j') Θ (Submission.BoseGases.kcInsN m i (y, r))
      = pairG v μ i Θ (r, y)
        * (∫ w : E3, KfrU v h μ fu N (y + w) * pairF v fc μ i (i.succAbove j') Θ j' (r, w)) := by
  have hA : (∫ w : E3, chCimgW v h fc fu μ N i (i.succAbove j') Θ
        (Submission.BoseGases.kcInsN m i (y, r), w))
      = ∫ w : E3, KfrU v h μ fu N (y + w)
          * pairF v fc μ i (i.succAbove j') Θ j' (r, w) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hU : (∫ u in Submission.BoseGases.acube (ellH v μ),
          fibreJoint v fc μ i (i.succAbove j') Θ
            ((Submission.BoseGases.kcInsN m i (y, r), w), u))
        = (∫ u in Submission.BoseGases.acube (ellH v μ),
            imgSumC fc (chKappa v μ) (ellH v μ) u w
              * ((Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
                  (Submission.BoseGases.aP (ellH v μ) i Θ)
                  (Submission.BoseGases.kcInsN m i
                    (0, Function.update r j' u)) : ℝ) : ℂ)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [fibreJoint]
      rw [psi_ins_update i j' (ellH v μ) Θ y r u]
    simp only [chCimgW, fibreInt, pairF]
    rw [Submission.BoseGases.kc_insN_apply_same, hU]
    ring_nf
  rw [chCimgInt_eq, Submission.BoseGases.kc_insN_apply_same, hA]
  simp only [pairG]
  ring_nf

/-- The joint integrand of `pairF` in the slot variable. -/
private noncomputable def pairFjoint {m : ℕ} (v : E3 → ℝ) (fc : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ) (j' : Fin m)
    (p : Submission.BoseGases.X m × E3) (u : E3) : ℂ :=
  imgSumC fc (chKappa v μ) (ellH v μ) u p.2
    * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
        (Submission.BoseGases.kcInsN m i (0, Function.update p.1 j' u)) : ℝ) : ℂ)

/-- `pairF` is the `χ`-weight times the `u`-integral of `pairFjoint`. -/
private theorem pairF_eq {m : ℕ} (v : E3 → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ) (j' : Fin m) :
    (pairF v fc μ i j Θ j')
      = fun p : Submission.BoseGases.X m × E3 =>
          ((Work.BoseK15.corpusBox.chiLam (ellH v μ) p.2 : ℝ) : ℂ)
            * (∫ u in Submission.BoseGases.acube (ellH v μ),
                pairFjoint v fc μ i j Θ j' p u) := rfl

/-- Measurability of the slot insertion `(y, r) ↦ kcInsN m i (y, r)`. -/
private theorem measurable_kcInsN {m : ℕ} (i : Fin (m + 1)) :
    Measurable fun p : E3 × Submission.BoseGases.X m => Submission.BoseGases.kcInsN m i p := by
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hk : k = i
  · rw [hk]
    have hfun : (fun p : E3 × Submission.BoseGases.X m => Submission.BoseGases.kcInsN m i p i)
        = fun p => p.1 := by
      funext p
      exact Submission.BoseGases.kc_insN_apply_same m i p.1 p.2
    rw [hfun]
    exact measurable_fst
  · obtain ⟨j'', hj''⟩ := Fin.exists_succAbove_eq hk
    have hfun : (fun p : E3 × Submission.BoseGases.X m => Submission.BoseGases.kcInsN m i p k)
        = fun p => p.2 j'' := by
      funext p
      rw [← hj'']
      exact Submission.BoseGases.kc_insN_apply_succ m i p.1 p.2 j''
    rw [hfun]
    exact (measurable_pi_apply j'').comp measurable_snd

/-- The `(w,u)`-integrand of the `pairF`-slice at fixed `r`, as a definition (this keeps the
`tsum` of `imgSumC` out of the statement, which is what makes the measurability proof cheap). -/
private noncomputable def pairFsliceJoint {m : ℕ} (v : E3 → ℝ) (fc : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ) (j' : Fin m)
    (r : Submission.BoseGases.X m) : E3 × E3 → ℂ :=
  fun z => imgSumC fc (chKappa v μ) (ellH v μ) z.2 z.1
        * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
            (Submission.BoseGases.kcInsN m i (0, Function.update r j' z.2)) : ℝ) : ℂ)

/-- Measurability of the joint `u`-integrand of `pairF` (used for the slice). -/
private theorem measurable_pairFjoint {m : ℕ} {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ}
    {N' : ℕ} (hℓ : 0 < ellH v μ) (hκ : 0 < chKappa v μ)
    (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i j : Fin (m + 1))
    (j' : Fin m) (r : Submission.BoseGases.X m) :
    Measurable (pairFsliceJoint v fc μ i j Θ j' r) := by
  unfold pairFsliceJoint
  exact ((measurable_imgSumC hℓ hκ hN').comp
      (by fun_prop : Measurable fun z : E3 × E3 => (z.2, z.1))).mul
    (Complex.measurable_ofReal.comp (Measurable.comp
      (Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm))
      (Measurable.comp (measurable_kcInsN i)
        (by fun_prop : Measurable fun z : E3 × E3 =>
          ((0 : E3), Function.update r j' z.2)))))

/-- The box bump vanishes off the box `boxL ℓ`. -/
private theorem chiLam_eq_zero_of_notMem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (hz : z ∉ Work.BoseK15.corpusBox.boxL ℓ) : Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
  by_contra hne
  exact hz (Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ
    (Function.mem_support.mpr hne))

/-- The box bump vanishes off the centred cube (for `0 < ℓ`). -/
private theorem chiLam_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (hz : z ∉ Submission.BoseGases.acube ℓ) : Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
  refine chiLam_eq_zero_of_notMem_boxL hℓ ?_
  rwa [Work.BoseBoxFock.boxL_eq_acube hℓ]

/-- The `w`-slice of `pairF` vanishes off the cube. -/
private theorem pairF_slice_zero {m : ℕ} {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ}
    (hℓ : 0 < ellH v μ) (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ)
    (j' : Fin m) (r : Submission.BoseGases.X m) {w : E3}
    (hw : w ∉ Submission.BoseGases.acube (ellH v μ)) : pairF v fc μ i j Θ j' (r, w) = 0 := by
  have hχ := chiLam_eq_zero_of_notMem_acube (ellH_pos v μ) hw
  simp only [pairF, hχ, Complex.ofReal_zero, zero_mul]

/-- The `y`-slice of `pairG` vanishes off the cube. -/
private theorem pairG_slice_zero {m : ℕ} {v : E3 → ℝ} {μ : ℝ} (hℓ : 0 < ellH v μ)
    (i : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ) (r : Submission.BoseGases.X m)
    {y : E3} (hy : y ∉ Submission.BoseGases.acube (ellH v μ)) : pairG v μ i Θ (r, y) = 0 := by
  have hχ := chiLam_eq_zero_of_notMem_acube hℓ hy
  simp only [pairG, hχ, Complex.ofReal_zero, zero_mul]

/-- A.e. strong measurability of the `y`-function of the peeled pairing. -/
private theorem aestronglyMeasurable_pairG_slice {m : ℕ} {v : E3 → ℝ} {μ : ℝ}
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i : Fin (m + 1))
    (r : Submission.BoseGases.X m) :
    AEStronglyMeasurable (fun y : E3 => pairG v μ i Θ (r, y)) (volume : Measure E3) := by
  have hχc : Measurable fun y : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox (ellH v μ)).measurable
  have hins : Measurable fun y : E3 => Submission.BoseGases.kcInsN m i (y, r) :=
    (measurable_kcInsN i).comp (Measurable.prod measurable_id measurable_const)
  refine ((hχc.mul (Complex.measurable_ofReal.comp (hΘm.comp hins))).aestronglyMeasurable).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [pairG, Pi.mul_apply, Function.comp_apply]

/-- A.e. strong measurability of the `w`-function of the peeled pairing (slice form). -/
private theorem aestronglyMeasurable_pairF_slice {m : ℕ} {v : E3 → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N' : ℕ} (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ) (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i j : Fin (m + 1))
    (j' : Fin m) (r : Submission.BoseGases.X m) :
    AEStronglyMeasurable (fun w : E3 => pairF v fc μ i j Θ j' (r, w)) (volume : Measure E3) := by
  have hint : AEStronglyMeasurable
      (fun w : E3 => ∫ u in Submission.BoseGases.acube (ellH v μ),
        pairFsliceJoint v fc μ i j Θ j' r (w, u))
      (volume : Measure E3) :=
    AEStronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ)))
      (measurable_pairFjoint (v := v) (fc := fc) (μ := μ) (N' := N')
        hℓ hκ hN' hΘm i j j' r).aestronglyMeasurable
  have hχc : Measurable fun w : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox (ellH v μ)).measurable
  refine ((hχc.aestronglyMeasurable.mul hint)).congr (Filter.Eventually.of_forall fun w => ?_)
  rw [pairF_eq]
  simp only [Pi.mul_apply]
  congr 1

/-- A.e. strong measurability of the fibre mean `r ↦ ∫_y Θ(ins(y,r))²`. -/
private theorem aesm_theta_ins {m : ℕ} {v : E3 → ℝ} {μ : ℝ}
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) (i : Fin (m + 1)) :
    AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
        ∫ y in Submission.BoseGases.acube (ellH v μ),
          (Θ (Submission.BoseGases.kcInsN m i (y, r))) ^ 2)
      ((volume : Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m (ellH v μ))) := by
  have hswap : Measurable fun z : Submission.BoseGases.X m × E3 => (z.2, z.1) := by
    fun_prop
  have hjoint : Measurable fun z : Submission.BoseGases.X m × E3 =>
      (Θ (Submission.BoseGases.kcInsN m i (z.2, z.1))) ^ 2 :=
    ((hΘm.comp (measurable_kcInsN i)).comp hswap).pow_const 2
  exact AEStronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ)))
    hjoint.aestronglyMeasurable

/-- A.e. strong measurability of the fibre mean `r ↦ ∫_u F(r[j' ↦ u])²`. -/
private theorem aesm_fibre_update {m : ℕ} {ℓ : ℝ} {F : Submission.BoseGases.X m → ℝ}
    (hFm : Measurable F) (j' : Fin m) :
    AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
        ∫ u in Submission.BoseGases.acube ℓ, (F (Function.update r j' u)) ^ 2)
      ((volume : Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)) := by
  have hupd : Measurable fun z : Submission.BoseGases.X m × E3 => Function.update z.1 j' z.2 := by
    fun_prop
  have hjoint : Measurable fun z : Submission.BoseGases.X m × E3 =>
      (F (Function.update z.1 j' z.2)) ^ 2 :=
    (hFm.comp hupd).pow_const 2
  exact AEStronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
    hjoint.aestronglyMeasurable

/-- A.e. strong measurability of the fibre mean `r ↦ ∫_u |F(r[j' ↦ u])|`. -/
private theorem aesm_fibre_abs {m : ℕ} {ℓ : ℝ} {F : Submission.BoseGases.X m → ℝ}
    (hFm : Measurable F) (j' : Fin m) :
    AEStronglyMeasurable (fun r : Submission.BoseGases.X m =>
        ∫ u in Submission.BoseGases.acube ℓ, |F (Function.update r j' u)|)
      ((volume : Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)) := by
  have hupd : Measurable fun z : Submission.BoseGases.X m × E3 => Function.update z.1 j' z.2 := by
    fun_prop
  have hjoint : Measurable fun z : Submission.BoseGases.X m × E3 =>
      |F (Function.update z.1 j' z.2)| :=
    continuous_abs.measurable.comp (hFm.comp hupd)
  exact AEStronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
    hjoint.aestronglyMeasurable

/-- The slice support of `pairF` is contained in `boxL ℓ`. -/
private theorem tsupport_pairF_slice {m : ℕ} {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut}
    {μ : ℝ} (i j : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ) (j' : Fin m)
    (r : Submission.BoseGases.X m) :
    tsupport (fun w : E3 => pairF v fc μ i j Θ j' (r, w))
      ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
  refine subset_trans ?_ (tsupport_chiLam_subset_boxL (ellH_pos v μ))
  refine closure_mono ?_
  intro w hw
  rw [Function.mem_support] at hw ⊢
  intro h0
  exact hw (by simp only [pairF, h0, zero_mul])

/-- The slice support of `pairG` is contained in `boxL ℓ`. -/
private theorem tsupport_pairG_slice {m : ℕ} {v : E3 → ℝ} {μ : ℝ} (i : Fin (m + 1))
    (Θ : Submission.BoseGases.X (m + 1) → ℝ) (r : Submission.BoseGases.X m) :
    tsupport (fun y : E3 => pairG v μ i Θ (r, y))
      ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
  refine subset_trans ?_ (tsupport_chiLam_subset_boxL (ellH_pos v μ))
  refine closure_mono ?_
  intro w hw
  rw [Function.mem_support] at hw ⊢
  intro h0
  exact hw (by simp only [pairG, h0, zero_mul])

/-- **The pointwise bound on the `w`-function of the peeled pairing**, in the sharp
`L¹`-form: `‖pairF (r,·)‖ ≤ Cimg · ∫_u |Ψ (r[j' ↦ u])|`. -/
private theorem pairF_slice_le {m : ℕ} {v : E3 → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} (hℓ : 0 < ellH v μ)
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB0 : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B) (i : Fin (m + 1)) (j' : Fin m) {Cimg : ℝ}
    (himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖ ≤ Cimg)
    (r : Submission.BoseGases.X m) (w : E3) :
    ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖
      ≤ Cimg * ∫ u in Submission.BoseGases.acube (ellH v μ),
          |Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
            (Submission.BoseGases.aP (ellH v μ) i Θ)
            (Submission.BoseGases.kcInsN m i (0, Function.update r j' u))| := by
  have hinner := chCimg_inner_le (m := m) (v := v) (fc := fc) (μ := μ) hℓ (Θ := Θ) hΘm hB0 hΘb
    i (i.succAbove j') (Cimg := Cimg) himg w (Submission.BoseGases.kcInsN m i (0, r))
  have hI : (∫ u in Submission.BoseGases.acube (ellH v μ),
        imgSumC fc (chKappa v μ) (ellH v μ) u w
          * ((Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
              (Submission.BoseGases.aP (ellH v μ) i Θ)
              (Submission.BoseGases.kcInsN m i (0, Function.update r j' u)) : ℝ) : ℂ))
      = ∫ u in Submission.BoseGases.acube (ellH v μ),
          imgSumC fc (chKappa v μ) (ellH v μ) u w
            * ((Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
                (Submission.BoseGases.aP (ellH v μ) i Θ)
                (Function.update (Submission.BoseGases.kcInsN m i (0, r)) (i.succAbove j') u)
                : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only []
    have h1 : Submission.BoseGases.kcInsN m i (0, Function.update r j' u)
        = Function.update (Submission.BoseGases.kcInsN m i (0, r)) (i.succAbove j') u :=
      (update_kcInsN_succAbove i j' 0 r u).symm
    rw [h1]
  have hI2 : (∫ u in Submission.BoseGases.acube (ellH v μ),
        |Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
          (Submission.BoseGases.aP (ellH v μ) i Θ)
          (Submission.BoseGases.kcInsN m i (0, Function.update r j' u))|)
      = ∫ u in Submission.BoseGases.acube (ellH v μ),
          |Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
            (Submission.BoseGases.aP (ellH v μ) i Θ)
            (Function.update (Submission.BoseGases.kcInsN m i (0, r)) (i.succAbove j') u)| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only []
    have h1 : Submission.BoseGases.kcInsN m i (0, Function.update r j' u)
        = Function.update (Submission.BoseGases.kcInsN m i (0, r)) (i.succAbove j') u :=
      (update_kcInsN_succAbove i j' 0 r u).symm
    rw [h1]
  rw [pairF, hI, hI2]
  exact hinner

/-- The pointwise bound on the `w`-function of the peeled pairing (uniform form). -/
private theorem norm_pairF_slice {m : ℕ} {v : E3 → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} (hℓ : 0 < ellH v μ) {N' : ℕ}
    (hκ : 0 < chKappa v μ) (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB0 : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B) (i : Fin (m + 1)) (j' : Fin m) {Cimg : ℝ} (hCimg0 : 0 ≤ Cimg)
    (himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖ ≤ Cimg)
    (r : Submission.BoseGases.X m) (w : E3) :
    ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ≤ Cimg * (2 * B * (ellH v μ) ^ 3) := by
  refine le_trans (pairF_slice_le hℓ hΘm hB0 hΘb i j' himg r w) ?_
  refine mul_le_mul_of_nonneg_left ?_ hCimg0
  haveI : IsFiniteMeasure
      ((volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ))) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume _ hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  have hQb : ∀ u : E3, |Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
      (Submission.BoseGases.aP (ellH v μ) i Θ)
      (Submission.BoseGases.kcInsN m i (0, Function.update r j' u))| ≤ 2 * B :=
    fun u => aQ_aP_abs_le_bounded hℓ hB0 hΘb i (i.succAbove j') _
  have hvol : (volume : Measure E3).real (Submission.BoseGases.acube (ellH v μ))
      = (ellH v μ) ^ 3 := by
    rw [Measure.real_def]
    have h := Submission.BoseGases.real_volume_acube (ellH v μ) hℓ.le
    rw [Measure.real_def, Measure.restrict_apply_univ] at h
    exact h
  have hconst : (∫ _u in Submission.BoseGases.acube (ellH v μ), (2 * B))
      = (2 * B) * (ellH v μ) ^ 3 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol, mul_comm]
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _)
    (integrable_const (2 * B)) (Filter.Eventually.of_forall fun u => hQb u)) ?_
  rw [hconst]

/-- `MemLp` of the `w`-slice of `pairF`. -/
private theorem memLp_pairF_slice {m : ℕ} {v : E3 → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} (hℓ : 0 < ellH v μ) {N' : ℕ}
    (hκ : 0 < chKappa v μ) (hN' : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ (N' : ℝ))
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB0 : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B) (i : Fin (m + 1)) (j' : Fin m) {Cimg : ℝ} (hCimg0 : 0 ≤ Cimg)
    (himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖ ≤ Cimg)
    (r : Submission.BoseGases.X m) :
    MemLp (fun w : E3 => pairF v fc μ i (i.succAbove j') Θ j' (r, w)) 2
      (volume : Measure E3) :=
  HasCompactSupport.memLp_of_bound
    ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (ellH v μ)).of_isClosed_subset
      (isClosed_tsupport _)
      (tsupport_pairF_slice (v := v) (fc := fc) (μ := μ) i (i.succAbove j') Θ j' r))
    (aestronglyMeasurable_pairF_slice hℓ hκ hN' hΘm i (i.succAbove j') j' r)
    (Cimg * (2 * B * (ellH v μ) ^ 3))
    (Filter.Eventually.of_forall fun w =>
      norm_pairF_slice hℓ hκ hN' hΘm hB0 hΘb i j' hCimg0 himg r w)

/-- `MemLp` of the `y`-slice of `pairG`. -/
private theorem memLp_pairG_slice {m : ℕ} {v : E3 → ℝ} {μ : ℝ} (hℓ : 0 < ellH v μ)
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB0 : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B) (i : Fin (m + 1)) (r : Submission.BoseGases.X m) :
    MemLp (fun y : E3 => pairG v μ i Θ (r, y)) 2 (volume : Measure E3) :=
  HasCompactSupport.memLp_of_bound
    ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (ellH v μ)).of_isClosed_subset
      (isClosed_tsupport _)
      (tsupport_pairG_slice (v := v) (μ := μ) i Θ r))
    (aestronglyMeasurable_pairG_slice hΘm i r) (chiBound * B)
    (Filter.Eventually.of_forall fun y => by
      simp only [pairG, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul ?_ (hΘb _) (abs_nonneg _) chiBound_nonneg
      rw [abs_of_nonneg (Work.BoseB4.BoxData.chiLam_nonneg Work.BoseK15.corpusBox (ellH v μ) y)]
      exact chiLam_le_chiBound (ellH v μ) y)
/-- `a·√b ≤ (a²+b)/2` for `b ≥ 0`. -/
private theorem mul_sqrt_le {a b : ℝ} (hb : 0 ≤ b) :
    a * Real.sqrt b ≤ (a ^ 2 + b) / 2 := by
  nlinarith [sq_nonneg (a - Real.sqrt b), Real.sq_sqrt hb]

/-- Real measure of the centred cube. -/
private theorem real_volume_acube_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure E3).real (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
  rw [Measure.real_def]
  have h := Submission.BoseGases.real_volume_acube ℓ hℓ.le
  rw [Measure.real_def, Measure.restrict_apply_univ] at h
  exact h

/-- Integral of a constant over the centred cube. -/
private theorem setIntegral_const_acube {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) :
    (∫ _y in Submission.BoseGases.acube ℓ, c) = c * ℓ ^ 3 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, real_volume_acube_pos hℓ, mul_comm]

/-- Integral of a constant over `boxL ℓ`. -/
private theorem setIntegral_const_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) :
    (∫ _y in Work.BoseK15.corpusBox.boxL ℓ, c) = c * ℓ ^ 3 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, Measure.real_def,
    Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
    ENNReal.toReal_ofReal (by positivity), mul_comm]

/-- The pointwise bound `‖pairG (r,y)‖² ≤ (sup χ)²·Θ(ins(y,r))²`. -/
private theorem normSq_pairG_le {m : ℕ} {v : E3 → ℝ} {μ : ℝ} (hℓ : 0 < ellH v μ)
    (i : Fin (m + 1)) (Θ : Submission.BoseGases.X (m + 1) → ℝ) (r : Submission.BoseGases.X m)
    (y : E3) :
    ‖pairG v μ i Θ (r, y)‖ ^ 2 ≤ chiBound ^ 2
      * (Θ (Submission.BoseGases.kcInsN m i (y, r))) ^ 2 := by
  have hχ0 : 0 ≤ Work.BoseK15.corpusBox.chiLam (ellH v μ) y :=
    Work.BoseB4.BoxData.chiLam_nonneg Work.BoseK15.corpusBox (ellH v μ) y
  have hχb : Work.BoseK15.corpusBox.chiLam (ellH v μ) y ≤ chiBound := chiLam_le_chiBound _ y
  simp only [pairG, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow]
  simp only [sq_abs]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hχ0 hχb 2) (sq_nonneg _)

/-- The `i`-slot peel collapse of the box integral. -/
private theorem abox_peel_collapse {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (m + 1))
    {F : Submission.BoseGases.X (m + 1) → ℝ}
    (hindep : ∀ (x : Submission.BoseGases.X (m + 1)) (z : E3),
      F (Function.update x i z) = F x)
    (hF : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox (m + 1) ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ, F x)
      = ℓ ^ 3 * ∫ r in Submission.BoseGases.abox m ℓ,
          F (Submission.BoseGases.kcInsN m i (0, r)) := by
  rw [Submission.BoseGases.abox_integral_peel (n := m) (ℓ := ℓ) i F hF]
  have hconst : ∀ r : Submission.BoseGases.X m,
      (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN m i (y, r)))
        = ℓ ^ 3 * F (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro r
    have hpt : ∀ y : E3, F (Submission.BoseGases.kcInsN m i (y, r))
        = F (Submission.BoseGases.kcInsN m i (0, r)) := by
      intro y
      rw [Submission.BoseGases.kcInsN_update_zero i y r]
      exact hindep _ y
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      setIntegral_const_acube hℓ]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hconst),
    MeasureTheory.integral_const_mul]

theorem chCimg_key (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ {μ : ℝ} {N n : ℕ}, 0 < μ → 1 ≤ N →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
      2 * R ≤ Work.BoseBoxFock.ellH v μ →
      ∀ (i j : Fin n), i ≠ j →
      ∀ (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        ‖Work.BoseBoxFock.PCFU.chCimg v h fc fu μ N i j
            (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ CE * (Work.BoseBoxFock.ellH v μ) ^ 3
              * (∫ x : EuclideanSpace ℝ (Fin 3),
                  |Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x|)
              * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d) ^ 110
              * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := chiLam_imageSum_le fc 55
  refine ⟨C₁ * chiBound, mul_nonneg hC₁0 chiBound_nonneg, ?_⟩
  intro μ N n hμ hN hcR h2R i j hij Φ
  rcases n with _ | m
  · exact i.elim0
  -- ## the parameters
  have hsidepos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hside : Work.BoseBox.sideAt μ (BoseGases.a v) = ellH v μ := by
    rw [ellH, if_pos hsidepos]
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
    show 0 < Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 6
    exact Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3))
  have hκeq : chKappa v μ
      = 1 / ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ) := by
    rw [chKappa, ← hside, inv_eq_one_div]
  have hκ : 0 < chKappa v μ := by
    rw [hκeq]; exact one_div_pos.mpr (mul_pos (pow_pos hd 2) hℓ)
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * chKappa v μ * ellH v μ / (2 * Real.pi))
  have hN'm : 2 * chKappa v μ * ellH v μ / (2 * Real.pi) ≤ ((max N N₀ : ℕ) : ℝ) :=
    le_trans hN₀ (by exact_mod_cast Nat.le_max_right N N₀)
  have himg : ∀ (w u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * imgSumC fc (chKappa v μ) (ellH v μ) u w‖
      ≤ C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3 := by
    intro w u hu
    have hh := hC₁ hd hℓ hκeq w u hu
    simpa only [show (2 : ℕ) * 55 = 110 by norm_num] using hh
  -- ## rename the second slot
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (show j ≠ i from fun hji => hij hji.symm)
  have hij' : i ≠ i.succAbove j' := fun hh => hij (hh.trans hj')
  rw [← hj']
  -- ## the state
  have hΦc : Continuous ((Φ : Work.BoseKinLoc.BoxState (m + 1)
      (Work.BoseBox.sideAt μ (BoseGases.a v))) : Submission.BoseGases.X (m + 1) → ℝ) :=
    Φ.contDiff.continuous
  set Θ : Submission.BoseGases.X (m + 1) → ℝ :=
    Work.BoseBoxFock.boxRestrictR (ellH v μ)
      ((Φ : Submission.BoseGases.X (m + 1) → ℝ)) with hΘdef
  have hΘm : Measurable Θ := by
    rw [hΘdef]
    unfold Work.BoseBoxFock.boxRestrictR
    exact hΦc.measurable.mul (Measurable.indicator measurable_const
      (Submission.BoseGases.abox_measurable (m + 1) (ellH v μ)))
  have hΘsupp : ∀ x, x ∉ Submission.BoseGases.abox (m + 1) (ellH v μ) → Θ x = 0 := by
    intro x hx
    rw [hΘdef]
    unfold Work.BoseBoxFock.boxRestrictR
    rw [Set.indicator_of_notMem hx, mul_zero]
  -- ## a global bound on the state
  obtain ⟨Cφ, hCφ⟩ := (Submission.BoseGases.abox_compact (m + 1) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (m + 1) (ellH v μ))
    (f := ((Φ : Work.BoseKinLoc.BoxState (m + 1)
      (Work.BoseBox.sideAt μ (BoseGases.a v))) : Submission.BoseGases.X (m + 1) → ℝ))
    hΦc.continuousOn
  have hM0 : 0 ≤ max Cφ 0 := le_max_right Cφ 0
  have hΘb : ∀ x, |Θ x| ≤ max Cφ 0 := by
    intro x
    rw [hΘdef]
    unfold Work.BoseBoxFock.boxRestrictR
    by_cases hx : x ∈ Submission.BoseGases.abox (m + 1) (ellH v μ)
    · rw [Set.indicator_of_mem hx, mul_one]
      exact le_trans (by simpa only [Real.norm_eq_abs] using hCφ x hx) (le_max_left Cφ 0)
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact le_max_right Cφ 0
  have hIntA : Integrable (fun x : Submission.BoseGases.X (m + 1) =>
      |Θ x| * ∫ u in Submission.BoseGases.acube (ellH v μ),
        |Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
          (Submission.BoseGases.aP (ellH v μ) i Θ)
          (Function.update x (i.succAbove j') u)|) volume := by
    have hh := (chBimg_state_le (ℓ := ellH v μ) hℓ i (i.succAbove j') hij' hΦc).1
    simpa only [hΘdef] using hh
  have hCimg0 : 0 ≤ C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3 :=
    div_nonneg (mul_nonneg hC₁0 (pow_nonneg hd.le 110)) (by positivity)
  -- ## the peeling identity
  have hpeel := chCimg_eq_peel (m := m) (v := v) (h := h) (fc := fc) (fu := fu) (μ := μ)
    (N := N) (N' := max N N₀) (Θ := Θ) hℓ hκ hN'm hΘm hM0 hΘb i (i.succAbove j')
    hCimg0 himg hΘsupp hIntA
  rw [hpeel]
  -- ## abbreviations
  set A : Submission.BoseGases.X m → ℝ := fun r => ∫ u in Submission.BoseGases.acube (ellH v μ),
      |Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
        (Submission.BoseGases.aP (ellH v μ) i Θ)
        (Submission.BoseGases.kcInsN m i (0, Function.update r j' u))| with hAdef
  set T : Submission.BoseGases.X m → ℝ := fun r => ∫ y in Submission.BoseGases.acube (ellH v μ),
      (Θ (Submission.BoseGases.kcInsN m i (y, r))) ^ 2 with hTdef
  set F₀ : Submission.BoseGases.X m → ℝ := fun x =>
      Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
        (Submission.BoseGases.aP (ellH v μ) i Θ) (Submission.BoseGases.kcInsN m i (0, x)) with hF₀def
  set Ψ : Submission.BoseGases.X (m + 1) → ℝ :=
      Submission.BoseGases.aQ (ellH v μ) (i.succAbove j')
        (Submission.BoseGases.aP (ellH v μ) i Θ) with hΨdef
  have hA_eq : ∀ r, A r = ∫ u in Submission.BoseGases.acube (ellH v μ),
      |F₀ (Function.update r j' u)| := by
    intro r
    rw [hAdef, hF₀def]
  have hboxMeas : (volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m (ellH v μ)) = Measure.pi
        (fun _ : Fin m => (volume : Measure E3).restrict (Submission.BoseGases.acube (ellH v μ))) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi]
  haveI hfinA : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m (ellH v μ))) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume m (ellH v μ) hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  haveI hfinC : IsFiniteMeasure ((volume : Measure E3).restrict
      (Submission.BoseGases.acube (ellH v μ))) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume (ellH v μ) hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  -- ## the `L¹`-bound on the pair `(pairF, pairG)` for every `r`
  have hpair : ∀ r : Submission.BoseGases.X m,
      ‖(∫ y in Submission.BoseGases.acube (ellH v μ),
          pairG v μ i Θ (r, y) * (∫ w : E3,
            KfrU v h μ fu N (y + w) * pairF v fc μ i (i.succAbove j') Θ j' (r, w)))‖
        ≤ (∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
            * (ellH v μ) ^ 3
            * Real.sqrt (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
            * Real.sqrt (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2) := by
    intro r
    set K : E3 → ℂ := fun y => ∫ w : E3,
      KfrU v h μ fu N (y + w) * pairF v fc μ i (i.succAbove j') Θ j' (r, w) with hKdef
    have hy0 : ∀ y ∉ Submission.BoseGases.acube (ellH v μ), pairG v μ i Θ (r, y) * K y = 0 := by
      intro y hy
      rw [hKdef, pairG_slice_zero (v := v) (μ := μ) hℓ i Θ r hy, zero_mul]
    have hyid : (∫ y in Submission.BoseGases.acube (ellH v μ), pairG v μ i Θ (r, y) * K y)
        = ∫ y : E3, pairG v μ i Θ (r, y) * K y := by
      rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable (ellH v μ))]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only []
      by_cases hy : y ∈ Submission.BoseGases.acube (ellH v μ)
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, hy0 y hy]
    rw [hyid, hKdef]
    exact KfrU_pairing_eplus (v := v) (h := h) (μ := μ) (fu := fu) (N := N)
      (f := fun w : E3 => pairF v fc μ i (i.succAbove j') Θ j' (r, w))
      (g := fun y : E3 => pairG v μ i Θ (r, y))
      (memLp_pairF_slice hℓ hκ hN'm hΘm hM0 hΘb i j' hCimg0 himg r)
      (memLp_pairG_slice hℓ hΘm hM0 hΘb i r)
      (tsupport_pairF_slice (v := v) (fc := fc) (μ := μ) i (i.succAbove j') Θ j' r)
      (tsupport_pairG_slice (v := v) (μ := μ) i Θ r)
  -- ## the pointwise `L²`-bound on the `pairF`-slice
  have hF₂_le : ∀ r, (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
      ≤ (ellH v μ) ^ 3 * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
          / (ellH v μ) ^ 3) ^ 2 * (A r) ^ 2 := by
    intro r
    have hEq : (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
        = ∫ w in Work.BoseK15.corpusBox.boxL (ellH v μ),
            ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2 := by
      rw [← MeasureTheory.integral_indicator
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox (ellH v μ))]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only []
      by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
      · rw [Set.indicator_of_mem hw]
      · rw [Set.indicator_of_notMem hw]
        have hz : pairF v fc μ i (i.succAbove j') Θ j' (r, w) = 0 := by
          refine pairF_slice_zero (v := v) (fc := fc) (μ := μ) hℓ i (i.succAbove j') Θ j' r ?_
          rwa [Work.BoseBoxFock.boxL_eq_acube hℓ] at hw
        rw [hz, norm_zero]
        ring
    have hvol : (volume : Measure E3).real (Work.BoseK15.corpusBox.boxL (ellH v μ))
        = (ellH v μ) ^ 3 := by
      rw [Measure.real_def, Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
        ENNReal.toReal_ofReal (by positivity)]
    haveI hfinB : IsFiniteMeasure ((volume : Measure E3).restrict
        (Work.BoseK15.corpusBox.boxL (ellH v μ))) :=
      ⟨by rw [Measure.restrict_apply_univ, Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ]
          exact ENNReal.ofReal_lt_top⟩
    have hconst : (∫ _w in Work.BoseK15.corpusBox.boxL (ellH v μ),
          (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3 * A r) ^ 2)
        = (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3 * A r) ^ 2
          * (ellH v μ) ^ 3 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
      ring
    rw [hEq]
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => sq_nonneg _)
      (integrable_const ((C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
        / (ellH v μ) ^ 3 * A r) ^ 2))
      (Filter.Eventually.of_forall fun w => ?_)) ?_
    · simp only []
      exact pow_le_pow_left₀ (norm_nonneg _)
        (pairF_slice_le hℓ hΘm hM0 hΘb i j' himg r w) 2
    · rw [hconst]
      exact le_of_eq (by ring)
  -- ## the pointwise `L²`-bound on the `pairG`-slice
  have hGp_le : ∀ r : Submission.BoseGases.X m,
      (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2) ≤ chiBound ^ 2 * T r := by
    intro r
    have hEq : (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2)
        = ∫ y in Submission.BoseGases.acube (ellH v μ), ‖pairG v μ i Θ (r, y)‖ ^ 2 := by
      rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable (ellH v μ))]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only []
      by_cases hy : y ∈ Submission.BoseGases.acube (ellH v μ)
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy,
          pairG_slice_zero (v := v) (μ := μ) hℓ i Θ r hy, norm_zero]
        ring
    rw [hEq, hTdef, ← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
      (Integrable.const_mul ?_ (chiBound ^ 2)) (Filter.Eventually.of_forall fun y => ?_)
    · exact Integrable.mono' (integrable_const ((max Cφ 0) ^ 2))
        ((Measurable.comp (Measurable.comp hΘm (measurable_kcInsN i))
          (by fun_prop : Measurable fun y : E3 => (y, r))).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          calc Θ (Submission.BoseGases.kcInsN m i (y, r)) ^ 2
              = |Θ (Submission.BoseGases.kcInsN m i (y, r))| ^ 2 := by rw [sq_abs]
            _ ≤ (max Cφ 0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hΘb _) 2)
    · simp only []
      exact normSq_pairG_le hℓ i Θ r y
  -- ## integrability of `T`
  have hTaesm : AEStronglyMeasurable T ((volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m (ellH v μ))) := by
    rw [hTdef]
    exact aesm_theta_ins hΘm i
  have hTnn : ∀ r : Submission.BoseGases.X m, 0 ≤ T r := by
    intro r
    rw [hTdef]
    exact integral_nonneg fun y => sq_nonneg _
  have hTb : ∀ r : Submission.BoseGases.X m, T r ≤ (max Cφ 0) ^ 2 * (ellH v μ) ^ 3 := by
    intro r
    have h1 : (∫ y in Submission.BoseGases.acube (ellH v μ),
        (Θ (Submission.BoseGases.kcInsN m i (y, r))) ^ 2)
        ≤ ∫ _y in Submission.BoseGases.acube (ellH v μ), (max Cφ 0) ^ 2 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
      simp only []
      calc Θ (Submission.BoseGases.kcInsN m i (y, r)) ^ 2
          = |Θ (Submission.BoseGases.kcInsN m i (y, r))| ^ 2 := by rw [sq_abs]
        _ ≤ (max Cφ 0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hΘb _) 2
    rw [hTdef]
    exact le_trans h1 (le_of_eq (setIntegral_const_acube hℓ _))
  have hIntT : Integrable T ((volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m (ellH v μ))) :=
    Integrable.mono' (integrable_const ((max Cφ 0) ^ 2 * (ellH v μ) ^ 3)) hTaesm
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_of_nonneg (hTnn r)]
        exact hTb r)
  -- ## the peel of `Θ²` and its domination by the state
  haveI hfinD : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
      (Submission.BoseGases.abox (m + 1) (ellH v μ))) :=
    ⟨by rw [Measure.restrict_apply_univ,
        Submission.BoseGases.abox_volume (m + 1) (ellH v μ) hℓ.le]
        exact ENNReal.ofReal_lt_top⟩
  have hΘ2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => (Θ x) ^ 2)
      (Submission.BoseGases.abox (m + 1) (ellH v μ)) volume := by
    refine IntegrableOn.of_bound ?_ ((hΘm.pow_const 2).aestronglyMeasurable) ((max Cφ 0) ^ 2) ?_
    · rw [Submission.BoseGases.abox_volume (m + 1) (ellH v μ) hℓ.le]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable (m + 1) (ellH v μ))] with x _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc Θ x ^ 2 = |Θ x| ^ 2 := by rw [sq_abs]
        _ ≤ (max Cφ 0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hΘb x) 2
  have hTpeel : (∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Θ x) ^ 2)
      = ∫ r in Submission.BoseGases.abox m (ellH v μ), T r := by
    rw [hTdef]
    exact Submission.BoseGases.abox_integral_peel (n := m) (ℓ := ellH v μ) i
      (fun x => (Θ x) ^ 2) hΘ2int
  have hΦ2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) =>
      ((Φ : Submission.BoseGases.X (m + 1) → ℝ) x) ^ 2)
      (Submission.BoseGases.abox (m + 1) (ellH v μ)) volume := by
    refine IntegrableOn.of_bound ?_ ((hΦc.measurable.pow_const 2).aestronglyMeasurable)
      (Cφ ^ 2) ?_
    · rw [Submission.BoseGases.abox_volume (m + 1) (ellH v μ) hℓ.le]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable (m + 1) (ellH v μ))] with x hx
      have hb : |((Φ : Submission.BoseGases.X (m + 1) → ℝ) x)| ≤ Cφ := by
        simpa only [Real.norm_eq_abs] using hCφ x hx
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc ((Φ : Submission.BoseGases.X (m + 1) → ℝ) x) ^ 2
          = |((Φ : Submission.BoseGases.X (m + 1) → ℝ) x)| ^ 2 := by rw [sq_abs]
        _ ≤ Cφ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hnormB : Work.BoseBoxFix.normB v μ (m + 1) Φ
      = ∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ),
          ((Φ : Submission.BoseGases.X (m + 1) → ℝ) x) ^ 2 := by
    simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hside]
  have hΘ_le_Φ : (∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Θ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ),
          ((Φ : Submission.BoseGases.X (m + 1) → ℝ) x) ^ 2 := by
    have hpoint : ∀ x : Submission.BoseGases.X (m + 1),
        Θ x ^ 2 ≤ ((Φ : Submission.BoseGases.X (m + 1) → ℝ) x) ^ 2 := by
      intro x
      by_cases hx : x ∈ Submission.BoseGases.abox (m + 1) (ellH v μ)
      · have hx' : Θ x = (Φ : Submission.BoseGases.X (m + 1) → ℝ) x := by
          rw [hΘdef]
          unfold Work.BoseBoxFock.boxRestrictR
          rw [Set.indicator_of_mem hx, mul_one]
        rw [hx']
      · rw [hΘsupp x hx]
        nlinarith [sq_nonneg ((Φ : Submission.BoseGases.X (m + 1) → ℝ) x)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hΦ2int
      (Filter.Eventually.of_forall hpoint)
  have hΘ_le_normB : (∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Θ x) ^ 2)
      ≤ Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    rw [hnormB]
    exact hΘ_le_Φ
  have hT_le : (∫ r in Submission.BoseGases.abox m (ellH v μ), T r)
      ≤ Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    rw [← hTpeel]
    exact hΘ_le_normB
  -- ## the `A²`-bound
  have hΨm : Measurable Ψ := by
    rw [hΨdef]
    exact Work.BoseBoxFock.Weak.aQ_measurable (i.succAbove j')
      (Work.BoseBoxFock.Weak.aP_measurable i hΘm)
  have hΨb : ∀ x : Submission.BoseGases.X (m + 1), |Ψ x| ≤ 2 * max Cφ 0 := by
    intro x
    rw [hΨdef]
    exact aQ_aP_abs_le_bounded hℓ hM0 hΘb i (i.succAbove j') x
  have hF₀m : Measurable F₀ := by
    rw [hF₀def]
    exact Measurable.comp hΨm (Measurable.comp (measurable_kcInsN i)
      (by fun_prop : Measurable fun x : Submission.BoseGases.X m => ((0 : E3), x)))
  have hF₀b : ∀ x : Submission.BoseGases.X m, |F₀ x| ≤ 2 * max Cφ 0 := by
    intro x
    rw [hF₀def]
    exact hΨb _
  have h2M0 : (0 : ℝ) ≤ 2 * max Cφ 0 := by positivity
  have hF₀int : IntegrableOn (fun x : Submission.BoseGases.X m => (F₀ x) ^ 2)
      (Submission.BoseGases.abox m (ellH v μ)) volume := by
    refine IntegrableOn.of_bound ?_ ((hF₀m.pow_const 2).aestronglyMeasurable)
      ((2 * max Cφ 0) ^ 2) ?_
    · rw [Submission.BoseGases.abox_volume m (ellH v μ) hℓ.le]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable m (ellH v μ))] with x _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc F₀ x ^ 2 = |F₀ x| ^ 2 := by rw [sq_abs]
        _ ≤ (2 * max Cφ 0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hF₀b x) 2
  have hΨ2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => (Ψ x) ^ 2)
      (Submission.BoseGases.abox (m + 1) (ellH v μ)) volume := by
    refine IntegrableOn.of_bound ?_ ((hΨm.pow_const 2).aestronglyMeasurable)
      ((2 * max Cφ 0) ^ 2) ?_
    · rw [Submission.BoseGases.abox_volume (m + 1) (ellH v μ) hℓ.le]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable (m + 1) (ellH v μ))] with x _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc Ψ x ^ 2 = |Ψ x| ^ 2 := by rw [sq_abs]
        _ ≤ (2 * max Cφ 0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hΨb x) 2
  have hindepΨ : ∀ (x : Submission.BoseGases.X (m + 1)) (z : E3),
      (Ψ (Function.update x i z)) ^ 2 = (Ψ x) ^ 2 := by
    intro x z
    rw [hΨdef]
    rw [aQ_aP_update_invariant (i := i) (j := i.succAbove j') hij' x z]
  have hcoll : (∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Ψ x) ^ 2)
      = (ellH v μ) ^ 3 * ∫ r in Submission.BoseGases.abox m (ellH v μ), (F₀ r) ^ 2 := by
    rw [abox_peel_collapse hℓ i hindepΨ hΨ2int]
  have hΨ_le_Θ : (∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Ψ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Θ x) ^ 2 := by
    have hmem : MemLp Θ 2 ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) (ellH v μ))) :=
      MemLp.of_bound hΘm.aestronglyMeasurable (max Cφ 0)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hΘb x)
    have h := aQ_aP_sq_integral_le (n := m + 1) (ℓ := ellH v μ) hℓ
      (i := i) (j := i.succAbove j') hij' hmem
    rw [hΨdef]
    exact h
  have hA2_le : (∫ r in Submission.BoseGases.abox m (ellH v μ), (A r) ^ 2)
      ≤ (ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    have h1 : (∫ r in Submission.BoseGases.abox m (ellH v μ), (A r) ^ 2)
        = ∫ r in Submission.BoseGases.abox m (ellH v μ),
            (∫ u in Submission.BoseGases.acube (ellH v μ), |F₀ (Function.update r j' u)|) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      simp only []
      rw [hA_eq r]
    rw [h1]
    calc (∫ r in Submission.BoseGases.abox m (ellH v μ),
            (∫ u in Submission.BoseGases.acube (ellH v μ), |F₀ (Function.update r j' u)|) ^ 2)
        ≤ (ellH v μ) ^ 3 * ((ellH v μ) ^ 3
            * ∫ r in Submission.BoseGases.abox m (ellH v μ), (F₀ r) ^ 2) :=
          fibre_update_sq_le hℓ j' hF₀m h2M0 hF₀b
      _ = (ellH v μ) ^ 3
            * (∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Ψ x) ^ 2) := by
          rw [hcoll]
      _ ≤ (ellH v μ) ^ 3 * (∫ x in Submission.BoseGases.abox (m + 1) (ellH v μ), (Θ x) ^ 2) :=
          mul_le_mul_of_nonneg_left hΨ_le_Θ (by positivity)
      _ ≤ (ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ :=
          mul_le_mul_of_nonneg_left hΘ_le_normB (by positivity)
  -- ## integrability of the profiles
  have hAaesm : AEStronglyMeasurable A ((volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m (ellH v μ))) := by
    refine (aesm_fibre_abs hF₀m j').congr (Filter.Eventually.of_forall fun r => ?_)
    rw [hA_eq r]
  have hAnn : ∀ r : Submission.BoseGases.X m, 0 ≤ A r := by
    intro r
    rw [hA_eq r]
    exact integral_nonneg fun u => abs_nonneg _
  have hIntA2 : Integrable (fun r : Submission.BoseGases.X m => (A r) ^ 2)
      ((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m (ellH v μ))) := by
    refine Integrable.mono' (integrable_const ((2 * max Cφ 0 * (ellH v μ) ^ 3) ^ 2))
      (hAaesm.pow 2) (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (hAnn r) ?_ 2
    rw [hA_eq r]
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _)
      (integrable_const (2 * max Cφ 0)) (Filter.Eventually.of_forall fun u => hF₀b _)) ?_
    exact le_of_eq (setIntegral_const_acube hℓ _)
  have hIntAT : Integrable (fun r : Submission.BoseGases.X m => A r * Real.sqrt (T r))
      ((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m (ellH v μ))) := by
    refine Integrable.mono' ((hIntA2.add hIntT).div_const 2)
      (hAaesm.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hTaesm))
      (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hAnn r) (Real.sqrt_nonneg _))]
    exact mul_sqrt_le (hTnn r)
  -- ## the Hölder step
  have hMemA : MemLp A (ENNReal.ofReal 2) ((volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m (ellH v μ))) := by
    simpa using (memLp_two_iff_integrable_sq hAaesm).mpr hIntA2
  have hMemT : MemLp (fun r : Submission.BoseGases.X m => Real.sqrt (T r)) (ENNReal.ofReal 2)
      ((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m (ellH v μ))) := by
    simpa using (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hTaesm)).mpr
        (hIntT.congr (Filter.Eventually.of_forall fun r => (Real.sq_sqrt (hTnn r)).symm))
  have hCS : (∫ r in Submission.BoseGases.abox m (ellH v μ), A r * Real.sqrt (T r))
      ≤ Real.sqrt (∫ r in Submission.BoseGases.abox m (ellH v μ), (A r) ^ 2)
        * Real.sqrt (∫ r in Submission.BoseGases.abox m (ellH v μ), T r) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m (ellH v μ)))
      (p := 2) (q := 2) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun r => hAnn r)
      (Filter.Eventually.of_forall fun r => Real.sqrt_nonneg _) hMemA hMemT
    have hIdA : (∫ r in Submission.BoseGases.abox m (ellH v μ), A r ^ (2 : ℝ))
        = ∫ r in Submission.BoseGases.abox m (ellH v μ), (A r) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      simp only []
      rw [Real.rpow_two]
    have hIdT : (∫ r in Submission.BoseGases.abox m (ellH v μ),
          (Real.sqrt (T r)) ^ (2 : ℝ))
        = ∫ r in Submission.BoseGases.abox m (ellH v μ), T r := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      simp only []
      rw [Real.rpow_two, Real.sq_sqrt (hTnn r)]
    rw [hIdA, hIdT] at h
    rw [← Real.sqrt_eq_rpow (∫ r in Submission.BoseGases.abox m (ellH v μ), (A r) ^ 2),
      ← Real.sqrt_eq_rpow (∫ r in Submission.BoseGases.abox m (ellH v μ), T r)] at h
    exact h
  -- ## the F₂-integral
  have hF₂int : (∫ r in Submission.BoseGases.abox m (ellH v μ),
        ∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
      ≤ (ellH v μ) ^ 3 * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
          / (ellH v μ) ^ 3) ^ 2 * ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ) := by
    refine le_trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun r => integral_nonneg fun w => sq_nonneg _)
      (Integrable.const_mul hIntA2 ((ellH v μ) ^ 3
        * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2))
      (Filter.Eventually.of_forall fun r => hF₂_le r)) ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hA2_le (by positivity)
  have hG₂int : (∫ r in Submission.BoseGases.abox m (ellH v μ),
        ∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2)
      ≤ chiBound ^ 2 * Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    refine le_trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun r => integral_nonneg fun y => sq_nonneg _)
      (hIntT.const_mul (chiBound ^ 2)) (Filter.Eventually.of_forall fun r => hGp_le r)) ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hT_le (by positivity)
  -- ## the peeled integrand is the pairing
  have hins : ∀ r : Submission.BoseGases.X m,
      (∫ y in Submission.BoseGases.acube (ellH v μ),
          chCimgInt v h fc fu μ N i (i.succAbove j') Θ
            (Submission.BoseGases.kcInsN m i (y, r)))
        = ∫ y in Submission.BoseGases.acube (ellH v μ),
            pairG v μ i Θ (r, y) * (∫ w : E3,
              KfrU v h μ fu N (y + w) * pairF v fc μ i (i.succAbove j') Θ j' (r, w)) := by
    intro r
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact chCimgInt_ins_eq (v := v) (h := h) (fc := fc) (fu := fu) (μ := μ) (N := N)
      (Θ := Θ) i j' r y
  rw [show (∫ r in Submission.BoseGases.abox m (ellH v μ),
        ∫ y in Submission.BoseGases.acube (ellH v μ),
          chCimgInt v h fc fu μ N i (i.succAbove j') Θ
            (Submission.BoseGases.kcInsN m i (y, r)))
      = ∫ r in Submission.BoseGases.abox m (ellH v μ),
        ∫ y in Submission.BoseGases.acube (ellH v μ),
          pairG v μ i Θ (r, y) * (∫ w : E3,
            KfrU v h μ fu N (y + w) * pairF v fc μ i (i.succAbove j') Θ j' (r, w)) from by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    exact hins r]
  -- ## the pointwise bounds
  have hW0 : 0 ≤ ∫ x : E3,
      |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x| :=
    integral_nonneg fun x => abs_nonneg _
  have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    rw [hnormB]
    exact integral_nonneg fun x => sq_nonneg _
  have hK0 : 0 ≤ Real.sqrt ((ellH v μ) ^ 3
      * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2) :=
    Real.sqrt_nonneg _
  have hpointF : ∀ r : Submission.BoseGases.X m,
      Real.sqrt (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
        ≤ Real.sqrt ((ellH v μ) ^ 3
            * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
          * A r := by
    intro r
    refine le_trans (Real.sqrt_le_sqrt (hF₂_le r)) ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (hAnn r)]
  have hpointG : ∀ r : Submission.BoseGases.X m,
      Real.sqrt (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2) ≤ chiBound * Real.sqrt (T r) := by
    intro r
    refine le_trans (Real.sqrt_le_sqrt (hGp_le r)) ?_
    rw [Real.sqrt_mul (sq_nonneg chiBound), Real.sqrt_sq chiBound_nonneg]
  have hpoint : ∀ r : Submission.BoseGases.X m,
      (∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
          * (ellH v μ) ^ 3
          * Real.sqrt (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2)
        ≤ ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
            * (ellH v μ) ^ 3
            * Real.sqrt ((ellH v μ) ^ 3
              * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
                / (ellH v μ) ^ 3) ^ 2)
            * chiBound) * (A r * Real.sqrt (T r)) := by
    intro r
    have hstep : Real.sqrt (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2)
        ≤ (Real.sqrt ((ellH v μ) ^ 3
              * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
                / (ellH v μ) ^ 3) ^ 2) * A r)
          * (chiBound * Real.sqrt (T r)) :=
      mul_le_mul (hpointF r) (hpointG r) (Real.sqrt_nonneg _) (mul_nonneg hK0 (hAnn r))
    calc (((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
            * (ellH v μ) ^ 3)
          * Real.sqrt (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2))
        * Real.sqrt (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2)
        = ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
            * (ellH v μ) ^ 3)
          * (Real.sqrt (∫ w : E3, ‖pairF v fc μ i (i.succAbove j') Θ j' (r, w)‖ ^ 2)
            * Real.sqrt (∫ y : E3, ‖pairG v μ i Θ (r, y)‖ ^ 2)) := by ring
      _ ≤ ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
            * (ellH v μ) ^ 3)
          * ((Real.sqrt ((ellH v μ) ^ 3
              * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
                / (ellH v μ) ^ 3) ^ 2) * A r)
            * (chiBound * Real.sqrt (T r))) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hW0 (by positivity))
      _ = ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
            * (ellH v μ) ^ 3
            * Real.sqrt ((ellH v μ) ^ 3
              * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
                / (ellH v μ) ^ 3) ^ 2)
            * chiBound) * (A r * Real.sqrt (T r)) := by ring
  -- ## the majorant and its integrability
  have hIntMaj : Integrable (fun r : Submission.BoseGases.X m =>
      ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
          * (ellH v μ) ^ 3
          * Real.sqrt ((ellH v μ) ^ 3
            * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
          * chiBound) * (A r * Real.sqrt (T r)))
      ((volume : Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m (ellH v μ))) :=
    hIntAT.const_mul _
  have hstepA : ‖(∫ r in Submission.BoseGases.abox m (ellH v μ),
        ∫ y in Submission.BoseGases.acube (ellH v μ),
          pairG v μ i Θ (r, y) * (∫ w : E3,
            KfrU v h μ fu N (y + w) * pairF v fc μ i (i.succAbove j') Θ j' (r, w)))‖
      ≤ ∫ r in Submission.BoseGases.abox m (ellH v μ),
          ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
            * (ellH v μ) ^ 3
            * Real.sqrt ((ellH v μ) ^ 3
              * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
            * chiBound) * (A r * Real.sqrt (T r)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => norm_nonneg _) hIntMaj
      (Filter.Eventually.of_forall fun r => le_trans (hpair r) (hpoint r))
  have hstepB : (∫ r in Submission.BoseGases.abox m (ellH v μ),
        ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
          * (ellH v μ) ^ 3
          * Real.sqrt ((ellH v μ) ^ 3
            * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
          * chiBound) * (A r * Real.sqrt (T r)))
      = ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
          * (ellH v μ) ^ 3
          * Real.sqrt ((ellH v μ) ^ 3
            * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
          * chiBound)
        * (∫ r in Submission.BoseGases.abox m (ellH v μ), A r * Real.sqrt (T r)) := by
    rw [MeasureTheory.integral_const_mul]
  have hstepC : ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
        * (ellH v μ) ^ 3
        * Real.sqrt ((ellH v μ) ^ 3
          * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
        * chiBound)
      * (∫ r in Submission.BoseGases.abox m (ellH v μ), A r * Real.sqrt (T r))
      ≤ ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
        * (ellH v μ) ^ 3
        * Real.sqrt ((ellH v μ) ^ 3
          * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
        * chiBound)
      * (Real.sqrt (∫ r in Submission.BoseGases.abox m (ellH v μ), (A r) ^ 2)
        * Real.sqrt (∫ r in Submission.BoseGases.abox m (ellH v μ), T r)) :=
    mul_le_mul_of_nonneg_left hCS
      (mul_nonneg (mul_nonneg (mul_nonneg hW0 (by positivity)) hK0) chiBound_nonneg)
  have hstepD : ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
        * (ellH v μ) ^ 3
        * Real.sqrt ((ellH v μ) ^ 3
          * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
        * chiBound)
      * (Real.sqrt (∫ r in Submission.BoseGases.abox m (ellH v μ), (A r) ^ 2)
        * Real.sqrt (∫ r in Submission.BoseGases.abox m (ellH v μ), T r))
      ≤ ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
        * (ellH v μ) ^ 3
        * Real.sqrt ((ellH v μ) ^ 3
          * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
        * chiBound)
      * (Real.sqrt ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ)
        * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ)) := by
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (mul_nonneg (mul_nonneg hW0 (by positivity)) hK0) chiBound_nonneg)
    exact mul_le_mul (Real.sqrt_le_sqrt hA2_le) (Real.sqrt_le_sqrt hT_le)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## the final arithmetic
  have hCx3 : (ellH v μ) ^ 3
      * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3)
      = C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 := by
    have h3 : (ellH v μ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    field_simp
  have hKLN : Real.sqrt ((ellH v μ) ^ 3
        * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
      * (Real.sqrt ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ)
        * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ))
      = C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
        * Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    have hL0 : 0 ≤ Real.sqrt ((ellH v μ) ^ 3
          * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
        * (Real.sqrt ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ)
          * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ)) :=
      mul_nonneg hK0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hR0 : 0 ≤ C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
        * Work.BoseBoxFix.normB v μ (m + 1) Φ :=
      mul_nonneg (mul_nonneg hC₁0 (pow_nonneg hd.le 110)) hN0
    have hs : (Real.sqrt ((ellH v μ) ^ 3
          * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
        * (Real.sqrt ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ)
          * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ))) ^ 2
        = (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
            * Work.BoseBoxFix.normB v μ (m + 1) Φ) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (by positivity :
          0 ≤ (ellH v μ) ^ 3
            * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2),
        Real.sq_sqrt (mul_nonneg (by positivity) hN0), Real.sq_sqrt hN0]
      have h3 : (ellH v μ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
      field_simp
    have h := congrArg Real.sqrt hs
    rwa [Real.sqrt_sq hL0, Real.sqrt_sq hR0] at h
  have hstepE : ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
        * (ellH v μ) ^ 3
        * Real.sqrt ((ellH v μ) ^ 3
          * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
        * chiBound)
      * (Real.sqrt ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ)
        * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ))
      ≤ (C₁ * chiBound) * (ellH v μ) ^ 3
          * (∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
          * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110
          * Work.BoseBoxFix.normB v μ (m + 1) Φ := by
    rw [show ((∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
          * (ellH v μ) ^ 3
          * Real.sqrt ((ellH v μ) ^ 3
            * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
          * chiBound)
        * (Real.sqrt ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ)
          * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ))
        = (∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|)
          * (ellH v μ) ^ 3 * chiBound
          * (Real.sqrt ((ellH v μ) ^ 3
              * (C₁ * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 110 / (ellH v μ) ^ 3) ^ 2)
            * (Real.sqrt ((ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ (m + 1) Φ)
              * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ))) from by ring]
    rw [hKLN]
    exact le_of_eq (by ring)
  refine le_trans hstepA (le_trans (le_of_eq hstepB) (le_trans hstepC
    (le_trans hstepD (le_trans hstepE ?_))))
  rw [← hside]


end Work.BoseBoxFock.PCFU

end
