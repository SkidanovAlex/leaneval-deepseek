import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.chBimg_Kchi_sup
import Submission.Work.BoseBoxFock.PCFU.chBimg_arith_aux
import Submission.Work.BoseBoxFock.PCFU.chBimg_state_le
import Submission.Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The exact scaling of the low-momentum kernel**: `Κ_κ(z) = κ³·Κ₁(κz)`
(the symbol `f(‖p‖/κ)` is the `κ`-dilate of `f(‖p‖)`). -/
private lemma lowKer_smul_scale (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (z : E3) :
    lowKer fc κ z = κ ^ 3 * lowKer fc 1 (κ • z) := by
  have hG : ∀ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z)
      = fc.f (‖q‖ / 1) * Real.cos (inner ℝ q (κ • z)) := by
    intro q
    have h1 : ‖κ • q‖ / κ = ‖q‖ / 1 := by
      rw [norm_smul, Real.norm_of_nonneg hκ.le, div_one]
      field_simp
    have h2 : inner ℝ (κ • q) z = inner ℝ q (κ • z) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [h1, h2]
  have hsub := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure E3))
    (f := fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)) κ (hR := hκ.le)
  have hfin : Module.finrank ℝ E3 = 3 := by simp [EuclideanSpace]
  rw [hfin] at hsub
  rw [lowKer_apply, lowKer_apply]
  have hkey : (∫ p : E3, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z))
      = κ ^ 3 * ∫ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z) := by
    rw [hsub, smul_eq_mul]
    have hne : κ ^ 3 ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
    field_simp
  rw [hkey, integral_congr_ae (Filter.Eventually.of_forall hG)]
  ring

/-- `Κ` does not see the cutoff trivialities: the `corpusBox` bump is the corpus bump. -/
private lemma chiLam_eq_chiScale (ℓ : ℝ) :
    Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl

/-- The `κ`-dilate of a centered cube is the centered cube of the rescaled side. -/
private lemma mem_acube_smul {κ ℓ : ℝ} (hκ : 0 < κ) {u : E3}
    (hu : u ∈ Submission.BoseGases.acube ℓ) : κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := by
  rw [Submission.BoseGases.mem_acube_iff] at hu ⊢
  intro m
  have hm := hu m
  have hcomp : (κ • u).ofLp m = κ * u.ofLp m := by
    rw [WithLp.ofLp_smul]
    rfl
  rw [hcomp]
  constructor
  · nlinarith [hm.1, hκ]
  · nlinarith [hm.2, hκ]

/-- The `χ`-weighted lattice-image bound of the low-momentum kernel, with the smallness in the
box ratio `d`: at the tied cutoff `κ = 1/(d²ℓ)` the kernel's rescaled width is frozen and the
proved `chiScale_imageSum_lowKer_le` at `κ = 1` gives `d^{2M}/ℓ³`. -/
private lemma chiScale_lowKer_image_le (fc : Work.BoseBoxFix.LowCut) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ d ℓ : ℝ}, 0 < d → 0 < ℓ → κ = 1 / (d ^ 2 * ℓ) →
      ∀ (b u : E3), u ∈ Submission.BoseGases.acube ℓ →
        ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
          * (∑' e : Fin 3 → ℤ, if e = 0 then 0
              else ((Work.BoseBoxFock.PCFU.lowKer fc κ
                (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
          ≤ C * d ^ (2 * M) / ℓ ^ 3 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le fc (κ := 1) one_pos M
  refine ⟨C₁, hC₁0, ?_⟩
  intro κ d ℓ hd hℓ hκeq b u hu
  have hκpos : 0 < κ := by rw [hκeq]; positivity
  have hκℓpos : 0 < κ * ℓ := mul_pos hκpos hℓ
  -- the `χ`-identity `χ_{κℓ}(κb) = χ_ℓ(b)`
  have hchi : Submission.BoseGases.chiScale (κ * ℓ) (κ • b)
      = Submission.BoseGases.chiScale ℓ b := by
    rw [Submission.BoseGases.chiScale, Submission.BoseGases.chiScale, smul_smul]
    congr 1
    field_simp
  -- the rescaled argument identity
  have harg : ∀ e : Fin 3 → ℤ,
      κ • (u - b + ℓ • Work.BoseBoxFock.latVec e)
        = κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e := by
    intro e
    rw [smul_add, smul_sub, smul_smul]
  -- the termwise scaling identity (complex-valued)
  have hterm : ∀ e : Fin 3 → ℤ,
      ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)
        = ((κ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseBoxFock.PCFU.lowKer fc 1
              (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) := by
    intro e
    have h := lowKer_smul_scale fc hκpos (u - b + ℓ • Work.BoseBoxFock.latVec e)
    rw [h, harg e]
    push_cast
    ring
  -- the two sums
  set S₁ : ℂ := ∑' e : Fin 3 → ℤ, if e = 0 then 0
      else ((Work.BoseBoxFock.PCFU.lowKer fc 1
        (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) with hS₁
  have hS : (∑' e : Fin 3 → ℤ, if e = 0 then 0
        else ((Work.BoseBoxFock.PCFU.lowKer fc κ
          (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)) = ((κ ^ 3 : ℝ) : ℂ) * S₁ := by
    have h1 : (∑' e : Fin 3 → ℤ, if e = 0 then 0
          else ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
        = ∑' e : Fin 3 → ℤ, ((κ ^ 3 : ℝ) : ℂ) * (if e = 0 then 0
            else ((Work.BoseBoxFock.PCFU.lowKer fc 1
              (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)) := by
      refine tsum_congr (fun e => ?_)
      by_cases he : e = 0
      · subst he; simp
      · rw [if_neg he, if_neg he]
        exact hterm e
    rw [h1, tsum_mul_left, hS₁]
  -- the `κ = 1` lemma at `ℓ̃ = κℓ`, `b̃ = κb`, `ũ = κu`
  have hac : κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := mem_acube_smul hκpos hu
  have hb := hC₁ hκℓpos (κ • b) (κ • u) hac
  -- extract `‖χ_{κℓ}(κb)·S₁‖` from the lemma's norm
  have hb' : ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖
      ≤ C₁ / (κ * ℓ) ^ (M + 3) := by
    rw [← hS₁] at hb
    have hnorm : ‖((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ)
          * (((κ * ℓ) ^ 3 : ℝ) : ℂ) * S₁‖
        = (κ * ℓ) ^ 3 * ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖ := by
      rw [← hchi]
      rw [show ((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ)
            * (((κ * ℓ) ^ 3 : ℝ) : ℂ) * S₁
          = (((κ * ℓ) ^ 3 : ℝ) : ℂ)
            * (((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ) * S₁) from by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hnorm] at hb
    have hsplit : C₁ / (κ * ℓ) ^ M = (κ * ℓ) ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3)) := by
      rw [pow_add]
      field_simp
    rw [hsplit] at hb
    exact le_of_mul_le_mul_left hb (by positivity)
  -- the arithmetic identity
  have hκℓ : κ * ℓ = (d ^ 2)⁻¹ := by
    rw [hκeq]; field_simp
  have harith : κ ^ 3 / (κ * ℓ) ^ (M + 3) = d ^ (2 * M) / ℓ ^ 3 := by
    rw [div_eq_div_iff (by positivity) (by positivity), ← mul_pow]
    rw [pow_add, pow_mul, ← mul_assoc, ← mul_pow]
    have hd2κℓ : d ^ 2 * (κ * ℓ) = 1 := by
      rw [hκℓ]; field_simp
    rw [hd2κℓ]
    simp
  -- assembly
  calc ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((Work.BoseBoxFock.PCFU.lowKer fc κ
              (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
      = ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((κ ^ 3 : ℝ) : ℂ) * S₁)‖ := by
        rw [hS]
      _ = κ ^ 3 * ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖ := by
        rw [show ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((κ ^ 3 : ℝ) : ℂ) * S₁)
            = (((κ ^ 3 : ℝ) : ℂ)) * (((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁) from by
              ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ κ ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3)) := by
        refine mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = C₁ * d ^ (2 * M) / ℓ ^ 3 := by
        rw [show κ ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3))
              = C₁ * (κ ^ 3 / (κ * ℓ) ^ (M + 3)) from by ring, harith]
        ring

/-- The `j`-slot fibre `L¹` of the state deviation `Q_jP_iΘ`, as a function of the configuration. -/
private noncomputable def slotFibre {n : ℕ} (ℓ : ℝ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) : ℝ :=
  ∫ u in Submission.BoseGases.acube ℓ,
    |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|

/-- The slot mean of a bounded configuration function is bounded by the same constant. -/
private lemma aP_abs_le_of_bounded {n : ℕ} {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘb : ∀ x, |Θ x| ≤ B) (i : Fin n)
    (x : Submission.BoseGases.X n) :
    |Submission.BoseGases.aP ℓ i Θ x| ≤ B := by
  have hvol : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Bornology.IsBounded.measure_lt_top (Submission.BoseGases.acube_isBounded ℓ hℓ.le)
  have hmeas : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
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

/-- The state deviation of a bounded configuration function is bounded by twice the bound. -/
private lemma aQ_aP_abs_le {n : ℕ} {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘb : ∀ x, |Θ x| ≤ B) (i j : Fin n)
    (x : Submission.BoseGases.X n) :
    |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ 2 * B := by
  have h1 : ∀ y, |Submission.BoseGases.aP ℓ i Θ y| ≤ B :=
    fun y => aP_abs_le_of_bounded hℓ hB hΘb i y
  have h2 : |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ B :=
    aP_abs_le_of_bounded hℓ hB h1 j x
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

/-- **The inner slot-integral bound**: the `χ`-weighted lattice-image factor paired with the
state deviation is bounded by `Cimg` times the fibre `L¹` of the deviation. -/
private lemma chBimg_inner_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B) {fc : Work.BoseBoxFix.LowCut} {κ Cimg : ℝ}
    (himg : ∀ (b u : E3), u ∈ Submission.BoseGases.acube ℓ →
      ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖ ≤ Cimg)
    (x : Submission.BoseGases.X n) :
    |Work.BoseK15.corpusBox.chiLam ℓ (x j)|
      * ‖∫ u in Submission.BoseGases.acube ℓ,
          (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
          * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u) : ℝ) : ℂ)‖
      ≤ Cimg * (∫ u in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|) := by
  have hvol : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Bornology.IsBounded.measure_lt_top (Submission.BoseGases.acube_isBounded ℓ hℓ.le)
  set c : ℂ := ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ) with hc
  set Sf : E3 → ℂ := fun u => ∑' e : Fin 3 → ℤ, if e = 0 then 0
      else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) with hSf
  set Ψf : E3 → ℂ := fun u => ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
      (Function.update x j u) : ℝ) : ℂ) with hΨf
  set ψf : E3 → ℝ := fun u => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
      (Function.update x j u) with hψf
  have hψm : Measurable ψf := by
    have hupd : Measurable (Function.update x j : E3 → Submission.BoseGases.X n) := by
      refine measurable_pi_iff.mpr (fun k => ?_)
      have hfun : (fun u : E3 => Function.update x j u k)
          = (if k = j then (fun u : E3 => u) else (fun _ => x k)) := by
        funext u
        by_cases hk : k = j
        · rw [hk, if_pos rfl]
          exact Function.update_self j u x
        · rw [if_neg hk]
          exact Function.update_of_ne hk u x
      rw [hfun]
      by_cases hk : k = j
      · rw [if_pos hk]; exact measurable_id
      · rw [if_neg hk]; exact measurable_const
    exact (Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)).comp
      hupd
  have hΨm : Measurable Ψf := Complex.measurable_ofReal.comp hψm
  have hψb : ∀ u : E3, ‖ψf u‖ ≤ 2 * B := fun u => by
    rw [hψf, Real.norm_eq_abs]
    exact aQ_aP_abs_le hℓ hB hΘb i j (Function.update x j u)
  have hΨb : ∀ u : E3, ‖Ψf u‖ ≤ 2 * B := fun u => by
    simp only [hΨf, Complex.norm_real, Real.norm_eq_abs]
    exact hψb u
  have hInt : Integrable Ψf ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    IntegrableOn.of_bound hvol hΨm.aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall hΨb)
  have hcn : ‖c‖ = |Work.BoseK15.corpusBox.chiLam ℓ (x j)| := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
  have hpull : (∫ u in Submission.BoseGases.acube ℓ, c * Sf u * Ψf u)
      = c * ∫ u in Submission.BoseGases.acube ℓ, Sf u * Ψf u := by
    rw [show (fun u : E3 => c * Sf u * Ψf u) = (fun u : E3 => c * (Sf u * Ψf u)) from
      funext (fun u => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have hmain : ‖∫ u in Submission.BoseGases.acube ℓ, c * Sf u * Ψf u‖
      ≤ ∫ u in Submission.BoseGases.acube ℓ, Cimg * |ψf u| := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg _)) ?_ ?_
    · refine (hInt.norm.const_mul Cimg).congr ?_
      filter_upwards with u
      simp only [hΨf, hψf, Complex.norm_real, Real.norm_eq_abs]
    · filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)]
        with u hu
      rw [norm_mul]
      have hcS : ‖c * Sf u‖ ≤ Cimg := by
        have h := himg (x j) u hu
        rw [← chiLam_eq_chiScale] at h
        simpa only [hc, hSf] using h
      have hΨu : ‖Ψf u‖ = |ψf u| := by
        simp only [hΨf, hψf, Complex.norm_real, Real.norm_eq_abs]
      rw [hΨu]
      exact mul_le_mul_of_nonneg_right hcS (abs_nonneg _)
  have hlast : (∫ u in Submission.BoseGases.acube ℓ, Cimg * |ψf u|)
      = Cimg * ∫ u in Submission.BoseGases.acube ℓ, |ψf u| :=
    MeasureTheory.integral_const_mul _ _
  calc |Work.BoseK15.corpusBox.chiLam ℓ (x j)|
        * ‖∫ u in Submission.BoseGases.acube ℓ, Sf u * Ψf u‖
      = ‖c * (∫ u in Submission.BoseGases.acube ℓ, Sf u * Ψf u)‖ := by rw [← hcn, norm_mul]
    _ = ‖∫ u in Submission.BoseGases.acube ℓ, c * Sf u * Ψf u‖ := by rw [hpull]
    _ ≤ ∫ u in Submission.BoseGases.acube ℓ, Cimg * |ψf u| := hmain
    _ = Cimg * ∫ u in Submission.BoseGases.acube ℓ, |ψf u| := hlast
    _ = Cimg * (∫ u in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|) := by
        rw [hψf]

/-- **The core per-slot estimate for `chBimg`**: given the `KχfrU` sup bound `Csup`, the
image bound `Cimg`, and the state estimate `∫|Θ|·(fibre L¹) ≤ 8ℓ³∫Θ²`, the slot is bounded by
`8·Csup·Cimg·∫Θ²`. -/
private lemma chBimg_core {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N n : ℕ} {ℓ : ℝ}
    (hℓeq : ℓ = Work.BoseBoxFock.ellH v μ)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B)
    {Csup Cimg : ℝ} (hCsup : ∀ z : E3, ‖KχfrU v h μ fu N z‖ ≤ Csup)
    (himg : ∀ (b u : E3), u ∈ Submission.BoseGases.acube ℓ →
      ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((lowKer fc (chKappa v μ) (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
        ≤ Cimg)
    (i j : Fin n)
    (hstI : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
      |Θ x| * slotFibre ℓ i j Θ x))
    (hstB : (∫ x : Submission.BoseGases.X n, |Θ x| * slotFibre ℓ i j Θ x)
      ≤ 8 * ℓ ^ 3 * ∫ x : Submission.BoseGases.X n, (Θ x) ^ 2) :
    ‖chBimg v h fc fu μ N i j Θ‖
      ≤ 8 * Csup * Cimg * (ℓ ^ 3 * ∫ x : Submission.BoseGases.X n, (Θ x) ^ 2) := by
  subst hℓeq
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hCsup0 : 0 ≤ Csup := le_trans (norm_nonneg _) (hCsup 0)
  have hCimg0 : 0 ≤ Cimg := by
    have h0 : (0 : E3) ∈ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ) := by
      rw [Submission.BoseGases.mem_acube_iff]
      intro m
      have hzero : (0 : E3).ofLp m = (0 : ℝ) := rfl
      rw [hzero, Set.mem_Icc]
      constructor <;> linarith [hℓpos]
    exact le_trans (norm_nonneg _) (himg 0 0 h0)
  -- the pointwise bound of the integrand
  have hpt : ∀ x : Submission.BoseGases.X n,
      ‖(Θ x : ℂ) * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
        * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
            (∑' e : Fin 3 → ℤ, if e = 0 then 0
              else ((lowKer fc (chKappa v μ)
                (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
            * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                (Function.update x j u) : ℝ) : ℂ))‖
      ≤ Csup * Cimg * (|Θ x| * slotFibre (Work.BoseBoxFock.ellH v μ) i j Θ x) := by
    intro x
    have hin := chBimg_inner_le (i := i) (j := j) hℓpos hΘm hB hΘb himg x
    have hK := hCsup (x j)
    have hnorm : ‖(Θ x : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
          * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              (∑' e : Fin 3 → ℤ, if e = 0 then 0
                else ((lowKer fc (chKappa v μ)
                  (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
              * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ))‖
        = |Θ x| * |Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j)|
          * ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)‖
          * ‖∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              (∑' e : Fin 3 → ℤ, if e = 0 then 0
                else ((lowKer fc (chKappa v μ)
                  (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
              * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |Θ x| * |Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j)|
          * ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)‖
          * ‖∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              (∑' e : Fin 3 → ℤ, if e = 0 then 0
                else ((lowKer fc (chKappa v μ)
                  (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
              * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ)‖
        = |Θ x| * ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)‖
          * (|Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j)|
            * ‖∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                (∑' e : Fin 3 → ℤ, if e = 0 then 0
                  else ((lowKer fc (chKappa v μ)
                    (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
                * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                    (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                    (Function.update x j u) : ℝ) : ℂ)‖) := by ring
      _ ≤ |Θ x| * Csup * (Cimg * slotFibre (Work.BoseBoxFock.ellH v μ) i j Θ x) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hK (abs_nonneg _)) hin
          (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by positivity)
      _ = Csup * Cimg * (|Θ x| * slotFibre (Work.BoseBoxFock.ellH v μ) i j Θ x) := by ring
  rw [chBimg]
  calc ‖∫ x : Submission.BoseGases.X n,
        (Θ x : ℂ) * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
          * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              (∑' e : Fin 3 → ℤ, if e = 0 then 0
                else ((lowKer fc (chKappa v μ)
                  (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
              * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ))‖
      ≤ ∫ x : Submission.BoseGases.X n,
          ‖(Θ x : ℂ) * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
            * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                (∑' e : Fin 3 → ℤ, if e = 0 then 0
                  else ((lowKer fc (chKappa v μ)
                    (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
                * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                    (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                    (Function.update x j u) : ℝ) : ℂ))‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x : Submission.BoseGases.X n,
          Csup * Cimg * (|Θ x| * slotFibre (Work.BoseBoxFock.ellH v μ) i j Θ x) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _))
          (hstI.const_mul (Csup * Cimg)) (Filter.Eventually.of_forall (fun x => hpt x))
      _ = Csup * Cimg * ∫ x : Submission.BoseGases.X n,
            |Θ x| * slotFibre (Work.BoseBoxFock.ellH v μ) i j Θ x := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ Csup * Cimg * (8 * (Work.BoseBoxFock.ellH v μ) ^ 3
            * ∫ x : Submission.BoseGases.X n, (Θ x) ^ 2) :=
        mul_le_mul_of_nonneg_left hstB (by positivity)
      _ = 8 * Csup * Cimg * ((Work.BoseBoxFock.ellH v μ) ^ 3
            * ∫ x : Submission.BoseGases.X n, (Θ x) ^ 2) := by ring

/-- The squared box restriction integrates to the box norm. -/
private lemma integral_boxRestrictR_sq {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    ∫ x : Submission.BoseGases.X n, (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2
      = Work.BoseKinLoc.sqNormB n ℓ Φ := by
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2
        = (Submission.BoseGases.abox n ℓ).indicator (fun x => (Φ x) ^ 2) x := by
    intro x
    rw [Work.BoseBoxFock.boxRestrictR]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [Work.BoseKinLoc.sqNormB,
    ← MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)

theorem chBimg_piece (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chBimg v h fc fu μ N i j Θ) := by
  obtain ⟨Csup, hCsup0, hCsup⟩ := chBimg_Kchi_sup v h hv hav hv1 hvrad hR hv_supp fu
  obtain ⟨Cimg₀, hCimg₀0, himg₀⟩ := chiScale_lowKer_image_le fc 20
  set K0 : ℝ := 64 * Csup * Cimg₀
      * ((BoseGases.a v ^ 3 * (max 1 ε₀) ^ (((12 : ℝ) * 20 - 166) / 323)
          + (max 1 ε₀) ^ (((12 : ℝ) * 20 + 323) / 323)) / (BoseGases.a v) ^ 4) + 1 with hK0def
  have hK0pos : 0 < K0 := by
    rw [hK0def]
    have h1 : (0 : ℝ) ≤ (max 1 ε₀) ^ (((12 : ℝ) * 20 - 166) / 323) :=
      Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    have h2 : (0 : ℝ) ≤ (max 1 ε₀) ^ (((12 : ℝ) * 20 + 323) / 323) :=
      Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    positivity
  refine ⟨K0, hK0pos, ?_⟩
  refine ⟨fun μ => if 0 < μ then K0 * BoseGases.a v
      / (8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) else 0, fun _ => 0, ?_, ?_, ?_⟩
  · intro μ
    dsimp only
    by_cases hμ : 0 < μ
    · rw [if_pos hμ]
      have hden : (0 : ℝ) < 8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1) := by
        have := Work.BoseBoxFock.ellH_pos v μ
        positivity
      exact div_nonneg (mul_nonneg (le_of_lt hK0pos) (le_of_lt hav)) (le_of_lt hden)
    · rw [if_neg hμ]
  · intro μ hμ
    dsimp only
    rw [if_pos hμ]
    have hℓ : (0 : ℝ) < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
    simp only [zpow_neg]
    field_simp
    norm_num
  · intro Nmin hNth hT hreg HM hMono μ hAdm hJ n Φ hn hnorm hlow hspec i j hij
    have ha : (0 : ℝ) < BoseGases.a v := hav
    have hμ : 0 < μ := hAdm.1
    have hℓpos : (0 : ℝ) < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
    have hreg' : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0
        ∧ 4 * R ≤ Work.BoseBoxFock.ellH v μ := hreg μ hAdm
    have h2R : 2 * R ≤ Work.BoseBoxFock.ellH v μ := le_trans (by linarith) hreg'.2
    set t : ℝ := μ * (BoseGases.a v) ^ 3 with htdef
    have htpos : (0 : ℝ) < t := by rw [htdef]; positivity
    have htε : t ≤ ε₀ := by rw [htdef]; exact hAdm.2.1
    have hCsup' : ∀ z : E3, ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu (HM μ).N z‖ ≤ Csup :=
      fun z => hCsup μ hμ hreg'.1 h2R (HM μ).N z
    have hside : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
      if_pos (Work.BoseBox.sideAt_pos hμ ha)
    have hdeq : (Work.BoseBox.paramsAt μ (BoseGases.a v)).d = Work.BoseBox.fsXp t 6 := by
      rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, htdef]
    have hKleq : (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
        = Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) := by
      rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, htdef]
    have hdpos : (0 : ℝ) < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
      rw [hdeq]; exact Work.BoseBox.fsXp_pos htpos
    have hκeq : Work.BoseBoxFock.PCFU.chKappa v μ
        = 1 / ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * Work.BoseBoxFock.ellH v μ) := by
      rw [Work.BoseBoxFock.PCFU.chKappa, hside, one_div]
    have himg : ∀ (b u : E3), u ∈ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ) →
        ‖((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) b : ℝ) : ℂ)
          * (∑' e : Fin 3 → ℤ, if e = 0 then 0
              else ((lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (u - b + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
        ≤ Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
            / (Work.BoseBoxFock.ellH v μ) ^ 3 :=
      fun b u hu => himg₀ hdpos hℓpos hκeq b u hu
    -- the state estimate (the delegated `chBimg_state_le`)
    have hstate : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        |Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x|
          * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              |Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                  (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ))
                (Function.update x j u)|))
      ∧ (∫ x : Submission.BoseGases.X n,
            |Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x|
              * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                  |Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                    (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                      (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ))
                    (Function.update x j u)|))
          ≤ 8 * (Work.BoseBoxFock.ellH v μ) ^ 3
              * ∫ x : Submission.BoseGases.X n,
                  (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x) ^ 2 :=
      chBimg_state_le hℓpos i j hij (Φ := (Φ : Submission.BoseGases.X n → ℝ))
        Φ.contDiff.continuous
    have hΘm : Measurable (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ) := by
      have hunf : (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)
          = fun x : Submission.BoseGases.X n =>
              Φ x * (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)).indicator
                (fun _ => (1 : ℝ)) x := rfl
      rw [hunf]
      exact Φ.contDiff.continuous.measurable.mul
        (measurable_const.indicator
          (Submission.BoseGases.abox_measurable n (Work.BoseBoxFock.ellH v μ)))
    obtain ⟨B₀, hB₀⟩ := (Submission.BoseGases.abox_compact n hℓpos).exists_bound_of_continuousOn
      Φ.contDiff.continuous.continuousOn
    have hB : (0 : ℝ) ≤ max B₀ 0 := le_max_right _ _
    have hΘb : ∀ x, |Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x|
        ≤ max B₀ 0 := by
      intro x
      simp only [Work.BoseBoxFock.boxRestrictR]
      by_cases hx : x ∈ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)
      · rw [Set.indicator_of_mem hx, mul_one]
        have hb := hB₀ x hx
        rw [Real.norm_eq_abs] at hb
        exact le_trans hb (le_max_left _ _)
      · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
        exact hB
    have hcore := chBimg_core (ℓ := Work.BoseBoxFock.ellH v μ) rfl
      (Θ := Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)
      hΘm hB hΘb hCsup' himg i j hstate.1 hstate.2
    -- the arithmetic (the delegated `chBimg_arith`)
    have harith : (Work.BoseBox.fsXp t 6) ^ (2 * 20) * (t / (BoseGases.a v) ^ 3)
          * ((Work.BoseBox.fsXp t (-(3 / 2 : ℝ))
              * (t / (BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ))) ^ 3 + 1) / (BoseGases.a v)
        ≤ ((BoseGases.a v) ^ 3 * (max 1 ε₀) ^ (((12 : ℝ) * 20 - 166) / 323)
            + (max 1 ε₀) ^ (((12 : ℝ) * 20 + 323) / 323)) / (BoseGases.a v) ^ 4 :=
      chBimg_arith_aux (a := BoseGases.a v) (t := t) (ε₀ := ε₀) hav htpos htε 20 (by norm_num)
    have hℓeq : Work.BoseBoxFock.ellH v μ
        = Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) * (t / (BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ)) := by
      rw [hside, Work.BoseBox.sideAt, Work.BoseBox.boxSide, hKleq]
      congr 1
      have hbase : μ * BoseGases.a v = t / (BoseGases.a v) ^ 2 := by
        rw [htdef]; field_simp
      rw [hbase]
    have hμeq : μ = t / (BoseGases.a v) ^ 3 := by
      rw [htdef]; field_simp
    have hC0 : (0 : ℝ) ≤ 64 * Csup * Cimg₀ := by positivity
    have hkey : 64 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
          * (μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) / (BoseGases.a v) ≤ K0 := by
      have hle : (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20)
            * (μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) / (BoseGases.a v)
          ≤ ((BoseGases.a v) ^ 3 * (max 1 ε₀) ^ (((12 : ℝ) * 20 - 166) / 323)
              + (max 1 ε₀) ^ (((12 : ℝ) * 20 + 323) / 323)) / (BoseGases.a v) ^ 4 := by
        have hshape : (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20)
              * (μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) / (BoseGases.a v)
            = (Work.BoseBox.fsXp t 6) ^ (2 * 20) * (t / (BoseGases.a v) ^ 3)
              * ((Work.BoseBox.fsXp t (-(3 / 2 : ℝ))
                  * (t / (BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ))) ^ 3 + 1) / (BoseGases.a v) := by
          rw [hdeq, hℓeq, hμeq]
          ring
        rw [hshape]
        exact harith
      have h1 : 64 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20)
            * (μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) / (BoseGases.a v))
          ≤ 64 * Csup * Cimg₀
            * (((BoseGases.a v) ^ 3 * (max 1 ε₀) ^ (((12 : ℝ) * 20 - 166) / 323)
              + (max 1 ε₀) ^ (((12 : ℝ) * 20 + 323) / 323)) / (BoseGases.a v) ^ 4) :=
        mul_le_mul_of_nonneg_left hle hC0
      have hgoal : 64 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
            * (μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) / (BoseGases.a v)
          = 64 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20)
            * (μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) / (BoseGases.a v)) := by ring
      rw [hgoal, hK0def]
      have h2 : 64 * Csup * Cimg₀
            * (((BoseGases.a v) ^ 3 * (max 1 ε₀) ^ (((12 : ℝ) * 20 - 166) / 323)
              + (max 1 ε₀) ^ (((12 : ℝ) * 20 + 323) / 323)) / (BoseGases.a v) ^ 4)
          ≤ 64 * Csup * Cimg₀
            * (((BoseGases.a v) ^ 3 * (max 1 ε₀) ^ (((12 : ℝ) * 20 - 166) / 323)
              + (max 1 ε₀) ^ (((12 : ℝ) * 20 + 323) / 323)) / (BoseGases.a v) ^ 4) + 1 :=
        le_add_of_nonneg_right zero_le_one
      linarith [h1, h2]
    have hnormB : ∫ x : Submission.BoseGases.X n,
          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x) ^ 2
        = Work.BoseBoxFix.normB v μ n Φ := by
      rw [Work.BoseBoxFix.normB, hside, integral_boxRestrictR_sq]
    have hfinal : 8 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
        ≤ (if 0 < μ then K0 * BoseGases.a v
            / (8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) else 0) := by
      rw [if_pos hμ]
      have hpos : (0 : ℝ) < BoseGases.a v
          / (8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) := by positivity
      have h1 := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
      have h2 : (64 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
            * (μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) / (BoseGases.a v))
            * (BoseGases.a v / (8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)))
          = 8 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20)) := by
        field_simp
        ring
      have h3 : K0 * (BoseGases.a v / (8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)))
          = K0 * BoseGases.a v / (8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) := by ring
      rw [h2, h3] at h1
      exact h1
    calc ‖Work.BoseBoxFock.PCFU.chBimg v h fc fu μ (HM μ).N i j
          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)‖
        ≤ 8 * Csup * (Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
              / (Work.BoseBoxFock.ellH v μ) ^ 3)
            * ((Work.BoseBoxFock.ellH v μ) ^ 3
              * ∫ x : Submission.BoseGases.X n,
                  (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x) ^ 2) := hcore
      _ = 8 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
            * ∫ x : Submission.BoseGases.X n,
                (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x) ^ 2 := by
          field_simp
      _ = 8 * Csup * Cimg₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ (2 * 20))
            * Work.BoseBoxFix.normB v μ n Φ := by rw [hnormB]
      _ ≤ (if 0 < μ then K0 * BoseGases.a v
            / (8 * μ * ((Work.BoseBoxFock.ellH v μ) ^ 3 + 1)) else 0)
            * Work.BoseBoxFix.normB v μ n Φ :=
          mul_le_mul_of_nonneg_right hfinal (le_of_lt hnorm)

end Work.BoseBoxFock.PCFU
