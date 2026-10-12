import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB3.Conv.pair_peel
import Submission.Work.BoseFixB3.Conv.pair_transfer_pos
import Submission.Work.BoseFixB3.Eps.highSlot_chiSq_aP_eq
import Submission.Work.BoseFixB3.HighMass.highSlot_sq_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.Conv

set_option autoImplicit false

/-- The pointwise identity turning the `χ_ℓ² I` weight into the residual `hRes`. -/
lemma highMult_chiSq_mul_const (fc : Work.BoseBoxFix.LowCut) (κ ℓ I : ℝ)
    (y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB3.highMult fc κ ℓ
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ z * (Submission.BoseGases.chiScale ℓ z * I)) y
      = I * Work.BoseFixB3.Eps.hRes fc κ ℓ y := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ z * (Submission.BoseGases.chiScale ℓ z * I))
      = fun z : EuclideanSpace ℝ (Fin 3) =>
          I * (fun w : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiScale ℓ w ^ 2) z := by
    funext z; ring
  simp only [Work.BoseFixB3.highMult]
  rw [hfun, Work.BoseFixB3.Eps.lowMult_const_mul]
  simp only [Work.BoseFixB3.Eps.hRes, Work.BoseFixB3.chiU_zero_eq_chiScale]
  ring

/-- The convolution `conv3 f χ_ℓ` of an integrable `f` with the continuous bump is
a.e. strongly measurable. -/
lemma conv3_chiScale_aesm {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    (ℓ : ℝ) :
    AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.conv3 f
        (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹) • z)) y) volume := by
  set g : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹) • z) with hg
  have hgm : Measurable g := by
    rw [hg]
    exact (Submission.BoseGases.chi_contDiff.continuous.comp
      (Continuous.const_smul continuous_id (ℓ⁻¹))).measurable
  have hjoint : StronglyMeasurable (fun w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (hf.aestronglyMeasurable.mk f) w.2 * g (w.1 - w.2)) :=
    (((hf.aestronglyMeasurable.stronglyMeasurable_mk).comp_measurable measurable_snd)).mul
      (hgm.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  have hint : StronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
      ∫ x : EuclideanSpace ℝ (Fin 3), (hf.aestronglyMeasurable.mk f) x * g (y - x)) :=
    StronglyMeasurable.integral_prod_right' (ν := volume) hjoint
  have heq : (fun y : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.conv3 f g y)
      = fun y : EuclideanSpace ℝ (Fin 3) =>
          ∫ x : EuclideanSpace ℝ (Fin 3), (hf.aestronglyMeasurable.mk f) x * g (y - x) := by
    funext y
    rw [Submission.BoseGases.conv3]
    apply integral_congr_ae
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with x hx
    rw [hx]
  rw [hg] at heq
  rw [heq]
  exact hint.aestronglyMeasurable

/-- The same convolution evaluated in one slot of an `n`-body configuration is a.e.
strongly measurable. -/
lemma conv3_chiScale_apply_aesm {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.Integrable f) (ℓ : ℝ) {n : ℕ} (j : Fin n) :
    AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.conv3 f
        (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (x j)) volume := by
  set g : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹) • z) with hg
  have hgm : Measurable g := by
    rw [hg]
    exact (Submission.BoseGases.chi_contDiff.continuous.comp
      (Continuous.const_smul continuous_id (ℓ⁻¹))).measurable
  have hjm : Measurable (fun x : Submission.BoseGases.X n => x j) := (continuous_apply j).measurable
  have hjoint : StronglyMeasurable
      (fun w : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
        (hf.aestronglyMeasurable.mk f) w.2 * g (w.1 j - w.2)) :=
    ((hf.aestronglyMeasurable.stronglyMeasurable_mk).comp_measurable measurable_snd).mul
      (hgm.comp ((hjm.comp measurable_fst).sub measurable_snd)).stronglyMeasurable
  have hint : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∫ y : EuclideanSpace ℝ (Fin 3), (hf.aestronglyMeasurable.mk f) y * g (x j - y)) :=
    StronglyMeasurable.integral_prod_right' (ν := volume) hjoint
  have heq : (fun x : Submission.BoseGases.X n => Submission.BoseGases.conv3 f g (x j))
      = fun x : Submission.BoseGases.X n =>
          ∫ y : EuclideanSpace ℝ (Fin 3), (hf.aestronglyMeasurable.mk f) y * g (x j - y) := by
    funext x
    rw [Submission.BoseGases.conv3]
    apply integral_congr_ae
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with y hy
    rw [hy]
  rw [hg] at heq
  rw [heq]
  exact hint.aestronglyMeasurable

/-- Measurability of the residual `ρ` in a slot of an `n`-body configuration, from the
defining convolution identity. -/
lemma rho_apply_aesm {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    {ℓ I : ℝ} {ρ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hρ : ∀ y, Submission.BoseGases.conv3 f
        (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) y
      = Submission.BoseGases.chiScale ℓ y * I + ρ y) {n : ℕ} (j : Fin n) :
    AEStronglyMeasurable (fun x : Submission.BoseGases.X n => ρ (x j)) volume := by
  have heq : ρ = fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) y
        - Submission.BoseGases.chiScale ℓ y * I := by
    funext y
    have h := hρ y
    linarith
  have hfun : (fun x : Submission.BoseGases.X n => ρ (x j))
      = fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (x j)
            - Submission.BoseGases.chiScale ℓ (x j) * I := by
    funext x
    rw [heq]
  rw [hfun]
  exact (conv3_chiScale_apply_aesm hf ℓ j).sub
    (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j)).aestronglyMeasurable.mul_const I)

/-- A pointwise bounded, a.e. strongly measurable function on the box is integrable. -/
lemma integrableOn_of_bounded {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Submission.BoseGases.X n → ℝ}
    (hmeas : AEStronglyMeasurable F
      ((volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)))
    {C : ℝ} (hC : ∀ x ∈ Submission.BoseGases.abox n ℓ, |F x| ≤ C) :
    IntegrableOn F (Submission.BoseGases.abox n ℓ) volume := by
  refine MeasureTheory.IntegrableOn.of_bound
    ((Submission.BoseGases.abox_compact n hℓ).measure_lt_top) hmeas C ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
  exact Filter.Eventually.of_forall (fun x hx => by
    rw [Real.norm_eq_abs]; exact hC x hx)

/-- The slot-`j` transfer of the weight `χ_ℓ² · I` into the residual pairing. -/
lemma transfer_step {n : ℕ} {ℓ κ : ℝ} {fc : Work.BoseBoxFix.LowCut} (hℓ : 0 < ℓ) (hκ : 0 < κ)
    {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) (I : ℝ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x j) * (Submission.BoseGases.chiScale ℓ (x j) * I)))
      = I * ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j)) := by
  set W : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun z => Submission.BoseGases.chiScale ℓ z * (Submission.BoseGases.chiScale ℓ z * I) with hW
  have hWm : Measurable W := by
    rw [hW]
    exact (Submission.BoseGases.chiScale_continuous ℓ).measurable.mul
      (((Submission.BoseGases.chiScale_continuous ℓ).measurable).mul_const I)
  have hWb : ∃ C : ℝ, ∀ y, |W y| ≤ C := by
    refine ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * |I|), fun y => ?_⟩
    have hWy : W y = Submission.BoseGases.chiScale ℓ y
        * (Submission.BoseGases.chiScale ℓ y * I) := rfl
    have h1 : |Submission.BoseGases.chiScale ℓ y| ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      Submission.BoseGases.abs_chiScale_le ℓ y
    have h3 : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by positivity
    rw [hWy]
    simp only [abs_mul]
    exact mul_le_mul h1 (mul_le_mul h1 le_rfl (abs_nonneg I) h3)
      (mul_nonneg (abs_nonneg _) (abs_nonneg I)) h3
  have htr := pair_transfer_pos (n := n) (ℓ := ℓ) (κ := κ) fc hℓ hκ hij hΦ hWm hWb
  rw [htr]
  have hpt : ∀ x : Submission.BoseGases.X n,
      Submission.BoseGases.aP ℓ i Φ x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Work.BoseFixB3.highMult fc κ ℓ W (x j)
        = I * (Submission.BoseGases.aP ℓ i Φ x
            * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j))) := by
    intro x
    rw [hW, highMult_chiSq_mul_const]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul]

/-- The residual term is bounded by `ρmax · χ_M · ∫ Φ²`. -/
lemma rho_pair_le {n : ℕ} {ℓ κ : ℝ} {fc : Work.BoseBoxFix.LowCut} (hℓ : 0 < ℓ) (hκ : 0 < κ)
    {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    {ρ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hρae : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => ρ (x j)) volume)
    {ρmax : ℝ} (hρmax : 0 ≤ ρmax) (hρb : ∀ y, |ρ y| ≤ ρmax) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x j) * ρ (x j)))
      ≤ ρmax * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  set Ψ : Submission.BoseGases.X n → ℝ := Submission.BoseGases.aP ℓ i Φ with hΨ
  set B : Submission.BoseGases.X n → ℝ := Submission.BoseGases.aP ℓ j Ψ with hB
  set H : Submission.BoseGases.X n → ℝ := Work.BoseFixB3.highSlot fc κ ℓ j Ψ with hH
  set χ : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.chiScale ℓ with hχ
  set chiM : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hchiM
  have hχc : Continuous χ := by rw [hχ]; exact Submission.BoseGases.chiScale_continuous ℓ
  have hchiM0 : 0 ≤ chiM := by rw [hchiM]; positivity
  have hχb : ∀ y, |χ y| ≤ chiM := by
    intro y; rw [hχ, hchiM]; exact Submission.BoseGases.abs_chiScale_le ℓ y
  obtain ⟨CH, hCH0, hCH⟩ :=
    Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ)
      hκ hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦ)
  have hHpt : ∀ x ∈ Submission.BoseGases.abox n ℓ, |H x| ≤ CH := by
    intro x hx; rw [hH, hΨ]; exact hCH x hx
  have hBc : Continuous B := by
    rw [hB, hΨ]
    exact Submission.BoseGases.aP_continuous hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦ)
  obtain ⟨CB, hCB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := B) hBc.continuousOn
  have hCB0 : 0 ≤ CB := by
    have h := hCB (0 : Submission.BoseGases.X n) (Submission.BoseGases.zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg _) h
  have hBpt : ∀ x ∈ Submission.BoseGases.abox n ℓ, |B x| ≤ CB := by
    intro x hx
    have h := hCB x hx
    rwa [Real.norm_eq_abs] at h
  have hHm : Measurable H := by
    rw [hH]
    exact Work.BoseFixB3.HighMass.measurable_highSlot (fc := fc) (κ := κ) (ℓ := ℓ) j
      (Submission.BoseGases.aP_continuous hℓ i hΦ)
  have hIntAbs : IntegrableOn (fun x : Submission.BoseGases.X n => |H x * B x|)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_bounded hℓ ?_ (C := CH * CB) (fun x hx => ?_)
    · exact ((hHm.mul hBc.measurable).abs).aestronglyMeasurable.restrict
    · rw [abs_of_nonneg (abs_nonneg (H x * B x)), abs_mul]
      exact mul_le_mul (hHpt x hx) (hBpt x hx) (abs_nonneg _) hCH0
  have hH2 : (∫ x in Submission.BoseGases.abox n ℓ, (H x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
    have h1 : (∫ x in Submission.BoseGases.abox n ℓ, (H x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2 := by
      rw [hH, hΨ]
      exact Work.BoseFixB3.HighMass.highSlot_sq_integral_le hℓ j
        (Submission.BoseGases.aP_continuous hℓ i hΦ)
    have h2 : (∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
      rw [hΨ]; exact Submission.BoseGases.aP_sq_le hℓ i hΦ
    exact le_trans h1 h2
  have hB2 : (∫ x in Submission.BoseGases.abox n ℓ, (B x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
    have h1 : (∫ x in Submission.BoseGases.abox n ℓ, (B x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2 := by
      rw [hB]
      exact Submission.BoseGases.aP_sq_le hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦ)
    have h2 : (∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
      rw [hΨ]; exact Submission.BoseGases.aP_sq_le hℓ i hΦ
    exact le_trans h1 h2
  have hIntHS2 : IntegrableOn (fun x : Submission.BoseGases.X n => (H x ^ 2 + B x ^ 2) / 2)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_bounded hℓ ?_ (C := (CH ^ 2 + CB ^ 2) / 2) (fun x hx => ?_)
    · have hm : Measurable (fun x : Submission.BoseGases.X n => (H x ^ 2 + B x ^ 2) / 2) :=
        ((hHm.pow_const 2).add (hBc.measurable.pow_const 2)).div_const 2
      exact hm.aestronglyMeasurable.restrict
    · have hh : H x ^ 2 ≤ CH ^ 2 := by
        rw [← sq_abs (H x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hHpt x hx) 2
      have hb : B x ^ 2 ≤ CB ^ 2 := by
        rw [← sq_abs (B x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hBpt x hx) 2
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (H x ^ 2 + B x ^ 2) / 2)]
      linarith
  have hIntH2h : IntegrableOn (fun x : Submission.BoseGases.X n => H x ^ 2 / 2)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_bounded hℓ ?_ (C := CH ^ 2 / 2) (fun x hx => ?_)
    · exact ((hHm.pow_const 2).div_const 2).aestronglyMeasurable.restrict
    · have hh : H x ^ 2 ≤ CH ^ 2 := by
        rw [← sq_abs (H x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hHpt x hx) 2
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ H x ^ 2 / 2)]
      linarith
  have hIntB2h : IntegrableOn (fun x : Submission.BoseGases.X n => B x ^ 2 / 2)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_bounded hℓ ?_ (C := CB ^ 2 / 2) (fun x hx => ?_)
    · exact ((hBc.measurable.pow_const 2).div_const 2).aestronglyMeasurable.restrict
    · have hb : B x ^ 2 ≤ CB ^ 2 := by
        rw [← sq_abs (B x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hBpt x hx) 2
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ B x ^ 2 / 2)]
      linarith
  have hcs : (∫ x in Submission.BoseGases.abox n ℓ, |H x * B x|)
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
    have h1 : (∫ x in Submission.BoseGases.abox n ℓ, |H x * B x|)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, (H x ^ 2 + B x ^ 2) / 2 := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hIntHS2
        (Filter.Eventually.of_forall (fun x => ?_))
      show |H x * B x| ≤ (H x ^ 2 + B x ^ 2) / 2
      rw [abs_mul, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [sq_nonneg (|H x| - |B x|), abs_nonneg (H x), abs_nonneg (B x),
        sq_abs (H x), sq_abs (B x)]
    have h2 : (∫ x in Submission.BoseGases.abox n ℓ, (H x ^ 2 + B x ^ 2) / 2)
        = ((∫ x in Submission.BoseGases.abox n ℓ, H x ^ 2)
            + (∫ x in Submission.BoseGases.abox n ℓ, B x ^ 2)) / 2 := by
      rw [show (∫ x in Submission.BoseGases.abox n ℓ, (H x ^ 2 + B x ^ 2) / 2)
          = ∫ x in Submission.BoseGases.abox n ℓ, (H x ^ 2 / 2 + B x ^ 2 / 2) from
        integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))]
      rw [MeasureTheory.integral_add hIntH2h hIntB2h]
      rw [MeasureTheory.integral_div 2 (fun x => H x ^ 2),
        MeasureTheory.integral_div 2 (fun x => B x ^ 2)]
      ring
    calc (∫ x in Submission.BoseGases.abox n ℓ, |H x * B x|)
        ≤ ∫ x in Submission.BoseGases.abox n ℓ, (H x ^ 2 + B x ^ 2) / 2 := h1
      _ = ((∫ x in Submission.BoseGases.abox n ℓ, H x ^ 2)
            + (∫ x in Submission.BoseGases.abox n ℓ, B x ^ 2)) / 2 := h2
      _ ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by linarith [hH2, hB2]
  have hIntR : IntegrableOn
      (fun x : Submission.BoseGases.X n => H x * B x * (χ (x j) * ρ (x j)))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_bounded hℓ ?_ (C := CH * CB * (chiM * ρmax)) (fun x hx => ?_)
    · have h1 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => H x * B x) volume :=
        hHm.aestronglyMeasurable.mul hBc.measurable.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => χ (x j)) volume :=
        (hχc.measurable.comp (continuous_apply j).measurable).aestronglyMeasurable
      have h3 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => χ (x j) * ρ (x j)) volume :=
        h2.mul hρae
      exact (h1.mul h3).restrict
    · simp only [abs_mul]
      have hχρ : |χ (x j)| * |ρ (x j)| ≤ chiM * ρmax :=
        mul_le_mul (hχb (x j)) (hρb (x j)) (abs_nonneg _) hchiM0
      have hHB : |H x| * |B x| ≤ CH * CB :=
        mul_le_mul (hHpt x hx) (hBpt x hx) (abs_nonneg _) hCH0
      exact mul_le_mul hHB hχρ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hCH0 hCB0)
  have hIntRabs : IntegrableOn
      (fun x : Submission.BoseGases.X n => ρmax * chiM * |H x * B x|)
      (Submission.BoseGases.abox n ℓ) volume := by
    have h' : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => |H x * B x|)
        ((volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := hIntAbs
    exact h'.const_mul (ρmax * chiM)
  calc (∫ x in Submission.BoseGases.abox n ℓ, H x * B x * (χ (x j) * ρ (x j)))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, |H x * B x * (χ (x j) * ρ (x j))| :=
        le_trans (le_abs_self _) abs_integral_le_integral_abs
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ, ρmax * chiM * |H x * B x| := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hIntRabs
          (Filter.Eventually.of_forall (fun x => ?_))
        show |H x * B x * (χ (x j) * ρ (x j))| ≤ ρmax * chiM * |H x * B x|
        simp only [abs_mul]
        have hχρ : |χ (x j)| * |ρ (x j)| ≤ chiM * ρmax :=
          mul_le_mul (hχb (x j)) (hρb (x j)) (abs_nonneg _) hchiM0
        have h3 : |H x| * |B x| * (|χ (x j)| * |ρ (x j)|)
            ≤ |H x| * |B x| * (chiM * ρmax) :=
          mul_le_mul_of_nonneg_left hχρ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have h4 : |H x| * |B x| * (chiM * ρmax) = ρmax * chiM * (|H x| * |B x|) := by ring
        rw [h4] at h3
        exact h3
    _ = ρmax * chiM * (∫ x in Submission.BoseGases.abox n ℓ, |H x * B x|) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ρmax * chiM * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (mul_nonneg hρmax hchiM0)

/-- Integrability of the two pieces of the residual split. -/
lemma integrable_pair_parts {n : ℕ} {ℓ κ I : ℝ} {fc : Work.BoseBoxFix.LowCut} (hℓ : 0 < ℓ)
    (hκ : 0 < κ) {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) {ρ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hρae : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => ρ (x j)) volume)
    {ρmax : ℝ} (hρmax : 0 ≤ ρmax) (hρb : ∀ y, |ρ y| ≤ ρmax) :
    IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x j) * (Submission.BoseGases.chiScale ℓ (x j) * I)))
      (Submission.BoseGases.abox n ℓ) volume
    ∧ IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x j) * ρ (x j)))
      (Submission.BoseGases.abox n ℓ) volume := by
  set Ψ : Submission.BoseGases.X n → ℝ := Submission.BoseGases.aP ℓ i Φ with hΨ
  set B : Submission.BoseGases.X n → ℝ := Submission.BoseGases.aP ℓ j Ψ with hB
  set H : Submission.BoseGases.X n → ℝ := Work.BoseFixB3.highSlot fc κ ℓ j Ψ with hH
  set χ : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.chiScale ℓ with hχ
  set chiM : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hchiM
  have hχc : Continuous χ := by rw [hχ]; exact Submission.BoseGases.chiScale_continuous ℓ
  have hchiM0 : 0 ≤ chiM := by rw [hchiM]; positivity
  have hχb : ∀ y, |χ y| ≤ chiM := by
    intro y; rw [hχ, hchiM]; exact Submission.BoseGases.abs_chiScale_le ℓ y
  obtain ⟨CH, hCH0, hCH⟩ :=
    Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ)
      hκ hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦ)
  have hHpt : ∀ x ∈ Submission.BoseGases.abox n ℓ, |H x| ≤ CH := by
    intro x hx; rw [hH, hΨ]; exact hCH x hx
  have hBc : Continuous B := by
    rw [hB, hΨ]
    exact Submission.BoseGases.aP_continuous hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦ)
  obtain ⟨CB, hCB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := B) hBc.continuousOn
  have hCB0 : 0 ≤ CB := by
    have h := hCB (0 : Submission.BoseGases.X n) (Submission.BoseGases.zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg _) h
  have hBpt : ∀ x ∈ Submission.BoseGases.abox n ℓ, |B x| ≤ CB := by
    intro x hx
    have h := hCB x hx
    rwa [Real.norm_eq_abs] at h
  have hHm : Measurable H := by
    rw [hH]
    exact Work.BoseFixB3.HighMass.measurable_highSlot (fc := fc) (κ := κ) (ℓ := ℓ) j
      (Submission.BoseGases.aP_continuous hℓ i hΦ)
  have hmHB : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => H x * B x) volume :=
    hHm.aestronglyMeasurable.mul hBc.measurable.aestronglyMeasurable
  have hmχ : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => χ (x j)) volume :=
    (hχc.measurable.comp (continuous_apply j).measurable).aestronglyMeasurable
  constructor
  · refine integrableOn_of_bounded hℓ ?_ (C := CH * CB * (chiM * (chiM * |I|))) (fun x hx => ?_)
    · have h2 : AEStronglyMeasurable
          (fun x : Submission.BoseGases.X n => χ (x j) * (χ (x j) * I)) volume :=
        hmχ.mul (hmχ.mul_const I)
      exact (hmHB.mul h2).restrict
    · simp only [abs_mul]
      have h1 : |H x| * |B x| ≤ CH * CB :=
        mul_le_mul (hHpt x hx) (hBpt x hx) (abs_nonneg _) hCH0
      have h2 : |χ (x j)| * (|χ (x j)| * |I|) ≤ chiM * (chiM * |I|) :=
        mul_le_mul (hχb (x j))
          (mul_le_mul (hχb (x j)) le_rfl (abs_nonneg I) hchiM0)
          (mul_nonneg (abs_nonneg (χ (x j))) (abs_nonneg I)) hchiM0
      exact mul_le_mul h1 h2
        (mul_nonneg (abs_nonneg (χ (x j))) (mul_nonneg (abs_nonneg (χ (x j))) (abs_nonneg I)))
        (mul_nonneg hCH0 hCB0)
  · refine integrableOn_of_bounded hℓ ?_ (C := CH * CB * (chiM * ρmax)) (fun x hx => ?_)
    · have h1 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => H x * B x) volume :=
        hmHB
      have h2 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => χ (x j)) volume := hmχ
      have h3 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => χ (x j) * ρ (x j)) volume :=
        h2.mul hρae
      exact (h1.mul h3).restrict
    · simp only [abs_mul]
      have hχρ : |χ (x j)| * |ρ (x j)| ≤ chiM * ρmax :=
        mul_le_mul (hχb (x j)) (hρb (x j)) (abs_nonneg _) hchiM0
      have hHB : |H x| * |B x| ≤ CH * CB :=
        mul_le_mul (hHpt x hx) (hBpt x hx) (abs_nonneg _) hCH0
      exact mul_le_mul hHB hχρ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hCH0 hCB0)

/-- The peel, the substitution of the convolution identity and the split of the residual. -/
lemma pair_conv_split {n : ℕ} {ℓ κ : ℝ} {fc : Work.BoseBoxFix.LowCut} (hℓ : 0 < ℓ) (hκ : 0 < κ)
    {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hfint : MeasureTheory.Integrable f)
    (hfeven : ∀ x : EuclideanSpace ℝ (Fin 3), f (-x) = f x)
    {I : ℝ} {ρ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hρ : ∀ y, Submission.BoseGases.conv3 f
        (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) y
      = Submission.BoseGases.chiScale ℓ y * I + ρ y)
    (hInt1 : IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x j) * (Submission.BoseGases.chiScale ℓ (x j) * I)))
      (Submission.BoseGases.abox n ℓ) volume)
    (hInt2 : IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x j) * ρ (x j)))
      (Submission.BoseGases.abox n ℓ) volume) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x i) * f (x i - x j)
              * Submission.BoseGases.chiScale ℓ (x j)))
      = (ℓ ^ 3)⁻¹ *
          ((∫ x in Submission.BoseGases.abox n ℓ,
              Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                * (Submission.BoseGases.chiScale ℓ (x j)
                    * (Submission.BoseGases.chiScale ℓ (x j) * I)))
            + (∫ x in Submission.BoseGases.abox n ℓ,
                Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                  * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                  * (Submission.BoseGases.chiScale ℓ (x j) * ρ (x j)))) := by
  rw [pair_peel fc hℓ hij hΦ hfint hfeven]
  congr 1
  have hsub : (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x j)
              * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (x j)))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            * (Submission.BoseGases.chiScale ℓ (x j)
                * (Submission.BoseGases.chiScale ℓ (x j) * I + ρ (x j))) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hρ (x j)]
  rw [hsub]
  rw [← MeasureTheory.integral_add hInt1 hInt2]
  apply integral_congr_ae
  filter_upwards with x
  ring


/-- **The pair convolution bound** (FS `lem:Convolution` applied to a pair of slots). -/
theorem pair_conv_bound {n : ℕ} {ℓ κ : ℝ} {fc : Work.BoseBoxFix.LowCut} (hℓ : 0 < ℓ) (hκ : 0 < κ)
    {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hfint : MeasureTheory.Integrable f)
    (hfeven : ∀ x : EuclideanSpace ℝ (Fin 3), f (-x) = f x)
    {I : ℝ} (hI : I = ∫ y, f y)
    {ρ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hρ : ∀ y, Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) y
      = Submission.BoseGases.chiScale ℓ y * I + ρ y)
    {ρmax : ℝ} (hρmax : 0 ≤ ρmax)
    (hρb : ∀ y, |ρ y| ≤ ρmax) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x i) * f (x i - x j)
              * Submission.BoseGases.chiScale ℓ (x j)))
      ≤ (ℓ ^ 3)⁻¹ *
          (I * (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Φ x
                * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
                    * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j)))
            + ρmax * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
                * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
  have hρae : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => ρ (x j)) volume :=
    rho_apply_aesm hfint hρ j
  obtain ⟨hInt1, hInt2⟩ := integrable_pair_parts (fc := fc) hℓ hκ hij hΦ hρae hρmax hρb
  rw [pair_conv_split (fc := fc) hℓ hκ hij hΦ hfint hfeven hρ hInt1 hInt2]
  rw [transfer_step (fc := fc) hℓ hκ hij hΦ I]
  have hbound := rho_pair_le (fc := fc) hℓ hκ hij hΦ hρae hρmax hρb
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · linarith [hbound]
  · positivity


end Work.BoseFixB3.Conv
