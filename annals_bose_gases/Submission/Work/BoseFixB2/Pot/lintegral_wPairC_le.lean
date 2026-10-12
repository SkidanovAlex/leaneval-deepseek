import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Pot.lintegral_wPairC_le`

The `L¹`-bound for the χ-renormalized localized two-body kernel

`wPairC ℓ h x y = χ_ℓ x · (h (x−y) / (χ⋆χ)_ℓ (x−y)) · χ_ℓ y`:

    ∫⁻_{(x,y)} ‖wPairC ℓ h x y‖ₑ  ≤  ofReal (ℓ³ · ∫ |h|)

for `0 < ℓ` and *integrable* `h` (no diluteness hypothesis, and the denominator
`(χ⋆χ)_ℓ` is never assumed to be nonvanishing).  The proof is the exact
cancellation, in the *joint* integral, of the two cutoff factors against the
denominator: Tonelli plus the substitution `y ↦ x − y` turns the double
integral into `∫⁻_z ‖h(z)/(χ⋆χ)_ℓ(z)‖ₑ · ∫⁻_x χ_ℓ x · χ_ℓ (x−z)`, and the
inner fibre is `ofReal (ℓ³ · (χ⋆χ)_ℓ z)` (`Submission.BoseGases.integral_pair_scale`);
pointwise `c · (|h z| / c) ≤ |h z|` for `c = (χ⋆χ)_ℓ z ≥ 0` (with Lean's `x/0 = 0`
convention the case `c = 0` is trivial).  Everything is stated with `∫⁻` because
Bochner integrals of non-integrable functions would be `0` and make the
intermediate steps vacuous.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.Pot

set_option autoImplicit false

-- `ℝ³` is the (global) notation `EuclideanSpace ℝ (Fin 3)`, provided by
-- `Submission.Work.BoseKinLoc.Defs` through the `Prelude` import bundle.

/-- `(x,y) ↦ x − y` is quasi-measure-preserving on `ℝ³ × ℝ³` for Lebesgue measure. -/
private lemma qmp_sub_prod_vol :
    Measure.QuasiMeasurePreserving (fun p : ℝ³ × ℝ³ => p.1 - p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) (volume : Measure ℝ³) :=
  quasiMeasurePreserving_sub_of_right_invariant _ _

/-- Pointwise expansion of the `enorm` of the kernel into a product of three
`ENNReal.ofReal` factors (`χ_ℓ ≥ 0`). -/
private lemma wPairC_enorm_eq (ℓ : ℝ) (h : ℝ³ → ℝ) (x y : ℝ³) :
    ‖Submission.BoseGases.wPairC ℓ h x y‖ₑ
      = ENNReal.ofReal (Submission.BoseGases.chiScale ℓ x)
        * ENNReal.ofReal |Submission.BoseGases.wScaled ℓ h (x - y)|
        * ENNReal.ofReal (Submission.BoseGases.chiScale ℓ y) := by
  rw [Real.enorm_eq_ofReal_abs]
  have habs : |Submission.BoseGases.wPairC ℓ h x y|
      = Submission.BoseGases.chiScale ℓ x
        * |Submission.BoseGases.wScaled ℓ h (x - y)|
        * Submission.BoseGases.chiScale ℓ y := by
    simp only [Submission.BoseGases.wPairC, Submission.BoseGases.wPair]
    rw [abs_mul, abs_mul, abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x),
      abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ y)]
  rw [habs,
    ENNReal.ofReal_mul (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x) (abs_nonneg _)),
    ENNReal.ofReal_mul (Submission.BoseGases.chiScale_nonneg ℓ x)]

/-- Tonelli plus the difference substitution on `ℝ³ × ℝ³`: for measurable
`F G : ℝ³ → ℝ≥0∞`,

    ∫⁻_{(x,y)} F x · G (x−y) · F y = ∫⁻_z G z · ∫⁻_x F x · F (x−z). -/
private lemma pair_lintegral_aux {F G : ℝ³ → ENNReal} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ p : ℝ³ × ℝ³, F p.1 * G (p.1 - p.2) * F p.2
        ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
      = ∫⁻ z : ℝ³, G z * (∫⁻ x : ℝ³, F x * F (x - z)) := by
  have hsubm : Measurable (fun p : ℝ³ × ℝ³ => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hΦ : Measurable (fun p : ℝ³ × ℝ³ => F p.1 * G (p.1 - p.2) * F p.2) :=
    ((hF.comp measurable_fst).mul (hG.comp hsubm)).mul (hF.comp measurable_snd)
  have hGy : ∀ x : ℝ³, Measurable (fun y : ℝ³ => G (x - y)) :=
    fun x => hG.comp (measurable_const.sub measurable_id)
  have hfib : ∀ x : ℝ³, Measurable (fun z : ℝ³ => G z * F (x - z)) :=
    fun x => hG.mul (hF.comp (measurable_const.sub measurable_id))
  rw [lintegral_prod _ hΦ.aemeasurable]
  have key2 : ∀ x : ℝ³,
      (∫⁻ y : ℝ³, F x * G (x - y) * F y) = F x * (∫⁻ z : ℝ³, G z * F (x - z)) := by
    intro x
    rw [show (fun y : ℝ³ => F x * G (x - y) * F y)
          = (fun y : ℝ³ => F x * (G (x - y) * F y)) from by
        funext y; rw [mul_assoc]]
    have hstep1 : (∫⁻ y : ℝ³, F x * (G (x - y) * F y))
        = F x * (∫⁻ y : ℝ³, G (x - y) * F y) :=
      lintegral_const_mul (μ := (volume : Measure ℝ³)) (F x) ((hGy x).mul hF)
    have hstep2 : (∫⁻ y : ℝ³, G (x - y) * F y) = ∫⁻ z : ℝ³, G z * F (x - z) := by
      rw [← (Submission.BoseGases.measurePreserving_sub_left x).lintegral_comp (hfib x)]
      apply lintegral_congr
      intro y
      show G (x - y) * F y = G (x - y) * F (x - (x - y))
      rw [show x - (x - y) = y by abel]
    rw [hstep1, hstep2]
  rw [lintegral_congr key2]
  have hgm : Measurable (fun q : ℝ³ × ℝ³ => F q.1 * (G q.2 * F (q.1 - q.2))) :=
    (hF.comp measurable_fst).mul ((hG.comp measurable_snd).mul (hF.comp hsubm))
  calc (∫⁻ x : ℝ³, F x * (∫⁻ z : ℝ³, G z * F (x - z)))
      = ∫⁻ x : ℝ³, ∫⁻ z : ℝ³, F x * (G z * F (x - z)) := by
        apply lintegral_congr
        intro x
        exact (lintegral_const_mul (μ := (volume : Measure ℝ³)) (F x) (hfib x)).symm
    _ = ∫⁻ q : ℝ³ × ℝ³, F q.1 * (G q.2 * F (q.1 - q.2)) :=
        (lintegral_prod _ hgm.aemeasurable).symm
    _ = ∫⁻ z : ℝ³, ∫⁻ x : ℝ³, F x * (G z * F (x - z)) :=
        lintegral_prod_symm _ hgm.aemeasurable
    _ = ∫⁻ z : ℝ³, G z * (∫⁻ x : ℝ³, F x * F (x - z)) := by
        apply lintegral_congr
        intro z
        rw [show (fun x : ℝ³ => F x * (G z * F (x - z)))
              = (fun x : ℝ³ => G z * (F x * F (x - z))) from by
            funext x; rw [mul_left_comm]]
        have hstep : (∫⁻ x : ℝ³, G z * (F x * F (x - z)))
            = G z * (∫⁻ x : ℝ³, F x * F (x - z)) :=
          lintegral_const_mul (μ := (volume : Measure ℝ³)) (G z)
            (hF.mul (hF.comp ((measurable_id.sub measurable_const) :
              Measurable (fun x : ℝ³ => x - z))))
        rw [hstep]

theorem lintegral_wPairC_le {h : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hh : MeasureTheory.Integrable h (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∫⁻ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.wPairC ℓ h p.1 p.2‖ₑ
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))))
      ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), |h z|) := by
  -- replace `h` by a measurable representative `q`
  let q : ℝ³ → ℝ := AEStronglyMeasurable.mk h hh.aestronglyMeasurable
  have hqm : Measurable q := hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hqae : h =ᵐ[(volume : Measure ℝ³)] q := hh.aestronglyMeasurable.ae_eq_mk
  have hqint : Integrable q (volume : Measure ℝ³) := hh.congr hqae
  set F : ℝ³ → ENNReal := fun x => ENNReal.ofReal (Submission.BoseGases.chiScale ℓ x) with hFdef
  set G : ℝ³ → ENNReal := fun z => ENNReal.ofReal |Submission.BoseGases.wScaled ℓ q z| with hGdef
  have hFm : Measurable F := by
    rw [hFdef]
    exact ENNReal.measurable_ofReal.comp (Submission.BoseGases.chiScale_continuous ℓ).measurable
  have hwm : Measurable (fun z : ℝ³ => Submission.BoseGases.wScaled ℓ q z) := by
    show Measurable (fun z : ℝ³ => q z / Submission.BoseGases.convScale ℓ z)
    exact hqm.div (Submission.BoseGases.convScale_continuous ℓ).measurable
  have hGm : Measurable G := by
    rw [hGdef]
    exact ENNReal.measurable_ofReal.comp hwm.abs
  -- the inner fibre: `∫⁻ x, χ_ℓ x · χ_ℓ (x−z) = ofReal (ℓ³ (χ⋆χ)_ℓ z)`
  have hfibre : ∀ z : ℝ³, (∫⁻ x : ℝ³, F x * F (x - z))
      = ENNReal.ofReal (ℓ ^ 3 * Submission.BoseGases.convScale ℓ z) := by
    intro z
    have hcont : Continuous (fun x : ℝ³ =>
        Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ (x - z)) :=
      (Submission.BoseGases.chiScale_continuous ℓ).mul
        ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_id.sub continuous_const))
    have hχint : Integrable (fun x : ℝ³ => Submission.BoseGases.chiScale ℓ x) (volume : Measure ℝ³) :=
      Continuous.integrable_of_hasCompactSupport (Submission.BoseGases.chiScale_continuous ℓ)
        (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ))
    have hdom : Integrable (fun x : ℝ³ => (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
        * Submission.BoseGases.chiScale ℓ (x - z)) (volume : Measure ℝ³) :=
      (hχint.comp_sub_right z).const_mul _
    have haesm : AEStronglyMeasurable (fun x : ℝ³ => Submission.BoseGases.chiScale ℓ x
        * Submission.BoseGases.chiScale ℓ (x - z)) (volume : Measure ℝ³) :=
      (hcont.aestronglyMeasurable)
    have hle : ∀ x : ℝ³, ‖Submission.BoseGases.chiScale ℓ x
        * Submission.BoseGases.chiScale ℓ (x - z)‖ ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
        * Submission.BoseGases.chiScale ℓ (x - z) := by
      intro x
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ (x - z))]
      exact mul_le_mul_of_nonneg_right (Submission.BoseGases.abs_chiScale_le ℓ x)
        (Submission.BoseGases.chiScale_nonneg ℓ (x - z))
    have hint : Integrable (fun x : ℝ³ =>
        Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ (x - z))
        (volume : Measure ℝ³) :=
      Integrable.mono' hdom haesm (Filter.Eventually.of_forall hle)
    have hnn : 0 ≤ᵐ[(volume : Measure ℝ³)] (fun x : ℝ³ =>
        Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ (x - z)) :=
      Filter.Eventually.of_forall (fun x => mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
        (Submission.BoseGases.chiScale_nonneg ℓ (x - z)))
    have key := ofReal_integral_eq_lintegral_ofReal hint hnn
    rw [Submission.BoseGases.integral_pair_scale hℓ z] at key
    have hcongr : (∫⁻ x : ℝ³, F x * F (x - z))
        = ∫⁻ x : ℝ³, ENNReal.ofReal (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiScale ℓ (x - z)) := by
      apply lintegral_congr
      intro x
      simp only [hFdef]
      exact (ENNReal.ofReal_mul (Submission.BoseGases.chiScale_nonneg ℓ x)).symm
    rw [hcongr]
    exact key.symm
  -- the pointwise cancellation
  have hbound : ∀ z : ℝ³, G z * ENNReal.ofReal (ℓ ^ 3 * Submission.BoseGases.convScale ℓ z)
      ≤ ENNReal.ofReal (ℓ ^ 3 * |q z|) := by
    intro z
    have hC : 0 ≤ Submission.BoseGases.convScale ℓ z := Submission.BoseGases.convScale_nonneg ℓ z
    have hreal : |Submission.BoseGases.wScaled ℓ q z|
          * (ℓ ^ 3 * Submission.BoseGases.convScale ℓ z) ≤ ℓ ^ 3 * |q z| := by
      by_cases hC0 : Submission.BoseGases.convScale ℓ z = 0
      · rw [hC0, mul_zero, mul_zero]
        exact mul_nonneg (pow_nonneg (le_of_lt hℓ) 3) (abs_nonneg _)
      · have hpos : 0 < Submission.BoseGases.convScale ℓ z := lt_of_le_of_ne hC (Ne.symm hC0)
        have heq : |Submission.BoseGases.wScaled ℓ q z|
            * (ℓ ^ 3 * Submission.BoseGases.convScale ℓ z) = ℓ ^ 3 * |q z| := by
          simp only [Submission.BoseGases.wScaled]
          rw [abs_div, abs_of_pos hpos]
          field_simp
        exact le_of_eq heq
    calc G z * ENNReal.ofReal (ℓ ^ 3 * Submission.BoseGases.convScale ℓ z)
        = ENNReal.ofReal (|Submission.BoseGases.wScaled ℓ q z|
            * (ℓ ^ 3 * Submission.BoseGases.convScale ℓ z)) := by
          rw [hGdef]
          exact (ENNReal.ofReal_mul (abs_nonneg _)).symm
      _ ≤ ENNReal.ofReal (ℓ ^ 3 * |q z|) := ENNReal.ofReal_le_ofReal hreal
  -- the `h`-integrand is a.e. the `q`-integrand
  have hLHS : (∫⁻ p : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC ℓ h p.1 p.2‖ₑ
        ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
      = (∫⁻ p : ℝ³ × ℝ³, F p.1 * G (p.1 - p.2) * F p.2
        ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) := by
    apply lintegral_congr_ae
    filter_upwards [qmp_sub_prod_vol.ae hqae] with p hp
    rw [wPairC_enorm_eq ℓ h p.1 p.2]
    simp only [hFdef, hGdef]
    rw [show Submission.BoseGases.wScaled ℓ h (p.1 - p.2)
          = Submission.BoseGases.wScaled ℓ q (p.1 - p.2) from by
        simp only [Submission.BoseGases.wScaled]; rw [hp]]
  have hqabs_int : Integrable (fun z : ℝ³ => ℓ ^ 3 * |q z|) (volume : Measure ℝ³) :=
    hqint.abs.const_mul (ℓ ^ 3)
  have hqabs_nn : 0 ≤ᵐ[(volume : Measure ℝ³)] (fun z : ℝ³ => ℓ ^ 3 * |q z|) :=
    Filter.Eventually.of_forall (fun z => mul_nonneg (pow_nonneg (le_of_lt hℓ) 3) (abs_nonneg _))
  have hqae_abs : (fun z : ℝ³ => |q z|) =ᵐ[(volume : Measure ℝ³)] (fun z : ℝ³ => |h z|) := by
    filter_upwards [hqae] with z hz
    rw [← hz]
  calc (∫⁻ p : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC ℓ h p.1 p.2‖ₑ
        ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
      = (∫⁻ p : ℝ³ × ℝ³, F p.1 * G (p.1 - p.2) * F p.2
        ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) := hLHS
    _ = ∫⁻ z : ℝ³, G z * (∫⁻ x : ℝ³, F x * F (x - z)) := pair_lintegral_aux hFm hGm
    _ = ∫⁻ z : ℝ³, G z * ENNReal.ofReal (ℓ ^ 3 * Submission.BoseGases.convScale ℓ z) := by
        apply lintegral_congr
        intro z
        rw [hfibre z]
    _ ≤ ∫⁻ z : ℝ³, ENNReal.ofReal (ℓ ^ 3 * |q z|) := lintegral_mono hbound
    _ = ENNReal.ofReal (∫ z : ℝ³, ℓ ^ 3 * |q z|) :=
        (ofReal_integral_eq_lintegral_ofReal hqabs_int hqabs_nn).symm
    _ = ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |h z|) := by
        rw [integral_const_mul]
        congr 1
        congr 1
        exact integral_congr_ae hqae_abs

end Work.BoseFixB2.Pot
