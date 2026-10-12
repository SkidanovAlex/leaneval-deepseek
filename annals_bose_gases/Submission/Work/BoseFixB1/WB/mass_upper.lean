import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.mass_upper` — the localised one-body mass is bounded by `C·a·χ_{B(u)}`

FS's localisation of the one-body kernel gives the *per-box* mass bound

    `∬ w_{1,B(u)}(x,y) dx dy ≤ C · (a v) · ∫ χ_{B(u)}²`   (uniformly in `u`),

the sharp form of FS `eq:appw1sliding` (`w_{1,B(u)} ≈ 8πa·|B(u)|`) which the
window argument (`WB/Defs.lean`) consumes as `hmassU`.

The proof is: `wSmall1Pair` factors as `χ_{B(u)}(x)·(g₀(x−y)/den)·χ_{B(u)}(y)`
with `den ≥ 1/c` on the support of `g₀`, so pointwise
`|wSmall1Pair| ≤ c·χ_{B(u)}(x)·|g₀(x−y)|·χ_{B(u)}(y)`; the double integral of the
right side is `≤ (∫χ²)(∫|g₀|)` by the elementary convolution pairing bound
(`iterated_abs_mul_le_aux`, proved below by Tonelli + the substitution
`y ↦ x − y` + the arithmetic-geometric mean), and `∫|g₀| = 8πa v`.
-/

namespace Work.BoseFixB1.WB

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`ofReal` of an integral is at most the integral of the `ofReal`s**, for an a.e.
nonnegative real function.  No integrability hypothesis is needed: if `f` is not integrable
the Bochner integral is `0` (`integral_undef`) and the inequality is trivial; if it is, the
identity `integral_eq_lintegral_of_nonneg_ae` together with `ofReal_toReal_le` gives it. -/
private lemma ofReal_integral_le_lintegral_of_nonneg {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases h : MeasureTheory.Integrable f μ
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hf h.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact bot_le

/-- **The convolution pairing bound.**  For a nonnegative *continuous* compactly supported
`χ` and an integrable `f`,

    `∫∫ χ x · |f (x−y)| · χ y  ≤  (∫χ²)·(∫|f|)`,

together with the two integrability statements used by the assembly.  The bound is proved by
substituting `y ↦ x − y` in the inner integral (`MeasurePreserving.lintegral_comp`), Tonelli
(`lintegral_prod`, `lintegral_prod_symm`) and, in the resulting fibre, the arithmetic-geometric
mean `χ x · χ (x−z) ≤ (χ x² + χ (x−z)²)/2` whose `x`-integral is `∫χ²` by translation
invariance of Lebesgue measure. -/
private theorem iterated_abs_mul_le_aux {χ f : ℝ³ → ℝ}
    (hχ0 : ∀ x, 0 ≤ χ x) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hf : MeasureTheory.Integrable f) :
    (∀ x, MeasureTheory.Integrable (fun y => χ x * |f (x - y)| * χ y)) ∧
    MeasureTheory.Integrable (fun x => ∫ y, χ x * |f (x - y)| * χ y) ∧
    (∫ x, ∫ y, χ x * |f (x - y)| * χ y) ≤ (∫ x, χ x ^ 2) * (∫ z, |f z|) := by
  obtain ⟨B, hB⟩ := hχc.bounded_above_of_compact_support hχs
  have hχB : ∀ x, χ x ≤ B := fun x => by
    have h := hB x
    rwa [Real.norm_eq_abs, abs_of_nonneg (hχ0 x)] at h
  have hB0 : 0 ≤ B := le_trans (hχ0 0) (hχB 0)
  have hχint : MeasureTheory.Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  have hχ2int : MeasureTheory.Integrable (fun x => χ x ^ 2) := by
    refine MeasureTheory.Integrable.mono' (hχint.const_mul B) (hχc.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hχ0 x) 2)]
    nlinarith [hχ0 x, hχB x]
  have hfabs : MeasureTheory.Integrable (fun z => |f z|) := hf.abs
  have hqmp : Measure.QuasiMeasurePreserving (fun p : ℝ³ × ℝ³ => p.1 - p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) (volume : Measure ℝ³) :=
    quasiMeasurePreserving_sub_of_right_invariant _ _
  -- ## conjunct 1: the `y`-fibres are integrable, for *every* `x`
  have hInner : ∀ x, MeasureTheory.Integrable (fun y => χ x * |f (x - y)| * χ y) := by
    intro x
    have h1 : MeasureTheory.Integrable (fun y : ℝ³ => |f (x - y)|) := hfabs.comp_sub_left x
    refine MeasureTheory.Integrable.mono' (h1.const_mul (χ x * B)) ?_ ?_
    · exact (h1.aestronglyMeasurable.const_mul (χ x)).mul hχc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (hχ0 x) (abs_nonneg _)) (hχ0 y))]
      calc χ x * |f (x - y)| * χ y ≤ χ x * |f (x - y)| * B :=
            mul_le_mul_of_nonneg_left (hχB y) (mul_nonneg (hχ0 x) (abs_nonneg _))
        _ = χ x * B * |f (x - y)| := by ring
  -- ## conjunct 2: the outer function is integrable
  have hOuter : MeasureTheory.Integrable (fun x => ∫ y, χ x * |f (x - y)| * χ y) := by
    have hGae : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ => χ p.1 * |f (p.1 - p.2)| * χ p.2)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      ((hχc.comp continuous_fst).aestronglyMeasurable.mul
        (hfabs.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp)).mul
        (hχc.comp continuous_snd).aestronglyMeasurable
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ³ => ∫ y, χ x * |f (x - y)| * χ y) (volume : Measure ℝ³) :=
      hGae.integral_prod_right'
    refine MeasureTheory.Integrable.mono' (hχint.const_mul (B * ∫ z, |f z|)) haesm ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 : |∫ y : ℝ³, χ x * |f (x - y)| * χ y| ≤
        ∫ y : ℝ³, χ x * |f (x - y)| * χ y := by
      calc |∫ y : ℝ³, χ x * |f (x - y)| * χ y|
          ≤ ∫ y : ℝ³, ‖χ x * |f (x - y)| * χ y‖ := by
            simpa only [Real.norm_eq_abs] using
              MeasureTheory.norm_integral_le_integral_norm
                (fun y : ℝ³ => χ x * |f (x - y)| * χ y)
        _ = ∫ y : ℝ³, χ x * |f (x - y)| * χ y := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            rw [Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (mul_nonneg (hχ0 x) (abs_nonneg _)) (hχ0 y))]
    have h2 : (∫ y : ℝ³, χ x * |f (x - y)| * χ y) =
        χ x * ∫ y : ℝ³, |f (x - y)| * χ y := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    have h3 : (∫ y : ℝ³, |f (x - y)| * χ y) ≤ B * ∫ y : ℝ³, |f (x - y)| := by
      refine (MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun y => mul_nonneg (abs_nonneg _) (hχ0 y)))
        ((hfabs.comp_sub_left x).const_mul B)
        (Filter.Eventually.of_forall (fun y => ?_))).trans (le_of_eq ?_)
      · show |f (x - y)| * χ y ≤ B * |f (x - y)|
        rw [mul_comm B]
        exact mul_le_mul_of_nonneg_left (hχB y) (abs_nonneg _)
      · rw [MeasureTheory.integral_const_mul]
    have h4 : (∫ y : ℝ³, |f (x - y)|) = ∫ z : ℝ³, |f z| :=
      Submission.BoseGases.integral_comp_sub_left (fun z : ℝ³ => |f z|) x
    rw [Real.norm_eq_abs]
    calc |∫ y : ℝ³, χ x * |f (x - y)| * χ y| ≤
          ∫ y : ℝ³, χ x * |f (x - y)| * χ y := h1
      _ = χ x * ∫ y : ℝ³, |f (x - y)| * χ y := h2
      _ ≤ χ x * (B * ∫ y : ℝ³, |f (x - y)|) := mul_le_mul_of_nonneg_left h3 (hχ0 x)
      _ = χ x * (B * ∫ z : ℝ³, |f z|) := by rw [h4]
      _ = (B * ∫ z : ℝ³, |f z|) * χ x := by ring
  -- ## conjunct 3: the double-integral bound
  have hConj3 : (∫ x, ∫ y, χ x * |f (x - y)| * χ y) ≤ (∫ x, χ x ^ 2) * (∫ z, |f z|) := by
    -- replace `f` by a genuine measurable representative
    obtain ⟨q, hqm, hqae⟩ : ∃ q : ℝ³ → ℝ, Measurable q ∧ f =ᵐ[volume] q :=
      ⟨hf.aestronglyMeasurable.mk f, hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
        hf.aestronglyMeasurable.ae_eq_mk⟩
    have hqint : MeasureTheory.Integrable q := hf.congr hqae
    -- Step A: `ofReal` of the Bochner double integral is at most the
    -- iterated `lintegral` of the `ofReal`s
    have hstepA : ENNReal.ofReal (∫ x, ∫ y, χ x * |f (x - y)| * χ y) ≤
        ∫⁻ x, ∫⁻ y, ENNReal.ofReal (χ x * |f (x - y)| * χ y) := by
      refine (ofReal_integral_le_lintegral_of_nonneg (μ := (volume : Measure ℝ³))
        (f := fun x => ∫ y, χ x * |f (x - y)| * χ y)
        (Filter.Eventually.of_forall (fun x => MeasureTheory.integral_nonneg
          (fun y => mul_nonneg (mul_nonneg (hχ0 x) (abs_nonneg _)) (hχ0 y))))).trans ?_
      refine MeasureTheory.lintegral_mono (fun x => ?_)
      exact ofReal_integral_le_lintegral_of_nonneg (μ := (volume : Measure ℝ³))
        (Filter.Eventually.of_forall (fun y =>
          mul_nonneg (mul_nonneg (hχ0 x) (abs_nonneg _)) (hχ0 y)))
    -- Step B: replace `f` by `q` inside the lintegral
    have hshift_ae : ∀ᵐ p : ℝ³ × ℝ³ ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)),
        |f (p.1 - p.2)| = |q (p.1 - p.2)| := by
      filter_upwards [hqmp.ae hqae] with p hp
      rw [hp]
    have hstepB : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (χ x * |f (x - y)| * χ y)) =
        ∫⁻ x, ∫⁻ y, ENNReal.ofReal (χ x * |q (x - y)| * χ y) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hshift_ae] with x hx
      exact MeasureTheory.lintegral_congr_ae (hx.mono (fun y hy => by
        show ENNReal.ofReal (χ x * |f (x - y)| * χ y) =
          ENNReal.ofReal (χ x * |q (x - y)| * χ y)
        rw [hy]))
    -- Step C: the ENNReal computation with the measurable `q`
    have hstepC : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (χ x * |q (x - y)| * χ y)) ≤
        ENNReal.ofReal ((∫ x, χ x ^ 2) * (∫ z, |f z|)) := by
      set F : ℝ³ → ℝ≥0∞ := fun x => ENNReal.ofReal (χ x) with hFdef
      set G : ℝ³ → ℝ≥0∞ := fun z => ENNReal.ofReal |q z| with hGdef
      have hFm : Measurable F := ENNReal.measurable_ofReal.comp hχc.measurable
      have hGm : Measurable G := ENNReal.measurable_ofReal.comp hqm.abs
      have hsubm : Measurable (fun p : ℝ³ × ℝ³ => p.1 - p.2) :=
        measurable_fst.sub measurable_snd
      -- the various AEMeasurability facts
      have hsub_left_meas : ∀ x : ℝ³, Measurable (fun y : ℝ³ => G (x - y) * F y) := fun x =>
        (hGm.comp (measurable_const.sub measurable_id)).mul hFm
      have hsub_right_meas : ∀ x : ℝ³, Measurable (fun z : ℝ³ => G z * F (x - z)) := fun x =>
        hGm.mul (hFm.comp (measurable_const.sub measurable_id))
      -- Step C0: expand the `ofReal` products
      have hC0 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (χ x * |q (x - y)| * χ y)) =
          ∫⁻ x, ∫⁻ y, F x * G (x - y) * F y := by
        refine MeasureTheory.lintegral_congr (fun x => ?_)
        refine MeasureTheory.lintegral_congr (fun y => ?_)
        simp only [hFdef, hGdef]
        rw [ENNReal.ofReal_mul (mul_nonneg (hχ0 x) (abs_nonneg _)),
          ENNReal.ofReal_mul (hχ0 x)]
      -- Step C1: pull the constant `F x` out of the `y`-integral
      have hC1 : (∫⁻ x, ∫⁻ y, F x * G (x - y) * F y) =
          ∫⁻ x, F x * (∫⁻ y, G (x - y) * F y) := by
        refine MeasureTheory.lintegral_congr (fun x => ?_)
        rw [show (fun y : ℝ³ => F x * G (x - y) * F y)
            = (fun y : ℝ³ => F x * (G (x - y) * F y)) from by
          funext y; rw [mul_assoc]]
        exact MeasureTheory.lintegral_const_mul'' (F x) ((hsub_left_meas x).aemeasurable)
      -- Step C2: substitute `y ↦ x − y` in the fibre
      have hC2 : (∫⁻ x, F x * (∫⁻ y, G (x - y) * F y)) =
          ∫⁻ x, F x * (∫⁻ z, G z * F (x - z)) := by
        refine MeasureTheory.lintegral_congr (fun x => ?_)
        congr 1
        have h1 : (∫⁻ y : ℝ³, G (x - y) * F y) =
            ∫⁻ y : ℝ³, (fun z : ℝ³ => G z * F (x - z)) (x - y) := by
          refine MeasureTheory.lintegral_congr (fun y => ?_)
          show G (x - y) * F y = G (x - y) * F (x - (x - y))
          rw [show x - (x - y) = y by abel]
        rw [h1, (Measure.measurePreserving_sub_left (volume : Measure ℝ³) x).lintegral_comp
          (hsub_right_meas x)]
      -- Step C3: Tonelli (swap the `x`- and `z`-integrals)
      have hC3 : (∫⁻ x, F x * (∫⁻ z, G z * F (x - z))) =
          ∫⁻ z, G z * (∫⁻ x, F x * F (x - z)) := by
        have hJ : Measurable (fun p : ℝ³ × ℝ³ => F p.1 * (G p.2 * F (p.1 - p.2))) :=
          (hFm.comp measurable_fst).mul
            ((hGm.comp measurable_snd).mul (hFm.comp hsubm))
        calc (∫⁻ x, F x * (∫⁻ z, G z * F (x - z)))
            = ∫⁻ x, ∫⁻ z, F x * (G z * F (x - z)) := by
              refine MeasureTheory.lintegral_congr (fun x => ?_)
              exact (MeasureTheory.lintegral_const_mul'' (F x)
                ((hsub_right_meas x).aemeasurable)).symm
          _ = ∫⁻ p : ℝ³ × ℝ³, F p.1 * (G p.2 * F (p.1 - p.2)) :=
              (MeasureTheory.lintegral_prod _ hJ.aemeasurable).symm
          _ = ∫⁻ z, ∫⁻ x, F x * (G z * F (x - z)) :=
              MeasureTheory.lintegral_prod_symm _ hJ.aemeasurable
          _ = ∫⁻ z, G z * (∫⁻ x, F x * F (x - z)) := by
              refine MeasureTheory.lintegral_congr (fun z => ?_)
              rw [show (fun x : ℝ³ => F x * (G z * F (x - z)))
                  = (fun x : ℝ³ => G z * (F x * F (x - z))) from by
                funext x; rw [← mul_assoc, mul_comm (F x) (G z), mul_assoc]]
              exact MeasureTheory.lintegral_const_mul'' (G z)
                ((hFm.mul (hFm.comp (measurable_id.sub measurable_const))).aemeasurable)
      -- Step C4: the fibre bound `∫⁻ x, F x · F (x−z) ≤ ofReal (∫χ²)`
      have hC4 : ∀ z : ℝ³, (∫⁻ x, F x * F (x - z)) ≤ ENNReal.ofReal (∫ x, χ x ^ 2) := by
        intro z
        have hcont : Continuous (fun x : ℝ³ => χ x * χ (x - z)) :=
          hχc.mul (hχc.comp (continuous_id.sub continuous_const))
        have hint : MeasureTheory.Integrable (fun x : ℝ³ => χ x * χ (x - z)) := by
          refine MeasureTheory.Integrable.mono' ((hχint.comp_sub_right z).const_mul B) ?_ ?_
          · exact hcont.aestronglyMeasurable
          · refine Filter.Eventually.of_forall (fun x => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ0 x) (hχ0 _))]
            exact mul_le_mul_of_nonneg_right (hχB x) (hχ0 _)
        have hnn : 0 ≤ᵐ[(volume : Measure ℝ³)] (fun x : ℝ³ => χ x * χ (x - z)) :=
          Filter.Eventually.of_forall (fun x => mul_nonneg (hχ0 x) (hχ0 _))
        have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
        have hcongr : (∫⁻ x : ℝ³, F x * F (x - z)) =
            ∫⁻ x : ℝ³, ENNReal.ofReal (χ x * χ (x - z)) := by
          refine MeasureTheory.lintegral_congr (fun x => ?_)
          simp only [hFdef]
          exact (ENNReal.ofReal_mul (hχ0 x)).symm
        rw [hcongr, ← hbridge]
        refine ENNReal.ofReal_le_ofReal ?_
        calc (∫ x : ℝ³, χ x * χ (x - z))
            ≤ ∫ x : ℝ³, (χ x ^ 2 + χ (x - z) ^ 2) / 2 := by
              refine MeasureTheory.integral_mono hint
                ((hχ2int.add (hχ2int.comp_sub_right z)).div_const 2) (fun x => ?_)
              nlinarith [sq_nonneg (χ x - χ (x - z))]
          _ = (1 / 2) * (∫ x : ℝ³, χ x ^ 2 + χ (x - z) ^ 2) := by
              rw [← MeasureTheory.integral_const_mul]
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
              ring
          _ = (1 / 2) * ((∫ x : ℝ³, χ x ^ 2) + ∫ x : ℝ³, χ (x - z) ^ 2) := by
              rw [MeasureTheory.integral_add hχ2int (hχ2int.comp_sub_right z)]
          _ = (1 / 2) * ((∫ x : ℝ³, χ x ^ 2) + ∫ x : ℝ³, χ x ^ 2) := by
              rw [MeasureTheory.integral_sub_right_eq_self (fun x : ℝ³ => χ x ^ 2) z]
          _ = ∫ x : ℝ³, χ x ^ 2 := by ring
      -- Step C5: assemble
      have hq_abs : (∫ z : ℝ³, |q z|) = ∫ z : ℝ³, |f z| := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hqae] with z hz
        rw [hz]
      have hGint : (∫⁻ z : ℝ³, G z) = ENNReal.ofReal (∫ z : ℝ³, |q z|) := by
        rw [hGdef]
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hqint.abs
          (Filter.Eventually.of_forall (fun z => abs_nonneg _))).symm
      have hχ2nn : 0 ≤ ∫ x : ℝ³, χ x ^ 2 :=
        MeasureTheory.integral_nonneg (fun x => pow_nonneg (hχ0 x) 2)
      calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (χ x * |q (x - y)| * χ y))
          = ∫⁻ x, ∫⁻ y, F x * G (x - y) * F y := hC0
        _ = ∫⁻ x, F x * (∫⁻ y, G (x - y) * F y) := hC1
        _ = ∫⁻ x, F x * (∫⁻ z, G z * F (x - z)) := hC2
        _ = ∫⁻ z, G z * (∫⁻ x, F x * F (x - z)) := hC3
        _ ≤ ∫⁻ z, G z * ENNReal.ofReal (∫ x, χ x ^ 2) :=
            MeasureTheory.lintegral_mono (fun z =>
              mul_le_mul' le_rfl (hC4 z))
        _ = ENNReal.ofReal (∫ x, χ x ^ 2) * (∫⁻ z, G z) := by
            rw [show (fun z : ℝ³ => G z * ENNReal.ofReal (∫ x, χ x ^ 2))
                = (fun z : ℝ³ => ENNReal.ofReal (∫ x, χ x ^ 2) * G z) from by
              funext z; rw [mul_comm]]
            rw [MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (∫ x, χ x ^ 2))
              hGm.aemeasurable]
        _ = ENNReal.ofReal (∫ x, χ x ^ 2) * ENNReal.ofReal (∫ z, |q z|) := by rw [hGint]
        _ = ENNReal.ofReal ((∫ x, χ x ^ 2) * (∫ z, |q z|)) :=
            (ENNReal.ofReal_mul hχ2nn).symm
        _ = ENNReal.ofReal ((∫ x, χ x ^ 2) * (∫ z, |f z|)) := by rw [hq_abs]
    have hfin : ENNReal.ofReal (∫ x, ∫ y, χ x * |f (x - y)| * χ y) ≤
        ENNReal.ofReal ((∫ x, χ x ^ 2) * (∫ z, |f z|)) :=
      hstepA.trans (hstepB.le.trans hstepC)
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp hfin
    exact mul_nonneg (MeasureTheory.integral_nonneg (fun x => pow_nonneg (hχ0 x) 2))
      (MeasureTheory.integral_nonneg (fun z => abs_nonneg _))
  exact ⟨hInner, hOuter, hConj3⟩

theorem mass_upper {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ} {M : ℕ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ d : ℝ}, 0 < ℓ → 0 < d → R0 ≤ ℓ * d / 16 →
      R0 ≤ ℓ * Submission.BoseGases.chiR0 → ∀ u : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixB1.w1MassB h M ℓ d u
          ≤ C * _root_.BoseGases.a v * Work.SmallBoxSliding.chiMass M ℓ d u := by
  have hsCLpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  refine ⟨16 * Real.pi * (Work.SmallBoxSliding.smallConvLower M)⁻¹, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (inv_nonneg.mpr hsCLpos.le)
  intro ℓ d hℓ hd hR hRχ u
  obtain ⟨hInnerInt, hOuterInt, hBound⟩ :=
    iterated_abs_mul_le_aux
      (χ := fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x)
      (f := Submission.BoseGases.g0 v h)
      (fun x => Submission.BoseGases.chiSmallB_nonneg M ℓ d u x)
      (Submission.BoseGases.chiSmallB_continuous hM hℓ hd u)
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u)
      (Submission.BoseGases.g0_integrable hR0 hv_supp h)
  -- the pointwise domination constant
  set c : ℝ := 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  -- pointwise domination of the localised one-body kernel
  have hpt : ∀ x y : ℝ³, |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      c * (Submission.BoseGases.chiSmallB M ℓ d u x * |Submission.BoseGases.g0 v h (x - y)| *
        Submission.BoseGases.chiSmallB M ℓ d u y) := by
    intro x y
    have hb := Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le (v := v) (R0 := R0)
      hv_supp hR0 h hM hℓ hd hR hRχ u x y
    calc |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
            Submission.BoseGases.chiSmallB M ℓ d u x *
            |Submission.BoseGases.g0 v h (x - y)| *
            Submission.BoseGases.chiSmallB M ℓ d u y := hb
      _ = c * (Submission.BoseGases.chiSmallB M ℓ d u x *
            |Submission.BoseGases.g0 v h (x - y)| *
            Submission.BoseGases.chiSmallB M ℓ d u y) := by
          rw [hcdef]; ring
  -- the inner (in `y`) domination
  have hinner : ∀ x : ℝ³, (∫ y : ℝ³,
        |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|) ≤
      c * ∫ y : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x *
        |Submission.BoseGases.g0 v h (x - y)| *
        Submission.BoseGases.chiSmallB M ℓ d u y) := by
    intro x
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y => abs_nonneg _)) ((hInnerInt x).const_mul c)
      (Filter.Eventually.of_forall (fun y => hpt x y))
  -- the outer chain
  have hwdef : Work.BoseFixB1.w1MassB h M ℓ d u =
      ∫ x : ℝ³, ∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y := rfl
  have hmain : Work.BoseFixB1.w1MassB h M ℓ d u ≤
      c * (∫ x : ℝ³, ∫ y : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x *
        |Submission.BoseGases.g0 v h (x - y)| *
        Submission.BoseGases.chiSmallB M ℓ d u y)) := by
    refine le_trans (le_abs_self _) ?_
    calc |Work.BoseFixB1.w1MassB h M ℓ d u|
        = ‖∫ x : ℝ³,
            (∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)‖ := by
          rw [hwdef, Real.norm_eq_abs]
      _ ≤ ∫ x : ℝ³,
            ‖∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ³, c * ∫ y : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x *
            |Submission.BoseGases.g0 v h (x - y)| *
            Submission.BoseGases.chiSmallB M ℓ d u y) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun x => norm_nonneg _)) (hOuterInt.const_mul c)
            (Filter.Eventually.of_forall (fun x => ?_))
          calc ‖∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y‖
              = |∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y| :=
                Real.norm_eq_abs _
            _ ≤ ∫ y : ℝ³, |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| := by
                simpa only [Real.norm_eq_abs] using
                  MeasureTheory.norm_integral_le_integral_norm
                    (fun y : ℝ³ => Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
            _ ≤ c * ∫ y : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x *
                  |Submission.BoseGases.g0 v h (x - y)| *
                  Submission.BoseGases.chiSmallB M ℓ d u y) := hinner x
      _ = c * (∫ x : ℝ³, ∫ y : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x *
            |Submission.BoseGases.g0 v h (x - y)| *
            Submission.BoseGases.chiSmallB M ℓ d u y)) :=
          MeasureTheory.integral_const_mul c _
  -- assemble
  have hg0abs : (∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) = 8 * Real.pi * _root_.BoseGases.a v :=
    Submission.BoseGases.g0_abs_integral hR0 hv hvrad hv_supp h
  have hchi : (∫ x : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2) =
      Work.SmallBoxSliding.chiMass M ℓ d u :=
    (Work.SmallBoxSliding.chiMass_def M ℓ d u).symm
  calc Work.BoseFixB1.w1MassB h M ℓ d u
      ≤ c * (∫ x : ℝ³, ∫ y : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x *
            |Submission.BoseGases.g0 v h (x - y)| *
            Submission.BoseGases.chiSmallB M ℓ d u y)) := hmain
    _ ≤ c * ((∫ x : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2) *
          (∫ z : ℝ³, |Submission.BoseGases.g0 v h z|)) :=
        mul_le_mul_of_nonneg_left hBound hc0
    _ = (16 * Real.pi * (Work.SmallBoxSliding.smallConvLower M)⁻¹) *
          _root_.BoseGases.a v * Work.SmallBoxSliding.chiMass M ℓ d u := by
        rw [hcdef, hchi, hg0abs]; ring

end Work.BoseFixB1.WB
