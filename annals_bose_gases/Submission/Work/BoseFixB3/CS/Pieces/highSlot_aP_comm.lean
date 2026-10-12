import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.Pieces.lowMult_abs_le_of_box_bound
import Submission.Work.BoseFixB3.CS.Pieces.lowMult_eq_kernel_integral
import Submission.Work.BoseFixB3.CS.Pieces.measurable_lowMult_family
import Submission.Work.BoseFixB3.CS.Reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/CS/Pieces/highSlot_aP_comm`

`Work.BoseFixB3.CS.Pieces.highSlot_aP_comm`: the slot-`j` complementary multiplier
`(1 − f_L)_j` (`Work.BoseFixB3.highSlot`) commutes with the box-mean projection `P_i`
(`Submission.BoseGases.aP`) in a **different** slot `i ≠ j`.

After unfolding `highSlot`, `lowSlot` and `aP` the identity is a statement about the
low-momentum Fourier multiplier `lowMult fc κ ℓ`: writing `G y z := Ψ(x_{i↦y,j↦z})`, both
sides reduce to the **commutation of `lowMult` with the box mean over the other slot**,

`lowMult fc κ ℓ (fun z => (1/ℓ³)∫_{y∈Λ} G y z) x₀ = (1/ℓ³)∫_{y∈Λ} lowMult fc κ ℓ (fun z => G y z) x₀`

(`lowMult_box_mean_comm`).  This is Fubini: substituting the definitions of `kinFT` (the
`z`-integral) and of `lowMult` (the `p`-integral), both sides are the (real part of the)
integral of one single function `e^{i⟪p,x₀⟫} f(‖p‖/κ) e^{−i⟪p,z⟫} 1_Λ(z) G y z` over
`(p, z, y)` in two different orders.  The `κ > 0` hypothesis is essential: for `κ ≤ 0` the
symbol is `≡ 1`, the `p`-integral is not absolutely convergent and `lowMult` degenerates into
a "junk" operator that does **not** commute with the box mean (counterexample:
`Conv/pair_slot_transfer.lean`).

The multiplier is handled through its `(p,z)`-kernel form
(`CS/Pieces/lowMult_eq_kernel_integral`), which turns `lowMult ψ x₀` into
`(2π)⁻³ ∫_z (∫_p Re(e^{i⟪p,x₀⟫}f(‖p‖/κ)e^{−i⟪p,z⟫})) · 1_Λ(z)ψ(z) dz` — manifestly linear in
`1_Λ·ψ`, so that the Fubini above becomes a single swap of two *bounded* integrations over the
box `Λ(ℓ) × Λ(ℓ)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

/-! ## 0. Box-measure facts -/

lemma acube_isFiniteMeasure_restrict {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsFiniteMeasure (volume.restrict (Submission.BoseGases.acube ℓ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩

/-! ## 1. The `(p,z)`-kernel of the low-momentum multiplier -/

/-- The `(p,z)`-kernel of `lowMult` at the base point `x`:
`K(z) = ∫_p Re(e^{i⟪p,x⟫} f(‖p‖/κ) e^{−i⟪p,z⟫})`. -/
def lowKernel (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (x : E3) (z : E3) : ℝ :=
  ∫ p : E3, (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re

lemma continuous_lowKernelIntegrand (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (x z : E3) :
    Continuous (fun p : E3 => (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re) := by
  have hf : Continuous (fun p : E3 => (fc.f (‖p‖ / κ) : ℝ)) :=
    fc.smooth.continuous.comp (continuous_norm.div_const κ)
  have h1 : Continuous (fun p : E3 => Complex.exp (Complex.I * (inner ℝ p x : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_inner.comp
        (continuous_id.prodMk continuous_const))))
  have h2 : Continuous (fun p : E3 => ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hf
  have h3 : Continuous (fun p : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) :=
    Complex.continuous_exp.comp ((continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_inner.comp
        (continuous_id.prodMk continuous_const)))).neg)
  exact Complex.continuous_re.comp ((h1.mul h2).mul h3)

lemma measurable_lowKernel (fc : Work.BoseBoxFix.LowCut) (κ : ℝ) (x : E3) :
    Measurable (lowKernel fc κ x) := by
  have hcont : Continuous (fun q : E3 × E3 => (Complex.exp (Complex.I * (inner ℝ q.2 x : ℂ)) *
      ((fc.f (‖q.2‖ / κ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ q.2 q.1 : ℂ)))).re) := by
    have hf : Continuous (fun p : E3 => (fc.f (‖p‖ / κ) : ℝ)) :=
      fc.smooth.continuous.comp (continuous_norm.div_const κ)
    have h1 : Continuous (fun q : E3 × E3 => Complex.exp (Complex.I * (inner ℝ q.2 x : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_inner.comp
          (continuous_snd.prodMk continuous_const))))
    have h2 : Continuous (fun q : E3 × E3 => ((fc.f (‖q.2‖ / κ) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hf.comp continuous_snd)
    have h3 : Continuous (fun q : E3 × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ q.2 q.1 : ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_inner.comp
          (continuous_snd.prodMk continuous_fst)))).neg)
    exact Complex.continuous_re.comp ((h1.mul h2).mul h3)
  refine (StronglyMeasurable.integral_prod_right (ν := volume)
    (f := fun z p : E3 => (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re) ?_).measurable
  exact hcont.measurable.stronglyMeasurable

/-- The cut-off symbol is `L¹` for `κ > 0` (it is compactly supported). -/
lemma integrable_symbol (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun p : E3 => |fc.f (‖p‖ / κ)|) volume :=
  Continuous.integrable_of_hasCompactSupport
    ((fc.smooth.continuous.comp (continuous_norm.div_const κ)).abs)
    ((Work.BoseFixB3.HighMass.lowcut_symbol_hasCompactSupport (fc := fc) (κ := κ) hκ).comp_left
      (g := fun r : ℝ => |r|) (by simp))

/-- The kernel is bounded by the `L¹`-norm of the symbol. -/
lemma abs_lowKernel_le (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (x z : E3) :
    |lowKernel fc κ x z| ≤ ∫ p : E3, |fc.f (‖p‖ / κ)| := by
  have hint : Integrable (fun p : E3 => |fc.f (‖p‖ / κ)|) volume := integrable_symbol fc hκ
  have hpt : ∀ p : E3, ‖(Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re‖ ≤ |fc.f (‖p‖ / κ)| := by
    intro p
    change |(Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re| ≤ |fc.f (‖p‖ / κ)|
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, norm_mul]
    rw [show ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ))‖ = 1 from by
          rw [show Complex.I * (inner ℝ p x : ℂ) = (inner ℝ p x : ℂ) * Complex.I from
              mul_comm _ _, Complex.norm_exp_ofReal_mul_I],
        show ‖((fc.f (‖p‖ / κ) : ℝ) : ℂ)‖ = |fc.f (‖p‖ / κ)| from RCLike.norm_ofReal _,
        show ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 from by
          rw [show -(Complex.I * (inner ℝ p z : ℂ)) =
                ((-(inner ℝ p z) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]]
    exact le_of_eq (by ring)
  have hFint : Integrable (fun p : E3 => (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re) volume :=
    Integrable.mono' hint (continuous_lowKernelIntegrand fc κ x z).aestronglyMeasurable
      (Eventually.of_forall hpt)
  rw [lowKernel]
  calc |∫ p : E3, (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re|
      = ‖∫ p : E3, (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
          ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ p : E3, ‖(Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
          ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).re‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p : E3, |fc.f (‖p‖ / κ)| := by
        refine integral_mono hFint.norm hint (fun p => ?_)
        simpa [Real.norm_eq_abs] using hpt p

/-! ## 3. Fubini: the low-momentum multiplier commutes with the box mean -/

/-- **The box-mean commutation of the low-momentum multiplier.**  For `κ > 0` (so that the
symbol is compactly supported and the multiplier is an honest absolutely convergent
`p`-integral) the multiplier of the box mean is the box mean of the multipliers. -/
theorem lowMult_box_mean_comm {fc : Work.BoseBoxFix.LowCut} {κ ℓ M : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (hM : 0 ≤ M) {G : E3 → E3 → ℝ} (hG : Continuous (Function.uncurry G))
    (hGb : ∀ y ∈ Submission.BoseGases.acube ℓ, ∀ z ∈ Submission.BoseGases.acube ℓ, |G y z| ≤ M)
    (x₀ : E3) :
    Work.BoseBoxFix.lowMult fc κ ℓ
        (fun z => (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, G y z) x₀
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
          Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) x₀ := by
  classical
  have hbox : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  haveI : IsFiniteMeasure (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    acube_isFiniteMeasure_restrict hℓ
  have hGc : Continuous (fun q : E3 × E3 => G q.2 q.1) :=
    hG.comp (continuous_snd.prodMk continuous_fst)
  -- the mean and its bound
  set Φ : E3 → ℝ := fun z => (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, G y z with hΦ
  have hΦb : ∀ z ∈ Submission.BoseGases.acube ℓ, |Φ z| ≤ M := by
    intro z hz
    have hGi : Integrable (fun y : E3 => G y z)
        (volume.restrict (Submission.BoseGases.acube ℓ)) := by
      refine Integrable.mono' (integrable_const M)
        ((hG.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem hbox] with y hy
      rw [Real.norm_eq_abs]
      exact hGb y hy z hz
    have h1 : |∫ y in Submission.BoseGases.acube ℓ, G y z| ≤ ℓ ^ 3 * M := by
      calc |∫ y in Submission.BoseGases.acube ℓ, G y z|
          = ‖∫ y in Submission.BoseGases.acube ℓ, G y z‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ y in Submission.BoseGases.acube ℓ, ‖G y z‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ y in Submission.BoseGases.acube ℓ, M := by
            refine integral_mono_ae hGi.norm (integrable_const M) ?_
            filter_upwards [ae_restrict_mem hbox] with y hy
            rw [Real.norm_eq_abs]
            exact hGb y hy z hz
        _ = ℓ ^ 3 * M := by
            rw [MeasureTheory.setIntegral_const, Measure.real_def,
              Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity),
              smul_eq_mul]
    have h4 : (1 / ℓ ^ 3) * |∫ y in Submission.BoseGases.acube ℓ, G y z| ≤
        (1 / ℓ ^ 3) * (ℓ ^ 3 * M) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 / ℓ ^ 3) * (ℓ ^ 3 * M) = M := by field_simp
    simp only [hΦ]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ℓ ^ 3)]
    linarith
  -- measurability of the mean
  have hΦm : AEStronglyMeasurable Φ volume := by
    have hΦs : StronglyMeasurable
        (fun z : E3 => ∫ y, G y z ∂(volume.restrict (Submission.BoseGases.acube ℓ))) :=
      StronglyMeasurable.integral_prod_right (ν := volume.restrict (Submission.BoseGases.acube ℓ))
        (f := fun z y : E3 => G y z) (hGc.measurable.stronglyMeasurable)
    rw [hΦ]
    exact (hΦs.const_mul (1 / ℓ ^ 3)).aestronglyMeasurable
  -- the kernel form of the two sides
  have hRΦ : Work.BoseBoxFix.lowMult fc κ ℓ Φ x₀
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ z : E3, lowKernel fc κ x₀ z *
          ((Submission.BoseGases.acube ℓ).indicator Φ z) :=
    lowMult_eq_kernel_integral (fc := fc) (C := M) hκ hℓ hΦm hΦb hM x₀
  have hRfib : ∀ y ∈ Submission.BoseGases.acube ℓ,
      Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) x₀
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ z : E3, lowKernel fc κ x₀ z *
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z) := by
    intro y hy
    refine lowMult_eq_kernel_integral (fc := fc) (C := M) hκ hℓ ?_ ?_ hM x₀
    · exact ((hG.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
    · intro z hz
      exact hGb y hy z hz
  -- the pointwise indicator identity
  have hind : ∀ z : E3, ((Submission.BoseGases.acube ℓ).indicator Φ z)
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z) := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz]
      simp only [hΦ]
      rw [show (∫ y in Submission.BoseGases.acube ℓ, G y z)
            = ∫ y in Submission.BoseGases.acube ℓ,
                ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z) from
          integral_congr_ae (Eventually.of_forall (fun y => by
            show G y z = (Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z
            rw [Set.indicator_of_mem hz]))]
    · rw [Set.indicator_of_notMem hz]
      symm
      rw [show (fun y : E3 => (Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)
            = fun _ : E3 => (0 : ℝ) from
          funext (fun y => Set.indicator_of_notMem hz _)]
      simp
  -- integrability of the `(z,y)` joint integrand
  have hInt : Integrable (fun q : E3 × E3 => lowKernel fc κ x₀ q.1 *
      ((Submission.BoseGases.acube ℓ).indicator (fun z => G q.2 z) q.1))
      (volume.prod (volume.restrict (Submission.BoseGases.acube ℓ))) := by
    have hKbd : ∀ z : E3, |lowKernel fc κ x₀ z| ≤ ∫ p : E3, |fc.f (‖p‖ / κ)| :=
      fun z => abs_lowKernel_le fc hκ x₀ z
    have hind1 : Integrable
        (fun z : E3 => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) z) volume :=
      (MeasureTheory.integrableOn_const (μ := volume) (s := Submission.BoseGases.acube ℓ)
        (C := (1 : ℝ)) (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le))).integrable_indicator
        hbox
    have hmaj : Integrable (fun q : E3 × E3 =>
        (∫ p : E3, |fc.f (‖p‖ / κ)|) * M *
          (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) q.1)
        (volume.prod (volume.restrict (Submission.BoseGases.acube ℓ))) := by
      refine ((hind1.const_mul ((∫ p : E3, |fc.f (‖p‖ / κ)|) * M)).mul_prod
        (MeasureTheory.integrableOn_const (μ := volume) (s := Submission.BoseGases.acube ℓ)
          (C := (1 : ℝ)) (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)))).congr ?_
      filter_upwards with q
      ring
    have hae2 : ∀ᵐ q : E3 × E3 ∂(volume.prod (volume.restrict (Submission.BoseGases.acube ℓ))),
        q.2 ∈ Submission.BoseGases.acube ℓ := by
      rw [ae_iff]
      have hset : {q : E3 × E3 | ¬ q.2 ∈ Submission.BoseGases.acube ℓ}
          = Set.univ ×ˢ (Submission.BoseGases.acube ℓ)ᶜ := by
        ext q
        simp
      rw [hset, Measure.prod_prod, Measure.restrict_apply hbox.compl, Set.compl_inter_self,
        measure_empty, mul_zero]
    have hmeas : Measurable (fun q : E3 × E3 =>
        (Submission.BoseGases.acube ℓ).indicator (fun z => G q.2 z) q.1) := by
      rw [show (fun q : E3 × E3 =>
            (Submission.BoseGases.acube ℓ).indicator (fun z => G q.2 z) q.1)
          = (Submission.BoseGases.acube ℓ ×ˢ Set.univ).indicator (fun q => G q.2 q.1) from by
            funext q
            by_cases hq : q.1 ∈ Submission.BoseGases.acube ℓ <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, hq, Set.mem_prod]]
      exact Measurable.indicator hGc.measurable (hbox.prod MeasurableSet.univ)
    refine Integrable.mono' hmaj
      (((measurable_lowKernel fc κ x₀).comp measurable_fst).mul hmeas).aestronglyMeasurable ?_
    filter_upwards [hae2] with q hq
    rw [norm_mul]
    by_cases hq1 : q.1 ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hq1]
      calc ‖lowKernel fc κ x₀ q.1‖ * ‖G q.2 q.1‖
          ≤ (∫ p : E3, |fc.f (‖p‖ / κ)|) * M := by
            refine mul_le_mul (hKbd q.1) ?_ (norm_nonneg _)
              (integral_nonneg fun p => abs_nonneg _)
            rw [Real.norm_eq_abs]
            exact hGb q.2 hq q.1 hq1
        _ = (∫ p : E3, |fc.f (‖p‖ / κ)|) * M *
              (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) q.1 := by
            rw [Set.indicator_of_mem hq1, mul_one]
    · rw [Set.indicator_of_notMem hq1, norm_zero, Set.indicator_of_notMem hq1]
      simp
  -- the main computation
  have hstep1 : ∫ z : E3, lowKernel fc κ x₀ z * ((Submission.BoseGases.acube ℓ).indicator Φ z)
      = ∫ z : E3, lowKernel fc κ x₀ z * ((1 / ℓ ^ 3) *
          ∫ y in Submission.BoseGases.acube ℓ,
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)) := by
    refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
    show lowKernel fc κ x₀ z * ((Submission.BoseGases.acube ℓ).indicator Φ z)
        = lowKernel fc κ x₀ z * ((1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z))
    rw [hind z]
  have hstep2 : ∫ z : E3, lowKernel fc κ x₀ z * ((1 / ℓ ^ 3) *
        ∫ y in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z))
      = ∫ z : E3, ∫ y in Submission.BoseGases.acube ℓ, (1 / ℓ ^ 3) *
          (lowKernel fc κ x₀ z *
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)) := by
    refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
    show lowKernel fc κ x₀ z * ((1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z))
        = ∫ y in Submission.BoseGases.acube ℓ, (1 / ℓ ^ 3) *
            (lowKernel fc κ x₀ z *
              ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z))
    rw [← MeasureTheory.integral_const_mul (1 / ℓ ^ 3),
      ← MeasureTheory.integral_const_mul (lowKernel fc κ x₀ z)]
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    show lowKernel fc κ x₀ z * ((1 / ℓ ^ 3) *
          (Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)
        = (1 / ℓ ^ 3) * (lowKernel fc κ x₀ z *
            (Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)
    ring
  have hstep3 : ∫ z : E3, ∫ y in Submission.BoseGases.acube ℓ, (1 / ℓ ^ 3) *
        (lowKernel fc κ x₀ z *
          ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z))
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z : E3, (1 / ℓ ^ 3) *
          (lowKernel fc κ x₀ z *
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)) :=
    MeasureTheory.integral_integral_swap (hInt.const_mul (1 / ℓ ^ 3))
  have hstep4 : ∫ y in Submission.BoseGases.acube ℓ, ∫ z : E3, (1 / ℓ ^ 3) *
        (lowKernel fc κ x₀ z *
          ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z))
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, ∫ z : E3,
          (lowKernel fc κ x₀ z *
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)) := by
    rw [show (fun y : E3 => ∫ z : E3, (1 / ℓ ^ 3) *
            (lowKernel fc κ x₀ z *
              ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)))
          = fun y : E3 => (1 / ℓ ^ 3) * ∫ z : E3,
              (lowKernel fc κ x₀ z *
                ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)) from
        funext (fun y => MeasureTheory.integral_const_mul _ _)]
    rw [MeasureTheory.integral_const_mul]
  have hmain : ∫ z : E3, lowKernel fc κ x₀ z *
        ((Submission.BoseGases.acube ℓ).indicator Φ z)
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, ∫ z : E3,
          lowKernel fc κ x₀ z *
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z) := by
    rw [hstep1, hstep2, hstep3, hstep4]
  -- the right-hand side in kernel form
  have hRHSker : (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) x₀
      = ((2 * Real.pi) ^ 3)⁻¹ * ((1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, ∫ z : E3,
          lowKernel fc κ x₀ z *
            ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z)) := by
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) x₀)
        = ∫ y in Submission.BoseGases.acube ℓ, ((2 * Real.pi) ^ 3)⁻¹ * ∫ z : E3,
            lowKernel fc κ x₀ z *
              ((Submission.BoseGases.acube ℓ).indicator (fun z => G y z) z) from
        integral_congr_ae (by
          filter_upwards [ae_restrict_mem hbox] with y hy
          exact hRfib y hy)]
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [hRΦ, hmain, hRHSker]

/-! ## 4. The target: commutation of `highSlot` with `aP` in a different slot -/

theorem highSlot_aP_comm (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : Continuous Ψ) (x : Submission.BoseGases.X n) :
    Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Ψ) x
      = Submission.BoseGases.aP ℓ i (Work.BoseFixB3.highSlot fc κ ℓ j Ψ) x := by
  classical
  have hbox : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  haveI : IsFiniteMeasure (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    acube_isFiniteMeasure_restrict hℓ
  set G : E3 → E3 → ℝ := fun y z => Ψ (Function.update (Function.update x i y) j z) with hG
  have hGc : Continuous (Function.uncurry G) := by
    rw [show Function.uncurry G = fun q : E3 × E3 =>
        Ψ (Function.update (Function.update x i q.1) j q.2) from rfl]
    exact hΨc.comp ((Continuous.update (X := E3 × E3)
      (continuous_const : Continuous fun _ : E3 × E3 => x) i continuous_fst).update j continuous_snd)
  obtain ⟨M, hMnn, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Submission.BoseGases.acube ℓ,
      ∀ z ∈ Submission.BoseGases.acube ℓ, |G y z| ≤ M := by
    have hKc : IsCompact (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
      (Submission.BoseGases.acube_compact hℓ).prod (Submission.BoseGases.acube_compact hℓ)
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hGc.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro y hy z hz
    refine le_trans ?_ (le_max_left _ _)
    have h := hC (y, z) ⟨hy, hz⟩
    rwa [Real.norm_eq_abs] at h
  -- the slot-`j` fibre of `aP ℓ i Ψ`
  have hfib : ∀ z : E3, Submission.BoseGases.aP ℓ i Ψ (Function.update x j z)
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, G y z := by
    intro z
    unfold Submission.BoseGases.aP
    congr 1
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    show Ψ (Function.update (Function.update x j z) i y) = G y z
    simp only [hG]
    exact congrArg Ψ (Function.update_comm (Ne.symm hij) z y x)
  -- the crux
  have hcrux := lowMult_box_mean_comm (fc := fc) (κ := κ) (ℓ := ℓ) (M := M) hκ hℓ hMnn hGc hMb
    (x j)
  have hcrux' : (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) (x j)
      = Work.BoseBoxFix.lowMult fc κ ℓ
          (fun z => (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, G y z) (x j) :=
    hcrux.symm
  -- the left-hand side
  have hLHS : Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Ψ) x
      = Submission.BoseGases.aP ℓ i Ψ x
        - Work.BoseBoxFix.lowMult fc κ ℓ
            (fun z => (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, G y z) (x j) := by
    unfold Work.BoseFixB3.highSlot Work.BoseBoxFix.lowSlot
    rw [show (fun z : E3 => Submission.BoseGases.aP ℓ i Ψ (Function.update x j z))
        = fun z : E3 => (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, G y z from
      funext hfib]
  -- the right-hand side
  have hRHS : Submission.BoseGases.aP ℓ i (Work.BoseFixB3.highSlot fc κ ℓ j Ψ) x
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
          Work.BoseFixB3.highSlot fc κ ℓ j Ψ (Function.update x i y) := rfl
  -- the pointwise split `highSlot = id − lowSlot`
  have hpoint : (fun y : E3 => Work.BoseFixB3.highSlot fc κ ℓ j Ψ (Function.update x i y))
      = fun y : E3 => Ψ (Function.update x i y)
          - Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) (x j) := by
    funext y
    unfold Work.BoseFixB3.highSlot Work.BoseBoxFix.lowSlot
    rw [show (fun z : E3 => Ψ (Function.update (Function.update x i y) j z))
          = fun z : E3 => G y z from funext (fun z => by simp only [hG]),
      Function.update_of_ne (Ne.symm hij)]
  -- integrability of the two halves of the split integrand
  have hAint : Integrable (fun y : E3 => Ψ (Function.update x i y))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((hΨc.comp (Continuous.update continuous_const i continuous_id)).continuousOn)
  have hBint : Integrable (fun y : E3 =>
        Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) (x j))
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    refine Integrable.of_bound
      ((measurable_lowMult_family fc κ ℓ hGc (x j)).aestronglyMeasurable)
      (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, |fc.f (‖p‖ / κ)|) * (M * ℓ ^ 3)) ?_
    filter_upwards [ae_restrict_mem hbox] with y hy
    rw [Real.norm_eq_abs]
    exact lowMult_abs_le_of_box_bound (fc := fc) (D := M) hκ hℓ hMnn
      ((hGc.comp (continuous_const.prodMk continuous_id)).measurable) (fun z hz => hMb y hy z hz)
      (x j)
  -- the split
  have hsplit : (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j Ψ (Function.update x i y)
      = Submission.BoseGases.aP ℓ i Ψ x
        - (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ,
            Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) (x j) := by
    rw [hpoint, MeasureTheory.integral_sub hAint hBint, mul_sub, hcrux']
    have hA : ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y)
        = ℓ ^ 3 * Submission.BoseGases.aP ℓ i Ψ x := by
      unfold Submission.BoseGases.aP
      field_simp
    have h2 : (1 / ℓ ^ 3) * (ℓ ^ 3 * Submission.BoseGases.aP ℓ i Ψ x)
        = Submission.BoseGases.aP ℓ i Ψ x := by
      field_simp
    rw [hA, h2]
  rw [hLHS, hRHS, hsplit, hcrux']

end Work.BoseFixB3.CS.Pieces
