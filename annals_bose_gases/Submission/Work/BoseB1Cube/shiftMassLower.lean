import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.Defs
import Submission.Work.BoseB1Cube.g0ChiChiLeWSmall1Pair
import Submission.Work.BoseFixB1S.fibreAeTransfer
import Submission.Work.BoseFixB1S.flatFibDeviationB1
import Submission.Work.BoseFixB1S.flatOmegaAllStateB1
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.shiftMassLower`

The **lower bound for the localised one-body mass `w1MassB`** under the fibre-shift
(autocorrelation) hypothesis:

    (1 − θ)·8π(a v)·chiMass M ℓ d u  ≤  w1MassB h M ℓ d u .

## The mathematics

Write `χ = χ_B = chiSmallB M ℓ d u`, `g₀ = v(1−ω₀)` (so `∫g₀ = 8π a v` by
`Submission.BoseGases.g0_integral`, `g₀ ≥ 0` a.e. and `g₀` vanishes outside `ball 0 R`) and
`w₁ = wSmall1Pair h M ℓ d u`, whose factors are
`χ(x)·(g₀(x−y)/(C_{ℓd}(x−y)·C_ℓ(x−y)))·χ(y)`.  Since the renormalisation denominators lie in
`(0,1]` on `supp g₀` (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`), the pointwise comparison

    g₀(x−y)·χ(x)·χ(y) ≤ w₁(x,y)        (a.e.)

holds (`Work.BoseB1Cube.g0_chi_chi_le_wSmall1Pair`).  The shear identity
(`Work.BoseFixB1S.shear_integral_identity`: the map `(x,y) ↦ (x−y,y)` is measure-preserving)
evaluates the resulting double integral as the single integral

    ∬ g₀(x−y) χ(x) χ(y) = ∫ z, g₀(z) · (∫ y, χ(z+y)χ(y)) ,

and translation invariance of the fibre integral (`Work.BoseFixB1S.conv_shift_eq`) turns the
inner integral into `∫ x, χ(x)χ(x−z)`, which the shift hypothesis bounds below by
`(1−θ)·chiMass` for `‖z‖ ≤ R`.  Since `g₀ ≥ 0` a.e. and `g₀(z) = 0` for `‖z‖ > R`, the last
integral is at least `(1−θ)·chiMass·∫z, g₀ z = (1−θ)·chiMass·8π(a v)`.

This is the `w1MassB`-form of the identical argument in
`Work.BoseB1Cube.boxM1GeConvChiMass` (there stated with `boxM1 ℓ (dlBox ℓ d u) w₁` on the
right; the two right-hand sides agree definitionally by
`Work.BoseFixB1S.boxM1_eq_nested`), here without the extra (and in fact unused) geometric
hypothesis `dlBox ℓ d u ⊆ ball 0 (ℓ/4)` of that file.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem shiftMassLower {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d θ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    (hshift : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      (1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u
        ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
            * Submission.BoseGases.chiSmallB M ℓ d u (x - z)) :
    (1 - θ) * (8 * Real.pi * _root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ Work.BoseFixB1.w1MassB h M ℓ d u := by
  classical
  -- ### Step 1: continuity, positivity and bounds for the cutoff `χ = chiSmallB M ℓ d u`
  have hXcont : Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) := by
    show Continuous fun x : E3 =>
      Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp
        ((continuous_const_smul ((ℓ * d)⁻¹)).sub continuous_const))
  have hXnonneg : ∀ x : E3, 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u
  -- ### Step 2: strong measurability of the pair integrands
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((volume : Measure E3).prod volume) (volume : Measure E3) :=
    MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant _ _
  have hgaesm : AEStronglyMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
    (Submission.BoseGases.g0_integrable hR0 hv_supp h).aestronglyMeasurable
  have hgaesm' : AEStronglyMeasurable (fun p : E3 × E3 => Submission.BoseGases.g0 v h (p.1 - p.2))
      ((volume : Measure E3).prod volume) := hgaesm.comp_quasiMeasurePreserving hqmp
  have hX1m : AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1)
      ((volume : Measure E3).prod volume) :=
    (hXcont.measurable.comp measurable_fst).aestronglyMeasurable
  have hX2m : AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume : Measure E3).prod volume) :=
    (hXcont.measurable.comp measurable_snd).aestronglyMeasurable
  have haesmGf : AEStronglyMeasurable (fun p : E3 × E3 =>
      Submission.BoseGases.g0 v h (p.1 - p.2)
        * Submission.BoseGases.chiSmallB M ℓ d u p.1
        * Submission.BoseGases.chiSmallB M ℓ d u p.2) ((volume : Measure E3).prod volume) :=
    (hgaesm'.mul hX1m).mul hX2m
  -- ### Step 3: integrability of the pair integrands
  have hDom : Integrable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1
      * |Submission.BoseGases.g0 v h (p.1 - p.2)| * Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume : Measure E3).prod volume) := by
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset ?_).mp
      (Work.BoseFixB1.integrable_sbMassKernel hv_supp hR0 h hM hℓ hd hR hRχ u)
    rintro ⟨x, y⟩ hp
    have hx : Submission.BoseGases.chiSmallB M ℓ d u x ≠ 0 := by
      intro h0; exact hp (by simp [h0])
    have hy : Submission.BoseGases.chiSmallB M ℓ d u y ≠ 0 := by
      intro h0; exact hp (by simp [h0])
    exact Set.mem_prod.mpr ⟨Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hx,
      Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hy⟩
  have hvanW1 : ∀ x y : E3, (x ∉ Submission.BoseGases.dlBox ℓ d u
      ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) →
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 := fun x y hxy =>
    Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  have hIntW1On : IntegrableOn (fun p : E3 × E3 =>
      Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u) :=
    MeasureTheory.IntegrableOn.mono_set
      (Work.BoseFixB1.integrableOn_wSmallPair_cube (f := Submission.BoseGases.g0 v h)
        (Submission.BoseGases.g0_integrable hR0 hv_supp h) (R0 := R)
        (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR hRχ u)
      (Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
        (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u))
  have hIntW1 : Integrable (fun p : E3 × E3 =>
      Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) ((volume : Measure E3).prod volume) := by
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset ?_).mp hIntW1On
    rintro ⟨x, y⟩ hp
    rw [Set.mem_prod]
    by_contra hc
    rw [not_and_or] at hc
    exact hp (hvanW1 x y hc)
  have hIntGf : Integrable (fun p : E3 × E3 => Submission.BoseGases.g0 v h (p.1 - p.2)
      * Submission.BoseGases.chiSmallB M ℓ d u p.1
      * Submission.BoseGases.chiSmallB M ℓ d u p.2) ((volume : Measure E3).prod volume) := by
    refine Integrable.mono' hDom haesmGf ?_
    filter_upwards with p
    have hχ1 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u p.1 := hXnonneg p.1
    have hχ2 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u p.2 := hXnonneg p.2
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hχ1, abs_of_nonneg hχ2]
    exact le_of_eq (by ring)
  -- ### Step 4: the a.e. pointwise comparison `g₀χχ ≤ w₁`
  have hgnn : ∀ᵐ z ∂(volume : Measure E3), 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae hR0 hv hvrad hv_supp h
  have hae_cmp : ∀ᵐ p ∂((volume : Measure E3).prod volume),
      Submission.BoseGases.g0 v h (p.1 - p.2) * Submission.BoseGases.chiSmallB M ℓ d u p.1
          * Submission.BoseGases.chiSmallB M ℓ d u p.2
        ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 :=
    (hqmp.ae hgnn).mono fun p hp =>
      g0_chi_chi_le_wSmall1Pair hv_supp hR0 h hM hℓ hd hR hRχ u p.1 p.2 hp
  -- ### Step 5: the shear identity
  have hint : Integrable (fun q : E3 × E3 =>
      Submission.BoseGases.g0 v h q.1
        * (Submission.BoseGases.chiSmallB M ℓ d u (q.1 + q.2)
            * Submission.BoseGases.chiSmallB M ℓ d u q.2)) ((volume : Measure E3).prod volume) := by
    have hmp : MeasurePreserving (fun z : E3 × E3 => (z.1 + z.2, z.2))
        ((volume : Measure E3).prod volume) ((volume : Measure E3).prod volume) :=
      MeasureTheory.measurePreserving_add_prod _ _
    have hcomp : Integrable ((fun p : E3 × E3 => Submission.BoseGases.g0 v h (p.1 - p.2)
        * Submission.BoseGases.chiSmallB M ℓ d u p.1
        * Submission.BoseGases.chiSmallB M ℓ d u p.2) ∘ (fun z : E3 × E3 => (z.1 + z.2, z.2)))
        ((volume : Measure E3).prod volume) :=
      (hmp.integrable_comp haesmGf).mpr hIntGf
    refine hcomp.congr (Eventually.of_forall fun q => ?_)
    simp only [Function.comp_apply]
    show Submission.BoseGases.g0 v h (q.1 + q.2 - q.2)
        * Submission.BoseGases.chiSmallB M ℓ d u (q.1 + q.2)
        * Submission.BoseGases.chiSmallB M ℓ d u q.2
      = Submission.BoseGases.g0 v h q.1
        * (Submission.BoseGases.chiSmallB M ℓ d u (q.1 + q.2)
            * Submission.BoseGases.chiSmallB M ℓ d u q.2)
    rw [add_sub_cancel_right]
    ring
  have hShear : (∫ p : E3 × E3, Submission.BoseGases.g0 v h (p.1 - p.2)
        * Submission.BoseGases.chiSmallB M ℓ d u p.1
        * Submission.BoseGases.chiSmallB M ℓ d u p.2 ∂((volume : Measure E3).prod volume))
      = ∫ z, Submission.BoseGases.g0 v h z
          * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3))
          ∂(volume : Measure E3) := by
    rw [show (∫ p : E3 × E3, Submission.BoseGases.g0 v h (p.1 - p.2)
          * Submission.BoseGases.chiSmallB M ℓ d u p.1
          * Submission.BoseGases.chiSmallB M ℓ d u p.2 ∂((volume : Measure E3).prod volume))
        = ∫ p : E3 × E3, Submission.BoseGases.g0 v h (p.1 - p.2)
            * (Submission.BoseGases.chiSmallB M ℓ d u p.1
                * Submission.BoseGases.chiSmallB M ℓ d u p.2)
          ∂((volume : Measure E3).prod volume) from
      integral_congr_ae (Eventually.of_forall fun p => by ring)]
    exact Work.BoseFixB1S.shear_integral_identity (Submission.BoseGases.g0 v h)
      (fun x => Submission.BoseGases.chiSmallB M ℓ d u x) hint
  -- ### Step 6: the `z`-integral comparison
  have hIntZC : Integrable (fun z : E3 => Submission.BoseGases.g0 v h z
      * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
          * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)))
      (volume : Measure E3) := by
    have h1 : Integrable (fun z : E3 => ∫ y, Submission.BoseGases.g0 v h z
        * (Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y) ∂(volume : Measure E3))
        (volume : Measure E3) := hint.integral_prod_left
    refine h1.congr (Eventually.of_forall fun z => ?_)
    show (∫ y : E3, Submission.BoseGases.g0 v h z
        * (Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y) ∂(volume : Measure E3))
      = Submission.BoseGases.g0 v h z
        * ∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)
    rw [MeasureTheory.integral_const_mul]
  have hIntGc : Integrable (fun z : E3 => Submission.BoseGases.g0 v h z
      * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u)) (volume : Measure E3) :=
    (Submission.BoseGases.g0_integrable hR0 hv_supp h).mul_const
      ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u)
  have haeD : ∀ᵐ z ∂(volume : Measure E3),
      Submission.BoseGases.g0 v h z * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u)
        ≤ Submission.BoseGases.g0 v h z
          * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)) := by
    filter_upwards [hgnn] with z hgz
    by_cases hz : ‖z‖ ≤ R
    · have hcr : (1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u
          ≤ ∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3) := by
        rw [Work.BoseFixB1S.conv_shift_eq (fun x => Submission.BoseGases.chiSmallB M ℓ d u x) z]
        exact hshift z hz
      exact mul_le_mul_of_nonneg_left hcr hgz
    · have hz0 : Submission.BoseGases.g0 v h z = 0 :=
        Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_not_ge hz) h
      rw [hz0, zero_mul, zero_mul]
  have hstepD : (∫ z : E3, Submission.BoseGases.g0 v h z
        * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u) ∂(volume : Measure E3))
      ≤ ∫ z : E3, Submission.BoseGases.g0 v h z
          * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3))
          ∂(volume : Measure E3) :=
    MeasureTheory.integral_mono_ae hIntGc hIntZC haeD
  -- ### Step 7: monotonicity at the pair level
  have hstepB : (∫ p : E3 × E3, Submission.BoseGases.g0 v h (p.1 - p.2)
        * Submission.BoseGases.chiSmallB M ℓ d u p.1
        * Submission.BoseGases.chiSmallB M ℓ d u p.2 ∂((volume : Measure E3).prod volume))
      ≤ ∫ p : E3 × E3, Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
        ∂((volume : Measure E3).prod volume) :=
    MeasureTheory.integral_mono_ae hIntGf hIntW1 hae_cmp
  -- ### Step 8: the assembly
  have hmain : (1 - θ) * (8 * Real.pi * _root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ ∫ p : E3 × E3, Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
        ∂((volume : Measure E3).prod volume) := by
    calc (1 - θ) * (8 * Real.pi * _root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u
        = (8 * Real.pi * _root_.BoseGases.a v)
            * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u) := by ring
      _ = (∫ z : E3, Submission.BoseGases.g0 v h z)
            * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u) := by
          rw [Submission.BoseGases.g0_integral hR0 hv_supp h]
      _ = ∫ z : E3, Submission.BoseGases.g0 v h z
            * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u) ∂(volume : Measure E3) :=
          (MeasureTheory.integral_mul_const _ (Submission.BoseGases.g0 v h)).symm
      _ ≤ ∫ z : E3, Submission.BoseGases.g0 v h z
            * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
                * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3))
            ∂(volume : Measure E3) := hstepD
      _ = ∫ p : E3 × E3, Submission.BoseGases.g0 v h (p.1 - p.2)
            * Submission.BoseGases.chiSmallB M ℓ d u p.1
            * Submission.BoseGases.chiSmallB M ℓ d u p.2 ∂((volume : Measure E3).prod volume) :=
          hShear.symm
      _ ≤ ∫ p : E3 × E3, Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
            ∂((volume : Measure E3).prod volume) := hstepB
  have hprod : Work.BoseFixB1.w1MassB h M ℓ d u
      = ∫ p : E3 × E3, Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
        ∂((volume : Measure E3).prod volume) := by
    show (∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmall1Pair h M ℓ d u x y
        ∂(volume : Measure E3) ∂(volume : Measure E3)) = _
    exact (MeasureTheory.integral_prod
      (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) hIntW1).symm
  rw [hprod]
  exact hmain

end Work.BoseB1Cube
