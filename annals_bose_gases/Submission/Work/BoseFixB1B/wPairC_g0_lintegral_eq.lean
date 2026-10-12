import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB2.Pot.lintegral_wPairC_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.wPairC_g0_lintegral_eq`

The `ℝ≥0∞`-level box identity FS `eq:DefU` (Fournais--Solovej, *The energy of
dilute Bose gases*) for the chosen scattering numerator `g₀ = v(1−w₀)`: in the
dilute regime `R ≤ ℓ·chiR0` with `0 < ℓ`,

    ∫⁻_x ∫⁻_y ofReal (wPairC ℓ (g₀ v h) x y) = ofReal (8π (a v) ℓ³).

Route: Tonelli (`MeasureTheory.lintegral_prod`) turns the iterated `lintegral`
into the `lintegral` over the product `ℝ³ × ℝ³`, which
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` and
`MeasureTheory.integral_prod` convert into the Bochner double integral of the
kernel; that is `8π(a v)ℓ³` by the un-normalised box identity
`Submission.BoseGases.kernel_double_integral` composed with `∫g₀ = 8π(a v)`
(`Submission.BoseGases.g0_integral`).

The only integrability input beyond `kernel_double_integral` is the *product*
integrability of the kernel `wPairC ℓ (g₀ v h)`, which follows from the
`L¹`-bound `Work.BoseFixB2.Pot.lintegral_wPairC_le` together with
`MeasureTheory.hasFiniteIntegral_iff_enorm`; no slice or marginal
integrability is needed.  The a.e. nonnegativity is transported from `g₀ ≥ 0`
a.e. along the quasi-measure-preserving difference map `(x,y) ↦ x − y`, and the
a.e. measurability is transported from a measurable representative of `g₀`
along the same map.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal

namespace Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Euc3" => EuclideanSpace ℝ (Fin 3)

/-- Pointwise form of the renormalized kernel: the two `χ_ℓ` factors on the
outside, the numerator/denominator pair in the middle. -/
private lemma wPairC_pointwise (ℓ : ℝ) (g : Euc3 → ℝ) (x y : Euc3) :
    Submission.BoseGases.wPairC ℓ g x y
      = Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
        * (g (x - y) / Submission.BoseGases.convScale ℓ (x - y)) := by
  unfold Submission.BoseGases.wPairC Submission.BoseGases.wPair Submission.BoseGases.wScaled
  ring

/-- For a **measurable** numerator `g` the uncurried kernel `(x,y) ↦ wPairC ℓ g x y`
is a.e. measurable on the product: every factor is a measurable function of
`(x,y)` (`χ_ℓ` composed with the projections, `g` composed with the measurable
difference map, and the continuous denominator `(χ⋆χ)_ℓ`). -/
private lemma aemeasurable_wPairC_uncurry_of_measurable {g : Euc3 → ℝ} (hg : Measurable g)
    (ℓ : ℝ) :
    AEMeasurable (fun p : Euc3 × Euc3 => Submission.BoseGases.wPairC ℓ g p.1 p.2)
      ((volume : Measure Euc3).prod volume) := by
  have hsub : Measurable (fun p : Euc3 × Euc3 => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  have h1 : Measurable (fun p : Euc3 × Euc3 => Submission.BoseGases.chiScale ℓ p.1) :=
    (Submission.BoseGases.chiScale_continuous ℓ).measurable.comp measurable_fst
  have h2 : Measurable (fun p : Euc3 × Euc3 => Submission.BoseGases.chiScale ℓ p.2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).measurable.comp measurable_snd
  have hk : Measurable (fun p : Euc3 × Euc3 =>
      g (p.1 - p.2) / Submission.BoseGases.convScale ℓ (p.1 - p.2)) :=
    (hg.comp hsub).div ((Submission.BoseGases.convScale_continuous ℓ).measurable.comp hsub)
  have hm : Measurable (fun p : Euc3 × Euc3 =>
      Submission.BoseGases.chiScale ℓ p.1
        * (g (p.1 - p.2) / Submission.BoseGases.convScale ℓ (p.1 - p.2))
        * Submission.BoseGases.chiScale ℓ p.2) := (h1.mul hk).mul h2
  have hm' : Measurable (fun p : Euc3 × Euc3 => Submission.BoseGases.wPairC ℓ g p.1 p.2) := hm
  exact hm'.aemeasurable

theorem wPairC_g0_lintegral_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < ℓ) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y))
      = ENNReal.ofReal (8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3) := by
  have hgint : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hgnn : ∀ᵐ z : Euc3, 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  -- the quasi-measure-preserving difference map on the product
  have hqmp : Measure.QuasiMeasurePreserving (fun p : Euc3 × Euc3 => p.1 - p.2)
      ((volume : Measure Euc3).prod volume) (volume : Measure Euc3) :=
    quasiMeasurePreserving_sub_of_right_invariant _ _
  -- a measurable representative `q` of `g₀`
  let q : Euc3 → ℝ := AEStronglyMeasurable.mk (Submission.BoseGases.g0 v h)
    hgint.aestronglyMeasurable
  have hqm : Measurable q := hgint.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hqae : Submission.BoseGases.g0 v h =ᵐ[(volume : Measure Euc3)] q :=
    hgint.aestronglyMeasurable.ae_eq_mk
  -- a.e. equality of the kernels of `g₀` and of `q`
  have hEq : (fun p : Euc3 × Euc3 => Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
      =ᵐ[((volume : Measure Euc3).prod volume)]
      (fun p : Euc3 × Euc3 => Submission.BoseGases.wPairC ℓ q p.1 p.2) := by
    filter_upwards [hqmp.ae hqae] with p hp
    have h := congrArg (fun u : ℝ => Submission.BoseGases.chiScale ℓ p.1
      * (u / Submission.BoseGases.convScale ℓ (p.1 - p.2)) * Submission.BoseGases.chiScale ℓ p.2) hp
    simpa only [Submission.BoseGases.wPairC, Submission.BoseGases.wPair,
      Submission.BoseGases.wScaled] using h
  -- a.e. measurability of the uncurried kernel
  have hAEM : AEMeasurable
      (fun p : Euc3 × Euc3 => Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
      ((volume : Measure Euc3).prod volume) :=
    (aemeasurable_wPairC_uncurry_of_measurable hqm ℓ).congr hEq.symm
  -- product integrability of the uncurried kernel
  have hInt : Integrable
      (fun p : Euc3 × Euc3 => Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
      ((volume : Measure Euc3).prod volume) := by
    refine ⟨hAEM.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt
      (Work.BoseFixB2.Pot.lintegral_wPairC_le (h := Submission.BoseGases.g0 v h) hℓ hgint)
      ENNReal.ofReal_lt_top
  -- a.e. nonnegativity of the kernel on the product
  have hnn : 0 ≤ᵐ[((volume : Measure Euc3).prod volume)]
      (fun p : Euc3 × Euc3 => Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2) := by
    filter_upwards [hqmp.ae hgnn] with p hp
    rw [wPairC_pointwise ℓ (Submission.BoseGases.g0 v h) p.1 p.2]
    exact mul_nonneg
      (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ p.1)
        (Submission.BoseGases.chiScale_nonneg ℓ p.2))
      (div_nonneg hp (Submission.BoseGases.convScale_nonneg ℓ (p.1 - p.2)))
  -- a.e. measurability of the `ofReal`-integrand on the product
  have hAEMofReal : AEMeasurable
      (fun p : Euc3 × Euc3 =>
        ENNReal.ofReal (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2))
      ((volume : Measure Euc3).prod volume) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hAEM
  -- the value of the Bochner double integral of the kernel
  have hmain : (∫ x : Euc3, ∫ y : Euc3,
        Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y)
      = 8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3 := by
    have hKeq : (∫ x : Euc3, ∫ y : Euc3,
          Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
            * (Submission.BoseGases.g0 v h (x - y) / Submission.BoseGases.convScale ℓ (x - y)))
        = ∫ x : Euc3, ∫ y : Euc3,
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      exact (wPairC_pointwise ℓ (Submission.BoseGases.g0 v h) x y).symm
    have hK := Submission.BoseGases.kernel_double_integral
      (h := Submission.BoseGases.g0 v h) (ℓ := ℓ) (R := R) (r₀ := Submission.BoseGases.chiR0)
      hℓ hgint (fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h)
      Submission.BoseGases.chiR0_pos hRχ Submission.BoseGases.chiR0_half
    rw [hKeq, Submission.BoseGases.g0_integral hR hv_supp h] at hK
    rw [hK]
    ring
  calc (∫⁻ x : Euc3, ∫⁻ y : Euc3,
        ENNReal.ofReal (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y))
      = ∫⁻ p : Euc3 × Euc3,
          ENNReal.ofReal (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
          ∂((volume : Measure Euc3).prod volume) :=
        (MeasureTheory.lintegral_prod
          (fun p : Euc3 × Euc3 =>
            ENNReal.ofReal (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2))
          hAEMofReal).symm
    _ = ENNReal.ofReal (∫ p : Euc3 × Euc3,
          Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2
          ∂((volume : Measure Euc3).prod volume)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
    _ = ENNReal.ofReal (∫ x : Euc3, ∫ y : Euc3,
          Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y) := by
        rw [MeasureTheory.integral_prod
          (fun p : Euc3 × Euc3 =>
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2) hInt]
    _ = ENNReal.ofReal (8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3) := by rw [hmain]

end Work.BoseFixB1B
