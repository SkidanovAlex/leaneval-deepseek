import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.sliceStep5Weak
import Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vv0
import Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vv1
import Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Vg0
import Submission.Work.FTS.EllipticEst.H2W.G1Alt.g1BoundAlt
import Submission.Work.FTS.EllipticEst.H2W.VTwoAlt.vTwoW4WeakAlt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `topB_sliceStep5_uniform`: Elgindi Step 5 for the slice, with a constant uniform in `γ`

The statement is that of `Work.FTS.EllipticEst.H2W.sliceStep5Weak` with the constant hoisted
out of the `γ`-quantifier: for `1 ≤ γ ≤ 3/2` and a `C⁴` function `u` on `(0, π/2)`
(continuous on the closed interval, vanishing at both ends) with `Lzero1 u = g` on `(0,π/2)`,

  `∫ (u⁗)² sin(2θ)^{4-γ} ≤ C (∫ (g'')² sin(2θ)^{4-γ} + ∫ (u''')² sin(2θ)^{2-γ}`
  `  + ∫ (u'')² sEta + ∫ (u')² + ∫ u²)`,

with a single `C` working for every `γ ∈ [1, 3/2]` (this is what the two-dimensional
Step-5 estimate needs, since it is instantiated at `γ = gam α` which varies with `α`).

The proof is the assembly of `sliceStep5Weak`; the point is that *its* proof already produces a
`γ`-independent constant, because the three leaves it invokes
(`sliceStep5Vv0`, `sliceStep5Vv1`, `g1BoundAlt vTwoW4WeakAlt`) are themselves stated with the
constant outside the `γ`-quantifier.  So the same integral bookkeeping, run with `γ` introduced
after the constant, yields the uniform estimate.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

open Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem topB_sliceStep5_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u g : ℝ → ℝ),
      ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
                Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := sliceStep5Vv0
  obtain ⟨C1, hC1pos, hC1⟩ := sliceStep5Vv1
  obtain ⟨C3, hC3pos, hC3⟩ := g1BoundAlt VTwoAlt.vTwoW4WeakAlt
  refine ⟨3 * (4 * (16 * (16 + 225 + C0 + 9 * C3) + 27 * (2 + 4 * C1) + 9 * C1 + 1) + 37),
    by linarith, ?_⟩
  intro γ hγ1 hγ2 u g hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hIθm : MeasurableSet Work.Spaces.Iθ := Iθ_measurableSet
  obtain ⟨hIntV0, hIntV1, _hIntG0, hIntG1⟩ :=
    sliceStep5Integrable γ hγ1 hγ2 u g hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hC0b := hC0 γ u g hγ1 hγ2 hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hC1b := hC1 γ u g hγ1 hγ2 hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  have hC3b := hC3 γ u g hγ1 hγ2 hu huc hu0 hupi hode h4 h3 h2 h1 h0 hB
  -- ==== abbreviations ====
  set B2 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hB2
  set A3 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hA3
  set A2 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ) with hA2
  set A1 := (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) with hA1
  set A0 := (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) with hA0
  set R := B2 + A3 + A2 + A1 + A0 with hR
  set A4 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hA4
  set AA := (∫ θ in Work.Spaces.Iθ,
    (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hAA
  set J2 := (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hJ2
  set J1 := (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hJ1
  set J0 := (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hJ0
  set Q := (∫ θ in Work.Spaces.Iθ,
    (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hQ
  set X2 := (∫ θ in Work.Spaces.Iθ,
    (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hX2
  set X1 := (∫ θ in Work.Spaces.Iθ,
    (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hX1
  set X0 := (∫ θ in Work.Spaces.Iθ,
    (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hX0
  set V0 := (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hV0
  set Bv1 := (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hBv1
  set G1 := (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 - γ)) with hG1
  -- ==== basic integrability ====
  have hIntJ2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' h2
      (((measurable_deriv (deriv u)).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))]
        exact mul_le_mul_of_nonneg_left (rpow4_le_sEta_rp γ hγ1 hγ2 hθ) (sq_nonneg _))
  have hIntJ1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' h1
      (((measurable_deriv u).pow_const 2).mul
        (measurable_rpow_sin_two γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow2_nonneg_rp γ hθ))]
        simpa using mul_le_mul_of_nonneg_left (rpow2_le_one_rp γ hγ1 hγ2 hθ) (sq_nonneg _))
  have hIntJ0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' h0
      (((huc.aestronglyMeasurable hIθm).pow 2).mul
        (measurable_rpow_sin_four γ hγ2).aestronglyMeasurable)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))]
        simpa using mul_le_mul_of_nonneg_left (rpow4_le_one_rp γ hγ1 hγ2 hθ) (sq_nonneg _))
  have hIntSv1 : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hIntV1
      (((Real.continuous_sin.measurable.mul
        (measurable_deriv (fun t => u t / Real.cos t))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))]
        exact mul_le_mul_of_nonneg_right
          (sin_mul_sq_le_sq θ (deriv (fun t => u t / Real.cos t) θ))
          (rpow4_nonneg_rp γ hθ))
  have hIntCv0 : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun_ae hIntJ0 (by
      filter_upwards [cos_mul_ae (u := u)] with θ h
      rw [h])
  -- the same facts in `Integrable` form (this is what `integral_add` wants)
  have hIJ2 : MeasureTheory.Integrable
      (fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntJ2
  have hIJ1 : MeasureTheory.Integrable
      (fun θ => (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntJ1
  have hIJ0 : MeasureTheory.Integrable
      (fun θ => (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntJ0
  have hISv1 : MeasureTheory.Integrable
      (fun θ => (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntSv1
  have hICv0i : MeasureTheory.Integrable
      (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntCv0
  have hI3i : MeasureTheory.Integrable
      (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := h3
  have hIG1i : MeasureTheory.Integrable
      (fun θ => (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntG1
  have hIV0i : MeasureTheory.Integrable
      (fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict Work.Spaces.Iθ) := hIntV0
  have hIBi : MeasureTheory.Integrable
      (fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (volume.restrict Work.Spaces.Iθ) := hB
  -- ==== X2 ====
  set D2 : ℝ → ℝ := fun θ => 3 *
      ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))) with hD2
  have hD2int : MeasureTheory.IntegrableOn D2 Work.Spaces.Iθ := by
    rw [hD2]
    exact ((hIntJ2.add hIntJ0).add (hIntSv1.const_mul 4)).const_mul 3
  have hae_nnX2 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeX2 : (fun θ => (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] D2 := by
    filter_upwards [ae_mem_Ioo_Iθ, CV2_ae hu hode] with θ hθ hCV2
    have hw : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := rpow4_nonneg_rp γ (Iθ_of_Ioo hθ)
    have hsq : (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
        ≤ 3 * ((deriv (deriv u) θ) ^ 2 + (u θ) ^ 2
            + 4 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2) := by
      rw [hCV2]
      nlinarith [sq_add_le_three (deriv (deriv u) θ) (u θ)
        (2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ))]
    rw [hD2]
    calc (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (3 * ((deriv (deriv u) θ) ^ 2 + (u θ) ^ 2
            + 4 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2)) *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) := mul_le_mul_of_nonneg_right hsq hw
      _ = 3 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) := by ring
  have hIntCv2 : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hD2int
      ((((Real.continuous_cos.measurable).mul
        (measurable_deriv (deriv (fun t => u t / Real.cos t)))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [hae_nnX2, haeX2] with θ h1 h2
        rwa [Real.norm_eq_abs, abs_of_nonneg h1])
  have hD2val : (∫ θ in Work.Spaces.Iθ, D2 θ) = 3 * (J2 + J0 + 4 * X1) := by
    have hA : MeasureTheory.Integrable
        (fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
          + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIJ2.add hIJ0
    have hB' : MeasureTheory.Integrable
        (fun θ => 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hISv1.const_mul 4
    rw [hD2, MeasureTheory.integral_const_mul 3]
    rw [MeasureTheory.integral_add
      (f := fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (g := fun θ => 4 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))) hA hB']
    rw [MeasureTheory.integral_add
      (f := fun θ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (g := fun θ => (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      hIJ2 hIJ0]
    rw [MeasureTheory.integral_const_mul 4, hJ2, hJ0, hX1]
  have hX2cmp : X2 ≤ 3 * (J2 + J0 + 4 * X1) := by
    rw [hX2]
    calc (∫ θ in Work.Spaces.Iθ,
          (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, D2 θ := integral_le_of_ae hae_nnX2 hD2int haeX2
      _ = 3 * (J2 + J0 + 4 * X1) := hD2val
  -- ==== Q ====
  set DQ : ℝ → ℝ := fun θ => 16 *
      (16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))) with hDQ
  have hDQint : MeasureTheory.IntegrableOn DQ Work.Spaces.Iθ := by
    rw [hDQ]
    exact ((((h3.const_mul 16).add (hIntJ1.const_mul 225)).add hIntV0).add
      (hIntG1.const_mul 9)).const_mul 16
  have hae_nnQ : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeQ : (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] DQ := by
    filter_upwards [ae_mem_Ioo_Iθ, CV3_ae hu hode] with θ hθ hCV3
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hcos : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).ne'
    have htan : Real.tan θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ 4 * Real.rpow (Real.sin (2 * θ)) (2 - γ) := tan_sq_mul_rpow4_le_rp γ hθ
    have hsqeq : (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
        = Real.tan θ ^ 2 *
          (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 :=
      sin_mul_sq_eq_tan hcos _
    have hcv : (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
        ≤ 4 * ((4 * deriv (deriv (deriv u)) θ) ^ 2 + (15 * deriv u θ) ^ 2
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 + (3 * deriv g θ) ^ 2) := by
      rw [hCV3]
      nlinarith [sq_add_le_four (4 * deriv (deriv (deriv u)) θ) (15 * deriv u θ)
        (-(Real.sin θ * (u θ / Real.cos θ))) (3 * deriv g θ)]
    have hsv : (Real.sin θ * (u θ / Real.cos θ)) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_le_mul_of_nonneg_right (sin_mul_sq_le_sq θ _) (rpow2_nonneg_rp γ (Iθ_of_Ioo hθ))
    rw [hsqeq, hDQ]
    have hw2 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := rpow2_nonneg_rp γ (Iθ_of_Ioo hθ)
    calc Real.tan θ ^ 2 *
          (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        = (Real.tan θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) *
          (Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 := by ring
      _ ≤ (4 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) *
          (4 * ((4 * deriv (deriv (deriv u)) θ) ^ 2 + (15 * deriv u θ) ^ 2
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 + (3 * deriv g θ) ^ 2)) :=
          mul_le_mul htan hcv (sq_nonneg _) (by positivity)
      _ = 16 * Real.rpow (Real.sin (2 * θ)) (2 - γ) *
          (16 * (deriv (deriv (deriv u)) θ) ^ 2 + 225 * (deriv u θ) ^ 2
            + (Real.sin θ * (u θ / Real.cos θ)) ^ 2 + 9 * (deriv g θ) ^ 2) := by ring
      _ ≤ 16 * Real.rpow (Real.sin (2 * θ)) (2 - γ) *
          (16 * (deriv (deriv (deriv u)) θ) ^ 2 + 225 * (deriv u θ) ^ 2
            + (u θ / Real.cos θ) ^ 2 + 9 * (deriv g θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (by linarith [sin_mul_sq_le_sq θ (u θ / Real.cos θ)])
            (by positivity)
      _ = 16 * (16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))) := by ring
  have hIntQint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hDQint
      ((((Real.continuous_sin.measurable).mul
        (measurable_deriv (deriv (deriv (fun t => u t / Real.cos t))))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [hae_nnQ, haeQ] with θ h1 h2
        rwa [Real.norm_eq_abs, abs_of_nonneg h1])
  have hDQval : (∫ θ in Work.Spaces.Iθ, DQ θ) = 16 * (16 * A3 + 225 * J1 + V0 + 9 * G1) := by
    have hA : MeasureTheory.Integrable
        (fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hI3i.const_mul 16).add (hIJ1.const_mul 225)).add hIV0i
    have hA' : MeasureTheory.Integrable
        (fun θ => 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hIG1i.const_mul 9
    have hB : MeasureTheory.Integrable
        (fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) :=
      (hI3i.const_mul 16).add (hIJ1.const_mul 225)
    have hB' : MeasureTheory.Integrable
        (fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIV0i
    have hC : MeasureTheory.Integrable
        (fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hI3i.const_mul 16
    have hC' : MeasureTheory.Integrable
        (fun θ => 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hIJ1.const_mul 225
    rw [hDQ, MeasureTheory.integral_const_mul 16]
    rw [MeasureTheory.integral_add
      (f := fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (g := fun θ => 9 * ((deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))) hA hA']
    rw [MeasureTheory.integral_add
      (f := fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
      (g := fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      hB hB']
    rw [MeasureTheory.integral_add
      (f := fun θ => 16 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
      (g := fun θ => 225 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)))
      hC hC']
    rw [MeasureTheory.integral_const_mul 16, MeasureTheory.integral_const_mul 225,
      MeasureTheory.integral_const_mul 9, hA3, hJ1, hV0, hG1]
  have hQcmp : Q ≤ 16 * (16 * A3 + 225 * J1 + V0 + 9 * G1) := by
    rw [hQ]
    calc (∫ θ in Work.Spaces.Iθ,
          (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, DQ θ := integral_le_of_ae hae_nnQ hDQint haeQ
      _ = 16 * (16 * A3 + 225 * J1 + V0 + 9 * G1) := hDQval
  -- ==== AA ====
  set DAA : ℝ → ℝ := fun θ => 4 *
      ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hDAA
  have hDAAint : MeasureTheory.IntegrableOn DAA Work.Spaces.Iθ := by
    rw [hDAA]
    exact (((hIntQint.add (hIntCv2.const_mul 9)).add (hIntSv1.const_mul 9)).add
      hIntCv0).const_mul 4
  have hae_nnAA : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeAA : (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] DAA := by
    filter_upwards [ae_mem_Ioo_Iθ, tanu3_ae hu] with θ hθ htan3
    have hw : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := rpow4_nonneg_rp γ (Iθ_of_Ioo hθ)
    have hsq : (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
        ≤ 4 * ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
            + 9 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
            + 9 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2
            + (Real.cos θ * (u θ / Real.cos θ)) ^ 2) := by
      rw [htan3]
      nlinarith [sq_add_le_four
        (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ)
        (3 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ))
        (-(3 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ)))
        (-(Real.cos θ * (u θ / Real.cos θ)))]
    rw [hDAA]
    calc (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (4 * ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
            + 9 * (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
            + 9 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2
            + (Real.cos θ * (u θ / Real.cos θ)) ^ 2)) *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) := mul_le_mul_of_nonneg_right hsq hw
      _ = 4 * ((Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by ring
  have hIntAAint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mono' hDAAint
      (((measurable_deriv (deriv (deriv (fun t => Real.tan t * u t)))).pow_const 2).mul
        (measurable_rpow_sin_four γ hγ2)).aestronglyMeasurable
      (by
        filter_upwards [hae_nnAA, haeAA] with θ h1 h2
        rwa [Real.norm_eq_abs, abs_of_nonneg h1])
  have hDAAval : (∫ θ in Work.Spaces.Iθ, DAA θ) = 4 * (Q + 9 * X2 + 9 * X1 + X0) := by
    have hIQi : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIntQint
    have hICv2i : MeasureTheory.Integrable
        (fun θ => (Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIntCv2
    have hA : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) :=
      (hIQi.add (hICv2i.const_mul 9)).add (hISv1.const_mul 9)
    have hA' : MeasureTheory.Integrable
        (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hICv0i
    have hB : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hIQi.add (hICv2i.const_mul 9)
    have hB' : MeasureTheory.Integrable
        (fun θ => 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hISv1.const_mul 9
    have hC : MeasureTheory.Integrable
        (fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (volume.restrict Work.Spaces.Iθ) := hIQi
    have hC' : MeasureTheory.Integrable
        (fun θ => 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        (volume.restrict Work.Spaces.Iθ) := hICv2i.const_mul 9
    rw [hDAA, MeasureTheory.integral_const_mul 4]
    rw [MeasureTheory.integral_add
      (f := fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
      (g := fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)) hA hA']
    rw [MeasureTheory.integral_add
      (f := fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)))
      (g := fun θ => 9 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) hB hB']
    rw [MeasureTheory.integral_add
      (f := fun θ => (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (g := fun θ => 9 * ((Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) hC hC']
    rw [MeasureTheory.integral_const_mul 9, MeasureTheory.integral_const_mul 9,
      hQ, hX2, hX1, hX0]
  have hAAcmp : AA ≤ 4 * (Q + 9 * X2 + 9 * X1 + X0) := by
    rw [hAA]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, DAA θ := integral_le_of_ae hae_nnAA hDAAint haeAA
      _ = 4 * (Q + 9 * X2 + 9 * X1 + X0) := hDAAval
  -- ==== A4 ====
  set DA4 : ℝ → ℝ := fun θ => 3 *
      ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) with hDA4
  have hDA4int : MeasureTheory.IntegrableOn DA4 Work.Spaces.Iθ := by
    rw [hDA4]
    exact (((hIntAAint.add (hIntJ2.const_mul 36))).add hB).const_mul 3
  have hae_nnA4 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      0 ≤ (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
    exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ)
  have haeA4 : (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] DA4 := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθm, eqn_deriv2_ae hu hode] with θ hθ heqn
    have hw : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := rpow4_nonneg_rp γ hθ
    have hsq : (deriv (deriv (deriv (deriv u))) θ) ^ 2
        ≤ 3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
            + 36 * (deriv (deriv u) θ) ^ 2 + (deriv (deriv g) θ) ^ 2) := by
      rw [heqn]
      nlinarith [sq_sub_sub_le_three (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ)
        (6 * deriv (deriv u) θ) (deriv (deriv g) θ)]
    rw [hDA4]
    calc (deriv (deriv (deriv (deriv u))) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
            + 36 * (deriv (deriv u) θ) ^ 2 + (deriv (deriv g) θ) ^ 2)) *
          Real.rpow (Real.sin (2 * θ)) (4 - γ) := mul_le_mul_of_nonneg_right hsq hw
      _ = 3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by ring
  have hA4cmp : A4 ≤ 3 * (AA + 36 * J2 + B2) := by
    rw [hA4]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (deriv (deriv u))) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, DA4 θ := integral_le_of_ae hae_nnA4 hDA4int haeA4
      _ = 3 * (AA + 36 * J2 + B2) := by
        have hIAA : MeasureTheory.Integrable
            (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ))
            (volume.restrict Work.Spaces.Iθ) := hIntAAint
        have hE : MeasureTheory.Integrable
            (fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (4 - γ)
                + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
            (volume.restrict Work.Spaces.Iθ) := hIAA.add (hIJ2.const_mul 36)
        have hE' : MeasureTheory.Integrable
            (fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
            (volume.restrict Work.Spaces.Iθ) := hIBi
        have hF : MeasureTheory.Integrable
            (fun θ => 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
            (volume.restrict Work.Spaces.Iθ) := hIJ2.const_mul 36
        rw [hDA4, MeasureTheory.integral_const_mul 3]
        rw [MeasureTheory.integral_add
          (f := fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ)
              + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
          (g := fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
          hE hE']
        rw [MeasureTheory.integral_add
          (f := fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ))
          (g := fun θ => 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
          hIAA hF]
        rw [MeasureTheory.integral_const_mul 36, hAA, hJ2, hB2]
  -- ==== the simple comparisons ====
  have hX1cmp : X1 ≤ Bv1 := by
    rw [hX1]
    calc (∫ θ in Work.Spaces.Iθ,
          (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
            hIntV1
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_le_mul_of_nonneg_right
                (sin_mul_sq_le_sq θ (deriv (fun t => u t / Real.cos t) θ))
                (rpow4_nonneg_rp γ hθ))
      _ = Bv1 := hBv1.symm
  have hX0eq : X0 = J0 := by
    rw [hX0, hJ0]
    exact MeasureTheory.integral_congr_ae (by
      filter_upwards [cos_mul_ae (u := u)] with θ h
      rw [h])
  have hJ0le : J0 ≤ A0 := by
    rw [hJ0]
    calc (∫ θ in Work.Spaces.Iθ,
          (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
            h0
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              simpa using mul_le_mul_of_nonneg_left (rpow4_le_one_rp γ hγ1 hγ2 hθ)
                (sq_nonneg (u θ)))
      _ = A0 := hA0.symm
  have hJ1le : J1 ≤ A1 := by
    rw [hJ1]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow2_nonneg_rp γ hθ))
            h1
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              simpa using mul_le_mul_of_nonneg_left (rpow2_le_one_rp γ hγ1 hγ2 hθ)
                (sq_nonneg (deriv u θ)))
      _ = A1 := hA1.symm
  have hJ2le : J2 ≤ A2 := by
    rw [hJ2]
    calc (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
          integral_le_of_ae
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
            h2
            (by
              filter_upwards [MeasureTheory.ae_restrict_mem hIθm] with θ hθ
              exact mul_le_mul_of_nonneg_left (rpow4_le_sEta_rp γ hγ1 hγ2 hθ)
                (sq_nonneg (deriv (deriv u) θ)))
      _ = A2 := hA2.symm
  -- ==== nonnegativity and elementary bounds ====
  have hA0nn : 0 ≤ A0 := by
    rw [hA0]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ _ => sq_nonneg _)
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ _ => sq_nonneg _)
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (by
        rw [Work.FTS.EllipticEst.sEta]
        exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have hA3nn : 0 ≤ A3 := by
    rw [hA3]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (rpow2_nonneg_rp γ hθ))
  have hB2nn : 0 ≤ B2 := by
    rw [hB2]
    exact MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (rpow4_nonneg_rp γ hθ))
  have hA0le : A0 ≤ R := by rw [hR]; linarith [hA1nn, hA2nn, hA3nn, hB2nn]
  have hA1le : A1 ≤ R := by rw [hR]; linarith [hA0nn, hA2nn, hA3nn, hB2nn]
  have hA2le : A2 ≤ R := by rw [hR]; linarith [hA0nn, hA1nn, hA3nn, hB2nn]
  have hA3le : A3 ≤ R := by rw [hR]; linarith [hA0nn, hA1nn, hA2nn, hB2nn]
  have hB2le : B2 ≤ R := by rw [hR]; linarith [hA0nn, hA1nn, hA2nn, hA3nn]
  -- ==== the final arithmetic ====
  have hV0b : V0 ≤ C0 * R := hC0b
  have hBv1b : Bv1 ≤ C1 * R := hC1b
  have hG1b : G1 ≤ C3 * R := hC3b
  have hQb : Q ≤ 16 * (16 + 225 + C0 + 9 * C3) * R := by
    linarith [hQcmp, hA3le, hJ1le, hA1le, hV0b, hG1b]
  have hAAb : AA ≤ 4 * (16 * (16 + 225 + C0 + 9 * C3) + 27 * (2 + 4 * C1) + 9 * C1 + 1) * R := by
    linarith [hAAcmp, hQb, hX2cmp, hX1cmp, hBv1b, hX0eq, hJ2le, hJ0le, hA0le, hA1le, hA2le]
  have hA4b : A4 ≤ 3 * (4 * (16 * (16 + 225 + C0 + 9 * C3) + 27 * (2 + 4 * C1) + 9 * C1 + 1) + 37) * R := by
    linarith [hA4cmp, hAAb, hJ2le, hA2le, hB2le]
  exact hA4b

end Work.FTS.EllipticEst.Cores
