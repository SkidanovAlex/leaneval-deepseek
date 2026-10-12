import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.LocRepoint.ConvDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.LocRepoint.convScale_cube_lower`

`convScale ℓ z = (χ⋆χ)(z/ℓ) = ∫_y χ(y)·χ(z/ℓ − y)`.  Since `χ = 1/√chiNormSq`
identically on the ball `‖·‖ ≤ 1/4` (`CubicChi.chiBase_eq_one_of_norm_le`), any
cube of half-side `t` contained in the intersection
`ball (−z/(2ℓ), 1/4) ∩ ball (z/(2ℓ), 1/4)` contributes `(2t)³/chiNormSq` to the
convolution integral.  For `‖z‖ ≤ R < ℓ/2` the cube of half-side
`t = (1/4 − R/(2ℓ))/(2√3)` centred at `z/(2ℓ)` does the job, which is exactly
the explicit constant `convCubeLower ℓ R`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real Convolution

namespace Work.LocRepoint

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- The coordinate cube of half-side `t` in `ℝ³` has volume `(2t)³`. -/
private lemma volume_cube_ofLp {t : ℝ} (ht : 0 ≤ t) :
    (volume {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}) = ENNReal.ofReal ((2 * t) ^ 3) := by
  let C : Set (Fin 3 → ℝ) := {f | ∀ i : Fin 3, |f i| ≤ t}
  have hpre : {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t} = WithLp.ofLp ⁻¹' C := by
    ext y; rfl
  rw [hpre]
  have hCpi : C = Set.univ.pi (fun _ : Fin 3 => Set.Icc (-t) t) := by
    ext f
    simp [C, Set.mem_Icc, abs_le, Pi.le_def, forall_and]
  have hCmeas : MeasurableSet C := by
    rw [hCpi]
    exact MeasurableSet.pi (Set.countable_univ) (fun _ _ => measurableSet_Icc)
  rw [MeasureTheory.MeasurePreserving.measure_preimage
      (PiLp.volume_preserving_ofLp (Fin 3)) hCmeas.nullMeasurableSet]
  rw [hCpi, MeasureTheory.volume_pi_pi]
  have hI : ∀ _i : Fin 3, (volume (Set.Icc (-t) t)) = ENNReal.ofReal (2 * t) := by
    intro i
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i _ => hI i)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * t)]

/-- The coordinate cube of half-side `t` in `ℝ³` is measurable. -/
private lemma measurableSet_cube_ofLp (t : ℝ) :
    MeasurableSet {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t} := by
  have hpre : {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}
      = WithLp.ofLp ⁻¹' {f : Fin 3 → ℝ | ∀ i : Fin 3, |f i| ≤ t} := by
    ext y; rfl
  rw [hpre]
  refine MeasurableSet.preimage ?_ (WithLp.measurable_ofLp 2 (Fin 3 → ℝ))
  have hCpi : {f : Fin 3 → ℝ | ∀ i : Fin 3, |f i| ≤ t}
      = Set.univ.pi (fun _ : Fin 3 => Set.Icc (-t) t) := by
    ext f
    simp [Set.mem_Icc, abs_le, Pi.le_def, forall_and]
  rw [hCpi]
  exact MeasurableSet.pi (Set.countable_univ) (fun _ _ => measurableSet_Icc)

theorem convScale_cube_lower {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : R < ℓ / 2) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : ‖z‖ ≤ R) :
    Work.LocRepoint.convCubeLower ℓ R ≤ Submission.BoseGases.convScale ℓ z := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  -- `R/(2ℓ) < 1/4` and hence `t > 0`
  have hR2 : R / (2 * ℓ) < 1 / 4 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ℓ)]
    linarith
  set t : ℝ := (1 / 4 - R / (2 * ℓ)) / (2 * Real.sqrt 3) with ht_def
  have htpos : 0 < t := by
    rw [ht_def]
    exact div_pos (by linarith) (by positivity)
  have hsqrt3t : Real.sqrt 3 * t = (1 / 4 - R / (2 * ℓ)) / 2 := by
    rw [ht_def]; field_simp; try ring
  have hsqrt3t' : Real.sqrt 3 * t = 1 / 8 - R / (4 * ℓ) := by
    rw [hsqrt3t]; field_simp; try ring
  -- norm of `z/ℓ` and of `c := z/(2ℓ)`
  have hxnorm : ‖(ℓ⁻¹) • z‖ ≤ R / ℓ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hℓ)), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hz (le_of_lt hℓ)
  set c : ℝ³ := (1 / 2 : ℝ) • ((ℓ⁻¹) • z) with hc_def
  have hcnorm : ‖c‖ ≤ R / (2 * ℓ) := by
    rw [hc_def, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc (1 / 2) * ‖(ℓ⁻¹) • z‖ ≤ (1 / 2) * (R / ℓ) :=
          mul_le_mul_of_nonneg_left hxnorm (by norm_num)
      _ = R / (2 * ℓ) := by ring
  have hR4 : R / (4 * ℓ) < 1 / 8 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ℓ)]
    linarith
  have hkey : R / (2 * ℓ) + Real.sqrt 3 * t < 1 / 4 := by
    rw [hsqrt3t']
    have h2 : R / (2 * ℓ) = 2 * (R / (4 * ℓ)) := by ring
    rw [h2]
    linarith
  -- points of the cube stay inside `ball (−c, 1/4)` and `ball (c, 1/4)`
  have hw_norm : ∀ w : ℝ³, (∀ i : Fin 3, |w.ofLp i| ≤ t) → ‖w‖ ≤ Real.sqrt 3 * t := by
    intro w hw
    have h2 : ‖w‖ ^ 2 ≤ (Real.sqrt 3 * t) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hsum : ∑ i : Fin 3, ‖w.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, t ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : ‖w.ofLp i‖ ≤ t := by rw [Real.norm_eq_abs]; exact hw i
        nlinarith [norm_nonneg (w.ofLp i), htpos.le]
      calc ∑ i : Fin 3, ‖w.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, t ^ 2 := hsum
        _ = (Real.sqrt 3 * t) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
              ring
    have hbnn : 0 ≤ Real.sqrt 3 * t := mul_nonneg hsqrt3pos.le htpos.le
    simpa [abs_of_nonneg (norm_nonneg w), abs_of_nonneg hbnn] using (sq_le_sq.mp h2)
  have hbound : ∀ w : ℝ³, (∀ i : Fin 3, |w.ofLp i| ≤ t) →
      ‖c + w‖ ≤ 1 / 4 ∧ ‖c - w‖ ≤ 1 / 4 := by
    intro w hw
    have hwn := hw_norm w hw
    have h1 : ‖c + w‖ ≤ R / (2 * ℓ) + Real.sqrt 3 * t :=
      (norm_add_le c w).trans (add_le_add hcnorm hwn)
    have h2 : ‖c - w‖ ≤ R / (2 * ℓ) + Real.sqrt 3 * t := by
      have h := norm_add_le c (-w)
      rw [sub_eq_add_neg]
      exact h.trans (add_le_add hcnorm (by rw [norm_neg]; exact hwn))
    exact ⟨h1.trans hkey.le, h2.trans hkey.le⟩
  -- the value of the integrand on the cube
  have hchi : ∀ w : ℝ³, (∀ i : Fin 3, |w.ofLp i| ≤ t) →
      chi (c + w) * chi (c - w) = 1 / chiNormSq := by
    intro w hw
    obtain ⟨h1, h2⟩ := hbound w hw
    have e1 : chi (c + w) = 1 / Real.sqrt chiNormSq := by
      rw [chi, chiBase_eq_one_of_norm_le h1]
    have e2 : chi (c - w) = 1 / Real.sqrt chiNormSq := by
      rw [chi, chiBase_eq_one_of_norm_le h2]
    rw [e1, e2, div_mul_div_comm, one_mul,
      div_eq_div_iff (mul_ne_zero chi_sqrt_ne_zero chi_sqrt_ne_zero) chiNormSq_ne_zero,
      one_mul, one_mul, Real.mul_self_sqrt chiNormSq_pos.le]
  have hSmeas : MeasurableSet {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t} :=
    measurableSet_cube_ofLp t
  have hvolS : volume {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}
      = ENNReal.ofReal ((2 * t) ^ 3) := volume_cube_ofLp htpos.le
  -- integrability and the truncation inequality
  have hcont : Continuous (fun w : ℝ³ => chi (c + w) * chi (c - w)) :=
    (chi_continuous.comp (continuous_const.add continuous_id)).mul
      (chi_continuous.comp (continuous_const.sub continuous_id))
  have hcs : HasCompactSupport (fun w : ℝ³ => chi (c + w) * chi (c - w)) := by
    have h1 : HasCompactSupport (fun w : ℝ³ => chi (c + w)) :=
      chi_hasCompactSupport.comp_homeomorph (Homeomorph.addLeft c)
    have h2 : HasCompactSupport (fun w : ℝ³ => chi (c - w)) :=
      chi_hasCompactSupport.comp_homeomorph (Homeomorph.subLeft c)
    exact HasCompactSupport.mul_right h1
  have hint : Integrable (fun w : ℝ³ => chi (c + w) * chi (c - w)) volume :=
    hcont.integrable_of_hasCompactSupport hcs
  have hmain : ∫ w in {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}, chi (c + w) * chi (c - w)
      ≤ ∫ w : ℝ³, chi (c + w) * chi (c - w) :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall
      (fun w => mul_nonneg (chi_nonneg _) (chi_nonneg _)))
  have hval : ∫ w in {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}, chi (c + w) * chi (c - w)
      = (2 * t) ^ 3 / chiNormSq := by
    have hcongr : ∫ w in {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}, chi (c + w) * chi (c - w)
        = ∫ w in {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}, (1 / chiNormSq) :=
      setIntegral_congr_fun hSmeas (fun w hw => hchi w hw)
    rw [hcongr, setIntegral_const, MeasureTheory.measureReal_def, hvolS,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 * t) ^ 3)]
    rw [smul_eq_mul, one_div, div_eq_mul_inv]
  -- the substitution `y = c + w` and the identity `z/ℓ − c = c`
  have hconv : convScale ℓ z = ∫ w : ℝ³, chi (c + w) * chi (c - w) := by
    rw [convScale, conv3,
      ← integral_comp_add_left (fun y : ℝ³ => chi y * chi ((ℓ⁻¹) • z - y)) c]
    apply integral_congr_ae
    filter_upwards with w
    have hx : (ℓ⁻¹) • z - (c + w) = c - w := by
      rw [hc_def]; module
    rw [hx]
  calc convCubeLower ℓ R = (2 * t) ^ 3 / chiNormSq := by
        rw [convCubeLower, ← ht_def]
    _ = ∫ w in {y : ℝ³ | ∀ i : Fin 3, |y.ofLp i| ≤ t}, chi (c + w) * chi (c - w) :=
        hval.symm
    _ ≤ ∫ w : ℝ³, chi (c + w) * chi (c - w) := hmain
    _ = convScale ℓ z := hconv.symm

end Work.LocRepoint
