import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamLeftW
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamRightW
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.ibpSurr
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.csThEta
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.integralSqSub
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypBundle
import Submission.Work.FTS.EllipticEst.AngAWeak.corrSlice_limits
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Auxiliary facts -/

/-- `Icc a b` and `Ioo a b` agree almost everywhere. -/
lemma tvc_ae_eq_Icc_Ioo (a b : ℝ) : Set.Icc a b =ᵐ[volume] Set.Ioo a b := by
  have h0 : volume (Set.Icc a b \ Set.Ioo a b) = 0 := by
    have hsub : Set.Icc a b \ Set.Ioo a b ⊆ ({a, b} : Set ℝ) := by
      rintro x ⟨hx, hx'⟩
      rw [Set.mem_Icc] at hx
      rw [Set.mem_Ioo] at hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hxa : x = a
      · exact Or.inl hxa
      · by_cases hxb : x = b
        · exact Or.inr hxb
        · exfalso
          exact hx' ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    exact measure_mono_null hsub (Set.Finite.measure_zero (by simp) volume)
  have hmem : ∀ᵐ x : ℝ, x ∉ (Set.Icc a b \ Set.Ioo a b) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using h0
  filter_upwards [hmem] with x hx
  rw [Set.mem_sdiff] at hx
  exact propext ⟨fun h1 => by
      by_contra h2
      exact hx ⟨h1, h2⟩,
    fun h1 => ⟨le_of_lt h1.1, le_of_lt h1.2⟩⟩

lemma tvc_ae_eq_Iθ_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  simpa only [Work.Spaces.Iθ] using tvc_ae_eq_Icc_Ioo 0 (Real.pi / 2)

lemma tvc_integrableOn_Iθ_of_Ioo {g : ℝ → ℝ}
    (h : IntegrableOn g (Set.Ioo 0 (Real.pi / 2))) : IntegrableOn g Work.Spaces.Iθ := by
  rw [IntegrableOn] at h ⊢
  rwa [Measure.restrict_congr_set tvc_ae_eq_Iθ_Ioo]

lemma tvc_setIntegral_Iθ_eq_Ioo (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in Set.Ioo 0 (Real.pi / 2), g θ :=
  MeasureTheory.setIntegral_congr_set tvc_ae_eq_Iθ_Ioo

lemma tvc_integrableOn_Ioo_of_Iθ {g : ℝ → ℝ}
    (h : IntegrableOn g Work.Spaces.Iθ) : IntegrableOn g (Set.Ioo 0 (Real.pi / 2)) := by
  rw [IntegrableOn] at h ⊢
  rwa [← Measure.restrict_congr_set tvc_ae_eq_Iθ_Ioo]

/-- The weight is a.e. strongly measurable on `Iθ` (it is continuous on the open interval). -/
lemma tvc_aesm_thEta :
    AEStronglyMeasurable Work.FTS.EllipticEst.thEta (volume.restrict Work.Spaces.Iθ) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hcont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo 0 (Real.pi / 2)) := by
    refine hsin.rpow_const ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  rw [Measure.restrict_congr_set tvc_ae_eq_Iθ_Ioo]
  exact hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioo

lemma tvc_integrableOn_thEta_Iθ :
    IntegrableOn Work.FTS.EllipticEst.thEta Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.integrableOn_thEta.1

/-! ## The scale -/

/-- The scale of the surrogate: `L⁴ = P / (16 (P + E))`. -/
noncomputable def sScale (P E : ℝ) : ℝ := Real.sqrt (Real.sqrt (P / (16 * (P + E))))

lemma sScale_nonneg (P E : ℝ) : 0 ≤ sScale P E := Real.sqrt_nonneg _

lemma sScale_pos {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) : 0 < sScale P E := by
  have h1 : 0 < P / (16 * (P + E)) := by
    apply div_pos hP
    nlinarith
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h1)

lemma sScale_sq (P E : ℝ) : sScale P E ^ 2 = Real.sqrt (P / (16 * (P + E))) := by
  rw [sScale, Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma sScale_pow4 {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ 4 = P / (16 * (P + E)) := by
  have h1 : 0 ≤ P / (16 * (P + E)) := by
    apply div_nonneg hP.le
    nlinarith
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sScale_sq, Real.sq_sqrt h1]

lemma sScale_rpow_four {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (4 : ℝ) = P / (16 * (P + E)) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sScale_pow4 hP hE

lemma sScale_le_half {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) : sScale P E ≤ 1 / 2 := by
  have h1 : P / (16 * (P + E)) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by nlinarith : (0:ℝ) < 16 * (P + E))]
    nlinarith
  have h2 : (0 : ℝ) ≤ P / (16 * (P + E)) := by
    apply div_nonneg hP.le; nlinarith
  calc sScale P E = Real.sqrt (Real.sqrt (P / (16 * (P + E)))) := rfl
    _ ≤ Real.sqrt (Real.sqrt (1 / 16)) := by
        apply Real.sqrt_le_sqrt
        apply Real.sqrt_le_sqrt
        exact h1
    _ = 1 / 2 := by
        rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
          show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma sScale_mul_A {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (3 + Work.Spaces.eta) * sScale P E ^ (1 - Work.Spaces.eta)
      = sScale P E ^ (4 : ℝ) := by
  rw [← Real.rpow_add (sScale_pos hP hE)]
  congr 1
  ring

lemma sScale_mul_B {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (Work.Spaces.eta - 1) * sScale P E ^ (1 - Work.Spaces.eta) = 1 := by
  rw [← Real.rpow_add (sScale_pos hP hE),
    show Work.Spaces.eta - 1 + (1 - Work.Spaces.eta) = 0 by ring,
    Real.rpow_zero (sScale P E)]

lemma sScale_mul_C {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (-(3 + Work.Spaces.eta)) * sScale P E ^ (3 + Work.Spaces.eta) = 1 := by
  rw [← Real.rpow_add (sScale_pos hP hE),
    show -(3 + Work.Spaces.eta) + (3 + Work.Spaces.eta) = 0 by ring,
    Real.rpow_zero (sScale P E)]

lemma sScale_inv_four {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (-4 : ℝ) = 16 * (P + E) / P := by
  have h4 : sScale P E ^ (4 : ℝ) = P / (16 * (P + E)) := sScale_rpow_four hP hE
  rw [show (-4 : ℝ) = -(4 : ℝ) by ring, Real.rpow_neg (le_of_lt (sScale_pos hP hE)), h4]
  try field_simp
  try ring

lemma sScale_mul_D {P E : ℝ} (hP : 0 < P) (hE : 0 ≤ E) :
    sScale P E ^ (-(3 + Work.Spaces.eta)) * sScale P E ^ (Work.Spaces.eta - 1)
      = 16 * (P + E) / P := by
  rw [← Real.rpow_add (sScale_pos hP hE),
    show -(3 + Work.Spaces.eta) + (Work.Spaces.eta - 1) = -4 by ring]
  exact sScale_inv_four hP hE

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
lemma tvc_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
  apply Real.sqrt_le_sqrt
  rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (Real.sqrt a - Real.sqrt b),
    Real.sq_sqrt (mul_nonneg ha hb)]

/-- `√(P (P + E)) ≤ P + √(P E)` for `P, E ≥ 0`. -/
lemma tvc_sqrt_mul_le {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    Real.sqrt (P * (P + E)) ≤ P + Real.sqrt (P * E) := by
  have h1 : P * (P + E) = P ^ 2 + P * E := by ring
  calc Real.sqrt (P * (P + E)) = Real.sqrt (P ^ 2 + P * E) := by rw [h1]
    _ ≤ Real.sqrt (P ^ 2) + Real.sqrt (P * E) :=
        tvc_sqrt_add_le (sq_nonneg P) (mul_nonneg hP hE)
    _ = P + Real.sqrt (P * E) := by rw [Real.sqrt_sq hP]

end

end Work.EllipticEst.Core.i0Aux
