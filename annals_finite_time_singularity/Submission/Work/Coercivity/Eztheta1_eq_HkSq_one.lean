/-
# `E_{z,θ}¹ = |f|²_{H¹}`

The paper's energy `E_{z,θ}¹ = |D_zf·w/√(sin 2θ^η)|² + |D_θf·w/√(sin 2θ^γ)|²
+ |f·w/√(sin 2θ^η)|²` is by definition the sum of the squared weighted `L²`-norms of
the three first-order weighted derivatives, which are exactly the summands of
`HkIntegrand α 1 f`.  The proof therefore

1. splits the pointwise `H¹`-integrand into its three summands (`hkIntegrand_one_split`);
2. splits the iterated integral of a sum of three honest functions
   (`iterated_integral_add3`), using the integrability of each summand
   (`L2Mem_DzIter_Hwt`, `L2Mem_mixed_Wt_gen`), which is inherited from `HkMem α 1 f`
   by summing over the (nonnegative) terms of the `H¹`-integrand;
3. identifies each `L²Sq` with the corresponding energy (`L2Sq_U0_eq_EfEta`,
   `L2Sq_U1_eq_EDz`, `L2Sq_U2_eq_EDth`), an elementary pointwise comparison of
   `w/sin(2θ)^{η/2}` with `w·sin(2θ)^{-η/2}`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EzDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HProductRule_Zsummand
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## 1. The pointwise split of the `H¹`-integrand -/

theorem hkIntegrand_one_split (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.HkIntegrand α 1 f z θ
      = (U0 f z θ) ^ 2 + (U1 f z θ) ^ 2 + (U2 α f z θ) ^ 2 := by
  simp only [Spaces.HkIntegrand, U0, U1, U2, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! ## 2. Additivity of the iterated integral -/

/-- The iterated integral over `[0,∞) × [0,π/2]` of a sum of three honest integrands
splits into the sum of the iterated integrals. -/
theorem iterated_integral_add3 {A B C : ℝ → ℝ → ℝ}
    (hA : I2Mem A) (hB : I2Mem B) (hC : I2Mem C) :
    (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
      = (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, A z θ)
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, B z θ)
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, C z θ) := by
  have hinner : Set.EqOn
      (fun z => ∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
      (fun z => (∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)
        + (∫ θ in Spaces.Iθ, C z θ)) Spaces.Iz := by
    intro z hz
    change (∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
        = (∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ) + (∫ θ in Spaces.Iθ, C z θ)
    have e1 : (∫ θ in Spaces.Iθ, (A z θ + B z θ + C z θ))
        = (∫ θ in Spaces.Iθ, (A z θ + B z θ)) + (∫ θ in Spaces.Iθ, C z θ) :=
      MeasureTheory.integral_add ((hA.1 z hz).add (hB.1 z hz)) (hC.1 z hz)
    have e2 : (∫ θ in Spaces.Iθ, (A z θ + B z θ))
        = (∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ) :=
      MeasureTheory.integral_add (hA.1 z hz) (hB.1 z hz)
    rw [e1, e2]
  rw [MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici hinner]
  have f1 : (∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)
        + (∫ θ in Spaces.Iθ, C z θ)))
      = (∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)))
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, C z θ) :=
    MeasureTheory.integral_add ((hA.2).add (hB.2)) hC.2
  have f2 : (∫ z in Spaces.Iz, ((∫ θ in Spaces.Iθ, A z θ) + (∫ θ in Spaces.Iθ, B z θ)))
      = (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, A z θ)
        + (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, B z θ) :=
    MeasureTheory.integral_add hA.2 hB.2
  rw [f1, f2]

/-- `L2Mem` for the pure `D_z`-summand of `HkIntegrand`. -/
theorem L2Mem_DzIter_Hwt (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hsm : Spaces.SmoothNbhd f) (hmem : Spaces.HkMem α k f) (b : ℕ) (hb : b ≤ k) :
    Spaces.L2Mem (fun z θ => Spaces.DzIter b f z θ
      * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) := by
  constructor
  · intro z hz
    refine Integrable.mono' (hmem.1 z hz)
      ((Spaces.HPRZ.aesm_DzIter_H_weight_slice f hsm b hz).pow 2) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)]
      with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Spaces.sq_le_HkIntegrand_z α k f z θ b hb
  · have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Spaces.DzIter b f p.1 p.2
          * (Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Spaces.eta / 2))) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
      (Spaces.HPRZ.aesm_DzIter_H_weight_prod f hsm b).pow 2
    refine Integrable.mono' hmem.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => Spaces.sq_le_HkIntegrand_z α k f z θ b hb))

/-- `L2Mem` for the mixed summand of `HkIntegrand`. -/
theorem L2Mem_mixed_Wt_gen (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hsm : Spaces.SmoothNbhd f) (hmem : Spaces.HkMem α k f) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ k) :
    Spaces.L2Mem (fun z θ => Spaces.mixed j i f z θ * Spaces.Wt α z θ) := by
  have hsm' : Spaces.SmoothNbhd (Spaces.mixed j i f) :=
    Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsm i) j
  have hWt_meas : ∀ z : ℝ, Measurable (fun θ : ℝ => Spaces.Wt α z θ) := by
    intro z
    have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.measurable_sin.comp (measurable_const.mul measurable_id)
    have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) :=
      hsin.pow_const _
    have h : Measurable (fun θ : ℝ =>
        Spaces.w z * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) :=
      measurable_const.mul hpow
    simpa only [Spaces.Wt, Spaces.wTheta] using h
  constructor
  · intro z hz
    have hcont : ContinuousOn (fun θ : ℝ => Spaces.mixed j i f z θ) Spaces.Iθ := by
      intro θ hθ
      have hcd : ContDiffAt ℝ ⊤ (Function.uncurry (Spaces.mixed j i f)) (z, θ) :=
        hsm'.contDiffAt (Spaces.isOpen_nbhU.mem_nhds (Spaces.mem_nbhU hz hθ))
      exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt
    have haesm1 : AEStronglyMeasurable (fun θ : ℝ => Spaces.mixed j i f z θ)
        (volume.restrict Spaces.Iθ) :=
      hcont.aestronglyMeasurable (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
    have haesm2 : AEStronglyMeasurable (fun θ : ℝ => Spaces.Wt α z θ)
        (volume.restrict Spaces.Iθ) := (hWt_meas z).aestronglyMeasurable
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (Spaces.mixed j i f z θ * Spaces.Wt α z θ) ^ 2)
        (volume.restrict Spaces.Iθ) := (haesm1.mul haesm2).pow 2
    refine (hmem.1 z hz).mono' haesm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij
  · have hAE : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Spaces.mixed j i f p.1 p.2 * Spaces.Wt α p.1 p.2) ^ 2)
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
      Spaces.aesm_mixed_Wt_sq_prod α f hsm j i
    refine Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij))

/-! ## 3. Identification of the three `L²Sq`'s with the energies -/

theorem L2Sq_U0_eq_EfEta (f : ℝ → ℝ → ℝ) : Spaces.L2Sq (U0 f) = EfEta f := by
  simp only [Spaces.L2Sq, U0, EfEta, wtEta, wtGam, Spaces.DzIter_zero]
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici
    fun z hz => ?_
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iθ) measurableSet_Icc
    fun θ hθ => ?_
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h : Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)
      = Spaces.w z * Real.sin (2 * θ) ^ (-(Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs]
  rw [h]

theorem L2Sq_U1_eq_EDz (f : ℝ → ℝ → ℝ) : Spaces.L2Sq (U1 f) = EDz f := by
  simp only [Spaces.L2Sq, U1, EDz, wtEta, wtGam, Spaces.DzIter_succ, Spaces.DzIter_zero]
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici
    fun z hz => ?_
  refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iθ) measurableSet_Icc
    fun θ hθ => ?_
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h : Spaces.w z / Real.sin (2 * θ) ^ (Spaces.eta / 2)
      = Spaces.w z * Real.sin (2 * θ) ^ (-(Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs]
  rw [h]

theorem L2Sq_U2_eq_EDth (α : ℝ) (f : ℝ → ℝ → ℝ) : Spaces.L2Sq (U2 α f) = EDth α f := rfl

/-! ## 4. Assembly -/

theorem Eztheta1_eq_HkSq_one (α : ℝ) (f : ℝ → ℝ → ℝ) (h : Spaces.HkMem α 1 f)
    (hs : Spaces.SmoothNbhd f) : Eztheta1 α f = Spaces.HkSq α 1 f := by
  have hL0 : Spaces.L2Mem (U0 f) := L2Mem_DzIter_Hwt α 1 f hs h 0 (by norm_num)
  have hL1 : Spaces.L2Mem (U1 f) := L2Mem_DzIter_Hwt α 1 f hs h 1 (by norm_num)
  have hL2 : Spaces.L2Mem (U2 α f) :=
    L2Mem_mixed_Wt_gen α 1 f hs h 1 0 (by norm_num) (by norm_num)
  have hsplit : Spaces.HkSq α 1 f
      = Spaces.L2Sq (U0 f) + Spaces.L2Sq (U1 f) + Spaces.L2Sq (U2 α f) := by
    rw [Spaces.HkSq]
    have h1 : (∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 1 f z θ)
        = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
            ((U0 f z θ) ^ 2 + (U1 f z θ) ^ 2 + (U2 α f z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iz) measurableSet_Ici
        fun z hz => ?_
      refine MeasureTheory.setIntegral_congr_fun (s := Spaces.Iθ) measurableSet_Icc
        fun θ hθ => ?_
      exact hkIntegrand_one_split α f z θ
    rw [h1]
    have hadd := iterated_integral_add3
      (A := fun z θ => (U0 f z θ) ^ 2) (B := fun z θ => (U1 f z θ) ^ 2)
      (C := fun z θ => (U2 α f z θ) ^ 2)
      ((I2Mem_sq_iff (U0 f)).mpr hL0) ((I2Mem_sq_iff (U1 f)).mpr hL1)
      ((I2Mem_sq_iff (U2 α f)).mpr hL2)
    rw [hadd]
    simp only [Spaces.L2Sq]
  rw [hsplit, L2Sq_U0_eq_EfEta, L2Sq_U1_eq_EDz, L2Sq_U2_eq_EDth]
  simp only [Eztheta1]
  ring

end Work.Coercivity
