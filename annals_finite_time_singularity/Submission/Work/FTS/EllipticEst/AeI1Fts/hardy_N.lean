import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_slice_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.H2W.SlotA.weightedNLePp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/hardy_N` — the sharp weighted Hardy bound of `I₁`, integrated in `z`

The slicewise sharp bound `hardy_slice_ae` (constant `(1+η)^{-2}`, from
`H2W.SlotA.sharpHardyCosWeight_open`) is integrated against the radial weight `w(z)²`.

Because the `z`-uniform version `weightedNLePp` needs the slice integrability for *every*
`z ∈ Iz` (which is not available), the integration is done here directly, with the standard
`by_cases` on the `z`-integrability of the weighted `N`-energy: in the integrable case
`integral_mono_ae` applies, and in the non-integrable case the totalised integral is `0` and
the right-hand side is non-negative.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- Elementary coefficient step.  From the sharp slicewise bound
`A ≤ (1+η)⁻² B` with `η > 0` one gets `2η(1+η) A ≤ (2η/(1+η)) B`: multiplying the
hypothesis by `(1+η)² > 0` gives `(1+η)² A ≤ B`, and
`2η(1+η) = (2η/(1+η))·(1+η)²`. -/
private theorem coef_step {η A B : ℝ} (hη : 0 < η)
    (h : A ≤ (1 / (1 + η) ^ 2) * B) :
    2 * η * (1 + η) * A ≤ (2 * η / (1 + η)) * B := by
  have h1 : (0 : ℝ) < 1 + η := by linarith
  have hgoal : (1 + η) ^ 2 * A ≤ B := by
    have h5 : (1 + η) ^ 2 * ((1 / (1 + η) ^ 2) * B) = B := by
      rw [one_div, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt h1)), one_mul]
    calc (1 + η) ^ 2 * A ≤ (1 + η) ^ 2 * ((1 / (1 + η) ^ 2) * B) :=
          mul_le_mul_of_nonneg_left h (pow_nonneg h1.le 2)
      _ = B := h5
  have hcoef : 2 * η * (1 + η) * A = (2 * η / (1 + η)) * ((1 + η) ^ 2 * A) := by
    field_simp
  calc 2 * η * (1 + η) * A = (2 * η / (1 + η)) * ((1 + η) ^ 2 * A) := hcoef
    _ ≤ (2 * η / (1 + η)) * B := by
        apply mul_le_mul_of_nonneg_left hgoal
        positivity

theorem hardy_N {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u)) :
    2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
        * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sig2 θ)
      ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta))
          * (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
              * ∫ θ in Set.Ioo 0 (Real.pi / 2),
                  (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
                    * Work.FTS.EllipticEst.AeI1Fts.sigE θ) := by
  -- the a.e.-in-`z` sharp slicewise Hardy bound
  have hsl := hardy_slice_ae h hU hV
  -- integrability of the `w²`-weighted `V`-energy of the slice, from `hV`
  have hBint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)
      (Set.Ioi 0) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (V u) z θ)
        Work.Spaces.Iz := hV.2
    have h2 : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (V u z θ) ^ 2 * sigE θ)
        Work.Spaces.Iz := by
      refine MeasureTheory.IntegrableOn.congr_fun h1 (fun z _ => ?_) measurableSet_Ici
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [hkIntegrand_zero_eq_of_mem α (V u) hθ]
      ring
    have h3 : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)
        Work.Spaces.Iz := by
      refine MeasureTheory.IntegrableOn.congr_fun h2 (fun z _ => ?_) measurableSet_Ici
      congr 1
      exact (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))).symm
    exact h3.mono_set (fun z hz =>
      show z ∈ Work.Spaces.Iz from Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz)))
  -- non-negativity of the right-hand side
  have hBnn : 0 ≤ ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
      * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun z _ =>
      mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun θ hθ => mul_nonneg (sq_nonneg _) (by
          rw [sigE]
          exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos])) _))))
  by_cases hInt : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
        (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ) (Set.Ioi 0)
  · have hle : (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
          (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun z => (1 / (1 + Work.Spaces.eta) ^ 2)
          * ((Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ)) := by
      filter_upwards [hsl] with z hz
      calc (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo,
            (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ
          ≤ (Work.Spaces.w z) ^ 2
              * ((1 / (1 + Work.Spaces.eta) ^ 2)
                  * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) :=
            mul_le_mul_of_nonneg_left hz (sq_nonneg _)
        _ = (1 / (1 + Work.Spaces.eta) ^ 2)
              * ((Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ) := by ring
    have h2 : MeasureTheory.IntegrableOn
        (fun z => (1 / (1 + Work.Spaces.eta) ^ 2)
          * ((Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, (V u z θ) ^ 2 * sigE θ))
        (Set.Ioi 0) := hBint.const_mul _
    have hkey := MeasureTheory.integral_mono_ae hInt h2 hle
    rw [MeasureTheory.integral_const_mul] at hkey
    exact coef_step Work.Spaces.eta_pos hkey
  · rw [MeasureTheory.integral_undef hInt, mul_zero]
    have hd : 0 ≤ 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) :=
      div_nonneg (by linarith [Work.Spaces.eta_pos]) (by linarith [Work.Spaces.eta_pos])
    exact mul_nonneg hd hBnn

end

end Work.FTS.EllipticEst.AeI1Fts
