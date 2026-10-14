import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.PthEVzR
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_MuLamOK.RowReduction
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.one_le_mul_w
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.perTermLow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.Galerkin (Fn)
open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The `α`-conversion `(√(γ-1))⁻¹ = √10 · α^{-1/2}`. -/
theorem inv_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  have hγ : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hs : Real.sqrt (α / 10) = Real.sqrt α / Real.sqrt 10 :=
    Real.sqrt_div' α (by norm_num)
  have hinv : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα.le]
  calc (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = (Real.sqrt (α / 10))⁻¹ := by rw [hγ]
    _ = (Real.sqrt α / Real.sqrt 10)⁻¹ := by rw [hs]
    _ = Real.sqrt 10 / Real.sqrt α := by rw [inv_div]
    _ = Real.sqrt 10 * (Real.sqrt α)⁻¹ := by rw [div_eq_mul_inv]
    _ = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by rw [hinv]

theorem caseLe2Mine : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b i j : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ → i ≤ a → j ≤ b → ¬(i = 0 ∧ j = 0) →
      i + j ≤ 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  set CX : ℝ := max (Cz * Real.sqrt 10) Cm with hCXdef
  have hCXpos : 0 < CX :=
    lt_of_lt_of_le (mul_pos hCzpos (Real.sqrt_pos_of_pos (by norm_num))) (le_max_left _ _)
  refine ⟨CX, hCXpos, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hia hjb hne hcase
  obtain ⟨hsmA, hA4, hA6, hvalA, hn4, hn6⟩ := hcoef
  obtain ⟨hsmf, hf6, hf7, hvanish, haxis, hbdd⟩ := hdat
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hn4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hn6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hK0nn : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hvalA 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
  have hCXnn : 0 ≤ CX := hCXpos.le
  have hCmnn : 0 ≤ Cm := hCmpos.le
  have hCznn : 0 ≤ Cz := hCzpos.le
  have hαnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  obtain ⟨q, rfl, hq0, hqγ, hqη⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leafW_canon_cases hα0 hleaf
  -- ## index bookkeeping
  have hge : 1 ≤ a - i + 1 := by omega
  have hYle : (a - i + 1) + (b - j) ≤ 6 := by omega
  -- ## the two level-`6` dominations of the `f`-slots
  have hY6 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z θ hθ0 hθ1 => canonW_mul_mixed_le6 hα0 hq0 hqγ hge hYle ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hZ6 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z θ hθ0 hθ1 =>
      Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f a b hqγ hqη hab ⟨hθ0, hθ1⟩
  -- ## the AM–GM bound on the product of the two `f`-slots
  have hYZ : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hθ0 hθ1
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have h := two_mul_le_add_sq |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
      |Work.Spaces.mixed b a f z θ|
    rw [sq_abs, sq_abs] at h
    nlinarith [h, hcw, hY6 z θ hθ0 hθ1, hZ6 z θ hθ0 hθ1]
  -- ## the sup bound on the coefficient slot
  have hXsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ CX * α ^ (-(1 / 2 : ℝ)) * K4 := by
    intro z θ hz hθ0 hθ1
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hj2 : j ≤ 2 := by omega
      have h1 : |Work.Spaces.DzIter j A z θ|
          ≤ Cz / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A :=
        hCz α A hα0 hα1 hsmA hA4 j hj2 z θ hz hθ0 hθ1
      have hxn : Work.FTS.Nonlin.Xn α A ≤ K4 := hn4
      calc |Work.Spaces.mixed j 0 A z θ| = |Work.Spaces.DzIter j A z θ| := by
            rw [Work.Spaces.mixed_zero_right]
        _ ≤ Cz / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := h1
        _ = Cz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α A := by
            rw [div_eq_mul_inv, inv_sqrt_gam_sub_one hα0]; ring
        _ ≤ CX * α ^ (-(1 / 2 : ℝ)) * K4 := by
            have h2 : Cz * Real.sqrt 10 ≤ CX := le_max_left _ _
            calc Cz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α A
                ≤ CX * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α A :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hαnn)
                    (Work.Spaces.HkNorm_nonneg α 4 A)
              _ ≤ CX * α ^ (-(1 / 2 : ℝ)) * K4 :=
                  mul_le_mul_of_nonneg_left hxn (mul_nonneg hCXnn hαnn)
    · have hi1 : 1 ≤ i := hipos
      have hij2 : i + j ≤ 2 := by omega
      have h1 : |Work.Spaces.mixed j i A z θ| ≤ Cm * Work.FTS.Nonlin.Xn α A :=
        hCm α A hα0 hα1 hsmA hA4 j i hi1 hij2 z θ hz hθ0 hθ1
      have hhalf : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_alpha_rpow_neg_half hα0 hα1
      have h2 : Cm ≤ CX := le_max_right _ _
      calc |Work.Spaces.mixed j i A z θ| ≤ Cm * Work.FTS.Nonlin.Xn α A := h1
        _ ≤ Cm * K4 := mul_le_mul_of_nonneg_left hn4 hCmnn
        _ = (1 : ℝ) * Cm * K4 := by ring
        _ ≤ α ^ (-(1 / 2 : ℝ)) * Cm * K4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhalf hCmnn) hK4nn
        _ ≤ α ^ (-(1 / 2 : ℝ)) * CX * K4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hαnn) hK4nn
        _ = CX * α ^ (-(1 / 2 : ℝ)) * K4 := by ring
  -- ## the pointwise bound on the full integrand
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        ≤ (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hXs := hXsup z θ hz hθ0 hθ1
    have hYZ' := hYZ z θ hθ0 hθ1
    have hleft : 0 ≤ canonW q z θ
        * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
      mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcst : 0 ≤ CX * α ^ (-(1 / 2 : ℝ)) * K4 := mul_nonneg (mul_nonneg hCXnn hαnn) hK4nn
    calc |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        = |Work.Spaces.mixed j i A z θ| * (canonW q z θ
          * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
      _ ≤ (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul hXs hYZ' hleft hcst
  -- ## integrability
  have hFcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ
      * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
      * Work.Spaces.mixed b a f z θ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (hsmA.mixed j i).continuousOn).mul
      (hsmf.mixed (b - j) (a - i + 1)).continuousOn).mul (hsmf.mixed b a).continuousOn
  have hinter := integrableConjuncts
    (F := fun z θ => canonW q z θ * Work.Spaces.mixed j i A z θ
      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ)
    (H := fun z θ => (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ)
    hFcont
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_const.mul (hsmf.continuousOn_HkIntegrand α 6)))
    (fun θ => by rw [canonW_zero_z]; ring)
    (fun z hz => (hf6.1 z hz).const_mul _)
    (by
      rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ)
          = fun z => (CX * α ^ (-(1 / 2 : ℝ)) * K4)
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ from
            funext (fun z => MeasureTheory.integral_const_mul _ _)]
      exact hf6.2.const_mul _)
    hpt
  refine ⟨hinter.1, hinter.2, ?_⟩
  -- ## the value bound
  have hmargH : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iz := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ)
        = fun z => (CX * α ^ (-(1 / 2 : ℝ)) * K4)
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ from
          funext (fun z => MeasureTheory.integral_const_mul _ _)]
    exact hf6.2.const_mul _
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ := by
        refine integral_Iz_mono_ae (fun z hz => ?_) (fun z hz => abs_nonneg _) hmargH
        exact le_trans MeasureTheory.abs_integral_le_integral_abs
          (integral_Iθ_mono_ae (f := fun θ => |canonW q z θ * Work.Spaces.mixed j i A z θ
              * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|)
            (g := fun θ => (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ)
            (fun θ hθ => hpt z θ (Set.mem_Ioi.mp hz) hθ.1 hθ.2)
            (fun θ hθ => abs_nonneg _)
            ((hf6.1 z (Set.mem_Ici.mpr hz.le)).const_mul _))
    _ = (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkSq α 6 f := by
        rw [Work.Spaces.HkSq]
        rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
              (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkIntegrand α 6 f z θ)
            = fun z => (CX * α ^ (-(1 / 2 : ℝ)) * K4)
              * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ from
              funext (fun z => MeasureTheory.integral_const_mul _ _)]
        rw [MeasureTheory.integral_const_mul]
    _ ≤ CX * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
        have hbr : K4 * Work.Spaces.HkSq α 6 f
            ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
          have h4 : K4 ≤ 1 + K0 + K4 := by linarith
          have h5 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
          have hnn : (0 : ℝ) ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
            positivity
          calc K4 * Work.Spaces.HkSq α 6 f ≤ (1 + K0 + K4) * Work.Spaces.HkSq α 6 f :=
                mul_le_mul_of_nonneg_right h4 hSq6nn
            _ ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
                mul_le_mul_of_nonneg_left h5 (by linarith)
            _ ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                  + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by linarith
        have h1 : (CX * α ^ (-(1 / 2 : ℝ)) * K4) * Work.Spaces.HkSq α 6 f
            = CX * α ^ (-(1 / 2 : ℝ)) * (K4 * Work.Spaces.HkSq α 6 f) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_left hbr (mul_nonneg hCXnn hαnn)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.perTermMid =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.Galerkin (Fn)
open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- From `u² ≤ c²v²`, `0 ≤ c`, `0 ≤ v` conclude `|u| ≤ c v`. -/
theorem abs_le_of_sq_le_nn' {u c v : ℝ} (h : u ^ 2 ≤ c ^ 2 * v ^ 2) (hc : 0 ≤ c)
    (hv : 0 ≤ v) : |u| ≤ c * v := by
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg hc hv)
  rw [mul_pow]
  exact h

theorem caseTo4Mine : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b i j : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ → i ≤ a → j ≤ b → ¬(i = 0 ∧ j = 0) →
      3 ≤ i + j → i + j ≤ 4 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Cp, hCppos, hCp⟩ := Work.FTS.StrongPersist.N6.PwAny6
  set CB : ℝ := Real.sqrt (Cp * 10) + 1 with hCBdef
  have hCBpos : 0 < CB := by rw [hCBdef]; positivity
  refine ⟨CB, hCBpos, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hia hjb hne h3 h4
  obtain ⟨hsmA, hA4, hA6, hvalA, hn4, hn6⟩ := hcoef
  obtain ⟨hsmf, hf6, hf7, hvanish, haxis, hbdd⟩ := hdat
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hf4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmf 4 (by norm_num) hf6
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hn4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hn6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hK0nn : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hvalA 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
  have hCBnn : 0 ≤ CB := hCBpos.le
  have hαnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  obtain ⟨q, rfl, hq0, hqγ, hqη⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leafW_canon_cases hα0 hleaf
  -- ## index bookkeeping
  have hge : 1 ≤ a - i + 1 := by omega
  have hY6le : (a - i + 1) + (b - j) ≤ 6 := by omega
  have hY4le : (a - i + 1) + (b - j) ≤ 4 := by omega
  -- ## the level-`6` dominations of the two `f`-slots
  have hY6 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z θ hθ0 hθ1 => canonW_mul_mixed_le6 hα0 hq0 hqγ hge hY6le ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hZ6 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z θ hθ0 hθ1 =>
      Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f a b hqγ hqη hab ⟨hθ0, hθ1⟩
  have hYZ : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hθ0 hθ1
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have h := two_mul_le_add_sq |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
      |Work.Spaces.mixed b a f z θ|
    rw [sq_abs, sq_abs] at h
    nlinarith [h, hcw, hY6 z θ hθ0 hθ1, hZ6 z θ hθ0 hθ1]
  -- ## the sup bound on the coefficient slot
  have hXsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A := by
    intro z θ hz hθ0 hθ1
    have h := hCp α A j i hα0 hα1 hsmA hA6 (by omega) z hz θ ⟨hθ0, hθ1⟩
    have hfac : Cp / (Work.Spaces.gam α - 1) ≤ (CB * α ^ (-(1 / 2 : ℝ))) ^ 2 := by
      have hfac1 : Cp / (Work.Spaces.gam α - 1) = Cp * 10 * α⁻¹ := by
        rw [Work.Spaces.gam_sub_one]
        field_simp
      have hsq : Cp * 10 ≤ CB ^ 2 := by
        rw [hCBdef]
        have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ Cp * 10 by positivity)
        nlinarith [Real.sqrt_nonneg (Cp * 10)]
      have hhalf : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
        rw [sq, ← Real.rpow_add hα0, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num,
          Real.rpow_neg_one]
      rw [hfac1, mul_pow, hhalf]
      exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hα0.le)
    have h2 : (Work.Spaces.mixed j i A z θ) ^ 2
        ≤ (CB * α ^ (-(1 / 2 : ℝ))) ^ 2 * (Work.Spaces.HkNorm α 6 A) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 A)]
      exact le_trans h (mul_le_mul_of_nonneg_right hfac (Work.Spaces.HkSq_nonneg α 6 A))
    exact abs_le_of_sq_le_nn' h2 (mul_nonneg hCBnn hαnn)
      (Work.Spaces.HkNorm_nonneg α 6 A)
  -- ## the pointwise bound on the full integrand
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
            * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hXs := hXsup z θ hz hθ0 hθ1
    have hYZ' := hYZ z θ hθ0 hθ1
    have hleft : 0 ≤ canonW q z θ
        * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
      mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcst : 0 ≤ CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A :=
      mul_nonneg (mul_nonneg hCBnn hαnn) (Work.Spaces.HkNorm_nonneg α 6 A)
    calc |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        = |Work.Spaces.mixed j i A z θ| * (canonW q z θ
          * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
      _ ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
            * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul hXs hYZ' hleft hcst
  -- ## integrability of the full integrand
  have hFcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ
      * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
      * Work.Spaces.mixed b a f z θ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (hsmA.mixed j i).continuousOn).mul
      (hsmf.mixed (b - j) (a - i + 1)).continuousOn).mul (hsmf.mixed b a).continuousOn
  have hmargH : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iz := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
            * Work.Spaces.HkIntegrand α 6 f z θ)
        = fun z => (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ from
          funext (fun z => MeasureTheory.integral_const_mul _ _)]
    exact hf6.2.const_mul _
  have hinter := integrableConjuncts
    (F := fun z θ => canonW q z θ * Work.Spaces.mixed j i A z θ
      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ)
    (H := fun z θ => (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
      * Work.Spaces.HkIntegrand α 6 f z θ)
    hFcont
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_const.mul (hsmf.continuousOn_HkIntegrand α 6)))
    (fun θ => by rw [canonW_zero_z]; ring)
    (fun z hz => (hf6.1 z hz).const_mul _)
    hmargH
    hpt
  -- ## the level-`4` energy of the middle slot and the level-`6` energy of the last slot
  have hEY4 := canonW_energy_mixed4 hα0 hq0 hqγ hsmf hf4 hge hY4le
  have hZsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
      * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.StrongPersist.N6Trans.T1SixAux.slotSliceIntegrable α q hsmf hf6
      hqγ hqη hab hz
  have hZen := Work.FTS.StrongPersist.N6Trans.T1SixAux.slotEnergyZOuter α q hsmf hf6
    hq0 hqγ hqη hab
  -- ## the iterated Cauchy–Schwarz on the two `f`-slots
  have hCS := cs_iterated (ρ := fun z θ => canonW q z θ)
    (A := fun z θ => Work.Spaces.mixed (b - j) (a - i + 1) f z θ)
    (B := fun z θ => Work.Spaces.mixed b a f z θ)
    (fun z hz θ hθ => canonW_nonneg hθ) hEY4.1 hZsl hEY4.2.1 hZen.1
  have hCS' : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
      * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
    refine le_trans hCS ?_
    have h1 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2) ≤ Work.Spaces.HkNorm α 4 f :=
      le_trans (Real.sqrt_le_sqrt hEY4.2.2) le_rfl
    have h2 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkNorm α 6 f :=
      le_trans (Real.sqrt_le_sqrt hZen.2) le_rfl
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Work.Spaces.HkNorm_nonneg α 4 f)
  -- ## slice and marginal integrability of `ρ|Y||Z|`
  have hYZcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ
      * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (hsmf.mixed (b - j) (a - i + 1)).continuousOn.abs).mul
      (hsmf.mixed b a).continuousOn.abs)
  have hYZi : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iz :=
    integrableConjuncts
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
        * |Work.Spaces.mixed b a f z θ|)
      (H := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
      hYZcont
      (Work.Spaces.aesm_of_continuousOn_Qd _ (hsmf.continuousOn_HkIntegrand α 6))
      (fun θ => by rw [canonW_zero_z]; ring)
      (fun z hz => hf6.1 z hz)
      hf6.2
      (fun z θ hz hθ0 hθ1 => by
        have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)), mul_assoc]
        exact hYZ z θ hθ0 hθ1)
  -- ## the value bound
  have hKxnn : 0 ≤ CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A :=
    mul_nonneg (mul_nonneg hCBnn hαnn) (Work.Spaces.HkNorm_nonneg α 6 A)
  refine ⟨hinter.1, hinter.2, ?_⟩
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * (∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        refine integral_Iz_mono_ae (fun z hz => ?_) (fun z hz => abs_nonneg _)
          (hYZi.2.const_mul _)
        refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
        rw [← MeasureTheory.integral_const_mul]
        refine integral_Iθ_mono_ae (fun θ hθ => ?_) (fun θ hθ => abs_nonneg _)
          ((hYZi.1 z (Set.mem_Ici.mpr hz.le)).const_mul _)
        have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
        have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
        have hXs := hXsup z θ (Set.mem_Ioi.mp hz) hθ.1 hθ.2
        have hleft : 0 ≤ canonW q z θ
            * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
          mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        calc |canonW q z θ * Work.Spaces.mixed j i A z θ
              * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
              * Work.Spaces.mixed b a f z θ|
            = |Work.Spaces.mixed j i A z θ| * (canonW q z θ
              * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
          _ ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
              * (canonW q z θ * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|)) :=
              mul_le_mul_of_nonneg_right hXs hleft
          _ = (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
              * (canonW q z θ * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by ring
    _ = (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) :=
        mul_le_mul_of_nonneg_left hCS' hKxnn
    _ ≤ CB * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
        have hx6le : Work.Spaces.HkNorm α 6 A ≤ K6 := hn6
        have hh4 : Work.Spaces.HkNorm α 4 f ≤ M := hbdd
        have hbr : K6 * M * Work.Spaces.HkNorm α 6 f
            ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
          have h1 : (0 : ℝ) ≤ K4 + K6 := by linarith
          have hK6M : K6 * M ≤ (K4 + K6) * (1 + M) :=
            mul_le_mul (by linarith) (by linarith) hMnn h1
          have hstep : K6 * M * Work.Spaces.HkNorm α 6 f
              ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
            mul_le_mul hK6M (by linarith) hX6nn (by positivity)
          have hnn : (0 : ℝ) ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
            mul_nonneg (by linarith) (by linarith)
          linarith
        have hnn2 : 0 ≤ K6 * M * Work.Spaces.HkNorm α 6 f :=
          mul_nonneg (mul_nonneg hK6nn hMnn) hX6nn
        have hmid : Work.Spaces.HkNorm α 6 A * (Work.Spaces.HkNorm α 4 f
              * Work.Spaces.HkNorm α 6 f) ≤ K6 * M * Work.Spaces.HkNorm α 6 f := by
          calc Work.Spaces.HkNorm α 6 A * (Work.Spaces.HkNorm α 4 f
                * Work.Spaces.HkNorm α 6 f)
              ≤ K6 * (M * Work.Spaces.HkNorm α 6 f) :=
                mul_le_mul hx6le (mul_le_mul_of_nonneg_right hh4 hX6nn)
                  (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) hX6nn) hK6nn
            _ = K6 * M * Work.Spaces.HkNorm α 6 f := by ring
        calc (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
            = CB * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.HkNorm α 6 A
                * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)) := by ring
          _ ≤ CB * α ^ (-(1 / 2 : ℝ)) * (K6 * M * Work.Spaces.HkNorm α 6 f) :=
              mul_le_mul_of_nonneg_left (hmid.trans le_rfl)
                (mul_nonneg hCBnn hαnn)
          _ ≤ CB * α ^ (-(1 / 2 : ℝ))
                * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                   + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
              mul_le_mul_of_nonneg_left hbr (mul_nonneg hCBnn hαnn)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.EVz6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

set_option maxHeartbeats 1000000

/-! ## The two halves of the order-six bound of `EVz`

`Work.FTS.PhiStar.EVz Y = 2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY` is a sum of two products of a
fixed smooth angular coefficient with one of the blocks `Y`, `∂_θY`, so it is bounded by the
bilinear flat calculus (`F0_mul` never squares the block constant).  The file `F0SixEVzR.lean`
already supplies the first half,

`∃ C, ∀ K KY Y, F0 6 K Y → F0 6 KY (∂_θY) → F0 6 (C·(K+KY)) (EVzR Y)`,

and here we add

* the pointwise identity `∂_θ(EVzR Y) = EVzD Y` on the open quadrant (product rule, plus
  `∂_θ(cos² − 2 sin²) = −3 sin 2θ` and `∂_θ(sin 2·) = 2 cos 2·` — in the form in which the
  product rule produces them, i.e. as `deriv (fun θ' => …) θ`);
* the second half `∃ C, ∀ K KY Y, F0 6 K Y → F0 6 KY (∂_θY) → F0 5 (C·(K+KY)) (EVzD Y)`.

The assembly is then `F0_congr` (`EVz Y = EVzR Y`), `flatW6_of_F0`, and the arithmetic
`mono_const` of `Flat6Defs`. -/

/-- **The `∂_θ`-identity of the reassociated `EVz`-field.**  On the open quadrant the
`θ`-derivative of `EVzR Y` is the explicit expression `EVzD Y`: the product rule applied to the
two summands `2(cos²θ − 2 sin²θ)·Y` and `sin(2θ)·∂_θY`, with `∂_θ(sin 2θ)·∂_θY` split off and
`sin(2θ)·∂_θ(∂_θY) = D_θ(∂_θY)`. -/
private theorem evz6_pth_Q0 (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EVzR Y) z θ = EVzD Y z θ := by
  have hc2 : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
        = fun p : ℝ × ℝ => Real.cos p.2 ^ 2 - 2 * Real.sin p.2 ^ 2 := rfl
    rw [h]
    fun_prop
  have hc3 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) := by
    refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry (fun _ θ : ℝ => Real.sin (2 * θ))
        = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
    rw [h]
    fun_prop
  have hs1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc2 2) hsm
  have hs2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Real.sin (2 * θ) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hc3 hsm.pth
  have hd2' : deriv (fun θ' : ℝ => 2 * (Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2))
      = fun θ => 2 * deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ := by
    funext θ
    exact deriv_const_mul_field (x := θ)
      (v := fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) (2 : ℝ)
  intro z θ hz hθ hθ'
  let A1 : ℝ → ℝ → ℝ := fun z θ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ
  let A2 : ℝ → ℝ → ℝ := fun z θ => Real.sin (2 * θ) * Work.Spaces.pth Y z θ
  have hs1' : Work.FTS.EllipticEst.SmoothOpen A1 := hs1
  have hs2' : Work.FTS.EllipticEst.SmoothOpen A2 := hs2
  have hsplit : EVzR Y = fun z θ => A1 z θ + A2 z θ := by
    funext a b
    simp only [A1, A2, EVzR]
  have hd1 : Work.Spaces.pth A1 z θ
      = Work.Spaces.pth (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) z θ * Y z θ
        + (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ := by
    have h := Work.FTS.PhiStar.CoreAux.Fbq_pth_mul
      (f := fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) (g := Y)
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc2 2) hsm z θ hz hθ hθ'
    simpa only [A1] using h
  have hd2 : Work.Spaces.pth A2 z θ
      = Work.Spaces.pth (fun z θ : ℝ => Real.sin (2 * θ)) z θ * Work.Spaces.pth Y z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth Y) z θ := by
    have h := Work.FTS.PhiStar.CoreAux.Fbq_pth_mul
      (f := fun z θ : ℝ => Real.sin (2 * θ)) (g := Work.Spaces.pth Y) hc3 hsm.pth
      z θ hz hθ hθ'
    simpa only [A2] using h
  have hsum : Work.Spaces.pth (EVzR Y) z θ
      = Work.Spaces.pth A1 z θ + Work.Spaces.pth A2 z θ := by
    rw [hsplit]
    exact Work.FTS.PhiStar.CoreAux.pth_add_Q0 (f := A1) (g := A2) hs1' hs2' z θ hz hθ hθ'
  rw [hsum, hd1, hd2,
    pth_thetaOnly (fun θ' : ℝ => 2 * (Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)),
    hd2',
    pth_thetaOnly (fun θ' : ℝ => Real.sin (2 * θ'))]
  simp only [EVzD, Work.Spaces.Dth]
  ring

/-- **The second half of the order-six bound of `EVz`**: the `F0 5`-bound of the reassociated
`θ`-derivative `EVzD Y`, linear in the two block constants `K` (of `Y`) and `KY` (of `∂_θY`).

`EVzD Y` is the sum of four products: `(2·∂_θ(cos²−2sin²))·Y`, `(2(cos²−2sin²))·∂_θY`,
`(∂_θ sin 2·)·∂_θY` and `D_θ(∂_θY)`.  The first three are `F0_mul` of a coefficient with
constant `2A` (resp. `A`) and a block with constant `K` (resp. `KY`); the last is `F0_Dth` of
`F0 6 KY (∂_θY)`, which costs one angular order. -/
private theorem evz6_f0five : ∃ C : ℝ, 0 < C ∧ ∀ (K KY : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → 0 ≤ KY → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 K Y → Work.FTS.PhiStar.F0 6 KY (Work.Spaces.pth Y) →
    Work.FTS.PhiStar.F0 5 (C * (K + KY)) (EVzD Y) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  refine ⟨200 * A, by linarith, ?_⟩
  intro K KY Y hK hKY hsm hY hdY
  -- the three coefficient functions and their level-`5` bounds
  have hc2 := hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])
  have hc6 := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
    (by simp [coefFun])
  have hc7 := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) (by simp [coefFun])
  have hc2' : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    hc2.1.mono (by norm_num) le_rfl
  have hc6' : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    hc6.1.mono (by norm_num) le_rfl
  have hc7' : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) :=
    hc7.1.mono (by norm_num) le_rfl
  -- the coefficients doubled by the factor `2` in `EVzD`
  have h2c6 : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hc6'
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  have h2c2 : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hc2'
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  have s2c6 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc6.2 2
  have s2c2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc2.2 2
  -- the blocks
  have hY5 : Work.FTS.PhiStar.F0 5 K Y := hY.mono (by norm_num) le_rfl
  have hdY5 : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.pth Y) := hdY.mono (by norm_num) le_rfl
  have hddY : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_Dth (n := 5) hdY
  -- the four summands
  have t1 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * K)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (n := 5) (mul_nonneg (by norm_num) hA0) hK s2c6 hsm
      h2c6 hY5
  have t2 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * KY)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
        * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (n := 5) (mul_nonneg (by norm_num) hA0) hKY s2c2 hsm.pth
      h2c2 hdY5
  have t3 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ
        * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (n := 5) hA0 hKY hc7.2 hsm.pth hc7' hdY5
  -- the smoothness of the summands
  have st1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2c6 hsm
  have st2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2c2 hsm.pth
  have st3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hc7.2 hsm.pth
  have st4 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    hsm.pth.Dth
  have st12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add st1 st2
  have st123 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ)
        + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add st12 st3
  -- the three sums
  have h12 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_add st1 st2 t1 t2
  have h123 : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ => (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ)
        + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_add st12 st3 h12 t3
  have h1234 : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY + KY)
      (fun z θ : ℝ =>
        ((2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
          + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ)
          + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ)
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_add st123 st4 h123 hddY
  -- transfer to `EVzD Y`
  have hEVzD : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY + KY)
      (EVzD Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => by
      simp only [EVzD, Work.Spaces.Dth]) h1234
  refine hEVzD.mono le_rfl ?_
  have hAK0 : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  have hAKY0 : (0 : ℝ) ≤ A * KY := mul_nonneg hA0 hKY
  have h1 : (2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY + KY
      = 64 * A * K + 96 * A * KY + KY := by norm_num; ring
  rw [h1]
  nlinarith [hA1, hK, hKY, hAK0, hAKY0]

/-- **The order-six flat bound of the `EVz`-star-field.**

Prove `FlatW 6 (EVz Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD`.

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`, which provides `CoefBundle6s`
(one `A ≥ 1` with `F0 6 A c` and `SmoothOpen c` for the ten coefficient functions `coefFun`),
`atomData` (the block bounds, including `F0 5 (K+KY) (Dth (pth Y))` for the `Tblk`-slot),
`EVzR`/`EVzD` and `evzEVzR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`, `pth_thetaOnly`.
Natural route: the strong pair `F0 6 (EVzR Y)` and `F0 5 (pth (EVzR Y))` (`pth (EVzR Y) = EVzD Y`
on `Q0`, via `Fbq_pth_mul`, `deriv_cos_sq_sub`, `deriv_sin_two`), then `F0_congr` and
`flatW6_of_F0`. The sibling `Submission/Work/FTS/PhiStar/CoreAux/Fb_EV_bound.lean` proves the
order-**four** version. -/
theorem EVz6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := F0SixEVzR
  obtain ⟨C₂, hC₂0, hC₂⟩ := evz6_f0five
  refine ⟨2 * C₁ + 2 * C₂ + 1, by linarith, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  set S : ℝ := K + KY + KD with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; linarith
  have hY : Work.FTS.PhiStar.F0 6 S Y := hFb.f0.mono le_rfl (by rw [hSdef]; linarith)
  have hPY : Work.FTS.PhiStar.F0 6 S (Work.Spaces.pth Y) :=
    (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hW).mono le_rfl (by rw [hSdef]; linarith)
  have hR : Work.FTS.PhiStar.F0 6 (C₁ * (S + S)) (EVzR Y) := hC₁ S S Y hS0 hS0 hsm hY hPY
  have hD5 : Work.FTS.PhiStar.F0 5 (C₂ * (S + S)) (EVzD Y) := hC₂ S S Y hS0 hS0 hsm hY hPY
  have hEVz : Work.FTS.PhiStar.F0 6 (C₁ * (S + S)) (Work.FTS.PhiStar.EVz Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => evzEVzR_eq Y z θ) hR
  have hpth : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.FTS.PhiStar.EVz Y) z θ = EVzD Y z θ := by
    intro z θ hz hθ hθ'
    rw [pth_congr6 (fun z θ _ _ _ => evzEVzR_eq Y z θ) z θ hz hθ hθ']
    exact evz6_pth_Q0 Y hsm z θ hz hθ hθ'
  have hPEVz : Work.FTS.PhiStar.F0 5 (C₂ * (S + S))
      (Work.Spaces.pth (Work.FTS.PhiStar.EVz Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr hpth hD5
  have hSS0 : (0 : ℝ) ≤ S + S := by linarith
  have hle1 : C₁ * (S + S) ≤ (C₁ + C₂) * (S + S) :=
    mul_le_mul_of_nonneg_right (by linarith) hSS0
  have hle2 : C₂ * (S + S) ≤ (C₁ + C₂) * (S + S) :=
    mul_le_mul_of_nonneg_right (by linarith) hSS0
  have hEVz' : Work.FTS.PhiStar.F0 6 ((C₁ + C₂) * (S + S)) (Work.FTS.PhiStar.EVz Y) :=
    hEVz.mono le_rfl hle1
  have hPEVz' : Work.FTS.PhiStar.F0 5 ((C₁ + C₂) * (S + S))
      (Work.Spaces.pth (Work.FTS.PhiStar.EVz Y)) := hPEVz.mono le_rfl hle2
  have hflat : Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) ((C₁ + C₂) * (S + S)) :=
    flatW6_of_F0 hEVz' hPEVz'
  refine FlatW_mono6 hflat ?_
  have hα1 : (1 : ℝ) ≤ α + 1 := by linarith
  have hC12 : 2 * (C₁ + C₂) ≤ 2 * C₁ + 2 * C₂ + 1 := by linarith
  calc (C₁ + C₂) * (S + S) = (2 * (C₁ + C₂)) * S := by ring
    _ ≤ ((2 * C₁ + 2 * C₂ + 1) * (α + 1)) * S := by
          apply mul_le_mul_of_nonneg_right _ hS0
          nlinarith [hα1, hC12]
    _ = (2 * C₁ + 2 * C₂ + 1) * (α + 1) * S := by ring

end Work.FTS.StrongPersist.SP6
end
