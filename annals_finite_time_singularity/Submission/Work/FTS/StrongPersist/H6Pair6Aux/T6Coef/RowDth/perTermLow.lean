/-
# The low slots of the `D_θ`-row per-term estimate (`i + j ≤ 4`)

Two cases of the per-term bound for the Leibniz remainder of `Work.FTS.TransportS.slotPairing`:

* `caseLe2Mine` — `i + j ≤ 2`: the coefficient slot `X = D_z^jD_θ^iA` is bounded *pointwise*
  (`TransportS.sup_dz_le_hk` for the pure slot `i = 0`,
  `TransportS.T2SupB2.mixed_pointwise_le_Xn` for the mixed one), and the two `f`-slots are
  estimated by AM–GM against the level-`6` integrand of `f`;
* `caseTo4Mine` — `3 ≤ i + j ≤ 4`: the coefficient slot is bounded pointwise by the level-`6`
  norm of `A` (`N6.PwAny6`), and the two `f`-slots are paired by the iterated Cauchy–Schwarz
  `RowDth.cs_iterated`, the middle slot at level `4` and the last one at level `6`.

In both cases the integrability conjuncts come from `RowDth.integrableConjuncts`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.CS
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Integ
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SlicePrep

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
