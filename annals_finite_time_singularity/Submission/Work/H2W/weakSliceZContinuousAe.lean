import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.errMSlot_le
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.H2W.dzPsiSliceLimits
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.H2W.momentChainAe
import Submission.Work.H2W.weakSliceContinuousKit
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.OpenPkg.Galerkin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  IsGalerkinCoeff IsDynGSolWith GlobalODEExistence DenseSpan WeakDetermines IsDynWeakOn
  ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof galFam ProfileEquicont)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The regularity of the slices of the limit -/


/-! ## The ODE layer of the chapter, for the core bundle -/



/-! ## The migrated bundle -/



end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.MixedSlotCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The termwise bound.** For `a ≤ i`, `b ≤ j`, the product
`D_z^bD_θ^a(χζ-1) · D_z^{j-b}D_θ^{i-a}F · Wt` is bounded in square by `Base · Good`, where
`Base` dominates both coefficient bounds `(1+K b²)(1+L a²)`.  Three cases: (i) `a=b=0`, where
`(χζ-1)² ≤ omegaInd` and the `F`-factor is an `ℋ^k`-slot; (ii) `i - a = 0` (so `a = i ≥ 1`),
where the coefficient bound with `thShrink` is used and the `F`-factor is a pure `D_z`-slot,
absorbed by the second group of `Good`; (iii) `1 ≤ i - a`, where both factors are
`Ω_n`-supported slots. -/
theorem ems_core_le (k : ℕ) {Base : ℝ} (hBase : 1 ≤ Base)
    (hCoeffInd : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a + b → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
    (hCoeffTs : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ)
    {α : ℝ} {n : ℕ} {F : ℝ → ℝ → ℝ} (hn : 2 ≤ n) {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k)
    {a b : ℕ} (ha : a ≤ i) (hb : b ≤ j) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
        * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  have hBase0 : 0 ≤ Base := le_trans zero_le_one hBase
  have hG : 0 ≤ Good α k n F z θ := Good_nonneg α k n F hθ
  have hgnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  by_cases h0 : a + b = 0
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0; subst hb0
    have h1 : (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) ^ 2 ≤ omegaInd n z θ :=
      chiR_zetaR_sub_one_sq_le hn z θ
    have h2 : (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k F z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi hij
    have h3 : ((Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)
        * Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ omegaInd n z θ * Work.Spaces.HkIntegrand α k F z θ := by
      rw [show ((Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)
          * Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) ^ 2
            * (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 from by ring]
      exact mul_le_mul h1 h2 (sq_nonneg _) (omegaInd_nonneg n z θ)
    calc ((Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)
          * Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ omegaInd n z θ * Work.Spaces.HkIntegrand α k F z θ := h3
      _ = omegaPart α k n F z θ := ems_omegaInd_mul_HkIntegrand α k n F z θ
      _ ≤ Good α k n F z θ := ems_omegaPart_le_Good α k n F hθ
      _ ≤ Base * Good α k n F z θ := le_mul_of_one_le_left hG hBase
  · have hab : 1 ≤ a + b := by omega
    have hWt2 := ems_Wt_sq (α := α) (z := z) (θ := θ) hgnn
    by_cases hia : i - a = 0
    · -- the coefficient carries the full angular weight: use the `thShrink` bound
      have ha1 : 1 ≤ a := by omega
      have hs : j - b < k := by omega
      have hX : (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
          ≤ Base * thShrink n θ := hCoeffTs n a b hn ha1 (by omega) (by omega) z θ
      have hYeq : Work.Spaces.mixed (j - b) (i - a) F z θ
          = Work.Spaces.DzIter (j - b) F z θ := by
        rw [hia, Work.Spaces.mixed_zero_right]
      have hYb : thShrink n θ
            * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ thShrink n θ * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [hYeq, show (Work.Spaces.DzIter (j - b) F z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.DzIter (j - b) F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
          rw [mul_pow, hWt2]; ring]
        exact ems_zslot_le_thShrinkSum (F := F) (α := α) (n := n) hs hθ
      calc (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
              * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ (Base * thShrink n θ)
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hX (sq_nonneg _)
        _ = Base * (thShrink n θ
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ Base * (thShrink n θ * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
            mul_le_mul_of_nonneg_left hYb hBase0
        _ ≤ Base * Good α k n F z θ :=
            mul_le_mul_of_nonneg_left (ems_thShrink_sum_le_Good α k n F hθ) hBase0
    · have hia1 : 1 ≤ i - a := by omega
      have hX : (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
          ≤ Base * omegaInd n z θ := hCoeffInd n a b hn hab (by omega) (by omega) z θ
      have hY : (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k F z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ (i - a) (j - b) hia1 (by omega)
      calc (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
              * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ (Base * omegaInd n z θ) * Work.Spaces.HkIntegrand α k F z θ :=
            mul_le_mul hX hY (sq_nonneg _) (mul_nonneg hBase0 (omegaInd_nonneg n z θ))
        _ = Base * omegaPart α k n F z θ := by
            rw [mul_assoc, ems_omegaInd_mul_HkIntegrand α k n F z θ]
        _ ≤ Base * Good α k n F z θ :=
            mul_le_mul_of_nonneg_left (ems_omegaPart_le_Good α k n F hθ) hBase0

/-- **The `(χζ-1)·F` group of the expansion.** The full double sum of Leibniz terms of
`(χζ-1)·F` is bounded in square, after multiplication by `Wt`, by `C · Good`. -/
theorem ems_prod_sq_le (k : ℕ) (Base : ℝ) (hBase : 1 ≤ Base)
    (hCoeffInd : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a + b → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
    (hCoeffTs : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → 2 ≤ n →
        ∀ (i j : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          ((∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                      * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
                   * Work.Spaces.mixed (j - b) (i - a) F z θ))
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  refine ⟨((k : ℝ) + 1) ^ 8 * (16 : ℝ) ^ k * Base + 1, by positivity, ?_⟩
  intro α n F hα hn i j hi hij z hz θ hθ
  have hBase0 : 0 ≤ Base := le_trans zero_le_one hBase
  have hG : 0 ≤ Good α k n F z θ := Good_nonneg α k n F hθ
  have h16 : 0 ≤ (16 : ℝ) ^ k := by positivity
  have hcoef : ∀ a b : ℕ, a ≤ i → b ≤ j →
      ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 ≤ (16 : ℝ) ^ k := by
    intro a b ha hb
    have h1 : i.choose a ≤ 2 ^ i := Nat.choose_le_two_pow i a
    have h2 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
    have h3 : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ (2 : ℝ) ^ k := by
      have h4 : (i.choose a : ℝ) * (j.choose b : ℝ)
          ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ j := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact_mod_cast h1
        · exact_mod_cast h2
      have h5 : (2 : ℝ) ^ i * (2 : ℝ) ^ j = (2 : ℝ) ^ (i + j) := by rw [← pow_add]
      have h6 : (2 : ℝ) ^ (i + j) ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      rw [h5] at h4
      exact le_trans h4 h6
    have h7 : ((2 : ℝ) ^ k) ^ 2 ≤ (16 : ℝ) ^ k := by
      rw [← pow_mul]
      rw [show (16 : ℝ) = 2 ^ 4 from by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h3 2
      _ ≤ (16 : ℝ) ^ k := h7
  let T : ℕ → ℕ → ℝ := fun a b => ((i.choose a : ℝ) * (j.choose b : ℝ))
      * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
         * Work.Spaces.mixed (j - b) (i - a) F z θ) * Work.Spaces.Wt α z θ
  have hterm : ∀ a b : ℕ, a ≤ i → b ≤ j →
      (T a b) ^ 2 ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
        * (Base * Good α k n F z θ) := by
    intro a b ha hb
    have hc : (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
        * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
      ems_core_le k (Base := Base) hBase hCoeffInd hCoeffTs (α := α) (F := F) hn hi hij ha hb
        (z := z) hθ
    calc (T a b) ^ 2 = ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
          * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
              * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          simp only [T]; ring
      _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 * (Base * Good α k n F z θ) :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  have hSsplit : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
             * Work.Spaces.mixed (j - b) (i - a) F z θ)) * Work.Spaces.Wt α z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b := by
    simp only [Finset.sum_mul, T]
  have hcs : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2
      ≤ (((i : ℝ) + 1) * ((j : ℝ) + 1))
        * (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2) := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun a => ∑ b ∈ Finset.range (j + 1), T a b)
    have h1' : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2
        ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
            (∑ b ∈ Finset.range (j + 1), T a b) ^ 2 := by
      simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h1
    have h2 : ∀ a : ℕ, (∑ b ∈ Finset.range (j + 1), T a b) ^ 2
        ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2 := by
      intro a
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := fun b => T a b)
      simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
    calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2
        ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
            (∑ b ∈ Finset.range (j + 1), T a b) ^ 2 := h1'
      _ ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
            (((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => h2 a) (by positivity)
      _ = (((i : ℝ) + 1) * ((j : ℝ) + 1))
            * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2 := by
          rw [← Finset.mul_sum]; ring
  have hsum2 : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2)
      ≤ ((i : ℝ) + 1) * (((j : ℝ) + 1) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ))) := by
    have hper : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
        (T a b) ^ 2 ≤ (16 : ℝ) ^ k * (Base * Good α k n F z θ) := by
      intro a ha b hb
      have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      exact le_trans (hterm a b hai hbj)
        (mul_le_mul_of_nonneg_right (hcoef a b hai hbj) (mul_nonneg hBase0 hG))
    calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2)
        ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
      _ = ((i : ℝ) + 1) * (((j : ℝ) + 1) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hNle : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
    have hi1 : (i : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have : i + 1 ≤ k + 1 := by omega
      exact_mod_cast this
    have hj1 : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have : j + 1 ≤ k + 1 := by omega
      exact_mod_cast this
    exact mul_le_mul hi1 hj1 (by positivity) (by positivity)
  have hN2 : (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 ≤ ((k : ℝ) + 1) ^ 4 := by
    calc (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2
        ≤ (((k : ℝ) + 1) * ((k : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) hNle 2
      _ = ((k : ℝ) + 1) ^ 4 := by ring
  have hpow : ((k : ℝ) + 1) ^ 4 ≤ ((k : ℝ) + 1) ^ 8 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := one_le_pow₀ hk1
    calc ((k : ℝ) + 1) ^ 4 = ((k : ℝ) + 1) ^ 4 * 1 := by ring
      _ ≤ ((k : ℝ) + 1) ^ 4 * ((k : ℝ) + 1) ^ 4 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((k : ℝ) + 1) ^ 8 := by ring
  calc ((∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                  * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
               * Work.Spaces.mixed (j - b) (i - a) F z θ))
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2 := by rw [hSsplit]
    _ ≤ (((i : ℝ) + 1) * ((j : ℝ) + 1))
          * (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2) := hcs
    _ ≤ (((i : ℝ) + 1) * ((j : ℝ) + 1))
          * (((i : ℝ) + 1) * (((j : ℝ) + 1)
              * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)))) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = ((((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2)
          * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) := by ring
    _ ≤ (((k : ℝ) + 1) ^ 4) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) :=
        mul_le_mul_of_nonneg_right hN2 (mul_nonneg h16 (mul_nonneg hBase0 hG))
    _ ≤ (((k : ℝ) + 1) ^ 8) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg h16 (mul_nonneg hBase0 hG))
    _ ≤ ((((k : ℝ) + 1) ^ 8 * (16 : ℝ) ^ k * Base + 1))
          * Good α k n F z θ := by nlinarith [h16, hBase0, hG]

end Work.FTS.PhiStar.Honesty.CptApp.Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.err_dzSlot_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

set_option autoImplicit false

/-! ## Locality of `D_z` in the angular variable -/

/-- `D_z`-iterates only see the `z`-slice at the given angle: two functions with the same
`θ`-slice at `θ` have the same `D_z`-iterates at `(z,θ)`. -/
theorem estDzIter_congr_slice {f g : ℝ → ℝ → ℝ} (i : ℕ) {θ : ℝ}
    (h : ∀ z : ℝ, f z θ = g z θ) (z : ℝ) :
    Work.Spaces.DzIter i f z θ = Work.Spaces.DzIter i g z θ := by
  have hfg : (fun z' : ℝ => f z' θ) = fun z' : ℝ => g z' θ := funext fun z' => h z'
  rw [congrFun (Work.FTS.LocData.Zop_iterate_slice i f θ) z,
      congrFun (Work.FTS.LocData.Zop_iterate_slice i g θ) z, hfg]

/-! ## Additivity of `D_z`-iterates over differences -/

/-- **The iterated `D_z`-operator is additive over differences** on the open quadrant, for
`SmoothOpen` data: the same induction as for `SmoothOpen.DzIter_add`, with `deriv_sub`. -/
theorem estDzIter_sub {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter i (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.DzIter i f z θ - Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ - g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_sub hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The `Ω_n`-part of `Good` is exactly `omegaInd · HkIntegrand`. -/
theorem estOmegaPart_eq (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
      = Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
        * Work.Spaces.HkIntegrand α k F z θ := by
  rw [Work.FTS.PhiStar.Honesty.CptApp.omegaPart,
      Work.FTS.PhiStar.Honesty.CptApp.omegaInd]
  split_ifs <;> ring

/-- The `Ω_n`-part of `Good` is dominated by `Good`. -/
theorem estOmegaPart_le_Good (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
      ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  rw [Work.FTS.PhiStar.Honesty.CptApp.Good]
  have h1 : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ
      * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_nonneg (Work.FTS.PhiStar.Honesty.CptApp.thShrink_nonneg n θ)
      (Work.FTS.PhiStar.Honesty.CptApp.hkZsum_nonneg α k F z hθ)
  have h2 : 0 ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      * ((Work.Spaces.w z) ^ 2 * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) :=
    mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (Work.FTS.PhiStar.Honesty.CptApp.rhoProf_nonneg α k hθ))
  linarith

/-- **Abstract `(χζ−1)·F` slot bound.**  Given a family of multipliers `A n`, whose
`D_z`-jets are bounded by `K b` inside the shrinking region `Ω n` and whose Leibniz
expansion holds, the corresponding `D_z`-slots of `A n · F` are dominated by `Good`. -/
theorem estASlot_general (k : ℕ) (A : ℕ → ℝ → ℝ → ℝ) (K : ℕ → ℝ) (hKnn : ∀ b : ℕ, 0 ≤ K b)
    (hAB : ∀ (n b : ℕ), 2 ≤ n → ∀ (z θ : ℝ),
      |Work.Spaces.DzIter b (A n) z θ| ≤ K b * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
    (hExp : ∀ (F : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen F → ∀ (n i : ℕ) (z θ : ℝ),
      0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DzIter i (fun z θ => A n z θ * F z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
        Work.FTS.EllipticEst.SmoothOpen F →
        ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          (Work.Spaces.DzIter i (fun z θ => A n z θ * F z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  set Bc : ℕ → ℝ := fun i' => ((i' : ℝ) + 1) * ∑ b ∈ Finset.range (i' + 1),
      ((i'.choose b : ℝ) ^ 2 * (K b) ^ 2) with hBc
  have hBcnn : ∀ i' : ℕ, 0 ≤ Bc i' := by
    intro i'
    rw [hBc]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hBsum : 0 ≤ ∑ i' ∈ Finset.range (k + 1), Bc i' :=
    Finset.sum_nonneg fun i' _ => hBcnn i'
  refine ⟨1 + ∑ i' ∈ Finset.range (k + 1), Bc i', by linarith, ?_⟩
  intro α n F hα hα1 hn hsm i hi z hz θ hθ
  have hn2 : 2 ≤ n := by omega
  set Wz := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hWz
  have hWz0 : 0 ≤ Wz := by
    rw [hWz]
    exact div_nonneg (Work.FTS.PhiStar.Honesty.CptApp.w_nonneg z)
      (Real.rpow_nonneg (Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ) _)
  have hOPnn : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ :=
    Work.FTS.PhiStar.Honesty.CptApp.omegaPart_nonneg α k n F z θ
  have hBle : Bc i ≤ 1 + ∑ i' ∈ Finset.range (k + 1), Bc i' := by
    have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have h := Finset.single_le_sum (f := Bc) (fun i' _ => hBcnn i') hmem
    linarith
  have hCA : 0 ≤ 1 + ∑ i' ∈ Finset.range (k + 1), Bc i' := by linarith
  suffices hmain : (Work.Spaces.DzIter i (fun z θ => A n z θ * F z θ) z θ * Wz) ^ 2
      ≤ (1 + ∑ i' ∈ Finset.range (k + 1), Bc i')
        * Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ by
    exact le_trans hmain (mul_le_mul_of_nonneg_left (estOmegaPart_le_Good α k n F hθ) hCA)
  by_cases hz0 : z = 0
  · have h0 : Wz = 0 := by rw [hWz, hz0, Work.Spaces.w]; norm_num
    rw [h0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg hCA hOPnn
  · by_cases hs : Real.sin (2 * θ) = 0
    · have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
        rw [hs]; exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
      have h0 : Wz = 0 := by rw [hWz, hsin, div_zero]
      rw [h0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg hCA hOPnn
    · have hzpos : 0 < z := lt_of_le_of_ne (show (0 : ℝ) ≤ z from hz) (Ne.symm hz0)
      have hθpos : 0 < θ := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.1 with h | h
        · exact h
        · exfalso; apply hs; rw [← h]; norm_num
      have hθlt : θ < Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exfalso; apply hs
          rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      rw [hExp F hsm n i z θ hzpos ⟨hθpos, hθlt⟩]
      have hω0 : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ :=
        Work.FTS.PhiStar.Honesty.CptApp.omegaInd_nonneg n z θ
      have hω1 : Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ ≤ 1 :=
        Work.FTS.PhiStar.Honesty.CptApp.omegaInd_le_one n z θ
      have hsum_bound : |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)|
          ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
            * ∑ b ∈ Finset.range (i + 1),
                ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by
        calc |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)|
            ≤ ∑ b ∈ Finset.range (i + 1), |(i.choose b : ℝ)
                * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ b ∈ Finset.range (i + 1),
                Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                  * ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by
              refine Finset.sum_le_sum fun b _ => ?_
              have hcb : (0 : ℝ) ≤ (i.choose b : ℝ) := Nat.cast_nonneg _
              rw [abs_mul, abs_mul, abs_of_nonneg hcb]
              calc (i.choose b : ℝ) * (|Work.Spaces.DzIter b (A n) z θ|
                    * |Work.Spaces.DzIter (i - b) F z θ|)
                  ≤ (i.choose b : ℝ)
                      * ((K b * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
                          * |Work.Spaces.DzIter (i - b) F z θ|) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right (hAB n b hn2 z θ) (abs_nonneg _)) hcb
                _ = Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                      * ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by ring
          _ = Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                * ∑ b ∈ Finset.range (i + 1),
                    ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by
              rw [Finset.mul_sum]
      have hSmul : (∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|)) * Wz
          = ∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) :=
        Finset.sum_mul _ _ _
      have hS2Sq : (∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)) ^ 2
          ≤ Bc i * Work.Spaces.HkIntegrand α k F z θ := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
          (f := fun b => (i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)
        have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
          rw [Finset.card_range]; push_cast; ring
        have hterm : ∀ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) ^ 2
              ≤ (i.choose b : ℝ) ^ 2 * (K b) ^ 2 * Work.Spaces.HkIntegrand α k F z θ := by
          intro b hb
          have hb' : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hik : i - b ≤ k := by omega
          have hHI := Work.Spaces.sq_le_HkIntegrand_z α k F z θ (i - b) hik
          have hnn : 0 ≤ (i.choose b : ℝ) ^ 2 * (K b) ^ 2 :=
            mul_nonneg (sq_nonneg _) (sq_nonneg _)
          have heq : ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) ^ 2
              = (i.choose b : ℝ) ^ 2 * (K b) ^ 2
                * (Work.Spaces.DzIter (i - b) F z θ * Wz) ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
          rw [heq]
          exact mul_le_mul_of_nonneg_left hHI hnn
        calc (∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)) ^ 2
            ≤ ((Finset.range (i + 1)).card : ℝ)
                * ∑ b ∈ Finset.range (i + 1),
                    ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) ^ 2 :=
              hcs
          _ ≤ ((i : ℝ) + 1)
                * ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ) ^ 2 * (K b) ^ 2
                    * Work.Spaces.HkIntegrand α k F z θ) := by
              rw [hcard]
              exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
          _ = Bc i * Work.Spaces.HkIntegrand α k F z θ := by
              rw [hBc]
              rw [← Finset.sum_mul]
              ring
      calc ((∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)) * Wz) ^ 2
          = (|∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
                * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)| * Wz) ^ 2 := by
              rw [← sq_abs ((∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
                * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)) * Wz),
                abs_mul, abs_of_nonneg hWz0]
        _ ≤ (Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
              * (∑ b ∈ Finset.range (i + 1),
                  ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz))) ^ 2 := by
              refine pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hWz0) ?_ 2
              rw [← hSmul]
              exact le_trans (mul_le_mul_of_nonneg_right hsum_bound hWz0) (le_of_eq (by ring))
        _ ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
              * (∑ b ∈ Finset.range (i + 1),
                  ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)) ^ 2 := by
              rw [mul_pow]
              have hω2 : Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ ^ 2
                  ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by nlinarith
              exact mul_le_mul_of_nonneg_right hω2 (sq_nonneg _)
        _ ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
              * (Bc i * Work.Spaces.HkIntegrand α k F z θ) :=
              mul_le_mul_of_nonneg_left hS2Sq hω0
        _ = Bc i * Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
              rw [show Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                    * (Bc i * Work.Spaces.HkIntegrand α k F z θ)
                  = Bc i * (Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                    * Work.Spaces.HkIntegrand α k F z θ) by ring,
                ← estOmegaPart_eq α k n F z θ]
        _ ≤ (1 + ∑ i' ∈ Finset.range (k + 1), Bc i')
              * Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ :=
              mul_le_mul_of_nonneg_right hBle hOPnn

/-- The `(χζ−1)·F` slot of the error, from the two delegated ingredients. -/
theorem estASlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  obtain ⟨K, hKnn, hKbd⟩ := Work.FTS.PhiStar.Honesty.CptApp.EstAux.errAdjBound
  exact estASlot_general k (fun n z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
      * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) K hKnn hKbd
    (fun F hsm n i z θ hz hθ => Work.FTS.PhiStar.Honesty.CptApp.EstAux.errASlot_expand hsm n i hz hθ)

/-! ## The two halves of the error (delegated) -/

/-- The moment-correction slot of the error (delegated to `EstAux.errMSlot_le`):
`(D_z^i (mu n F · rho) · w/sin(2θ)^{η/2})² ≤ C · Good α k n F`. -/
theorem estMSlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
  Work.FTS.PhiStar.Honesty.CptApp.EstAux.errMSlot_le k

/-! ## The main estimate -/

theorem err_dzSlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  obtain ⟨C₁, hC₁pos, hA⟩ := estASlot_le k
  obtain ⟨C₂, hC₂pos, hM⟩ := estMSlot_le k
  refine ⟨2 * (C₁ + C₂) + 1, by linarith, ?_⟩
  intro α n F hα hα1 hn hsm i hi z hz θ hθ
  have hn1 : 1 ≤ n := by omega
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`: the weight `w 0 = 0` kills the slot
    rw [← hz0, Work.Spaces.w]
    have hL : (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) 0 θ
        * ((1 + 0) ^ 2 / 0 ^ 2
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
      norm_num
    rw [hL]
    exact mul_nonneg (by linarith) (Work.FTS.PhiStar.Honesty.CptApp.Good_nonneg α k n F hθ)
  · by_cases hs : Real.sin (2 * θ) = 0
    · -- `θ ∈ {0, π/2}`: the angular weight vanishes
      have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
        rw [hs]; exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
      have hL : (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
        rw [hsin, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      rw [hL]
      exact mul_nonneg (by linarith) (Work.FTS.PhiStar.Honesty.CptApp.Good_nonneg α k n F hθ)
    · -- the interior of the quadrant: `0 < θ < π/2`
      have hθpos : 0 < θ := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.1 with h | h
        · exact h
        · exfalso; apply hs; rw [← h]; norm_num
      have hθlt : θ < Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exfalso; apply hs
          rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      -- the two summands of `err`
      have hdec := estDzIter_sub
        (Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_chiZeta_sub_one hsm n)
        (Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_muRho hsm hn1) i z θ hzpos hθpos hθlt
      have hpoint : ∀ z' : ℝ, Work.FTS.PhiStar.Honesty.CptApp.err n F z' θ
          = (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z' θ
            - (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
              * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z' θ := by
        intro z'
        simp only [Work.FTS.PhiStar.Honesty.CptApp.err, Work.FTS.PhiStar.Honesty.CptApp.approx,
          Work.FTS.PhiStar.Honesty.CptApp.mu]
        ring
      have hXeq : Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
          = Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ
            - Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
                * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ := by
        rw [← hdec]
        exact estDzIter_congr_slice i (θ := θ) hpoint z
      set X := Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ with hXdef
      set Y := Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
          * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ with hYdef
      set Wz := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hWdef
      have hGnn : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
        Work.FTS.PhiStar.Honesty.CptApp.Good_nonneg α k n F hθ
      have hXq : Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
          = X - Y := hXeq
      have hA' : (X * Wz) ^ 2
          ≤ C₁ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
        hA α n F hα hα1 hn hsm i hi z hz θ hθ
      have hM' : (Y * Wz) ^ 2
          ≤ C₂ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
        hM α n F hα hα1 hn hsm i hi z hz θ hθ
      calc (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ * Wz) ^ 2
          = ((X - Y) * Wz) ^ 2 := by rw [hXq]
        _ = (X * Wz - Y * Wz) ^ 2 := by ring
        _ ≤ 2 * (X * Wz) ^ 2 + 2 * (Y * Wz) ^ 2 := by
              nlinarith [sq_nonneg (X * Wz + Y * Wz)]
        _ ≤ 2 * (C₁ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ)
              + 2 * (C₂ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ) := by
              linarith [mul_le_mul_of_nonneg_left hA' (by norm_num : (0 : ℝ) ≤ 2),
                mul_le_mul_of_nonneg_left hM' (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 * (C₁ + C₂) + 1) * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
              nlinarith [hGnn]

end Work.FTS.PhiStar.Honesty.CptApp.Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.hardyShrink_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

set_option autoImplicit false

/-! ## An abstract slice inequality

The measure-theoretic skeleton of the estimate, with the two Hardy inputs and the two
pointwise majorants left as hypotheses. -/
private theorem shrink_slice_abstract {n : ℕ} (hn : 3 ≤ n) {γ : ℝ} (hγ1 : 1 < γ)
    (hγ32 : γ ≤ 3 / 2) {W : ℝ} {u G : ℝ → ℝ}
    (hsmL : ContDiffOn ℝ 1 (fun θ => W * u θ) (Set.Ioo 0 (2 / (n : ℝ))))
    (htrL : Filter.Tendsto (fun θ => W * u θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hsmR : ContDiffOn ℝ 1 (fun θ => W * u θ)
      (Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2)))
    (htrR : Filter.Tendsto (fun θ => W * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hbdL : ∀ θ ∈ Set.Ioo 0 (2 / (n : ℝ)),
      (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (fun θ' => W * u θ') θ) ^ 2 ≤ G θ)
    (hbdR : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (fun θ' => W * u θ') θ) ^ 2 ≤ G θ) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W ^ 2
        * (Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-γ))))
      ≤ ENNReal.ofReal (8 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2n_pos : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have h2n_le : 2 / (n : ℝ) ≤ Real.pi / 4 := by
    rw [div_le_iff₀ hnR]
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have h2n_lt : 2 / (n : ℝ) < Real.pi / 2 := by linarith [h2n_le, Real.pi_pos]
  have hHL := Work.FTS.PhiStar.Honesty.CptApp.hardyLoc γ (2 / (n : ℝ)) hγ1 hγ32 h2n_pos h2n_le
    hsmL htrL
  have hHR := Work.FTS.PhiStar.Honesty.CptApp.hardyLocRight γ (Real.pi / 2 - 2 / (n : ℝ))
    hγ1 hγ32
    (by linarith : Real.pi / 2 - 2 / (n : ℝ) < Real.pi / 2)
    (by linarith : Real.pi / 4 ≤ Real.pi / 2 - 2 / (n : ℝ)) hsmR htrR
  -- the left half is contained in `(0, 2/n) ∪ {0}`, the right one in `(π/2-2/n, π/2) ∪ {π/2}`
  have hLsub : Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ))
      ⊆ Set.Ioo 0 (2 / (n : ℝ)) ∪ ({0} : Set ℝ) := by
    intro θ hθ
    obtain ⟨hθI, hθL⟩ := hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    rw [Set.mem_Iio] at hθL
    rcases eq_or_lt_of_le hθI.1 with h | h
    · exact Or.inr (by rw [← h]; exact Set.mem_singleton 0)
    · exact Or.inl ⟨h, hθL⟩
  have hRsub : Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))
      ⊆ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2) ∪ ({Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    obtain ⟨hθI, hθR⟩ := hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    rw [Set.mem_Ioi] at hθR
    rcases lt_or_eq_of_le hθI.2 with h | h
    · exact Or.inl ⟨hθR, h⟩
    · exact Or.inr (by rw [h]; exact Set.mem_singleton (Real.pi / 2))
  have hleft : (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ)),
        ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
      ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
    calc (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ)),
          ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
        ≤ ∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)) ∪ ({0} : Set ℝ),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) :=
          MeasureTheory.lintegral_mono_set hLsub
      _ = (∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
            + (∫⁻ θ in ({0} : Set ℝ),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))) :=
          MeasureTheory.lintegral_union (A := Set.Ioo 0 (2 / (n : ℝ))) (B := ({0} : Set ℝ))
            (measurableSet_singleton 0) (by rw [Set.disjoint_singleton_right]; simp)
      _ = ∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by
          rw [MeasureTheory.lintegral_singleton]; simp
      _ = ∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-γ) * (W * u θ) ^ 2) := by
          refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
          congr 1
          ring
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - γ)
              * (deriv (fun θ' => W * u θ') θ) ^ 2)) := hHL
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo 0 (2 / (n : ℝ)),
            ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          exact MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
              (fun θ hθ => ENNReal.ofReal_le_ofReal (hbdL θ hθ)))
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          refine MeasureTheory.lintegral_mono_set (fun θ hθ => ?_)
          exact ⟨hθ.1.le, by linarith [hθ.2, h2n_lt]⟩
  have hright : (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)),
        ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
      ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
    calc (∫⁻ θ in Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)),
          ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
        ≤ ∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2) ∪ ({Real.pi / 2} : Set ℝ),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) :=
          MeasureTheory.lintegral_mono_set hRsub
      _ = (∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
            + (∫⁻ θ in ({Real.pi / 2} : Set ℝ),
              ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))) :=
          MeasureTheory.lintegral_union (A := Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2))
            (B := ({Real.pi / 2} : Set ℝ)) (measurableSet_singleton _)
            (by rw [Set.disjoint_singleton_right]; simp)
      _ = ∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
            ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) := by
          rw [MeasureTheory.lintegral_singleton]; simp
      _ = ∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-γ) * (W * u θ) ^ 2) := by
          refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
          congr 1
          ring
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ))
            (Real.pi / 2), ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - γ)
              * (deriv (fun θ' => W * u θ') θ) ^ 2)) := hHR
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Set.Ioo (Real.pi / 2 - 2 / (n : ℝ))
            (Real.pi / 2), ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          exact MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
              (fun θ hθ => ENNReal.ofReal_le_ofReal (hbdR θ hθ)))
      _ ≤ ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
          refine mul_le_mul_right ?_ _
          refine MeasureTheory.lintegral_mono_set (fun θ hθ => ?_)
          exact ⟨by linarith [h2n_lt, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- `thShrink` is exactly the indicator of `L ∪ R`
  have hstep1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W ^ 2
        * (Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ * (u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-γ))))
      = ∫⁻ θ in Work.Spaces.Iθ,
          (Set.Iio (2 / (n : ℝ)) ∪ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))).indicator
            (fun θ => ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))) θ := by
    refine MeasureTheory.setLIntegral_congr_fun hIθ (fun θ _ => ?_)
    by_cases h : θ ∈ Set.Iio (2 / (n : ℝ)) ∪ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))
    · rw [Set.indicator_of_mem h]
      have hone : Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ = 1 := by
        rw [Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_one_iff]
        simpa only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using h
      rw [hone]
      congr 1
      ring
    · rw [Set.indicator_of_notMem h]
      have hzero : Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ = 0 := by
        rcases Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_zero_or_one n θ with h0 | h1
        · exact h0
        · exact absurd (by
            rw [Work.FTS.PhiStar.Honesty.CptApp.thShrink_eq_one_iff] at h1
            simpa only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using h1) h
      rw [hzero]
      simp
  have hunion : ((Set.Iio (2 / (n : ℝ)) ∩ Work.Spaces.Iθ)
        ∪ (Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)) ∩ Work.Spaces.Iθ))
      = (Work.Spaces.Iθ ∩ Set.Iio (2 / (n : ℝ)))
        ∪ (Work.Spaces.Iθ ∩ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ))) := by
    rw [Set.inter_comm (Set.Iio (2 / (n : ℝ))),
      Set.inter_comm (Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)))]
  have hlast : ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ))
      + ENNReal.ofReal (4 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ))
      = ENNReal.ofReal (8 / (γ - 1) ^ 2) * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (G θ)) := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring_nf
  rw [hstep1]
  rw [MeasureTheory.setLIntegral_indicator
    (s := Set.Iio (2 / (n : ℝ)) ∪ Set.Ioi (Real.pi / 2 - 2 / (n : ℝ)))
    (t := Work.Spaces.Iθ)
    (f := fun θ => ENNReal.ofReal (W ^ 2 * (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)))
    (by measurability)]
  rw [Set.union_inter_distrib_right, hunion]
  refine le_trans (MeasureTheory.lintegral_union_le _ _ _) ?_
  exact le_trans (add_le_add hleft hright) (le_of_eq hlast)

/-! ## The requested estimate -/

theorem hardyShrink_slice (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℝ → ℝ → ℝ) (n s : ℕ), 3 ≤ n → s + 1 ≤ k →
      Work.FTS.EllipticEst.SmoothOpen F → Work.FTS.PhiStar.ThetaTraces α k F →
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2
              * (Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ
                * (Work.Spaces.DzIter s F z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
          ≤ ENNReal.ofReal C
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ)) := by
  have hgam1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hgam32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hCpos : 0 < 8 / (Work.Spaces.gam α - 1) ^ 2 := by
    have h : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
    exact div_pos (by norm_num) (pow_pos h 2)
  refine ⟨8 / (Work.Spaces.gam α - 1) ^ 2, hCpos, ?_⟩
  intro F n s hn hs hF hB z hz
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2n_lt : 2 / (n : ℝ) < Real.pi / 2 := by
    rw [div_lt_iff₀ hnR]
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  -- ## the vanishing traces, from `ThetaTraces`
  have hBD := hB s hs z hz
  have htraceL : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.DzIter s F z θ) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Work.Spaces.mixed_zero_right] using hBD.1
  have htraceR : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.DzIter s F z θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa only [Work.Spaces.mixed_zero_right] using hBD.2
  have hlL : ∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Ioi 0), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have hmem : ∀ᶠ θ : ℝ in nhds (0 : ℝ), θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2) :=
      isOpen_Ioo.mem_nhds ⟨by norm_num, by linarith [Real.pi_pos]⟩
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with θ h1 h2
    exact ⟨h2, h1.2⟩
  have hlR : ∀ᶠ θ : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have hmem : ∀ᶠ θ : ℝ in nhds (Real.pi / 2), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 + 1) :=
      isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with θ h1 h2
    exact ⟨h1.1, h2⟩
  have hsliceL := Work.FTS.ClassC.tendsto_of_sin_rpow_sq hgam1 hlL htraceL
  have hsliceR := Work.FTS.ClassC.tendsto_of_sin_rpow_sq hgam1 hlR htraceR
  -- ## smoothness of the scaled slices
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.DzIter s F z θ)
      (Set.Ioo 0 (Real.pi / 2)) := (hF.DzIter s).curry_θ hz
  have hsmvL : ContDiffOn ℝ 1 (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (Set.Ioo 0 (2 / (n : ℝ))) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ) (Set.Ioo 0 (2 / (n : ℝ))) := by
      simpa only [smul_eq_mul] using
        (hsm.mono (Set.Ioo_subset_Ioo_right h2n_lt.le)).const_smul (Work.Spaces.w z)
    exact h1.of_le (by simp [Work.Stability.smoothOrder])
  have hsmvR : ContDiffOn ℝ 1 (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2)) := by
    have hle : (0 : ℝ) ≤ Real.pi / 2 - 2 / (n : ℝ) := by linarith [h2n_lt]
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
        (Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2)) := by
      simpa only [smul_eq_mul] using
        (hsm.mono (Set.Ioo_subset_Ioo_left hle)).const_smul (Work.Spaces.w z)
    exact h1.of_le (by simp [Work.Stability.smoothOrder])
  have htrvL : Filter.Tendsto (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hsliceL.const_mul (Work.Spaces.w z)
  have htrvR : Filter.Tendsto (fun θ => Work.Spaces.w z * Work.Spaces.DzIter s F z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hsliceR.const_mul (Work.Spaces.w z)
  -- ## the pointwise majorants
  have homegaL : ∀ θ ∈ Set.Ioo 0 (2 / (n : ℝ)),
      (Work.Spaces.mixed s 1 F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have ho : Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
        = Work.Spaces.HkIntegrand α k F z θ := by
      rw [Work.FTS.PhiStar.Honesty.CptApp.omegaPart,
        if_pos (Work.FTS.PhiStar.Honesty.CptApp.mem_Omega_of_lt_th hθ.2)]
    rw [ho]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ 1 s le_rfl (by omega)
  have homegaR : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
      (Work.Spaces.mixed s 1 F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have ho : Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
        = Work.Spaces.HkIntegrand α k F z θ := by
      rw [Work.FTS.PhiStar.Honesty.CptApp.omegaPart,
        if_pos (Work.FTS.PhiStar.Honesty.CptApp.mem_Omega_of_gt_th hθ.1)]
    rw [ho]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ 1 s le_rfl (by omega)
  have hbdL : ∀ θ ∈ Set.Ioo 0 (2 / (n : ℝ)),
      (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (deriv (fun θ' => Work.Spaces.w z * Work.Spaces.DzIter s F z θ') θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, h2n_lt]⟩
    rw [deriv_const_mul_field]
    rw [show (Work.Spaces.w z * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ) ^ 2
        = (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2 by ring]
    rw [Work.FTS.PhiStar.Honesty.CptApp.EstAux.sin_rpow_deriv_sq_eq α F hF s hz hθ']
    exact homegaL θ hθ
  have hbdR : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 2 / (n : ℝ)) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        * (deriv (fun θ' => Work.Spaces.w z * Work.Spaces.DzIter s F z θ') θ) ^ 2
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [h2n_lt, hθ.1], hθ.2⟩
    rw [deriv_const_mul_field]
    rw [show (Work.Spaces.w z * deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ) ^ 2
        = (deriv (fun θ' => Work.Spaces.DzIter s F z θ') θ * Work.Spaces.w z) ^ 2 by ring]
    rw [Work.FTS.PhiStar.Honesty.CptApp.EstAux.sin_rpow_deriv_sq_eq α F hF s hz hθ']
    exact homegaR θ hθ
  exact shrink_slice_abstract hn hgam1 hgam32 hsmvL htrvL hsmvR htrvR hbdL hbdR

end Work.FTS.PhiStar.Honesty.CptApp.Est
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_Dz_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

/-! ## Helper identities for the `D_z`-index shift

The identity `mixed p q (D_z X) = mixed (p+1) q X` splits into two independent pieces:

* the *commutation* `D_θ^q (D_z X) = D_z (D_θ^q X)` on the open quadrant, which is Clairaut's
  theorem at the finite order `q + 1 ≤ 3` (this is
  `Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin`, since `D_z = D_z^1`);
* the purely *definitional* identity `D_z^p (D_z f) = D_z^{p+1} f`
  (`Work.Spaces.DzIter_add_right` at `(p,1)`), together with the locality of the `D_z`-iterates
  on an open set (an induction on `p` whose step is `Work.Spaces.pz_congr_of_isOpen`). -/

/-- The iterates of `D_z` are local: two functions that agree on an open set `V` have the same
`D_z^p` at every point of `V`.  (Induction on `p`, the step being `pz_congr_of_isOpen`.) -/
private theorem DzIter_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) (p : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter p f))
      (Function.uncurry (Work.Spaces.DzIter p f')) V := by
  induction p with
  | zero => exact h
  | succ n ih =>
      intro y hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter n f) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter n f') y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]

theorem mixed_Dz_shift {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {p q : ℕ} (hpq : p + q ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed p q (Work.Spaces.Dz X) z θ = Work.Spaces.mixed (p + 1) q X z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨hz, hθ0, hθ1⟩
  -- Clairaut at the finite order `q + 1 ≤ 3`: `D_θ^q` crosses the single `D_z`.
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.DthIter q (Work.Spaces.DzIter 1 X)))
      (Function.uncurry (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q X)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin Work.FTS.EllipticEst.isOpen_Q0 3 hX q 1
      (by omega)
  -- Transport this identity through the `p` outer `D_z`-iterates (locality on the open
  -- quadrant), then absorb `D_z^p ∘ D_z` into `D_z^{p+1}`.
  have hstep : Work.Spaces.DzIter p (Work.Spaces.DthIter q (Work.Spaces.DzIter 1 X)) z θ
      = Work.Spaces.DzIter p (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q X)) z θ :=
    DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm p hQ
  show Work.Spaces.DzIter p (Work.Spaces.DthIter q (Work.Spaces.DzIter 1 X)) z θ
      = Work.Spaces.DzIter (p + 1) (Work.Spaces.DthIter q X) z θ
  rw [hstep]
  exact congrFun (congrFun
    (Work.Spaces.DzIter_add_right p 1 (Work.Spaces.DthIter q X)).symm z) θ

end Work.FTS_RegExport.RXT.Sys.GdotAux
end
-- ===== merged: Submission.Work.H2W.weakSliceZContinuousAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2W

set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## Slice continuity on `Icc` from the two one-sided endpoint limits -/

/-- A function continuous on the open angular interval is a.e. strongly measurable for the
restricted measure on `Iθ` (the two endpoints are null). -/
theorem aesm_of_continuousOn_Ioo {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict Iθ) := by
  have h1 : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hf.aestronglyMeasurable measurableSet_Ioo
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))] at h1
  exact h1

/-! ## The endpoint values of the slices

`Ψ · 0` and `Ψ · (π/2)` are identically zero (`EllWeakPos.zero`, `EllWeakPos.pi_half`), so all
`z`-derivatives of `Ψ`, and hence all the slices appearing below, vanish at `θ = 0` and
`θ = π/2`. -/

theorem pz_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pz Ψ z 0 = 0 := by
  have hfun : (fun z' : ℝ => Ψ z' 0) = fun _ => (0 : ℝ) := funext fun z' => h.zero z'
  show deriv (fun z' : ℝ => Ψ z' 0) z = 0
  rw [hfun, deriv_const]

theorem pz_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pz Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' : ℝ => Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => h.pi_half z'
  show deriv (fun z' : ℝ => Ψ z' (Real.pi / 2)) z = 0
  rw [hfun, deriv_const]

theorem pzIter_two_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pzIter 2 Ψ z 0 = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.pz Ψ z' 0) = fun _ => (0 : ℝ) :=
    funext fun z' => pz_zero_at_zero h z'
  show deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' 0) z = 0
  rw [hfun, deriv_const]

theorem pzIter_two_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.pz Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => pz_zero_at_pi_half h z'
  show deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' (Real.pi / 2)) z = 0
  rw [hfun, deriv_const]

theorem aslice_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0 := by
  rw [pzIter_two_zero_at_zero h z, mul_zero]

theorem aslice_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0 := by
  rw [pzIter_two_zero_at_pi_half h z, mul_zero]

theorem dzIter_two_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.DzIter 2 Ψ z 0 = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) = fun _ => (0 : ℝ) :=
    funext fun z' => dz_zero_at_zero h z'
  show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0 = 0
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0
      = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) z from rfl, hfun, deriv_const,
    mul_zero]

theorem dzIter_two_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => dz_zero_at_pi_half h z'
  show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2) = 0
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2)
      = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) z from rfl, hfun,
    deriv_const, mul_zero]

/-! ## Integrability of the square of the `A`-slice -/

/-- `(z²∂_z²Ψ(z,·))²` is integrable on `Iθ`: it is the `i = 0` weighted `D_z`-slot of
`HkMem α 2 (z²∂_z²Ψ)`, divided by the weight `sEta ≥ 1` on the open interval. -/
theorem aslice_sq_integrableOn (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
      Work.Spaces.Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hslot :=
    (Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (k := 2) (le_refl 2) h z hz)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have h1 := hslot.2.2.2.2.1
    refine MeasureTheory.IntegrableOn.congr_fun (h1.const_mul (z ^ 4))
      (fun θ _ => ?_) measurableSet_Icc
    show z ^ 4 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    ring
  have hcont : ContinuousOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.SmoothOpen.curry_θ
      (Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso) hz).continuousOn).pow 2
  have haesm := aesm_of_continuousOn_Ioo hcont
  refine Integrable.mono' h2 haesm ?_
  have hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ),
      ‖(z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2‖
        ≤ (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hs : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
        rw [Work.FTS.EllipticEst.sEta]
        have h0 : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
        have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        have h2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
        have h3 := Real.rpow_le_rpow_of_nonpos h0 h1 h2
        rwa [Real.one_rpow] at h3
      nlinarith [sq_nonneg (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)])
  exact hb

/-! ## The `A`-slice is continuous on `Icc` when the two moments vanish -/

/-- If the two moments `F_*(D_z²F)(z)` and `F_*(D_z⁴Ψ)(z)` vanish, then the `A`-slice
`θ ↦ z²∂_z²Ψ(z,θ)` is continuous on the closed angular interval. -/
theorem aslice_continuousOn (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z)
    (h2F : Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0)
    (h4 : Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0) :
    ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have hall : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) := fun n =>
    contDiffOn_iff_forall_nat_le.mp (hAso.curry_θ hz) n le_top
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.H2W.aSliceHonest α F Ψ hα hα4 h z (Set.mem_Ici.mpr hz.le)
  have hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1
        (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    asliceLzero1Energy α F Ψ h z hz
  have h3 := aslice_sq_integrableOn (α := α) (F := F) h hz
  have hmom : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1
      (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * Work.Elliptic.sinCos2 θ) = 0 := by
    rw [asliceMomentEq α F Ψ h z hz, h2F, h4]
    ring
  have hleft := Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
    (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (hall 2) h2 hL h3 hmom
  have hright := (Work.FTS.EllipticEst.H2W.weakSliceLimits
    (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hall (aslice_zero_at_zero h z)
    (aslice_zero_at_pi_half h z) h2 hL).2.2.1
  exact continuousOn_Icc_of_limits (hall 0).continuousOn
    (by rw [aslice_zero_at_zero h z]; exact hleft)
    (by rw [aslice_zero_at_pi_half h z]; exact hright)

/-! ## The `D_zΨ`-slice is continuous on `Icc` -/

theorem dzPsi_continuousOn (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.Dz Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨hl, hr⟩ := dzPsiSliceLimits α F Ψ h z hz
  have hcont : ContinuousOn (fun θ => z * Work.Spaces.pz Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.SmoothOpen.curry_θ (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)
      hz).continuousOn).const_mul z
  have h0 : Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := hl.const_mul z
    simpa using hh
  have hp : Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have hh := hr.const_mul z
    simpa using hh
  exact continuousOn_Icc_of_limits hcont
    (by
      show Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ) (𝓝[>] (0 : ℝ))
        (𝓝 (z * Work.Spaces.pz Ψ z 0))
      rw [pz_zero_at_zero h z, mul_zero]
      exact h0)
    (by
      show Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ) (𝓝[<] (Real.pi / 2))
        (𝓝 (z * Work.Spaces.pz Ψ z (Real.pi / 2)))
      rw [pz_zero_at_pi_half h z, mul_zero]
      exact hp)

/-! ## The `D_z²Ψ`-slice is continuous on `Icc` when the two moments vanish -/

/-- The `D_z²Ψ`-slice is the sum of the `D_zΨ`-slice (continuous by `dzPsi_continuousOn`) and
the `A`-slice (continuous when the two moments vanish), by the product rule
`D_z²Ψ = D_zΨ + z²∂_z²Ψ`; the identity also holds at the two endpoints, where every term is `0`. -/
theorem dzIterTwo_continuousOn (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z)
    (h2F : Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0)
    (h4 : Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0) :
    ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA := aslice_continuousOn hα hα4 h hz h2F h4
  have hdz := dzPsi_continuousOn (α := α) (F := F) h hz
  refine (hdz.add hA).congr ?_
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]
    show Work.Spaces.DzIter 2 Ψ z 0
      = Work.Spaces.Dz Ψ z 0 + z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0
    rw [aslice_zero_at_zero h z, dz_zero_at_zero h z, dzIter_two_zero_at_zero h z]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1]
      show Work.Spaces.DzIter 2 Ψ z (Real.pi / 2)
        = Work.Spaces.Dz Ψ z (Real.pi / 2) + z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2)
      rw [aslice_zero_at_pi_half h z, dz_zero_at_pi_half h z,
        dzIter_two_zero_at_pi_half h z]
      ring
    · show Work.Spaces.DzIter 2 Ψ z θ
        = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      rw [Work.FTS.EllipticEst.H2W.PsiSlices.DzIter_two_eq hΨso hz ⟨h0, h1⟩,
        show Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ from rfl]

/-! ## The target -/

theorem weakSliceZContinuousAe : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2))
        ∧ ContinuousOn (fun θ => Work.Spaces.Dz (Work.Spaces.Dz Ψ) z θ)
            (Set.Icc 0 (Real.pi / 2)) := by
  intro α F Ψ hα hα4 h
  have hfour : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0 := fstarDzIterFourAe α F Ψ h
  have htwoF : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 :=
    Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F_ae α F Ψ h
  have hgoal : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), 0 < z →
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2))
        ∧ ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
    filter_upwards [hfour, htwoF, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z h4z h2Fz _
    intro hz
    exact ⟨aslice_continuousOn hα hα4 h hz h2Fz h4z,
      dzIterTwo_continuousOn hα hα4 h hz h2Fz h4z⟩
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hgoal
  filter_upwards [hgoal] with z hz _ hzpos
  exact hz (Set.mem_Ioi.mpr hzpos) hzpos

end Work.H2W
end
end
