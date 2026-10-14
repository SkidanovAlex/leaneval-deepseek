import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_MuLamOK.Rows.Rl1Pieces
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.NSSplit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The split of the straightened stream function -/





end Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Pointwise domination of the slots of `HkIntegrand`, with the weight `sin(2θ)^{-η}` -/

/-- On the open angular interval, `sin(2θ)^{-η} ≤ sin(2θ)^{-γ(α)}` for `0 < α` (both weights
are `≥ 1`, and `γ ≥ η`). -/
theorem fkSliceSup_sin_rpow_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hle : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    have h1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    have h2 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
    linarith
  have hγ : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1 hle
  rw [Real.rpow_neg (le_of_lt hs0), Real.rpow_neg (le_of_lt hs0)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hs0 Work.Spaces.eta)
    (Real.rpow_pos_of_pos hs0 (Work.Spaces.gam α))).mpr hγ

/-- On the open quadrant, a *mixed* slot times `(w z)²` is dominated by `HkIntegrand`, with the
`η`-weight in place of the `γ`-weight. -/
theorem fkSliceSup_mixed_slot_le {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hstep : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_left (fkSliceSup_sin_rpow_le hα hθ)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have heq : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθI]
    ring
  rw [heq] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij)

/-- On the open quadrant, a *radial* slot times `(w z)²` is dominated by `HkIntegrand`, with the
`η`-weight in place. -/
theorem fkSliceSup_dz_slot_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j : ℕ} (hj : j ≤ k) :
    (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hrew : (Work.Spaces.DzIter j f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, Work.FTS.H2.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta
      hs0.le (ne_of_gt Work.Spaces.eta_pos)]
    ring
  have hzle := Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hj
  rwa [hrew] at hzle

/-- **The window domination of the `z`-derivative slot**: with `w` on the slot, the `η`-weight
in front. -/
theorem fkSliceSup_slot_wt_le {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hij : i + j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp only [Work.Spaces.mixed_zero_right]
    have h := fkSliceSup_dz_slot_le α k f hz hθ (j := j) (by omega)
    have hrew : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter j f z θ * Work.Spaces.w z) ^ 2
        = (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow]; ring
    rw [hrew]
    exact h
  · have h := fkSliceSup_mixed_slot_le hα k f hz hθ (j := j) (i := i) hi hij
    have hrew : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
        = (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow]; ring
    rw [hrew]
    exact h

/-- **The bare slot domination**: `sin(2θ)^{-η}(D_z^jD_θ^if z θ)² ≤ HkIntegrand α k f z θ` on the
open quadrant, as soon as the slot `(j,i)` is one of the slots of `ℋ^k`.  (The `w² ≥ 1` of
`fkSliceSup_slot_wt_le` is dropped.) -/
theorem fkSliceSup_slice_integrand_le {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hij : i + j ≤ k) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hsin0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  have h := fkSliceSup_slot_wt_le hα k f hz hθ hij
  have hle : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hsin0.le _)
    calc (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2 := by rw [mul_pow]
  exact le_trans hle h

/-- The same domination without the `η`-weight: `(D_z^jD_θ^if z θ)² ≤ HkIntegrand α k f z θ`
(used for the integrability of the bare squared slice). -/
theorem fkSliceSup_sq_le_HkIntegrand {α : ℝ} (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j i : ℕ} (hij : i + j ≤ k) :
    (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hs0.le hs1 Work.Spaces.eta_nonneg
  have hkey : (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 1 := by
    rw [← Real.rpow_add hs0, show Work.Spaces.eta + -(Work.Spaces.eta) = 0 by ring,
      Real.rpow_zero]
  have hbase := fkSliceSup_slice_integrand_le hα k f hz hθ hij
  calc (Work.Spaces.mixed j i f z θ) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed j i f z θ) ^ 2) := by
        rw [show (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * (Work.Spaces.mixed j i f z θ) ^ 2)
            = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              * (Work.Spaces.mixed j i f z θ) ^ 2 from by ring, hkey, one_mul]
    _ ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.eta) * Work.Spaces.HkIntegrand α k f z θ :=
        mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hs0.le _)
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := by
        simpa using mul_le_mul_of_nonneg_right h1 (Work.Spaces.HkIntegrand_nonneg α k f z θ)

/-! ## Integrability of the `θ`-slices -/

/-- The weighted squared slice `θ ↦ sin(2θ)^{-η}(D_z^jD_θ^if z θ)²` is integrable on `Iθ`, for
every `z > 0`, as soon as the slot `(j,i)` occurs in `ℋ^k`. -/
theorem fkSliceSup_slice_integrable {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hij : i + j ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le)) ?_ ?_
  · refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) ?_ hz
    have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        Work.FTS.EllipticEst.Q0 :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
    exact h1.mul ((hF.mixed j i).continuousOn.pow 2)
  · filter_upwards [ae_mem_Ioo_Iθ_k] with θ hθ
    have hsin0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hsin0.le _) (sq_nonneg _))]
    exact fkSliceSup_slice_integrand_le hα k f hz hθ hij

/-- The bare squared slice `θ ↦ (D_z^jD_θ^if z θ)²` is integrable on `Iθ` for every `z > 0`. -/
theorem fkSliceSup_sq_integrable {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hij : i + j ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ => (Work.Spaces.mixed j i f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le)) ?_ ?_
  · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      ((hF.mixed j i).continuousOn.pow 2) hz)
  · filter_upwards [ae_mem_Ioo_Iθ_k] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact fkSliceSup_sq_le_HkIntegrand hα k f hz hθ hij

/-! ## The window step at a fixed angle -/

/-- **The window estimate at a fixed angle.**  For `z > 0`, an interior angle `σ`, a slot
`(j,i)` with `i + j + 1 ≤ k` (so that both `(j,i)` and `(j+1,i)` occur in `ℋ^k`) and a window
radius `R₀ ≥ z` (`d = 2/R₀`):

  `sin(2σ)^{-η}(D_z^jD_θ^if z σ)² ≤ (2 + d)·∫_z^∞ HkIntegrand α k f s σ ds`.

The two window integrands of `half_line_window_bound` are dominated by `HkIntegrand` multiplied
by `sin(2σ)^{η}` (`fkSliceSup_slice_integrand_le` at the slots `(j+1,i)` and `(j,i)`), so
multiplying the window inequality by `sin(2σ)^{-η}` cancels the weight. -/
theorem fkSliceSup_window_step {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hji : i + j + 1 ≤ k) {z σ R₀ d : ℝ} (hz : 0 < z) (hR : z ≤ R₀)
    (hd : d = 2 / R₀) (hσ : σ ∈ Set.Ioo 0 (π / 2))
    (hσint : MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α k f s σ)
      Work.Spaces.Iz) :
    (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z σ) ^ 2
      ≤ (2 + d) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  have hs0 : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  -- derivatives, continuity and integrability on the two windows
  have hderiv : ∀ x ∈ Set.Icc z (2 * R₀), HasDerivAt (fun x => Work.Spaces.mixed j i f x σ)
      (Work.Spaces.pz (Work.Spaces.mixed j i f) x σ) x :=
    fun x hx => (hF.mixed j i).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
  have hcont : ContinuousOn (fun x => Work.Spaces.mixed j i f x σ) (Set.Icc R₀ (2 * R₀)) :=
    ((hF.mixed j i).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
  have hcont' : ContinuousOn (fun x => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
      (Set.Icc z (2 * R₀)) :=
    (((hF.mixed j i).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
  have hint : MeasureTheory.IntegrableOn (fun x => (Work.Spaces.mixed j i f x σ) ^ 2)
      (Set.Icc R₀ (2 * R₀)) :=
    (hcont.pow 2).integrableOn_Icc
  have hwin := Work.FTS.TransportS.half_line_window_bound hz hR hderiv hcont hcont' hint
  -- the continuity of the weighted integrands
  have hcontW : ContinuousOn (fun x : ℝ =>
      x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x)
      (Set.Icc z (2 * R₀)) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
  have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.Icc z (2 * R₀)) := by
    have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
        Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
    have hc := (hF.continuousOn_HkIntegrand α k).comp
      (continuousOn_id.prodMk continuousOn_const) hmap
    simpa only [Function.comp_def, id_eq] using hc
  -- the pointwise window estimates, localised
  set u : ℝ := (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) with hu_def
  have hu : 0 ≤ u := by rw [hu_def]; exact Real.rpow_nonneg hs0.le _
  set IA : ℝ := ∫ x in z..(2 * R₀),
    (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2 with hIA_def
  set IB : ℝ := ∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2 with hIB_def
  have hwin' : (Work.Spaces.mixed j i f z σ) ^ 2 ≤ 2 * IA + d * IB := by
    rw [hIA_def, hIB_def, hd]
    exact hwin
  -- the two window integrals, with the weight `u` pulled in
  have huAint : IntervalIntegrable (fun x : ℝ => u
      * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u
        * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact continuousOn_const.mul (hcontW.pow 2)
  have hHkAint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume z (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hz2R]
    exact hHkcont
  have huBint : IntervalIntegrable (fun x : ℝ => u * (Work.Spaces.mixed j i f x σ) ^ 2)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => u * (Work.Spaces.mixed j i f x σ) ^ 2)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact continuousOn_const.mul (hcont.pow 2)
  have hHkBint : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α k f x σ)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
  have hptA : ∀ x ∈ Set.Icc z (2 * R₀), u
      * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
    have hcomm : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
        = Work.Spaces.mixed (j + 1) i f x σ := rfl
    rw [hcomm]
    exact fkSliceSup_slot_wt_le hα k f hxpos hσ (by omega)
  have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀), u * (Work.Spaces.mixed j i f x σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f x σ := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx.1
    exact fkSliceSup_slice_integrand_le hα k f hxpos hσ (by omega)
  have hIA_le : u * IA ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [hIA_def, ← intervalIntegral.integral_const_mul]
    refine le_trans (intervalIntegral.integral_mono_on hz2R huAint hHkAint hptA) ?_
    rw [intervalIntegral.integral_of_le hz2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
  have hIB_le : u * IB ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ := by
    rw [hIB_def, ← intervalIntegral.integral_const_mul]
    refine le_trans (intervalIntegral.integral_mono_on hR2R huBint hHkBint hptB) ?_
    rw [intervalIntegral.integral_of_le hR2R]
    refine MeasureTheory.setIntegral_mono_set hσint
      (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α k f x σ) ?_
    exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
  -- assembly
  have hmain : u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ 2 * (u * IA) + d * (u * IB) := by
    have h1 : u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ u * (2 * IA + d * IB) :=
      mul_le_mul_of_nonneg_left hwin' hu
    calc u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ u * (2 * IA + d * IB) := h1
      _ = 2 * (u * IA) + d * (u * IB) := by ring
  have hfinal : u * (Work.Spaces.mixed j i f z σ) ^ 2
      ≤ (2 + d) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by
    have h2 : 2 * (u * IA) + d * (u * IB)
        ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
          + d * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) :=
      add_le_add (mul_le_mul_of_nonneg_left hIA_le (by norm_num))
        (mul_le_mul_of_nonneg_left hIB_le (by rw [hd]; positivity))
    calc u * (Work.Spaces.mixed j i f z σ) ^ 2 ≤ 2 * (u * IA) + d * (u * IB) := hmain
      _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ)
            + d * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := h2
      _ = (2 + d) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α k f s σ) := by ring
  rw [hu_def] at hfinal
  exact hfinal

/-! ## The uniform-in-`z` weighted slice bound -/

/-- **The graded weighted slice bound.**  For a datum which is `C^∞` on the open quadrant and
`ℋ^k`-honest, every slot `(j,i)` with `i + j + 1 ≤ k` satisfies, for **every** `z > 0`,

  `∫_θ sin(2θ)^{-η}(D_z^jD_θ^if z θ)² dθ ≤ 3 ∫∫ HkIntegrand α k f`.

The constant `3` is universal (independent of `α`, `k`, `f`, `z`): the window step with
`R₀ = max z 2` gives `∫_θ … ≤ 3 ∫_σ ∫_s HkIntegrand`, and the double integral is `HkSq` by
Tonelli (`swapK`). -/
theorem fkSliceSup_sliceSupGraded {α : ℝ} (hα : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    ∀ (j i : ℕ), i + j + 1 ≤ k → ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.mixed j i f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α k f := by
  intro j i hji z hz
  obtain ⟨hswap, hGint, hGslice⟩ := swapK α k f hF hmem
  have hbound : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.mixed j i f z σ) ^ 2
        ≤ (2 + 2 / max z 2) * (∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) := by
    filter_upwards [hGslice, ae_mem_Ioo_Iθ_k] with σ hσint hσθ
    exact fkSliceSup_window_step hα hF hmem hji hz (le_max_left z 2) rfl hσθ hσint
  have hLI := fkSliceSup_slice_integrable hα hF hmem (j := j) (i := i) (by omega) hz
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
    have h2max : 2 ≤ max z 2 := le_max_right z 2
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed j i f z θ) ^ 2)
      ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / max z 2) * (∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) :=
        MeasureTheory.integral_mono_ae hLI (hGint.const_mul _) hbound
    _ = (2 + 2 / max z 2) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α k f s σ) := MeasureTheory.integral_const_mul _ _
    _ = (2 + 2 / max z 2) * Work.Spaces.HkSq α k f := by rw [hswap]
    _ ≤ 3 * Work.Spaces.HkSq α k f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α k f)

/-! ## The target -/

theorem fkSliceSup : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ z : ℝ, 0 < z → |Work.Construction.FK f z| ≤ C * M) ∧
      ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0) ∧
      (∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2) ≤ C * M ^ 2) ∧
      (∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.Dth f z θ) ^ 2) ≤ C * M ^ 2) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hαI f M hD
  obtain ⟨hα0, hα1⟩ := hαI
  have hSO : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO 4 (by norm_num) hmem6
  have hXn : Work.Spaces.HkNorm α 4 f ≤ M := hD.bdd
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXn
  have hSq4 : Work.Spaces.HkSq α 4 f ≤ M ^ 2 := by
    have h1 : (Work.Spaces.HkNorm α 4 f) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 f) hXn 2
    rwa [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)] at h1
  -- the two weighted slice bounds
  have hslice0 : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2)
      ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro z hz
    have h := fkSliceSup_sliceSupGraded hα0 hSO hmem4 0 0 (by norm_num) z hz
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  have hslice1 : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.Dth f z θ) ^ 2)
      ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro z hz
    have h := fkSliceSup_sliceSupGraded hα0 hSO hmem4 0 1 (by norm_num) z hz
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using h
  -- the angular moment
  have hf2 : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro z hz
    have hI1 : MeasureTheory.Integrable (fun θ => (f z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h := fkSliceSup_sq_integrable hα0 hSO hmem4 (j := 0) (i := 0) (by norm_num) hz
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    have hI2 : MeasureTheory.Integrable (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (f z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h := fkSliceSup_slice_integrable hα0 hSO hmem4 (j := 0) (i := 0) (by norm_num) hz
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (f z θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2 := by
      filter_upwards [Work.FTS.H2.ae_sin_two_pos] with θ hsin
      have h1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Work.FTS.H2.one_le_rpow_neg hsin (Real.sin_le_one _) Work.Spaces.eta_nonneg
      nlinarith [sq_nonneg (f z θ)]
    exact le_trans (MeasureTheory.integral_mono_ae hI1 hI2 hpt) (hslice0 z hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `|FK f z| ≤ 100 M`
    intro z hz
    have hFK2 : (Work.Construction.FK f z) ^ 2 ≤ 16 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 := by
      have h := FKdzIter_sq_le hSO hmem6 0 (by norm_num) hz
      simpa only [Work.Spaces.DzIter_zero] using h
    have hsq : (Work.Construction.FK f z) ^ 2 ≤ (7 * M) ^ 2 := by
      have h2 := hf2 z hz
      nlinarith [hSq4, hM0, sq_nonneg M]
    have h7M : 0 ≤ 7 * M := by linarith
    calc |Work.Construction.FK f z| = Real.sqrt ((Work.Construction.FK f z) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((7 * M) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 7 * M := Real.sqrt_sq h7M
      _ ≤ 100 * M := by linarith
  · -- continuity
    exact fk_cont_FK hSO hmem4
  · -- the `f`-slice
    intro z hz
    have h := hslice0 z hz
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2)
        ≤ 3 * Work.Spaces.HkSq α 4 f := h
      _ ≤ 100 * M ^ 2 := by nlinarith [hSq4, sq_nonneg M]
  · -- the `D_θ f`-slice
    intro z hz
    have h := hslice1 z hz
    calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.Dth f z θ) ^ 2)
        ≤ 3 * Work.Spaces.HkSq α 4 f := h
      _ ≤ 100 * M ^ 2 := by nlinarith [hSq4, sq_nonneg M]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaEnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000
/-! ## The remaining one-dimensional estimate -/

/-- **The `g`-form of `end_bound_fts`.**  After the angular integration by parts the pairing
reduces to `(q-1)·∫_z (g z·w(z)²)·∫_θ cos(2θ)σ^{-q}·h²` with `h = D_z^bD_θ^af`; since
`|q-1| ≤ 1`, `|cos| ≤ 1` and `|g z| ≤ A`, it is dominated by `A·∫∫ρ·h² ≤ A·HkSq α 6 f`
(`leaf_slot_le6`). -/
theorem fk_end_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q A : ℝ} (g : ℝ → ℝ)
    (hα : 0 < α) (hmem6 : Work.Spaces.HkMem α 6 f) (hab : a + b ≤ 6)
    (hqabs : |q - 1| ≤ 1) (hA : 0 ≤ A) (hgA : ∀ z : ℝ, 0 < z → |g z| ≤ A)
    (hleaf : Work.FTS.TransportS.IsLeafW α a
      (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
    (hout : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) :
    |(q - 1) * (∫ z in Work.Spaces.Iz,
        (g z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      ≤ A * Work.Spaces.HkSq α 6 f := by
  have hsnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ Real.sin (2 * θ) :=
    (Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ).mono fun θ hθ =>
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  have hinner_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2|
        ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    filter_upwards [hslice] with z hz
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hz ?_
    filter_upwards [hsnn] with θ hθ
    have hσ : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hθ _
    have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |(Real.sin (2 * θ)) ^ (-q)| = (Real.sin (2 * θ)) ^ (-q) := abs_of_nonneg hσ
    have h3 : |(Work.Spaces.mixed b a f z θ) ^ 2|
        = (Work.Spaces.mixed b a f z θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [abs_mul, abs_mul, h2, h3]
    calc (|Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (1 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcos hσ) (sq_nonneg _)
      _ = (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by ring
  have hmaj_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |(g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        ≤ A * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    filter_upwards [hinner_le, fkTheta_ae_pos] with z hzin hzp
    have hDnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hsnn] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg hθ _) (sq_nonneg _)
    have hW2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    calc |(g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        = |g z| * (Work.Spaces.w z) ^ 2
          * |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hW2]
      _ ≤ A * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
          refine mul_le_mul (mul_le_mul (hgA z hzp) le_rfl (sq_nonneg _) hA) hzin
            (abs_nonneg _) (mul_nonneg hA hW2)
      _ = A * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
  have hmaj : MeasureTheory.IntegrableOn (fun z => A
      * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) Work.Spaces.Iz :=
    hout.const_mul A
  have htarget : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hleafslab := Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6 hα hmem6 a b
    (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) hab hleaf
  calc |(q - 1) * (∫ z in Work.Spaces.Iz,
        (g z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      = |q - 1| * |∫ z in Work.Spaces.Iz,
          (g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := by rw [abs_mul]
    _ ≤ 1 * |∫ z in Work.Spaces.Iz,
          (g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| :=
        mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
    _ = |∫ z in Work.Spaces.Iz,
          (g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := one_mul _
    _ ≤ ∫ z in Work.Spaces.Iz,
        |(g z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, A * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _) hmaj hmaj_le
    _ = A * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
        rw [MeasureTheory.integral_const_mul]
    _ = A * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by rw [htarget]
    _ ≤ A * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hleafslab hA

/-! ## The general radial-multiplier estimate -/

/-- **The `g`-form of `L12ShiftThetaLe`**: for an arbitrary radial multiplier `g` which is
continuous on `(0,∞)` and bounded by `A` there, the shifted `θ`-slot pairing is bounded by
`A·HkSq α 6 f`.  The proof is the angular integration by parts of the two `σ^{-q}D_θh·h`-slots
(which is why the level-`7` slot `D_θh` never has to be priced). -/
theorem fk_radial_shift : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ} {A : ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 7 f →
    ∀ (g : ℝ → ℝ), ContinuousOn g (Set.Ioi 0) → 0 ≤ A →
      (∀ z : ℝ, 0 < z → |g z| ≤ A) →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |∫ z in Work.Spaces.Iz, g z *
            (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ)|
          ≤ C * A * Work.Spaces.HkSq α 6 f := by
  refine ⟨1, one_pos, ?_⟩
  intro α f A hα hα1 hO hmem6 hmem7 g hgc hA hgA a b ρ hab hρ
  simp only [one_mul]
  have main : ∀ (q : ℝ) (ρ : ℝ → ℝ → ℝ),
      |q - 1| ≤ 1 → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      ρ = (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, g z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ A * Work.Spaces.HkSq α 6 f := by
    intro q ρ hqabs hqle hq0 hρq hρlem
    subst hρq
    obtain ⟨hi0, hi1, hi2, hout, hslice⟩ :=
      fk_ibp_integrable (f := f) g hα hA hgc hgA hO hmem6 hmem7 hab hqle hq0
    -- Step A: pull the radial weight `(w z)²` out of the angular integral.
    have hAint : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ := by
      intro z
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    have hA' : (∫ z in Work.Spaces.Iz, g z *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show g z *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      rw [hAint z]
      ring
    -- Step B: replace `D_z^bD_θ^{a+1}f` by `D_θ(D_z^bD_θ^a f)` inside the angular integral.
    have hB : (∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [fkTheta_ae_pos] with z hz
      have hinner : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
        have h2 := Work.FTS.StrongPersist.H6Pair6Aux.dth_mixed_eqOn_Q0 (f := f) hO a b
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ.1, hθ.2⟩)
        have h1 : Work.Spaces.mixed b (a + 1) f z θ
            = Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ := h2.symm
        rw [h1]
      show (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
      rw [hinner]
    -- Step C: identify the iterated integral with the `ρ`-weighted pairing `wip`.
    have hC : (∫ z in Work.Spaces.Iz,
            (g z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ))
        = Work.Coercivity.wip
            (fun z θ => (g z * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-q))
            (Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ))
            (fun z θ => Work.Spaces.mixed b a f z θ) := by
      rw [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (g z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
          = ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * ((g z * (Work.Spaces.w z) ^ 2)
                * (Real.sin (2 * θ)) ^ (-q))
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    -- The angular integration by parts.
    have hIBP := Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
        (h := fun z θ => Work.Spaces.mixed b a f z θ)
        (Φ := fun z => g z * (Work.Spaces.w z) ^ 2) (q := q)
        (hO.mixed b a) hi0 hi1 hi2
    rw [hA', hB, hC, hIBP]
    -- The remaining one-dimensional estimate.
    exact fk_end_bound (f := f) g hα hmem6 hab hqabs hA hgA hρlem hout hslice
  rcases hρ with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = w²σ^{-η}`
    subst hρ
    exact main Work.Spaces.eta Work.FTS.TransportS.leafEta
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta, Work.Spaces.gam]; linarith) (fun _ => le_rfl) rfl (Or.inl rfl)
  · -- `ρ = w²`
    subst hρ
    refine main 0 Work.FTS.TransportS.leafOne ?_ (by rw [Work.Spaces.gam]; linarith)
      (fun _ => by rw [Work.Spaces.eta]; norm_num) ?_ (Or.inr (Or.inl rfl))
    · rw [zero_sub, abs_neg, abs_one]
    · funext z θ
      simp [Work.FTS.TransportS.leafOne, Real.rpow_zero]
  · -- `ρ = w²σ^{-γ}` (only for `a ≥ 1`)
    subst hρ
    refine main (Work.Spaces.gam α) (Work.FTS.TransportS.leafGam α) ?_ le_rfl ?_ rfl
      (Or.inr (Or.inr ⟨ha1, rfl⟩))
    · rw [Work.Spaces.gam_sub_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ α / 10)]
      linarith
    · intro ha0; omega

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.FK_w_sq_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

/-- The pointwise (in `z`) identity behind the sharp `L²`-bound for the angular moment:
for `θ ∈ Iθ` the weighted datum `K · Sw · Gaz` is the radial weight times `g · K`. -/
private theorem FK_K_Sw_Gaz_eq {g : ℝ → ℝ → ℝ} (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ * Work.FTS.GalBasis.cc.Gaz g z θ
      = Work.Spaces.w z * (g z θ * Work.Spaces.K θ) := by
  rcases eq_or_ne (Work.FTS.GalBasis.cc.Sw θ) 0 with hS | hS
  · have hK : Work.Spaces.K θ = 0 :=
      Work.FTS.GalBasis.cc.sw_eq_zero_imp_K_eq_zero hθ hS
    rw [hS, hK]
    ring
  · rw [Work.FTS.GalBasis.cc.Gaz_apply, div_eq_mul_inv]
    field_simp

theorem FK_w_sq_bound {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.ClassC.ClassC α g) :
    MeasureTheory.IntegrableOn (fun z => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g := by
  have hmem7 : Work.Spaces.HkMem α 7 g := hg.mem
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    HkMem_mono_le hg.reg (show (4 : ℕ) ≤ 7 by norm_num) hmem7
  -- the per-`z` sharp bound for the weighted angular moment
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    have hint : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 g z θ) Work.Spaces.Iθ := hmem4.1 z hz
    have hcs := Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le α g hint
    -- the weighted angular profile equals the radial weight times `FK`
    have hid : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ * Work.FTS.GalBasis.cc.Gaz g z θ)
        = Work.Spaces.w z * Work.Construction.FK g z := by
      have hcongr : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ * Work.FTS.GalBasis.cc.Gaz g z θ)
          = ∫ θ in Work.Spaces.Iθ, Work.Spaces.w z * (g z θ * Work.Spaces.K θ) := by
        refine MeasureTheory.integral_congr_ae ?_
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => FK_K_Sw_Gaz_eq z θ hθ)
      rw [hcongr, MeasureTheory.integral_const_mul, Work.Construction.FK]
    have hI0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have hBK0 : 0 ≤ Work.FTS.GalBasis.cc.BK := Work.FTS.GalBasis.cc.BK_nonneg
    have hs : |Work.Spaces.w z * Work.Construction.FK g z| ≤ Work.FTS.GalBasis.cc.BK
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
      rw [← hid]; exact hcs
    have hsq : (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
        ≤ (Work.FTS.GalBasis.cc.BK
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.Spaces.w z * Work.Construction.FK g z)) hs 2
      rwa [sq_abs] at h
    have hmain : (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
        ≤ Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
      have hstep : (Work.FTS.GalBasis.cc.BK
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) ^ 2
          = Work.FTS.GalBasis.cc.BK ^ 2
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
        rw [mul_pow, Real.sq_sqrt hI0]
      calc (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
          ≤ (Work.FTS.GalBasis.cc.BK
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) ^ 2 := hsq
        _ = Work.FTS.GalBasis.cc.BK ^ 2
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := hstep
    have hcomm : (Work.Spaces.w z * Work.Construction.FK g z) ^ 2
        = (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    rwa [hcomm] at hmain
  -- measurability of the integrand
  have hmeasw : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    unfold Work.Spaces.w
    fun_prop
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hcont := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fk_cont_FK hg.reg hmem4
    have h1 : AEStronglyMeasurable (fun z => Work.Construction.FK g z)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have hEq : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    have h2 : AEStronglyMeasurable (fun z => Work.Construction.FK g z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set hEq]
      exact h1
    exact (h2.pow 2).mul ((hmeasw.pow_const 2).aestronglyMeasurable)
  have hbigInt : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.GalBasis.cc.BK ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) Work.Spaces.Iz :=
    hmem4.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hbigInt haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt z hz
  · calc (∫ z in Work.Spaces.Iz,
          (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            hbigInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
      _ = Work.FTS.GalBasis.cc.BK ^ 2
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 g z θ) :=
          MeasureTheory.integral_const_mul _ _
      _ = Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g := by
          rw [Work.Spaces.HkSq]

end Work.FTS_EllLimOK.PkgJets
end
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Rows.Rl1Open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem Rl1Open : ∀ Ce Cs : ℝ, ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Φs Φg : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce f Φg →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) := by
  intro Ce Cs
  obtain ⟨Kc, hKcpos, hpiece⟩ := piecesEnv Ce Cs
  refine ⟨20 * Kc + 1, by linarith, ?_⟩
  intro α f Φs Φg hα hα1 hso hmem hs hell
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hEnv0 : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  -- the three inputs of the split
  have hadd := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hso hmem
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α f) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z :=
    fun z hz => hadd.1 z hz.le
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z := hadd.2.1
  have hsp := Work.FTS.NonlinRows.Rl1.splitOpen (α := α) (g := f) (Φs := Φs) (Φg := Φg)
    hα hα1 hso hs.smooth hell.smooth hL (FKaddOpen hα hso hmem) hL12
  -- the exact split of `N` into its twenty summands
  have hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Φg z θ) r θ
        = ∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg k r θ := by
    intro r θ hq
    rw [hsp r θ hq]
    simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  -- the measurability and the `L¹(dr/r)`-triangle inequality
  have hmeas := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.meas_open hα hα1 hso hmem hs hell
  have htri := Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
    (N := Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Φg z θ))
    (p := Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg) hsplit hmeas.1 hmeas.2
  -- the twenty per-piece bounds
  have hsum : (∑ k : Fin 20,
        Fa (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg k))
      ≤ ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
    have h1 : ∑ k : Fin 20, Fa (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg k)
        ≤ ∑ _k : Fin 20, ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) :=
      Finset.sum_le_sum (fun k _ => hpiece hα hα1 hso hmem hs hell k)
    have h2 : ∑ _k : Fin 20, ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f)
        = 20 • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
      simp [Finset.sum_const, Finset.card_univ]
    have h3 : (20 : ℕ) • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f)
        = ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
      have h20 : (0 : ℝ) ≤ 20 := by norm_num
      have h20e : (20 : ENNReal) = ENNReal.ofReal 20 := (ENNReal.ofReal_natCast 20).symm
      calc (20 : ℕ) • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f)
          = (20 : ENNReal) * ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) :=
            nsmul_eq_mul 20 _
        _ = ENNReal.ofReal 20 * ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
            rw [h20e]
        _ = ENNReal.ofReal (20 * (Kc * Work.FTS.NonlinRows.Rl1.Env α f)) :=
            (ENNReal.ofReal_mul h20).symm
        _ = ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
            congr 1
            ring
    rw [h2, h3] at h1
    exact h1
  -- the `ofReal`-glue and the passage to `|L₁₂(N)(0)|`
  have hkey : ENNReal.ofReal |Work.Construction.L12 (Work.Construction.N α
      (Work.Construction.Ftot α f) (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) :=
    (Work.FTS.Nonlinear.Pieces.ofReal_L12_le _).trans (htri.trans hsum)
  have hfin : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ 20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg (by norm_num) hKcpos.le) hEnv0)).mp hkey
  -- unfold the envelope and enlarge the constant
  refine hfin.trans ?_
  rw [Work.FTS.NonlinRows.Rl1.Env]
  have hB0 : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
      + α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have h2 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (Real.sqrt_nonneg α) hX
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  exact mul_le_mul_of_nonneg_right (by linarith) hB0

end Work.FTS_MuLamOK.Rows
end
