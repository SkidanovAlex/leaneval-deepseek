import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.L12Add
-- ===== merged: Submission.Work.FTS.ClassC.ModeSumZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-! ## The sharp linear sup bound for the eigenfamily -/

/-- **`|eFam m θ| ≤ 3(m+1)` on `Iθ`.**  The interior is `EB.eFam_abs_le_sqrt_N`; at `θ = 0`
the Gegenbauer polynomial `gC (2m+1)` is odd hence vanishes, and at `θ = π/2` the factor
`cos θ` vanishes. -/
theorem abs_eFam_le (m : ℕ) {θ : ℝ} (hθ : θ ∈ Iθ) : |eFam m θ| ≤ 3 * ((m : ℝ) + 1) := by
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have h := Work.FTS.PhiStar.Series.EB.eFam_abs_le_sqrt_N m ⟨h0, h1⟩
      have hN : Work.FTS.PhiStar.Series.EB.Npsi m ≤ (3 * ((m : ℝ) + 1)) ^ 2 := by
        rw [Work.FTS.PhiStar.Series.EB.Npsi]
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      calc |eFam m θ| ≤ Real.sqrt (Work.FTS.PhiStar.Series.EB.Npsi m) := h
        _ ≤ Real.sqrt ((3 * ((m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hN
        _ = 3 * ((m : ℝ) + 1) := Real.sqrt_sq (by positivity)
    · subst h1
      have hz : eFam m (Real.pi / 2) = 0 := by
        simp [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two]
      rw [hz, abs_zero]
      positivity
  · subst h0
    have hz : eFam m 0 = 0 := by
      simp [Work.FTS.PhiStar.Gegenbauer.eFam,
        Work.FTS.PhiStar.Gegenbauer.gC_odd_zero m]
    rw [hz, abs_zero]
    positivity

/-- **The sup bound for a finite mode sum**: `|Σ_{m≤N} b_m e_m θ| ≤ 3·Σ_{m≤N}(m+1)|b_m|`. -/
theorem abs_sum_eFam_le {N : ℕ} (b : ℕ → ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |∑ m ∈ Finset.range (N + 1), b m * eFam m θ|
      ≤ 3 * ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |b m| := by
  calc |∑ m ∈ Finset.range (N + 1), b m * eFam m θ|
      ≤ ∑ m ∈ Finset.range (N + 1), |b m * eFam m θ| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Finset.range (N + 1), |b m| * |eFam m θ| :=
        Finset.sum_congr rfl fun m _ => abs_mul _ _
    _ ≤ ∑ m ∈ Finset.range (N + 1), |b m| * (3 * ((m : ℝ) + 1)) :=
        Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (abs_eFam_le m hθ) (abs_nonneg _)
    _ = 3 * ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |b m| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring

/-! ## `HkSq α 0` as an explicit weighted double integral -/

/-- **`HkSq α 0` in terms of `w²` and `sEta`.** -/
theorem HkSq_zero_eq_w (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Iz, ∫ θ in Iθ, (g z θ) ^ 2 * (w z) ^ 2 * sEta θ := by
  rw [Work.FTS.EllipticEst.Honest.HkSq_zero_eq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
    (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ)]
  rfl

/-! ## The assembly -/


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Slope =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000



end Work.FTS.ClassCHon.Zpz
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CmodeZero.cmode_zero_abs_le_of_cptQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CmodeZero

/-- **The mode-`0` coefficient of a `C^∞` source compactly supported in the open quadrant is
bounded by a constant, uniformly in `z`.**

The source vanishes identically off its support rectangle `[a,b] × [c,d]`, so every slice
`G z ·` is identically zero for `z ∉ [a,b]` (whence `cmode 0 G z = 0`), while for `z ∈ [a,b]`
the Cauchy–Schwarz (Bessel) estimate for a continuous source bounds `cmode 0 G z` by a constant
times `1/√(eNorm 0)`; `eNorm 0 > 0` turns that into a constant. -/
theorem cmode_zero_abs_le_of_cptQ {G : ℝ → ℝ → ℝ} (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, |Work.FTS.PhiStar.Series.cmode 0 G z| ≤ K := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := hG.cpt
  -- joint continuity of the source
  have hcont : Continuous (Function.uncurry G) := (hG.smooth 0).continuous
  -- the source vanishes identically off the support rectangle
  have hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0 := by
    intro z θ hz
    by_contra hne
    exact hz (H z θ hne).1
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.ClassCHon.CmpSupp.cmode_abs_le_of_continuous hcont hsupp
  refine ⟨K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm 0),
    div_nonneg hKpos.le (Real.sqrt_nonneg _), fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · exact hK 0 z hz
  · -- outside the support rectangle the whole slice, hence the mode coefficient, vanishes
    have hfun : (fun θ : ℝ =>
          G z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ) = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hsupp z θ hz, zero_mul, zero_mul]
    have hzero : Work.FTS.PhiStar.Series.cmode 0 G z = 0 := by
      rw [Work.FTS.PhiStar.Series.cmode, hfun]
      simp
    rw [hzero, abs_zero]
    exact div_nonneg hKpos.le (Real.sqrt_nonneg _)

end Work.FTS.PhiStar.Honesty.CmodeZero
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.abs_cmode_le_lzero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- The `m`-th Gegenbauer mode `e_m`, locally abbreviated. -/
private abbrev eF (m : ℕ) : ℝ → ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `cos θ ≥ 0` on `Iθ`. -/
private theorem cos_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-- **The sharp per-mode slice bound.**  For every `m` and every slice `F z ·` whose
`η`-weighted square is integrable on `Iθ`, the squared mode coefficient, weighted by the mode
norm `eNorm m`, is bounded by that weighted square:

  `eNorm m * (cmode m F z)² ≤ ∫_{Iθ} (F z θ)² sin(2θ)^{-η}`. -/
theorem eNorm_mul_cmode_sq_le_sliceMass {m : ℕ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  set Aint : ℝ := ∫ θ in Work.Spaces.Iθ, F z θ * eF m θ * Real.cos θ with hAint
  set target : ℝ := ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with htarget
  set N : ℝ := ∫ θ in Work.Spaces.Iθ,
      (eF m θ * Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hN
  -- the slice mass is nonnegative (the integrand is a nonnegative a.e.-strongly-measurable
  -- function, as `hint` asserts integrability)
  have htnn : 0 ≤ target := by
    rw [htarget]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  -- the second Cauchy–Schwarz factor is dominated by the mode norm
  have hNle : N ≤ Work.EllipticEst.ModalSolution.eNorm m := by
    rw [hN]
    exact eFam_cos_sq_sin_rpow_integral_le_eNorm m
  -- the weighted Cauchy–Schwarz moment bound for the numerator
  have hmoment : Aint ^ 2 ≤ target * N := by
    rw [hAint, htarget, hN]
    exact sliceMass_moment_le (m := m) (F := F) (z := z) hint
  have hfin : Aint ^ 2 ≤ target * Work.EllipticEst.ModalSolution.eNorm m :=
    le_trans hmoment (mul_le_mul_of_nonneg_left hNle htnn)
  -- `cmode` is the numerator divided by the mode norm
  have hcm : Work.FTS.PhiStar.Series.cmode m F z
      = Aint / Work.EllipticEst.ModalSolution.eNorm m := by
    rw [Work.EllipticEst.ModalSolution.cmode_eq m F z]
    congr 1
    rw [hAint, Work.EllipticEst.ModalSolution.bInt]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    have hc : 0 ≤ Real.cos θ := cos_nonneg_Iθ hθ
    conv_rhs => rw [← Real.sq_sqrt hc]
    ring
  have hE : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hpow : (Work.EllipticEst.ModalSolution.eNorm m)
      * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      = Aint ^ 2 / Work.EllipticEst.ModalSolution.eNorm m := by
    rw [hcm]
    field_simp
  calc Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      = Aint ^ 2 / Work.EllipticEst.ModalSolution.eNorm m := hpow
    _ ≤ target * Work.EllipticEst.ModalSolution.eNorm m
          / Work.EllipticEst.ModalSolution.eNorm m :=
        div_le_div_of_nonneg_right hfin (le_of_lt hE)
    _ = target := by
        rw [mul_div_cancel_right₀ _ (ne_of_gt hE)]

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SmoothPieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The open quadrant, in the shape `SmoothOpen`-statements use. -/
abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

/-- A radial factor which is `C^k` on `(0,∞)` times a `C^k` function on the open quadrant is
`C^k` on the open quadrant. -/
theorem contDiffOn_radial_mul {k : ℕ} {X : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ k X (Set.Ioi 0))
    (hψ : ContDiffOn ℝ k (Function.uncurry ψ) Q0) :
    ContDiffOn ℝ k (Function.uncurry (fun z θ => X z * ψ z θ)) Q0 := by
  have h : Function.uncurry (fun z θ => X z * ψ z θ)
      = (fun p : ℝ × ℝ => X p.1) * Function.uncurry ψ := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (hX.comp contDiffOn_fst
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul hψ

/-- Multiplication by a constant, for `C^k`-functions on the open quadrant. -/
theorem contDiffOn_const_mul {k : ℕ} (c : ℝ) {F : ℝ × ℝ → ℝ}
    (h : ContDiffOn ℝ k F Q0) : ContDiffOn ℝ k (fun p => c * F p) Q0 :=
  contDiffOn_const.mul h

/-- The `C^k` smoothness of the six `f`-dependent pieces of `N₀`, from the `C^k` smoothness of
the radial factor `L₁₂(f)` (all the other factors are smooth on the open quadrant). -/
theorem N0piecesSmooth {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) {k : ℕ}
    (hLk : ContDiffOn ℝ k (fun z => Work.Construction.L12 f z) (Set.Ioi 0)) :
    ContDiffOn ℝ k (Function.uncurry (NP3 α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP4a α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP4b α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP5a α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP5b α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP6 α f)) Q0 := by
  have hfk : ContDiffOn ℝ k (Function.uncurry (fun z θ => f z θ)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsmf k
  have hDthk : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.Dth f)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dth f)).mp hsmf.Dth k
  have hDzk : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.Dz f)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz f)).mp hsmf.Dz k
  have hNA4k : ContDiffOn ℝ k (Function.uncurry (NA4 α)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (NA4 α)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA4 α) k
  have hNA5k : ContDiffOn ℝ k (Function.uncurry (NA5 α)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (NA5 α)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA5 α) k
  have hNA6k : ContDiffOn ℝ k (Function.uncurry (NA6 α)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (NA6 α)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA6 α) k
  have hCk : ContDiffOn ℝ k (Function.uncurry (fun z θ => Work.Construction.c2m θ)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (fun z θ => Work.Construction.c2m θ)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.so_snd
        Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m) k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `NP3 = (1/α)·(L₁₂ f · f)`
    refine (contDiffOn_const_mul (1 / α)
      (contDiffOn_radial_mul hLk hfk)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP3, Function.uncurry, Pi.mul_apply]
  · -- `NP4a = (3/(2α))·(L₁₂ f · D_θF_*)`
    refine (contDiffOn_const_mul (3 / (2 * α))
      (contDiffOn_radial_mul hLk hNA4k)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP4a, Function.uncurry, Pi.mul_apply]
  · -- `NP4b = (3/(2α))·(L₁₂ f · D_θ f)`
    refine (contDiffOn_const_mul (3 / (2 * α))
      (contDiffOn_radial_mul hLk hDthk)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP4b, Function.uncurry, Pi.mul_apply]
  · -- `NP5a = (-1)·(L₁₂ f · (c₂ₘ·D_zF_*))`
    refine (contDiffOn_const_mul (-1)
      (contDiffOn_radial_mul hLk hNA5k)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP5a, Function.uncurry, Pi.mul_apply]
  · -- `NP5b = (-1)·(c₂ₘ · L₁₂ f · D_z f)`
    have hψ : ContDiffOn ℝ k
        (Function.uncurry (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz f z θ)) Q0 := by
      have h : Function.uncurry (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz f z θ)
          = (Function.uncurry (fun z θ => Work.Construction.c2m θ))
            * Function.uncurry (Work.Spaces.Dz f) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h]; exact hCk.mul hDzk
    refine (contDiffOn_const_mul (-1)
      (contDiffOn_radial_mul hLk hψ)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP5b, Function.uncurry, Pi.mul_apply]
    ring
  · -- `NP6 = (-1)·(c₂ₘ·L₁₂(F_*)·D_z f)`
    have hψ : ContDiffOn ℝ k
        (Function.uncurry (fun z θ => NA6 α z θ * Work.Spaces.Dz f z θ)) Q0 := by
      have h : Function.uncurry (fun z θ => NA6 α z θ * Work.Spaces.Dz f z θ)
          = Function.uncurry (NA6 α) * Function.uncurry (Work.Spaces.Dz f) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h]; exact hNA6k.mul hDzk
    refine (contDiffOn_const_mul (-1) hψ).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP6, Function.uncurry, Pi.mul_apply]

/-- The seven-fold sum `NA1 + NP3 + … + NP6` of the pieces of `N₀`, as a function. -/
def N0Sum (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ + NP5a α f z θ
    + NP5b α f z θ + NP6 α f z θ

/-- The `C^k` smoothness of the seven-fold sum of the pieces of `N₀`. -/
theorem N0SumSmooth {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) {k : ℕ}
    (hLk : ContDiffOn ℝ k (fun z => Work.Construction.L12 f z) (Set.Ioi 0)) :
    ContDiffOn ℝ k (Function.uncurry (N0Sum α f)) Q0 := by
  obtain ⟨h3, h4a, h4b, h5a, h5b, h6⟩ := N0piecesSmooth (α := α) hsmf hLk
  have h1 : ContDiffOn ℝ k (Function.uncurry (fun z θ => NA1 α z θ)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z θ => NA1 α z θ)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α) k
  have h13 : ContDiffOn ℝ k (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ) + Function.uncurry (NP3 α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h1.add h3
  have h134a : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ)
          + Function.uncurry (NP4a α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h13.add h4a
  have h134ab : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
        + NP4b α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
          + NP4b α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ)
          + Function.uncurry (NP4b α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134a.add h4b
  have h134ab5a : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
        + NP4b α f z θ + NP5a α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
          + NP4b α f z θ + NP5a α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
            + NP4b α f z θ)
          + Function.uncurry (NP5a α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134ab.add h5a
  have h134ab5ab : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
        + NP4b α f z θ + NP5a α f z θ + NP5b α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
          + NP4b α f z θ + NP5a α f z θ + NP5b α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
            + NP4b α f z θ + NP5a α f z θ)
          + Function.uncurry (NP5b α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134ab5a.add h5b
  have hall : ContDiffOn ℝ k (Function.uncurry (N0Sum α f)) Q0 := by
    have h : Function.uncurry (N0Sum α f)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
            + NP4b α f z θ + NP5a α f z θ + NP5b α f z θ)
          + Function.uncurry (NP6 α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134ab5ab.add h6
  exact hall

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary pointwise tools -/

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a| * |b| ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  calc |a * b| = |a| * |b| := abs_mul a b
    _ ≤ (|a| ^ 2 + |b| ^ 2) / 2 := by linarith
    _ = (a ^ 2 + b ^ 2) / 2 := by rw [sq_abs a, sq_abs b]

/-- `a² ≤ (a·c)²` for `1 ≤ c`. -/
private lemma sq_le_sq_mul_of_one_le {a c : ℝ} (hc : 1 ≤ c) : a ^ 2 ≤ (a * c) ^ 2 := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  calc a ^ 2 = (|a| * 1) ^ 2 := by rw [mul_one, sq_abs]
    _ ≤ (|a| * c) ^ 2 := pow_le_pow_left₀ (mul_nonneg (abs_nonneg a) zero_le_one)
        (mul_le_mul_of_nonneg_left hc (abs_nonneg a)) 2
    _ = (a * c) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]

/-! ## Integrability of the angular slices -/

/-- The angular slice `θ ↦ f s θ` of a function `C^∞` on the open quadrant is a.e. strongly
measurable for `volume.restrict Iθ` and `s > 0`: its restriction to `(0,π/2)` is continuous,
and the two endpoints are null. -/
private theorem aesm_slice_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {s : ℝ} (hs : 0 < s) :
    AEStronglyMeasurable (fun θ : ℝ => f s θ) (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ : ℝ => f s θ)
      (volume.restrict (Set.Ioo 0 (π / 2))) :=
    (hsm.curry_θ hs).continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hcongr : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  rw [hcongr]
  exact h1

/-- For `s > 0` the square slice `θ ↦ (f s θ)²` of an `ℋ^k`-datum with interior smoothness is
integrable on `Iθ`.  Only the `i = 0` term of the `D_z`-part of `HkIntegrand` is used, and only
on the open interval (where `sin(2θ) > 0`); the two endpoints are null. -/
private theorem integrableOn_sq_slice {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ := by
  refine (hmem.1 s (le_of_lt hs)).mono' ((aesm_slice_of_smoothOpen hsm hs).pow 2) ?_
  -- replace `volume.restrict Iθ` by `volume.restrict (0,π/2)`, where `sin(2θ) > 0`
  have hcongr : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hs0.le (Real.sin_le_one _)
      (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w, le_div_iff₀ (pow_pos hs 2)]
    nlinarith
  have hA : 1 ≤ Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    (le_div_iff₀ hspos).mpr (by rw [one_mul]; exact le_trans hsle hw1)
  have h1 : (f s θ) ^ 2
      ≤ (f s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    sq_le_sq_mul_of_one_le hA
  have h2 : (Work.Spaces.DzIter 0 f s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f s θ :=
    Work.Spaces.sq_le_HkIntegrand_z α k f s θ 0 (Nat.zero_le k)
  simpa only [Work.Spaces.DzIter_zero] using le_trans h1 h2

/-- For `s > 0` the `K`-weighted slice `θ ↦ f s θ · K θ` is integrable on `Iθ`, from
`SmoothOpen f` and `HkMem α k f`: `K` is bounded on the compact `Iθ`, and the square slice is
integrable. -/
private theorem integrableOn_K_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun θ : ℝ => f s θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  have hsq := integrableOn_sq_slice hsm hmem hs
  have hKcont : Continuous Work.Spaces.K := by
    have h : Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by
      funext θ; rfl
    rw [h]
    exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)
  have hKsq : IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ) ^ 2) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hKcont.continuousOn.pow 2)
  have hmaj : Integrable (fun θ => ((f s θ) ^ 2 + (Work.Spaces.K θ) ^ 2) / 2)
      (volume.restrict Work.Spaces.Iθ) := (hsq.add hKsq).div_const 2
  refine hmaj.mono' ?_ ?_
  · exact (aesm_slice_of_smoothOpen hsm hs).mul (hKcont.aestronglyMeasurable.restrict)
  · filter_upwards with θ
    rw [Real.norm_eq_abs]
    exact abs_mul_le_half_sq (f s θ) (Work.Spaces.K θ)

/-- The `F_*`-slice `θ ↦ F_*(α) z θ · K θ` is integrable on `Iθ` for every `z` and `α > 0`:
it is continuous on the compact `Iθ`. -/
private theorem integrableOn_slice_Fstar_mul_K (α : ℝ) (hα : 0 < α) (s : ℝ) :
    IntegrableOn (fun θ => Work.Construction.Fstar α s θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have hGam : ContinuousOn (fun θ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.Gam
    intro θ _
    exact (Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))).comp_continuousWithinAt
      (by fun_prop)
  have hF : ContinuousOn (fun θ => Work.Construction.Fstar α s θ) Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact ((continuousOn_const.mul (hGam.div_const (Work.Spaces.c α))).mul continuousOn_const)
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  exact hF.mul hK

/-! ## The main theorem -/

theorem L3RhsFKadd : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.StrongPersist.H6Adm α f → ∀ z : ℝ, 0 < z →
    Work.Construction.FK (Work.Construction.Ftot α f) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK f z := by
  intro α hα f hadm z hz
  obtain ⟨hsm, hmem⟩ := hadm.reg
  have hFint : IntegrableOn
      (fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    integrableOn_slice_Fstar_mul_K α hα.1 z
  have hfint : IntegrableOn (fun θ => f z θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    integrableOn_K_mul_slice hsm hmem hz
  have key : (∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Fstar α z θ + f z θ) * Work.Spaces.K θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Construction.Fstar α z θ * Work.Spaces.K θ)
        + ∫ θ in Work.Spaces.Iθ, f z θ * Work.Spaces.K θ := by
    have hpt : (fun θ => (Work.Construction.Fstar α z θ + f z θ) * Work.Spaces.K θ)
        = fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ
            + f z θ * Work.Spaces.K θ := by
      funext θ; ring
    rw [hpt]
    exact MeasureTheory.integral_add hFint hfint
  simpa only [Work.Construction.FK, Work.Construction.Ftot] using key

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsL12add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false

theorem L3RhsL12add : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.StrongPersist.H6Adm α f → ∀ z : ℝ, 0 < z →
    Work.Construction.L12 (Work.Construction.Ftot α f) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z := by
  intro α hα f hf z hz
  obtain ⟨hα0, hα1⟩ := hα
  -- the honest fields of the class
  have hSO : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO 4 (by norm_num) hf.reg.2
  -- linearity of the integral operator on the four integrability certificates
  have hadd := (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := f)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα0 s)
    (fun s hs =>
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hSO hmem4
        (lt_of_lt_of_le hz hs.le))
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα0 hα1 z hz.le)
    ((Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hSO hmem4).mono_set
      (fun s hs => lt_of_lt_of_le hz hs.le))).1
  -- `Ftot α f` is definitionally `fun z θ => F_* z θ + f z θ`
  change Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z
  exact hadd

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.RadSupZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about the radial weight `w z = (1+z)²/z²` -/

private lemma w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

private lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (pow_pos hz 2)]
  nlinarith

/-- The pointwise square of an a.e. strongly measurable function is a.e. strongly
measurable (the `Pi`-power form of Mathlib's `AEStronglyMeasurable.pow` is not
definitionally the pointwise one, so this small rewriting step is recorded once). -/
private lemma aeSM_sq {f : ℝ → ℝ} {μ : Measure ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun t => (f t) ^ 2) μ :=
  (hf.pow 2).congr (Filter.Eventually.of_forall fun t => by simp [Pi.pow_apply])

/-- `t ↦ t * f t` is a.e. strongly measurable when `f` is. -/
private lemma aeSM_id_mul {f : ℝ → ℝ} {μ : Measure ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun t => t * f t) μ :=
  (aestronglyMeasurable_id.mul hf).congr
    (Filter.Eventually.of_forall fun t => by simp [Pi.mul_apply])

/-- `w` is antitone on `(0,∞)`; in the form needed here: `w t ≥ w (2c)` for `t ∈ [c,2c]`,
`c > 0`. -/
private lemma w_two_le_of_mem {c t : ℝ} (hc : 0 < c) (ht : t ∈ Set.Icc c (2 * c)) :
    Work.Spaces.w (2 * c) ≤ Work.Spaces.w t := by
  have h2c : 0 < 2 * c := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le hc ht.1
  have hle : (1 + 2 * c) / (2 * c) ≤ (1 + t) / t := by
    have h1 : (1 + 2 * c) / (2 * c) = 1 / (2 * c) + 1 := by
      rw [add_div, div_self (ne_of_gt h2c)]
    have h2 : (1 + t) / t = 1 / t + 1 := by rw [add_div, div_self (ne_of_gt ht0)]
    rw [h1, h2]
    have h3 : 1 / (2 * c) ≤ 1 / t := one_div_le_one_div_of_le ht0 ht.2
    linarith
  rw [Work.Spaces.w, Work.Spaces.w, ← div_pow, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) hle 2

/-! ## The main theorem -/

theorem RadSupZ : ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ),
    (∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ h z) →
    MeasureTheory.IntegrableOn (fun z : ℝ => (h z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) →
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.Dz (fun z _ => h z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) →
    ∀ z ∈ Set.Ioi (0 : ℝ), (h z) ^ 2 ≤ C *
      ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.Dz (fun z _ => h z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
  refine ⟨1, one_pos, ?_⟩
  intro h hdiff hA hB z hz
  have hz0 : (0 : ℝ) < z := hz
  -- the value of `D_z` on a `θ`-independent function
  have hDz : ∀ t : ℝ, Work.Spaces.Dz (fun z _ => h z) t 0 = t * deriv h t := by
    intro t
    simp [Work.Spaces.Dz, Work.Spaces.pz]
  -- the second hypothesis, in the `z * deriv h z` form
  have hB' : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    hB.congr_fun (fun t _ => by
      show Work.Spaces.Dz (fun z _ => h z) t 0 ^ 2 * (Work.Spaces.w t) ^ 2
        = (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2
      rw [hDz t]) measurableSet_Ioi
  -- the window `[c, 2c]` containing `z`
  set c : ℝ := z / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hc2c : c ≤ 2 * c := by linarith
  have h2c : 2 * c = z := by rw [hc_def]; ring
  have hzIcc : z ∈ Set.Icc c (2 * c) := by
    constructor <;> rw [hc_def] <;> linarith
  have hIcc_sub : Set.Icc c (2 * c) ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hc ht.1
  have hIoc_sub : Set.Ioc c (2 * c) ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hc ht.1.le
  -- `h` is continuous on the window
  have hdiffOn : DifferentiableOn ℝ h (Set.Ioi (0 : ℝ)) :=
    fun x hx => (hdiff x hx).differentiableWithinAt
  have hcont : ContinuousOn h (Set.Icc c (2 * c)) := hdiffOn.continuousOn.mono hIcc_sub
  -- ### Step 1: `(∂_z h)²` and `∂_z h` are integrable on the window
  -- `(z h')²` is integrable on `(0,∞)` since `w ≥ 1`
  have hB1 : MeasureTheory.IntegrableOn (fun t : ℝ => (t * deriv h t) ^ 2) (Set.Ioi 0) := by
    refine Integrable.mono' hB' ?_ ?_
    · exact aeSM_sq (aeSM_id_mul (aestronglyMeasurable_deriv h (volume.restrict (Set.Ioi (0 : ℝ)))))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 := by
        have hw := one_le_w ht
        nlinarith
      nlinarith [sq_nonneg (t * deriv h t)]
  -- hence `(h')²` is integrable on `[c,2c]`
  have hB2 : MeasureTheory.IntegrableOn (fun t : ℝ => (deriv h t) ^ 2) (Set.Icc c (2 * c)) := by
    have hc2 : 0 < c ^ 2 := pow_pos hc 2
    refine Integrable.mono' ((hB'.mono_set hIcc_sub).const_mul (1 / c ^ 2)) ?_ ?_
    · exact aeSM_sq (aestronglyMeasurable_deriv h (volume.restrict (Set.Icc c (2 * c))))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have ht0 : 0 < t := lt_of_lt_of_le hc ht.1
      have hct : c ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hc.le ht.1 2
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 := by
        have hw := one_le_w ht0
        nlinarith
      have h1 : (deriv h t) ^ 2 ≤ (t * deriv h t) ^ 2 / c ^ 2 := by
        rw [le_div_iff₀ hc2, show (t * deriv h t) ^ 2 = (deriv h t) ^ 2 * t ^ 2 by ring]
        exact mul_le_mul_of_nonneg_left hct (sq_nonneg _)
      have h2 : (t * deriv h t) ^ 2 / c ^ 2
          ≤ (1 / c ^ 2) * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
        rw [show (t * deriv h t) ^ 2 / c ^ 2 = (1 / c ^ 2) * (t * deriv h t) ^ 2 by ring]
        exact mul_le_mul_of_nonneg_left
          (by simpa using mul_le_mul_of_nonneg_left hw1 (sq_nonneg (t * deriv h t)))
          (by positivity)
      linarith
  -- `h'` itself is integrable on `[c,2c]` (Cauchy–Schwarz on a set of finite measure)
  have hderivInt : MeasureTheory.IntegrableOn (fun t : ℝ => deriv h t) (Set.Icc c (2 * c)) := by
    have hfin : IsFiniteMeasure (volume.restrict (Set.Icc c (2 * c))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    haveI := hfin
    have hmem : MemLp (fun t : ℝ => deriv h t) 2 (volume.restrict (Set.Icc c (2 * c))) := by
      rw [memLp_two_iff_integrable_sq
        (aestronglyMeasurable_deriv h (volume.restrict (Set.Icc c (2 * c))))]
      exact hB2
    exact hmem.integrable (by norm_num)
  -- ### Step 2: the fundamental theorem of calculus on the window
  have hFTC : ∀ x ∈ Set.Icc c (2 * c), ∀ y ∈ Set.Icc c (2 * c),
      h x - h y = ∫ t in y..x, deriv h t := by
    intro x hx y hy
    have hsub₁ : Set.Ioc y x ⊆ Set.Icc c (2 * c) :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hy.1 hx.2)
    have hsub₂ : Set.Ioc x y ⊆ Set.Icc c (2 * c) :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hx.1 hy.2)
    have hint : IntervalIntegrable (fun t : ℝ => deriv h t) volume y x :=
      ⟨hderivInt.mono_set hsub₁, hderivInt.mono_set hsub₂⟩
    have hsub_uIcc : Set.uIcc y x ⊆ Set.Icc c (2 * c) := by
      rcases le_total y x with hle | hle
      · rw [Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc hy.1 hx.2
      · rw [Set.uIcc_of_ge hle]; exact Set.Icc_subset_Icc hx.1 hy.2
    have hder : ∀ s ∈ Set.uIcc y x, HasDerivAt h (deriv h s) s := by
      intro s hs
      exact (hdiff s (lt_of_lt_of_le hc (hsub_uIcc hs).1)).hasDerivAt
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint).symm
  -- ### Step 3: the two interval integrability hypotheses of Agmon
  have hint1 : IntervalIntegrable (fun t : ℝ => (h t) ^ 2) volume c (2 * c) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc2c]
    refine Integrable.mono' (hA.mono_set hIcc_sub) ?_ ?_
    · exact aeSM_sq (hcont.aestronglyMeasurable measurableSet_Icc)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 := by
        have hw := one_le_w (lt_of_lt_of_le hc ht.1)
        nlinarith
      nlinarith [sq_nonneg (h t)]
  have hint2 : IntervalIntegrable (fun t : ℝ => (deriv h t) ^ 2) volume c (2 * c) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc2c]
    exact hB2
  -- ### Step 4: the local Agmon inequality on the window
  have hZg := Work.FTS.H2.CruxPair.ZAgmon h hc hcont hFTC hint1 hint2 z hzIcc
  -- ### Step 5: dominating the window integrals by the weighted global data
  have hb1 : ∫ t in Set.Ioc c (2 * c), (h t) ^ 2
      ≤ (1 / (Work.Spaces.w (2 * c)) ^ 2) *
          ∫ t in Set.Ioi (0 : ℝ), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
    have hm0 : 0 < (Work.Spaces.w (2 * c)) ^ 2 := pow_pos (w_pos (by linarith)) 2
    have hpt : ∀ t ∈ Set.Ioc c (2 * c), (h t) ^ 2
        ≤ (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
      intro t ht
      have hwt : Work.Spaces.w (2 * c) ≤ Work.Spaces.w t :=
        w_two_le_of_mem hc ⟨ht.1.le, ht.2⟩
      have h2 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 / (Work.Spaces.w (2 * c)) ^ 2 := by
        rw [one_le_div hm0]
        exact pow_le_pow_left₀ (le_of_lt (w_pos (by linarith))) hwt 2
      calc (h t) ^ 2 = (h t) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (h t) ^ 2 * ((Work.Spaces.w t) ^ 2 / (Work.Spaces.w (2 * c)) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by ring
    have hIntR : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2))
        (Set.Ioc c (2 * c)) :=
      (hA.mono_set hIoc_sub).const_mul _
    have hmono : ∫ t in Set.Ioc c (2 * c), (h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) :=
      integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hIntR
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hpt))
    have hstep : ∫ t in Set.Ioc c (2 * c),
          (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2)
        = (1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      MeasureTheory.integral_const_mul _ _
    have hdom : ∫ t in Set.Ioc c (2 * c), (h t) ^ 2 * (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi (0 : ℝ), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      setIntegral_mono_set hA (ae_of_all _ fun t => by positivity) hIoc_sub.eventuallySubset
    calc ∫ t in Set.Ioc c (2 * c), (h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) := hmono
      _ = (1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 := hstep
      _ ≤ (1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioi (0 : ℝ), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hdom (by positivity)
  have hb2 : ∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2
      ≤ (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
          ∫ t in Set.Ioi (0 : ℝ), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
    have hm0 : 0 < (c * Work.Spaces.w (2 * c)) ^ 2 := by
      have := w_pos (show (0 : ℝ) < 2 * c by linarith)
      positivity
    have hpt : ∀ t ∈ Set.Ioc c (2 * c), (deriv h t) ^ 2
        ≤ (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hc ht.1.le
      have hwt : Work.Spaces.w (2 * c) ≤ Work.Spaces.w t :=
        w_two_le_of_mem hc ⟨ht.1.le, ht.2⟩
      have hct : c ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hc.le ht.1.le 2
      have hwt2 : (Work.Spaces.w (2 * c)) ^ 2 ≤ (Work.Spaces.w t) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt (w_pos (by linarith))) hwt 2
      have hkey : (deriv h t) ^ 2 * (c * Work.Spaces.w (2 * c)) ^ 2
          ≤ (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
        have hdh : (0 : ℝ) ≤ (deriv h t) ^ 2 := sq_nonneg _
        have htw : (0 : ℝ) ≤ (Work.Spaces.w (2 * c)) ^ 2 := sq_nonneg _
        have hcur : (deriv h t) ^ 2 * c ^ 2 * (Work.Spaces.w (2 * c)) ^ 2
            ≤ (deriv h t) ^ 2 * t ^ 2 * (Work.Spaces.w (2 * c)) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hct hdh) htw
        have hcur2 : (deriv h t) ^ 2 * t ^ 2 * (Work.Spaces.w (2 * c)) ^ 2
            ≤ (deriv h t) ^ 2 * t ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hwt2 (by positivity)
        have e1 : (deriv h t) ^ 2 * (c * Work.Spaces.w (2 * c)) ^ 2
            = (deriv h t) ^ 2 * c ^ 2 * (Work.Spaces.w (2 * c)) ^ 2 := by ring
        have e2 : (t * deriv h t) ^ 2 = (deriv h t) ^ 2 * t ^ 2 := by ring
        rw [e1, e2]
        linarith
      rw [show (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
            * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2)
          = ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2)
            / (c * Work.Spaces.w (2 * c)) ^ 2 by ring,
        le_div_iff₀ hm0]
      exact hkey
    have hIntR : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
          * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2))
        (Set.Ioc c (2 * c)) :=
      (hB'.mono_set hIoc_sub).const_mul _
    have hmono : ∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
              * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) :=
      integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hIntR
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hpt))
    have hstep : ∫ t in Set.Ioc c (2 * c),
          (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
            * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2)
        = (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      MeasureTheory.integral_const_mul _ _
    have hdom : ∫ t in Set.Ioc c (2 * c), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi (0 : ℝ), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      setIntegral_mono_set hB' (ae_of_all _ fun t => by positivity) hIoc_sub.eventuallySubset
    calc ∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
              * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) := hmono
      _ = (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 := hstep
      _ ≤ (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioi (0 : ℝ), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hdom (by positivity)
  -- ### Step 6: the coefficient is at most `1`
  have hcoef : 2 / (c * (Work.Spaces.w (2 * c)) ^ 2) ≤ 1 := by
    have hcm0 : 0 < c * (Work.Spaces.w (2 * c)) ^ 2 := by
      have := w_pos (show (0 : ℝ) < 2 * c by linarith)
      positivity
    rw [div_le_one hcm0]
    -- it remains to see `2 ≤ c · w(2c)²`
    have hmain : 4 ≤ z * (Work.Spaces.w z) ^ 2 := by
      have hwz : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [Work.Spaces.w, div_pow]
        ring_nf
      have hz0ne : z ≠ 0 := ne_of_gt hz0
      have hz4 : (0 : ℝ) < z ^ 4 := by positivity
      have hzsplit : z * ((1 + z) ^ 4 / z ^ 4) = (1 + z) ^ 4 / z ^ 3 := by
        field_simp
      rw [hwz, hzsplit]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 3)]
      have hexp : (1 + z) ^ 4 = 1 + 4 * z + 6 * z ^ 2 + 4 * z ^ 3 + z ^ 4 := by ring
      have hnn : (0 : ℝ) ≤ 1 + 4 * z + 6 * z ^ 2 + z ^ 4 := by positivity
      nlinarith [hexp, hnn]
    have hceq : c * (Work.Spaces.w (2 * c)) ^ 2 = (z * (Work.Spaces.w z) ^ 2) / 2 := by
      rw [hc_def, h2c]
      ring
    rw [hceq]
    linarith
  -- ### Step 7: assembly
  have hAB : 0 ≤ (∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    have h1 : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      integral_nonneg_of_ae (ae_of_all _ fun t => by positivity)
    have h2 : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      integral_nonneg_of_ae (ae_of_all _ fun t => by positivity)
    linarith
  have hfinal : (h z) ^ 2 ≤ 1 *
      ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    simp only [intervalIntegral.integral_of_le hc2c] at hZg
    have hstep1 := mul_le_mul_of_nonneg_left hb1 (show (0 : ℝ) ≤ 2 / c by positivity)
    have hstep2 := mul_le_mul_of_nonneg_left hb2 (show (0 : ℝ) ≤ 2 * c by positivity)
    have harith :
        (2 / c) * ((1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (2 * c) * ((1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)
        = (2 / (c * (Work.Spaces.w (2 * c)) ^ 2)) *
          ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
      have hcne : c ≠ 0 := ne_of_gt hc
      have hmne : (Work.Spaces.w (2 * c)) ^ 2 ≠ 0 :=
        ne_of_gt (pow_pos (w_pos (show (0 : ℝ) < 2 * c by linarith)) 2)
      field_simp
    calc (h z) ^ 2
        ≤ (2 / c) * (∫ t in Set.Ioc c (2 * c), (h t) ^ 2)
            + (2 * c) * (∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2) := hZg
      _ ≤ (2 / c) * ((1 / (Work.Spaces.w (2 * c)) ^ 2) *
              ∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + (2 * c) * ((1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
              ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          add_le_add hstep1 hstep2
      _ = (2 / (c * (Work.Spaces.w (2 * c)) ^ 2)) *
            ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) := harith
      _ ≤ 1 * ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcoef hAB
  -- rewrite the `D_z` occurrence of the statement into `z * deriv h z`
  have hBeq : (∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.Dz (fun z _ => h z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    show Work.Spaces.Dz (fun z _ => h z) t 0 ^ 2 * (Work.Spaces.w t) ^ 2
      = (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2
    rw [hDz t]
  rw [hBeq]
  exact hfinal

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongPersist


end Work.FTS.StrongPersist
end
