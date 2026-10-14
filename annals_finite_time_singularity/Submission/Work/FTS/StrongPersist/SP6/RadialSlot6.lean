import Mathlib
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.n4norm_exists
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2_pkg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The package `(ℋ^n, BlocksCont n, BlocksAdd n)` for the `D_z`-defect `E₂ α f`

`E₂ α f = Ê₂ f + Γ(θ)·radS α f z` (`E2_eq`) is a sum of two functions with *different*
regularity:

* `Ê₂ f` is `C^∞` on the open quadrant (`AuxE2.E2hat_contDiffOn_three`), and its `ℋ^n`-membership
  descends from `RegQ α (n+1) f` (`Assembly.E2hat_RegQ`);
* `Γ(θ)·radS α f z` is only `C³` there (`E2pkg.radS_contDiffOn_three`) but *separates* into an
  angular and a radial factor, so its `ℋ^n`-membership for `n ≤ 3` is
  `E2pkg.HkMem_gam_rad`.

The block continuity `BlocksCont n (E₂ α f)` is the sibling `E2_blocks`; the block additivity
`BlocksAdd n (𝓛̂(D_z f)) (E₂ α f)` follows from the `C^n`-regularity of both functions on the
open quadrant (`E2pkg.blocksAdd_of_contDiffOn`). -/




end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeCrux.AeSliceHonV =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst.AeCrux

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-
The a.e. `σ`-slice honesty of the mixed slot `V = z ∂_z∂_θu = ∂_θ(z ∂_zu)` for a datum of the
a.e. class `AeData α u G` (plus the radial honesty, itself derivable from `AeData` by
`Dispatch.hkMem_gradUD`).  This is the *first conjunct* of `Cores/AeStep2Aux/aeMixedAe_mem` and one
of the two hypotheses of `remov/AeI1PaperOfHonest`, hence a shared bottleneck of the two remaining
`Ae` leaves of `propHkWeakFts`.

## The proof in this file (the "flat heavy" route)

The target is *proved* by the body of `AeSliceHonV` below.  The route is the tree's
two-dimensional (frequency + angular Agmon) interpolation: `Work.FTS.EllSol.HeavyFlat.FlatHeavy`
(from `Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness`) gives the flat statement — for `u` of
class `C²` on the strip with vanishing end-point *values* whose three `σ_η`-weighted shifted
diagonal slots are integrable, the mixed slot `(∂_θ(∂_t-b)u)² σ_η` has finite `∫⁻` — proved per
frequency by the angular Agmon inequality (`Trunc.curlAgmon`), Plancherel in `t`
(`Shift2Flat.niceRangePlanch`) and Cauchy–Schwarz in the frequency, the general datum being
reached by exact ODE truncation and Fatou.  `HeavyFlat.omOfFlat` transfers it to the logarithmic
weight `Ω(t) = w(e^t)²·e^t`, and the pull-back `z = e^t` (`AeCrux/AeVGlobalFin2.lean`,
`AeCrux/AeVLib/*`) identifies the three `σ_η`-slots of `t ↦ u(e^t,·)` with the `HkMem α 0`-slots
of `D_zu`, `z²∂_zzu`, `∂_θ²u`, i.e. with `hU`, `h.memRad2`, `h.memAng2`.  Finally Tonelli
(`lintegral_prod`) plus `lintegral_box_exp_rev` give the finiteness of the `θ`-`∫⁻` of the
level-`0` `HkIntegrand` of the mixed slot for a.e. `z > 0`, and since
`HkIntegrand α 0 (D_z(pth u)) z θ = w(z)²·((z ∂_z∂_θu)²·σ_η(θ))` with `w z ≠ 0` for `z > 0`,
`lintegral_ofReal_ne_top_iff_integrable` converts this into the stated `IntegrableOn`.

No per-`z` argument is possible (the slicewise version is FALSE,
`AngAWeak/NOTES_aeMixedHon_FALSE.md`).  The three *proved* reductions below state the same
content against the tree's older interfaces; see
`NOTES_AeSliceHonV_analysis.md` / `NOTES_AeSliceHonV_session2.md`.
-/




/-- The requested statement: the angular slice `θ ↦ (z ∂_z∂_θu)^2 σ θ` of the mixed slot is
integrable for almost every `z > 0`.  Proved by the flat heavy route of the module docstring. -/
theorem AeSliceHonV {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G := h
  have hSm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth
  have hU' : Work.Spaces.HkMem α 0 (Work.Spaces.Dz u) := hU
  have hthEta : ∀ θ ∈ Iθ, 0 ≤ Work.FTS.EllipticEst.thEta θ :=
    fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ
  -- ## slot 1 (f = Dz u)
  have hF1nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF1cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := hSm.Dz.continuousOn_HkIntegrand α 0
  have hg1 : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp p.1 * Work.Spaces.pz u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_exp.comp continuous_fst).continuousOn
        (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))).mul
      (contOn_expComp hSm.pz.continuousOn)
  have hidg1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Real.exp t * Work.Spaces.pz u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz hSm hθ]
  have hid1 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz u (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz u (Real.exp t) θ from rfl]
    ring
  have hslot1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF1nn (Phi_nonneg hidg1) hid1 hF1cont (continuousOn_Phi hg1 hidg1) hU'.1 hU'.2
  -- ## slot 3 (f = pthIter 2 u)
  have hF3nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hF3cont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hSm.pth.pth).continuousOn_HkIntegrand α 0
  have hg3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pthIter 2 u (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.pth.pth).continuousOn
  have hidg3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.pthIter 2 u (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pthIter]
  have hid3 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pthIter, HkIntegrand_zero_eq α (Work.Spaces.pthIter 2 u) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul]
    ring
  have hslot3 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pthIter 2 (pb u) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      (Φ := fun t θ => (Work.Spaces.pthIter 2 (pb u) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
        * Work.FTS.EllipticEst.sEta θ)
      hF3nn (Phi_nonneg hidg3) hid3 hF3cont (continuousOn_Phi hg3 hidg3)
      hAe.memAng2.1 hAe.memAng2.2
  -- ## slot 2 (f = Dz (Dz u))
  have hF2nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ := by
    intro z θ; rw [HkIntegrand_zero]; exact sq_nonneg _
  have hdom2 : ∀ z θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 < z →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ := by
    intro z θ hθ hz
    rw [HkIntegrand_zero, HkIntegrand_zero, HkIntegrand_zero]
    rw [show Work.Spaces.Dz (Work.Spaces.Dz u) z θ
        = Work.Spaces.Dz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ from pb_DzDz hSm hz hθ]
    nlinarith [sq_nonneg (Work.Spaces.Dz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      - z ^ 2 * Work.Spaces.pzIter 2 u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
  have hslices2 : ∀ z ∈ Work.Spaces.Iz, Integrable (fun θ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (MeasureTheory.volume.restrict Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · rw [← h0]
      simp only [Work.Spaces.HkIntegrand_zero_z, Pi.zero_apply]
      exact MeasureTheory.integrable_zero ℝ ℝ _
    · refine MeasureTheory.Integrable.mono'
        (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
        (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
          + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ?_ ?_ ?_
      · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0) hpos
      · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
        rw [Real.norm_of_nonneg (hF2nn z θ)]
        exact hdom2 z θ hθIoo hpos
  have houter2 : Integrable (fun z => ∫ θ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hg : Integrable (fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine ((hU'.2.const_mul 2).add (hAe.memRad2.2.const_mul 2)).congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      show 2 * (∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          + 2 * (∫ θ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
            ∂(MeasureTheory.volume.restrict Iθ))
          = ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
              + 2 * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
            ∂(MeasureTheory.volume.restrict Iθ)
      rw [MeasureTheory.integral_add ((hU'.1 z hz).const_mul 2)
          ((hAe.memRad2.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    refine MeasureTheory.Integrable.mono'
      (f := fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ
        ∂(MeasureTheory.volume.restrict Iθ))
      (g := fun z => ∫ θ, (2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) ?_ ?_ ?_
    · exact hg
    · exact (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)).integral_prod_right'
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
      · rw [← h0]
        simp only [Work.Spaces.HkIntegrand_zero_z]
        simp
      · rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg_of_ae ?_)]
        swap
        · filter_upwards with θ
          exact hF2nn z θ
        refine MeasureTheory.integral_mono_of_nonneg
          (μ := MeasureTheory.volume.restrict Iθ)
          (f := fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
          (g := fun θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ) ?_ ?_ ?_
        · filter_upwards with θ; exact hF2nn z θ
        · exact (hU'.1 z hz).const_mul 2 |>.add ((hAe.memRad2.1 z hz).const_mul 2)
        · filter_upwards [ae_Iθ_Ioo] with θ hθIoo
          exact hdom2 z θ hθIoo hpos
  have hg2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp (hSm.Dz.Dz).continuousOn
  have hidg2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = (Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ) ^ 2
          * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ := by
    intro t θ hθ; rw [pb_pz2 hSm hθ]
  have hid2 : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pz2 hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.Dz u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.Dz u) (Real.exp t) θ from rfl]
    ring
  have hslot2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.pz (pb u)) p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
        * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    slot_integrableOn
      (F := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.Dz u)) z θ)
      (Φ := fun t θ => (Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ) ^ 2
        * Work.FTS.EllSol.HeavyFlat.omw t * Work.FTS.EllipticEst.sEta θ)
      hF2nn (Phi_nonneg hidg2) hid2 ((hSm.Dz.Dz).continuousOn_HkIntegrand α 0)
      (continuousOn_Phi hg2 hidg2) hslices2 houter2
  -- ## the interface
  have hOm : Work.FTS.EllSol.HeavyFlat.OmHeavy :=
    Work.FTS.EllSol.HeavyFlat.omOfFlat Work.FTS.EllSol.HeavyFlat.flatHeavy
  -- ## the interface
  have hconcl := hOm (pb u) (pb_contDiff hAe.smooth 2)
    (fun t => hAe.dirZero (Real.exp t)) (fun t => hAe.dirPi (Real.exp t))
    hslot1 hslot2 hslot3
  -- ## the reverse transfer
  have hGcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    contOn_expComp ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
  have hidM : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw t
          * Work.FTS.EllipticEst.sEta θ
        = Real.exp t * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp t) θ := by
    intro t θ hθ
    have hIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [pb_pth_pz hSm hθ, HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hIθ,
      Work.FTS.EllSol.HeavyFlat.omw_eq_w_sq_mul,
      show Work.Spaces.Dz (Work.Spaces.pth u) (Real.exp t) θ
        = Real.exp t * Work.Spaces.pz (Work.Spaces.pth u) (Real.exp t) θ from rfl]
    ring
  have hGF : (fun q : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (pb u)) q.1 q.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw q.1
          * Work.FTS.EllipticEst.sEta q.2))
      =ᵐ[MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)]
      (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
            (Real.exp q.1) q.2)) := by
    filter_upwards [ae_strip_of hidM] with q hq
    rw [hq, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hAEz : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2))
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (MeasureTheory.volume.restrict Iθ)) := by
    have h := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)
      ((hSm.pth.Dz).continuousOn_HkIntegrand α 0)
    rw [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm] at h
    exact (ENNReal.measurable_ofReal.comp_aemeasurable h.aemeasurable)
  have hAEt : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u))
          (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((Real.measurable_exp.comp measurable_fst).aemeasurable)).mul ?_
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((aesm_prod_univ_Iθ (f := fun t θ => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp t) θ) hGcont).aemeasurable)
  have hAEt' : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1
      * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) (Real.exp q.1) q.2))
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (MeasureTheory.volume.restrict Iθ)) := by
    refine hAEt.congr ?_
    filter_upwards with q
    rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos q.1))]
  have hfinT := lintegral_box_exp_rev (F := fun z θ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ))
    hAEz hAEt hGF hconcl
  -- ## Tonelli: the box `∫⁻` of the mixed slot is the iterated one
  have hfinIter : (∫⁻ z, (∫⁻ θ, (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)) (z, θ)
      ∂(MeasureTheory.volume.restrict Iθ))
      ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) < ⊤ := by
    rw [← MeasureTheory.lintegral_prod
      (f := fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) p.1 p.2)) hAEz]
    exact hfinT
  have hmeasZ : AEMeasurable (fun z : ℝ => ∫⁻ θ, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
      ∂(MeasureTheory.volume.restrict Iθ))
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
    have h := AEMeasurable.lintegral_prod_right
      (μ := (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
      (ν := MeasureTheory.volume.restrict Iθ)
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)) hAEz
    exact h
  have haeFin : ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
        ∂(MeasureTheory.volume.restrict Iθ)) < ⊤ :=
    MeasureTheory.ae_lt_top' hmeasZ (ne_of_lt hfinIter)
  -- ## the a.e. slice
  filter_upwards [haeFin, self_mem_ae_restrict measurableSet_Ioi] with z hzfin hzpos
  have hz : (0 : ℝ) < z := hzpos
  -- the level-0 integrand is `w z ^ 2` times the target integrand on `Iθ`
  have hkey : ∀ θ ∈ Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
      (Work.Spaces.Dz (Work.Spaces.pth u)) z θ)
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    rw [HkIntegrand_zero_eq α (Work.Spaces.Dz (Work.Spaces.pth u)) hθ]
    rw [show Work.FTS.EllipticEst.sEta θ
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
    rw [show Work.Spaces.Dz (Work.Spaces.pth u) z θ
        = z * Work.Spaces.pz (Work.Spaces.pth u) z θ from rfl]
    rw [show (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (Work.Spaces.w z) ^ 2 * ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) from by ring]
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
  have hAeq : (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ) ∂(MeasureTheory.volume.restrict Iθ))
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ, ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            ∂(MeasureTheory.volume.restrict Iθ)) := by
    have hcongr : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.Spaces.Dz (Work.Spaces.pth u)) z θ))
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hkey θ hθ
    rw [MeasureTheory.lintegral_congr_ae hcongr,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hwne : ENNReal.ofReal ((Work.Spaces.w z) ^ 2) ≠ 0 := by
    have hwpos : 0 < (Work.Spaces.w z) ^ 2 := by
      rw [Work.Spaces.w]
      exact pow_pos (div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)) 2
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hwpos)
  have hBfin : (∫⁻ θ, ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ∂(MeasureTheory.volume.restrict Iθ)) < ⊤ := by
    have h1 : ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ, ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            ∂(MeasureTheory.volume.restrict Iθ)) < ⊤ := by
      rw [← hAeq]
      exact hzfin
    rcases ENNReal.mul_lt_top_iff.mp h1 with h2 | h0 | h0'
    · exact h2.2
    · exact absurd h0 hwne
    · rw [h0']; exact ENNReal.zero_lt_top
  have hBfin' : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) < ⊤ := by
    refine lt_of_le_of_lt ?_ hBfin
    exact MeasureTheory.lintegral_mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- ## the Bochner statement
  have hcontθ : ContinuousOn (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hzsl : ContinuousOn (fun θ : ℝ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      continuousOn_const.mul ((hSm.pth.pz.curry_θ hz).continuousOn)
    have hsigcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have hsincont : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_id)
      exact hsincont.continuousOn.rpow_const (p := -(Work.Spaces.eta))
        (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))
    exact (hzsl.pow 2).mul hsigcont
  have haesm : AEStronglyMeasurable (fun θ : ℝ =>
      (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontθ.aestronglyMeasurable measurableSet_Ioo
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      (0 : ℝ) ≤ (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _))
  rw [MeasureTheory.IntegrableOn]
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm hnn).mp (ne_of_lt hBfin')


end Work.FTS.EllipticEst.AeCrux
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.smoothOpen_FK_of_gal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.PvecMeasOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin Work.Construction Work.Spaces
open Work.FTS.Nonlinear.Pieces.rl1Tools (aesm_congr aesm_mul aesm_const_mul aesm_neg
  aesm_s2_mul aesm_sinsq_mul aesm_FK aesm_Uop_of_div aesm_of_contOn_Qd aesm_g_ops aesm_F_ops
  aesm_FK_ops QdMeas pv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The bridge `SmoothOpen ⟹` a.e. strong measurability -/

/-- A function which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` is a.e. strongly
measurable for the product measure `volume ↾ (0,∞) ⊗ volume ↾ Iθ` (the two sets differ by the
null angular boundary lines). -/
theorem aesm_of_smoothOpen {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas :=
  aesm_of_contOn_Qd h.continuousOn

/-! ## `SmoothOpen` is preserved by `𝒰` and `𝒱`

`ℛ` is handled by `Work.FTS.NonlinRows.smoothOpen_Rop` (delivered in
`NonlinRows/smoothOpen_radA.lean`); the other two operators are closed under `SmoothOpen` for
purely algebraic reasons, proved here so that no extra module is needed:

* `𝒰(Ψ) = -3Ψ - α D_zΨ` (with `D_z = z∂_z`) is a linear combination of `Ψ` and `D_zΨ`;
* `𝒱(Ψ) = ∂_θΨ - tan θ · Ψ`, and `tan` is `C^∞` on the open quadrant. -/

theorem smoothOpen_Uop_open {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α Ψ) := by
  rw [show Work.Construction.Uop α Ψ
      = fun z θ => -3 * Ψ z θ - α * Work.Spaces.Dz Ψ z θ from by
    funext z θ; simp only [Work.Construction.Uop, Work.Spaces.Dz]; ring]
  exact Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-3) hΨ)
    (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl α hΨ.Dz)

theorem smoothOpen_Vop_open {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have hprod : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨ
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (f := fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ)
    (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hΨ.pth hprod) ?_
  intro z θ _ _ _
  rfl

/-! ## The three `g`-side coefficients of `EllPkgGo`

`EllPkgGo.R`/`.U`/`.V` are `HQo α 4`, i.e. `SmoothOpen` plus `HkMem`, so the a.e. strong
measurability of `ℛ(Φ̃_g)`, `𝒰(Φ̃_g)`, `𝒱(Φ̃_g)` is immediate (for `𝒰` one first undoes the
division by `sin 2θ` with `aesm_Uop_of_div`). -/

theorem aesm_Tg_ops_open {α Ce : ℝ} {g Φg : Fn}
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) QdMeas :=
  ⟨aesm_of_smoothOpen hell.R.1.1,
    aesm_Uop_of_div (aesm_of_smoothOpen hell.U.1.1),
    aesm_of_smoothOpen hell.V.1.1⟩

/-! ## The three star-side coefficients of `StarPkgo`

Here the package only gives `SmoothOpen Φ_*`, so the coefficients are obtained by first
forming `Φ̃_* = Φ_* - Θ_*(α)` (`smoothOpen_PhiTs`, which uses `0 < α ≤ 1` for the explicit
profile identity `L₁₂(F_*) = 2α/(1+z)`) and then applying the three operators. -/

theorem aesm_star_ops_open {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) QdMeas := by
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs
  exact ⟨aesm_of_smoothOpen (Work.FTS.NonlinRows.smoothOpen_Rop hPhi),
    aesm_of_smoothOpen (smoothOpen_Uop_open hPhi),
    aesm_of_smoothOpen (smoothOpen_Vop_open hPhi)⟩

/-! ## The target statement -/

theorem PvecMeasOpen {α Ce Cs : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.VocabO.StarPkgo α Cs Φs)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    (∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20, AEMeasurable
        (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    (∀ k : Fin 20, AEMeasurable
        (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  obtain ⟨hg, hpthg, hDzg, hDthg⟩ := aesm_g_ops hgal
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := aesm_Tg_ops_open hell
  obtain ⟨hFKg, hFKF⟩ := aesm_FK_ops hgal
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ := aesm_star_ops_open hα hα1 hs
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Φg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Φg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Φg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK g z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKg hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK g z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKg hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hg))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  -- the `ENNReal`-valued versions, with the angular weight `K`
  have hENN : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlinear.Pieces.rl1Tools.pv
        α g Φs Φg k r θ|)) QdMeas := by
    intro k
    have hKcont : Continuous fun p : ℝ × ℝ => Work.Spaces.K p.2 := by
      simp only [Work.Spaces.K]; fun_prop
    have hK : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) QdMeas :=
      hKcont.aestronglyMeasurable
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.K p.2, Function.uncurry (fun r θ =>
          Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ) p)) QdMeas :=
      hK.prodMk (hpiece k)
    have hcomp : Continuous (fun q : ℝ × ℝ => ENNReal.ofReal |q.1 * q.2|) :=
      ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_fst.mul continuous_snd))
    exact hcomp.comp_aestronglyMeasurable hpair
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_all.2 fun k => (hENN k).prodMk_left] with r hr
    intro k
    exact (hr k).aemeasurable
  · intro k
    exact (hENN k).aemeasurable.lintegral_prod_right

end

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.starUopBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

open scoped Real Topology
open Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-
Port of `Work.FTS.Nonlinear.Pieces.Rl1.StarUBound` (already proved, constant `4`) from the
frozen `StarPkg` to the open-quadrant `StarPkgo`.  The only genuinely new ingredient is the
θ-slice smoothness of `θ ↦ Uop α (PhiTs α Φs) z θ` on `(0, π/2)` from `SmoothOpen Φs`
(the frozen proof uses `smoothQuad_PhiTs`/`smoothQuad_Uop`/`contDiffOn_thSlice_Uop`, which need
`SmoothQuad`); the rest is verbatim: the anchor `Uop_pi_div_four` at `π/4` plus
`star_Rop_le`/`star_Vop_le` (in `Rl1/tools.lean`) give `|Uop z (π/4)| ≤ 2 max Cs 0 α`, and the
interior mean-value lemma `Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound`
with the derivative bound `|pth (Uop …)| ≤ max Cs 0 α` (from `hs.dU` via
`Work.FTS.OpenPkg.WDMem_of_WDp_le`) gives `|Uop z θ - Uop z (π/4)| ≤ (π/4) max Cs 0 α`.
The endpoints `θ = 0, π/2` follow from `hs.vanishU`.  `C = 4` works.
-/

/-! ## The new ingredient: `θ`-slice smoothness in the open-quadrant class

`SmoothOpen Φ_*` (from `StarPkgo.smooth`) makes `Φ̃_* = PhiTs α Φs` and then `U(Φ̃_*)` `C^∞`
on the open quadrant (`smoothOpen_PhiTs`, `smoothOpen_Uop`), so the angular slice at any
`z > 0` is `C^n` on `(0, π/2)` for every finite `n` (`SmoothOpen.curry_θ`).  This replaces the
frozen `contDiffOn_thSlice_Uop`, which went through `SmoothQuad`. -/
theorem contDiffOn_thSlice_Uop_open {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    ∀ z : ℝ, 0 < z → ∀ n : ℕ, ContDiffOn ℝ n
      (fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro z hz n
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs
  have hU : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.EllipticEst.smoothOpen_Uop hPhi
  exact (hU.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])

theorem starUopBound : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.VocabO.StarPkgo α Cs Φs →
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ C * max Cs 0 * α := by
  refine ⟨4, by norm_num, ?_⟩
  intro α Cs Φs hα hα1 hs z hz θ hθ
  have hMnn : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hMα : 0 ≤ max Cs 0 * α := mul_nonneg hMnn hα.le
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hpi4Ioo : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hpi4Iθ : (Real.pi / 4) ∈ Work.Spaces.Iθ :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  -- the three pointwise bounds of `StarPkgo`, on the open angular interval
  have hR : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z ξ| ≤ max Cs 0 * α :=
    fun ξ hξ => star_Rop_le hα hs z hz ξ hξ
  have hV : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z ξ| ≤ max Cs 0 * α :=
    fun ξ hξ => star_Vop_le hα hs z hz ξ hξ
  have hdU : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z ξ|
        ≤ max Cs 0 * α := by
    intro ξ hξ
    have h1 := Work.FTS.OpenPkg.WDMem_of_WDp_le hs.dU.1 hs.dU.2 0 0 (by norm_num)
      z ξ hz hξ.1 hξ.2
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hvU : Work.Spaces.VanishTheta
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := hs.vanishU
  -- ### (i) the anchor at `θ = π/4`
  have hanchor : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
      ≤ 2 * (max Cs 0 * α) := by
    rw [Work.FTS.Nonlinear.Pieces.Rl1.Uop_pi_div_four α (Work.FTS.Nonlin.PhiTs α Φs) z,
      abs_neg]
    have h1 := hR (Real.pi / 4) hpi4Ioo
    have h2 := hV (Real.pi / 4) hpi4Ioo
    have htri : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)
        - Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
        ≤ |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
          + |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)| := by
      have h := abs_add_le
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4))
        (-(Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)))
      rw [abs_neg] at h
      simpa only [sub_eq_add_neg] using h
    linarith
  -- ### the two boundary values
  rcases eq_or_ne θ 0 with hθ0 | hθ0
  · subst hθ0
    rw [hvU.1 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  rcases eq_or_ne θ (Real.pi / 2) with hθ2 | hθ2
  · subst hθ2
    rw [hvU.2 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  -- ### (ii) the interior mean-value step
  have hθint : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ2⟩
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n
      (fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_thSlice_Uop_open hα hα1 hs z hz
  have hK : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ') ξ|
        ≤ max Cs 0 * α := by
    intro ξ hξ
    have h := hdU ξ hξ
    simpa only [Work.Spaces.pth] using h
  have hmvt := Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
    (u := fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
    hslice hθint hpi4Ioo hK
  have hdist : |θ - Real.pi / 4| ≤ Real.pi / 4 := by
    rw [abs_le]
    exact ⟨by linarith [hθint.1], by linarith [hθint.2]⟩
  have hb1 : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      - Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
      ≤ (max Cs 0 * α) * (Real.pi / 4) :=
    le_trans hmvt (mul_le_mul_of_nonneg_left hdist hMα)
  have htri : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
      ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          - Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
        + |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)| := by
    have h := abs_add_le
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        - Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4))
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4))
    rwa [sub_add_cancel] at h
  have hpi : (Real.pi / 4 : ℝ) ≤ 2 := by linarith [Real.pi_lt_four]
  have hstep : (max Cs 0 * α) * (Real.pi / 4) ≤ (max Cs 0 * α) * 2 :=
    mul_le_mul_of_nonneg_left hpi hMα
  linarith [hb1, hanchor, htri, hstep]

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.dthIter_four_Rop_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 19: the order-4 angular bound for `ℛ(Φ̃_*)`

For a frozen `StarPkg α Cs Φs`, the `𝒲^{4,∞}`-field `StarPkg.R` controls the function

  `ℛ := (z+1)/z · Rop α (Φ̃_*)`   (`Φ̃_* = PhiTs α Φs`),

because `(z+1)/z` is a `z`-only factor.  Its `(k = 0, j = 4)`-slot therefore gives

  `|D_θ^4 ℛ z θ| · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ |ℛ|_{𝒲^{4,∞}} ≤ Cs · α`

for `z ∈ Iz`, `θ ∈ Iθ`; multiplying by `(z+1)/z` is an invertible operation and yields the
bound of `dthIter_four_Rop_le` (`z/(1+z)` on the right).  All the work is in
`Work.Spaces.pz_Dth_sup_bound`, which also disposes of the angular endpoints `θ = 0, π/2`
(there `sin(2θ) = 0`, so `D_θ^4` vanishes identically and both sides are `0`).
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row19.helpers

/-- **The `(k = 0, j = 4)`-slot bound for `ℛ(Φ̃_*)`.**  `D_θ^4 Rop α (PhiTs α Φs)` inherits
its bound from the frozen `𝒲^{4,∞}`-field of `(z+1)/z · Rop α (PhiTs α Φs)`: the factor
`(z+1)/z` is constant in `θ`, hence commutes with `D_θ`, and it cancels against the
`z/(1+z)` on the right hand side. -/
theorem dthIter_four_Rop_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter 4 (Work.Construction.Rop α
          (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * (z / (1 + z)) := by
  intro z hz θ hθ
  have hz0 : (0 : ℝ) < z := hz
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; exact hz.le
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hcpos : (0 : ℝ) < (z + 1) / z := div_pos hz1 hz0
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hmem := hs.R.1
  have hle : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ max Cs 0 * α :=
    le_trans hs.R.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  have hkey := Work.Spaces.pz_Dth_sup_bound α hα 4
    (fun z θ => (z + 1) / z * Work.Construction.Rop α
      (Work.FTS.Nonlin.PhiTs α Φs) z θ) hmem 4 0 (by norm_num) (by norm_num) z θ hzIz hθ
  simp only [Work.Spaces.pzIter_zero, pow_zero, div_one] at hkey
  have hbnd : (z + 1) / z * |Work.Spaces.DthIter 4 (Work.Construction.Rop α
      (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
      ≤ (max Cs 0 * α) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    have h := le_trans hkey (mul_le_mul_of_nonneg_right hle hΛ0)
    have hfac := Work.FTS.Nonlinear.Pieces.RNP.row19.DthIter_mul_zfactor 4
      (fun z => (z + 1) / z) (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
    rw [hfac, abs_mul, abs_of_pos hcpos] at h
    exact h
  have hprod : ((z + 1) / z) * (z / (1 + z)) = 1 := by
    field_simp
    ring
  have hd : 0 ≤ z / (1 + z) := div_nonneg hz0.le (by linarith : (0 : ℝ) ≤ 1 + z)
  have hstep := mul_le_mul_of_nonneg_right hbnd hd
  have hL : ((z + 1) / z * |Work.Spaces.DthIter 4 (Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTs α Φs)) z θ|) * (z / (1 + z))
      = |Work.Spaces.DthIter 4 (Work.Construction.Rop α
        (Work.FTS.Nonlin.PhiTs α Φs)) z θ| := by
    rw [mul_assoc, mul_left_comm, hprod, mul_one]
  rw [hL] at hstep
  exact hstep

end Work.FTS.Nonlinear.Pieces.RNP.row19.helpers
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.pz_dthIter_four_pthU_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 19: the `(k = 1, j = 4)`-slot bound for `∂_θ𝒰(Φ̃_*)`

The frozen `StarPkg α Cs Φs` carries the `𝒲^{5,∞}`-field

  `∂_θ𝒰(Φ̃_*) = ∂_θ (Uop α (PhiTs α Φs))`,   `|·|_{𝒲^{5,∞}} ≤ Cs · α`

(`StarPkg.dU`).  Its slot `(j, k) = (4, 1)` — four angular `D_θ`-derivatives followed by one
radial `∂_z` — is therefore controlled by

  `|∂_z D_θ^4 (∂_θ𝒰(Φ̃_*))(z,θ)| ≤ |·|_{𝒲^{5,∞}} / (1+z) · (α + sin 2θ) sin(2θ)^{α/5}`,

which is `Work.Spaces.pz_Dth_sup_bound` instantiated at `l = 5`, `j = 4`, `k = 1` (legitimate
since `1 + 4 ≤ 5`).  The `z`-weight `1/(z+1)^k = 1/(1+z)` is exactly the one in the statement,
and the `α`-factor `max Cs 0` replaces `Cs` through `Cs ≤ max Cs 0` (`α > 0`).  The proof is
purely bookkeeping: `pzIter 1 = ∂_z`, and the endpoint cases `θ = 0, π/2` are already handled
inside `pz_Dth_sup_bound` (there `sin(2θ) = 0`, so every `D_θ`-iterate vanishes).
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row19.helpers

/-- **The `(k = 1, j = 4)`-slot bound for `∂_θ𝒰(Φ̃_*)`.**  Directly from the frozen
`𝒲^{5,∞}`-bound `StarPkg.dU` via `Work.Spaces.pz_Dth_sup_bound`. -/
theorem pz_dthIter_four_pthU_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Spaces.pth
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            / (1 + z) := by
  intro z hz θ hθ
  -- the frozen `𝒲^{5,∞}`-bound of `∂_θ𝒰(Φ̃_*)`, with `Cs` upgraded to `max Cs 0`
  have hle : Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) ≤ max Cs 0 * α :=
    le_trans hs.dU.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  -- the slot bound `(j, k) = (4, 1)`, `1 + 4 ≤ 5`
  have hkey := Work.Spaces.pz_Dth_sup_bound α hα 5 (Work.Spaces.pth
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) hs.dU.1 4 1
      (by norm_num) (by norm_num) z θ hz hθ
  -- the two `z`-weights involved are the same
  have hz1 : (0 : ℝ) < z + 1 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    linarith
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  -- divide the `𝒲^{5,∞}`-bound by `(z+1)^1 = 1+z` and compare with `(max Cs 0 * α)/(1+z)`
  have hdiv : Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) / (z + 1) ^ 1 ≤ (max Cs 0 * α) / (1 + z) := by
    rw [pow_one, show (1 + z : ℝ) = z + 1 by ring]
    exact div_le_div_of_nonneg_right hle hz1.le
  have hstep := mul_le_mul_of_nonneg_right hdiv hΛ0
  -- reassociate the right hand side
  have hri : (max Cs 0 * α) / (1 + z)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          / (1 + z) := by
    ring
  -- `∂_z = pzIter 1`
  calc |Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
      = |Work.Spaces.pzIter 1 (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs)))) z θ| := rfl
    _ ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          / (1 + z) := by
        rw [← hri]
        exact le_trans hkey hstep

end Work.FTS.Nonlinear.Pieces.RNP.row19.helpers
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false

/-- **Additivity of `∂_z^k D_θ^i` on the open quadrant** for two data which are `C^∞` there:
`∂_z^k D_θ^i (f + g) = ∂_z^k D_θ^i f + ∂_z^k D_θ^i g` at every point of
`Q0 = (0,∞) × (0,π/2)`.

The induction is on `k`: the base case `k = 0` is the additivity of `D_θ^i`
(`SmoothOpen.DthIter_add`), and the step differentiates the (eventually equal) `z`-slices with
`deriv_add`, both summands being `C^∞` on the open quadrant. -/
theorem pzIter_DthIter_add_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i : ℕ) : ∀ k : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k (Work.Spaces.DthIter i (fun z θ => f z θ + g z θ)) z θ
        = Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ
          + Work.Spaces.pzIter k (Work.Spaces.DthIter i g) z θ := by
  intro k
  induction k with
  | zero =>
      intro z θ hz h1 h2
      exact Work.FTS.EllipticEst.SmoothOpen.DthIter_add hf hg i z θ hz h1 h2
  | succ m ih =>
      intro z θ hz h1 h2
      have heq : (fun z' : ℝ =>
            Work.Spaces.pzIter m (Work.Spaces.DthIter i (fun z θ => f z θ + g z θ)) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ
              + Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ
          (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ) z :=
        (((hf.DthIter i).pzIter m).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ
          (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) z :=
        (((hg.DthIter i).pzIter m).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ
            + Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) z
          = deriv (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ) z
            + deriv (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]

theorem F0_add {n : ℕ} {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hf : Work.FTS.PhiStar.F0 n K f) (hg : Work.FTS.PhiStar.F0 n K' g) : Work.FTS.PhiStar.F0 n (K + K') (fun z θ => f z θ + g z θ) := by
  intro k i hki z θ hz h1 h2
  have hsum := pzIter_DthIter_add_Q0 hsf hsg i k z θ hz h1 h2
  rw [hsum, mul_add]
  exact le_trans (abs_add_le _ _)
    (add_le_add (hf k i hki z θ hz h1 h2) (hg k i hki z θ hz h1 h2))

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_congr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false

/-! ## Congruence of the iterated operators on the open quadrant -/

/-- **`D_θ^i` only sees the germ in `θ`**:  if `f` and `g` agree on the open quadrant `Q0`, then
so do all their `D_θ`-iterates.

Induction on `i`:  `D_θ^{i+1} = sin(2θ)·∂_θ D_θ^i`, and `∂_θ` is unchanged when the `θ`-slice
is replaced by a function agreeing with it near `θ` (which stays inside `Q0` since `Q0` is open
in `θ`). -/
private lemma DthIter_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) Work.FTS.EllipticEst.Q0) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  induction i with
  | zero => exact h
  | succ i ih =>
      intro p hp
      have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
      have hslice : (fun θ' => Function.uncurry (Work.Spaces.DthIter i f) (p.1, θ'))
          =ᶠ[𝓝 p.2] (fun θ' => Function.uncurry (Work.Spaces.DthIter i g) (p.1, θ')) := by
        filter_upwards [hnb] with θ' hθ'
        exact ih hθ'
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i f) p.1 p.2
          = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i g) p.1 p.2
      rw [Work.Spaces.pth, Work.Spaces.pth]
      exact congrArg (fun t => Real.sin (2 * p.2) * t) hslice.deriv_eq

/-- **`∂_z^k` only sees the germ in `z`**:  if `f` and `g` agree on the open quadrant `Q0`, then
so do all their `∂_z`-iterates.

Induction on `k`: each step replaces the `z`-slice by a function agreeing with it near `z`
(still inside `Q0` since `Q0` is open in `z`) and uses that `deriv` respects eventual equality. -/
private lemma pzIter_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) Work.FTS.EllipticEst.Q0) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter k f))
      (Function.uncurry (Work.Spaces.pzIter k g)) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  induction k with
  | zero => exact h
  | succ n ih =>
      intro p hp
      have hnb : ∀ᶠ z' in 𝓝 p.1, (z', p.2) ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
      have hslice : (fun z' => Work.Spaces.pzIter n f z' p.2)
          =ᶠ[𝓝 p.1] (fun z' => Work.Spaces.pzIter n g z' p.2) := by
        filter_upwards [hnb] with z' hz'
        exact ih hz'
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pz, Function.uncurry]
        using hslice.deriv_eq

/-! ## The main lemma -/

theorem F0_congr {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ} (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (hg : Work.FTS.PhiStar.F0 n K g) : Work.FTS.PhiStar.F0 n K f := by
  intro k i hki z θ hz hθ hθ'
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ'⟩
  have hfg : Set.EqOn (Function.uncurry f) (Function.uncurry g) Work.FTS.EllipticEst.Q0 :=
    fun p hp => h p.1 p.2 hp.1 hp.2.1 hp.2.2
  have heq : Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ
      = Work.Spaces.pzIter k (Work.Spaces.DthIter i g) z θ :=
    pzIter_congr_Q0 (DthIter_congr_Q0 hfg i) k hmem
  rw [heq]
  exact hg k i hki z θ hz hθ hθ'

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

/-- **The flat class `F0` is closed under pointwise products**, with the constant
`2^n · K · K'`.  The proof is the two-operator Leibniz rule

`∂_z^k D_θ^i (f·g) = ∑_{a≤i} ∑_{c≤k} C(i,a) C(k,c) ∂_z^c D_θ^a f · ∂_z^{k-c} D_θ^{i-a} g`

(`Work.FTS.NonlinRows.sqo_pz_DthIter_mul_eq`), together with the split
`(z+1)^k = (z+1)^c · (z+1)^{k-c}`: every summand inherits the bound `K` from `f` and
`K'` from `g`, and the total coefficient is
`∑_{a≤i} ∑_{c≤k} C(i,a)C(k,c) = 2^i · 2^k ≤ 2^{i+k} ≤ 2^n`. -/
theorem F0_mul {n : ℕ} {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K') (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hf : Work.FTS.PhiStar.F0 n K f) (hg : Work.FTS.PhiStar.F0 n K' g) : Work.FTS.PhiStar.F0 n ((2 : ℝ) ^ n * K * K') (fun z θ => f z θ * g z θ) := by
  intro k i hki z θ hz hθ hθ'
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  rw [Work.FTS.NonlinRows.sqo_pz_DthIter_mul_eq k i f g hsf hsg z hz θ ⟨hθ, hθ'⟩]
  simp only [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun a ha => Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
        |(z + 1) ^ k * (↑(i.choose a) * ↑(k.choose c) *
          (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ *
            Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ))|
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
          ↑(i.choose a) * ↑(k.choose c) * K * K' := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc => ?_
        have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hck : c ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
        have hA : (z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| ≤ K := by
          have h := hf c a (by omega) z θ hz hθ hθ'
          rwa [abs_mul, abs_of_pos (pow_pos hz1 c)] at h
        have hB : (z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ| ≤ K' := by
          have h := hg (k - c) (i - a) (by omega) z θ hz hθ hθ'
          rwa [abs_mul, abs_of_pos (pow_pos hz1 (k - c))] at h
        have hcoef : (0 : ℝ) ≤ ↑(i.choose a) * ↑(k.choose c) := by positivity
        have hpow : (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) := by
          rw [← pow_add, Nat.add_sub_of_le hck]
        have heq : |(z + 1) ^ k * (↑(i.choose a) * ↑(k.choose c) *
            (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ *
              Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ))|
            = (↑(i.choose a) * ↑(k.choose c)) *
                ((z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|) *
                ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ|) := by
          simp only [abs_mul, abs_of_pos (pow_pos hz1 c), abs_of_pos (pow_pos hz1 (k - c)),
            abs_of_nonneg hcoef, hpow]
          ring
        rw [heq]
        calc (↑(i.choose a) * ↑(k.choose c)) *
                ((z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|) *
                ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (i - a) g) z θ|)
            ≤ ((↑(i.choose a) * ↑(k.choose c)) * K) * K' :=
              mul_le_mul (mul_le_mul_of_nonneg_left hA hcoef) hB
                (mul_nonneg (pow_nonneg (le_of_lt hz1) _) (abs_nonneg _))
                (mul_nonneg hcoef hK)
          _ = ↑(i.choose a) * ↑(k.choose c) * K * K' := by ring
    _ ≤ 2 ^ n * K * K' := by
        have hSi : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℝ))) = (2 : ℝ) ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        have hSk : (∑ c ∈ Finset.range (k + 1), ((k.choose c : ℝ))) = (2 : ℝ) ^ k := by
          exact_mod_cast Nat.sum_range_choose k
        have hstep0 : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
              ((i.choose a : ℝ) * (k.choose c : ℝ)) * K * K')
            = (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ)) * (K * K')) := by
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
          ring
        have hstep1 : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ)) * (K * K'))
            = (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ))) * (K * K') := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_mul]
        have hstep2 : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
                ((i.choose a : ℝ) * (k.choose c : ℝ)))
            = (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)) * (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)) := by
          rw [Finset.sum_mul_sum]
        have hS : (∑ a ∈ Finset.range (i + 1), ∑ c ∈ Finset.range (k + 1),
              ((i.choose a : ℝ) * (k.choose c : ℝ)) * K * K')
            = ((2 : ℝ) ^ i * (2 : ℝ) ^ k) * (K * K') := by
          rw [hstep0, hstep1, hstep2, hSi, hSk]
        refine le_trans (le_of_eq hS) ?_
        have hik : i + k ≤ n := by omega
        have hpow2 : (2 : ℝ) ^ i * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) hik
        have hKK' : 0 ≤ K * K' := mul_nonneg hK hK'
        calc ((2 : ℝ) ^ i * (2 : ℝ) ^ k) * (K * K') ≤ (2 : ℝ) ^ n * (K * K') :=
              mul_le_mul_of_nonneg_right hpow2 hKK'
          _ = (2 : ℝ) ^ n * K * K' := by ring

end Work.FTS.PhiStar.CoreAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_theta_coefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

/-- **A `θ`-only function with `C^m` slice belongs to `F0 m`.**

If all the angular iterates `dthU^[i] c` (`i ≤ m`) are continuous on the compact interval
`Iθ`, then there is a positive constant `A` with `F0 m A (fun _ θ => c θ)`: indeed every slot
with a radial derivative vanishes, and the purely angular slots are bounded by the finitely
many suprema of the continuous functions `dthU^[i] c` on `Iθ`.

The constant produced is `(∑_{i ≤ m} B i) + 1`, where `B i` is a bound for `dthU^[i] c` on
`Iθ`; the `+1` makes it positive without any hypothesis on the signs of the `B i`. -/
theorem exists_F0_of_theta_only_aux (m : ℕ) (c : ℝ → ℝ)
    (hc : ∀ i ≤ m, ContinuousOn (fun θ => (Work.Spaces.dthU^[i]) c θ) Work.Spaces.Iθ) :
    ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 m A (fun _ θ => c θ) := by
  have hbdd : ∀ i : ℕ, ∃ B : ℝ, i ≤ m → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.dthU^[i]) c θ| ≤ B := by
    intro i
    by_cases hi : i ≤ m
    · obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc i hi)
      exact ⟨B, fun _ θ hθ => by simpa [Real.norm_eq_abs] using hB θ hθ⟩
    · exact ⟨0, fun h => absurd h hi⟩
  classical
  choose B hB using hbdd
  have hB0 : ∀ i, i ≤ m → 0 ≤ B i := by
    intro i hi
    have h := hB i hi 0 (by
      simp only [Work.Spaces.Iθ, Set.mem_Icc]
      exact ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
    linarith [abs_nonneg ((Work.Spaces.dthU^[i]) c 0)]
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m + 1), B i :=
    Finset.sum_nonneg (fun i hi => hB0 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  refine ⟨(∑ i ∈ Finset.range (m + 1), B i) + 1, by linarith, ?_⟩
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hi : i ≤ m := by omega
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ'.le⟩
    rw [Work.FTS.PhiStar.Psi0Est.DthIter_theta_only c i]
    simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul]
    have h1 := hB i hi θ hθI
    have h2 : B i ≤ ∑ j ∈ Finset.range (m + 1), B j :=
      Finset.single_le_sum (fun j hj => hB0 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
        (Finset.mem_range.mpr (by omega))
    linarith
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Work.FTS.PhiStar.Psi0Est.DthIter_theta_only c i,
        Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ (Work.Spaces.dthU^[i] c) k']
    simp only [mul_zero, abs_zero]
    linarith

theorem F0_theta_coefs (m : ℕ) : ∃ C : ℝ, 0 < C ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.sin θ ^ 2) ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.cos (2 * θ)) ∧ Work.FTS.PhiStar.F0 m C (fun _ θ => Real.sin (2 * θ)) := by
  have key : ∀ (c : ℝ → ℝ), ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) c →
      ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 m A (fun _ θ => c θ) := fun c hc =>
    exists_F0_of_theta_only_aux m c
      (fun i hi => LopIter_continuousOn_of_contDiff m c hc i hi)
  obtain ⟨A1, hA1, hF1⟩ := key (fun θ => Real.sin θ ^ 2) (by fun_prop)
  obtain ⟨A2, hA2, hF2⟩ := key (fun θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by fun_prop)
  obtain ⟨A3, hA3, hF3⟩ := key (fun θ => Real.cos (2 * θ)) (by fun_prop)
  obtain ⟨A4, hA4, hF4⟩ := key (fun θ => Real.sin (2 * θ)) (by fun_prop)
  refine ⟨A1 + A2 + A3 + A4, by linarith, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF1
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF2
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF3
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) hF4

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_z_coefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false

/-! ## `D_θ` of a function of `z` alone -/


/-- All the higher `D_θ`-iterates of a `θ`-independent function vanish. -/
private lemma DthIter_thetaOnly_succ (φ : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter (i+1) (fun z _ => φ z) = fun _ _ => 0 := by
  induction i with
  | zero =>
    funext z θ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
      Work.Spaces.pth]
    rw [deriv_const]; ring
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const]; ring

/-- `∂_z^k` of the zero function is zero. -/
private lemma pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0:ℝ)) = fun _ _ => 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; rfl
  · exact Work.FTS.PhiStar.pzIter_const_of_theta_only 0 k hk

/-- For a function of `z` alone the iterated operator `∂_z^k` acts on the `z`-variable. -/
private lemma pzIter_thetaOnly (φ : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z _ => φ z) = fun z _ => (deriv^[k]) φ z := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pzIter_succ, ih, Function.iterate_succ_apply']; rfl

/-! ## The radial bounds -/

/-- `|(1+z)^k ∂_z^k (1+z)⁻¹| ≤ k!` for `z > 0`. -/
private lemma inv_bound (k : ℕ) (z : ℝ) (hz : 0 < z) :
    |(1+z)^k * (deriv^[k] (fun z => (1+z)⁻¹)) z| ≤ (k.factorial : ℝ) := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  have hformula : (deriv^[k] (fun z => (1+z)⁻¹)) z
      = (-1)^k * (k.factorial : ℝ) * (1+z)^(-1 - (k:ℤ)) := by
    rw [← iteratedDeriv_eq_iterate]
    rw [iteratedDeriv_comp_const_add k Inv.inv 1]
    simp only []
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hzpow : (1+z)^k * (1+z)^(-1 - (k:ℤ)) = (1+z)⁻¹ := by
    rw [← zpow_natCast (1+z) k, ← zpow_add₀ (ne_of_gt h1z)]
    rw [show ((k:ℤ) + (-1 - (k:ℤ))) = -1 by ring, zpow_neg_one]
  have hkey : (1+z)^k * (deriv^[k] (fun z => (1+z)⁻¹)) z
      = (-1)^k * (k.factorial : ℝ) * (1+z)⁻¹ := by
    rw [hformula]
    rw [show (1+z)^k * ((-1)^k * (k.factorial : ℝ) * (1+z)^(-1 - (k:ℤ)))
        = (-1)^k * (k.factorial : ℝ) * ((1+z)^k * (1+z)^(-1 - (k:ℤ))) by ring, hzpow]
  rw [hkey, abs_mul, abs_mul]
  rw [show |(-1:ℝ)^k| = 1 by simp, abs_of_nonneg (Nat.cast_nonneg k.factorial),
      abs_of_pos (inv_pos.mpr h1z), one_mul]
  calc (k.factorial : ℝ) * (1+z)⁻¹ ≤ (k.factorial : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [inv_le_one₀ (by linarith)]; linarith
    _ = (k.factorial : ℝ) := by ring

/-- `|(1+z)^k ∂_z^k (z/(1+z))| ≤ k!` for `z > 0`.

Since `z/(1+z) = 1 - (1+z)⁻¹` on the open half line, `∂_z^k` of it is `[k = 0] - ∂_z^k(1+z)⁻¹`
(the two functions agree on the open set `(-1,∞)`, and `iteratedDeriv` is additive). -/
private lemma div_bound (k : ℕ) (z : ℝ) (hz : 0 < z) :
    |(1+z)^k * (deriv^[k] (fun z => z/(1+z))) z| ≤ (k.factorial : ℝ) := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  have hne : (1:ℝ) + z ≠ 0 := ne_of_gt h1z
  have heqon : Set.EqOn (fun z : ℝ => z/(1+z)) (fun z : ℝ => 1 - (1+z)⁻¹)
      (Set.Ioi (-1)) := by
    intro w hw
    simp only [Set.mem_Ioi] at hw
    have hw1 : (1:ℝ) + w ≠ 0 := by linarith
    rw [div_eq_iff hw1, sub_mul, one_mul, inv_mul_cancel₀ hw1]
    ring
  have hc1 : ContDiffAt ℝ k (fun z : ℝ => (1+z)⁻¹) z := by
    have h : ContDiffAt ℝ k (fun z : ℝ => 1 + z) z := by fun_prop
    exact h.inv hne
  have hc0 : ContDiffAt ℝ k (fun z : ℝ => (1:ℝ)) z := contDiffAt_const
  have hfe : ((fun _ : ℝ => (1:ℝ)) - fun z : ℝ => (1+z)⁻¹)
      = (fun z : ℝ => 1 - (1+z)⁻¹) := by
    funext w; rfl
  have hsub : iteratedDeriv k (fun z : ℝ => 1 - (1+z)⁻¹) z
      = (if k = 0 then (1:ℝ) else 0) - iteratedDeriv k (fun z : ℝ => (1+z)⁻¹) z := by
    have h := iteratedDeriv_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun z : ℝ => (1+z)⁻¹)
      hc0 hc1
    rw [iteratedDeriv_const, hfe] at h
    exact h
  have hiter : iteratedDeriv k (fun z : ℝ => z/(1+z)) z
      = iteratedDeriv k (fun z : ℝ => 1 - (1+z)⁻¹) z :=
    heqon.iteratedDeriv_of_isOpen isOpen_Ioi k (by simp only [Set.mem_Ioi]; linarith)
  have hmain : iteratedDeriv k (fun z : ℝ => z/(1+z)) z
      = (if k = 0 then (1:ℝ) else 0) - iteratedDeriv k (fun z : ℝ => (1+z)⁻¹) z := by
    rw [hiter, hsub]
  rw [← iteratedDeriv_eq_iterate, hmain]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, iteratedDeriv_zero]
    norm_num
    have hval : (1:ℝ) - (1+z)⁻¹ = z/(1+z) := by
      rw [eq_div_iff hne, sub_mul, one_mul, inv_mul_cancel₀ hne]; ring
    rw [hval, abs_of_nonneg (by positivity), div_le_iff₀ h1z]
    linarith
  · rw [ite_eq_right (by omega), zero_sub, mul_neg, abs_neg, iteratedDeriv_eq_iterate]
    exact inv_bound k z hz

/-! ## From the radial bounds to `F0` -/

/-- A `θ`-independent function whose radial bounds are all `k!` lies in the flat class
`F0 m` with the constant `m!`: for `i ≥ 1` the integrand is `0`, and for `i = 0` we use
`k! ≤ m!`. -/
private lemma F0_thetaOnly (φ : ℝ → ℝ) (m : ℕ)
    (h : ∀ k, ∀ z, 0 < z → |(1+z)^k * (deriv^[k] φ) z| ≤ (k.factorial : ℝ)) :
    Work.FTS.PhiStar.F0 m (m.factorial : ℝ) (fun z _ => φ z) := by
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Work.Spaces.DthIter_zero, pzIter_thetaOnly]
    simp only []
    rw [show z + 1 = 1 + z by ring]
    exact le_trans (h k z hz) (by exact_mod_cast Nat.factorial_le (by omega : k ≤ m))
  · have hz0 : Work.Spaces.DthIter i (fun z _ => φ z) = fun _ _ => 0 := by
      conv_lhs => rw [← Nat.sub_add_cancel hi]
      exact DthIter_thetaOnly_succ φ (i-1)
    rw [hz0, pzIter_zero_fun]
    simp only [mul_zero, abs_zero]
    exact Nat.cast_nonneg _

theorem F0_z_coefs (m : ℕ) : ∃ C : ℝ, 0 < C ∧ Work.FTS.PhiStar.F0 m C (fun z _ => z / (1 + z)) ∧ Work.FTS.PhiStar.F0 m C (fun z _ => (1 + z)⁻¹) := by
  refine ⟨(m.factorial : ℝ), Nat.cast_pos.mpr (Nat.factorial_pos m), ?_, ?_⟩
  · exact F0_thetaOnly (fun z => z/(1+z)) m div_bound
  · exact F0_thetaOnly (fun z => (1+z)⁻¹) m inv_bound

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_zpz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

/-- **Commutation of `D_θ^i` with `D_z = z ∂_z` on the open quadrant**, for a datum of class
`C^∞` there:  `D_θ^i (z ∂_z f) = z ∂_z (D_θ^i f)` at every interior point.

This is `DthIter_DzIter_eqOn_of_isOpen` (`j = 1`), whose left side is
`D_θ^i (D_z^1 f) = D_θ^i (z ∂_z f)` and whose right side is `mixed 1 i f = z ∂_z (D_θ^i f)`;
`SmoothOpen` is exactly the finite-order smoothness `∀ n, ContDiffOn ℝ n _ Q0` required by
that lemma. -/
theorem DthIter_Dz_comm_smoothOpen {f : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (fun z θ => z * Work.Spaces.pz f z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DthIter i f) z θ := by
  intro z θ hz hθ hθ'
  have h := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsf) 1 i
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)
  exact h

/-- **The `k`-fold product rule for `z ↦ z ∂_z g`.**  If `A` agrees with `z ∂_z B` on the open
quadrant and `B` is `C^∞` there, then for every interior point

`∂_z^k A = z · ∂_z^{k+1} B + k · ∂_z^k B`.

The proof is an induction on `k`.  The base case is the hypothesis.  In the step, the
induction hypothesis identifies the slice `z' ↦ ∂_z^k A z' θ` with
`z' ↦ z' ∂_z^{k+1} B z' θ + k ∂_z^k B z' θ` near `z` (it holds for every interior `z'`), so
its derivative is computed from the two `HasDerivAt`-statements for the `z`-slices of
`∂_z^{k+1} B` and `∂_z^k B` (`SmoothOpen.hasDerivAt_slice_pzIter`), giving
`∂_z^{k+1} B + z ∂_z^{k+2} B + k ∂_z^{k+1} B = z ∂_z^{k+2} B + (k+1) ∂_z^{k+1} B`. -/
theorem pzIter_zpz_expand {A B : ℝ → ℝ → ℝ}
    (hA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → A z θ = z * Work.Spaces.pz B z θ)
    (hB : Work.FTS.EllipticEst.SmoothOpen B) (k : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k A z θ
        = z * Work.Spaces.pzIter (k + 1) B z θ + (k : ℝ) * Work.Spaces.pzIter k B z θ := by
  induction k with
  | zero =>
      intro z θ hz hθ hθ'
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Nat.cast_zero, zero_mul,
        add_zero]
      exact hA z θ hz hθ hθ'
  | succ k ih =>
      intro z θ hz hθ hθ'
      have heq : (fun z' : ℝ => Work.Spaces.pzIter k A z' θ)
          =ᶠ[𝓝 z] (fun z' => z' * Work.Spaces.pzIter (k + 1) B z' θ
              + (k : ℝ) * Work.Spaces.pzIter k B z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' hθ hθ'
      have hAd : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter (k + 1) B z' θ)
          (Work.Spaces.pzIter (k + 1 + 1) B z θ) z :=
        hB.hasDerivAt_slice_pzIter (k + 1) ⟨hθ, hθ'⟩ hz
      have hBd : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter k B z' θ)
          (Work.Spaces.pzIter (k + 1) B z θ) z :=
        hB.hasDerivAt_slice_pzIter k ⟨hθ, hθ'⟩ hz
      have h1 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter (k + 1) B z' θ)
          (1 * Work.Spaces.pzIter (k + 1) B z θ
            + z * Work.Spaces.pzIter (k + 1 + 1) B z θ) z :=
        (hasDerivAt_id z).mul hAd
      have h2 : HasDerivAt (fun z' : ℝ => (k : ℝ) * Work.Spaces.pzIter k B z' θ)
          ((k : ℝ) * Work.Spaces.pzIter (k + 1) B z θ) z := hBd.const_mul (k : ℝ)
      have hderiv : deriv (fun z' : ℝ => z' * Work.Spaces.pzIter (k + 1) B z' θ
            + (k : ℝ) * Work.Spaces.pzIter k B z' θ) z
          = 1 * Work.Spaces.pzIter (k + 1) B z θ
            + z * Work.Spaces.pzIter (k + 1 + 1) B z θ
            + (k : ℝ) * Work.Spaces.pzIter (k + 1) B z θ := (h1.add h2).deriv
      rw [Work.Spaces.pzIter_succ]
      simp only [Work.Spaces.pz]
      rw [heq.deriv_eq, hderiv]
      push_cast
      ring

theorem F0_zpz {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 (n + 1) K f) : Work.FTS.PhiStar.F0 n (((n : ℝ) + 1) * K) (fun z θ => z * Work.Spaces.pz f z θ) := by
  intro k i hki x y hx hy hxy
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  -- rewrite the `k`-fold `∂_z` by the product rule `∂_z^k(z ∂_z B) = z ∂_z^{k+1} B + k ∂_z^k B`
  have hexp := pzIter_zpz_expand
    (A := Work.Spaces.DthIter i (fun z θ => z * Work.Spaces.pz f z θ))
    (B := Work.Spaces.DthIter i f) (DthIter_Dz_comm_smoothOpen hsf i) (hsf.DthIter i) k x y
    hx hy hxy
  rw [hexp]
  -- the two pieces of the flat bound for `B = D_θ^i f`
  have hbA : (x + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y| ≤ K := by
    have h := hf (k + 1) i (by omega) x y hx hy hxy
    rwa [abs_mul, abs_of_pos (pow_pos hx1 (k + 1))] at h
  have hbB : (x + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| ≤ K := by
    have h := hf k i (by omega) x y hx hy hxy
    rwa [abs_mul, abs_of_pos (pow_pos hx1 k)] at h
  have htri : |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y
        + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
      ≤ (x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
        + (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := by
    have h1 : |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
        ≤ (x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y| := by
      rw [abs_mul, abs_of_nonneg hx.le]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h2 : |(k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
        = (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    calc |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y
            + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
        ≤ |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + |(k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := abs_add_le _ _
      _ ≤ (x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := by
            rw [h2]; exact add_le_add h1 le_rfl
  rw [abs_mul, abs_of_pos (pow_pos hx1 k)]
  calc (x + 1) ^ k * |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y
          + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
      ≤ (x + 1) ^ k * ((x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|) :=
          mul_le_mul_of_nonneg_left htri (pow_nonneg hx1.le k)
    _ = (x + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + (k : ℝ) * ((x + 1) ^ k
            * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|) := by
          rw [pow_succ]; ring
    _ ≤ K + (k : ℝ) * K := add_le_add hbA (mul_le_mul_of_nonneg_left hbB (Nat.cast_nonneg k))
    _ = ((k : ℝ) + 1) * K := by ring
    _ ≤ ((n : ℝ) + 1) * K := by
          have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : k ≤ n)
          exact mul_le_mul_of_nonneg_right (by linarith) hK

end Work.FTS.PhiStar.CoreAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Fb_of_FlatW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option maxHeartbeats 2000000

/-! ## The `∂_θ f`-half -/

/-- **`FlatW 7 f K` gives the flat bounds of `F0 6` for `∂_θ f`**, directly: `F0 6` needs the
angular order `k+i`, one *less* than the order `k+i+1` recorded by `FlatW 7`. -/
theorem F0_six_pth_of_FlatW {K : ℝ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.VocabO2.FlatW 7 f K) :
    Work.FTS.PhiStar.F0 6 K (Work.Spaces.pth f) := by
  intro k i hki z θ hz hθ hθ'
  exact (h z θ hz hθ hθ').2 k i (by omega)

/-! ## The Leibniz sum -/

/-- **The `a`-th summand of the Leibniz expansion is bounded by `C(i-1,a)·A·K`.** -/
theorem leibniz_term_le {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (h : Work.FTS.VocabO2.FlatW 7 f K) {i k a : ℕ} (ha : a ∈ Finset.range i) (hki : k + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * (((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ))|
      ≤ ((i - 1).choose a : ℝ) * (A * K) := by
  have hai : a ≤ i - 1 := by
    have := Finset.mem_range.mp ha
    omega
  have ha5 : a ≤ 5 := by omega
  have hX : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A := hAb a ha5 z θ hθ hθ'
  have hY : |(z + 1) ^ k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
    (h z θ hz hθ hθ').2 k (i - 1 - a) (by omega)
  have hcoef : (0 : ℝ) ≤ ((i - 1).choose a : ℝ) := by positivity
  have hzp : (0 : ℝ) < (z + 1) ^ k := pow_pos (by linarith) k
  have h1 : |(z + 1) ^ k * (((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ))|
      = ((i - 1).choose a : ℝ) *
        (|Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| *
          |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ|) := by
    simp only [abs_mul, abs_of_nonneg hcoef, abs_of_pos hzp]
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hX hY (abs_nonneg _) hA) hcoef

/-- **The Leibniz sum is bounded by `2^{i-1}·A·K ≤ 32·A·K`.** -/
theorem leibniz_sum_le {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (h : Work.FTS.VocabO2.FlatW 7 f K) {i k : ℕ} (hi : 1 ≤ i) (hki : k + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |(z + 1) ^ k * ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pth f)) z θ)|
      ≤ 32 * A * K := by
  have hchoose : (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) = (2 : ℝ) ^ (i - 1) := by
    have h1 : Finset.range i = Finset.range ((i - 1) + 1) := by
      congr 1
      omega
    rw [h1]
    exact_mod_cast Nat.sum_range_choose (n := i - 1)
  have hpow : (2 : ℝ) ^ (i - 1) ≤ 32 := by
    have hi6 : i ≤ 6 := by omega
    calc (2 : ℝ) ^ (i - 1) ≤ 2 ^ 5 := by
          apply pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 32 := by norm_num
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun a ha => leibniz_term_le hA hK hAb h ha hki hz hθ hθ')) ?_
  calc (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) * (A * K))
      = (∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ)) * (A * K) := (Finset.sum_mul ..).symm
    _ = (2 : ℝ) ^ (i - 1) * (A * K) := by rw [hchoose]
    _ ≤ 32 * (A * K) := mul_le_mul_of_nonneg_right hpow (mul_nonneg hA hK)
    _ = 32 * A * K := by ring

/-! ## The two halves of `Fb 6` -/

/-- **A bound on the fifth iterate gives a uniform bound on the iterates of orders `≤ 5`**: the
orders `≤ 4` are covered by the explicit `Work.FTS.H2.abs_DthIter_Sfun_le`
(`|D_θ^r(sin 2·)| ≤ Asin r · sin 2θ`, `Asin r ≤ 384`), and `sin 2θ ≤ 1` on `[0,π/2]`. -/
theorem exists_bound_of_five {M : ℝ} (hM : 0 < M)
    (h5 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ| ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A := by
  have hsmall : ∀ (r : ℕ), r ≤ 4 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter r Work.FTS.H2.Sfun z θ| ≤ 384 := by
    intro r hr z θ hθ hθ'
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hb := Work.FTS.H2.abs_DthIter_Sfun_le r hr z
      (θ := θ) (by simp only [Work.Spaces.Iθ]; exact ⟨hθ.le, hθ'.le⟩)
    have hA : Work.FTS.H2.Asin r ≤ 384 := by
      interval_cases r <;> norm_num [Work.FTS.H2.Asin]
    calc |Work.Spaces.DthIter r Work.FTS.H2.Sfun z θ|
        ≤ Work.FTS.H2.Asin r * Real.sin (2 * θ) := hb
      _ ≤ 384 * 1 := mul_le_mul hA hsin1 hsin0 (by norm_num)
      _ = 384 := by ring
  refine ⟨max 384 M, lt_max_of_lt_left (by norm_num), fun a ha z θ hθ hθ' => ?_⟩
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 by omega)
    with h | h | h | h | h | h <;> rw [h]
  · exact le_trans (hsmall 0 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 1 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 2 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 3 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (hsmall 4 (by norm_num) z θ hθ hθ') (le_max_left _ _)
  · exact le_trans (h5 z θ hθ hθ') (le_max_right _ _)

/-- **`FlatW 7 f K` gives `F0 6 (C·K) f`**, with the explicit constant `C = 32·A + 1` where `A`
bounds the `D_θ`-iterates of `sin 2·` up to order `5`. -/
theorem F0_six_of_FlatW {A K : ℝ} {f : ℝ → ℝ → ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hAb : ∀ a : ℕ, a ≤ 5 → ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| ≤ A)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h : Work.FTS.VocabO2.FlatW 7 f K) :
    Work.FTS.PhiStar.F0 6 ((32 * A + 1) * K) f := by
  intro k i hki z θ hz hθ hθ'
  have hC1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 0 f) z θ| ≤ K := by
      simpa using (h z θ hz hθ hθ').1 k (by omega)
    calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 0 f) z θ| ≤ K := h0
      _ = 1 * K := by ring
      _ ≤ (32 * A + 1) * K := mul_le_mul_of_nonneg_right hC1 hK
  · rw [Work.FTS.PhiStar.pzIter_DthIter_leibniz hsm hi hz ⟨hθ, hθ'⟩]
    exact le_trans (leibniz_sum_le hA hK hAb h hi hki hz hθ hθ') (by
      have h32 : (32 : ℝ) * A * K ≤ (32 * A + 1) * K := by nlinarith [mul_nonneg hA hK]
      linarith)

/-- **`FlatW 7` implies `Fb 6`** (up to a universal constant): the constant is `C = 32·A + 1`,
where `A = max 384 M` bounds the `D_θ`-iterates of `sin 2·` of orders `≤ 5`
(`Work.FTS.PhiStar.CoreAux.DthIter_five_Sfun_bound` supplies `M` for the order-`5` iterate and
`Work.FTS.H2.abs_DthIter_Sfun_le` the orders `≤ 4`). -/
theorem Fb_of_FlatW : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (f : ℝ → ℝ → ℝ), 0 ≤ K → Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 7 f K → Work.FTS.PhiStar.Fb 6 (C * K) f := by
  obtain ⟨M, hMpos, hM⟩ := DthIter_five_Sfun_bound
  obtain ⟨A, hApos, hAb⟩ := exists_bound_of_five hMpos hM
  refine ⟨32 * A + 1, by linarith, ?_⟩
  intro K f hK hsm hflat
  have hmono : K ≤ (32 * A + 1) * K := by
    have h1 : (1 : ℝ) ≤ 32 * A + 1 := by linarith
    calc K = 1 * K := by ring
      _ ≤ (32 * A + 1) * K := mul_le_mul_of_nonneg_right h1 hK
  exact ⟨F0_six_of_FlatW hApos.le hK hAb hsm hflat,
    (F0_six_pth_of_FlatW hflat).mono le_rfl hmono⟩

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The radial block `D_zŶ = z ∂_zŶ`. -/
def Yblk (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Y z θ

/-- The angular block `D_θŶ = sin(2θ)·∂_θŶ`. -/
def Tblk (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.s2 θ * Work.Spaces.pth Y z θ

/-- The combination `W₁ = 3Ŷ + α(Ŷ/(z+1) + D_zŶ)` appearing in `𝒰` and `∂_θ𝒰`. -/
def Wone (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 3 * Y z θ + α * (Y z θ / (z + 1) + Yblk Y z θ)

/-- `((z+1)/z)·ℛ(Φ̃_*)` in terms of `Ŷ`. -/
def EH (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Y z θ + 2 * α * Real.sin θ ^ 2 * (Y z θ / (z + 1) + Yblk Y z θ)
    + Tblk Y z θ

/-- `((z+1)/z)·𝒱(Φ̃_*)` in terms of `Ŷ`. -/
def EVz (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ + Tblk Y z θ

/-- `𝒱(Φ̃_*)` in terms of `Ŷ`. -/
def EV (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z / (z + 1) * EVz Y z θ

/-- `𝒰(Φ̃_*)/σ` in terms of `Ŷ`. -/
def EU (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(z / (z + 1)) * Wone α Y z θ

/-- `((z+1)/z)·𝒰(Φ̃_*)/σ` in terms of `Ŷ`. -/
def EUz (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => -Wone α Y z θ

/-- `∂_θ𝒰(Φ̃_*)` in terms of `Ŷ`. -/
def EPU (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(2 * Real.cos (2 * θ) * (z / (z + 1)) * Wone α Y z θ
    + Work.Construction.s2 θ * (z / (z + 1))
      * (3 * Work.Spaces.pth Y z θ
        + α * (Work.Spaces.pth Y z θ / (z + 1) + z * Work.Spaces.pz (Work.Spaces.pth Y) z θ)))

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ModeExpansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false


/-- `radGreen` is linear in its source. -/
theorem radGreen_const_mul (α : ℝ) (m : ℕ) (k : ℝ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun t => k * c t) z
      = k * Work.FTS.PhiStar.Radial.radGreen α m c z := by
  have h1 : (∫ t in (0 : ℝ)..z, (k * c t) * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = k * ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have h2 : (∫ t in Set.Ioi z, (k * c t) * t ^ (-(2 * (m : ℝ) / α) - 1))
      = k * ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]
  ring



/-- For an `AngModel` the kernel mode coefficient `bmode 0 ψ` vanishes. -/
theorem bmode_zero_of_moment {ψ : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  have h := Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF
  rw [Work.FTS.PhiStar.Series.bmode_eq_cmode 0 ψ 0]
  exact h

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.phiABddDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Finset

namespace Work.FTS.PhiStar.Series.Deleg

/-- **The `k`-th derivative of `phiA α` on `z > 0` is the closed form `phiAseries α k`.**
By induction on `k`: `k = 0` is `phiAeqSeries`, and the step differentiates
`iteratedDeriv k (phiA α)` (which agrees with `phiAseries α k` on the open set `Ioi 0`,
a neighbourhood of `z`) using `hasDerivAtPhiAseries`. -/
theorem iteratedDeriv_phiA_eq_series (α : ℝ) :
    ∀ k : ℕ, ∀ z : ℝ, 0 < z →
      iteratedDeriv k (Work.FTS.VocabO.phiA α) z = phiAseries α k z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero]
      exact phiAeqSeries α z (by intro h; rw [h] at hz; norm_num at hz)
  | succ k ih =>
      intro z hz
      have hz1 : z ≠ -1 := by intro h; rw [h] at hz; norm_num at hz
      have hev : iteratedDeriv k (Work.FTS.VocabO.phiA α) =ᶠ[𝓝 z] phiAseries α k := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hasDerivAtPhiAseries α k hz1).deriv

/-- Each term of `phiAseries α k` is bounded by `30 · 26^22` for `k ≤ 22` and `z > 0`
(`phiAtermBound`), and there are four terms. -/
theorem abs_phiAseries_le (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) {k : ℕ} (hk : k ≤ 22)
    {z : ℝ} (hz : 0 < z) : |phiAseries α k z| ≤ 1000 * 26 ^ 22 := by
  have hterm : ∀ n ∈ Finset.range 4,
      |phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| ≤ 30 * 26 ^ 22 :=
    fun n hn => phiAtermBound α hα hα5 n k (Finset.mem_range.mp hn) hk hz
  have hstep : |phiAseries α k z| ≤ ∑ n ∈ Finset.range 4, (30 * 26 ^ 22 : ℝ) := by
    have hsum : phiAseries α k z
        = ∑ n ∈ Finset.range 4, phiAcoef α n
            * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
            * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ)) := rfl
    rw [hsum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hsum4 : (∑ n ∈ Finset.range 4, (30 * 26 ^ 22 : ℝ)) = 120 * 26 ^ 22 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  calc |phiAseries α k z| ≤ ∑ n ∈ Finset.range 4, (30 * 26 ^ 22 : ℝ) := hstep
    _ = 120 * 26 ^ 22 := hsum4
    _ ≤ 1000 * 26 ^ 22 :=
        mul_le_mul_of_nonneg_right (by norm_num : (120 : ℝ) ≤ 1000) (by positivity)

/-- **The delegated target**: `𝒜φ = VocabO.phiA α` has all `22` first derivatives bounded
by the universal constant `1000·26^22`, for `0 < α ≤ 1/5`. -/
theorem phiABddDeriv (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) :
    ∃ K : ℝ, 0 ≤ K ∧ Work.FTS.PhiStar.BddDeriv 22 (Work.FTS.VocabO.phiA α) K := by
  refine ⟨1000 * 26 ^ 22, by positivity, ?_⟩
  intro k hk z hz
  rw [iteratedDeriv_phiA_eq_series α k z hz]
  exact abs_phiAseries_le α hα hα5 hk hz

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.wlInf_of_zeroOff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The radial slots

`radial_slot_le` (the closed-domain form of the first family of `FlatW`-slots) is imported from
`FTS/PhiStar/radial_slot_le.lean`; the lemmas below are the tools its sibling
`angular_slot_le` needs. -/

/-! ## `deriv` of a function vanishing on `(-∞,0]`

The whole point of the `zeroOff` hypothesis at `z = 0`: the `z`-slice `z' ↦ f z' θ` vanishes on
`(-∞,0]`, and for such a function the (totalised) `deriv` at `0` is `0`: if it is differentiable
then the two-sided difference-quotient limit is forced to `0` by the left half-line, and if it is
not differentiable Lean's `deriv` is `0` by definition. -/

theorem deriv_eq_zero_of_eqOn_Iic_zero {g : ℝ → ℝ} (h : ∀ x ≤ 0, g x = 0) :
    deriv g 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ g 0
  · have h1 : Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 (deriv g 0)) :=
      hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have h2 : Tendsto (slope g 0) (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)) (𝓝 (deriv g 0)) :=
      h1.mono_left (nhdsWithin_mono 0 fun x hx =>
        Set.mem_compl_singleton_iff.mpr (ne_of_lt hx))
    have h3 : (fun y => slope g 0 y) =ᶠ[𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [slope_def_field, h y (le_of_lt hy), h 0 le_rfl]
      ring
    have h4 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ))
        (𝓝 (deriv g 0)) :=
      h2.congr' h3
    haveI : (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
    exact tendsto_nhds_unique h4 tendsto_const_nhds
  · exact deriv_zero_of_not_differentiableAt hd

/-- Every iterated derivative, at a point of `(-∞,0]`, of a function vanishing on `(-∞,0]`,
vanishes.  (The intended use is `x = 0`.) -/
theorem iteratedDeriv_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} (h : ∀ x ≤ 0, g x = 0) :
    ∀ (k : ℕ) (x : ℝ), x ≤ 0 → iteratedDeriv k g x = 0 := by
  intro k
  induction k with
  | zero => intro x hx; exact h x hx
  | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      rcases lt_or_eq_of_le hx with hxlt | hxeq
      · have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 x := isOpen_Iio.mem_nhds hxlt
        have hev : (iteratedDeriv k g) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          filter_upwards [hmem] with y hy
          exact ih y (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const']
      · subst hxeq
        exact deriv_eq_zero_of_eqOn_Iic_zero ih

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- A `θ`-slice which vanishes identically has all its `D_θ`-iterates vanishing. -/
theorem DthIter_eq_zero_of_slice_zero {u : ℝ → ℝ → ℝ} {z : ℝ} (h : ∀ θ, u z θ = 0) (j : ℕ) :
    ∀ θ, Work.Spaces.DthIter j u z θ = 0 := by
  induction j with
  | zero => intro θ; exact h θ
  | succ j ih =>
      intro θ
      have hslice : (fun θ' => Work.Spaces.DthIter j u z θ') = fun _ => (0 : ℝ) := funext ih
      rw [Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [hslice, deriv_const']
      simp

/-- The `∂_z`-iterates of `D_θ^a(sin 2·)` are bounded by `Asin a · sin(2θ)`; for `c ≥ 1` they
vanish (the function is independent of `z`). -/
theorem abs_pzIter_DthIter_Sfun_le {c a : ℕ} (ha : a ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ|
      ≤ Work.FTS.H2.Asin a * Real.sin (2 * θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simpa using Work.FTS.H2.abs_DthIter_Sfun_le a ha z hθ
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hzero : Work.Spaces.pzIter (c' + 1) (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ = 0 := by
      rw [show Work.FTS.H2.Sfun = (fun _ θ' => Real.sin (2 * θ')) from rfl,
        Psi0Est.DthIter_theta_only]
      exact congrFun (congrFun (Psi0Est.pzIter_theta_only_succ
        (Work.Spaces.dthU^[a] (fun θ' => Real.sin (2 * θ'))) c') z) θ
    rw [hzero, abs_zero]
    exact mul_nonneg (le_of_lt (Work.FTS.H2.Asin_pos a)) hs

/-- The numerical constant of the `C(j-1,a)·Asin a` sum, for `j ≤ 4`. -/
theorem sum_choose_Asin_le (j : ℕ) (hj : j ≤ 4) :
    (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a) ≤ 1536 := by
  interval_cases j <;>
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Work.FTS.H2.Asin]

/-! ## The angular slots -/

/-- **The angular slot bound.**  For a flat datum, each of the angular slots of `WlInf α 4`
(`1 ≤ j`, `k + j ≤ 4`) is bounded by `10⁶ · K` on the closed domain. -/
theorem angular_slot_le {α K : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hzero : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0)
    (hF : Work.FTS.VocabO2.FlatW 4 f K) (hK : 0 ≤ K)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : k + j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ 1000000 * K := by
  intro z hz θ hθ
  have hKbig : (0 : ℝ) ≤ 1000000 * K := by positivity
  have hz0 : (0 : ℝ) ≤ z := hz
  rcases lt_or_eq_of_le hz0 with hzpos | hz0eq
  · by_cases hθI : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · -- interior: the `D_θ`-Leibniz expansion plus the flat bound
      have hsin_pos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθI.1]) (by linarith [hθI.2, Real.pi_pos])
      have hsin_nn : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin_pos
      have hden_pos : 0 < α + Real.sin (2 * θ) := by linarith
      have hleib := pzIter_DthIter_leibniz (k := k) hf hj hzpos hθI
      -- (1) the bound on the `D_z^k D_θ^j f`-part
      have hmain : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
          ≤ 1536 * K * Real.sin (2 * θ) := by
        have hsum : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
              * K * Real.sin (2 * θ) := by
          rw [hleib, Finset.mul_sum]
          calc |∑ a ∈ Finset.range j, (z + 1) ^ k * (((j - 1).choose a : ℝ) *
                (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                  Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                    z θ))|
              = |∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                      z θ))| := by
                congr 1
                refine Finset.sum_congr rfl fun a _ => ?_
                ring
            _ ≤ ∑ a ∈ Finset.range j, |((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                      z θ))| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                      z θ)| := by
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            _ ≤ ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  (Work.FTS.H2.Asin a * K * Real.sin (2 * θ)) := by
                refine Finset.sum_le_sum fun a ha => ?_
                refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
                have haj : a ≤ j - 1 := by rw [Finset.mem_range] at ha; omega
                have hA : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ|
                    ≤ Work.FTS.H2.Asin a * Real.sin (2 * θ) :=
                  abs_pzIter_DthIter_Sfun_le (c := 0) (a := a) (by omega) z hθ
                have hB : |(z + 1) ^ k * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
                  (hF z θ hzpos hθI.1 hθI.2).2 k (j - 1 - a) (by omega)
                calc |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                      Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                        (Work.Spaces.pth f)) z θ)|
                    = |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| *
                        |(z + 1) ^ k * Work.Spaces.pzIter k
                          (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| := by
                      rw [show (z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                              (Work.Spaces.pth f)) z θ)
                          = Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            ((z + 1) ^ k * Work.Spaces.pzIter k
                              (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ)
                          from by ring, abs_mul]
                  _ ≤ (Work.FTS.H2.Asin a * Real.sin (2 * θ)) * K :=
                      mul_le_mul hA hB (abs_nonneg _)
                        (mul_nonneg (le_of_lt (Work.FTS.H2.Asin_pos a)) hsin_nn)
                  _ = Work.FTS.H2.Asin a * K * Real.sin (2 * θ) := by ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
                  * (K * Real.sin (2 * θ)) := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun a _ => ?_
                ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
                  * K * Real.sin (2 * θ) := by ring
        have hj4 : j ≤ 4 := by omega
        calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
                * K * Real.sin (2 * θ) := hsum
          _ ≤ 1536 * K * Real.sin (2 * θ) := by
              refine mul_le_mul_of_nonneg_right ?_ hsin_nn
              exact mul_le_mul_of_nonneg_right (sum_choose_Asin_le j hj4) hK
      -- (2) multiply by the angular weight
      have hrpow : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
          = (Real.sin (2 * θ)) ^ (1 - α / 5) := by
        have h : (1 : ℝ) - α / 5 = 1 + -(α / 5) := by ring
        rw [h, Real.rpow_add hsin_pos, Real.rpow_one]
      calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
            rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsin_nn _),
              abs_of_nonneg (le_of_lt hden_pos)]
            ring
        _ ≤ (1536 * K * Real.sin (2 * θ))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
            refine mul_le_mul_of_nonneg_right hmain ?_
            exact div_nonneg (Real.rpow_nonneg hsin_nn _) (le_of_lt hden_pos)
        _ = 1536 * K * ((Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (-(α / 5))
              / (α + Real.sin (2 * θ))) := by ring
        _ = 1536 * K * ((Real.sin (2 * θ)) ^ (1 - α / 5)
              / (α + Real.sin (2 * θ))) := by rw [hrpow]
        _ ≤ 1536 * K * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sin_rpow_slack hα0 hα1 hsin_nn (Real.sin_le_one _)
        _ ≤ 1000000 * K := by nlinarith
    · -- `θ = 0` or `θ = π / 2`: the angular weight vanishes
      rw [Work.Spaces.Iθ] at hθ
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (le_antisymm hθ.2 (not_lt.mp fun hlt => hθI ⟨h, hlt⟩))
      have hsin0 : Real.sin (2 * θ) = 0 := by
        rcases hcases with h | h
        · rw [h]; norm_num
        · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hrpow : (Real.sin (2 * θ)) ^ (-(α / 5)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (by linarith : -(α / 5) ≠ 0)
      rw [hrpow, mul_zero, zero_div, abs_zero]
      exact hKbig
  · -- `z = 0`: the whole slice `z' ↦ D_θ^j f z' θ` vanishes on `(-∞,0]`
    have hz0'' : z = 0 := hz0eq.symm
    subst hz0''
    have hsd : Work.Spaces.pzIter k (Work.Spaces.DthIter j f) 0 θ = 0 := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv]
      refine iteratedDeriv_eq_zero_of_eqOn_Iic (g := fun z' => Work.Spaces.DthIter j f z' θ)
        ?_ k 0 le_rfl
      intro z' hz'
      exact DthIter_eq_zero_of_slice_zero (u := f) (fun θ' => hzero z' θ' (by
        intro hmem
        have h1 : (0 : ℝ) < z' := (Work.FTS.EllipticEst.mem_Q0.mp hmem).1
        linarith)) j θ
    rw [hsd]
    simp only [mul_zero, zero_mul, zero_div, abs_zero]
    exact hKbig

/-! ## The target -/

theorem wlInf_of_zeroOff : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn) (K : ℝ),
    0 < α → α ≤ 1 →
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
    Work.FTS.EllipticEst.SmoothOpen f →
    Work.FTS.VocabO2.FlatW 4 f K →
    Work.Spaces.WlInfMem α 4 f ∧ Work.Spaces.WlInf α 4 f ≤ C * K := by
  refine ⟨300000000, by norm_num, ?_⟩
  intro α f K hα0 hα1 hzero hf hF
  have hK : 0 ≤ K := by
    have h := (hF 1 1 (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three])).1 0 (by norm_num)
    exact le_trans (abs_nonneg _) h
  have hmem : Work.Spaces.WlInfMem α 4 f :=
    ⟨fun k hk => Work.Spaces.supFinite_of_pointwise
        (radial_slot_le hK hf hzero hF hk),
      fun j _ k _ hj1 hjk => Work.Spaces.supFinite_of_pointwise
        (angular_slot_le hα0 hα1 hf hzero hF hK hj1 hjk)⟩
  refine ⟨hmem, ?_⟩
  rw [Work.Spaces.WlInf]
  have h1 : (∑ k ∈ Finset.range 5,
      Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)) ≤ 5 * K := by
    calc _ ≤ ∑ _k ∈ Finset.range 5, K := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk4 : k ≤ 4 := by rw [Finset.mem_range] at hk; omega
          exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
            radial_slot_le hK hf hzero hF hk4 z hz θ hθ)
      _ = 5 * K := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have h2 : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
      if 1 ≤ j ∧ k + j ≤ 4 then
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) ≤ 25 * (1000000 * K) := by
    calc _ ≤ ∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, (1000000 * K) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
          split_ifs with hcond
          · exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
              angular_slot_le hα0 hα1 hf hzero hF hK hcond.1 hcond.2 z hz θ hθ)
          · exact mul_nonneg (by norm_num) hK
      _ = 25 * (1000000 * K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          ring
  linarith

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.tracePi4Five =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.N6Trans.SixRoute
  (trace_morrey wsq_dzIter_le_HkIntegrand_pi4 wsq_mixed_le_HkIntegrand_pi4
    half_le_sin_two_pi4 w_nonneg_pi4)

set_option maxHeartbeats 1600000

/-! ## The angular trace at `θ = π/4` of the level-six pure `D_z`-slots, orders up to `5`

`SixRoute.tracePi4` proves the *integrated* trace estimate at `θ = π/4` for the pure
`D_z`-slots of order `j ≤ 2`, and `T6Gen.tracePi4_six` provides the same statement at
level six for `j ≤ 5`.  Here we record the *pointwise-in-`z`* form of that estimate, for
every `z ∈ Iz` separately: this is the exact form in which the level-six transport
estimates consume the trace (they need a bound at a fixed radial point, not an average).

The mathematics is the one-dimensional Morrey inequality on the fixed subinterval
`J = [π/8, 3π/8] ∋ π/4`, on which `sin(2θ) ≥ 1/2`:
`h(π/4)² ≤ (2/|J|)∫_J h² + 2|J|∫_J (h')²`, applied to the angular slice
`h = fun θ => D_z^j g z θ`, followed by the pointwise slot comparisons
`w(z)²(D_z^j g)² ≤ HkIntegrand` and `w(z)²(∂_θD_z^j g)² ≤ 4·HkIntegrand`
(the latter through `∂_θ D_z^j g = mixed j 1 g / sin(2θ)`).  This is precisely the
`hkey` sub-argument of `tracePi4_six`, exposed without the final `z`-integration. -/

theorem tracePi4Five : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (g : ℝ → ℝ → ℝ) (j : ℕ),
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → j ≤ 5 →
      ∀ z ∈ Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2
          ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10, by norm_num, ?_⟩
  intro α hα g j hg hmem hj z hz
  have hα0 : 0 < α := hα.1
  have hj6 : j ≤ 6 := by omega
  -- the subinterval `J = [π/8, 3π/8]` around the trace angle `π/4`
  have hsubI : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hsubI' : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- `z = 0`: the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by
      rw [Work.Spaces.w]; norm_num
    rw [hw0]
    have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [h0, zero_mul]
    exact mul_nonneg (by norm_num)
      (integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 g 0 θ))
  · -- `z > 0`: the genuine estimate
    have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j g) := hg.DzIter j
    set h : ℝ → ℝ := fun θ => Work.Spaces.DzIter j g z θ with hh
    have hcont : ContinuousOn h (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
      (hsm.curry_θ hzpos).continuousOn.mono hsubI'
    have hdc : ContinuousOn (deriv h) (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
      refine ContinuousOn.congr ((hsm.pth.curry_θ hzpos).continuousOn.mono hsubI') ?_
      intro x hx
      have := Work.FTS.EllSol.WeakSlice.pth_DzIter_Q0 hg j hzpos (hsubI' hx)
      simpa only [hh, Work.Spaces.pth] using this
    have hd : ∀ x ∈ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8),
        HasDerivAt h (deriv h x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
      have := ((hsm.curry_θ hzpos).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hx')
      simpa only [hh] using this.hasDerivAt
    have hmor := trace_morrey (h := h) (a := Real.pi / 8) (x₀ := Real.pi / 4)
      (b := 3 * Real.pi / 8) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      hcont hdc hd
    have hbma : (3:ℝ) * Real.pi / 8 - Real.pi / 8 = Real.pi / 4 := by ring
    rw [hbma] at hmor
    -- the `L²`-block: `∫_J w² h² ≤ K`
    have hIntHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 g z θ)
        (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
      (hmem.1 z hz).mono_set hsubI
    have hI1 : (Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
          (h x) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ := by
      rw [← MeasureTheory.integral_const_mul]
      refine le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hIntHk
        (ae_restrict_of_forall_mem measurableSet_Icc
          (fun x hx => wsq_dzIter_le_HkIntegrand_pi4 hj6 (hsubI' hx)))) ?_
      exact MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
        (Eventually.of_forall (fun x => Work.Spaces.HkIntegrand_nonneg α 6 g z x))
        (Eventually.of_forall (fun x hx => hsubI hx))
    -- the `H¹`-block: `∫_J w² (h')² ≤ 4K`
    have hpt2 : ∀ x ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
        (Work.Spaces.w z) ^ 2 * (deriv h x) ^ 2
          ≤ 4 * Work.Spaces.HkIntegrand α 6 g z x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hsubI' hx
      have hsinpos : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx'.1])
          (by linarith [hx'.2, Real.pi_pos])
      have hder : deriv h x = Work.Spaces.DzIter j (Work.Spaces.pth g) z x := by
        have := Work.FTS.EllSol.WeakSlice.pth_DzIter_Q0 hg j hzpos hx'
        simpa only [hh, Work.Spaces.pth] using this
      have hmix : Work.Spaces.mixed j 1 g z x
          = Real.sin (2 * x) * Work.Spaces.DzIter j (Work.Spaces.pth g) z x :=
        (Work.FTS.H2.sin_mul_dzIter_pth g j z x).symm
      have hsin := half_le_sin_two_pi4 hx
      have hsinne : Real.sin (2 * x) ≠ 0 := ne_of_gt hsinpos
      have habs : |Work.Spaces.DzIter j (Work.Spaces.pth g) z x|
          = |Work.Spaces.mixed j 1 g z x| / Real.sin (2 * x) := by
        have h3 : Real.sin (2 * x)
            * |Work.Spaces.DzIter j (Work.Spaces.pth g) z x|
            = |Work.Spaces.mixed j 1 g z x| := by
          rw [← abs_of_pos hsinpos, ← abs_mul, ← hmix]
        rw [eq_div_iff hsinne, mul_comm]
        exact h3
      have hbound : |deriv h x| ≤ 2 * |Work.Spaces.mixed j 1 g z x| := by
        rw [hder, habs, div_le_iff₀ hsinpos]
        nlinarith [abs_nonneg (Work.Spaces.mixed j 1 g z x), hsin]
      have hd2 : (deriv h x) ^ 2 ≤ 4 * (Work.Spaces.mixed j 1 g z x) ^ 2 := by
        have h3 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
        rw [sq_abs, mul_pow, sq_abs] at h3
        nlinarith [h3]
      calc (Work.Spaces.w z) ^ 2 * (deriv h x) ^ 2
          ≤ (Work.Spaces.w z) ^ 2 * (4 * (Work.Spaces.mixed j 1 g z x) ^ 2) :=
            mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
        _ = 4 * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j 1 g z x) ^ 2) := by ring
        _ ≤ 4 * Work.Spaces.HkIntegrand α 6 g z x :=
            mul_le_mul_of_nonneg_left
              (wsq_mixed_le_HkIntegrand_pi4 hα0.le (by norm_num) (by omega) hx') (by norm_num)
    have hI2 : (Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
          (deriv h x) ^ 2)
        ≤ 4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
      rw [← MeasureTheory.integral_const_mul]
      have hInt4 : IntegrableOn (fun θ => 4 * Work.Spaces.HkIntegrand α 6 g z θ)
          (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := hIntHk.const_mul 4
      refine le_trans (MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))) hInt4
        (ae_restrict_of_forall_mem measurableSet_Icc hpt2)) ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 4)
      exact MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
        (Eventually.of_forall (fun x => Work.Spaces.HkIntegrand_nonneg α 6 g z x))
        (Eventually.of_forall (fun x hx => hsubI hx))
    set K : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ with hK
    have hKnn : 0 ≤ K := by
      rw [hK]; exact integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
    have hc1 : 2 / (Real.pi / 4) = 8 / Real.pi := by
      field_simp
      norm_num
    have hc2 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    have hcoef : 8 / Real.pi + 2 * Real.pi ≤ 10 := by
      have hp1 : (1:ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
      have hp4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
      have hprod : (Real.pi - 1) * (Real.pi - 4) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have heq : 8 / Real.pi + 2 * Real.pi = (8 + 2 * Real.pi * Real.pi) / Real.pi := by
        field_simp
      rw [heq, div_le_iff₀ Real.pi_pos]
      nlinarith [hprod]
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z (Real.pi / 4)) ^ 2
        = (Work.Spaces.w z) ^ 2 * (h (Real.pi / 4)) ^ 2 := by rw [hh]
      _ ≤ (Work.Spaces.w z) ^ 2 * ((2 / (Real.pi / 4)) * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (h x) ^ 2)
            + 2 * (Real.pi / 4) * (∫ x in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
              (deriv h x) ^ 2)) := mul_le_mul_of_nonneg_left hmor (sq_nonneg _)
      _ = (2 / (Real.pi / 4)) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (h x) ^ 2))
            + 2 * (Real.pi / 4) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (deriv h x) ^ 2)) := by ring
      _ = (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (h x) ^ 2))
            + (Real.pi / 2) * ((Work.Spaces.w z) ^ 2 * (∫ x in Set.Icc (Real.pi / 8)
              (3 * Real.pi / 8), (deriv h x) ^ 2)) := by rw [hc1, hc2]
      _ ≤ (8 / Real.pi) * K + (Real.pi / 2) * (4 * K) := by
          have h8 : 0 ≤ (8:ℝ) / Real.pi := by positivity
          have hp2 : 0 ≤ Real.pi / 2 := by positivity
          have hA := mul_le_mul_of_nonneg_left hI1 h8
          have hB := mul_le_mul_of_nonneg_left hI2 hp2
          rw [hK] at hA hB ⊢
          linarith
      _ = (8 / Real.pi + 2 * Real.pi) * K := by ring
      _ ≤ 10 * K := mul_le_mul_of_nonneg_right hcoef hKnn

end
end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N1ssPriced =====
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

set_option linter.unusedVariables false

/-- **Priced row 11**: the `ℋ⁴`-honesty and the `α²`-bound of the star piece `N₁^{**} = 2 · ℛ(Φ̃_*) · F_*`, with the constant *uniform* in `Cs` (linear loss in `1 + |Cs|`).

This is the priced form of `Work.FTS.NonlinRows.NRow11_of_wlInf` (row 11 in the open
vocabulary): that result states `∃ K, 0 < K ∧ ∀ …, Ctx … → HkMem α 4 (N1ss α Φs) ∧
Xn α (N1ss α Φs) ≤ K * α ^ 2`, but its `K` is opaque in `Cs`, which a consumer needing
`≤ C * (1 + |Cs|) ^ 4 * α ^ (-Cpow)` cannot use.  The proof of `NRow11_of_wlInf` already
*constructs* the explicit constant `1 + Cw * (10 ^ 6 * Ca) * max Cs 0` (`Cw` = constant of
`Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, `Ca` = `Work.FTS.Nonlinear.Pieces.RNPV2.Ca`), and
its body uses nothing but `0 < α`, `α ≤ 1`, `StarPkgo α Cs Φs` and the two `𝒲^{4,∞}` facts about
`Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs = ((z+1)/z) · ℛ(Φ̃_*)`, which `StarPkgo2.RW` supplies.  So
the proof is a copy of that proof with the interfaces (`N4Norm'`, `N4Extra'`, `Ctx`, `GalClass`,
`EllPkgGo`) removed and `C = 1 + Cw * (10 ^ 6 * Ca)`, using `max Cs 0 ≤ 1 + |Cs|`. -/
theorem N1ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1ss α Φs) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ C * (1 + |Cs|) * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  have hCa0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca :=
    le_of_lt Work.FTS.Nonlinear.Pieces.RNPV2.Ca_pos
  refine ⟨1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca), ?_, ?_⟩
  · have h1 : 0 ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) :=
      mul_nonneg hCw.le (mul_nonneg (by norm_num) hCa0)
    linarith
  · intro α hαIoc Cs Φs hsp
    obtain ⟨hα, hα1⟩ := hαIoc
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hsp.toStarPkgo
    have hW : Work.Spaces.WlInfMem α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) :=
      show Work.Spaces.WlInfMem α 4
        (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) from hsp.RW.1
    have hWb : Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) ≤ Cs * α :=
      show Work.Spaces.WlInf α 4
        (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ Cs * α from hsp.RW.2
    set WA : ℝ := Work.Spaces.WlInf α 4 (Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs) with hWA
    have hWA0 : 0 ≤ WA := by
      rw [hWA]
      exact Work.FTS.H2.sqm_WlInf_nonneg α 4 _ hW
    have hWAle : WA ≤ max Cs 0 * α := by
      rw [hWA]
      exact hWb.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    -- the smoothness of the radial factor and the weighted identity
    have hid := (Work.FTS.NonlinRows.smoothOpen_radA hα hα1 hs).2
    have hSOrad : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) :=
      (Work.FTS.NonlinRows.smoothOpen_radA hα hα1 hs).1
    have hmemG : Work.Spaces.WlInfMem α 4
        (fun z θ => (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ) := by
      rw [Work.FTS.Nonlinear.Pieces.RNPV2.weighted_eq_Rv]
      exact hW
    have hWAeq : Work.Spaces.WlInf α 4
        (fun z θ => (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)
        = WA := by
      rw [Work.FTS.Nonlinear.Pieces.RNPV2.weighted_eq_Rv, hWA]
    -- the two pointwise estimates for the radial factor
    have hrad : ∀ m ≤ 4, ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ m
            * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ|
          ≤ 200000 * WA := by
      intro m hm z hz θ hθ
      have h := Work.FTS.NonlinRows.WtoH_Radial_O hα hα1 hSOrad hmemG m hm z hz θ hθ
      rwa [hWAeq] at h
    have hmix : ∀ i l, 1 ≤ i → l + i ≤ 4 → ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
          ≤ 200000 * (WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
      intro i l hi hli z hz θ hθ
      have h := Work.FTS.NonlinRows.WtoH_Mixed_O hα hα1 hSOrad hmemG i l hi hli z hz θ hθ
      rwa [hWAeq] at h
    -- smoothness of the angular factor and of the piece
    have hSOang : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ) :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad
        (Work.FTS.Nonlinear.Pieces.RNPV2.smoothQuad_angF α)
    have hSOmul : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
          * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ) := by
      show ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
          * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) Work.FTS.EllipticEst.Q0
      refine ContDiffOn.congr (hSOang.mul hSOrad) ?_
      intro p hp
      obtain ⟨z, θ⟩ := p
      rfl
    have hSmoothN1ss : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.Nonlin.N1ss α Φs) := by
      rw [Work.FTS.Nonlinear.Pieces.RNPV2.N1ss_eq_angB_mul_radA]
      simpa only [Work.FTS.Nonlinear.Pieces.RNPV2.angB] using hSOmul
    -- the weight
    set W : ℝ := 10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * WA) with hWdef
    have hW0 : 0 ≤ W := by
      rw [hWdef]
      exact mul_nonneg (mul_nonneg (by norm_num) hCa0) (mul_nonneg hα.le hWA0)
    -- the pointwise hypotheses of `wtoHQ_of_pointwise_open`
    have hboundA : ∀ m ≤ 4, ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ m
            * Work.Spaces.pzIter m (Work.FTS.Nonlin.N1ss α Φs) z θ|
          ≤ 200000 * W := by
      intro m hm z hz θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hfac : Work.Spaces.pzIter m (Work.FTS.Nonlin.N1ss α Φs) z θ
          = Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
            * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ := by
        rw [Work.FTS.Nonlinear.Pieces.RNPV2.N1ss_eq_angB_mul_radA]
        simp only [Work.FTS.Nonlinear.Pieces.RNPV2.angB]
        rw [Work.FTS.Nonlinear.Pieces.RNPV2.pzIter_theta_mul m
          (Work.FTS.Nonlinear.Pieces.RNPV2.angF α)
          (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)]
      rw [hfac]
      have habs : |(1 + z) * Work.Spaces.w z * z ^ m
            * (Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ)|
          = |Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ| * |(1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ| := by
        rw [show (1 + z) * Work.Spaces.w z * z ^ m
              * (Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ)
            = Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ * ((1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ)
            by ring, abs_mul]
      rw [habs]
      have h1 := Work.FTS.Nonlinear.Pieces.RNPV2.angF_abs_le hα hα1 hθI
      have h2 := hrad m hm z hz θ hθ
      have h40 : (40 : ℝ) ≤ 10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca := by
        have h := Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_40
        nlinarith [hCa0]
      have harith : 40 * α * (200000 * WA) ≤ 200000 * W := by
        rw [hWdef]
        calc 40 * α * (200000 * WA)
            ≤ (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * α * (200000 * WA) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right h40 hα.le
          _ = 200000 * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * WA)) := by ring
      calc |Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ| * |(1 + z) * Work.Spaces.w z * z ^ m
              * Work.Spaces.pzIter m (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ|
          ≤ (40 * α) * (200000 * WA) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ 200000 * W := harith
    have hboundB : ∀ i l, 1 ≤ i → l + i ≤ 4 → ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (Work.FTS.Nonlin.N1ss α Φs)) z θ|
          ≤ 200000 * (W * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
      intro i l hi hli z hz θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hl4 : l ≤ 4 := by omega
      have hi4 : i ≤ 4 := by omega
      have hΦ0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ :=
        Work.FTS.Nonlinear.Pieces.RNPV2.Phi_nonneg α hα hθI
      have hρ : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ l := by
        have hw0 : 0 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w]; positivity
        exact mul_nonneg (mul_nonneg (by linarith) hw0) (pow_nonneg (le_of_lt hz) l)
      have hfun : Work.Spaces.DthIter i (Work.FTS.Nonlin.N1ss α Φs)
          = Work.Spaces.DthIter i (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
              * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ) := by
        rw [Work.FTS.Nonlinear.Pieces.RNPV2.N1ss_eq_angB_mul_radA]
        simp only [Work.FTS.Nonlinear.Pieces.RNPV2.angB]
      rw [hfun]
      -- the Leibniz bound, with the sum collapsed
      have hleib := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
        (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ)
        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) hSOang hSOrad z hz θ hθ
      have hsum : |Work.Spaces.pzIter l
            (Work.Spaces.DthIter i (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
              * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          ≤ 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|) :=
        hleib.trans (le_of_eq (by rw [Work.FTS.Nonlinear.Pieces.RNPV2.mixed_sum_collapse l i
          (Work.FTS.Nonlinear.Pieces.RNPV2.angF α)
          (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ]))
      -- the per-`a` estimate
      have hterm : ∀ a ∈ Finset.range (i + 1),
          |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
            * |Work.Spaces.pzIter l
                (Work.Spaces.DthIter (i - a)
                  (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
            * ((1 + z) * Work.Spaces.w z * z ^ l)
          ≤ 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
              * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
        intro a ha
        have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        have heq : |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              * |Work.Spaces.pzIter l
                  (Work.Spaces.DthIter (i - a)
                    (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
              * ((1 + z) * Work.Spaces.w z * z ^ l)
            = |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              * |(1 + z) * Work.Spaces.w z * z ^ l
                  * Work.Spaces.pzIter l
                      (Work.Spaces.DthIter (i - a)
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ| := by
          rw [abs_mul, abs_of_nonneg hρ]
          ring
        rw [heq]
        rcases lt_or_eq_of_le hai with hlt | heq2
        · -- `a < i`: the mixed estimate for the radial factor
          have h1 : 1 ≤ i - a := by omega
          have h2 : l + (i - a) ≤ 4 := by omega
          have hR := hmix (i - a) l h1 h2 z hz θ hθ
          have hD : |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α := by
            rcases eq_or_lt_of_le (Nat.zero_le a) with h0 | hpos
            · subst h0
              show |Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ|
                ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
              have hf := Work.FTS.Nonlinear.Pieces.RNPV2.angF_abs_le hα hα1 hθI
              have h40 : 40 * α ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α :=
                mul_le_mul_of_nonneg_right
                  Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_40 hα.le
              linarith
            · have ha4 : a ≤ 4 := by omega
              have hf := Work.FTS.Nonlinear.Pieces.RNPV2.dthU_angF_le hα hα1 a hpos ha4 hθ
              have h80 : 80 * Work.FTS.Nonlinear.Pieces.RNPV2.TBound * α
                  ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α :=
                mul_le_mul_of_nonneg_right
                  Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_80 hα.le
              linarith
          have hR0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α := mul_nonneg hCa0 hα.le
          calc |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |(1 + z) * Work.Spaces.w z * z ^ l
                    * Work.Spaces.pzIter l
                        (Work.Spaces.DthIter (i - a)
                          (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
              ≤ (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α)
                  * (200000 * (WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) :=
                mul_le_mul hD hR (abs_nonneg _) hR0
            _ = 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                  * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by ring
        · -- `a = i`: the radial estimate for the radial factor
          have hia : i - a = 0 := by omega
          rw [hia, Work.Spaces.DthIter_zero]
          have ha1 : 1 ≤ a := by omega
          have ha4 : a ≤ 4 := by omega
          have hR := hrad l hl4 z hz θ hθ
          have hD := Work.FTS.Nonlinear.Pieces.RNPV2.dthU_angF_weight_le hα hα1 a ha1 ha4 hθ
          have hD' : |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
              ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ := by
            have h40 : 40 * α * Work.FTS.Nonlinear.Pieces.RNPV2.TBound
                ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α := by
              have h := mul_le_mul_of_nonneg_right
                Work.FTS.Nonlinear.Pieces.RNPV2.Ca_ge_40TB hα.le
              linarith
            calc |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                ≤ 40 * α * Work.FTS.Nonlinear.Pieces.RNPV2.TBound
                    * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ := hD
              _ ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
                    * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ :=
                  mul_le_mul_of_nonneg_right h40 hΦ0
          have hR0 : 0 ≤ Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
              * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ :=
            mul_nonneg (mul_nonneg hCa0 hα.le) hΦ0
          calc |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |(1 + z) * Work.Spaces.w z * z ^ l
                    * Work.Spaces.pzIter l
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs) z θ|
              ≤ (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α
                    * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) * (200000 * WA) :=
                mul_le_mul hD' hR (abs_nonneg _) hR0
            _ = 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                  * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by ring
      -- assemble
      have hρ2 : |(1 + z) * Work.Spaces.w z * z ^ l
            * Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          = ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ| := by
        rw [abs_mul, abs_of_nonneg hρ]
      rw [hρ2]
      have hnn : 0 ≤ 200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
          * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg (mul_nonneg hCa0 hα.le) hWA0) hΦ0)
      have hi5 : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
        have : i + 1 ≤ 5 := by omega
        exact_mod_cast this
      have hstep1 : ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          ≤ ((1 + z) * Work.Spaces.w z * z ^ l) * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|)) :=
        mul_le_mul_of_nonneg_left hsum hρ
      have hstep2 : ((1 + z) * Work.Spaces.w z * z ^ l)
            * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|))
          = 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l)) := by
        have h1 : ((1 + z) * Work.Spaces.w z * z ^ l)
              * (257 * (∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                  * |Work.Spaces.pzIter l
                      (Work.Spaces.DthIter (i - a)
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|))
            = 257 * (((1 + z) * Work.Spaces.w z * z ^ l) * (∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                  * |Work.Spaces.pzIter l
                      (Work.Spaces.DthIter (i - a)
                        (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|)) := by
          ring
        rw [h1, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun a ha => by ring)
      have hstep3 : 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l))
          ≤ 257 * (∑ _a ∈ Finset.range (i + 1),
              200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      have hstep4 : 257 * (∑ _a ∈ Finset.range (i + 1),
            200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
              * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ))
          = 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
              * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hstep5 : 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
              * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)))
          ≤ 200000 * (W * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by
        rw [hWdef]
        calc 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
                * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)))
            = (257 * ((i + 1 : ℕ) : ℝ)) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
                * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := by ring
          _ ≤ (257 * 5) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              exact mul_le_mul_of_nonneg_left hi5 (by norm_num)
          _ ≤ 10 ^ 6 * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              norm_num
          _ = 200000 * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * WA)
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := by ring
      calc ((1 + z) * Work.Spaces.w z * z ^ l)
            * |Work.Spaces.pzIter l (Work.Spaces.DthIter i
                (fun z θ => Work.FTS.Nonlinear.Pieces.RNPV2.angF α θ
                  * Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs z θ)) z θ|
          ≤ ((1 + z) * Work.Spaces.w z * z ^ l) * (257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|)) := hstep1
        _ = 257 * (∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.dthU^[a] (Work.FTS.Nonlinear.Pieces.RNPV2.angF α) θ|
                * |Work.Spaces.pzIter l
                    (Work.Spaces.DthIter (i - a)
                      (Work.FTS.Nonlinear.Pieces.RNPV2.radA α Φs)) z θ|
                * ((1 + z) * Work.Spaces.w z * z ^ l)) := hstep2
        _ ≤ 257 * (∑ _a ∈ Finset.range (i + 1),
              200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca * α * WA
                * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ)) := hstep3
        _ = 257 * (((i + 1 : ℕ) : ℝ) * (200000 * (Work.FTS.Nonlinear.Pieces.RNPV2.Ca
              * α * WA * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ))) := hstep4
        _ ≤ 200000 * (W * Work.FTS.Nonlinear.Pieces.RNPV2.Phi α θ) := hstep5
    -- the transfer: `ℋ⁴`-honesty and the norm bound
    have hmain := hwto α (Work.FTS.Nonlin.N1ss α Φs) W hα hα1 hW0 hSmoothN1ss hboundA hboundB
    -- the final arithmetic
    have hWle : W ≤ 10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * (max Cs 0 * α)) := by
      rw [hWdef]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWAle hα.le)
        (mul_nonneg (by norm_num) hCa0)
    have hstepC : Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0
        ≤ (1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca)) * (1 + |Cs|) := by
      have hCwCa : 0 ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) :=
        mul_nonneg hCw.le (mul_nonneg (by norm_num) hCa0)
      have hmax : max Cs 0 ≤ 1 + |Cs| := by
        have h1 : max Cs 0 ≤ |Cs| := max_le (le_abs_self Cs) (abs_nonneg Cs)
        linarith
      have habs1 : 0 ≤ 1 + |Cs| := by positivity
      calc Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0
          ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * (1 + |Cs|) :=
            mul_le_mul_of_nonneg_left hmax hCwCa
        _ ≤ (1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca)) * (1 + |Cs|) :=
            mul_le_mul_of_nonneg_right (by linarith) habs1
    refine ⟨hmain.1, ?_⟩
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ Cw * W := hmain.2
      _ ≤ Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca * (α * (max Cs 0 * α))) :=
          mul_le_mul_of_nonneg_left hWle hCw.le
      _ = (Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca) * max Cs 0) * α ^ 2 := by ring
      _ ≤ (1 + Cw * (10 ^ 6 * Work.FTS.Nonlinear.Pieces.RNPV2.Ca)) * (1 + |Cs|) * α ^ 2 :=
          mul_le_mul_of_nonneg_right hstepC (sq_nonneg α)

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.L6Remainder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono)

/-! ## Two elementary weight identities -/



/-! ## The pointwise per-summand bounds -/


-- ## The blocked piece: the summands with `a₁ ≥ 1` and `a₁ + b₁ ≥ 5`
--
-- The pointwise bound for these summands (`l6_summand_le_pos`) is stated here in
-- `Submission/Work/FTS/StrongPersist/N6Trans/NOTES_slotT3Six_gap.md`; it is provable for
-- `1/30 ≤ α` (via `rpow_gamma_sub_le` and the two-piece split of `(α+σ)σ^{α/5}`), but for
-- `α < 1/30` the weight `sin(2θ)^{-(γ-α/5)}` carried by the pure-`D_z` factor
-- `D_z^{b-b₁+1}g` is intermediate between the pure-`D_z` slot weight `sin(2θ)^{-η}` and the
-- mixed slot weight `sin(2θ)^{-γ}`, and is dominated by neither: every two-slot
-- Cauchy–Schwarz/AM–GM estimate for those summands requires
-- `2(γ - α/5) ≤ η + γ`, i.e. `α ≥ 1/30`.  See the NOTES file for the routes tried.

end Work.FTS.StrongPersist.N6Trans
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.SupPkg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise sup-bound package for the level-6 `T2` slot

The `f`- and `g`-side pointwise bounds consumed by the per-term case analysis of
`Work.FTS.StrongPersist.N6Trans.SixAux.term_bound`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The pointwise data on `(f, g)` with a common bound `K` used by the per-term bound. -/
structure SupPkg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg : ℝ) : Prop where
  /-- pure `D_z`-derivatives of `f` of order `≤ 4`. -/
  fpure : ∀ b : ℕ, b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.DzIter b f z θ| ≤ Kf
  /-- pure `D_z`-derivatives of `g` of order `≤ 4`. -/
  gpure : ∀ b : ℕ, b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.DzIter b g z θ| ≤ Kg
  /-- mixed derivatives of `f` of order `≤ 4` with at least one angular derivative. -/
  fmix : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.mixed j i f z θ| ≤ Kf
  /-- mixed derivatives of `g` of order `≤ 4` with at least one angular derivative. -/
  gmix : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.mixed j i g z θ| ≤ Kg
  /-- the plain angular derivative of `f` (the `σ`-gain of `D_θ f = sin(2·)·∂_θ f`). -/
  pthf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth f z θ| ≤ Kf




end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SlotZ.Base =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SlotZ

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_eta_eq canonW_gam_eq
  canonW_mono)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## An a.e.-conversion for the angular interval -/

/-- A property holding at every interior angle holds a.e. on `Iθ`. -/
theorem ae_Iθ_of_forall_Ioo {P : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), P θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), P θ := by
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iθ : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-! ## Monotonicity of `canonW` in the exponent, on the open interval -/

theorem canonW_le_int {q q' z θ : ℝ} (hqq : q ≤ q')
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    canonW q z θ ≤ canonW q' z θ := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h : Real.sin (2 * θ) ^ (-q) ≤ Real.sin (2 * θ) ^ (-q') :=
    Real.rpow_le_rpow_of_exponent_ge (y := -q) (z := -q') hσ hσ1 (by linarith)
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-! ## The pointwise slot dominations on the open interval -/

theorem canonW_mul_z_le_int {α q : ℝ} {h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hq : q ≤ Work.Spaces.eta) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (j : ℕ) (hj : j ≤ 6) :
    canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have h1 : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθI]
    exact canonW_le_int hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (Work.Spaces.DzIter j h z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 h z θ j hj

theorem canonW_mul_mixed_le_int {α q : ℝ} {h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hqγ : q ≤ Work.Spaces.gam α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 6) :
    canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have h1 : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθI]
    exact canonW_le_int hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 h z θ i j hi hij

/-! ## The AM–GM pairing of two slots -/


/-! ## The three-factor slot bound: sup-bounded factor times two slots -/


/-! ## The three-factor slot bound with a sup-bounded factor -/



end Work.FTS.StrongPersist.N6Trans.T1SlotZ
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.RadialSlot6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

open MeasureTheory Set Filter
open scoped Topology Real

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The radial slots of `FlatW` on the closed rectangle, at arbitrary order

`VocabO2.FlatW l f K` is a statement about the **open** quadrant
`Q0 = (0,∞) × (0,π/2)`: it bounds `|(z+1)^k ∂_z^k f|` there (and the flat angular slots).
`RadialSlot6` extends its first family of slots (`k ≤ l`) to the closed rectangle
`Iz × Iθ = [0,∞) × [0,π/2]`, for **every** order `l`.

The extra points are harmless because `f` vanishes off `Q0`:

* for `θ = 0` or `θ = π/2` the whole `z`-slice of `f` is `0`, hence every iterated
  `z`-derivative vanishes on the slice (`pzIter_eq_zero_of_slice_zero`);
* for `z = 0` and `θ ∈ (0,π/2)` the slice `z' ↦ f z' θ` vanishes on `(-∞,0)`, so each iterated
  `z`-derivative vanishes at `0`: the derivative at the origin of a function vanishing on
  `(-∞,0]` is `0` (`deriv_eq_zero_of_eqOn_Iic_zero`).

This is the general-`l` form of `Work.FTS.PhiStar.radial_slot_le` (which fixes `l = 4`); the
argument never uses the value of `l`. -/

/-- A function which vanishes on the closed left half-line `(-∞,0]` has derivative `0` at the
origin.  (`deriv` is `0` at a point of non-differentiability, while at `0` differentiability
would force the one-sided difference quotients `-g 0 / h`, `h → 0⁻`, to have a finite limit,
hence `g 0 = 0` and derivative `0`.) -/
private lemma deriv_eq_zero_of_eqOn_Iic_zero {g : ℝ → ℝ} (h : ∀ x ≤ 0, g x = 0) :
    deriv g 0 = 0 := by
  have hc : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic 0) (0 : ℝ) :=
    hasDerivWithinAt_const 0 (Set.Iic 0) 0
  exact (hc.congr (fun y hy => h y hy) (h 0 le_rfl)).deriv_eq_zero
    (uniqueDiffWithinAt_Iic 0)

/-- If every `z`-slice of `f` at the angular value `θ` vanishes, then every iterated
`z`-derivative of `f` at `θ` vanishes. -/
private lemma pzIter_eq_zero_of_slice_zero {f : ℝ → ℝ → ℝ} {θ : ℝ} (hs : ∀ z, f z θ = 0) :
    ∀ j z, Work.Spaces.pzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact hs z
  | succ j ih =>
      intro z
      have hfun : (fun z' => Work.Spaces.pzIter j f z' θ) = fun _ => (0 : ℝ) := funext ih
      rw [Work.Spaces.pzIter_succ]
      show deriv (fun z' => Work.Spaces.pzIter j f z' θ) z = 0
      rw [hfun, deriv_const]

/-- If `f (·, θ)` vanishes on the open left half-line and at the origin, then all its iterated
`z`-derivatives vanish at every point of `(-∞,0]`. -/
private lemma pzIter_eq_zero_of_Iio_zero {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hs : ∀ z < 0, f z θ = 0) (h0 : f 0 θ = 0) :
    ∀ j z, z ≤ 0 → Work.Spaces.pzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero =>
      intro z hz
      rcases hz.eq_or_lt with h | h
      · rw [h]; simpa using h0
      · exact hs z h
  | succ j ih =>
      intro z hz
      have hφ : ∀ w ≤ 0, Work.Spaces.pzIter j f w θ = 0 := ih
      have hstep : deriv (fun z' => Work.Spaces.pzIter j f z' θ) z = 0 := by
        rcases hz.eq_or_lt with h | h
        · rw [h]
          exact deriv_eq_zero_of_eqOn_Iic_zero hφ
        · -- at `z < 0` the slice is identically zero on a neighbourhood of `z`
          have hev : (fun z' => Work.Spaces.pzIter j f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
            filter_upwards [isOpen_Iio.mem_nhds h] with z' hz'
            exact hφ z' hz'.le
          rw [hev.deriv_eq, deriv_const]
      rw [Work.Spaces.pzIter_succ]
      show deriv (fun z' => Work.Spaces.pzIter j f z' θ) z = 0
      exact hstep

/-- **`RadialSlot6`.**  For a function which is `C^∞` on the open quadrant and vanishes off it,
the radial slots `|(z+1)^k ∂_z^k f| ≤ K`, `k ≤ l`, of `FlatW l` extend from `Q0` to the closed
rectangle `[0,∞) × [0,π/2]`. -/
theorem RadialSlot6 {l : ℕ} {f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hzero : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0)
    (hF : Work.FTS.VocabO2.FlatW l f K) {k : ℕ} (hk : k ≤ l) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |(z + 1) ^ k * Work.Spaces.pzIter k f z θ| ≤ K := by
  intro z hz θ hθ
  have hz0 : 0 ≤ z := hz
  -- `(z', θ) ∈ Q0` forces `θ ∈ (0, π/2)`
  have hth : ∀ z' : ℝ, (z', θ) ∈ Work.FTS.EllipticEst.Q0 → 0 < θ ∧ θ < π / 2 :=
    fun z' hq => ⟨(Work.FTS.EllipticEst.mem_Q0.mp hq).2.1,
      (Work.FTS.EllipticEst.mem_Q0.mp hq).2.2⟩
  rcases hz0.eq_or_lt with hz_eq | hzpos
  · -- `z = 0`
    subst hz_eq
    by_cases hθint : θ ∈ Set.Ioo 0 (π / 2)
    · -- the slice `z' ↦ f z' θ` vanishes off the open quadrant, hence on `(-∞,0]`
      have hs : ∀ z' < 0, f z' θ = 0 := by
        intro z' hz'
        exact hzero z' θ (fun hq =>
          absurd (Work.FTS.EllipticEst.mem_Q0.mp hq).1 (not_lt.mpr hz'.le))
      have h0 : f 0 θ = 0 := hzero 0 θ (fun hq =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hq).1 (lt_irrefl 0))
      have hk0 := pzIter_eq_zero_of_Iio_zero hs h0 k 0 le_rfl
      rw [hk0, mul_zero, abs_zero]
      exact hK
    · -- the whole `θ`-slice of `f` vanishes
      have hs : ∀ z', f z' θ = 0 := fun z' => hzero z' θ (fun hq => hθint (hth z' hq))
      have hk0 := pzIter_eq_zero_of_slice_zero hs k 0
      rw [hk0, mul_zero, abs_zero]
      exact hK
  · by_cases hθint : θ ∈ Set.Ioo 0 (π / 2)
    · -- the open quadrant: this is exactly the `k`-th slot of `FlatW`
      exact (hF z θ hzpos hθint.1 hθint.2).1 k hk
    · -- the whole `θ`-slice of `f` vanishes
      have hs : ∀ z', f z' θ = 0 := fun z' => hzero z' θ (fun hq => hθint (hth z' hq))
      have hk0 := pzIter_eq_zero_of_slice_zero hs k z
      rw [hk0, mul_zero, abs_zero]
      exact hK

end Work.FTS.StrongPersist.SP6
end
