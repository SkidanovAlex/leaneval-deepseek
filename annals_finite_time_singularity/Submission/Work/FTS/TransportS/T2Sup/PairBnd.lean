import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WProdWin.mslot_le_winf
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.radS_DzdIter_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The sum of the squares of the binomial coefficients is at most `4^j`
(its value is `C(2j,j) ≤ 4^j`). -/
private theorem sum_choose_sq_le (j : ℕ) :
    (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 4 ^ j := by
  have hsum : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  have hcb : ∀ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by
    intro b hb
    have h1 := Finset.single_le_sum (f := fun i : ℕ => ((j.choose i : ℕ) : ℝ))
      (fun i _ => Nat.cast_nonneg _) hb
    rwa [hsum] at h1
  calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2)
      ≤ ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) * (2 : ℝ) ^ j := by
        refine Finset.sum_le_sum fun b hb => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left (hcb b hb) (Nat.cast_nonneg _)
    _ = (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) * (2 : ℝ) ^ j := by
        rw [Finset.sum_mul]
    _ = 4 ^ j := by
        rw [hsum, ← mul_pow]
        norm_num



end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.HkMemGam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The majorant -/

/-- The angular majorant of the separated summand `Γ(θ)·radS α f z`:
`sin(2θ)^{-η} + sin(2θ)^{2α/5-γ}`.  Its first term is the weight of the `D_z`-slots, its
second is what `Γ(θ)²·sin(2θ)^{-γ}` is bounded by. -/
def angMaj (α : ℝ) (θ : ℝ) : ℝ :=
  Work.FTS.Nonlinear.RadialProd.smE θ
    + (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)

/-- The radial density of the `n`-th level of `radS α f`:
`∑_{j≤n} (D_z^j (radS α f)(z))² w(z)²`. -/
def radMaj (α : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2

/-! ## The two separation identities, in the shape used below -/

private lemma dzIter_gam_rad (α : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
      = Work.Spaces.Gam α θ * Work.Elliptic.DzdIter i (radS α f) z :=
  Work.FTS.Nonlinear.Pieces.dzIter_ang_rad _ _ i z θ

private lemma mixed_gam_rad (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
      = Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
        * Work.Elliptic.DzdIter j (radS α f) z :=
  Work.FTS.Nonlinear.Pieces.mixed_ang_rad _ _ j i z θ

/-! ## The angular inequality `Γ² sin(2θ)^{-γ} ≤ sin(2θ)^{2α/5-γ}` -/

/-- `(sin(2θ)^{α/5})² = sin(2θ)^{2α/5}` for `0 ≤ sin(2θ)`. -/
private lemma sin_rpow_fifth_sq {θ : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) (α : ℝ) :
    ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (α / 5)) 2, ← Real.rpow_mul hs]
  congr 1
  push_cast
  ring

/-- `Γ(θ)² · sin(2θ)^{-γ(α)} ≤ sin(2θ)^{2α/5-γ(α)}` on `Iθ`. -/
private lemma gam_sq_mul_smG_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hGnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ
  have hsq : (Work.Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    have h2 : (Work.Spaces.Gam α θ) ^ 2 ≤ ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
      sq_le_sq' (by linarith [hGnn, Real.rpow_nonneg hs (α / 5)]) hGle
    rwa [sin_rpow_fifth_sq hs α] at h2
  have hne : 2 * α / 5 + -(Work.Spaces.gam α) ≠ 0 := by
    intro h
    have h1 : Work.Spaces.gam α = 2 * α / 5 := by linarith
    rw [Work.Spaces.gam] at h1
    nlinarith
  rw [show Work.FTS.Nonlinear.RadialProd.smG α θ
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
  calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs _)
    _ = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
        rw [show (2 : ℝ) * α / 5 - Work.Spaces.gam α
              = 2 * α / 5 + -(Work.Spaces.gam α) from by ring,
          Real.rpow_add' (x := Real.sin (2 * θ)) (y := 2 * α / 5)
            (z := -(Work.Spaces.gam α)) hs hne]

/-! ## The pointwise domination -/

/-- **Pointwise domination of the `ℋ^n`-integrand of a separated summand.**  For `n ≤ 3` and
`0 < α ≤ 1`, at every `(z,θ)` in the closed quadrant the integrand of `Γ(θ)·radS α f z` is
bounded by `4·10^10 · angMaj α θ · radMaj α f n z`.  (No hypothesis on `f`: the statement is
purely angular/radial bookkeeping.) -/
theorem HkIntegrand_gam_rad_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {n : ℕ} (hn : n ≤ 3) (f : ℝ → ℝ → ℝ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n
          (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
        ≤ 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z) := by
  intro z hz θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ
  have hsmGnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
  have hrmnn : 0 ≤ radMaj α f n z := by
    refine Finset.sum_nonneg fun j hj => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hGam2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by
    have h := (Work.Spaces.Gam_bounds α θ hα hθ).2
    nlinarith [(Work.Spaces.Gam_bounds α θ hα hθ).1]
  -- ### the pure (`D_z`-only) slots
  have hpure : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 4 * 10 ^ 10 * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z) := by
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              * ((Work.Elliptic.DzdIter i (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i _
      rw [dzIter_gam_rad α f i z θ,
        show (Work.Spaces.Gam α θ * Work.Elliptic.DzdIter i (radS α f) z
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = ((Work.Spaces.Gam α θ * Work.Elliptic.DzdIter i (radS α f) z)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          from by ring,
        Work.FTS.NonlinRows.AuxAngRad.light_sq_nn _ z θ hs]
      ring
    calc (∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.DzIter i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
            * radMaj α f n z := by
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, radMaj]
      _ ≤ 4 * 10 ^ 10 * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z) := by
          have h1 : (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              * radMaj α f n z
              ≤ Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z := by
            have h2 : (Work.Spaces.Gam α θ) ^ 2
                  * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z)
                ≤ 1 * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z) :=
              mul_le_mul_of_nonneg_right hGam2 (mul_nonneg hsmEnn hrmnn)
            linarith [h2]
          have h3 : (0 : ℝ) ≤ Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z :=
            mul_nonneg hsmEnn hrmnn
          nlinarith [h1, h3]
  -- ### the mixed slots
  have hmix : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 4 * 10 ^ 10
          * ((Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z) := by
    have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hc]
        have hi3 : i ≤ 3 := by
          have h1 : i ≤ n := le_trans (Nat.le_add_right i j) hc.2
          omega
        have hGbd : |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
            ≤ 100000 * Work.Spaces.Gam α θ :=
          Work.FTS.LocData.DthIter_Gam_abs_le i (by omega) α hα hα1 hθ
        have hDth2 : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
            ≤ 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by
          have h2 := sq_le_sq' (abs_le.mp hGbd).1 (abs_le.mp hGbd).2
          calc (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
              ≤ (100000 * Work.Spaces.Gam α θ) ^ 2 := h2
            _ = 10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2 := by ring
        have hgam := gam_sq_mul_smG_le α hα hα1 hθ
        rw [mixed_gam_rad α f j i z θ,
          show (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
                * Work.Elliptic.DzdIter j (radS α f) z * Work.Spaces.Wt α z θ) ^ 2
              = ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
                  * Work.Elliptic.DzdIter j (radS α f) z)
                  * Work.Spaces.Wt α z θ) ^ 2 from by ring,
          Work.FTS.NonlinRows.AuxAngRad.heavy_sq_nn α _ z θ hs]
        have hAY : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ
            ≤ 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
          have h1 : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ
              ≤ (10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2)
                  * Work.FTS.Nonlinear.RadialProd.smG α θ :=
            mul_le_mul_of_nonneg_right hDth2 hsmGnn
          have h2 : (10 ^ 10 * (Work.Spaces.Gam α θ) ^ 2)
                * Work.FTS.Nonlinear.RadialProd.smG α θ
              = 10 ^ 10 * ((Work.Spaces.Gam α θ) ^ 2
                  * Work.FTS.Nonlinear.RadialProd.smG α θ) := by ring
          rw [h2] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left hgam (by norm_num))
        have hcw : (0 : ℝ)
            ≤ (Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
        rw [show (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ
                * Work.Elliptic.DzdIter j (radS α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
            = ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ) from by ring]
        calc ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ)
            ≤ ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_left hAY hcw
          _ = 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
              * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
            ring
      · rw [if_neg hc]
        exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hs _))
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hsum2 : (∑ j ∈ Finset.range (n + 1),
        (10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
            * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2)))
        = 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z := by
      rw [← Finset.mul_sum, radMaj]
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n then
            (Work.Spaces.mixed j i (fun z θ => Work.Spaces.Gam α θ * radS α f z) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
              * ((Work.Elliptic.DzdIter j (radS α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = ((n + 1 : ℕ) : ℝ)
            * (10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
              * radMaj α f n z) := by
          rw [Finset.sum_const, hsum2, Finset.card_range, nsmul_eq_mul]
      _ ≤ 4 * 10 ^ 10
            * ((Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z) := by
          have hS : (0 : ℝ)
              ≤ 10 ^ 10 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)
                * radMaj α f n z :=
            mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hs _)) hrmnn
          have hn4 : ((n + 1 : ℕ) : ℝ) ≤ 4 := by
            have : n + 1 ≤ 4 := by omega
            exact_mod_cast this
          have h1 := mul_le_mul_of_nonneg_right hn4 hS
          linarith [h1]
  -- ### assembly
  rw [Work.Spaces.HkIntegrand]
  have hsum := add_le_add hpure hmix
  have hang : (4 : ℝ) * 10 ^ 10
        * (Work.FTS.Nonlinear.RadialProd.smE θ * radMaj α f n z)
      + 4 * 10 ^ 10
        * ((Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) * radMaj α f n z)
      = 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z) := by
    rw [angMaj]; ring
  linarith [hsum, hang]

/-! ## `ℋ^n`-membership of the separated summand -/

private lemma integrableOn_angMaj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => angMaj α θ) Work.Spaces.Iθ := by
  have h1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have h2 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
      Work.Spaces.Iθ := by
    refine (Work.Spaces.sin_two_rpow (2 * α / 5 - Work.Spaces.gam α) ?_ ?_).1
    · rw [Work.Spaces.gam]; linarith
    · rw [Work.Spaces.gam]; linarith
  refine (h1.add h2).congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Pi.add_apply, angMaj, Work.FTS.Nonlinear.RadialProd.smE]




end Work.FTS.CoercivityFix.Transfer.E2pkg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeCrux.AeVGlobalFin2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-
The *outer* `z`-integrability of the weighted slice functional of the mixed slot
`V = z ∂_z∂_θu`: the second hypothesis of `remov/AeI1PaperOfHonest` (through
`remov/AeI1PaperHolds`), and — up to the harmless factor `w z ^ 2 ≥ 1` — the second conjunct of
`Cores/AeStep2Aux/aeMixedAe_mem`.  With `1 ≤ w z` for `z > 0` the weighted statement implies the
unweighted one used there, so this is the form the `remov` route consumes.

## The route

`aeVGlobalFin2_of_mixIntS` (below) shows that the target is *exactly*
`IntegrableOn (Work.EllipticEst.Core.mixIntS u) Work.Spaces.Iz`, i.e. the outer `z`-integrability
of the mixed slot `D_z∂_θu = z∂_z∂_θu` of the datum.  That is reduced here to the paper's
two-dimensional Agmon interpolation in the flat, shifted, heavy-weight form
`Work.FTS.EllSol.HeavyFlat.FlatHeavy` (a *proved* node, see `Submission/Work/FTS/EllSol/Shift2Flat/`
and `.../HeavyFlat/`):

* `Work.FTS.EllSol.HeavyFlat.flatHeavy : FlatHeavy` — the flat, `b`-shifted, `σ_η`-weighted
  mixed-slot finiteness (the frequency/Plancherel/Fatou route of
  `Shift2Flat/NOTES_mixedSlot_route.md`);
* `Work.FTS.EllSol.HeavyFlat.omOfFlat : FlatHeavy → OmHeavy` — the decomposition
  `Ω(t) = Σ_{k<5} C(4,k) e^{2 b_k t}`;
* `mixIntS_integrableOn_Ioi` (in `AeVLib.Main`) — the pull-back `g(t,θ) = u(e^t,θ)` of the datum,
  the three diagonal slots coming from `AeData` (`HkMem α 0 G` is not needed: only
  `HkMem α 0 (z∂_zu)`, `HkMem α 0 (z²∂_z²u)`, `HkMem α 0 (∂_θ²u)` enter, and `D_z(D_zu)` is
  dominated by the first and the second), the reverse change of variables `z = e^t`, and
  `∫⁻ ofReal (mixIntS u) < ⊤`.

The module `AeVLib.Meas`/`Slots`/`Pullback`/`Main` contain the whole measure-theoretic and
coordinate layer of that reduction; `AeCoreSlots` supplies the remaining `AeData`-side slots.
-/

/-- The target is exactly `IntegrableOn (mixIntS u) Iz`: the two sets `Iθ = Icc 0 (π/2)` and
`Ioo 0 (π/2)` differ by two points, so the `θ`-integrals agree at every `z` (the Bochner value
is a function of the restricted measure, junk value `0` included), and `Ioi 0` differs from
`Iz = Ici 0` by one point. -/
theorem aeVGlobalFin2_of_mixIntS {u : ℝ → ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.mixIntS u) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi (0 : ℝ)) := by
  -- `Icc 0 (π/2)` and `Ioo 0 (π/2)` differ by two points
  have hIcc : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume]
      Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  -- the two functions agree at every `z`
  have hpoint : Work.EllipticEst.Core.mixIntS u
      = fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    funext z
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
        (Work.Spaces.Dz (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    congr 1
    exact MeasureTheory.setIntegral_congr_set hIcc
  -- `volume.restrict (Ici 0) = volume.restrict (Ioi 0)`
  have hIci_meas : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ici (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
  have h1 : MeasureTheory.Integrable (Work.EllipticEst.Core.mixIntS u)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h2 : MeasureTheory.Integrable (Work.EllipticEst.Core.mixIntS u)
        (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := h
    rwa [← hIci_meas]
  rw [hpoint] at h1
  exact h1

/-- **The target.**  The paper's two-dimensional Agmon interpolation is available in flat form as
the *proved* node `HeavyFlat.flatHeavy : FlatHeavy`, and `HeavyFlat.omOfFlat` turns it into the
`Ω`-weighted form `OmHeavy`.  Feeding that into the proved `mixIntS_integrableOn_Ioi` gives
`IntegrableOn (mixIntS u) (Ioi 0)`, and `aeVGlobalFin2_of_mixIntS` rewrites the target as exactly
that statement. -/
theorem AeVGlobalFin2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi (0 : ℝ)) := by
  have hOm : Work.FTS.EllSol.HeavyFlat.OmHeavy :=
    Work.FTS.EllSol.HeavyFlat.omOfFlat Work.FTS.EllSol.HeavyFlat.flatHeavy
  have hIoi := mixIntS_integrableOn_Ioi hOm h hU
  have hIz : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.mixIntS u) Work.Spaces.Iz := by
    have h' : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    have h2 : MeasureTheory.Integrable (Work.EllipticEst.Core.mixIntS u)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [← h']
      exact hIoi
    exact h2
  exact aeVGlobalFin2_of_mixIntS hIz

end Work.FTS.EllipticEst.AeCrux
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields

open Work.FTS.Nonlin (RegQ GalClass CoerAdm UnifIP GalBasis Xn PsiCan)
open Work.FTS.Galerkin (Fn Fam slice galFun galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif profileFam prof Slab dynLin dynRHS famOf gdot EquicontSpace EquicontTau)
open Work.FTS.VocabO (EllPkgGo)
open Work.FTS.VocabO2 (StarPkgo2)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The energy ball `EBall n r = {c | Σₖ cₖ² ≤ r²}` -/

/-- The **energy ball** of the corrected compactness inputs: the set of coefficient vectors whose
ℓ²-energy is at most `r²`.  It contains every Galerkin trajectory of the a-priori chapter
(`IsGalFam` gives `Σₖ cₖ² ≤ R²`), and it is the correct domain of the projected vector field: on it
the `ℋ⁴`-size of the profile is `≤ r/√clo`, uniformly in the truncation `n`. -/
def EBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {c | ∑ k, c k ^ 2 ≤ r ^ 2}

@[simp] theorem mem_EBall {n : ℕ} {r : ℝ} {c : Fin n → ℝ} :
    c ∈ EBall n r ↔ ∑ k, c k ^ 2 ≤ r ^ 2 := Iff.rfl







/-! ## The corrected field lemmas (statements)

These are the corrected forms of the fields of `Work.FTS.Galerkin.DynInputs`.  The statements of
`hField_lip'` (with the energy ball `EBall n (2 * R)` in place of `Metric.closedBall 0 (2 * R)`)
are the ones frozen in `Submission/Work/FTS/FTS_ELL_GALERKIN_STMTS.lean.txt`, namespace
`Work.FTS.ScratchC46`; they are copied here verbatim (modulo the namespace). -/

/-- **The corrected Lipschitz field**: the projected vector field is Lipschitz on the *energy* ball
of radius `2R`, with a truncation-dependent constant. -/
def hField_lip' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ) (EBall n (2 * R))

/-- **The corrected bound field**: the projected vector field is bounded on the *energy* ball of
radius `2R`, with a truncation-dependent constant. -/
def hField_bound' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (L : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → ∀ c : Fin n → ℝ, c ∈ EBall n (2 * R) →
    ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n

/-- **The fake-time continuity field**: `τ ↦ galField … τ c` is continuous on `[0,∞)` on the energy
ball.  Unlike the delivered version this is *unconditional* — the projected field does not depend on
`τ` at all (`FieldBasic.lean`), so continuity is continuity of a constant. -/
def hField_cont' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ EBall n (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)

/-- **Uniform spatial equicontinuity of the Galerkin profiles** (the `(z,θ)`-half of the corrected
compactness input), for every Galerkin family in the a-priori ball. -/
def hProfileSpace' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → EquicontSpace (profileFam φ c)

/-- **Uniform equicontinuity in the fake time of the Galerkin profiles** (the `τ`-half of the
corrected compactness input), for every Galerkin family in the a-priori ball.  Its proof (the *tail
route*) is in `BesselTail.lean` + `ProfileTau.lean`. -/
def hProfileTau' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → EquicontTau (profileFam φ c)

/-! ## The dynamic right-hand side as a function of the profile -/

/-- The **dynamic right-hand side of the projected Galerkin equation, as a function of the
profile**: with `g` the profile of the truncation and `Φs + EllSol g` its stream function,
`Fr α Φs EllSol g` is the right-hand side `-𝓛_Γ^T(g) + gRHS(μ̄,λ,F_*,Φ,g)` of the fake-time
equation.  It is the same object for every truncation `n` and every fake time `τ`
(`FieldBasic.galRHS_eq_Fr`), which is what makes the projected field `τ`-independent. -/
def Fr (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g : Fn) : Fn :=
  dynLin α (famOf fun _ => g) 0
    + dynRHS α (PsiCan Φs EllSol (famOf fun _ => g)) (famOf fun _ => g) 0

/-- The size `|g|_{ℋ⁵}` — the higher norm that the field bounds of this chapter consume; see
`RHSData` below for why `Xn` (order 4) is not enough. -/
abbrev Xn5 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 5 g

/-- **The size and Lipschitz package of the dynamic right-hand side on the smallness ball.**

This is the single analytic input of the chapter that is not supplied by `FTS/GalBasis` or
`FTS/EllSol`: `Fr` is a polynomial of degree `≤ 3` in the profile (with coefficients built from
`Γ`, `K`, `F_*`, `Φ_*` and the linear operator `EllSol`), and on the smallness ball
`{|g|_{ℋ⁴} ≤ α^{7/4}}` it is

* bounded in the `ℋ⁴` metric by a polynomial in the **`ℋ⁵`-size** of `g`, and
* Lipschitz in the `ℋ⁴` metric, with a Lipschitz constant controlled by the `ℋ⁵`-sizes,

with constants independent of `α` in the range of validity.

## Why the `ℋ⁵`-dependence is unavoidable (and the constant form `Cb` is false)

Three of the pieces of `N₀` and six of the pieces of `N` are bounded in the N4 row bundle
(`Work.FTS.NonlinRows.NData2`) only in **pairing** form `|IP (Nᵢ) g| ≤ …` — rows 4, 6, 7 of
`N0Rows` and rows 12, 14, 16, 18, 20, 22 of `NRows`
(`N04bF = (3/2α) sin 2θ L₁₂(g) ∂_θg`, `N05bF = -c₂m L₁₂(g) D_zg`, `N06F = -c₂m L₁₂(F_*) D_zg`, and
the six `Nᵢ^{g·}` pieces carrying `U(Φ̃)·∂_θF` and `V(Φ̃)·D_zF` with `F = F_* + g`).  The reason is
that those pieces contain `D_z g` or `∂_θg`, whose **`ℋ⁴`-norm is not controlled by `|g|_{ℋ⁴}`**:

  `HkSq α 4 (D_z g) ≤ HkSq α 5 g`  but **not**  `≤ C·HkSq α 4 g`,

because `HkIntegrand α 4 (D_zg)` is a sub-sum of `HkIntegrand α 5 g` (the slots `D_z^{i+1}g`,
`D_z^{j+1}D_θ^ig` with `i+j+1 ≤ 5`), so the constant `Cb` in the form
`∀ g, |g|_{ℋ⁴} ≤ α^{7/4} → |Fr g|_{ℋ⁴} ≤ Cb` is **false** for a general `GalBasis`: the ball
`{|g|_{ℋ⁴} ≤ α^{7/4}}` is not bounded in `ℋ⁵`.  (The failed constant form is exactly the same kind
of defect as the delivered `hField_lip`/`hField_bound` on the sup-norm ball, recorded in the
design's "New defects".)

The finite constant therefore has to be produced from the *basis*: for `c ∈ EBall n (2R)` one has
`|galFun φ c|_{ℋ⁵} ≤ (Σₖcₖ²)^{1/2}·(Σ_{k<n}|φ k|_{ℋ⁵}²)^{1/2}`, which is finite for every
truncation `n` and is the `M5`-hypothesis carried by `FieldBnd.hField_bound'_holds`,
`FieldLip.hField_lip'_holds` and `ProfileTau.hProfileTau'_holds`.  (For the `τ`-field the
`ℋ⁵`-bound has to be **uniform in `n`**, which is a property of the basis, not of `GalBasis` as an
abstract class; see `NOTES_RHSData.md`.)

Both clauses are stated *on the smallness ball*, which is exactly what the smallness hypothesis
`α ≤ (2C₀)⁻⁴` of the field lemmas guarantees for every `c ∈ EBall n (2R)`
(`BallBound.HkNorm_le_alpha_rpow_of_mem_EBall`).  Without that hypothesis the Lipschitz constant
degenerates in `α → 0`: the modulation constant `μ` may leave `|μ| ≤ 1/2` and the coefficient
`μ + λ + μλ = -μ` of `N_*` blows up — the defect recorded in the design under "New defects".

## The exact form of the two clauses (corrected 2026-10-09)

Both clauses are stated for profiles of the **Galerkin class** `GalClass α` (which supplies
`HkMem α 5`, the honesty needed to compare the `ℋ⁴`- and `ℋ⁵`-sizes, `L₁₂ g 0 = 0` and the
vanishing of the profile at `z = 0`), and for `α ≤ 1` (used only for `α^{7/4} ≤ α`-type
arithmetic):

  `bdd : ∃ Cb ≥ 0, ∀ g, GalClass α g → α ≤ 1 → Xn α g ≤ α^{7/4} → Xn α (Fr g) ≤ Cb(1 + Xn5 g)³`,
  `lip : ∃ Cl ≥ 0, ∀ g g', GalClass α g → GalClass α g' → GalClass α (g - g') → α ≤ 1 →
           Xn α g, Xn α g' ≤ α^{7/4} →
           Xn α (Fr g - Fr g') ≤ Cl(1 + Xn5 g + Xn5 g')² Xn5 α (g - g')`.

The right-hand side of `lip` carries the `ℋ⁵`-size of the **difference** — this is essential and
is *not* a defect: `Fr` contains the unbounded operators `D_z = z∂_z` and `D_θ`, and
`HkSq α 4 (D_z h) ≤ HkSq α 5 h` is all that is available (`Norm/Basic.lean`); an `ℋ⁴`-difference
bound `|Fr g - Fr g'|_{ℋ⁴} ≤ C|g-g'|_{ℋ⁴}` is **false** (take `g' = 0` and `g = εψ` with `ψ` a
narrow bump in `z`: the `D_z`-slot of `g - g'` is not controlled by its `ℋ⁴`-size).  In the
application both `g`, `g'` and `g - g'` are Galerkin combinations in the ball — `g = galFun φ c`,
`g' = galFun φ c'` with `c, c' ∈ EBall n (2R)`, so `g - g' = galFun φ (c - c')` — and
`Xn5 α (galFun φ (c-c')) ≤ √(n/clo)·‖c - c'‖` is what produces the truncation-dependent Lipschitz
constant `K n` of `hField_lip'`.

**The constants `Cb`, `Cl` may depend on `α` and on the fixed data `Φs`, `EllSol`** (they are
existentials inside `RHSData α Φs EllSol`, which is instantiated at a fixed `α`), but *not* on
`g`, `g'`; the factorials in `Xn5` are the only genuine uniformity in the profile.  In particular
the `α^{-1}`-losses of the two `(3/(2α))·L₁₂(·)` pieces and of the modulation gradient are
absorbed by `Cl`. -/
structure RHSData (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) : Prop where
  /-- the `ℋ⁴`-size of the right-hand side on the smallness ball, in terms of its `ℋ⁵`-size -/
  bdd : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ g : Fn, GalClass α g → α ≤ 1 → Xn α g ≤ α ^ (7 / 4 : ℝ) →
    Xn α (Fr α Φs EllSol g) ≤ Cb * (1 + Xn5 α g) ^ 3
  /-- the Lipschitz continuity of the right-hand side in the `ℋ⁴` metric, on the smallness ball,
  with a Lipschitz constant controlled by the two `ℋ⁵`-sizes -/
  lip : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ g g' : Fn, GalClass α g → GalClass α g' →
    GalClass α (fun z θ => g z θ - g' z θ) → α ≤ 1 →
    Xn α g ≤ α ^ (7 / 4 : ℝ) → Xn α g' ≤ α ^ (7 / 4 : ℝ) →
    Xn α (fun z θ => Fr α Φs EllSol g z θ - Fr α Φs EllSol g' z θ)
      ≤ Cl * (1 + Xn5 α g + Xn5 α g') ^ 2 * Xn5 α (fun z θ => g z θ - g' z θ)

/-! ## The bundle of the five corrected fields -/

/-- **The five corrected compactness fields of the Galerkin existence theorem**, bundled in the
shape of `Work.FTS.Galerkin.DynInputs` (fields `L`, `hL`, `K`, `hK`, `hField_lip`,
`hField_bound`, `hField_cont`, `hProfileSpace`, `hProfileTau`), so that a caller can use this
structure as the `N4/N5` block of the a-priori bundle. -/
structure CorrectedFields (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) where
  /-- the bound constant of the projected field -/
  L : ℕ → ℝ
  /-- the Lipschitz constant of the projected field -/
  K : ℕ → ℝ
  /-- positivity of the bound constant (the shape consumed by the ODE layer) -/
  hL : ∀ n : ℕ, 0 < L n
  /-- nonnegativity of the Lipschitz constant -/
  hK : ∀ n : ℕ, 0 ≤ K n
  hField_lip : hField_lip' α IP φ Φs EllSol R K hK
  hField_bound : hField_bound' α IP φ Φs EllSol R L
  hField_cont : hField_cont' α IP φ Φs EllSol R
  hProfileSpace : hProfileSpace' α IP φ Φs EllSol R
  hProfileTau : hProfileTau' α IP φ Φs EllSol R

/-! ## The Hölder modulus of the `ℋ²`-class (the paper's Corollary `Linf_H2`) -/


/-! ## The ideal generated by the two analytic inputs -/

end Work.FTS.GalFields
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `L_Γ^T` is `C^∞` on the open quadrant

The transport-modified linearized operator of the paper is

`LGammaT α g = 𝓛 g − (2zΓ(θ)/(c(1+z)²))·L₁₂(g)(z)
                − 3 sin(2θ)∂_θg/(1+z)
                + (Γ(θ)/c)(2z²/(1+z)³)·L₁₂(Transport g)(0)`.

Two observations make this `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`:

* the second and fourth terms involve the *radial* object `L₁₂(·)` — of `g`, and the *constant*
  value `L₁₂(Transport g)(0)` — times a rational factor of `z` and the angular profile `Γ`; the
  hypothesis `SmoothOpen (L₁₂ g)` handles the first and the second is constant, so no
  integrability or further nonlocal information is used;
* every remaining division is by `(1+z)^k` (`k = 1,2,3`), which does not vanish for `z > 0`; the
  division by `c α` is pulled out as a *constant* multiplier `1/c α`, so `c α ≠ 0` is not needed.

The statement follows from the pointwise identity `LGammaT_eq_Nice` and the closure of
`SmoothOpen` under sums, differences, products and multiplication by constants.
-/

/-- **`Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on the open quadrant.** -/
private theorem smoothOpen_Gam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Work.Spaces.Gam α θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.FTS.EllipticEst.Q0
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
    ((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin p.2 * Real.cos p.2 ^ 2 ≠ 0 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hs : 0 < Real.sin p.2 :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    positivity
  simpa only [Work.Spaces.Gam] using hbase.rpow_const_of_ne hpos

/-- A constant function is `SmoothOpen`. -/
private theorem smoothOpen_const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (_ : ℝ) => c) :=
  Work.FTS.NonlinRows.smoothOpen_radial (r := fun _ => c) (fun _n => contDiffOn_const)

/-- The radial factor `z ↦ 1/(1+z)` (positive denominator on `(0,∞)`). -/
private theorem smoothOpen_inv_one_add :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 1 / (1 + z)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial (r := fun z => 1 / (1 + z)) (fun _n => ?_)
  exact (contDiffOn_const (c := (1 : ℝ))).div
    ((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id)
    (fun z hz => by
      have hz' : (0 : ℝ) < z := hz
      positivity)

/-- The radial factor `z ↦ 2z/(1+z)²`. -/
private theorem smoothOpen_zdz :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 2 * z * (1 / (1 + z) ^ 2)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z => 2 * z * (1 / (1 + z) ^ 2)) (fun _n => ?_)
  exact ((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_id).mul
    ((contDiffOn_const (c := (1 : ℝ))).div
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 2)
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        exact pow_ne_zero 2 (by positivity)))

/-- The radial factor `z ↦ 2z²/(1+z)³`. -/
private theorem smoothOpen_zsqdz :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 2 * z ^ 2 * (1 / (1 + z) ^ 3)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z => 2 * z ^ 2 * (1 / (1 + z) ^ 3)) (fun _n => ?_)
  exact ((contDiffOn_const (c := (2 : ℝ))).mul (contDiffOn_id.pow 2)).mul
    ((contDiffOn_const (c := (1 : ℝ))).div
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 3)
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        exact pow_ne_zero 3 (by positivity)))

/-- The normalised form of `LGammaT α g`: the constants `1/c α` are pulled in front of explicit
smooth factors and every division is by a power of `1+z`.  It is `C^∞` on the open quadrant as
soon as `g` and `z ↦ L₁₂(g)(z)` are (see `smoothOpen_Nice`), and it agrees with `LGammaT α g`
pointwise (`LGammaT_eq_Nice`). -/
private noncomputable def Nice (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (g z θ + Work.Spaces.Dz g z θ - 2 * (g z θ * (1 / (1 + z))))
      - (1 / Work.Spaces.c α)
          * ((2 * z * (1 / (1 + z) ^ 2)) * (Work.Spaces.Gam α θ * Work.Construction.L12 g z))
      - (3 * (Work.Spaces.Dth g z θ * (1 / (1 + z))))
      + (1 / Work.Spaces.c α)
          * (Work.Spaces.Gam α θ
            * ((2 * z ^ 2 * (1 / (1 + z) ^ 3))
              * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))

/-- **The pointwise identity**: `LGammaT α g` equals its normalised form `Nice α g`. -/
private theorem LGammaT_eq_Nice (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.LGammaT α g z θ = Nice α g z θ := by
  simp only [Nice, Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.Construction.L12, div_eq_mul_inv, mul_inv]
  ring_nf

/-- **`Nice α g` is `C^∞` on the open quadrant**, from the two hypotheses on `g`. -/
private theorem smoothOpen_Nice {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hL12 : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (Nice α g) := by
  have hGam := smoothOpen_Gam α
  have hz_inv := smoothOpen_inv_one_add
  have hz_sq := smoothOpen_zdz
  have hz_cu := smoothOpen_zsqdz
  have hC := smoothOpen_const (Work.Coercivity.L12f (Work.Coercivity.Transport g) 0)
  have hP1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => g z θ + Work.Spaces.Dz g z θ - 2 * (g z θ * (1 / (1 + z)))) :=
    Work.FTS.NonlinRows.smoothOpen_sub
      (Work.FTS.NonlinRows.smoothOpen_add hg (Work.FTS.EllipticEst.SmoothOpen.Dz hg))
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2
        (Work.FTS.NonlinRows.smoothOpen_mul hg hz_inv))
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / Work.Spaces.c α) * ((2 * z * (1 / (1 + z) ^ 2))
        * (Work.Spaces.Gam α θ * Work.Construction.L12 g z))) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (1 / Work.Spaces.c α)
      (Work.FTS.NonlinRows.smoothOpen_mul hz_sq
        (Work.FTS.NonlinRows.smoothOpen_mul hGam hL12))
  have hT : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 3 * (Work.Spaces.Dth g z θ * (1 / (1 + z)))) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul 3
      (Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.EllipticEst.SmoothOpen.Dth hg) hz_inv)
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / Work.Spaces.c α) * (Work.Spaces.Gam α θ
        * ((2 * z ^ 2 * (1 / (1 + z) ^ 3))
          * Work.Coercivity.L12f (Work.Coercivity.Transport g) 0))) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (1 / Work.Spaces.c α)
      (Work.FTS.NonlinRows.smoothOpen_mul hGam (Work.FTS.NonlinRows.smoothOpen_mul hz_cu hC))
  unfold Nice
  exact Work.FTS.NonlinRows.smoothOpen_add
    (Work.FTS.NonlinRows.smoothOpen_sub (Work.FTS.NonlinRows.smoothOpen_sub hP1 hA) hT) hB

theorem smoothOpen_LGammaT_of_L12 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hL12 : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α g) := by
  have hNice : Work.FTS.EllipticEst.SmoothOpen (Nice α g) := smoothOpen_Nice hL12 hg
  refine ContDiffOn.congr hNice ?_
  intro p _hp
  obtain ⟨z, θ⟩ := p
  exact LGammaT_eq_Nice α g z θ

end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS.NonlinRows.AuxFK.smoothOpen_FK_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.AuxFK

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## `FK g` is `C^∞` on the open quadrant

The angular moment `FK g z = ∫_θ K(θ)·g z θ dθ` is, on `z > 0`, the derivative of the radial
function `L₁₂(g)`:

  `∂_z L₁₂(g)(z) = - FK g z / z`   (`Work.FTS.OpenPkg.deriv_L12_eq`),

i.e. `FK g z = - z · ∂_z L₁₂(g)(z)`.  The hypothesis that `Vop (PhiTg α g Φg)` is `SmoothOpen`
gives (`Work.FTS.NonlinRows.smoothOpen_L12_radial`, via the identity
`Vop (PhiTil α g Φg) = Vop Φg - (1/(2α)) c₂(θ) L₁₂(g)(z)` and the non-degeneracy
`c₂(π/4) = -1/2`) that `z ↦ L₁₂(g)(z)` is `C^∞` on `(0,∞)`.  Being `C^∞` on `(0,∞)`, that
function is `C^{n+1}` for every `n`, hence its `deriv` is `C^n`, so `z ↦ -z·∂_z L₁₂(g)(z)` is
`C^∞` on `(0,∞)`, and `smoothOpen_radial` promotes it to the open quadrant. -/


end Work.FTS.NonlinRows.AuxFK
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow15T2Aux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two factors of row 15 -/

/-- The **weighted star coefficient** of row 15: `((z+1)/z)·(𝒰(Φ̃_*)/sin 2θ)`.  Its
`𝒲^{4,∞}`-membership (with the bound `≤ Cs·α`) is the field `UszW` of
`Work.FTS.VocabO2.StarPkgo2`. -/
def G15 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z
    * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)

/-- The **angular coefficient** of row 15: `C15 α θ = -2·(α/c(α))·D_θΓ(θ)`. -/
def C15 (α : ℝ) : ℝ → ℝ :=
  fun θ => -2 * (α / Work.Spaces.c α) * Work.Spaces.dthU (Work.Spaces.Gam α) θ

theorem C15_apply (α θ : ℝ) :
    C15 α θ = -2 * (α / Work.Spaces.c α) * Work.Spaces.dthU (Work.Spaces.Gam α) θ := rfl

theorem G15_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    G15 α Φs z θ = (z + 1) / z
      * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ) :=
  rfl

/-! ## The identity

`((z+1)³/z²)·N₂^{ss} = 2·C15·G15` on the closed quadrant.  The proof is the elementary
computation

`((z+1)³/z²)·(-2𝒰·α(Γ'/c)·2z/(1+z)²) = -4(α/c)·(sin2θ·Γ')·((z+1)/z)(𝒰/sin2θ)`,

the `z`-factors cancelling because `((z+1)³/z²)·(z/(1+z))·(2z/(1+z)²) = 2`; at the two
angular endpoints and at `z = 0` both sides vanish (at `θ = 0, π/2` by `VanishTheta` of `𝒰`,
and at `z = 0` by the junk values `1/0 = 0` of the two prefactors). -/

theorem N2ss_weighted_eq {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hv : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlin.N2ss α Φs z θ = 2 * C15 α θ * G15 α Φs z θ := by
  intro z hz θ hθ
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hz0 : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz0 with hz' | hz'
  · subst hz'
    simp [Work.FTS.Nonlin.N2ss, G15, C15, Work.Spaces.dthU, Work.Construction.s2_eq]
  rcases eq_or_lt_of_le hθ.1 with hθ0' | hθ0'
  · subst hθ0'
    simp [Work.FTS.Nonlin.N2ss, G15, C15, Work.Spaces.dthU, Work.Construction.s2_eq, hv.1 z]
  rcases eq_or_lt_of_le hθ.2 with hθ1' | hθ1'
  · subst hθ1'
    have hs' : Work.Construction.s2 (π / 2) = 0 := by
      rw [Work.Construction.s2_eq, show 2 * (π / 2) = π by ring, Real.sin_pi]
    simp [Work.FTS.Nonlin.N2ss, G15, C15, Work.Spaces.dthU, hs', hv.2 z]
  -- the open quadrant
  have hs2pos : 0 < Work.Construction.s2 θ := by
    rw [Work.Construction.s2_eq]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt hs2pos
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.FTS.Nonlin.N2ss, Work.Construction.pth_Fstar_eq hα]
  simp only [G15_apply, C15_apply, Work.Spaces.dthU, Work.FM.Fstar]
  field_simp
  rw [Work.Construction.s2_eq]
  ring


/-! ## Smoothness of the two factors -/

/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is `C^∞` on the open interval `(0,π/2)`. -/
theorem contDiffOn_Gam (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π / 2)) := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_sin.contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.cos θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_cos.contDiffOn
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) := hsin.mul (hcos.pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow (contDiffOn_const (c := α / 3)) hne
  refine h.congr (fun θ hθ => ?_)
  simp only [Work.Spaces.Gam]

/-- `D_θΓ = sin(2θ)·Γ'` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_dthU_Gam (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ) (Set.Ioo 0 (π / 2)) := by
  have hderiv : ContDiffOn ℝ Work.Stability.smoothOrder
      (deriv (fun t => Work.Spaces.Gam α t)) (Set.Ioo 0 (π / 2)) :=
    (contDiffOn_Gam α).deriv_of_isOpen isOpen_Ioo le_rfl
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (π / 2)) := by
    have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => 2 * θ) :=
      contDiff_const.mul contDiff_id
    exact (Real.contDiff_sin.comp h1).contDiffOn
  have h := hsin.mul hderiv
  refine h.congr (fun θ hθ => ?_)
  simp only [Work.Spaces.dthU]

/-- `C15 α` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_C15 (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (C15 α) (Set.Ioo 0 (π / 2)) := by
  have h := (contDiffOn_const (c := -2 * (α / Work.Spaces.c α))).mul (contDiffOn_dthU_Gam α)
  refine h.congr (fun θ hθ => ?_)
  simp only [C15_apply]

/-- A θ-only function smooth on `(0,π/2)` is `SmoothOpen` as a function of `(z,θ)`. -/
theorem smoothOpen_theta_only {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (π / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) :=
  ha.comp contDiffOn_snd (fun p hp => hp.2)

/-- A `z`-only function smooth on `(0,∞)` is `SmoothOpen` as a function of `(z,θ)`. -/
theorem smoothOpen_z_only {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ Work.Stability.smoothOrder r (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => r z) :=
  hr.comp contDiffOn_fst (fun p hp => hp.1)

theorem smoothOpen_C15_bsl (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => C15 α θ) :=
  smoothOpen_theta_only (contDiffOn_C15 α)

/-- The `𝒰`-expression of the `Φ̃_*`-node is smooth on the open quadrant. -/
theorem smoothOpen_Uop_PhiTs {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
  have hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -3 * Work.FTS.Nonlin.PhiTs α Φs z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-3) hΦ
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -α * (z * Work.Spaces.pz (Work.FTS.Nonlin.PhiTs α Φs) z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-α)
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hΦ.pz)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl h1 h2) ?_
  intro z θ _ _ _
  rw [Work.Construction.Uop]
  ring

/-- `G15 α Φs = ((z+1)/z)·(𝒰(Φ̃_*)/sin 2θ)` is smooth on the open quadrant. -/
theorem smoothOpen_G15 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (G15 α Φs) := by
  have hU : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    smoothOpen_Uop_PhiTs hα hα1 hs
  have hz : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (p.1 + 1) / p.1) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.div (contDiffOn_fst.add (contDiffOn_const (c := (1 : ℝ))))
      contDiffOn_fst ?_
    intro p hp
    exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hs2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.inv ?_ ?_
    · have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => 2 * p.2)
          Work.FTS.EllipticEst.Q0 :=
        (contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_snd
      exact (Real.contDiff_sin.contDiffOn).comp h1 (fun p hp => Set.mem_univ _)
    · intro p hp
      obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (G15 α Φs))
    Work.FTS.EllipticEst.Q0
  refine ContDiffOn.congr ((hz.mul hU).mul hs2) ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hpoint : ∀ z θ : ℝ,
      ((z + 1) / z * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
        * (Real.sin (2 * θ))⁻¹ = G15 α Φs z θ := by
    intro z θ
    rw [G15_apply, Work.Construction.s2_eq]
    ring
  exact (hpoint z θ).symm

/-- `F̲(z) = 2z/(1+z)²` is smooth on `(0,∞)`. -/
theorem smoothOpen_FM_Fstar_z :
    Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => Work.FM.Fstar z) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z / (1 + z) ^ 2)
      (Set.Ioi 0) := by
    refine ContDiffOn.div (contDiff_const.mul contDiff_id).contDiffOn
      ((contDiff_const.add contDiff_id).pow 2).contDiffOn ?_
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have h2 := smoothOpen_z_only h
  have hfun : (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) = fun z (_ : ℝ) => Work.FM.Fstar z := by
    funext z θ; rw [Work.FM.Fstar]
  rwa [hfun] at h2

/-- `N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*` is smooth on the open quadrant. -/
theorem smoothOpen_N2ss {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) := by
  have hU : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    smoothOpen_Uop_PhiTs hα hα1 hs
  have hder : ContDiffOn ℝ Work.Stability.smoothOrder
      (deriv (fun t => Work.Spaces.Gam α t)) (Set.Ioo 0 (π / 2)) :=
    (contDiffOn_Gam α).deriv_of_isOpen isOpen_Ioo le_rfl
  have hth0 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α))
      (Set.Ioo 0 (π / 2)) :=
    (contDiffOn_const (c := α)).mul (hder.div_const _)
  have hth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * (deriv (fun t => Work.Spaces.Gam α t) p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    smoothOpen_theta_only hth0
  have hrad : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.FM.Fstar p.1) Work.FTS.EllipticEst.Q0 :=
    smoothOpen_FM_Fstar_z
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.FTS.Nonlin.N2ss α Φs))
    Work.FTS.EllipticEst.Q0
  refine ContDiffOn.congr
    ((contDiffOn_const (c := (-2 : ℝ))).mul hU |>.mul (hth.mul hrad)) ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hpoint : ∀ z θ : ℝ,
      ((-2 : ℝ) * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
        * (α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α) * Work.FM.Fstar z)
      = Work.FTS.Nonlin.N2ss α Φs z θ := by
    intro z θ
    rw [Work.FTS.Nonlin.N2ss, Work.Construction.pth_Fstar_eq hα]
  exact (hpoint z θ).symm

/-! ## The angular jets of `C15` -/

/-- For a θ-only function, `D_θ^j` is the `dthU`-iterate. -/
theorem DthIter_theta_only (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun _ (θ : ℝ) => g θ) = fun _ θ => Work.Spaces.dthU^[j] g θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.dthU^[j] g θ') θ
        = Work.Spaces.dthU^[j + 1] g θ
      rw [Function.iterate_succ_apply' Work.Spaces.dthU j g, Work.Spaces.dthU]

/-- The `z`-derivatives of a product with a θ-only factor. -/
theorem pzIter_theta_mul (j : ℕ) (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pzIter j K z θ :=
  Work.FTS.H2.pzIter_const_mul c K j z θ

/-- The `dthU`-iterates of `C15 α` are the `D_θ`-jets of `Γ`, up to the constant
`-2α/c`: `dthU^[a] (C15 α) = -2(α/c)·D_θ^{a+1}Γ`. -/
theorem dthU_iter_C15 (α : ℝ) (a : ℕ) :
    Work.Spaces.dthU^[a] (C15 α)
      = fun θ => (-2 * (α / Work.Spaces.c α))
          * Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : C15 α = fun θ => (-2 * (α / Work.Spaces.c α))
      * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ := by
    funext θ; rw [C15_apply]
  rw [hfun, Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]

/-- **The angular jet bound of `C15`**: `|D_θ^a (C15 α)(θ)| ≤ K·α²·Γ(θ)` for `a ≤ 4`,
`0 < α ≤ 1`, `θ ∈ Iθ`. -/
theorem dthU_iter_C15_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[a] (C15 α) θ| ≤ K * α ^ 2 * Work.Spaces.Gam α θ := by
  refine ⟨20 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1), ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    linarith
  · intro α hα hα1 a ha θ hθ
    have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hc : (0 : ℝ) < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hcinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
      rw [inv_eq_one_div, div_le_iff₀ hc]
      linarith [(Work.Spaces.c_bounds α hα hα1).1]
    have hk : |α / Work.Spaces.c α| ≤ 10 * α := by
      rw [abs_of_nonneg (div_nonneg hα.le hc.le), div_eq_mul_inv]
      calc α * (Work.Spaces.c α)⁻¹ ≤ α * 10 := mul_le_mul_of_nonneg_left hcinv hα.le
        _ = 10 * α := by ring
    have hsum0 : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    have htb : Work.Spaces.tBound a 0 ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.single_le_sum (f := fun a => Work.Spaces.tBound a 0)
        (fun a _ => Work.Spaces.tBound_nonneg a 0) (Finset.mem_range.mpr (by omega))
    have hdth := Work.Spaces.dthU_Gam_le (a + 1) (by omega) α hα hα1 θ hθ
    rw [show a + 1 - 1 = a from by omega] at hdth
    rw [dthU_iter_C15]
    rw [abs_mul, abs_mul]
    have h2 : |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ := by
      refine hdth.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htb hα.le) hGam0
    have h3 : |(-2 : ℝ)| * |α / Work.Spaces.c α| = 2 * |α / Work.Spaces.c α| := by
      norm_num
    calc |(-2 : ℝ)| * |α / Work.Spaces.c α|
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        = 2 * |α / Work.Spaces.c α|
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ| := by rw [h3]
      _ ≤ 2 * (10 * α) * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
            * Work.Spaces.Gam α θ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) h2 (abs_nonneg _)
            (by positivity)
      _ ≤ 20 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1) * α ^ 2
            * Work.Spaces.Gam α θ := by
          have h1 : (2 : ℝ) * (10 * α) * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
              * Work.Spaces.Gam α θ)
              ≤ 20 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1) * α ^ 2
                * Work.Spaces.Gam α θ := by
            nlinarith [hGam0, hα, hsum0, sq_nonneg α]
          linarith [h1]

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row11 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.Row19Ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-! ## The algebraic identity `∂_θ 𝒰 = -(2𝒱 + ℛ + α D_z𝒱)` -/

/-- **The identity of row 19.**  For `Ψ` which is `C^∞` on the open quadrant and `(z,θ)` in that
quadrant,

  `∂_θ 𝒰(Ψ) = -(2 𝒱(Ψ) + ℛ(Ψ) + α · D_z 𝒱(Ψ))`.

Proof: write `a = ∂_θΨ`, `b = ∂_z∂_θΨ = ∂_θ∂_zΨ` (Clairaut), `c = ∂_zΨ`, `d = Ψ`.  Then
`∂_θ 𝒰 = -3a - αzb`, while `𝒱 = a - tan θ·d`, `∂_z𝒱 = b - tan θ·c` and
`ℛ = 2 tan θ·d + α tan θ·z c + a`; the two sides differ by
`2a - 2 tan θ d + 2 tan θ d + a - 3a + α z tan θ c - α z tan θ c = 0`. -/
theorem pth_Uop_eq_neg {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad Ψ)
    {z θ : ℝ} (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      = -(2 * Work.Construction.Vop Ψ z θ + Work.Construction.Rop α Ψ z θ
          + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) := by
  have hquad : (z, θ) ∈ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hz, hθ⟩
  have hquad_open : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
    (hsm.contDiffAt (hquad_open.mem_nhds hquad)).of_le (by simp [Work.Stability.smoothOrder])
  have hsm_pz : Work.FTS.LocData.SmoothQuad (Work.Spaces.pz Ψ) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU hsm)
  have hsm_pth : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Ψ) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm)
  have hd1 : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
    ((hsm.curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz Ψ z θ') θ :=
    ((hsm_pz.curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hdz1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    ((hsm.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hdz2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ) z :=
    ((hsm_pth.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hcl : Work.Spaces.pz (Work.Spaces.pth Ψ) z θ = Work.Spaces.pth (Work.Spaces.pz Ψ) z θ :=
    Work.Spaces.pz_pth_comm (f := Ψ) hcd
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hL : Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      = -3 * Work.Spaces.pth Ψ z θ - α * z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    change deriv ((fun θ' => -3 * Ψ z θ') - fun θ' => α * z * Work.Spaces.pz Ψ z θ') θ = _
    rw [deriv_sub (hd1.const_mul (-3)) (hd2.const_mul (α * z)),
      deriv_const_mul (-3) hd1, deriv_const_mul (α * z) hd2]
    rfl
  have hV1 : Work.Construction.Vop Ψ z θ = Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ := rfl
  have hR1 : Work.Construction.Rop α Ψ z θ
      = (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
          + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ := rfl
  have hDz : Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ
      = z * (Work.Spaces.pz (Work.Spaces.pth Ψ) z θ - Real.tan θ * Work.Spaces.pz Ψ z θ) := by
    change z * Work.Spaces.pz (Work.Construction.Vop Ψ) z θ = _
    have hVe : Work.Construction.Vop Ψ
        = fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ := rfl
    rw [hVe]
    change z * deriv ((fun z' => Work.Spaces.pth Ψ z' θ) - fun z' => Real.tan θ * Ψ z' θ) z = _
    rw [deriv_sub hdz2 (hdz1.const_mul (Real.tan θ)),
      deriv_const_mul (Real.tan θ) hdz1]
    rfl
  rw [hL, hV1, hR1, hDz, ← hcl, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## The calculus of `D_θ^i` on the open quadrant -/

/-- **Locality** of `D_θ^i` on the open quadrant: functions that agree on the quadrant have the
same iterated `D_θ`-derivatives there.  (No smoothness is needed; only the fact that `D_θ` is a
`θ`-derivative.) -/
theorem DthIter_congr_Ioi {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
    intro z θ hz h1 h2
    have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨h1, h2⟩)]
        with θ' hθ'
      exact ih z θ' hz hθ'.1 hθ'.2
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq]

/-- The identically vanishing function has vanishing `D_θ`-iterates. -/
theorem DthIter_zero_fun (i : ℕ) :
    ∀ z θ, Work.Spaces.DthIter i (fun _ : ℝ => fun _ : ℝ => (0 : ℝ)) z θ = 0 := by
  induction i with
  | zero => intro z θ; rfl
  | succ n ih =>
    intro z θ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    have h0 : (fun θ' : ℝ => Work.Spaces.DthIter n (fun _ : ℝ => fun _ : ℝ => (0 : ℝ)) z θ')
        = fun _ : ℝ => (0 : ℝ) := funext (fun θ' => ih z θ')
    rw [h0, deriv_const]
    ring

/-- **Additivity** of `D_θ^i` on sums of functions which are `C^∞` on the open quadrant. -/
theorem DthIter_add_smoothQuad {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.LocData.SmoothQuad F) (hG : Work.FTS.LocData.SmoothQuad G) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (fun z θ => F z θ + G z θ) z θ
        = Work.Spaces.DthIter i F z θ + Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
    intro z θ hz h1 h2
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
    have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => F z θ + G z θ) z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n F z θ' + Work.Spaces.DthIter n G z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact ih z θ' hz hθ'.1 hθ'.2
    have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n F z θ') θ :=
      hF.differentiableAt_slice_DthIter n hz hθ
    have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n G z θ') θ :=
      hG.differentiableAt_slice_DthIter n hz hθ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq,
      show (fun θ' => Work.Spaces.DthIter n F z θ' + Work.Spaces.DthIter n G z θ')
        = (fun θ' => Work.Spaces.DthIter n F z θ') + fun θ' => Work.Spaces.DthIter n G z θ'
        from rfl, deriv_add hd1 hd2]
    ring

/-- Multiplication by a `z`-only factor commutes with `D_θ^i` (pointwise, with no regularity
hypotheses: the constant rule for `deriv` is unconditional). -/
theorem DthIter_mul_zfactor (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    ∀ z θ, Work.Spaces.DthIter i (fun z θ => c z * g z θ) z θ
      = c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ n ih =>
    intro z θ
    have hfe : (fun θ' => Work.Spaces.DthIter n (fun z θ => c z * g z θ) z θ')
        = fun θ' => c z * Work.Spaces.DthIter n g z θ' := funext (fun θ' => ih z θ')
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [hfe, Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
    ring

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Defs =====
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

/-- **The flat class on the open quadrant.**  `F0 n K f` says that all the mixed
`(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on `Q0 = (0,∞)×(0,π/2)`. -/
def F0 (n : ℕ) (K : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ k i : ℕ, k + i ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| ≤ K

/-- **The flat class on the closed quadrant** `[0,∞) × [0,π/2]` — the shape needed by
`Work.Spaces.WlInf`. -/
def F0c (n : ℕ) (K : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ k i : ℕ, k + i ≤ n → ∀ z θ : ℝ, 0 ≤ z → 0 ≤ θ → θ ≤ Real.pi / 2 →
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| ≤ K

/-- **The invariant flat class**: `F0` of `f` together with `F0` of `∂_θ f`.  This pair is
what survives products (`F0` alone does not: the product rule for `∂_θ` needs the shifted
family) and it is exactly the data consumed by the `WlInf` angular slot. -/
structure Fb (n : ℕ) (K : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  /-- flat bounds on `f` itself -/
  f0 : F0 n K f
  /-- flat bounds on `∂_θ f` -/
  fd : F0 n K (Work.Spaces.pth f)

/-! ## Elementary API -/

theorem F0.mono {n n' : ℕ} {K K' : ℝ} {f : ℝ → ℝ → ℝ} (hn : n ≤ n') (hK : K' ≤ K)
    (h : F0 n' K' f) : F0 n K f :=
  fun k i hki z θ hz hθ hθ' => le_trans (h k i (le_trans hki hn) z θ hz hθ hθ') hK

theorem F0c.mono {n n' : ℕ} {K K' : ℝ} {f : ℝ → ℝ → ℝ} (hn : n ≤ n') (hK : K' ≤ K)
    (h : F0c n' K' f) : F0c n K f :=
  fun k i hki z θ hz hθ hθ' => le_trans (h k i (le_trans hki hn) z θ hz hθ hθ') hK


theorem Fb.mono {n n' : ℕ} {K K' : ℝ} {f : ℝ → ℝ → ℝ} (hn : n ≤ n') (hK : K' ≤ K)
    (h : Fb n' K' f) : Fb n K f :=
  ⟨h.f0.mono hn hK, h.fd.mono hn hK⟩


/-- `∂_z` of a function which does not depend on `z` is `0`, and so are all its iterates. -/
theorem pzIter_const_of_theta_only (d : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => d) = fun _ _ => 0 := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      funext z θ
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      rw [deriv_const]
    · rw [Work.Spaces.pzIter_succ, ih hn]
      funext z θ
      simp only [Work.Spaces.pz]
      rw [deriv_const]

/-- `D_θ^i` of a constant function is `0` for `i ≥ 1` and the constant itself for `i = 0`. -/
theorem DthIter_const (d : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => d) = fun _ _ => (if i = 0 then d else 0) := by
  induction i with
  | zero => funext z θ; simp
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const]
    simp

/-- The constant function belongs to the flat class. -/
theorem F0.const (n : ℕ) (c : ℝ) : F0 n |c| (fun _ _ => c) := by
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [DthIter_const]
    simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul]
    split_ifs with hi
    · subst hi; simp
    · simp
  · rw [DthIter_const, pzIter_const_of_theta_only _ k hk]
    simp

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs`

The `C^∞`-on-the-open-quadrant regularity of the three objects of the `StarCore` witness that
are built out of the datum `Φ_s` and the singular part `Θ_*(α) = Θ α (F_*)`:

* `Φ̃_* = PhiTs α Φs = Φs - Θ_*(α)`,
* `Φ̃_*/sin 2θ`,
* `Ŷ = Ycheck α Φs = ((z+1)/z)·(Φ̃_*/sin 2θ)`.

The only input about `Θ_*(α)` is the profile identity `L₁₂(F_*)(z) = 2α/(1+z)` (`α ≤ 1` is
carried along by `Work.FTS.PhiStar.L12_profile_eq`), which turns it into the explicit function
`(z,θ) ↦ sin(2θ)/(2(1+z))`, `C^∞` on the open quadrant `(0,∞) × (0,π/2)` because `1 + z > 0`
there.  The remaining two conjuncts are closure of `SmoothOpen` under multiplication and under
division by `sin 2θ ≠ 0` (and by `z ≠ 0`), both legitimate on the *open* quadrant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false

/-! ## Closure of `SmoothOpen` under the pointwise algebra (on the open quadrant) -/

/-- `SmoothOpen` is closed under subtraction. -/
private theorem smoothOpen_sub' {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).sub (hg.forall n)

/-- `SmoothOpen` is closed under multiplication. -/
private theorem smoothOpen_mul' {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).mul (hg.forall n)

/-- The quotient by `sin 2θ` of a `C^∞`-on-the-open-quadrant function is again `C^∞` there:
`sin 2θ > 0` for `0 < θ < π/2`. -/
private theorem smoothOpen_div_sin2' {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / Work.Construction.s2 θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf.forall n
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact h1.div h2 (fun p hp => by
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))

/-- The radial factor `(z+1)/z` is `C^∞` on the open quadrant (its only singularity, `z = 0`,
is outside `Q0`). -/
private theorem smoothOpen_zPlusOne_div_z' :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => (p.1 + 1) / p.1)
    Work.FTS.EllipticEst.Q0
  exact ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst
    (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-! ## The singular part `Θ_*(α) = sin(2θ)/(2(1+z))` -/

/-- **`Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant**: by
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for `z > 0`) it is the explicit function
`(z,θ) ↦ sin(2θ)/(2(1+z))`. -/
private theorem smoothOpen_ThetaFstar' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hbase : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1)))
      Work.FTS.EllipticEst.Q0 := by
    have hnum : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => 2 * (1 + p.1))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    exact hnum.div hden (fun p hp => by
      have hz : (0 : ℝ) < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      positivity)
  refine (hbase.of_le le_top).congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  show Work.Construction.Theta α (Work.Construction.Fstar α) z θ
      = Real.sin (2 * θ) / (2 * (1 + z))
  rw [Work.FTS.PhiStar.Theta_eq_thetaProfile hα hα1 hz.le θ, Work.FTS.PhiStar.ThetaProfile]
  ring

/-! ## The target -/

theorem smoothOpen_PhiTs {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen Φs) : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs α Φs) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.FTS.VocabO2.PhiTs α Φs z θ / Work.Construction.s2 θ) ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs) := by
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothOpen_ThetaFstar' hα hα1
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ) :=
    smoothOpen_sub' hsm hΘ
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
        / Work.Construction.s2 θ) :=
    smoothOpen_div_sin2' h1
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * ((Φs z θ
        - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
          / Work.Construction.s2 θ)) :=
    smoothOpen_mul' smoothOpen_zPlusOne_div_z' h2
  refine ⟨?_, ?_, ?_⟩
  · show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact h1
  · show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
        / Work.Construction.s2 θ)
    exact h2
  · show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * ((Φs z θ
        - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
          / Work.Construction.s2 θ))
    exact h3

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWApi.FlatW_congr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.PhiStar.FlatWApi

/-! ## `FlatW` depends only on the values on the open quadrant

`FlatW l f K` evaluates `f` and its iterated `∂_z`/`∂_θ` derivatives (the `D_θ`-operators are
pointwise multiplications by `sin 2θ` composed with `∂_θ`) only at points of the open quadrant
`Q = {z > 0, 0 < θ < π/2}`.  On the open set `Q` the operators `∂_z`, `∂_θ` are local: two
functions agreeing on `Q` have agreeing iterated derivatives at every point of `Q`.  Hence
`FlatW l f K` and `FlatW l g K` are equivalent whenever `f = g` on `Q`; the constant is `1`. -/

/-- `∂_z` respects agreement on the open quadrant (the slice at fixed `θ ∈ (0, π/2)` agrees
on a whole neighbourhood of any `z > 0`). -/
private lemma agree_pz {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  intro z θ hz hθ hπ
  simp only [Work.Spaces.pz]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hπ

/-- `∂_θ` respects agreement on the open quadrant. -/
private lemma agree_pth {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  intro z θ hz hθ hπ
  simp only [Work.Spaces.pth]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0:ℝ) (π/2) from ⟨hθ, hπ⟩)] with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

/-- Iterated `∂_z` respects agreement on the open quadrant. -/
private lemma agree_pzIter {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ k : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pzIter k f z θ = Work.Spaces.pzIter k g z θ := by
  intro k
  induction k with
  | zero => intro z θ hz hθ hπ; exact h z θ hz hθ hπ
  | succ k ih => intro z θ hz hθ hπ; exact agree_pz ih z θ hz hθ hπ

/-- `D_θ^i ∂_θ` respects agreement on the open quadrant (`D_θ` is multiplication by `sin 2θ`
followed by `∂_θ`, and both operations preserve agreement on the quadrant). -/
private lemma agree_DthIter_pth {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.DthIter i (Work.Spaces.pth f) z θ
          = Work.Spaces.DthIter i (Work.Spaces.pth g) z θ := by
  intro i
  induction i with
  | zero => intro z θ hz hθ hπ; exact agree_pth h z θ hz hθ hπ
  | succ i ih =>
      intro z θ hz hθ hπ
      have hthis := agree_pth (f := Work.Spaces.DthIter i (Work.Spaces.pth f))
        (g := Work.Spaces.DthIter i (Work.Spaces.pth g)) ih z θ hz hθ hπ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      rw [hthis]

theorem FlatW_congr : ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (f g : ℝ → ℝ → ℝ) (K : ℝ),
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π/2 → f z θ = g z θ) →
    Work.FTS.VocabO2.FlatW l f K → Work.FTS.VocabO2.FlatW l g (C * K) := by
  refine ⟨1, one_pos, ?_⟩
  intro l f g K hag hf z θ hz hθ hπ
  obtain ⟨ha, hb⟩ := hf z θ hz hθ hπ
  refine ⟨?_, ?_⟩
  · intro k hk
    have h1 := ha k hk
    rw [agree_pzIter hag k z θ hz hθ hπ] at h1
    simpa using h1
  · intro k i hki
    have h2 := hb k i hki
    have hD := agree_pzIter (f := Work.Spaces.DthIter i (Work.Spaces.pth f))
      (g := Work.Spaces.DthIter i (Work.Spaces.pth g)) (agree_DthIter_pth hag i)
      k z θ hz hθ hπ
    rw [hD] at h2
    simpa using h2

end Work.FTS.PhiStar.FlatWApi
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWApi.FlatW_theta_radial_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FlatW` is stable under multiplication by a radial factor

The operator `pzIter k` is the `k`-fold `∂_z` (applied to the `z`-slice), and `DthIter i` is the
`i`-fold `D_θ = sin(2θ)·∂_θ`.  Multiplying a function by a factor `a z` depending on `z` alone
interacts trivially with both: the `θ`-derivatives never see it and the `z`-derivatives act on it
by the Leibniz rule with a constant (`iteratedDeriv_mul_const_field`).  Consequently the flat
weighted bound `FlatW l` is multiplicative: if `a` satisfies the radial estimate
`|(z+1)^k ∂_z^k a| ≤ A` for `k ≤ l` and `θ ↦ u θ` satisfies `FlatW l _ K`, then
`(z,θ) ↦ a z * u θ` satisfies `FlatW l _ (A·K)`.

The identities are unconditional (no differentiability is assumed): the totalised `deriv` of
`c * f` is `c * deriv f` in a division ring, so the iterated versions
`iteratedDeriv_mul_const_field` / `deriv_const_mul_field` hold pointwise everywhere.
-/

namespace Work.FTS.PhiStar.FlatWApi

open Work.Spaces (Lop pzIter pth Dth DthIter pz)

set_option autoImplicit false

/-! ## The two structural identities -/

/-- Iterated `z`-derivatives commute with multiplication by a function of `θ` alone:
`∂_z^k (b z * φ θ) = (∂_z^k b z) * φ θ`. -/
lemma pzIter_mul_const (b φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    pzIter k (fun z' θ' => b z' * φ θ') z θ = iteratedDeriv k b z * φ θ := by
  have h1 : pzIter k (fun z' θ' => b z' * φ θ') z θ
      = iteratedDeriv k (fun z' => b z' * φ θ) z :=
    Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ
  rw [h1]
  exact iteratedDeriv_mul_const_field b (φ θ)

/-- `Lop u θ = sin(2θ)·u'(θ)` is linear: `Lop (c * g) = c * Lop g`. -/
lemma Lop_const_mul (c : ℝ) (g : ℝ → ℝ) :
    Lop (fun θ => c * g θ) = fun θ => c * Lop g θ := by
  funext θ
  simp only [Lop]
  rw [deriv_const_mul_field]
  ring

/-- Iterated `Lop` is linear. -/
lemma Lop_iter_const_mul (c : ℝ) (g : ℝ → ℝ) (i : ℕ) :
    Lop^[i] (fun θ => c * g θ) = fun θ => c * Lop^[i] g θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      calc Lop^[i.succ] (fun θ => c * g θ)
          = Lop (Lop^[i] (fun θ => c * g θ)) := Function.iterate_succ_apply' Lop i _
        _ = Lop (fun θ => c * Lop^[i] g θ) := by rw [ih]
        _ = (fun θ => c * Lop^[i.succ] g θ) := by
              rw [Lop_const_mul, ← Function.iterate_succ_apply' Lop i g]

/-- Iterated angular derivatives commute with multiplication by a function of `z` alone:
`D_θ^i (b z * φ θ) = b z * (Lop^i φ)(θ)`. -/
lemma DthIter_mul_const (b φ : ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    DthIter i (fun z' θ' => b z' * φ θ') z θ = b z * Lop^[i] φ θ := by
  have h1 : DthIter i (fun z' θ' => b z' * φ θ') z = Lop^[i] (fun θ' => b z * φ θ') :=
    Work.Spaces.DthIter_eq_iterate_Lop i _ z
  have h2 : Lop^[i] (fun θ' => b z * φ θ') = fun θ' => b z * Lop^[i] φ θ' :=
    Lop_iter_const_mul (b z) φ i
  have h3 := congrFun h2 θ
  rw [← h1] at h3
  exact h3

/-! ## The multiplication theorem -/

theorem FlatW_theta_radial_mul : ∃ C : ℝ, 0 < C ∧
  ∀ (l : ℕ) (a u : ℝ → ℝ) (A K : ℝ), 0 ≤ A → 0 ≤ K →
    (∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 < z → |(z + 1) ^ k * iteratedDeriv k a z| ≤ A) →
    Work.FTS.VocabO2.FlatW l (fun _ θ => u θ) K →
    Work.FTS.VocabO2.FlatW l (fun z θ => a z * u θ) (C * (A * K)) := by
  refine ⟨1, one_pos, ?_⟩
  intro l a u A K hA _ ha hU z θ hz hθ hπ
  have hUz := hU z θ hz hθ hπ
  have huz : |u θ| ≤ K := by
    simpa using hUz.1 0 (Nat.zero_le l)
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [pzIter_mul_const a u k z θ]
    have hmul : |(z + 1) ^ k * (iteratedDeriv k a z * u θ)|
        = |(z + 1) ^ k * iteratedDeriv k a z| * |u θ| := by
      rw [show (z + 1) ^ k * (iteratedDeriv k a z * u θ)
            = ((z + 1) ^ k * iteratedDeriv k a z) * u θ from (mul_assoc _ _ _).symm, abs_mul]
    rw [hmul]
    calc |(z + 1) ^ k * iteratedDeriv k a z| * |u θ| ≤ A * K :=
          mul_le_mul (ha k hk z hz) huz (abs_nonneg _) hA
      _ = 1 * (A * K) := by ring
  · intro k i hki
    have hpth : pth (fun z θ => a z * u θ)
        = fun z θ => a z * deriv (fun θ'' => u θ'') θ := by
      funext z' θ'
      simp only [Work.Spaces.pth]
      exact deriv_const_mul_field (a z')
    have hDth : DthIter i (pth (fun z θ => a z * u θ))
        = fun z θ => a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ := by
      rw [hpth]
      funext z' θ'
      exact DthIter_mul_const a (deriv (fun θ'' => u θ'')) i z' θ'
    have hpz : pzIter k (DthIter i (pth (fun z θ => a z * u θ))) z θ
        = iteratedDeriv k a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ := by
      rw [hDth]
      exact pzIter_mul_const a (Lop^[i] (deriv (fun θ'' => u θ''))) k z θ
    rw [hpz]
    have hpthU : (fun θ' => pth (fun _ θ'' => u θ'') z θ') = deriv (fun θ'' => u θ'') := by
      funext θ'
      rfl
    have hLopDth : Lop^[i] (deriv (fun θ'' => u θ'')) θ
        = DthIter i (pth (fun _ θ'' => u θ'')) z θ := by
      rw [Work.Spaces.DthIter_eq_iterate_Lop, hpthU]
    have hKl : |Lop^[i] (deriv (fun θ'' => u θ'')) θ| ≤ K := by
      rw [hLopDth]
      simpa using hUz.2 0 i (by omega)
    have hmul : |(z + 1) ^ k * (iteratedDeriv k a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ)|
        = |(z + 1) ^ k * iteratedDeriv k a z| * |Lop^[i] (deriv (fun θ'' => u θ'')) θ| := by
      rw [show (z + 1) ^ k * (iteratedDeriv k a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ)
            = ((z + 1) ^ k * iteratedDeriv k a z) * Lop^[i] (deriv (fun θ'' => u θ'')) θ
          from (mul_assoc _ _ _).symm, abs_mul]
    rw [hmul]
    calc |(z + 1) ^ k * iteratedDeriv k a z| * |Lop^[i] (deriv (fun θ'' => u θ'')) θ|
          ≤ A * K := mul_le_mul (ha k (by omega) z hz) hKl (abs_nonneg _) hA
      _ = 1 * (A * K) := by ring

end Work.FTS.PhiStar.FlatWApi
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatW_aprof =====
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

set_option linter.unusedVariables false

/-! ## The angular half: a radial function has no `∂_θ`-derivatives -/

/-- `pth` of a radial function vanishes. -/
private theorem pth_radial (g : ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => g z) = fun _ _ => (0 : ℝ) := by
  funext z θ
  simp [Work.Spaces.pth]

/-- `D_θ^i` of the zero function is zero. -/
private theorem DthIter_zero_fun (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

/-! ## The identification of the flat radial piece on `z > 0` -/


/-- The germ form of the identification, with the flat weight `(z+1)/z` applied:
on `{z > 0}`, `((z+1)/z)·Aprof α = (1/2)·(1+·)·At N 0`. -/
private theorem Aprof_germ {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 < z) :
    (fun z' => (z' + 1) / z' * Aprof α z')
      =ᶠ[𝓝 z] (fun z' => (1 / 2) * ((1 + z') * Work.FTS.H2.PhiStarE.At (5 / α) 0 z')) := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  have h := Aprof_eqOn_negDk hα hα1 (show z' ∈ Set.Ioi 0 from hz')
  rw [h, Work.FTS.H2.PhiStarE.Dk_zero]
  have hz'0 : z' ≠ 0 := ne_of_gt hz'
  field_simp
  ring

/-! ## The flat radial estimate -/

/-- **The radial half of `FlatW 7`.**  From the one-variable analytic bound
`At_linear_deriv_bound` for `(1+·)·At N 0`, transported along the germ equality
`Aprof_germ` and scaled by `1/2`. -/
private theorem flat_radial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z| ≤ C * α := by
  obtain ⟨C₀, hC₀, hbound⟩ := At_linear_deriv_bound
  refine ⟨C₀ / 10 + 1, by positivity, fun α hα hα1 k hk z hz => ?_⟩
  have hgerm := Aprof_germ hα hα1 hz
  have hN : (2 : ℝ) ≤ 5 / α := by
    rw [le_div_iff₀ hα]; linarith
  have h1 : (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z
      = (deriv^[k]) (fun w => (1 / 2) * ((1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w)) z := by
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
    exact hgerm.iteratedDeriv_eq k
  have h2 : (deriv^[k]) (fun w => (1 / 2) * ((1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w)) z
      = (1 / 2) * (deriv^[k]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w) z := by
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_const_mul_field (1 / 2)
      (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w)
  have hb := hbound (5 / α) z k hN hz hk
  rw [show (1 : ℝ) + z = z + 1 from by ring] at hb
  have hC₀N : C₀ / (5 / α) = C₀ * α / 5 := by field_simp
  rw [hC₀N] at hb
  have hrw : (z + 1) ^ k * (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z
      = (1 / 2) * ((z + 1) ^ k * (deriv^[k])
          (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w) z) := by
    rw [h1, h2]; ring
  rw [hrw, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc (1 / 2) * |(z + 1) ^ k * (deriv^[k])
          (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w) z|
      ≤ (1 / 2) * (C₀ * α / 5) :=
        mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ = C₀ * α / 10 := by ring
    _ ≤ (C₀ / 10 + 1) * α := by nlinarith [hα, hC₀]

/-! ## The main statement -/

/-- **The flat radial piece of the `StarCore` witness is `O(α)` in `FlatW 7`.**
The angular slots of `FlatW` vanish because the function is radial, and the radial slots
are `flat_radial_bound`. -/
theorem FlatW_aprof : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.FTS.VocabO2.FlatW 7 (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z) (C * α) := by
  obtain ⟨C₁, hC₁, hrad⟩ := flat_radial_bound
  refine ⟨C₁, hC₁, fun α hα hα1 => ?_⟩
  intro z θ hz hθ hθ2
  constructor
  · intro k hk
    rw [show Work.Spaces.pzIter k (fun z θ => (z + 1) / z * Aprof α z) z θ
        = (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z from
          Work.FTS.H2.PhiStarE.pzIter_radial (fun z' => (z' + 1) / z' * Aprof α z') k z θ]
    exact hrad α hα hα1 k hk z hz
  · intro k i hki
    have hf : Work.Spaces.DthIter i (Work.Spaces.pth (fun z θ => (z + 1) / z * Aprof α z))
        = fun _ _ => (0 : ℝ) := by
      rw [pth_radial (fun z' => (z' + 1) / z' * Aprof α z'), DthIter_zero_fun i]
    rw [hf, Work.FTS.H2.PhiStarE.pzIter_zero_fun]
    simp only [mul_zero, abs_zero]
    exact mul_nonneg (le_of_lt hC₁) (le_of_lt hα)

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatW_psiDiv =====
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
set_option maxHeartbeats 800000

/-! ## The divided profile and its derivative -/

/-- The divided angular profile `W θ = ψ θ / sin 2θ`. -/
abbrev Wdiv (ψ : ℝ → ℝ) : ℝ → ℝ := fun θ => ψ θ / Real.sin (2 * θ)

/-- Its `θ`-derivative `p = W'`. -/
abbrev Pdiv (ψ : ℝ → ℝ) : ℝ → ℝ := deriv (Wdiv ψ)

/-! ## A function with vanishing derivative on the open interval is constant -/

/-- If `h` is differentiable on `(0,π/2)` and `h' ≡ 0` there, then `h` is constant there
(Fundamental Theorem of Calculus on `[θ, π/4]`). -/
lemma exists_const_of_deriv_eq_zero {h : ℝ → ℝ}
    (hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), DifferentiableAt ℝ h θ)
    (hz : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv h θ = 0) :
    ∃ c : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), h θ = c := by
  refine ⟨h (Real.pi / 4), fun θ hθ => ?_⟩
  have h4 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rcases le_total θ (Real.pi / 4) with hle | hle
    · rw [Set.uIcc_of_le hle]
      intro x hx
      exact ⟨by linarith [hθ.1, hx.1], by linarith [hx.2, h4.2]⟩
    · rw [Set.uIcc_of_ge hle]
      intro x hx
      exact ⟨by linarith [h4.1, hx.1], by linarith [hx.2, hθ.2]⟩
  have hII : IntervalIntegrable (deriv h) volume θ (Real.pi / 4) :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr
      (fun x hx => (hz x (hsub (Set.uIoc_subset_uIcc hx))).symm)
  have hFTC := intervalIntegral.integral_deriv_eq_sub (f := h) (a := θ) (b := Real.pi / 4)
    (fun x hx => hdiff x (hsub hx)) hII
  have hzero : (∫ y in θ..(Real.pi / 4), deriv h y) = 0 := by
    have h1 : (∫ y in θ..(Real.pi / 4), deriv h y)
        = ∫ y in θ..(Real.pi / 4), (0 : ℝ) :=
      intervalIntegral.integral_congr (fun x hx => hz x (hsub hx))
    rw [h1, intervalIntegral.integral_zero]
  linarith [hFTC, hzero]

/-! ## An explicit (uniform) bound sequence for the `Lop`-iterates

`Work.FTS.PhiStar.LopIterRecursion` gives, for a solution of `Lop f = A·f - g` on the open
interval, the binomial expansion of the iterates.  For the final constant of `FlatW_psiDiv`
to be independent of `(α,ψ)` the *sequence* of bounds has to be an explicit function of the
data bounds `Ka`, `Kg` and the base bound `M`; `LopBdAux` below is exactly that sequence. -/

/-- The explicit sequence of bounds generated by the recursion
`Lop^{n+1} f = ∑_{j≤n} C(n,j)·(Lop^{n-j}A)·(Lop^j f) - Lop^n g`. -/
noncomputable def LopBdAux (Ka Kg : ℕ → ℝ) (M : ℝ) (n : ℕ) : ℕ → ℝ :=
  Nat.rec (Function.update (fun _ : ℕ => 0) 0 M)
    (fun k b => Function.update b (k + 1)
      ((∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * (Ka (k - j) * b j))) + Kg k)) n

/-- The level-`6` bound, the one used by the transfer to `FlatW 7`. -/
noncomputable def LopBd (Ka Kg : ℕ → ℝ) (M : ℝ) (i : ℕ) : ℝ := LopBdAux Ka Kg M 6 i

lemma LopBdAux_zero (Ka Kg : ℕ → ℝ) (M : ℝ) :
    LopBdAux Ka Kg M 0 = Function.update (fun _ : ℕ => 0) 0 M := rfl

lemma LopBdAux_succ (Ka Kg : ℕ → ℝ) (M : ℝ) (n : ℕ) :
    LopBdAux Ka Kg M (n + 1) = Function.update (LopBdAux Ka Kg M n) (n + 1)
      ((∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * (Ka (n - j) * LopBdAux Ka Kg M n j))) + Kg n) := rfl

/-- Non-negativity of the bound sequence. -/
lemma LopBdAux_nonneg {Ka Kg : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hKa0 : ∀ j, 0 ≤ Ka j) (hKg0 : ∀ j, 0 ≤ Kg j) :
    ∀ n i, 0 ≤ LopBdAux Ka Kg M n i := by
  intro n
  induction n with
  | zero =>
      intro i
      by_cases hi : i = 0
      · subst hi
        rw [LopBdAux_zero, Function.update_self]
        exact hM
      · rw [LopBdAux_zero, Function.update_of_ne hi]
  | succ n ih =>
      intro i
      by_cases hi : i = n + 1
      · subst hi
        rw [LopBdAux_succ, Function.update_self]
        exact add_nonneg
          (Finset.sum_nonneg fun j _ =>
            mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKa0 _) (ih j)))
          (hKg0 n)
      · rw [LopBdAux_succ, Function.update_of_ne hi]
        exact ih i

/-- The bound sequence dominates the `Lop`-iterates of a solution of `Lop f = A·f - g`. -/
lemma LopBdAux_bound {f A g : ℝ → ℝ} {Ka Kg : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M)
    (hKa0 : ∀ j, 0 ≤ Ka j) (hKg0 : ∀ j, 0 ≤ Kg j)
    (hKa : ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |(Work.Spaces.Lop^[j]) A θ| ≤ Ka j)
    (hKg : ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |(Work.Spaces.Lop^[j]) g θ| ≤ Kg j)
    (hrec : ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i + 1]) f θ
        = (∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) * ((Work.Spaces.Lop^[i - j]) A θ * (Work.Spaces.Lop^[j]) f θ))
          - (Work.Spaces.Lop^[i]) g θ) :
    ∀ n ≤ 6, ∀ i ≤ n, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) f θ| ≤ LopBdAux Ka Kg M n i := by
  intro n
  induction n with
  | zero =>
      intro _ i hi θ hθ
      have hi0 : i = 0 := by omega
      subst hi0
      rw [LopBdAux_zero, Function.update_self]
      simpa using hMf θ hθ
  | succ n ih =>
      intro hn i hi θ hθ
      rcases lt_or_eq_of_le hi with hlt | heq
      · rw [LopBdAux_succ, Function.update_of_ne (show i ≠ n + 1 by omega)]
        exact ih (by omega) i (by omega) θ hθ
      · subst heq
        rw [LopBdAux_succ, Function.update_self, hrec n θ hθ]
        have h1 : |∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * ((Work.Spaces.Lop^[n - j]) A θ * (Work.Spaces.Lop^[j]) f θ)|
            ≤ ∑ j ∈ Finset.range (n + 1),
                (n.choose j : ℝ) * (Ka (n - j) * LopBdAux Ka Kg M n j) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
          intro j hj
          have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hnj : n - j ≤ 6 := by omega
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose j))]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hKa (n - j) hnj θ hθ) (ih (by omega) j hjle θ hθ)
              (abs_nonneg _) (hKa0 _))
            (Nat.cast_nonneg (n.choose j))
        have h2 : |(Work.Spaces.Lop^[n]) g θ| ≤ Kg n := hKg n (by omega) θ hθ
        calc |(∑ j ∈ Finset.range (n + 1),
                  (n.choose j : ℝ) * ((Work.Spaces.Lop^[n - j]) A θ * (Work.Spaces.Lop^[j]) f θ))
                - (Work.Spaces.Lop^[n]) g θ|
              ≤ |∑ j ∈ Finset.range (n + 1),
                  (n.choose j : ℝ) * ((Work.Spaces.Lop^[n - j]) A θ * (Work.Spaces.Lop^[j]) f θ)|
                + |(Work.Spaces.Lop^[n]) g θ| := abs_sub _ _
          _ ≤ (∑ j ∈ Finset.range (n + 1),
                (n.choose j : ℝ) * (Ka (n - j) * LopBdAux Ka Kg M n j)) + Kg n := by
              linarith

/-! ## The transfer to `FlatW` for a `z`-independent function -/

/-- For a `θ`-only function `g`: a bound on `g` together with bounds on the `D_θ`-iterates of
`∂_θ g` up to order `6` give `FlatW 7 (fun z θ => g θ) C`. -/
lemma flatW_of_theta_only {g : ℝ → ℝ} {C CW CB : ℝ}
    (hW : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ CW)
    (hB : ∀ i ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i]) (deriv g) θ| ≤ CB)
    (hC0 : 0 ≤ C) (hWle : CW ≤ C) (hBle : CB ≤ C) :
    Work.FTS.VocabO2.FlatW 7 (fun z θ => g θ) C := by
  intro z θ hz hθ hθ2
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ2⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    rcases k with _ | k
    · simpa using le_trans (hW θ hθm) hWle
    · rw [Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ g k]
      simp only [mul_zero, abs_zero]
      exact hC0
  · intro k i hki
    have hpth : Work.Spaces.pth (fun z θ => g θ) = fun _ θ => deriv g θ := by
      funext z θ
      rfl
    rcases k with _ | k
    · have hi : i ≤ 6 := by omega
      rw [hpth, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only (deriv g) i]
      simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul]
      exact le_trans (hB i hi θ hθm) hBle
    · rw [hpth, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only (deriv g) i,
        Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ (Work.Spaces.dthU^[i] (deriv g)) k]
      simp only [mul_zero, abs_zero]
      exact hC0

/-! ## The main theorem -/

theorem FlatW_psiDiv : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.PhiStar.AngModel α ψ →
    Work.FTS.VocabO2.FlatW 7 (fun z θ => ψ θ / Work.Construction.s2 θ) C := by
  obtain ⟨K, hK0, hKgam, hKA⟩ := LopAuxBounds
  have hKd : (0 : ℝ) ≤ ∑ i ∈ Finset.range 7, LopBd K K 500 i :=
    Finset.sum_nonneg fun i _ => LopBdAux_nonneg (by norm_num) hK0 hK0 6 i
  refine ⟨(∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1, ?_, ?_⟩
  · have h2 : (0 : ℝ) < 500 * Real.pi + 1 := by positivity
    linarith
  · intro α ψ hα hα4 hang
    -- the honest `C^∞`-smoothness of `ψ` on the open interval
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)) := fun n =>
      hang.smooth.of_le (by
        rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
        exact_mod_cast le_top)
    have hψeq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ :=
      fun θ hθ => hang.eq θ hθ
    -- smoothness of the divided profile on the open interval
    have hWsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ' : ℝ => ψ θ' / Real.sin (2 * θ'))
        (Set.Ioo 0 (Real.pi / 2)) := by
      intro n
      have hsin : ContDiffOn ℝ n (fun t : ℝ => Real.sin (2 * t))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      exact (hsm n).div hsin (fun t ht => ne_of_gt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
          (by linarith [ht.2, Real.pi_pos])))
    -- (1) the first-order equation for the derivative of the divided profile
    have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.Spaces.Lop (Pdiv ψ) θ
        = (6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) * Pdiv ψ θ
          - Work.FTS.VocabO.GamBar α θ :=
      PsiDivS2Ode hsm hψeq
    -- (2) the first integral is constant
    have hderivzero : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (fun t => Real.sin t ^ 2 * Real.cos t ^ 3 * Pdiv ψ t
          - Work.FTS.PhiStar.Gzero α t / 2) θ = 0 :=
      DerivConstPhi (le_of_lt hα) hsm (PsiDivS2Ode hsm hψeq)
    have hdiffh : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        DifferentiableAt ℝ (fun t => Real.sin t ^ 2 * Real.cos t ^ 3 * Pdiv ψ t
          - Work.FTS.PhiStar.Gzero α t / 2) θ := by
      have hdw : ContDiffOn ℝ 1 (deriv (Wdiv ψ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (hWsm 2).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      have hsc : ContDiffOn ℝ 1 (fun t : ℝ => Real.sin t ^ 2 * Real.cos t ^ 3)
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have hG : ContDiffOn ℝ 1 (Work.FTS.PhiStar.Gzero α) (Set.Ioo 0 (Real.pi / 2)) :=
        (contDiffOn_Gzero α (le_of_lt hα)).of_le (by norm_num)
      have h1 : ContDiffOn ℝ 1 (fun t => Real.sin t ^ 2 * Real.cos t ^ 3 * Pdiv ψ t
          - Work.FTS.PhiStar.Gzero α t / 2) (Set.Ioo 0 (Real.pi / 2)) :=
        (hsc.mul hdw).sub (hG.div_const 2)
      intro θ hθ
      exact (h1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    obtain ⟨cc, hcc⟩ := exists_const_of_deriv_eq_zero hdiffh hderivzero
    have hconst : ∃ c : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Real.sin θ ^ 2 * Real.cos θ ^ 3 * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
          - Work.FTS.PhiStar.Gzero α θ / 2 = c :=
      ⟨cc, fun θ hθ => hcc θ hθ⟩
    -- (3) the derivative is the explicit regular solution
    have hpfun : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
          = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2 :=
      PsiDivS2EqPfun hα hα4 hsm hang.cont hang.bdry0 hconst
    -- (4) the flat bound on the divided profile
    have hdiffW : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        DifferentiableAt ℝ (fun θ' => ψ θ' / Real.sin (2 * θ')) θ := by
      intro θ hθ
      exact ((hWsm 1).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    have hWb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |ψ θ / Real.sin (2 * θ)| ≤ 500 * Real.pi :=
      Wdiv_bound hα hα4 hang.moment hang.bdry0 hang.bdry1 hdiffW hpfun
    -- (5) the `D_θ`-bounds for the derivative
    have hsmP : ∀ n : ℕ, ContDiffOn ℝ n (Pdiv ψ) (Set.Ioo 0 (Real.pi / 2)) := fun n =>
      (hWsm (n + 1)).deriv_of_isOpen isOpen_Ioo (m := n) (by simp)
    have hsmA : ∀ n : ℕ, ContDiffOn ℝ n
        (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) := fun n => by fun_prop
    have hsmG : ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.VocabO.GamBar α)
        (Set.Ioo 0 (Real.pi / 2)) := by
      intro n
      have hGam : ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (contDiffOn_Gam α).of_le (by exact_mod_cast le_top)
      have hsub : ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α
          - (5 / 4) * Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (hGam.div_const _).sub (by fun_prop)
      exact hsub
    have hrecLop : ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.Spaces.Lop^[i + 1]) (Pdiv ψ) θ
          = (∑ j ∈ Finset.range (i + 1),
              (i.choose j : ℝ) * ((Work.Spaces.Lop^[i - j])
                (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ
                * (Work.Spaces.Lop^[j]) (Pdiv ψ) θ))
            - (Work.Spaces.Lop^[i]) (Work.FTS.VocabO.GamBar α) θ :=
      LopIterRecursion hsmP hsmA hsmG hode
    have hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Pdiv ψ θ| ≤ 500 := by
      intro θ hθ
      have h1 := hpfun θ hθ
      have h2 := Pfun_div_sin_sq_le α hα hα4 (θ := θ)
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [show Pdiv ψ θ = deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ from rfl, h1]
      exact h2
    have hLopBd : ∀ i ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i]) (Pdiv ψ) θ| ≤ LopBd K K 500 i :=
      LopBdAux_bound (M := 500) (Ka := K) (Kg := K) (by norm_num) hMf hK0 hK0 hKA
        (hKgam α hα hα4) hrecLop 6 le_rfl
    -- (6) the transfer
    have hCBle : (∑ i ∈ Finset.range 7, LopBd K K 500 i)
        ≤ (∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1 := by
      have : (0 : ℝ) < 500 * Real.pi + 1 := by positivity
      linarith
    have hCWle : 500 * Real.pi
        ≤ (∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1 := by linarith [hKd]
    have hC0 : (0 : ℝ) ≤ (∑ i ∈ Finset.range 7, LopBd K K 500 i) + 500 * Real.pi + 1 := by
      have h2 : (0 : ℝ) < 500 * Real.pi + 1 := by positivity
      linarith
    have hB : ∀ i ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i]) (deriv (Wdiv ψ)) θ|
          ≤ ∑ i ∈ Finset.range 7, LopBd K K 500 i := by
      intro i hi θ hθ
      have hmem : i ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
      exact le_trans (hLopBd i hi θ hθ)
        (Finset.single_le_sum (fun j _ => LopBdAux_nonneg (by norm_num) hK0 hK0 6 j) hmem)
    have hFlat := flatW_of_theta_only (g := Wdiv ψ) (CW := 500 * Real.pi)
      (CB := ∑ i ∈ Finset.range 7, LopBd K K 500 i) hWb hB hC0 hCWle hCBle
    simpa only [Wdiv, Work.Construction.s2] using hFlat

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.ZeroOffWitness =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.ZeroOffWitness` — the zero-extension normal form of `Φ_*`

`StarCore.zeroOff` demands that `PhiTs α Φs = Φs − Θ` vanish *off* the open quadrant.
This is free: given any honest solution `Φ` of the profile equation one replaces it by

`ZeroOffW α Φ z θ = if (z,θ) ∈ Q0 then Φ z θ else Θ α (F_*)(z,θ)`,

which agrees with `Φ` on the open quadrant (an open set) and equals the singular part `Θ` outside
it.  Since `Θ(z,0) = Θ(z,π/2) = 0` (the factor `sin 2θ`) and `bslOp` is built from `deriv`, which
only sees the germ, the replacement preserves `IsBslSol`, `SmoothOpen` and every bound that is
stated on `Q0` only (`FlatW`, `Ycheck`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Classical

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The **zero-extension normal form**: equal to `Φ` on the open quadrant, and equal to the
singular part `Θ α (F_*)` off it (in particular on the lines `θ = 0`, `θ = π/2` and the axis
`z = 0`). -/
def ZeroOffW (α : ℝ) (Φ : Fn) : Fn :=
  fun z θ => if (z, θ) ∈ Work.FTS.EllipticEst.Q0 then Φ z θ
    else Work.Construction.Theta α (Work.Construction.Fstar α) z θ

/-- `ZeroOffW α Φ` agrees with `Φ` on the open quadrant. -/
theorem zeroOffW_eqOn (α : ℝ) (Φ : Fn) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → ZeroOffW α Φ z θ = Φ z θ := by
  intro z θ h
  unfold ZeroOffW
  rw [if_pos h]

/-- The singular part vanishes on the two boundary lines. -/
theorem Theta_zero (α : ℝ) (z : ℝ) :
    Work.Construction.Theta α (Work.Construction.Fstar α) z 0 = 0 ∧
      Work.Construction.Theta α (Work.Construction.Fstar α) z (π / 2) = 0 := by
  have h0 : Work.Construction.s2 0 = 0 := by simp [Work.Construction.s2]
  have h1 : Work.Construction.s2 (π / 2) = 0 := by
    simp only [Work.Construction.s2]
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  constructor
  · simp only [Work.Construction.Theta, h0, mul_zero, zero_mul]
  · simp only [Work.Construction.Theta, h1, mul_zero, zero_mul]

/-- `PhiTs` of the zero-extension agrees with `PhiTs` of `Φ` on the open quadrant. -/
theorem PhiTs_zeroOffW_eqOn (α : ℝ) (Φ : Fn) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Construction.PhiTil α (Work.Construction.Fstar α) (ZeroOffW α Φ) z θ
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φ z θ := by
  intro z θ h
  simp only [Work.Construction.PhiTil, zeroOffW_eqOn α Φ z θ h]

/-- **`zeroOff`**: `PhiTs` of the zero-extension vanishes off the open quadrant. -/
theorem PhiTs_zeroOffW_off (α : ℝ) (Φ : Fn) :
    ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      Work.Construction.PhiTil α (Work.Construction.Fstar α) (ZeroOffW α Φ) z θ = 0 := by
  intro z θ h
  simp only [Work.Construction.PhiTil, ZeroOffW, if_neg h, sub_self]

/-! ## `pthIter` as an iterated one-variable derivative -/

/-- `pthIter k` is the `k`-th derivative of the `θ`-slice. -/
theorem pthIter_eq_iteratedDeriv (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter k f z θ = iteratedDeriv k (fun θ' => f z θ') θ := by
  induction k generalizing θ with
  | zero => simp [Work.Spaces.pthIter]
  | succ k ih =>
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pth]
    have hfun : (fun θ' : ℝ => Work.Spaces.pthIter k f z θ')
        = fun θ' : ℝ => iteratedDeriv k (fun θ'' : ℝ => f z θ'') θ' := by
      funext θ'
      exact ih θ'
    rw [hfun, iteratedDeriv_succ]

/-! ## Locality of `Lzero` and `bslOp` on the open quadrant -/

/-- `Lzero` is local: two functions agreeing on `Q0` have the same `Lzero` at every point of
`Q0`.  (All its terms are built from `deriv`, which is a limit.) -/
theorem Lzero_congr (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0)
    (h : ∀ z' θ' : ℝ, (z', θ') ∈ Work.FTS.EllipticEst.Q0 → f z' θ' = g z' θ') :
    Work.Elliptic.Lzero f z θ = Work.Elliptic.Lzero g z θ := by
  have hU : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (z, θ) :=
    Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzp
  have hzslice : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    have hcont : ContinuousAt (fun z' : ℝ => (z', θ)) z := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds hU] with z' hz'
    exact h z' θ hz'
  have hthslice : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    have hcont : ContinuousAt (fun θ' : ℝ => (z, θ')) θ := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds hU] with θ' hθ'
    exact h z θ' hθ'
  have htan : (fun θ' : ℝ => Real.tan θ' * f z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Real.tan θ' * g z θ') := by
    filter_upwards [hthslice] with θ' hθ'
    rw [hθ']
  have hpth2 : Work.Spaces.pthIter 2 f z θ = Work.Spaces.pthIter 2 g z θ := by
    rw [pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv]
    exact hthslice.iteratedDeriv_eq 2
  have hcross : Work.Spaces.pth (fun z θ => Real.tan θ * f z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z θ := htan.deriv_eq
  have hpt : f z θ = g z θ := h z θ hzp
  simp only [Work.Elliptic.Lzero, hpth2, hcross, hpt]

/-- `bslOp` is local on the open quadrant. -/
theorem bslOp_congr (α : ℝ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0)
    (h : ∀ z' θ' : ℝ, (z', θ') ∈ Work.FTS.EllipticEst.Q0 → f z' θ' = g z' θ') :
    Work.Elliptic.bslOp α f z θ = Work.Elliptic.bslOp α g z θ := by
  have hU : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (z, θ) :=
    Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzp
  have hzslice : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    have hcont : ContinuousAt (fun z' : ℝ => (z', θ)) z := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds hU] with z' hz'
    exact h z' θ hz'
  have hpz2 : Work.Spaces.pzIter 2 f z θ = Work.Spaces.pzIter 2 g z θ := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
    exact hzslice.iteratedDeriv_eq 2
  have hpz1 : Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
    simp only [Work.Spaces.pz]
    exact hzslice.deriv_eq
  have hL : Work.Elliptic.Lzero f z θ = Work.Elliptic.Lzero g z θ :=
    Lzero_congr f g hzp h
  simp only [Work.Elliptic.bslOp, hpz2, hpz1, hL]

/-! ## Transport of the class properties -/

/-- The zero-extension is `C^∞` on the open quadrant when `Φ` is. -/
theorem smoothOpen_zeroOffW {α : ℝ} {Φ : Fn}
    (h : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (ZeroOffW α Φ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at h ⊢
  refine h.congr (fun p hp => ?_)
  simp only [Function.uncurry]
  exact zeroOffW_eqOn α Φ p.1 p.2 hp

/-- The zero-extension solves the same profile equation. -/
theorem isBslSol_zeroOffW {α : ℝ} {Φ : Fn}
    (h : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φ) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) (ZeroOffW α Φ) := by
  obtain ⟨heq, h0, h1, hdec⟩ := h
  have hz0 : (∀ z : ℝ, (z, 0) ∉ Work.FTS.EllipticEst.Q0) := fun z =>
    fun hh => lt_irrefl (0 : ℝ) ((Work.FTS.EllipticEst.mem_Q0).mp hh).2.1
  have hz1 : (∀ z : ℝ, (z, π / 2) ∉ Work.FTS.EllipticEst.Q0) := fun z =>
    fun hh => lt_irrefl (π / 2) ((Work.FTS.EllipticEst.mem_Q0).mp hh).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ hθ2
    have hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩
    rw [bslOp_congr α (ZeroOffW α Φ) Φ hzp (fun z' θ' h' => zeroOffW_eqOn α Φ z' θ' h')]
    exact heq z hz θ hθ hθ2
  · intro z
    unfold ZeroOffW
    rw [if_neg (hz0 z), (Theta_zero α z).1]
  · intro z
    unfold ZeroOffW
    rw [if_neg (hz1 z), (Theta_zero α z).2]
  · intro θ hθ
    rw [Work.Spaces.Iθ] at hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0]
      have hconst : (fun z : ℝ => ZeroOffW α Φ z 0) = fun _ => (0 : ℝ) := by
        funext z
        unfold ZeroOffW
        rw [if_neg (hz0 z), (Theta_zero α z).1]
      rw [hconst]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
    · rw [hθ1]
      have hconst : (fun z : ℝ => ZeroOffW α Φ z (π / 2)) = fun _ => (0 : ℝ) := by
        funext z
        unfold ZeroOffW
        rw [if_neg (hz1 z), (Theta_zero α z).2]
      rw [hconst]
      exact tendsto_const_nhds
    · have hev : (fun z : ℝ => ZeroOffW α Φ z θ) =ᶠ[atTop] (fun z : ℝ => Φ z θ) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        exact zeroOffW_eqOn α Φ z θ ((Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ0, hθ1⟩)
      exact (hdec θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩).congr' hev.symm

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.radial_slot_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

open MeasureTheory Set Filter
open scoped Topology Real

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The closed-domain radial slot bound

`VocabO2.FlatW l f K` is a statement about the **open** quadrant `Q0 = (0,∞) × (0,π/2)`: it
bounds `|(z+1)^k ∂_z^k f|` and the flat angular slots there.  `radial_slot_le` extends its
first family of slots (`k ≤ 4`) to the closed rectangle `Iz × Iθ = [0,∞) × [0,π/2]`.

The point of the statement is that the extra points are harmless: `f` is assumed to *vanish*
off `Q0`, so

* for `θ = 0` or `θ = π/2` the whole `z`-slice of `f` is `0`, hence every iterated
  `z`-derivative of `f` vanishes on the slice (`pzIter_eq_zero_of_slice_zero`);
* for `z = 0` and `θ ∈ (0,π/2)` the slice `z' ↦ f z' θ` vanishes on `(-∞,0)` (again because
  the whole half-plane `z < 0` is off `Q0`), so *each* iterated `z`-derivative vanishes at
  `0`: the derivative at the origin of a function which is zero on `(-∞,0]` is zero
  (`deriv_eq_zero_of_eqOn_Iic_zero_prv`), and the slices of the iterates vanish on `(-∞,0)`.

Note that the value of `deriv` at a point of non-differentiability is `0` in Mathlib
(`deriv_zero_of_not_differentiableAt`), which is exactly what makes the second bullet work
at the origin. -/

/-- A function which vanishes on the closed left half-line `(-∞,0]` has derivative `0` at the
origin.  (`deriv` is `0` at a point of non-differentiability, while at `0` differentiability
would force the one-sided difference quotients `-g 0 / h`, `h → 0⁻`, to have a finite limit,
hence `g 0 = 0` and derivative `0`.) -/
private lemma deriv_eq_zero_of_eqOn_Iic_zero_prv {g : ℝ → ℝ} (h : ∀ x ≤ 0, g x = 0) :
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
          exact deriv_eq_zero_of_eqOn_Iic_zero_prv hφ
        · -- at `z < 0` the slice is identically zero on a neighbourhood of `z`
          have hev : (fun z' => Work.Spaces.pzIter j f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
            filter_upwards [isOpen_Iio.mem_nhds h] with z' hz'
            exact hφ z' hz'.le
          rw [hev.deriv_eq, deriv_const]
      rw [Work.Spaces.pzIter_succ]
      show deriv (fun z' => Work.Spaces.pzIter j f z' θ) z = 0
      exact hstep

/-- **The closed-domain form of the radial slots of `FlatW`.**  For a function which is `C^∞`
on the open quadrant and vanishes off it, the bounds `|(z+1)^k ∂_z^k f| ≤ K` for `k ≤ 4`
extend from `Q0` to the closed rectangle `[0,∞) × [0,π/2]`. -/
theorem radial_slot_le {f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hzero : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0)
    (hF : Work.FTS.VocabO2.FlatW 4 f K) {k : ℕ} (hk : k ≤ 4) :
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

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Two elementary one-dimensional tools -/

/-- Cauchy–Schwarz in the form `(∫ √B·u)² ≤ (∫B)(∫u²)`, for `B ≥ 0`. -/
private theorem cs_sqrt_mul_gen {B u : ℝ → ℝ} {s : Set ℝ} (hBnn : ∀ x, 0 ≤ B x)
    (hBint : MeasureTheory.IntegrableOn B s)
    (hBaesm : MeasureTheory.AEStronglyMeasurable B (MeasureTheory.volume.restrict s))
    (huint : MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) s)
    (huaesm : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s)) :
    (∫ x in s, Real.sqrt (B x) * u x) ^ 2 ≤ (∫ x in s, B x) * (∫ x in s, (u x) ^ 2) := by
  have h1 : MeasureTheory.MemLp (fun x => Real.sqrt (B x)) 2 (MeasureTheory.volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hBaesm)]
    exact hBint.congr (Filter.Eventually.of_forall fun x => (Real.sq_sqrt (hBnn x)).symm)
  have h2 : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr huint
  have h := Work.Spaces.cs_integral h1 h2
  rw [show (∫ x in s, (Real.sqrt (B x)) ^ 2) = ∫ x in s, B x from
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))] at h
  exact h

/-- `∫_{(0,z)} (x/(1+x)²)² ≤ z³/3`. -/
private theorem u_sq_Ioc_le {z : ℝ} (hz : 0 ≤ z) :
    ∫ x in Set.Ioc 0 z, (x / (1 + x) ^ 2) ^ 2 ≤ z ^ 3 / 3 := by
  have hle : ∀ x ∈ Set.Ioc 0 z, (x / (1 + x) ^ 2) ^ 2 ≤ x ^ 2 := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < ((1 + x) ^ 2) ^ 2)]
    have h2 : (1:ℝ) ≤ (1 + x) ^ 4 := by
      nlinarith [hx0.le, sq_nonneg x, sq_nonneg (1 + x)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x))]
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioc 0 z) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (z ^ 2) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (continuousOn_id.pow 2).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [Real.norm_of_nonneg (sq_nonneg x)]
      exact pow_le_pow_left₀ hx.1.le hx.2 2
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (x / (1 + x) ^ 2)) hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hle)
  refine h.trans ?_
  rw [← intervalIntegral.integral_of_le hz, integral_pow]
  norm_num

/-- `∫_{(z,∞)} (x/(1+x)²)² ≤ 1/z` for `z > 0`. -/
private theorem u_sq_Ioi_le {z : ℝ} (hz : 0 < z) :
    ∫ x in Set.Ioi z, (x / (1 + x) ^ 2) ^ 2 ≤ 1 / z := by
  have hle : ∀ x ∈ Set.Ioi z, (x / (1 + x) ^ 2) ^ 2 ≤ x ^ (-(2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hz hx
    rw [div_pow, Real.rpow_neg hx0.le, Real.rpow_two, inv_eq_one_div,
      le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2), div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)), sq_nonneg (x * x)]
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(2 : ℝ))) (Set.Ioi z) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hz
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (x / (1 + x) ^ 2)) hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hle)
  refine h.trans ?_
  rw [integral_Ioi_rpow_of_lt (by norm_num) hz,
    show ((-2:ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-! ## The growth bounds -/

/-- **The `z`-pointwise growth bounds for `L₁₂(g)` in the open-quadrant class.**

For `g` of class `C^∞` on the open quadrant and `g ∈ ℋ⁴`, with `L₁₂(g)(0) = 0`, and for
`K₁ = ∫_θ K(θ)² dθ`, `X = |g|_{ℋ⁴}`:

  `(L₁₂ g z)² ≤ (max(K₁/3, K₁) + 1)·X²·z³`  and  `(L₁₂ g z)² ≤ (max(K₁/3, K₁) + 1)·X²/z`.

The first bound covers the behaviour near `z = 0` (where `L₁₂(g)` vanishes at least like
`z^{3/2}` because of the normalisation `L₁₂(g)(0) = 0`), the second the behaviour at infinity
(where `L₁₂(g)` decays at least like `z^{-1/2}`); the two together give
`|L₁₂(g)(z)| ≤ √C·X·min(z^{3/2}, z^{-1/2})`. -/
theorem L12_sq_le_growth_honest (α : ℝ) {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (h0 : Work.Construction.L12 g 0 = 0) :
    (∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
        ≤ (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3)
    ∧ (∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
        ≤ (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
              (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 / z) := by
  have hEE : Work.Construction.L12 g = Work.Elliptic.L12 g :=
    Work.FTS.H2.constructionL12_eq_ellipticL12 g
  -- integrability of the density, from *continuity* on the open quadrant only
  have hintL : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
      hsm.continuousOn hmem
  have h0' : Work.Elliptic.L12 g 0 = 0 := by rw [← hEE]; exact h0
  obtain ⟨hval, -, -⟩ := Work.Elliptic.L12_values g hintL h0'
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hK1def
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  set X : ℝ := Work.FTS.Nonlin.Xn α g with hXdef
  have hXnn : 0 ≤ X := by
    rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 4 g
  set B : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ
    with hBdef
  set u : ℝ → ℝ := fun s => s / (1 + s) ^ 2 with hudef
  have hBnn : ∀ s, 0 ≤ B s := fun s => MeasureTheory.integral_nonneg fun θ =>
    Work.Spaces.HkIntegrand_nonneg α 4 g s θ
  have hu0 : ∀ s, 0 < s → 0 ≤ u s := by
    intro s hs; rw [hudef]; positivity
  have hBint : MeasureTheory.IntegrableOn B Work.Spaces.Iz := hmem.2
  -- (1) the pointwise bound on the density
  have hdens : ∀ s : ℝ, 0 < s → (Work.Elliptic.L12dens g s) ^ 2 ≤ K1 * B s * (u s) ^ 2 := by
    intro s hs
    -- the angular Cauchy--Schwarz at slot `0`
    have hQ : (Work.Elliptic.Qang g 0 s) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
      have h := Work.FTS.OpenPkg.QangOpen.Qang_sq_leQ_open α g hsm hmem 0 (by norm_num) hs
      simpa only [Work.Spaces.DzIter_zero] using h
    -- the angular slice of `g` is dominated by the `ℋ⁴`-integrand
    have hslice : (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) * (Work.Spaces.w s) ^ 2 ≤ B s := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
        rw [Work.Spaces.Iθ]
        rw [MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
          have h2 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g 0 (by norm_num) hs hθ
          simp only [Work.Spaces.DzIter_zero] at h2
          have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (Work.Spaces.w s))
          rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hs)))] at h3)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 s (le_of_lt hs)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    have hw2 : 0 < (Work.Spaces.w s) ^ 2 := pow_pos (Work.FTS.H2.w_pos hs) 2
    -- the `b = 1` slot bound `(Q₀)² ≤ K₁·(s⁴/(1+s)⁴)·B(s)`
    have hb : (Work.Elliptic.Qang g 0 s) ^ 2 ≤ K1 * (s ^ 4 / (1 + s) ^ 4) * B s := by
      have hK1nn' : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
        MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      calc (Work.Elliptic.Qang g 0 s) ^ 2
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := hQ
        _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (((∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) * (Work.Spaces.w s) ^ 2)
                  / (Work.Spaces.w s) ^ 2) := by
              rw [mul_div_cancel_right₀ _ (ne_of_gt hw2)]
        _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (B s / (Work.Spaces.w s) ^ 2) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hslice hw2.le) hK1nn'
        _ = K1 * (s ^ 4 / (1 + s) ^ 4) * B s := by
              have hwinv : ((Work.Spaces.w s) ^ 2)⁻¹ = s ^ 4 / (1 + s) ^ 4 := by
                rw [Work.Spaces.w, div_pow, inv_div]
                congr 1 <;> ring
              rw [hK1def, div_eq_mul_inv, hwinv]
              ring
    rw [Work.Elliptic.L12dens_eq_Qang_div g s, div_pow, div_le_iff₀ (pow_pos hs 2)]
    refine hb.trans (le_of_eq ?_)
    rw [hK1def, hBdef, hudef]
    field_simp
  -- (2) the pointwise bound on the density, in absolute value
  have hdens' : ∀ s : ℝ, 0 < s → |Work.Elliptic.L12dens g s|
      ≤ Real.sqrt K1 * (Real.sqrt (B s) * u s) := by
    intro s hs
    have hKb : 0 ≤ K1 * B s := mul_nonneg hK1nn (hBnn s)
    have h := Real.sqrt_le_sqrt (hdens s hs)
    rw [Real.sqrt_mul hKb] at h
    rw [Real.sqrt_sq_eq_abs] at h
    rw [Real.sqrt_mul hK1nn] at h
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hu0 s hs)] at h
    simpa only [mul_assoc] using h
  -- (3) measurability and integrability of the auxiliary functions
  have hu_cont : ContinuousOn u (Set.Ioi (0:ℝ)) := by
    rw [hudef]
    refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have : (0:ℝ) < 1 + x := by linarith
    positivity
  have hu_aesm : ∀ {s : Set ℝ}, s ⊆ Set.Ioi (0:ℝ) →
      MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s) := by
    intro s hs
    exact (hu_cont.aestronglyMeasurable measurableSet_Ioi).mono_measure
      (MeasureTheory.Measure.restrict_mono hs le_rfl)
  have hu_int_Ioc : ∀ z : ℝ, MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioc 0 z) := by
    intro z
    refine MeasureTheory.IntegrableOn.of_bound ?_
      ((hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1)).pow 2) 1 ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      rw [Real.norm_of_nonneg (sq_nonneg _), hudef, div_pow,
        div_le_one (by
          have h2 : (1:ℝ) ≤ (1 + x) ^ 2 := by nlinarith [hx0.le]
          exact pow_pos (lt_of_lt_of_le one_pos h2) 2)]
      nlinarith [hx0.le, sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)),
        sq_nonneg (1 + x * x + x)]
  have hu_int_Ioi : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioi z) := by
    intro z hz
    refine MeasureTheory.Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hz)
      ((hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx)).pow 2) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans hz hx
    rw [Real.norm_of_nonneg (sq_nonneg _), hudef, div_pow, Real.rpow_neg hx0.le,
      Real.rpow_two, inv_eq_one_div, le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2),
      div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (1 + x), sq_nonneg ((1 + x) * (1 + x)), sq_nonneg (x * x)]
  -- (4) integrability of `√B · u`
  have hsqu : ∀ {s : Set ℝ}, MeasureTheory.IntegrableOn B s →
      MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) s →
      MeasureTheory.AEStronglyMeasurable B (MeasureTheory.volume.restrict s) →
      MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s) →
      MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) s := by
    intro s hBi hui hBa hua
    refine MeasureTheory.Integrable.mono' ((hBi.add hui).const_mul (1/2))
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hBa).mul hua) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (B x))]
    show Real.sqrt (B x) * |u x| ≤ 1 / 2 * (B x + (u x) ^ 2)
    nlinarith [sq_nonneg (Real.sqrt (B x) - |u x|), Real.sq_sqrt (hBnn x), sq_abs (u x)]
  have hHk : Work.Spaces.HkSq α 4 g = X ^ 2 := by
    have h0H : (0:ℝ) ≤ Work.Spaces.HkSq α 4 g :=
      MeasureTheory.integral_nonneg fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    rw [hXdef, show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl]
    exact (Real.sq_sqrt h0H).symm
  refine ⟨?_, ?_⟩
  · -- the small-`z` bound, from `L₁₂(g)(z) = -∫_{(0,z)}L₁₂dens`
    intro z hz
    have hB_ioc : MeasureTheory.IntegrableOn B (Set.Ioc 0 z) :=
      hBint.mono_set (fun s hs => hs.1.le)
    have hI_int : MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) (Set.Ioc 0 z) :=
      hsqu hB_ioc (hu_int_Ioc z) hB_ioc.aestronglyMeasurable
        (hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1))
    have hcs := cs_sqrt_mul_gen hBnn hB_ioc hB_ioc.aestronglyMeasurable (hu_int_Ioc z)
      (hu_aesm (s := Set.Ioc 0 z) (fun x hx => hx.1))
    have hBle : (∫ s in Set.Ioc 0 z, B s) ≤ X ^ 2 := by
      have h := MeasureTheory.setIntegral_mono_set hBint
        (Filter.Eventually.of_forall fun s => hBnn s)
        (Filter.Eventually.of_forall fun s (hs : s ∈ Set.Ioc 0 z) => hs.1.le)
      have hvalB : (∫ s in Work.Spaces.Iz, B s) = Work.Spaces.HkSq α 4 g := by
        simp only [hBdef, Work.Spaces.HkSq]
      rwa [hvalB, hHk] at h
    have hI2 : (∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 ≤ X ^ 2 * z ^ 3 := by
      refine hcs.trans ?_
      have hule := u_sq_Ioc_le hz.le
      have h1 : (∫ s in Set.Ioc 0 z, B s) * (∫ s in Set.Ioc 0 z, (u s) ^ 2)
          ≤ X ^ 2 * (z ^ 3 / 3) :=
        mul_le_mul hBle hule (MeasureTheory.integral_nonneg fun x => sq_nonneg _) (sq_nonneg X)
      have h2 : X ^ 2 * (z ^ 3 / 3) ≤ X ^ 2 * z ^ 3 := by
        have : (0:ℝ) ≤ z ^ 3 / 3 := by positivity
        nlinarith [sq_nonneg X]
      linarith
    have h1 : |Work.Elliptic.L12 g z| ≤ Real.sqrt K1
        * ∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s := by
      have habs : |Work.Elliptic.L12 g z| = |∫ s in (0)..z, Work.Elliptic.L12dens g s| := by
        rw [hval z hz.le]; simp
      rw [habs]
      refine (intervalIntegral.abs_integral_le_integral_abs hz.le).trans ?_
      rw [intervalIntegral.integral_of_le hz.le]
      refine (MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        (hI_int.const_mul (Real.sqrt K1)) ?_).trans
        (le_of_eq (MeasureTheory.integral_const_mul _ _))
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
        (fun s hs => hdens' s hs.1)
    have h2 : (Work.Elliptic.L12 g z) ^ 2 ≤ K1 * (X ^ 2 * z ^ 3) := by
      rw [← sq_abs]
      calc |Work.Elliptic.L12 g z| ^ 2
          ≤ (Real.sqrt K1 * ∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = K1 * (∫ s in Set.Ioc 0 z, Real.sqrt (B s) * u s) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hK1nn]
        _ ≤ K1 * (X ^ 2 * z ^ 3) := mul_le_mul_of_nonneg_left hI2 hK1nn
    rw [hEE]
    refine h2.trans ?_
    have hC : K1 ≤ max (K1 / 3) K1 + 1 :=
      le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have hXz : (0:ℝ) ≤ X ^ 2 * z ^ 3 := by positivity
    simpa [mul_assoc, ← hK1def] using mul_le_mul_of_nonneg_right hC hXz
  · -- the large-`z` bound, from `L₁₂(g)(z) = ∫_{(z,∞)}L₁₂dens`
    intro z hz
    have hB_ioi : MeasureTheory.IntegrableOn B (Set.Ioi z) :=
      hBint.mono_set (fun s hs => (lt_trans hz hs).le)
    have huioi := hu_int_Ioi z hz
    have hI_int : MeasureTheory.IntegrableOn (fun x => Real.sqrt (B x) * u x) (Set.Ioi z) :=
      hsqu hB_ioi huioi hB_ioi.aestronglyMeasurable
        (hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx))
    have hcs := cs_sqrt_mul_gen hBnn hB_ioi hB_ioi.aestronglyMeasurable huioi
      (hu_aesm (s := Set.Ioi z) (fun x hx => lt_trans hz hx))
    have hBle : (∫ s in Set.Ioi z, B s) ≤ X ^ 2 := by
      have h := MeasureTheory.setIntegral_mono_set hBint
        (Filter.Eventually.of_forall fun s => hBnn s)
        (Filter.Eventually.of_forall fun s (hs : s ∈ Set.Ioi z) => (lt_trans hz hs).le)
      have hvalB : (∫ s in Work.Spaces.Iz, B s) = Work.Spaces.HkSq α 4 g := by
        simp only [hBdef, Work.Spaces.HkSq]
      rwa [hvalB, hHk] at h
    have hI2 : (∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 ≤ X ^ 2 / z := by
      refine hcs.trans ?_
      have hule := u_sq_Ioi_le hz
      have h1 : (∫ s in Set.Ioi z, B s) * (∫ s in Set.Ioi z, (u s) ^ 2)
          ≤ X ^ 2 / z := by
        have h2 := mul_le_mul hBle hule
          (MeasureTheory.integral_nonneg fun x => sq_nonneg _) (sq_nonneg X)
        simpa only [hudef, mul_one_div] using h2
      exact h1
    have h1 : |Work.Elliptic.L12 g z| ≤ Real.sqrt K1
        * ∫ s in Set.Ioi z, Real.sqrt (B s) * u s := by
      have habs : |Work.Elliptic.L12 g z| = |∫ s in Set.Ioi z, Work.Elliptic.L12dens g s| := by
        rw [show Work.Elliptic.L12 g z = ∫ s in Set.Ioi z, Work.Elliptic.L12dens g s from rfl]
      rw [habs]
      refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
      refine (MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        (hI_int.const_mul (Real.sqrt K1)) ?_).trans
        (le_of_eq (MeasureTheory.integral_const_mul _ _))
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun s hs => hdens' s (lt_trans hz hs))
    have h2 : (Work.Elliptic.L12 g z) ^ 2 ≤ K1 * (X ^ 2 / z) := by
      rw [← sq_abs]
      calc |Work.Elliptic.L12 g z| ^ 2
          ≤ (Real.sqrt K1 * ∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = K1 * (∫ s in Set.Ioi z, Real.sqrt (B s) * u s) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hK1nn]
        _ ≤ K1 * (X ^ 2 / z) := mul_le_mul_of_nonneg_left hI2 hK1nn
    rw [hEE]
    refine h2.trans ?_
    have hC : K1 ≤ max (K1 / 3) K1 + 1 :=
      le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have hXz : (0:ℝ) ≤ X ^ 2 / z := by positivity
    simpa [mul_div_assoc, ← hK1def] using mul_le_mul_of_nonneg_right hC hXz

end Work.FTS.StrongEps.E4R3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux.ThetaIbpO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **`f` vanishes at the two angular endpoints**, for every `z > 0`, as a consequence of
`BdryTraces` (the `a + b = 0` slot: `sin(2θ)^{1-γ} f(z,θ)² → 0`).  The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.tendsto_slice_zero_bdry`, stated at level `0`, which is exactly
the slot supplied by `RegQo α 2 f`. -/
theorem tendsto_slice_zero_bdry_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hbd : Work.FTS.Nonlin.BdryTraces α 0 f) {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun θ => f s θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Filter.Tendsto (fun θ => f s θ) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hbd' := (hbd 0 0 (le_refl 0)).2 s hs
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  constructor
  · -- `θ → 0⁺`
    have hsq : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * f s θ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := hbd'.1
    have hg : Filter.Tendsto (fun θ =>
        Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcomp : Filter.Tendsto (fun θ =>
          Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at hcomp
      exact hcomp
    have hle : ∀ᶠ θ in 𝓝[>] (0 : ℝ), |f s θ|
        ≤ Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hpi2)]
        with θ hθ hθ2
      have hθ' : (0 : ℝ) < θ := hθ
      have hθ2' : θ < π / 2 := hθ2
      have hsin0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
      have h1 : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
          (show (1 : ℝ) - Work.Spaces.gam α ≤ (0 : ℝ) by
            rw [Work.Spaces.gam]; linarith)
        rw [Real.rpow_zero] at h
        exact h
      rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
      rw [sq_abs]
      nlinarith [sq_nonneg (f s θ)]
    have hzero : Filter.Tendsto (fun θ => |f s θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hle hg
    exact (tendsto_zero_iff_abs_tendsto_zero (fun θ => f s θ)).mpr hzero
  · -- `θ → (π/2)⁻`
    have hsq : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * f s θ ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := hbd'.2
    have hg : Filter.Tendsto (fun θ =>
        Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
        (𝓝[<] (π / 2)) (𝓝 0) := by
      have hcomp : Filter.Tendsto (fun θ =>
          Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
          (𝓝[<] (π / 2)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at hcomp
      exact hcomp
    have hle : ∀ᶠ θ in 𝓝[<] (π / 2), |f s θ|
        ≤ Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hpi2)]
        with θ hθ2 hθ
      have hθ' : (0 : ℝ) < θ := hθ
      have hθ2' : θ < π / 2 := hθ2
      have hsin0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
      have h1 : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
          (show (1 : ℝ) - Work.Spaces.gam α ≤ (0 : ℝ) by
            rw [Work.Spaces.gam]; linarith)
        rw [Real.rpow_zero] at h
        exact h
      rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
      rw [sq_abs]
      nlinarith [sq_nonneg (f s θ)]
    have hzero : Filter.Tendsto (fun θ => |f s θ|) (𝓝[<] (π / 2)) (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hle hg
    exact (tendsto_zero_iff_abs_tendsto_zero (fun θ => f s θ)).mpr hzero

/-- **The angular integration by parts in the open-quadrant class**:
`∫_{Iθ} C0h(θ) ∂_θ f(z,θ) dθ = -∫_{Iθ} C0g(θ) f(z,θ) dθ` for `z > 0`, where `C0h = 3K sin(2θ)`
is the angular factor of the density of `L₁₂(Transport f)` and `C0g = C0h'`.  The boundary
terms `C0h(0) = C0h(π/2) = 0` vanish, and the two endpoint limits of `C0h·f` are `0` by
`BdryTraces`.  This is `Work.FTS.CoercivityFix.Coer1T.C0thetaIBP_Q` with `SmoothOpen` in place
of `SmoothQuad` (the proof uses only *interior* differentiability of the slice plus the
endpoint limits). -/
theorem C0thetaIBP_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hbd : Work.FTS.Nonlin.BdryTraces α 0 f) {s : ℝ} (hs : 0 < s)
    (hfI : MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ)
    (hDI : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0h θ * Work.Spaces.pth f s θ
      = -∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0g θ * f s θ := by
  have hpi2 : (0 : ℝ) ≤ π / 2 := by positivity
  have hpi2pos : (0 : ℝ) < π / 2 := by positivity
  -- the endpoint limits of `f`
  obtain ⟨hf0, hf2⟩ := tendsto_slice_zero_bdry_O α hα hbd hs
  -- the primitive and its derivative on the open interval
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun θ' => Work.Coercivity.C0h θ' * f s θ')
        (Work.Coercivity.C0g θ * f s θ
          + Work.Coercivity.C0h θ * Work.Spaces.pth f s θ) θ := by
    intro θ hθ
    have h1 : HasDerivAt (fun θ' => f s θ') (Work.Spaces.pth f s θ) θ :=
      (differentiableAt_slice_theta_O hso hs hθ).hasDerivAt
    exact (Work.Coercivity.C0h_hasDerivAt θ).mul h1
  -- integrability of the two summands of the derivative
  have hC0h_cont : Continuous Work.Coercivity.C0h := by
    unfold Work.Coercivity.C0h Work.Spaces.K
    fun_prop
  have hC0g_cont : Continuous Work.Coercivity.C0g := by
    unfold Work.Coercivity.C0g
    fun_prop
  have hK_cont : Continuous (fun θ : ℝ => 3 * Work.Spaces.K θ) := by
    unfold Work.Spaces.K
    fun_prop
  have hI1 : MeasureTheory.IntegrableOn (fun θ => Work.Coercivity.C0g θ * f s θ)
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.continuousOn_mul hC0g_cont.continuousOn hfI isCompact_Icc
  have hI2 : MeasureTheory.IntegrableOn (fun θ => Work.Coercivity.C0h θ * Work.Spaces.pth f s θ)
      Work.Spaces.Iθ := by
    refine (MeasureTheory.IntegrableOn.continuousOn_mul hK_cont.continuousOn hDI
      isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro θ _
    simp only [Work.Coercivity.C0h, Work.Spaces.Dth, Work.Spaces.K]
    ring
  have hderiv_int : IntervalIntegrable (fun θ => Work.Coercivity.C0g θ * f s θ
      + Work.Coercivity.C0h θ * Work.Spaces.pth f s θ) MeasureTheory.volume 0 (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
      ((hI1.mono_set Set.Ioc_subset_Icc_self).add (hI2.mono_set Set.Ioc_subset_Icc_self))
  -- the limits of the primitive
  have hlim0 : Filter.Tendsto (fun θ => Work.Coercivity.C0h θ * f s θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Filter.Tendsto Work.Coercivity.C0h (𝓝[>] (0 : ℝ)) (𝓝 (Work.Coercivity.C0h 0)) :=
      hC0h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Work.Coercivity.C0h_zero.1] at h1
    simpa using h1.mul hf0
  have hlim2 : Filter.Tendsto (fun θ => Work.Coercivity.C0h θ * f s θ) (𝓝[<] (π / 2)) (𝓝 0) := by
    have h1 : Filter.Tendsto Work.Coercivity.C0h (𝓝[<] (π / 2))
        (𝓝 (Work.Coercivity.C0h (π / 2))) :=
      hC0h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Work.Coercivity.C0h_zero.2] at h1
    simpa using h1.mul hf2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := 0) (b := π / 2)
    hpi2pos hderiv hderiv_int hlim0 hlim2
  -- split and convert to set integrals over `Iθ`
  have hsplit : (∫ y in (0 : ℝ)..(π / 2), (Work.Coercivity.C0g y * f s y
        + Work.Coercivity.C0h y * Work.Spaces.pth f s y))
      = (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y)
        + (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y) :=
    intervalIntegral.integral_add
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
        (hI1.mono_set Set.Ioc_subset_Icc_self))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
        (hI2.mono_set Set.Ioc_subset_Icc_self))
  have hzero : (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y)
      + (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y) = 0 := by
    rw [← hsplit]
    simpa using hFTC
  have hg_eq : (∫ y in Work.Spaces.Iθ, Work.Coercivity.C0g y * f s y)
      = ∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)))).symm
  have hh_eq : (∫ y in Work.Spaces.Iθ, Work.Coercivity.C0h y * Work.Spaces.pth f s y)
      = ∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)))).symm
  rw [hg_eq, hh_eq]
  linarith [hzero]

end Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem wip_transport_le_O (β : ℝ) (u : Work.FTS.Galerkin.Fn)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hvan0 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (u z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvan2 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (u z θ) ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
        / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) (Work.Coercivity.Transport u) u
      ≤ (3 * |β - 1|) * Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) u u := by
  -- the two integrands on the product space
  let Gp : ℝ × ℝ → ℝ := fun p =>
    Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-β) * Work.Spaces.Dth u p.1 p.2 * u p.1 p.2
      / (1 + p.1)
  let Bp : ℝ × ℝ → ℝ := fun p =>
    Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-β) * (u p.1 p.2) ^ 2
  have hvol : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hGp : MeasureTheory.Integrable Gp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hvol]; exact hint
  have hBp : MeasureTheory.Integrable Bp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hvol]; exact hint2
  have hGslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Gp (z, θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hGp.prod_right_ae
  have hBslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Bp (z, θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hBp.prod_right_ae
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
      MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Work.Spaces.Iz, Set.mem_Ici, not_imp]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  -- the slice-wise inequality: `∫_θ Gp ≤ |β-1| ∫_θ Bp`
  have hkey : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ |β - 1| * (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    filter_upwards [hGslice, hBslice, hzpos] with z hGz hBz hzp
    have hwne : Work.Spaces.w z ^ 2 ≠ 0 := by
      have : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      positivity
    -- the core integrabilities, obtained from the two product integrabilities
    have hBcore : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hBz' : MeasureTheory.Integrable
          (fun θ => Work.Spaces.w z ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine hBz.congr (Filter.Eventually.of_forall (fun θ => ?_))
        dsimp only [Bp]; ring
      have h2 := hBz'.const_mul ((Work.Spaces.w z ^ 2))⁻¹
      refine h2.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.w z ^ 2)⁻¹ *
          (Work.Spaces.w z ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
        = (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
      rw [inv_mul_cancel_left₀ hwne]
    have hKcore : MeasureTheory.Integrable
        (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.CoercivityFix.Coer1.cos_sin_integrable_Q β u hzp hBz
    have hIcore : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (hGz.const_mul ((1 + z) / (Work.Spaces.w z) ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => ?_))
      dsimp only [Gp]
      have hw : Work.Spaces.w z ≠ 0 := by
        rw [Work.Spaces.w]; exact div_ne_zero (by positivity) (by positivity)
      have h1z : (1 : ℝ) + z ≠ 0 := by positivity
      field_simp
    -- the one-dimensional integration by parts
    have hslice := slice_ibp_gen_O β u hu hvan0 hvan2 z hzp hIcore hKcore
    -- the `θ`-independent factor `w z ^ 2/(1+z)` out of the slice integrals
    have h1 : (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (∫ θ, (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [show (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = ∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
              ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun θ => by dsimp only [Gp]; ring))]
      rw [MeasureTheory.integral_const_mul]
    have hGval : (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (β - 1) * (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [h1, hslice]
      rw [show ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((β - 1) * (∫ θ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          = (β - 1) * (((Work.Spaces.w z) ^ 2 / (1 + z)) *
              (∫ θ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) from by ring]
      rw [MeasureTheory.integral_const_mul]
    -- the three integral comparisons
    have hc1 : (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hintL : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hKcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring_nf))
      refine MeasureTheory.integral_mono_ae hintL hBz ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hA : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)) (sq_nonneg _)
      have hcoef : Real.cos (2 * θ) / (1 + z) ≤ 1 := by
        have h1z : 0 < 1 + z := by linarith [hzp]
        rw [div_le_iff₀ h1z]
        linarith [Real.cos_le_one (2 * θ)]
      dsimp only [Bp]
      calc ((Work.Spaces.w z) ^ 2 / (1 + z)) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
          = (Real.cos (2 * θ) / (1 + z)) *
              ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) := by
            ring
        _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hA
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 := one_mul _
    have hc2 : (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hintL : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hBcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring))
      refine MeasureTheory.integral_mono_ae hintL hBz ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hcoef : (Work.Spaces.w z) ^ 2 / (1 + z) ≤ (Work.Spaces.w z) ^ 2 := by
        have h1z : 0 < 1 + z := by linarith [hzp]
        rw [div_le_iff₀ h1z]; nlinarith [hzp, hw2]
      dsimp only [Bp]
      calc ((Work.Spaces.w z) ^ 2 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hX
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 := by ring
    have hc3 : -((∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hneg : (∫ θ, -(((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = -((∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
        simpa using MeasureTheory.integral_neg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      rw [← hneg]
      have hintL : MeasureTheory.Integrable (fun θ => -(((Work.Spaces.w z) ^ 2 / (1 + z)) *
          ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((hBcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).neg).congr
          (Filter.Eventually.of_forall (fun θ => by simp only [Pi.neg_apply]))
      have hintR : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hKcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring_nf))
      refine MeasureTheory.integral_mono_ae hintL hintR ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hc : 0 ≤ (Work.Spaces.w z) ^ 2 / (1 + z) :=
        div_nonneg (sq_nonneg _) (by linarith [hzp])
      have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
      have hcos : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
      calc -(((Work.Spaces.w z) ^ 2 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          = (Work.Spaces.w z) ^ 2 / (1 + z) *
              (-((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)) := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 / (1 + z) *
              (Real.cos (2 * θ) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ hc
            have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
                * (1 + Real.cos (2 * θ)) := mul_nonneg hX (by linarith)
            nlinarith [h1]
        _ = (Work.Spaces.w z) ^ 2 / (1 + z) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) := by ring
    -- combine, by cases on `β ≥ 1`
    rcases le_total (1 : ℝ) β with hb | hb
    · have hb1 : 0 ≤ β - 1 := by linarith
      have habs : |β - 1| = β - 1 := abs_of_nonneg hb1
      rw [hGval, habs]
      exact mul_le_mul_of_nonneg_left hc1 hb1
    · have hb1 : β - 1 ≤ 0 := by linarith
      have habs : |β - 1| = -(β - 1) := abs_of_nonpos hb1
      rw [hGval, habs]
      have hstep : (β - 1) * (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ≤ (β - 1) * (-(∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
        mul_le_mul_of_nonpos_left hc3 hb1
      have hstep2 : (β - 1) * (-(∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          ≤ (-(β - 1)) * (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        nlinarith [hc2, hb1]
      linarith [hstep, hstep2]
  -- integrate over `z`
  have hFz : MeasureTheory.Integrable
      (fun z => ∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hGp.integral_prod_left
  have hBzI : MeasureTheory.Integrable
      (fun z => ∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hBp.integral_prod_left
  have hmono : (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ (∫ z, |β - 1| *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_mono_ae hFz (hBzI.const_mul _) hkey
  have hmono2 : (∫ z, |β - 1| *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = |β - 1| *
          (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_const_mul _ _
  have hAG : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_prod Gp hGp
  have hAB : (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_prod Bp hBp
  have hAGle : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ |β - 1| * (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [hAG, hAB]
    linarith [hmono, hmono2]
  -- identify the two `wip`s with the product integrals
  have h2' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ *
        (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hint2.congr (Filter.Eventually.of_forall (fun p => by
      dsimp only [Function.uncurry]; ring))
  have hIntB : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * Work.FTS.CoercivityFix.Coer1.Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h2'.congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Function.uncurry, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
  have hwipB : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) u u
      = (∫ p, Bp p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [Work.Coercivity.wip_eq_integral_prod (Work.FTS.CoercivityFix.Coer1.Rho β) u u hIntB]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Bp, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
    ring
  have hA' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ
        * Work.FTS.CoercivityFix.Coer1.Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hint.const_mul 3).congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Function.uncurry, Work.Coercivity.Transport, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
    ring
  have hwipA : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β)
        (Work.Coercivity.Transport u) u
      = 3 * (∫ p, Gp p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [Work.Coercivity.wip_eq_integral_prod (Work.FTS.CoercivityFix.Coer1.Rho β)
      (Work.Coercivity.Transport u) u hA']
    rw [show (∫ p, Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2
            * Work.FTS.CoercivityFix.Coer1.Rho β p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ p, 3 * Gp p
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun p => by
          dsimp only [Gp, Work.Coercivity.Transport, Work.FTS.CoercivityFix.Coer1.Rho,
            Work.FTS.CoercivityFix.Coer1.sig]
          ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hwipB, hwipA]
  linarith [hAGle]

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotAmgm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open MeasureTheory

theorem slotAmgm {G X Y Z : ℝ → ℝ → ℝ} {A B : ℝ}
    (hXint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 ^ 2)
      Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm)
    (hYZint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)
      Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm)
    (hXv : (∫ p, G p.1 p.2 * X p.1 p.2 ^ 2
      ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm) ≤ A)
    (hYZv : (∫ p, G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2
      ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm) ≤ B)
    (hA : 0 < A) (hB : 0 < B)
    (hGnn : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm, 0 ≤ G p.1 p.2)
    (hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2)
      Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2)
        Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm ∧
      |∫ p, G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2
        ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm| ≤ Real.sqrt A * Real.sqrt B := by
  classical
  -- the pointwise AM–GM majorant of the product by `(G X² + G Y²Z²)/2`
  have hpt : ∀ᵐ p ∂pm,
      ‖G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2‖
        ≤ (G p.1 p.2 * X p.1 p.2 ^ 2 + G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2) / 2 := by
    filter_upwards [hGnn] with p hp
    have h := pt_le (G p.1 p.2) (X p.1 p.2) (Y p.1 p.2) (Z p.1 p.2) 1 hp (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hp]
    convert h using 1 <;> ring
  have hInt2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (G p.1 p.2 * X p.1 p.2 ^ 2
        + G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2) / 2) pm :=
    (hXint.add hYZint).div_const 2
  have hIntF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) pm :=
    MeasureTheory.Integrable.mono' hInt2 hFmeas hpt
  refine ⟨hIntF, ?_⟩
  -- the optimized AM–GM, integrated
  have key : ∀ lam : ℝ, 0 < lam →
      ∫ p, |G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂pm
        ≤ (lam * A + lam⁻¹ * B) / 2 := by
    intro lam hlam
    have hpt2 : ∀ᵐ p ∂pm,
        |G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2|
          ≤ (lam * (G p.1 p.2 * X p.1 p.2 ^ 2)
              + lam⁻¹ * (G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)) / 2 := by
      filter_upwards [hGnn] with p hp
      have h := pt_le (G p.1 p.2) (X p.1 p.2) (Y p.1 p.2) (Z p.1 p.2) lam hp hlam
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp]
      convert h using 1 <;> ring
    have hInt3 : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (lam * (G p.1 p.2 * X p.1 p.2 ^ 2)
          + lam⁻¹ * (G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)) / 2) pm :=
      ((hXint.const_mul lam).add (hYZint.const_mul lam⁻¹)).div_const 2
    have hmono := MeasureTheory.integral_mono_ae hIntF.abs hInt3 hpt2
    have hval : ∫ p, (lam * (G p.1 p.2 * X p.1 p.2 ^ 2)
          + lam⁻¹ * (G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)) / 2 ∂pm
        = (lam * (∫ p, G p.1 p.2 * X p.1 p.2 ^ 2 ∂pm)
            + lam⁻¹ * (∫ p, G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2 ∂pm)) / 2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add (hXint.const_mul lam) (hYZint.const_mul lam⁻¹),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hval] at hmono
    have h1 : lam * (∫ p, G p.1 p.2 * X p.1 p.2 ^ 2 ∂pm) ≤ lam * A :=
      mul_le_mul_of_nonneg_left hXv hlam.le
    have h2 : lam⁻¹ * (∫ p, G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2 ∂pm) ≤ lam⁻¹ * B :=
      mul_le_mul_of_nonneg_left hYZv (inv_nonneg.mpr hlam.le)
    linarith
  have hlam : 0 < Real.sqrt B / Real.sqrt A :=
    div_pos (Real.sqrt_pos.mpr hB) (Real.sqrt_pos.mpr hA)
  have hk := key (Real.sqrt B / Real.sqrt A) hlam
  have htarget : (Real.sqrt B / Real.sqrt A * A + (Real.sqrt B / Real.sqrt A)⁻¹ * B) / 2
      = Real.sqrt A * Real.sqrt B := by
    rw [inv_div]
    field_simp
    rw [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    ring
  rw [htarget] at hk
  calc |∫ p, G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂pm|
      ≤ ∫ p, |G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂pm :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ Real.sqrt A * Real.sqrt B := hk

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.tracePi4_six =====
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

`SixRoute.tracePi4` proves the trace estimate at `θ = π/4` for the pure `D_z`-slots of
order `j ≤ 2`.  The Morrey argument there is *uniform in the order*: the order enters only
through the pointwise domination of the tangential derivative `∂_θ (D_z^j f)` by the mixed
slot `mixed j 1 f`, together with `w²(mixed j 1 f)² ≤ HkIntegrand α 6 f`, which needs
`1 + j ≤ 6`, i.e. `j ≤ 5`.  This file replays that argument for `j ≤ 5`, which is what the
level-six transport estimates consume (the slots `D_z^5 f` appear in the `ℋ⁶` norm). -/

end
end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

/-- **`|D_z^b f| ≤ 1000 |f|_{𝒲^{6,∞}}` in the `C⁶`-class on the open quadrant.**

For `f` of class `C⁶` on the open quadrant `(0,∞) × (0,π/2)` and of class `𝒲^{6,∞}`, the
iterated radial operator `D_z = z ∂_z` is bounded by `1000 |f|_𝒲` at every interior point,
for `b ≤ 6`.

The proof expands `D_z^b` with the Stirling numbers of the second kind
(`D_z^b = ∑_{k≤b} S(b,k) z^k ∂_z^k`, which needs only `C^b ⊆ C⁶` on the open quadrant —
see `DzIter_eq_sum_scoef_of_contDiffOn_order`), bounds each term `|z^k ∂_z^k f|` by
`|f|_{𝒲^{6,∞}}` (`N6Trans.zpz_le_WlInf6`), and sums the (nonnegative) coefficients with
`Work.Spaces.abs_sum_scoef_mul_le` and the Bell number bound `bell b ≤ 203 ≤ 1000`
(`N6Trans.bell_le_six`). -/
theorem dzIter_le_WlInf6_cd6 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfm : Work.Spaces.WlInfMem α 6 f) {b : ℕ} (hb : b ≤ 6) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨hz, hθ.1, hθ.2⟩
  -- the finite-order hypothesis at the level actually needed
  have hsm : ContDiffOn ℝ ((b : ℕ) : WithTop ℕ∞) (Function.uncurry f)
      Work.FTS.EllipticEst.Q0 := hf.of_le (by exact_mod_cast hb)
  -- the Stirling expansion of `D_z^b`
  have hDz : Work.Spaces.DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) *
          (z ^ k * Work.Spaces.pzIter k f z θ) :=
    DzIter_eq_sum_scoef_of_contDiffOn_order Work.FTS.EllipticEst.isOpen_Q0 b hsm z θ hzθ
  -- the individual terms are bounded by the `𝒲^{6,∞}`-norm
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 6 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => Work.FTS.StrongPersist.N6Trans.zpz_le_WlInf6 hfm (le_trans hk hb) hzI hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 1000 := by
    exact_mod_cast Work.FTS.StrongPersist.N6Trans.bell_le_six b hb
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  calc |Work.Spaces.DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) *
          (z ^ k * Work.Spaces.pzIter k f z θ)| := by rw [hDz]
    _ ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 6 f := hsum
    _ ≤ 1000 * Work.Spaces.WlInf α 6 f := mul_le_mul_of_nonneg_right hbell hW

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.wprod6.mslot_le_winf6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.wprod6

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary angular and weight algebra -/

private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le

/-- The square of the `f`-side angular factor `(α + sin 2θ) sin(2θ)^{α/5}` is
`(α + sin 2θ)² sin(2θ)^{2α/5}`. -/
private theorem phi_sq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

/-- `(α + sin 2θ)² sin(2θ)^{2α/5} ≤ 4` for `0 < α ≤ 1` and `0 < θ < π/2`. -/
private theorem psi2_le_four {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]

/-- On the open quadrant, `(x·W)² = (x·w)² sin(2θ)^{-γ}`. -/
private theorem mul_Wt_sq {α z θ x : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (x * Work.Spaces.Wt α z θ) ^ 2
      = (x * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hstep]
  ring

/-! ## The `g`-side step: the mean-term hypothesis produces the `TW`-block of `GmajW6` -/

private theorem mslot_gside_le6 {α CB : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hgm : Work.Spaces.HkMem α 6 g)
    (hCB : ∀ d : ℕ, d ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
    {d : ℕ} (hd : d ≤ 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (Work.Spaces.DzIter d g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hCBle : CB ≤ max CB 1 := le_max_left CB 1
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTWnn : 0 ≤ Work.FTS.OpenPkg.WProdWin.TW α θ :=
    Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθI
  -- the mean-term block is nonnegative
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
      + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z :=
    add_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc (fun σ _ => sq_nonneg _)))
      (mul_nonneg hγinv (Work.FTS.H2.WPQ.Aang_nonneg α g d z))
  have hg1 : (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      ≤ max CB 1 * ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) :=
    le_trans (hCB d hd z θ hz hθ.1 hθ.2) (mul_le_mul_of_nonneg_right hCBle hX0)
  -- the mean term and the single `Aang` term are both dominated by `HgInt6`/`∑Aang`
  have hmem : d ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hAang_le : Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ d' ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d' z :=
    Finset.single_le_sum (fun d' _ => Work.FTS.H2.WPQ.Aang_nonneg α g d' z) hmem
  have hw : (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z :=
    Work.FTS.StrongPersist.H6Rows.WProd6.w_sq_mul_slice_le_HgInt6 hgm (by omega) hz
  have hXle : (Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z + (Work.Spaces.gam α - 1)⁻¹
          * ∑ d' ∈ Finset.range 6, Work.FTS.H2.WPQ.Aang α g d' z :=
    add_le_add hw (mul_le_mul_of_nonneg_left hAang_le hγinv)
  -- `(D_z^d g · W)² · (α+sin2θ)²sin(2θ)^{2α/5} = (D_z^d g · w)² · TW`
  rw [mul_Wt_sq hθ]
  have hBS : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
      = Work.FTS.OpenPkg.WProdWin.TW α θ := by
    rw [Work.FTS.OpenPkg.WProdWin.TW_eq_mul hθ]; ring
  rw [show ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * ((Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * Work.FTS.OpenPkg.WProdWin.TW α θ from by rw [← hBS]; ring]
  refine le_trans (mul_le_mul_of_nonneg_right hg1 hTWnn) ?_
  have hXTW : ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)
          * Work.FTS.OpenPkg.WProdWin.TW α θ
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    simp only [Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6]
    exact le_trans (mul_le_mul_of_nonneg_right hXle hTWnn)
      (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 6 g z θ))
  calc (max CB 1 * ((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
          * Work.FTS.OpenPkg.WProdWin.TW α θ
      = max CB 1 * (((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)
            * Work.FTS.OpenPkg.WProdWin.TW α θ) := by ring
    _ ≤ max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
        mul_le_mul_of_nonneg_left hXTW hCBB0

/-! ## The mixed slots -/

theorem mslot_le_winf6 (CB : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      (∀ d : ℕ, d ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) →
      ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
  have hCpos : (0 : ℝ) < 2 * 10 ^ 17 * (1 + max CB 1) := by
    have h2 : (0 : ℝ) < 2 * 10 ^ 17 := by norm_num
    have h1 : (1 : ℝ) ≤ max CB 1 := le_max_right CB 1
    have h3 : (0 : ℝ) < 1 + max CB 1 := by linarith
    exact mul_pos h2 h3
  refine ⟨2 * 10 ^ 17 * (1 + max CB 1), hCpos, ?_⟩
  intro α f g hα hα1 hf hfm hg hgm hCB I J hI hIJ z θ hz hθ0 hθ1
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  have hWsq : 0 ≤ (Work.Spaces.WlInf α 6 f) ^ 2 := sq_nonneg _
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ :=
    inv_nonneg.mpr (by rw [Work.Spaces.gam_sub_one]; linarith)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hGnn : 0 ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_nonneg hα g hθI
  have hTWnn : 0 ≤ Work.FTS.OpenPkg.WProdWin.TW α θ :=
    Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hHkG : Work.Spaces.HkIntegrand α 6 g z θ
      ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    Work.FTS.StrongPersist.H6Rows.WProd6.HkIntegrand_le_GmajW6 hα g hθI
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hKper_nn : (0 : ℝ) ≤ 16777216 * 4000000 * (1 + max CB 1) :=
    mul_nonneg (by norm_num) (by linarith)
  have hJ6 : J ≤ 6 := by omega
  have hI6 : I ≤ 6 := by omega
  have hA2nn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  -- Leibniz in the open class
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed J I f g hf hg z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((Work.Spaces.mixed b a f z θ)
        * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) with hYdef
  have hYsplit : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ)
          * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- the pointwise bound for each summand of the double sum
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ (16777216 * 4000000 * (1 + max CB 1))
        * (Work.Spaces.WlInf α 6 f) ^ 2
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 16777216 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 4096 * 4096 :=
            mul_le_mul (Work.FTS.StrongPersist.N6.binom_sq_le_4096 I a (by omega) hI6)
              (Work.FTS.StrongPersist.N6.binom_sq_le_4096 J b (by omega) hJ6)
              (by positivity) (by norm_num)
        _ = 16777216 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    by_cases hlt : a < I
    · -- at least one `θ`-derivative falls on `g`
      have hIa : 1 ≤ I - a := by omega
      have hma : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ 4000000 * (Work.Spaces.WlInf α 6 f) ^ 2 := by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          have h : |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f :=
            Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6 (α := α) (f := f) (b := b)
              (z := z) (θ := θ) hf hfm (by omega) hz hθ
          have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
              ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 := Work.Spaces.sq_le_sq_of_abs_le h
          show (Work.Spaces.DzIter b f z θ) ^ 2 ≤ 4000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          nlinarith [h1, sq_nonneg (1000 * Work.Spaces.WlInf α 6 f),
            sq_nonneg (Work.Spaces.WlInf α 6 f)]
        · have ha1 : 1 ≤ a := by omega
          have h := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 (α := α) (f := f)
            (a := a) (b := b) (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
          calc (Work.Spaces.mixed b a f z θ) ^ 2
              ≤ (1000 * (Work.Spaces.WlInf α 6 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
                Work.Spaces.sq_le_sq_of_abs_le h
            _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
                rw [mul_pow, mul_pow, phi_sq hθ]; ring
            _ ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 * 4 :=
                mul_le_mul_of_nonneg_left (psi2_le_four hα hα1 hθ) (sq_nonneg _)
            _ = 4000000 * (Work.Spaces.WlInf α 6 f) ^ 2 := by ring
      have hmg : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ (I - a) (J - b) hIa (by omega)
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (4000000 * (Work.Spaces.WlInf α 6 f) ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ (4000000 * (Work.Spaces.WlInf α 6 f) ^ 2)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hma (sq_nonneg _)
          _ ≤ (4000000 * (Work.Spaces.WlInf α 6 f) ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ :=
              mul_le_mul_of_nonneg_left hmg (by nlinarith [hWsq])
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 16777216 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 16777216 * ((4000000 * (Work.Spaces.WlInf α 6 f) ^ 2)
              * Work.Spaces.HkIntegrand α 6 g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
            rw [show 16777216 * ((4000000 * (Work.Spaces.WlInf α 6 f) ^ 2)
                  * Work.Spaces.HkIntegrand α 6 g z θ)
                = (16777216 * 4000000 : ℝ) * ((Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.Spaces.HkIntegrand α 6 g z θ) from by ring]
            calc (16777216 * 4000000 : ℝ) * ((Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.Spaces.HkIntegrand α 6 g z θ)
                ≤ (16777216 * 4000000 : ℝ) * ((Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHkG hWsq) (by norm_num)
              _ ≤ (16777216 * 4000000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 6 f) ^ 2
                      * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
                  mul_le_mul_of_nonneg_right (by nlinarith [hCBB0]) (mul_nonneg hWsq hGnn)
              _ = 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
    · -- all `θ`-derivatives fall on `f`: the mean-term hypothesis is used
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hdJ : J - b ≤ 5 := by omega
      have hmb : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        have ha1 : 1 ≤ a := by omega
        have h := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 (α := α) (f := f)
          (a := a) (b := b) (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
        calc (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ (1000 * (Work.Spaces.WlInf α 6 f
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le h
          _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq hθ]; ring
      have hT : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        have he : Work.Spaces.mixed (J - b) (I - a) g = Work.Spaces.DzIter (J - b) g := by
          rw [hsub, Work.Spaces.mixed_zero_right]
        rw [he]
      have hgside : ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
        mslot_gside_le6 (α := α) (CB := CB) (g := g) (d := J - b) hα hgm hCB hdJ hz hθ
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hT]
          _ ≤ ((1000 * Work.Spaces.WlInf α 6 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2
              * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
          _ ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2
                * (max CB 1 * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
              mul_le_mul_of_nonneg_left hgside (sq_nonneg _)
          _ = (1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 16777216 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 16777216 * ((1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
            rw [show 16777216 * ((1000 * Work.Spaces.WlInf α 6 f) ^ 2 * (max CB 1)
                  * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
                = (16777216 * 1000000 * (max CB 1)) * ((Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) from by ring]
            have hAB : (16777216 * 1000000 * (max CB 1) : ℝ)
                ≤ 16777216 * 4000000 * (1 + max CB 1) := by nlinarith [hCBB0]
            calc (16777216 * 1000000 * (max CB 1)) * ((Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
                ≤ (16777216 * 4000000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 6 f) ^ 2
                      * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
                  mul_le_mul_of_nonneg_right hAB (mul_nonneg hWsq hGnn)
              _ = 16777216 * 4000000 * (1 + max CB 1) * (Work.Spaces.WlInf α 6 f) ^ 2
                    * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hIJ49 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 49 := by
    have h1 : (I : ℝ) ≤ 6 := by exact_mod_cast hI6
    have h2 : (J : ℝ) ≤ 6 := by exact_mod_cast hJ6
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
    Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hper a ha b hb))
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
          * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        rw [hsumconst]; ring
    _ ≤ 2401 * ((16777216 * 4000000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hKper_nn hWsq) hGnn)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ49, h0]
    _ ≤ (2 * 10 ^ 17 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
          * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
        rw [show 2401 * ((16777216 * 4000000 * (1 + max CB 1))
              * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
            = (2401 * (16777216 * 4000000 * (1 + max CB 1)))
                * ((Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) from by ring]
        have hle : 2401 * (16777216 * 4000000 * (1 + max CB 1))
            ≤ 2 * 10 ^ 17 * (1 + max CB 1) := by nlinarith [hCBB0]
        calc (2401 * (16777216 * 4000000 * (1 + max CB 1)))
              * ((Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
            ≤ (2 * 10 ^ 17 * (1 + max CB 1))
              * ((Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hWsq hGnn)
          _ = (2 * 10 ^ 17 * (1 + max CB 1)) * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring

end Work.FTS.StrongPersist.H6Rows.wprod6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.slot_prod_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option maxHeartbeats 1600000

/-! ## The a.e. radial slice bound (open twin of `T3BadAux.slot_slice_le_ae`) -/

/-- **The radial slice bound for a.e. angle, honest hypotheses.**  All the slice hypotheses of
`slot_slice_le` hold for a.e. `θ ∈ Iθ`: the two smoothness conditions come from
`SmoothOpen f`/`SmoothOpen g`, the boundary conditions are the hypothesis `htr`, and the three
integrability conditions follow from the product-integrability of `HkIntegrand α 4 g`,
`HkIntegrand α 5 g` and `(Xz α g k)²` together with the pointwise dominations `slot_H1_le`,
`slot_gKprime_le`. -/
theorem slot_slice_le_ae_open {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)|
        ≤ 2 * Mf * ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- a.e. integrability of the radial slices of the `ℋ⁴`/`ℋ⁵` integrands
  have h4 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 4 g z θ)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (integrable_HkIntegrand_prod_open hsg hm4).1
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  have h5 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 5 g z θ)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 g p.1 p.2)
      (integrable_HkIntegrand_prod_open hsg hm5).1
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  have hX2 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.FTS.TransportS.Xz α g k z θ) ^ 2)
        (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.TransportS.ae_integrableOn_slice
      (H := fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      (integrable_Xz_sq_open hsg hm4 k)
    filter_upwards [h] with θ hθ
    exact (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hθ
  filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ, h4, h5, hX2, htr] with
    θ hθ hI4 hI5 hIX2 htrθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hmem : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → z ∈ Work.Spaces.Iz :=
    fun z hz => by simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
  have hfbI : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |f z θ| ≤ Mf :=
    fun z hz => hfb z (hmem z hz) θ hθI
  have hDfbI : ∀ z : ℝ, z ∈ Set.Ioi (0 : ℝ) → |Work.Spaces.Dz f z θ| ≤ Mf :=
    fun z hz => hDfb z (hmem z hz) θ hθI
  -- the two smoothness conditions
  have hφcd : ContDiffOn ℝ 1 (fun z => f z θ) (Set.Ioi (0 : ℝ)) :=
    (hsf.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hucd : ContDiffOn ℝ 1 (fun z => Work.FTS.H2.Thard g k z θ) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.Thard_eq_mixed g k]
    exact ((hsg.mixed (4 - k.val) k.val).curry_z hθ).of_le
      (by simp [Work.Stability.smoothOrder])
  -- the first integrability condition: rewrite `z ∂_z(Thard g k)` as `mixed (5-k) k g`
  have hint1 : MeasureTheory.IntegrableOn (fun z => f z θ * z * (Work.Spaces.w z) ^ 2
      * Work.FTS.H2.Thard g k z θ * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
      (Set.Ioi (0 : ℝ)) := by
    have hEq : (fun z => f z θ * z * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ
        * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        = fun z => f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ
          * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by
      funext z
      have h : z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
          = Work.Spaces.mixed (5 - k.val) k.val g z θ := by
        rw [← Work.FTS.TransportS.Dz_Thard_apply g k z θ]
        rfl
      calc f z θ * z * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ
            * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
          = f z θ * (z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
            * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by ring
        _ = f z θ * Work.Spaces.mixed (5 - k.val) k.val g z θ
            * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.Thard g k z θ := by rw [h]
    rw [hEq]
    refine MeasureTheory.Integrable.mono'
      (((hI4.add hI5).div_const (Work.FTS.H2.sghard α k θ)).const_mul (Mf / 2))
      (Work.FTS.TransportS.T3BadAux.aesm_zslice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
          * (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.Thard g k p.1 p.2)
        (continuousOn_slotH1_Qd_open hsf hsg k) hθ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs]
    exact Work.FTS.TransportS.T3BadAux.slot_H1_le (α := α) (Mf := Mf) hMf k hθ (hfbI z hz)
  -- the second integrability condition
  have hint2 : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.TransportS.gK' α f g k z θ) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      ((hI4.div_const (Work.FTS.H2.sghard α k θ)).const_mul (4 * Mf))
      (Work.FTS.TransportS.T3BadAux.aesm_zslice_of_continuousOn_Qd _
        (continuousOn_gK'_Qd_open hsf hsg k) hθ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs]
    exact Work.FTS.TransportS.T3BadAux.slot_gKprime_le (α := α) (Mf := Mf) hMf k hz hθ
      (hfbI z hz) (hDfbI z hz)
  have hkey : |∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.gK α f g k z θ|
      ≤ 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.FTS.TransportS.Xz α g k z θ) ^ 2 :=
    Work.FTS.TransportS.T3BadAux.slot_slice_le (α := α) (Mf := Mf) (f := f) (g := g) k hMf
      hθ hφcd hucd (fun z hz => hfb z hz θ hθI) (fun z hz => hDfb z hz θ hθI)
      htrθ.1 htrθ.2 hint1 hint2 hIX2
  rw [Work.FTS.TransportS.T3BadAux.restrict_Iz_eq_Ioi]
  exact hkey

/-! ## The product-measure bound -/

theorem slot_prod_le_open {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0)) :
    |∫ p, Work.FTS.TransportS.gK α f g k p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hfb' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ Mf :=
    fun z θ hz hθ hθ' => hfb z (le_of_lt hz) θ ⟨le_of_lt hθ, le_of_lt hθ'⟩
  have hΦ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α f g k p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_gK_open hsf hsg hm5 hMf hfb' k
  have hΨ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_Xz_sq_open hsg hm4 k
  have hΦc : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.FTS.TransportS.gK α f g k z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hΦ
  have hΨc : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.FTS.TransportS.Xz α g k z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hΨ
  have hslice := slot_slice_le_ae_open (α := α) (Mf := Mf) (f := f) (g := g) k hMf
    hsf hsg hm4 hm5 hfb hDfb htr
  have hmΦ : MeasureTheory.Integrable
      (fun θ => ∫ z, Work.FTS.TransportS.gK α f g k z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hΦ.integral_prod_right
  have hmΨ : MeasureTheory.Integrable
      (fun θ => ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hΨ.integral_prod_right
  have hL : (∫ p, Work.FTS.TransportS.gK α f g k p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, ∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integral_integral hΦc).symm.trans
      (MeasureTheory.integral_integral_swap hΦc)
  have hR : (∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ θ, ∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integral_integral hΨc).symm.trans
      (MeasureTheory.integral_integral_swap hΨc)
  rw [hL, ← Real.norm_eq_abs]
  calc ‖∫ θ, ∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖
      ≤ ∫ θ, ‖∫ z, Work.FTS.TransportS.gK α f g k z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ, 2 * Mf * (∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_ae hmΦ.norm (hmΨ.const_mul (2 * Mf)) hslice
    _ = 2 * Mf * ∫ θ, (∫ z, (Work.FTS.TransportS.Xz α g k z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_const_mul (2 * Mf) _
    _ = 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g k p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [hR]

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.L6Aux2 =====
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

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono cs_sqrt_le)


/-! ## The square-root algebra of the slot weights -/


/-! ## Measurability of the slot slices -/



/-! ## The two-dimensional weighted Cauchy–Schwarz -/


end Work.FTS.StrongPersist.N6Trans
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.PairBnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2


/-- A `g`-slot of order `≤ 4` priced at `η` is a canonical slot. -/
theorem slotWo_eta_of {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {j i : ℕ} (hij : i + j ≤ 4) :
    SlotWo α Work.Spaces.eta (Work.Spaces.mixed j i g) g := by
  rcases Nat.eq_zero_or_pos i with hi0 | hip
  · subst hi0
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using
      slotWo_z (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl g j (by omega)
  · exact slotWo_mixed (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos
      (eta_le_gam hα) g j i hip (by omega)

/-- `η < γ` for `α > 0`. -/
theorem eta_lt_gam_of_pos {α : ℝ} (hα : 0 < α) : Work.Spaces.eta < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have : Work.Spaces.eta = 99 / 100 := rfl
  linarith




/-- A pure `D_z`-slot of order `≤ 4` priced at any `0 ≤ q ≤ η`. -/
theorem slotWo_z_le {α q : ℝ} (hqnn : 0 ≤ q) (hq : q ≤ Work.Spaces.eta)
    (g : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) :
    SlotWo α q (Work.Spaces.DzIter j g) g := by
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    exact slotWo_zero_z g j hj
  · exact slotWo_z (α := α) (q := q) hpos hq g j hj

/-- A mixed slot of order `≤ 4` priced at any `0 ≤ q ≤ γ`. -/
theorem slotWo_mixed_le {α q : ℝ} (hα : 0 < α) (hqnn : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α)
    (g : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    SlotWo α q (Work.Spaces.mixed j i g) g := by
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    exact slotWo_zero_mixed hα g j i hi hij
  · exact slotWo_mixed (α := α) (q := q) hpos hqγ g j i hi hij

/-- The slot `mixed b' a g` at the exponent `q`, whose `θ`-order is exactly `a`. -/
theorem slotWo_theta_le {α q : ℝ} {g : ℝ → ℝ → ℝ} {a b' : ℕ}
    (hα : 0 < α) (hqnn : 0 ≤ q)
    (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hab : a + b' ≤ 4) :
    SlotWo α q (Work.Spaces.mixed b' a g) g := by
  rcases eq_or_ne a 0 with ha0 | ha0
  · subst ha0
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using
      slotWo_z_le (α := α) (q := q) hqnn (hq0 rfl) g b' (by omega)
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    exact slotWo_mixed_le (α := α) (q := q) hα hqnn hqγ g b' a ha1 (by omega)

/-- `q ≤ γ` implies `q ≤ 1 + η`. -/
theorem q_le_one_add_eta' {α q : ℝ} (hα1 : α ≤ 1) (hq : q ≤ Work.Spaces.gam α) :
    q ≤ 1 + Work.Spaces.eta := by
  rw [Work.Spaces.gam] at hq
  have : Work.Spaces.eta = 99 / 100 := rfl
  linarith [Work.Spaces.eta_lt_one]

/-- **The pointwise bound of a non-delicate Leibniz summand, general exponent.** -/
theorem termPair_nd' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg) (hqnn : 0 ≤ q)
    (hab : a + b ≤ 4) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) (hp1 : 1 ≤ a1 + b1)
    (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hqcase : q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    (hnd : ¬ (a1 = 0 ∧ b1 = 3 ∧ q = Work.Spaces.gam α))
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
          + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
  intro z θ hz hθ hθ2
  have hHIg : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hSQnn : 0 ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
      * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases Nat.eq_zero_or_pos a1 with ha1z | ha1p
  · subst ha1z
    simp only [Nat.sub_zero]
    by_cases hb12 : b1 ≤ 2
    · have hbnd := canonW_mul_abs_le_slotW (α := α) (q := q) (KF := Mf)
        (X := Work.Spaces.DzIter b1 f)
        (G := Work.Spaces.mixed (b + 1 - b1) a g)
        (Y := Work.Spaces.mixed b a g)
        (slotWo_theta_le hα hqnn hq0 hqγ (by omega))
        (slotWo_theta_le hα hqnn hq0 hqγ (by omega))
        hMf (fun z θ hz hθ hθ2 => hFsup b1 hb12 z θ hz hθ hθ2) z θ hz hθ hθ2
      have h1 : Mf * Work.Spaces.HkIntegrand α 4 g z θ
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        nlinarith [mul_nonneg hMK hHIg, mul_nonneg hMf hHIg, mul_nonneg hMg hSQnn]
      exact le_trans (by simpa only [Work.Spaces.mixed_zero_right] using hbnd) h1
    · have hb13 : 3 ≤ b1 := by omega
      by_cases hqg : q = Work.Spaces.gam α
      · have ha0' : 0 < a := by
          by_contra h
          have h0 : a = 0 := Nat.le_antisymm (le_of_not_gt h) (Nat.zero_le a)
          exact absurd (hq0 h0) (not_le.mpr (hqg ▸ eta_lt_gam_of_pos hα))
        exact absurd ⟨rfl, by omega, hqg⟩ hnd
      · have hqη : q ≤ Work.Spaces.eta := hqcase.resolve_right hqg
        have hmid : a + (b + 1 - b1) ≤ 2 := by omega
        have hFsl : SlotWo α q (Work.Spaces.DzIter b1 f) f := slotWo_z_le hqnn hqη f b1 (by omega)
        have hYsl : SlotWo α q (Work.Spaces.mixed b a g) g :=
          slotWo_theta_le hα hqnn hq0 hqγ (by omega)
        have hGb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            |Work.Spaces.mixed (b + 1 - b1) a g z θ| ≤ Mg :=
          fun z θ hz hθ hθ2 => hGsup (b + 1 - b1) a (by omega) z θ hz hθ hθ2
        have hbnd := canonW_mul_abs_le_slotG (α := α) (q := q) (KG := Mg)
          (F := Work.Spaces.DzIter b1 f)
          (Gm := Work.Spaces.mixed (b + 1 - b1) a g)
          (Y := Work.Spaces.mixed b a g)
          hFsl hYsl hMg hGb z θ hz hθ hθ2
        have h1 : Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
            ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
          have := mul_nonneg (add_nonneg hMf hMK) hHIg
          linarith
        exact le_trans hbnd h1
  · have ha1p1 : 1 ≤ a1 := ha1p
    have ha1pos : 0 < a := by omega
    by_cases hp2 : a1 + b1 ≤ 2
    · have hbnd := canonW_mul_abs_le_slotSigma (α := α) (q := q) (CK := MK)
        (X := Work.Spaces.mixed b1 a1 f)
        (G := Work.Spaces.mixed (b + 1 - b1) (a - a1) g)
        (Y := Work.Spaces.mixed b a g)
        hα hMK (fun z θ hz hθ hθ2 => hFσ b1 a1 ha1p1 hp2 z θ hz hθ hθ2)
        (q_le_one_add_eta' hα1 hqγ)
        (slotWo_eta_of hα (by omega))
        (slotWo_mixed_le (α := α) (q := Work.Spaces.gam α) hα
          (le_of_lt (Work.Spaces.gam_pos hα)) le_rfl g b a (by omega) (by omega))
        z θ hz hθ hθ2
      have h1 : MK * Work.Spaces.HkIntegrand α 4 g z θ
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        nlinarith [mul_nonneg hMK hHIg, mul_nonneg hMf hHIg, mul_nonneg hMg hSQnn]
      exact le_trans hbnd h1
    · have hmid : (a - a1) + (b + 1 - b1) ≤ 2 := by omega
      have hFsl : SlotWo α q (Work.Spaces.mixed b1 a1 f) f :=
        slotWo_mixed_le (α := α) (q := q) hα hqnn hqγ f b1 a1 ha1p1 (by omega)
      have hYsl : SlotWo α q (Work.Spaces.mixed b a g) g :=
        slotWo_mixed_le (α := α) (q := q) hα hqnn hqγ g b a (by omega) (by omega)
      have hbnd := canonW_mul_abs_le_slotG (α := α) (q := q) (KG := Mg)
        (F := Work.Spaces.mixed b1 a1 f)
        (Gm := Work.Spaces.mixed (b + 1 - b1) (a - a1) g)
        (Y := Work.Spaces.mixed b a g)
        hFsl hYsl hMg
        (fun z θ hz hθ hθ2 => hGsup (b + 1 - b1) (a - a1) hmid z θ hz hθ hθ2)
        z θ hz hθ hθ2
      have h1 : Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
            + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        have := mul_nonneg (add_nonneg hMf hMK) hHIg
        linarith
      exact le_trans hbnd h1

end Work.FTS.TransportS.T2Sup
end
end
