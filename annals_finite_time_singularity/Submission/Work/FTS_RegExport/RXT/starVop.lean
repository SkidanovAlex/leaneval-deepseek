import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_Vs0_mul_Gs_eq_zero
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0_interval_lower
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupOpenH2Z
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllSol.EllAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2
local notation "Kθ" => Work.Elliptic.Ktheta
/-! ## Linearity of `L₁₂` -/

/-- Additivity (with a scalar) of `L₁₂` at `z > 0`, from additivity of the densities on
`(0,∞)` and the integrability of the two densities on `(z,∞)`. -/
theorem L12_add_mul {f h : ℝ → ℝ → ℝ} {c z : ℝ} (hz : 0 ≤ z)
    (hd : ∀ s, 0 < s → Work.Elliptic.L12dens (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.L12dens f s + c * Work.Elliptic.L12dens h s)
    (hF : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens f) (Set.Ioi z))
    (hH : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens h) (Set.Ioi z)) :
    Work.Elliptic.L12 (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.L12 f z + c * Work.Elliptic.L12 h z := by
  rw [Work.Elliptic.L12, Work.Elliptic.L12, Work.Elliptic.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => hd s (lt_of_le_of_lt hz hs))]
  rw [MeasureTheory.integral_add hF (hH.const_mul c), MeasureTheory.integral_const_mul]

/-! ## Linearity of `Ḡ` -/

/-- Additivity (with a scalar) of `Ḡ(α,·)` at `z > 0`, from additivity of `F_*` on `(0,∞)` and
the interval integrability of the two integrands on `(0,z)`. -/
theorem Gbar_add_mul {α : ℝ} {f h : ℝ → ℝ → ℝ} {c z : ℝ} (hz : 0 < z)
    (hd : ∀ s, 0 < s → Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.Fstar f s + c * Work.Elliptic.Fstar h s)
    (hf : IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar f s)
      MeasureTheory.volume 0 z)
    (hh : IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar h s)
      MeasureTheory.volume 0 z) :
    Work.Elliptic.Gbar α (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Gbar α f z + c * Work.Elliptic.Gbar α h z := by
  rw [Work.Elliptic.Gbar, Work.Elliptic.Gbar, Work.Elliptic.Gbar]
  have hcongr : (∫ s in (0 : ℝ)..z,
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) s)
      = ∫ s in (0 : ℝ)..z,
          (s ^ ((5 - α) / α) * Work.Elliptic.Fstar f s
            + c * (s ^ ((5 - α) / α) * Work.Elliptic.Fstar h s)) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [hd s (Set.mem_Ioc.mp hs).1]
    ring
  rw [hcongr, intervalIntegral.integral_add hf (hh.const_mul c),
    intervalIntegral.integral_const_mul]
  ring


/-! ## Linearity of the singular term `Gsing` -/


/-! ## Moment of the shifted unknown of a datum of the weak class -/

/-- The angular slice of the unknown of an `EllWeakPos` datum is integrable against
`sinθcos²θ` for every `z > 0`: `HkMem α 0 (∂_θθ·)` together with the two Dirichlet values
bounds the slice (`Endpt.sliceBdd_of_hmB`). -/
theorem EllWeakPos.slice_sinCos2_integrable {α : ℝ} {k : ℕ} {F S : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F S) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => S z θ * sg θ) Iθ := by
  have hso : Work.FTS.EllipticEst.SmoothOpen S :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmem0 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 S) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := k) (by omega)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hso.pth.pth)) h.memB
  exact Work.FTS.EllipticEst.Dispatch.slice_mul_sinCos2_integrableD h.smooth hmem0 hz
    (h.zero z) (h.pi_half z)

/-! ## Closure of the weak class under linear combinations -/

/-- **`EllWeakPos` is closed under linear combinations** (for sources which are `C^∞` on the
open quadrant and whose combination satisfies the solvability condition). -/
theorem EllWeakPos_add_mul {α : ℝ} {k : ℕ} {F F' S S' : ℝ → ℝ → ℝ} {c : ℝ}
    (hsmF : Work.FTS.EllipticEst.SmoothOpen F)
    (hsmF' : Work.FTS.EllipticEst.SmoothOpen F')
    (horth : ∀ z, 0 < z → Work.Elliptic.Fstar (fun z θ => F z θ + c * F' z θ) z = 0)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F S)
    (h' : Work.FTS.EllipticEst.TT.EllWeakPos α k F' S') :
    Work.FTS.EllipticEst.TT.EllWeakPos α k (fun z θ => F z θ + c * F' z θ)
      (fun z θ => S z θ + c * S' z θ) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen S :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hso' : Work.FTS.EllipticEst.SmoothOpen S' :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h'.smooth
  have hcso' : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * S' z θ) := hso'.const_mul' c
  have hcS' : (fun z θ => c * S' z θ) = c • S' := by
    funext z θ; simp only [Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, horth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation
    intro z hz θ h0 h1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
    have hb1 : Work.Elliptic.bslOp α (fun z θ => S z θ + c * S' z θ) z θ
        = Work.Elliptic.bslOp α S z θ
          + Work.Elliptic.bslOp α (fun z θ => c * S' z θ) z θ :=
      Work.Elliptic.bslOp_add α S (fun z θ => c * S' z θ) z θ hcos
        (smoothOpen_contDiffAt_two hso hz h0 h1) (smoothOpen_contDiffAt_two hcso' hz h0 h1)
    have hb2 : Work.Elliptic.bslOp α (fun z θ => c * S' z θ) z θ
        = c * Work.Elliptic.bslOp α S' z θ := by
      have hs := Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul α c S' z θ
      rw [← hcS'] at hs
      exact hs
    rw [hb1, hb2, h.eq z hz θ h0 h1, h'.eq z hz θ h0 h1]
  · intro z; simp only [Pi.add_apply]; rw [h.zero z, h'.zero z]; ring
  · intro z; simp only [Pi.add_apply]; rw [h.pi_half z, h'.pi_half z]; ring
  · -- the moment of the unknown
    intro z hz
    rw [Fstar_add_mul (EllWeakPos.slice_sinCos2_integrable h hz)
      (EllWeakPos.slice_sinCos2_integrable h' hz), h.orthPsi z hz, h'.orthPsi z hz]
    ring
  · -- smoothness
    intro n
    have hfun : Function.uncurry (fun z θ => S z θ + c * S' z θ)
        = Function.uncurry S + c • Function.uncurry S' := by
      funext p
      simp only [Function.uncurry, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact (h.smooth n).add ((h'.smooth n).const_smul c)
  · -- the source, in `ℋ^k`
    exact Work.FTS.LocData.HkMem_const_mul α k c h'.memF |> fun hmem =>
      Work.FTS.EllipticEst.HkMem_add_open hsmF (hsmF'.const_mul' c) h.memF hmem
  · -- `z²∂_z²` of the unknown
    have hlin : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pzIter 2 (fun z θ => S z θ + c * S' z θ) z θ
          = Work.Spaces.pzIter 2 S z θ + c * Work.Spaces.pzIter 2 S' z θ := by
      intro z θ hz h0 h1
      rw [pzIter_add_open (f := S) (g := fun z θ => c * S' z θ) hso hcso' 2 z θ hz h0 h1,
        show Work.Spaces.pzIter 2 (fun z θ => c * S' z θ)
            = c • Work.Spaces.pzIter 2 S' from by rw [hcS', Work.FTS.EllipticEst.pzIter_smul]]
      simp only [Pi.smul_apply, smul_eq_mul]
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (u := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 S z θ
        + c * (z ^ 2 * Work.Spaces.pzIter 2 S' z θ)) ?_ ?_
    · exact Work.FTS.EllipticEst.HkMem_add_open ((hso.pzIter 2).zsq_mul)
        ((hso'.pzIter 2).zsq_mul.const_mul' c) h.memA
        (Work.FTS.LocData.HkMem_const_mul α k c h'.memA)
    · intro z hz θ hθ
      show z ^ 2 * Work.Spaces.pzIter 2 S z θ + c * (z ^ 2 * Work.Spaces.pzIter 2 S' z θ)
        = z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => S z θ + c * S' z θ) z θ
      rw [hlin z θ hz hθ.1 hθ.2]
      ring
  · -- `∂_θ²` of the unknown
    have hlin : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ) z θ
          = Work.Spaces.pthIter 2 S z θ + c * Work.Spaces.pthIter 2 S' z θ := by
      intro z θ hz h0 h1
      rw [Work.FTS.EllipticEst.pthIter_add_of_smoothOpen (f := S)
        (g := fun z θ => c * S' z θ) hso hcso' 2 z θ hz h0 h1,
        show Work.Spaces.pthIter 2 (fun z θ => c * S' z θ)
            = c • Work.Spaces.pthIter 2 S' from by rw [hcS', Work.FTS.EllipticEst.pthIter_smul]]
      simp only [Pi.smul_apply, smul_eq_mul]
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (u := fun z θ => Work.Spaces.pthIter 2 S z θ
        + c * Work.Spaces.pthIter 2 S' z θ) ?_ ?_
    · exact Work.FTS.EllipticEst.HkMem_add_open (hso.pth.pth)
        ((hso'.pth.pth).const_mul' c) h.memB
        (Work.FTS.LocData.HkMem_const_mul α k c h'.memB)
    · intro z hz θ hθ
      show Work.Spaces.pthIter 2 S z θ + c * Work.Spaces.pthIter 2 S' z θ
        = Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ) z θ
      rw [hlin z θ hz hθ.1 hθ.2]
  · -- `z∂_z∂_θ²` of the unknown
    have hlin : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ)) z θ
          = Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
            + c * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ := by
      intro z θ hz h0 h1
      have hloc : Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ)) z θ
          = Work.Spaces.pz (fun z θ => Work.Spaces.pthIter 2 S z θ
              + c * Work.Spaces.pthIter 2 S' z θ) z θ := by
        rw [Work.Spaces.pz, Work.Spaces.pz]
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        have hlin' : ∀ θ', 0 < θ' → θ' < π / 2 →
            Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ) z' θ'
              = Work.Spaces.pthIter 2 S z' θ' + c * Work.Spaces.pthIter 2 S' z' θ' := by
          intro θ' h0' h1'
          rw [Work.FTS.EllipticEst.pthIter_add_of_smoothOpen (f := S)
        (g := fun z θ => c * S' z θ) hso hcso' 2 z' θ' hz' h0' h1',
            show Work.Spaces.pthIter 2 (fun z θ => c * S' z θ)
                = c • Work.Spaces.pthIter 2 S' from by
              rw [hcS', Work.FTS.EllipticEst.pthIter_smul]]
          simp only [Pi.smul_apply, smul_eq_mul]
        exact hlin' θ h0 h1
      rw [hloc, pz_add_open (f := Work.Spaces.pthIter 2 S)
        (g := fun z θ => c * Work.Spaces.pthIter 2 S' z θ)
        (hso.pth.pth) ((hso'.pth.pth).const_mul' c) hz h0 h1]
      rw [show Work.Spaces.pz (fun z θ => c * Work.Spaces.pthIter 2 S' z θ) z θ
          = c * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ from by
        rw [show (fun z θ => c * Work.Spaces.pthIter 2 S' z θ)
            = c • (Work.Spaces.pthIter 2 S') from by
          funext z' θ'; simp only [Pi.smul_apply, smul_eq_mul],
          Work.FTS.EllipticEst.pz_smul]
        simp only [Pi.smul_apply, smul_eq_mul]]
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (u := fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
        + c * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ)) ?_ ?_
    · exact Work.FTS.EllipticEst.HkMem_add_open (smoothOpen_z_mul ((hso.pth.pth).pz))
        ((smoothOpen_z_mul ((hso'.pth.pth).pz)).const_mul' c) h.memZPth2
        (Work.FTS.LocData.HkMem_const_mul α k c h'.memZPth2)
    · intro z hz θ hθ
      show z * Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
          + c * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ)
        = z * Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ)) z θ
      rw [hlin z θ hz hθ.1 hθ.2]
      ring

/-! ## Congruence of the weak class along the open quadrant -/

/-- **`EllWeakPos` only depends on the values on the open quadrant.**  Two data agreeing there
(for the source, the equation transfers by locality of `bslOp`; for the unknown, by the
a.e.-congruence of `F_*` and of the `ℋ^k`-integrands) and having the prescribed Dirichlet
values are simultaneously in the class. -/
theorem EllWeakPos_congr_Q0 {α : ℝ} {k : ℕ} {F F' S S' : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F S)
    (hF : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = F' z θ)
    (hS : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → S z θ = S' z θ)
    (h0 : ∀ z, S' z 0 = 0) (hpi : ∀ z, S' z (π / 2) = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k F' S' := by
  have hQ : EqOn (Function.uncurry S) (Function.uncurry S') Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    show S p.1 p.2 = S' p.1 p.2
    exact hS p.1 p.2 h1 h2 h3
  refine ⟨?_, h0, hpi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation
    intro z hz θ h0' h1'
    have hev : ∀ᶠ q in 𝓝 (z, θ), S' q.1 q.2 = S q.1 q.2 :=
      Filter.eventually_of_mem
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0', h1'⟩))
        (fun q hq => (hQ hq).symm)
    rw [Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq α hev,
      h.eq z hz θ h0' h1']
    exact hF z θ hz h0' h1'
  · -- the moment of the source
    intro z hz
    rw [Fstar_congr_Ioo (f := F') (h := F) (fun θ h0' h1' => (hF z θ hz h0' h1').symm)]
    exact h.orthF z hz
  · -- the moment of the unknown
    intro z hz
    rw [Fstar_congr_Ioo (f := S') (h := S) (fun θ h0' h1' => (hS z θ hz h0' h1').symm)]
    exact h.orthPsi z hz
  · -- smoothness
    intro n
    exact (h.smooth n).congr fun p hp => (hQ hp).symm
  · -- the source, in `ℋ^k`
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memF ?_
    intro z hz θ hθ
    exact hF z θ hz hθ.1 hθ.2
  · -- `z²∂_z²` of the unknown
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memA ?_
    intro z hz θ hθ
    show z ^ 2 * Work.Spaces.pzIter 2 S z θ = z ^ 2 * Work.Spaces.pzIter 2 S' z θ
    rw [pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hQ 2 z θ
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
  · -- `∂_θ²` of the unknown
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memB ?_
    intro z hz θ hθ
    show Work.Spaces.pthIter 2 S z θ = Work.Spaces.pthIter 2 S' z θ
    rw [pthIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hQ 2 z θ
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
  · -- `z∂_z∂_θ²` of the unknown
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memZPth2 ?_
    intro z hz θ hθ
    show z * Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ
    have hEq : EqOn (Function.uncurry (Work.Spaces.pthIter 2 S))
        (Function.uncurry (Work.Spaces.pthIter 2 S')) Work.FTS.EllipticEst.Q0 :=
      fun p hp => pthIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hQ 2 p.1 p.2 hp
    rw [Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]

end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut.TTAuxLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts.TendstoTermsCut.TTAuxLimit`

The four `k → ∞` limits of the doubly truncated `I₁` identity: the radial cut-off `cut k` and the
angular cut-off `SliceMixedAux.cut (1/(k+1))` are removed simultaneously by dominated convergence
on `nuQ`, the untruncated slot being the dominating integrand.

Each proof rewrites the iterated integral of the statement into the product-measure integral
`∫ p, A p ∂nuQ` (Fubini, `MeasureTheory.integral_prod` via `II_eq_integral`), applies the
dominated-convergence limit of `TTAux`, and rewrites the limit value back by Fubini.
-/

namespace Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut
local notation "wt" => Work.Spaces.w
local notation "cwt" => Work.FTS.EllipticEst.AngSecond.cw





end

end Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

/-!
## The endpoint values of the angular slices of `D_z u = z ∂_z u`

For every datum in `AeData` the Dirichlet conditions `u · 0 ≡ 0` and `u · (π/2) ≡ 0` are
imposed for *every* `z`, hence the radial derivative at the two endpoint angles also vanishes:
`z ∂_z u (z,0) = z ∂_z u (z,π/2) = 0`.  These two *values* are the ones the one-dimensional
slice machinery consumes (`slice_ibp_sigma_fts`, `hardy_slice_cos2`, `slice_sharp_bound`), and
they cost nothing — the expensive input there is the *closed-interval* smoothness
`ContDiffOn ℝ 2 (fun θ => z * pz u z θ) (Icc 0 (π/2))`, i.e. the trace of `D_z u`; see
`NOTES_aeMixedAe_mem_ROUTE3.md`.
-/



theorem aeMixedAe_mem : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz := by
  intro α u G hA hU
  exact Work.FTS.EllipticEst.AeCrux.AeMixedAeMemOfCrux hA hU
    (Work.FTS.EllipticEst.AeCrux.AeSliceHonV hA hU)
    (Work.FTS.EllipticEst.AeCrux.AeVGlobalFin2 hA hU)

end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.SharpLocalized =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary arithmetic -/



/-! ## The sharpened localised product bound (localising sum over `b < 4`) -/


end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow15T2Aux.BoundB =====
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
set_option maxHeartbeats 3200000

theorem pzIter_AG_le {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (G15 α Φs)) :
    ∀ (k : ℕ), k ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (AG15 α Φs) z θ|
        ≤ KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
  have hBnn : 0 ≤ Work.Spaces.WlInf α 4 (G15 α Φs) := Work.FTS.H2.WlInf_nonneg hGm
  have hAs : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 2 * C15 α θ) :=
    smoothOpen_A15' α
  intro k hk z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hleib := sqm_pz_DthIter_mul_le_4_open k 0 hk (by norm_num)
    (fun z θ : ℝ => 2 * C15 α θ) (G15 α Φs) hAs hGs z hz θ hθ
  refine le_trans hleib ?_
  have hbase : (0 : ℝ) ≤ KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k :=
    div_nonneg (mul_nonneg (mul_nonneg KA15_pos.le (sq_nonneg α)) hBnn) (pow_pos hz1 k).le
  have hterm : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (0 + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (0 - a) (G15 α Φs)) z θ|
        ≤ KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
    intro c hc a ha
    have ha0 : a = 0 := by
      have h' := Finset.mem_range.mp ha
      omega
    subst ha0
    by_cases hc0 : c = 0
    · subst hc0
      have hA := KA15_bd α hα hα1 0 (by norm_num) θ hθI
      simp only [Function.iterate_zero, id_eq] at hA
      have hG := Work.Spaces.pz_sup_bound α 4 (G15 α Φs) hGm k (by omega) z θ
        (le_of_lt hz) hθI
      have h0 : (0 : ℝ) ≤ KA15 * α ^ 2 := mul_nonneg KA15_pos.le (sq_nonneg α)
      calc |(2 : ℝ) * C15 α θ| * |Work.Spaces.pzIter k (G15 α Φs) z θ|
          ≤ (KA15 * α ^ 2) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
            mul_le_mul hA hG (abs_nonneg _) h0
        _ = KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
            rw [div_eq_mul_inv]; ring_nf
    · have hpz : Work.Spaces.pzIter c (Work.Spaces.DthIter 0 (fun z θ : ℝ => 2 * C15 α θ))
          z θ = 0 := by
        rw [Work.Spaces.DthIter_zero,
          pzIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) c z θ, if_neg hc0]
      rw [hpz]
      simp only [abs_zero, zero_mul]
      exact hbase
  have hS : (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (0 + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (0 - a) (G15 α Φs)) z θ|)
      ≤ (((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
    le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
      (sum_range_range_const k 0 _)
  have hA5 : (((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ) ≤ 5 := by
    have h2 : k + 1 ≤ 5 := by omega
    have h3 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
    have h4 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
    rw [h4, mul_one]
    exact h3
  calc (257 : ℝ) * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (0 + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (0 - a) (G15 α Φs)) z θ|)
      ≤ 257 * ((((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k)) :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
    _ = (257 * ((((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)))
          * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) := by
        rw [div_eq_mul_inv]; ring_nf
    _ ≤ (257 * 5) * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hbase
    _ = KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
        rw [KAG15]; rw [div_eq_mul_inv]; ring_nf

theorem pzIter_DthIter_AG_le {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (G15 α Φs)) :
    ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (AG15 α Φs)) z θ|
        ≤ KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
  have hBnn : 0 ≤ Work.Spaces.WlInf α 4 (G15 α Φs) := Work.FTS.H2.WlInf_nonneg hGm
  have hAs : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 2 * C15 α θ) :=
    smoothOpen_A15' α
  have hC1 : (0 : ℝ) ≤ KA15 + KB15 + 1 := by linarith [KA15_pos, KB15_pos]
  intro j k hj hjk z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hk4 : k ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hsin2 : 0 ≤ Real.sin (2 * θ) := by
    have hs0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθI.1, by linarith [hθI.2, Real.pi_pos]⟩
    have hc0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
    rw [Real.sin_two_mul]; positivity
  have hw0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin2 _)
  have hleib := sqm_pz_DthIter_mul_le_4_open k j hk4 hj4
    (fun z θ : ℝ => 2 * C15 α θ) (G15 α Φs) hAs hGs z hz θ hθ
  refine le_trans hleib ?_
  have hbase : (0 : ℝ) ≤ (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1 hα.le) hBnn) hw0) (pow_pos hz1 k).le
  have hterm : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (j + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|
        ≤ (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
    intro c hc a ha
    have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have ha_le : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    by_cases hc0 : c = 0
    · subst hc0
      rcases eq_or_lt_of_le ha_le with haj | haj
      · -- `a = j`: all angular derivatives on `A` (weighted jet bound)
        rw [haj]
        rw [pzIter_DthIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) j 0 z θ, if_pos rfl,
          Nat.sub_self, Work.Spaces.DthIter_zero]
        have hA := KB15_bd α hα hα1 j (by omega) θ hθI
        have hG := Work.Spaces.pz_sup_bound α 4 (G15 α Φs) hGm k hk4 z θ
          (le_of_lt hz) hθI
        have h0 : (0 : ℝ) ≤ KB15 * α
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_nonneg (mul_nonneg KB15_pos.le hα.le) hw0
        have hstep : |Work.Spaces.dthU^[j] (fun θ => 2 * C15 α θ) θ|
              * |Work.Spaces.pzIter k (G15 α Φs) z θ|
            ≤ (KB15 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
          mul_le_mul hA hG (abs_nonneg _) h0
        have hKBle : KB15 ≤ KA15 + KB15 + 1 := by linarith [KA15_pos]
        have hmono : (KB15 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k)
            ≤ ((KA15 + KB15 + 1) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKBle hα.le) hw0)
            (div_nonneg hBnn (pow_pos hz1 k).le)
        have hfin : ((KA15 + KB15 + 1) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k)
            = (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
          rw [div_eq_mul_inv]; ring_nf
        exact le_trans hstep (le_trans hmono (le_of_eq hfin))
      · -- `a < j`: flat jet bound of `A`, weighted bound of `G`
        rw [pzIter_DthIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) a 0 z θ, if_pos rfl]
        have hja : 1 ≤ j - a := by omega
        have hjk' : k + (j - a) ≤ 4 := by omega
        have hA := KA15_bd α hα hα1 a (by omega) θ hθI
        have hG := Work.Spaces.pz_Dth_sup_bound α hα 4 (G15 α Φs) hGm (j - a) k hja hjk'
          z θ (le_of_lt hz) hθI
        have h0 : (0 : ℝ) ≤ KA15 * α ^ 2 := mul_nonneg KA15_pos.le (sq_nonneg α)
        have h1 : |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ|
              * |Work.Spaces.pzIter k (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|
            ≤ (KA15 * α ^ 2) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul hA hG (abs_nonneg _) h0
        have hX0 : (0 : ℝ) ≤ Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_nonneg (div_nonneg hBnn (pow_pos hz1 k).le) hw0
        have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
        have h2 : (KA15 * α ^ 2) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            ≤ (KA15 * α) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα2 KA15_pos.le) hX0
        have h3 : KA15 ≤ KA15 + KB15 + 1 := by linarith [KB15_pos]
        have h4 : (KA15 * α) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            ≤ ((KA15 + KB15 + 1) * α) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hα.le) hX0
        have hfin : ((KA15 + KB15 + 1) * α)
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            = (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
          rw [div_eq_mul_inv]; ring_nf
        exact le_trans h1 (le_trans h2 (le_trans h4 (le_of_eq hfin)))
    · have hpz : Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ))
          z θ = 0 := by
        rw [pzIter_DthIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) a c z θ, if_neg hc0]
      rw [hpz]
      simp only [abs_zero, zero_mul]
      exact hbase
  have hS : (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|)
      ≤ (((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ)
          * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k) :=
    le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
      (sum_range_range_const k j _)
  have hA5 : (((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ) ≤ 25 := by
    have h2 : k + 1 ≤ 5 := by omega
    have h3 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
    have h4 : j + 1 ≤ 5 := by omega
    have h5 : (((j + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h4
    nlinarith
  calc (257 : ℝ) * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|)
      ≤ 257 * ((((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ)
          * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k)) :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
    _ = (257 * ((((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ)))
          * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k) := by
        rw [div_eq_mul_inv]; ring_nf
    _ ≤ (257 * 25) * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hbase
    _ = KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
        rw [KAGd15]; rw [div_eq_mul_inv]; ring_nf

/-! ## The final arithmetic of the two pointwise bounds -/

theorem arith_hA_core (C K K' : ℝ) (hC : 0 < C) (hK : 0 < K) (hK' : 0 < K') :
    257 * 5 * (C * K) ≤ 200000 * (10 ^ 6 * (C * (K + K' + 1) + 1) + 1) := by
  have hCK : C * K ≤ C * (K + K' + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hK.le, hK'.le]) hC.le
  have h1 : 257 * 5 * (C * K) ≤ 257 * 5 * (C * (K + K' + 1)) :=
    mul_le_mul_of_nonneg_left hCK (by norm_num)
  have hnn : 0 ≤ C * (K + K' + 1) := mul_nonneg hC.le (by linarith [hK.le, hK'.le])
  nlinarith [h1, hnn]

theorem arith_hB_core (C K K' : ℝ) (hC : 0 < C) (hK : 0 < K) (hK' : 0 < K') :
    257 * 25 * (C * K') ≤ 200000 * (10 ^ 6 * (C * (K + K' + 1) + 1) + 1) := by
  have hCK : C * K' ≤ C * (K + K' + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hK.le, hK'.le]) hC.le
  have h1 : 257 * 25 * (C * K') ≤ 257 * 25 * (C * (K + K' + 1)) :=
    mul_le_mul_of_nonneg_left hCK (by norm_num)
  have hnn : 0 ≤ C * (K + K' + 1) := mul_nonneg hC.le (by linarith [hK.le, hK'.le])
  nlinarith [h1, hnn]
end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow19T2Parts.Gam =====
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
set_option maxHeartbeats 3200000

/-- **The (γ)-family**: the weighted `∂_z^l D_θ^i`-bound for `Z₁₉`. -/
theorem Z19_gam_bound {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs))
    (hAmem : Work.Spaces.WlInfMem α 4 (A19 α Φs)) {C2 : ℝ}
    (hC2 : ∀ m j : ℕ, m ≤ 4 → j ≤ m → ∀ z : ℝ, 0 < z →
      (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * |deriv^[j] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2)
    (hC2nn : 0 ≤ C2) :
    ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l
          * Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
        ≤ 200000 * ((CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) * PhiAng α θ) := by
  intro i l hi hli z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hl4 : l ≤ 4 := by omega
  have hi4 : i ≤ 4 := by omega
  have hKsm : Work.FTS.EllipticEst.SmoothOpen (K19 α Φs) := hAsm.mul smoothOpen_H2f
  have hL0 : 0 ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := WlInf_nonneg' α 4 _ hAmem
  have hPhi0 : 0 ≤ PhiAng α θ := PhiAng_nonneg hα hθI
  have hTB0 : 0 ≤ TB19 := TB19_nonneg
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hAraw : (1 + z) * Work.Spaces.w z * z ^ l = (1 + z) ^ 3 * z ^ l / z ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
  have hAraw0 : 0 ≤ (1 + z) ^ 3 * z ^ l / z ^ 2 := by positivity
  have hwnn : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ l := by
    rw [Work.Spaces.w]; positivity
  -- the Leibniz rule
  have hout := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
    (fun z θ => c19 α θ) (K19 α Φs) (smoothOpen_c19 α) hKsm z hz θ hθ
  have hout' : |Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
      ≤ 257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
            * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ| := by
    rw [show Z19 α Φs = (fun z θ => (fun z θ => c19 α θ) z θ * K19 α Φs z θ) from rfl]
    exact hout
  -- the `c19`-factor
  have hfac1 : ∀ c a : ℕ,
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
        ≤ (if c = 0 then |Work.Spaces.dthU^[a] (c19 α) θ| else 0) := by
    intro c a
    rw [Work.FTS.NonlinRows.DthIter_theta_only (c19 α) a,
      Work.FTS.Nonlinear.Open.Row19Prep.pzIter_theta_only]
    simp only []
    by_cases hc0 : c = 0
    · rw [if_pos hc0, if_pos hc0]
    · rw [if_neg hc0, if_neg hc0, abs_zero]
  have hfac1w : ∀ c a : ℕ,
      (1 + z) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
        ≤ |Work.Spaces.dthU^[a] (c19 α) θ| := by
    intro c a
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · subst hc0
      rw [pow_zero, one_mul]
      exact hfac1 0 a
    · have hle : |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ| ≤ 0 :=
        (hfac1 c a).trans (le_of_eq (by
          simp only [if_neg (Nat.pos_iff_ne_zero.mp hcpos)]))
      have hz0 : |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ| = 0 :=
        le_antisymm hle (abs_nonneg _)
      rw [hz0, mul_zero]
      exact abs_nonneg _
  -- the `K19`-factor
  have hfac2 : ∀ c a : ℕ, c ≤ l → a ≤ i →
      |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|
        ≤ 257 * ∑ c' ∈ Finset.range (l - c + 1),
            |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
              * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| :=
    fun c a _ _ => K19_pz_Dth_le hAsm (by omega) (by omega) z hz θ hθ
  -- the angular-jet bounds
  have hdth : ∀ a : ℕ, a ≤ 4 →
      |Work.Spaces.dthU^[a] (c19 α) θ| ≤ 10 * α * (1 + TB19) * Work.Spaces.Gam α θ := by
    intro a ha
    have h1 := dthU_c19_le_MGa hα hα1 ha θ hθI
    have h2 := MGa_le hα.le hα1 a
    have hG := Gam_nonneg' hα hθI
    calc |Work.Spaces.dthU^[a] (c19 α) θ| ≤ 10 * α * MGa α a * Work.Spaces.Gam α θ := h1
      _ ≤ 10 * α * (1 + TB19) * Work.Spaces.Gam α θ := by
          refine mul_le_mul_of_nonneg_right ?_ hG
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hkey : ∀ a : ℕ, a ≤ i →
      |Work.Spaces.dthU^[a] (c19 α) θ| * Psi19 α (i - a) θ
        ≤ 10 * α * (1 + TB19) * PhiAng α θ := by
    intro a hai
    by_cases hia : i - a = 0
    · have haei : a = i := by omega
      have h1 := dthU_c19_le_MGa hα hα1 (show i ≤ 4 by omega) θ hθI
      have h2 : MGa α i = α * TB19 := by
        rw [MGa, if_neg (by omega : i ≠ 0)]
      have h3 : α * Work.Spaces.Gam α θ ≤ PhiAng α θ := alpha_Gam_le_PhiAng hα hθI
      have hG := Gam_nonneg' hα hθI
      rw [Psi19, if_pos hia, mul_one, haei]
      calc |Work.Spaces.dthU^[i] (c19 α) θ| ≤ 10 * α * MGa α i * Work.Spaces.Gam α θ := h1
        _ = 10 * α * TB19 * (α * Work.Spaces.Gam α θ) := by rw [h2]; ring
        _ ≤ 10 * α * TB19 * PhiAng α θ := by
            refine mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ 10 * α * (1 + TB19) * PhiAng α θ := by nlinarith [hTB0, hPhi0, hα]
    · rw [Psi19, if_neg hia]
      have h1 := hdth a (by omega)
      have hG := Gam_le_one' hα hθI
      calc |Work.Spaces.dthU^[a] (c19 α) θ| * PhiAng α θ
          ≤ (10 * α * (1 + TB19) * Work.Spaces.Gam α θ) * PhiAng α θ :=
            mul_le_mul_of_nonneg_right h1 hPhi0
        _ ≤ (10 * α * (1 + TB19) * 1) * PhiAng α θ := by
            refine mul_le_mul_of_nonneg_right ?_ hPhi0
            exact mul_le_mul_of_nonneg_left hG (by positivity)
        _ = 10 * α * (1 + TB19) * PhiAng α θ := by ring
  have hK0 : 0 ≤ (10 * α * (1 + TB19) * PhiAng α θ)
      * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2) :=
    mul_nonneg (by positivity) (mul_nonneg hL0 hC2nn)
  -- the per-term bound
  have hmul : ∀ c a : ℕ, c ≤ l → a ≤ i →
      (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
        ≤ (10 * α * (1 + TB19) * PhiAng α θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by
    intro c a hcl hai
    have hX : (1 + z) ^ c
        * |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
        ≤ |Work.Spaces.dthU^[a] (c19 α) θ| := hfac1w c a
    have hsplit1 : (1 + z) ^ 3 * z ^ l / z ^ 2
        = (1 + z) ^ c * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c) := by
      have hp : (0 : ℝ) < (1 + z) ^ c := pow_pos hz1 _
      exact (mul_div_cancel₀ _ (ne_of_gt hp)).symm
    have hstep1 : (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
        = ((1 + z) ^ c
              * |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|)
            * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|) := by
      nth_rewrite 1 [hsplit1]
      ring
    rw [hstep1]
    have hcw : 0 ≤ (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c := by positivity
    have hY := hfac2 c a hcl hai
    have hYw : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
          * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|
        ≤ 257 * ∑ c' ∈ Finset.range (l - c + 1),
            ((1 + z) ^ c'
                * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
              * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|) := by
      have hmul' := mul_le_mul_of_nonneg_left hY hcw
      refine hmul'.trans (le_of_eq ?_)
      have h1 : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
            * (257 * ∑ c' ∈ Finset.range (l - c + 1),
                |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
          = 257 * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
              * ∑ c' ∈ Finset.range (l - c + 1),
                |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|) := by ring
      rw [h1, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun c' _ => ?_
      have hsp : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
          = (1 + z) ^ c'
              * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')) := by
        have h1 : (1 + z) ^ (c + c') = (1 + z) ^ c * (1 + z) ^ c' := pow_add _ _ _
        rw [h1, mul_div_assoc']
        rw [show (1 + z) ^ c' * ((1 + z) ^ 3 * z ^ l / z ^ 2)
              / ((1 + z) ^ c * (1 + z) ^ c')
            = ((1 + z) ^ 3 * z ^ l / z ^ 2) * (1 + z) ^ c'
              / ((1 + z) ^ c * (1 + z) ^ c') from by ring]
        rw [mul_div_mul_right]
        exact ne_of_gt (pow_pos hz1 c')
      rw [hsp]
      ring
    refine (mul_le_mul hX hYw (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)).trans ?_
    -- now bound `|dthU^a c19| * 257 * Σ_{c'} ((1+z)^{c'}|Y'|)*((A/(1+z)^{c+c'})|Z|)`
    have hsum2 : (∑ c' ∈ Finset.range (l - c + 1),
          ((1 + z) ^ c'
              * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
            * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
        ≤ (((l - c + 1 : ℕ)) : ℝ)
            * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2) := by
      have h1 : ∀ c' ∈ Finset.range (l - c + 1),
          ((1 + z) ^ c'
              * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
            * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
          ≤ (Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2 := by
        intro c' hc'
        rw [Finset.mem_range] at hc'
        have hc'0 : (0 : ℝ) ≤ (1 + z) ^ c' := by positivity
        have hY'' := Work.Spaces.factor_bound α hα (A19 α Φs) hAmem c' (i - a)
          (by omega) (fun _ => by omega) z θ hzI hθI
        have hYabs : |(z + 1) ^ c' * Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
            = (1 + z) ^ c'
                * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ| := by
          rw [show (z : ℝ) + 1 = 1 + z by ring, abs_mul, abs_of_nonneg hc'0]
        rw [hYabs] at hY''
        have hY''' : (1 + z) ^ c'
              * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
            ≤ Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ := by
          simpa only [Psi19, PhiAng] using hY''
        have hZ := hC2 l (l - c - c') hl4 (by omega) z hz
        have hlc : l - (l - c - c') = c + c' := by omega
        rw [hlc] at hZ
        have hZ' : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
            * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2 := by
          rwa [← hAraw]
        exact mul_le_mul hY''' hZ' (mul_nonneg (by positivity) (abs_nonneg _))
          (mul_nonneg hL0 (Psi19_nonneg hα hθI))
      calc (∑ c' ∈ Finset.range (l - c + 1),
            ((1 + z) ^ c'
                * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
              * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
          ≤ ∑ _c' ∈ Finset.range (l - c + 1),
              (Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2 :=
            Finset.sum_le_sum h1
        _ = (((l - c + 1 : ℕ)) : ℝ)
              * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc |Work.Spaces.dthU^[a] (c19 α) θ|
          * (257 * ∑ c' ∈ Finset.range (l - c + 1),
              ((1 + z) ^ c'
                  * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
                * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                    * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
        ≤ |Work.Spaces.dthU^[a] (c19 α) θ|
            * (257 * ((((l - c + 1 : ℕ)) : ℝ)
                * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum2 (by norm_num)) (abs_nonneg _)
      _ ≤ |Work.Spaces.dthU^[a] (c19 α) θ|
            * (257 * (5 * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2))) := by
          have hc : 0 ≤ (Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2 :=
            mul_nonneg (mul_nonneg hL0 (Psi19_nonneg hα hθI)) hC2nn
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ hc
          have : l - c + 1 ≤ 5 := by omega
          exact_mod_cast this
      _ = (|Work.Spaces.dthU^[a] (c19 α) θ| * Psi19 α (i - a) θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by ring
      _ ≤ (10 * α * (1 + TB19) * PhiAng α θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by
          have hc : 0 ≤ 257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)) := by positivity
          exact mul_le_mul_of_nonneg_right (hkey a hai) hc
  -- the sum bounds
  have hsumAB : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|))
      ≤ 125 * ((10 * α * (1 + TB19) * PhiAng α θ)
          * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))) := by
    have hK1 : 0 ≤ (10 * α * (1 + TB19) * PhiAng α θ)
        * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by positivity
    have hstep : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) ^ 3 * z ^ l / z ^ 2
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|))
        ≤ ∑ _c ∈ Finset.range (l + 1), ∑ _a ∈ Finset.range (i + 1),
            (10 * α * (1 + TB19) * PhiAng α θ)
              * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by
      refine Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => ?_
      rw [Finset.mem_range] at hc ha
      exact hmul c a (by omega) (by omega)
    refine hstep.trans ?_
    · have h2 : (∑ _c ∈ Finset.range (l + 1), ∑ _a ∈ Finset.range (i + 1),
          (10 * α * (1 + TB19) * PhiAng α θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))))
          = (((l + 1) * (i + 1) : ℕ) : ℝ)
            * ((10 * α * (1 + TB19) * PhiAng α θ)
              * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))) := by
        rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        push_cast
        ring
      rw [h2]
      refine mul_le_mul_of_nonneg_right ?_ hK1
      have h1 : ((l + 1) * (i + 1) : ℕ) ≤ 25 := by
        have a1 : l + 1 ≤ 5 := by omega
        have a2 : i + 1 ≤ 5 := by omega
        calc (l + 1) * (i + 1) ≤ 5 * 5 := Nat.mul_le_mul a1 a2
          _ = 25 := rfl
      have h2' : (((l + 1) * (i + 1) : ℕ) : ℝ) ≤ 25 := by exact_mod_cast h1
      linarith
  -- assembly
  have h1 : |(1 + z) * Work.Spaces.w z * z ^ l
        * Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
      = (1 + z) ^ 3 * z ^ l / z ^ 2
          * |Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ| := by
    rw [hAraw, abs_mul, abs_of_nonneg hAraw0]
  rw [h1]
  have h2 : (1 + z) ^ 3 * z ^ l / z ^ 2
        * |Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
      ≤ 257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) ^ 3 * z ^ l / z ^ 2
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)) := by
    have hs := mul_le_mul_of_nonneg_left hout' hAraw0
    have he : (1 + z) ^ 3 * z ^ l / z ^ 2
          * (257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
        = 257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
            (1 + z) ^ 3 * z ^ l / z ^ 2
              * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)) := by
      rw [show (1 + z) ^ 3 * z ^ l / z ^ 2
            * (257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
          = 257 * ((1 + z) ^ 3 * z ^ l / z ^ 2
              * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
          from by ring]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
    rw [he] at hs
    exact hs
  refine h2.trans ?_
  have h3 : (257 : ℝ) * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|))
      ≤ 257 * (125 * ((10 * α * (1 + TB19) * PhiAng α θ)
          * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))))) :=
    mul_le_mul_of_nonneg_left hsumAB (by norm_num)
  refine h3.trans ?_
  have h4 : 257 * (125 * ((10 * α * (1 + TB19) * PhiAng α θ)
        * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))))
      ≤ 200000 * ((CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) * PhiAng α θ) := by
    have hcoef : 257 * (125 * (10 * (1 + TB19) * (257 * 5 * C2)))
        ≤ 200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)) := by
      nlinarith [hC2nn, hTB0]
    have hcoef2 : 257 * (125 * ((10 * α * (1 + TB19) * PhiAng α θ)
          * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))))
        = (257 * (125 * (10 * (1 + TB19) * (257 * 5 * C2))))
            * (α * Work.Spaces.WlInf α 4 (A19 α Φs) * PhiAng α θ) := by ring
    have hcoef3 : 200000 * ((CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) * PhiAng α θ)
        = (200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)))
            * (α * Work.Spaces.WlInf α 4 (A19 α Φs) * PhiAng α θ) := by
      rw [CZ19]; ring
    rw [hcoef2, hcoef3]
    exact mul_le_mul_of_nonneg_right hcoef (mul_nonneg (mul_nonneg hα.le hL0) hPhi0)
  exact h4

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Rak =====
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
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Rl0 =====
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
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Rl2 =====
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
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.GsSmoothQuad =====
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

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

/-- `Gs α = D_zF_* = (αΓ(θ)/c)·prof(z)` is `C^∞` on the open quadrant `z > -1`, `0 < θ < π/2`. -/
theorem smoothQuad_Gs_of_pos {α : ℝ} (hα : 0 < α) :
    Work.FTS.LocData.SmoothQuad (Gs α) := by
  have hGam : Work.FTS.LocData.SmoothQuad (fun _ θ => Work.Spaces.Gam α θ) :=
    Work.FTS.LocData.smoothQuad_of_snd (Work.FTS.LocData.contDiffOn_Gam_Ioo α)
  have hprof : Work.FTS.LocData.SmoothQuad proff := smoothQuad_proff
  have h1 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * proff z θ)) :=
    Work.FTS.LocData.smoothQuad_const_mul _
      (Work.FTS.LocData.smoothQuad_mul hGam hprof)
  refine h1.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : (-1 : ℝ) < z := hp.1
  show Gs α z θ = (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ * proff z θ)
  rw [Gs_eq_prof hα hz]
  simp only [prof, proff]
  ring

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Fb_EU_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `SmoothOpen` for the elementary factors -/



theorem smoothOpen_mul_fts {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [h]
  exact hf.mul hg

theorem smoothOpen_add_fts {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  rw [h]
  exact hf.add hg

theorem smoothOpen_const_mul_fts (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => c * f z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

theorem smoothOpen_inv_one_plus_z_fts :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => (1 + z)⁻¹)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => (1 + z)⁻¹) = fun p : ℝ × ℝ => (1 + p.1)⁻¹ := rfl
  rw [h]
  refine ContDiffOn.inv (contDiffOn_const.add contDiffOn_fst) ?_
  intro p hp
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith


/-! ## Locality and the θ-only product -/






/-! ## The arithmetic bookkeeping -/



end Work.FTS.PhiStar.CoreAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Fb_mul_theta_free =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

theorem Fb_mul_theta_free {n : ℕ} {K A : ℝ} {f c : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsc : Work.FTS.EllipticEst.SmoothOpen c)
    (hf : Work.FTS.PhiStar.Fb n K f) (hc : Work.FTS.PhiStar.F0 n A c)
    (hcd : Work.FTS.PhiStar.F0 n A (Work.Spaces.pth c)) :
    Work.FTS.PhiStar.Fb n ((2 : ℝ) ^ (n + 1) * K * A) (fun z θ => f z θ * c z θ) := by
  have hle : (2 : ℝ) ^ n * K * A ≤ (2 : ℝ) ^ (n + 1) * K * A := by
    have hx : (0 : ℝ) ≤ (2 : ℝ) ^ n * K * A :=
      mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) n) hK) hA
    have hpow : (2 : ℝ) ^ (n + 1) * K * A = ((2 : ℝ) ^ n * K * A) * 2 := by
      rw [pow_succ]; ring
    rw [hpow]; linarith
  refine ⟨?_, ?_⟩
  · exact (F0_mul hK hA hsf hsc hf.f0 hc).mono le_rfl hle
  · have h2a : F0 n ((2 : ℝ) ^ n * K * A) (fun z θ => Work.Spaces.pth f z θ * c z θ) :=
      F0_mul hK hA hsf.pth hsc hf.fd hc
    have h2b : F0 n ((2 : ℝ) ^ n * K * A) (fun z θ => f z θ * Work.Spaces.pth c z θ) :=
      F0_mul hK hA hsf hsc.pth hf.f0 hcd
    have hsum : F0 n ((2 : ℝ) ^ n * K * A + (2 : ℝ) ^ n * K * A)
        (fun z θ => Work.Spaces.pth f z θ * c z θ + f z θ * Work.Spaces.pth c z θ) :=
      F0_add (Fbq_smoothOpen_mul hsf.pth hsc) (Fbq_smoothOpen_mul hsf hsc.pth) h2a h2b
    have hconst : (2 : ℝ) ^ n * K * A + (2 : ℝ) ^ n * K * A
        = (2 : ℝ) ^ (n + 1) * K * A := by
      rw [pow_succ]; ring
    exact F0_congr (Fbq_pth_mul hsf hsc) (hsum.mono le_rfl (le_of_eq hconst))

end Work.FTS.PhiStar.CoreAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.F0EPU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.PhiStar.StarPkgo2Aux

open Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Small closures of the smoothness class `SmoothOpen` -/

/-- `SmoothOpen` is closed under pointwise sums. -/
private theorem SmoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
  ContDiffOn.add hf hg

/-- `SmoothOpen` is closed under pointwise products. -/
private theorem SmoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) :=
  ContDiffOn.mul hf hg

/-- Constant functions are `SmoothOpen`. -/
private theorem SmoothOpen_const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => c) :=
  contDiffOn_const

/-- `cos(2θ)` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_cos_two :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos (2 * θ)) := by
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (2 : ℝ) * p.2) :=
    contDiff_const.mul contDiff_snd
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
    Real.contDiff_cos.comp h1
  exact h2.contDiffOn

/-- `sin(2θ)` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_sin_two :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) := by
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (2 : ℝ) * p.2) :=
    contDiff_const.mul contDiff_snd
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.contDiff_sin.comp h1
  exact h2.contDiffOn

/-- `z ↦ (z+1)⁻¹` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_inv_one_add :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1)⁻¹) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 + 1)
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_fst.add contDiff_const).contDiffOn
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (p.1 + 1)⁻¹)
      Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.inv h1 ?_
    intro p hp
    have hz : (0 : ℝ) < p.1 := hp.1
    have hz1 : (0 : ℝ) < p.1 + 1 := by linarith
    exact ne_of_gt hz1
  exact h2

/-- `z ↦ z/(z+1)` is `C^∞` on the open quadrant. -/
private theorem SmoothOpen_z_div :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (z + 1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiff_fst.contDiffOn
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 + 1)
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_fst.add contDiff_const).contDiffOn
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 / (p.1 + 1))
      Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.div h1 h2 ?_
    intro p hp
    have hz : (0 : ℝ) < p.1 := hp.1
    have hz1 : (0 : ℝ) < p.1 + 1 := by linarith
    exact ne_of_gt hz1
  exact h3

/-! ## The flat calculus at the level needed here -/

/-- Products at level `5`: the constant of `F0_mul` is `2^5 = 32` there. -/
private theorem F0_mul5 {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.FTS.PhiStar.F0 5 K f) (hg : Work.FTS.PhiStar.F0 5 K' g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ)
      ∧ Work.FTS.PhiStar.F0 5 (32 * K * K') (fun z θ => f z θ * g z θ) := by
  have h := F0_mul hK hK' hsf hsg hf hg
  have hpow : ((2 : ℝ) ^ 5 * K * K') = 32 * K * K' := by norm_num
  rw [hpow] at h
  exact ⟨SmoothOpen_mul hsf hsg, h⟩

/-- Sums at level `5`, carrying smoothness along. -/
private theorem F0_add5 {K K' : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.FTS.PhiStar.F0 5 K f) (hg : Work.FTS.PhiStar.F0 5 K' g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ)
      ∧ Work.FTS.PhiStar.F0 5 (K + K') (fun z θ => f z θ + g z θ) :=
  ⟨SmoothOpen_add hsf hsg, F0_add hsf hsg hf hg⟩

/-- `z ∂_z` drops one order and multiplies the constant by `6` at level `5`. -/
private theorem F0_zpz5 {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 6 K f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz f z θ)
      ∧ Work.FTS.PhiStar.F0 5 (6 * K) (fun z θ => z * Work.Spaces.pz f z θ) := by
  have h := F0_zpz (n := 5) hK hsf hf
  have h6 : ((5 : ℕ) : ℝ) + 1 = 6 := by norm_num
  refine ⟨hsf.Dz, h.mono (le_refl 5) ?_⟩
  show (((5 : ℕ) : ℝ) + 1) * K ≤ 6 * K
  rw [h6]

/-- Multiplication by a constant, with the constant `32 * |c|` at level `5`. -/
private theorem F0_const_mul5 {c K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 5 K f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ)
      ∧ Work.FTS.PhiStar.F0 5 (32 * |c| * K) (fun z θ => c * f z θ) :=
  F0_mul5 (abs_nonneg c) hK (SmoothOpen_const c) hsf (F0.const 5 c) hf

/-- Multiplication by a nonnegative constant, with the constant `32 * c`. -/
private theorem F0_const_mul5_of_nonneg {c K : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    {f : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hf : Work.FTS.PhiStar.F0 5 K f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ)
      ∧ Work.FTS.PhiStar.F0 5 (32 * c * K) (fun z θ => c * f z θ) := by
  obtain ⟨hs, h⟩ := F0_const_mul5 (c := c) hK hsf hf
  rw [abs_of_nonneg hc] at h
  exact ⟨hs, h⟩

/-- Negation at level `5`, with the constant `32 * K`. -/
private theorem F0_neg5 {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 5 K f) :
    Work.FTS.PhiStar.F0 5 (32 * K) (fun z θ => - f z θ) := by
  obtain ⟨hs, h⟩ := F0_const_mul5 (c := (-1 : ℝ)) hK hsf hf
  have hone : (32 : ℝ) * |(-1 : ℝ)| * K = 32 * K := by
    have habs : |(-1 : ℝ)| = 1 := by rw [abs_neg, abs_one]
    rw [habs]; ring
  rw [hone] at h
  refine F0_congr (fun z θ _ _ _ => ?_) h
  ring

/-! ## The main bound -/

theorem F0EPU : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.F0 5 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EPU α Y) := by
  refine ⟨10000000000, by norm_num, ?_⟩
  intro α K A Y hα hK hA hsY hsq hccs hcos hsin hz1 hinv hY
  -- elementary nonnegativity
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hL0 : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  have hAA0 : (0 : ℝ) ≤ A * A := mul_nonneg hA0 hA0
  have hX0 : (0 : ℝ) ≤ A ^ 2 * K := mul_nonneg (pow_nonneg hA0 2) hK
  -- smoothness of the two `Y`-blocks
  have hsPY : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hsY.pth
  -- the two coefficient functions rewritten in the `z + 1` shape
  have hz1c : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (z + 1)) := by
    refine F0_congr ?_ hz1
    intro z θ hz hθ hθ'
    show z / (z + 1) = z / (1 + z)
    rw [add_comm z 1]
  have hinvc : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (z + 1)⁻¹) := by
    refine F0_congr ?_ hinv
    intro z θ hz hθ hθ'
    show (z + 1)⁻¹ = (1 + z)⁻¹
    rw [add_comm z 1]
  -- level-5 forms
  have hY5 : Work.FTS.PhiStar.F0 5 (A * K) Y := hY.f0.mono (by norm_num) le_rfl
  have hPY5 : Work.FTS.PhiStar.F0 5 (A * K) (Work.Spaces.pth Y) :=
    hY.fd.mono (by norm_num) le_rfl
  have hcos5 : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.cos (2 * θ)) :=
    hcos.mono (by norm_num) le_rfl
  have hsin5 : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.sin (2 * θ)) :=
    hsin.mono (by norm_num) le_rfl
  have hz1c5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => z / (z + 1)) :=
    hz1c.mono (by norm_num) le_rfl
  have hinvc5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => (z + 1)⁻¹) :=
    hinvc.mono (by norm_num) le_rfl
  -- the four `Y`-blocks appearing in `W₁` and in the angular bracket
  obtain ⟨hsV1, hV1⟩ := F0_mul5 hL0 hA0 hsY SmoothOpen_inv_one_add hY5 hinvc5
  obtain ⟨hsV2, hV2⟩ := F0_mul5 hL0 hA0 hsPY SmoothOpen_inv_one_add hPY5 hinvc5
  obtain ⟨hsV3, hV3⟩ := F0_zpz5 hL0 hsY hY.f0
  obtain ⟨hsV4, hV4⟩ := F0_zpz5 hL0 hsPY hY.fd
  obtain ⟨hsV5, hV5⟩ := F0_add5 hsV1 hsV3 hV1 hV3
  obtain ⟨hsV6, hV6⟩ := F0_add5 hsV2 hsV4 hV2 hV4
  have hV5c0 : (0 : ℝ) ≤ 32 * (A * K) * A + 6 * (A * K) := by
    have h1 : (0 : ℝ) ≤ 32 * (A * K) * A := mul_nonneg (mul_nonneg (by norm_num) hL0) hA0
    have h2 : (0 : ℝ) ≤ 6 * (A * K) := mul_nonneg (by norm_num) hL0
    linarith
  obtain ⟨hsV7, hV7⟩ := F0_const_mul5_of_nonneg (c := α) hα hV5c0 hsV5 hV5
  obtain ⟨hsV7d, hV7d⟩ := F0_const_mul5_of_nonneg (c := α) hα hV5c0 hsV6 hV6
  obtain ⟨hsV8, hV8⟩ := F0_const_mul5_of_nonneg (c := (3 : ℝ)) (by norm_num) hL0 hsY hY5
  obtain ⟨hsV8d, hV8d⟩ := F0_const_mul5_of_nonneg (c := (3 : ℝ)) (by norm_num) hL0 hsPY hPY5
  -- `W₁` and the angular bracket, at level `5`
  obtain ⟨hsW, hW⟩ := F0_add5 hsV8 hsV7 hV8 hV7
  obtain ⟨hsU, hU⟩ := F0_add5 hsV8d hsV7d hV8d hV7d
  -- the bound `Kw ≤ (96 + 1216α) A²K` for the common constant `Kw`
  have hA2le : A ≤ A ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hA hA0
    simpa [pow_two] using h
  have hAK : A * K ≤ A ^ 2 * K := mul_le_mul_of_nonneg_right hA2le hK
  have hinner : 32 * (A * K) * A + 6 * (A * K) ≤ 38 * (A ^ 2 * K) := by
    have h1 : 32 * (A * K) * A = 32 * (A ^ 2 * K) := by ring
    have h2 : 6 * (A * K) ≤ 6 * (A ^ 2 * K) :=
      mul_le_mul_of_nonneg_left hAK (by norm_num)
    rw [h1]
    linarith [h2]
  have hKw : 32 * 3 * (A * K) + 32 * α * (32 * (A * K) * A + 6 * (A * K))
      ≤ (96 + 1216 * α) * (A ^ 2 * K) := by
    have h8 : 32 * 3 * (A * K) ≤ 96 * (A ^ 2 * K) := by
      have h : (32 : ℝ) * 3 * (A * K) = 96 * (A * K) := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_left hAK (by norm_num)
    have h32a : (0 : ℝ) ≤ 32 * α := by linarith
    have h3 : 32 * α * (32 * (A * K) * A + 6 * (A * K))
        ≤ 32 * α * (38 * (A ^ 2 * K)) :=
      mul_le_mul_of_nonneg_left hinner h32a
    have h3' : (32 : ℝ) * α * (38 * (A ^ 2 * K)) = 1216 * α * (A ^ 2 * K) := by ring
    rw [h3'] at h3
    have hsum := add_le_add h8 h3
    have heq : 96 * (A ^ 2 * K) + 1216 * α * (A ^ 2 * K)
        = (96 + 1216 * α) * (A ^ 2 * K) := by ring
    rw [heq] at hsum
    exact hsum
  have hKW : 32 * 3 * (A * K) + 32 * α * (32 * (A * K) * A + 6 * (A * K))
      ≤ 1312 * (α + 1) * (A ^ 2 * K) := by
    have hcoef : (96 + 1216 * α) ≤ 1312 * (α + 1) := by linarith
    have h2 := mul_le_mul_of_nonneg_right hcoef hX0
    calc 32 * 3 * (A * K) + 32 * α * (32 * (A * K) * A + 6 * (A * K))
        ≤ (96 + 1216 * α) * (A ^ 2 * K) := hKw
      _ ≤ 1312 * (α + 1) * (A ^ 2 * K) := h2
  have hW2 : Work.FTS.PhiStar.F0 5 (1312 * (α + 1) * (A ^ 2 * K))
      (fun z θ => 3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) :=
    hW.mono (le_refl 5) hKW
  have hU2 : Work.FTS.PhiStar.F0 5 (1312 * (α + 1) * (A ^ 2 * K))
      (fun z θ => 3 * Work.Spaces.pth Y z θ
        + α * (Work.Spaces.pth Y z θ * (z + 1)⁻¹
          + z * Work.Spaces.pz (Work.Spaces.pth Y) z θ)) :=
    hU.mono (le_refl 5) hKW
  -- the coefficient factors
  have hAA32 : (0 : ℝ) ≤ 32 * A * A := mul_nonneg (mul_nonneg (by norm_num) hA0) hA0
  have hE1c0 : (0 : ℝ) ≤ 32 * 2 * (32 * A * A) := mul_nonneg (by norm_num) hAA32
  have hCα0 : (0 : ℝ) ≤ 1312 * (α + 1) * (A ^ 2 * K) := by
    have h1 : (0 : ℝ) ≤ 1312 * (α + 1) :=
      mul_nonneg (by norm_num) (by linarith : (0 : ℝ) ≤ α + 1)
    exact mul_nonneg h1 hX0
  obtain ⟨hsG1, hG1⟩ := F0_mul5 hA0 hA0 SmoothOpen_cos_two SmoothOpen_z_div hcos5 hz1c5
  obtain ⟨hsE1, hE1⟩ := F0_const_mul5_of_nonneg (c := (2 : ℝ)) (by norm_num) hAA32 hsG1 hG1
  obtain ⟨hsG2, hG2⟩ := F0_mul5 hA0 hA0 SmoothOpen_sin_two SmoothOpen_z_div hsin5 hz1c5
  -- the two big products
  obtain ⟨hsP, hP⟩ := F0_mul5 hE1c0 hCα0 hsE1 hsW hE1 hW2
  obtain ⟨hsQ, hQ⟩ := F0_mul5 hAA32 hCα0 hsG2 hsU hG2 hU2
  obtain ⟨hsPQ, hPQ⟩ := F0_add5 hsP hsQ hP hQ
  have hPQ0 : (0 : ℝ) ≤ 32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
      + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)) := by
    have h1 : (0 : ℝ) ≤ 32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K)) :=
      mul_nonneg (mul_nonneg (by norm_num) hE1c0) hCα0
    have h2 : (0 : ℝ) ≤ 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)) :=
      mul_nonneg (mul_nonneg (by norm_num) hAA32) hCα0
    linarith
  have hN := F0_neg5 hPQ0 hsPQ hPQ
  -- unfold the definitions and identify the expression with `EPU α Y`
  have hFinal : Work.FTS.PhiStar.F0 5
      (32 * (32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
        + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K))))
      (Work.FTS.PhiStar.EPU α Y) := by
    refine F0_congr ?_ hN
    intro z θ hz hθ hθ'
    simp only [Work.FTS.PhiStar.EPU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk,
      Work.Construction.s2, div_eq_mul_inv]
    ring
  -- the numerical bound on the accumulated constant
  have hbound : 32 * (32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
        + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)))
      ≤ 10000000000 * A ^ 4 * K * (α + 1) := by
    have hnn : (0 : ℝ) ≤ (α + 1) * A ^ 4 * K :=
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ α + 1) (pow_nonneg hA0 4)) hK
    have hbig : (2794455040 : ℝ) ≤ 10000000000 := by norm_num
    calc 32 * (32 * (32 * 2 * (32 * A * A)) * (1312 * (α + 1) * (A ^ 2 * K))
            + 32 * (32 * A * A) * (1312 * (α + 1) * (A ^ 2 * K)))
        = 2794455040 * ((α + 1) * A ^ 4 * K) := by ring
      _ ≤ 10000000000 * ((α + 1) * A ^ 4 * K) := mul_le_mul_of_nonneg_right hbig hnn
      _ = 10000000000 * A ^ 4 * K * (α + 1) := by ring
  exact hFinal.mono (le_refl 5) hbound

end Work.FTS.PhiStar.StarPkgo2Aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.FbEH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.StarPkgo2Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Work.FTS.PhiStar.CoreAux

/-! ## Local vocabulary

The coefficient functions and the `Y`-blocks occurring in `EH`, together with the three
summands `EH1`, `EH2`, `EH3` of `EH α Y` and the terms of `∂_θ(EH α Y)`. -/

/-- The angular coefficient `sin²θ`. -/
private def Sqs : ℝ → ℝ → ℝ := fun _ θ => Real.sin θ ^ 2

/-- The angular coefficient `sin 2θ`. -/
private def Sin2 : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- The radial coefficient `(z+1)⁻¹`. -/
private def Rho : ℝ → ℝ → ℝ := fun z _ => (z + 1)⁻¹

/-- `∂_θ(sin²θ) = 2 sinθ cosθ`. -/
private def DSq : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.sin θ * Real.cos θ

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
private def DCos2 : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.cos (2 * θ)

/-- `Y·(z+1)⁻¹`. -/
private def Yrho (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Y z θ * Rho z θ

/-- `Y/(z+1) + D_zY`. -/
private def Zfun (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Yrho Y z θ + Yblk Y z θ

/-- `sin²θ·(Y/(z+1) + D_zY)`. -/
private def Gfun (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Sqs z θ * Zfun Y z θ

/-- The first summand `2Y` of `EH`. -/
private def EH1 (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => 2 * Y z θ

/-- The second summand `2α sin²θ (Y/(z+1) + D_zY)` of `EH`. -/
private def EH2 (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (2 * α) * Gfun Y z θ

/-- The third summand `D_θY = sin(2θ)∂_θY` of `EH`. -/
private def EH3 (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Sin2 z θ * Work.Spaces.pth Y z θ

/-- `EH1 + EH2`. -/
private def EH12 (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => EH1 Y z θ + EH2 α Y z θ

/-- The `∂_θ`-expansion of the middle summand of `EH α Y` (after the product rules). -/
private def Inner (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
    DSq z θ * Zfun Y z θ
      + (Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
          + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ)

/-- The explicit expression for `∂_θ(EH α Y)` on the open quadrant. -/
private def Dsum (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
    2 * Work.Spaces.pth Y z θ + (2 * α) * Inner Y z θ
      + (DCos2 z θ * Work.Spaces.pth Y z θ + Work.Spaces.Dth (Work.Spaces.pth Y) z θ)

/-! ## Smoothness of the coefficient functions -/

private theorem smooth_Sqs : EllipticEst.SmoothOpen Sqs := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry Sqs = fun p : ℝ × ℝ => Real.sin p.2 ^ 2 := rfl
  rw [h]
  fun_prop

private theorem smooth_Sin2 : EllipticEst.SmoothOpen Sin2 := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry Sin2 = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
  rw [h]
  fun_prop

private theorem smooth_Rho : EllipticEst.SmoothOpen Rho := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry Rho = fun p : ℝ × ℝ => (p.1 + 1)⁻¹ := rfl
  rw [h]
  exact ContDiffOn.inv (contDiffOn_fst.add contDiffOn_const) (fun p hp => by
    have h1 : (0 : ℝ) < p.1 := (EllipticEst.mem_Q0.mp hp).1
    positivity)

private theorem smooth_DSq : EllipticEst.SmoothOpen DSq := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry DSq = fun p : ℝ × ℝ => 2 * Real.sin p.2 * Real.cos p.2 := rfl
  rw [h]
  fun_prop

private theorem smooth_DCos2 : EllipticEst.SmoothOpen DCos2 := by
  refine EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry DCos2 = fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2) := rfl
  rw [h]
  fun_prop

/-! ## The three `θ`-derivative identities -/

private theorem pth_Sqs : ∀ z θ : ℝ, Work.Spaces.pth Sqs z θ = DSq z θ := by
  intro z θ
  have h := (Real.hasDerivAt_sin θ).pow 2
  show deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ
  rw [show (fun θ' : ℝ => Real.sin θ' ^ 2) = Real.sin ^ 2 from rfl, h.deriv]
  norm_num

private theorem pth_Rho : ∀ z θ : ℝ, Work.Spaces.pth Rho z θ = 0 := by
  intro z θ
  show deriv (fun _ : ℝ => (z + 1)⁻¹) θ = 0
  exact deriv_const θ _

private theorem pth_Sin2 : ∀ z θ : ℝ, Work.Spaces.pth Sin2 z θ = DCos2 z θ := by
  intro z θ
  have hinner : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    have h := (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa only [id_eq, mul_one] using h
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ hinner
  show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
  rw [show (fun θ' : ℝ => Real.sin (2 * θ')) = (Real.sin ∘ fun θ' : ℝ => 2 * θ') from rfl,
    h.deriv]
  ring

/-! ## Absorption of the constants

Every piece of the computation has a constant of the form `c·A^p·K` (or `c·α·A^p·K`) with
`p ≤ 4`; these lemmas show that such a piece is dominated by `c·A⁴K(α+1)`, using `A ≥ 1`,
`K ≥ 0`, `α ≥ 0`. -/

private theorem absorb_le {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) (hc : 0 ≤ c)
    {p : ℕ} (hp : p ≤ 4) : c * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hp4 : A ^ p ≤ A ^ 4 := pow_le_pow_right₀ hA hp
  have hA4K : (0 : ℝ) ≤ A ^ 4 * K := mul_nonneg (pow_nonneg hA0 4) hK
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) := mul_nonneg hA4K (by linarith)
  have h1 : c * A ^ p * K ≤ c * A ^ 4 * K := by
    refine mul_le_mul_of_nonneg_right ?_ hK
    exact mul_le_mul_of_nonneg_left hp4 hc
  have h2 : c * (A ^ 4 * K) ≤ c * (A ^ 4 * K * (α + 1)) := by
    have hα1 : (1 : ℝ) ≤ α + 1 := by linarith
    calc c * (A ^ 4 * K) = c * (A ^ 4 * K) * 1 := by ring
      _ ≤ c * (A ^ 4 * K) * (α + 1) := mul_le_mul_of_nonneg_left hα1 (mul_nonneg hc hA4K)
      _ = c * (A ^ 4 * K * (α + 1)) := by ring
  linarith

private theorem absorb_le_alpha {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hc : 0 ≤ c) {p : ℕ} (hp : p ≤ 4) :
    c * α * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hp4 : A ^ p ≤ A ^ 4 := pow_le_pow_right₀ hA hp
  have hA4K : (0 : ℝ) ≤ A ^ 4 * K := mul_nonneg (pow_nonneg hA0 4) hK
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) := mul_nonneg hA4K hα1
  have hstep1 : c * α * A ^ p * K ≤ c * A ^ p * K * (α + 1) := by
    have hle : α ≤ α + 1 := by linarith
    have h0 : (0 : ℝ) ≤ c * A ^ p * K := mul_nonneg (mul_nonneg hc (pow_nonneg hA0 p)) hK
    calc c * α * A ^ p * K = (c * A ^ p * K) * α := by ring
      _ ≤ (c * A ^ p * K) * (α + 1) := mul_le_mul_of_nonneg_left hle h0
      _ = c * A ^ p * K * (α + 1) := by ring
  have hstep2 : c * A ^ p * K * (α + 1) ≤ c * (A ^ 4 * K * (α + 1)) := by
    have h : A ^ p * K * (α + 1) ≤ A ^ 4 * K * (α + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp4 hK) hα1
    calc c * A ^ p * K * (α + 1) = c * (A ^ p * K * (α + 1)) := by ring
      _ ≤ c * (A ^ 4 * K * (α + 1)) := mul_le_mul_of_nonneg_left h hc
  linarith

/-- `2α·(256 A³K + 80 A²K) ≤ 1000·A⁴K(α+1)`. -/
private theorem alpha_one {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) :
    2 * α * (256 * A ^ 3 * K + 80 * A ^ 2 * K) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  have h1 : 512 * α * A ^ 3 * K ≤ 512 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 512) (by norm_num) (p := 3) (by norm_num)
  have h2 : 160 * α * A ^ 3 * K ≤ 160 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 160) (by norm_num) (p := 3) (by norm_num)
  have hA23 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA (by norm_num)
  have hstep : 80 * (α * K) * A ^ 2 ≤ 80 * (α * K) * A ^ 3 :=
    mul_le_mul_of_nonneg_left hA23 (mul_nonneg (by norm_num) (mul_nonneg hα hK))
  nlinarith [h1, h2, hstep, hM]

/-- `2α·((256 A³K + 80 A²K) + (256 A³K + 80 A²K)) ≤ 2000·A⁴K(α+1)`. -/
private theorem alpha_pair {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) :
    2 * α * ((256 * A ^ 3 * K + 80 * A ^ 2 * K) + (256 * A ^ 3 * K + 80 * A ^ 2 * K))
      ≤ 2000 * (A ^ 4 * K * (α + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hM : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  have h1 : 1024 * α * A ^ 3 * K ≤ 1024 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 1024) (by norm_num) (p := 3) (by norm_num)
  have h2 : 320 * α * A ^ 3 * K ≤ 320 * (A ^ 4 * K * (α + 1)) :=
    absorb_le_alpha hA hK hα (c := 320) (by norm_num) (p := 3) (by norm_num)
  have hA23 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA (by norm_num)
  have hstep : 160 * (α * K) * A ^ 2 ≤ 160 * (α * K) * A ^ 3 :=
    mul_le_mul_of_nonneg_left hA23 (mul_nonneg (by norm_num) (mul_nonneg hα hK))
  nlinarith [h1, h2, hstep, hM]

/-! ## The sum decomposition of `EH α Y` -/

private theorem EH_split {α : ℝ} {Y : ℝ → ℝ → ℝ} (z θ : ℝ) :
    EH α Y z θ = EH12 α Y z θ + EH3 Y z θ := by
  simp only [EH, EH12, EH1, EH2, EH3, Gfun, Zfun, Yrho, Sqs, Rho, Sin2, Tblk,
    Work.Construction.s2]
  ring

/-! ## The `∂_θ`-identity -/

/-- **The explicit form of `∂_θ(EH α Y)` on the open quadrant.**  The right-hand side `Dsum`
is the sum that the product rules produce: the `∂_θ` of `2Y`, of `2α sin²θ(Y/(z+1)+D_zY)`
(four terms) and of `sin(2θ)∂_θY` (two terms). -/
private theorem pth_EH_eq {α : ℝ} {Y : ℝ → ℝ → ℝ} (hYs : EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EH α Y) z θ = Dsum α Y z θ := by
  intro z θ hz hθ hθ'
  have sSqs : EllipticEst.SmoothOpen Sqs := smooth_Sqs
  have sSin : EllipticEst.SmoothOpen Sin2 := smooth_Sin2
  have sRho : EllipticEst.SmoothOpen Rho := smooth_Rho
  have sYrho : EllipticEst.SmoothOpen (Yrho Y) := Fbq_smoothOpen_mul hYs sRho
  have sYblk : EllipticEst.SmoothOpen (Yblk Y) := hYs.Dz
  have sZ : EllipticEst.SmoothOpen (Zfun Y) := SmoothOpen.add sYrho sYblk
  have sG : EllipticEst.SmoothOpen (Gfun Y) := Fbq_smoothOpen_mul sSqs sZ
  have sPY : EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hYs.pth
  have sEH1 : EllipticEst.SmoothOpen (EH1 Y) := SmoothOpen.const_mul hYs 2
  have sEH2 : EllipticEst.SmoothOpen (EH2 α Y) := SmoothOpen.const_mul sG (2 * α)
  have sEH3 : EllipticEst.SmoothOpen (EH3 Y) := Fbq_smoothOpen_mul sSin sPY
  have sEH12 : EllipticEst.SmoothOpen (EH12 α Y) := SmoothOpen.add sEH1 sEH2
  have hsplit : EH α Y = fun z θ => EH12 α Y z θ + EH3 Y z θ := by
    funext a b
    exact EH_split a b
  rw [hsplit]
  rw [show Work.Spaces.pth (fun z θ => EH12 α Y z θ + EH3 Y z θ) z θ
        = Work.Spaces.pth (EH12 α Y) z θ + Work.Spaces.pth (EH3 Y) z θ from
      pth_add_Q0 (f := EH12 α Y) (g := EH3 Y) sEH12 sEH3 z θ hz hθ hθ']
  rw [show Work.Spaces.pth (EH12 α Y) z θ
        = Work.Spaces.pth (EH1 Y) z θ + Work.Spaces.pth (EH2 α Y) z θ from
      pth_add_Q0 (f := EH1 Y) (g := EH2 α Y) sEH1 sEH2 z θ hz hθ hθ']
  rw [show Work.Spaces.pth (EH1 Y) z θ = 2 * Work.Spaces.pth Y z θ from
      congrFun (congrFun (pth_const_mul (2 : ℝ) Y) z) θ]
  rw [show Work.Spaces.pth (EH2 α Y) z θ = (2 * α) * Work.Spaces.pth (Gfun Y) z θ from
      congrFun (congrFun (pth_const_mul (2 * α) (Gfun Y)) z) θ]
  rw [show Work.Spaces.pth (Gfun Y) z θ
        = Work.Spaces.pth Sqs z θ * Zfun Y z θ
          + Sqs z θ * Work.Spaces.pth (Zfun Y) z θ from
      Fbq_pth_mul (f := Sqs) (g := Zfun Y) sSqs sZ z θ hz hθ hθ']
  rw [show Work.Spaces.pth (Zfun Y) z θ
        = Work.Spaces.pth (Yrho Y) z θ + Work.Spaces.pth (Yblk Y) z θ from
      pth_add_Q0 (f := Yrho Y) (g := Yblk Y) sYrho sYblk z θ hz hθ hθ']
  rw [show Work.Spaces.pth (Yrho Y) z θ = Work.Spaces.pth Y z θ * Rho z θ from by
    show Work.Spaces.pth (fun z θ => Y z θ * Rho z θ) z θ
        = Work.Spaces.pth Y z θ * Rho z θ
    rw [Fbq_pth_mul (f := Y) (g := Rho) hYs sRho z θ hz hθ hθ', pth_Rho z θ,
      mul_zero, add_zero]]
  rw [show Work.Spaces.pth (Yblk Y) z θ = Yblk (Work.Spaces.pth Y) z θ from
      pth_zpz_smoothOpen hYs z θ hz hθ hθ']
  rw [show Work.Spaces.pth (EH3 Y) z θ
        = Work.Spaces.pth Sin2 z θ * Work.Spaces.pth Y z θ
          + Sin2 z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ from
      Fbq_pth_mul (f := Sin2) (g := Work.Spaces.pth Y) sSin sPY z θ hz hθ hθ']
  rw [pth_Sqs z θ, pth_Sin2 z θ]
  simp only [Dsum, Inner, Zfun, Yrho, Sqs, Sin2, DSq, DCos2, Rho, Work.Spaces.Dth]
  ring

/-! ## The main bound -/

private theorem FbEH_aux {α K A : ℝ} {Y : ℝ → ℝ → ℝ}
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hA : 1 ≤ A) (hYs : EllipticEst.SmoothOpen Y)
    (hsq : F0 6 A Sqs) (hc2 : F0 6 A (fun _ θ => Real.cos (2 * θ)))
    (hsi : F0 6 A Sin2) (hci : F0 6 A (fun z _ => (1 + z)⁻¹)) (hY : Fb 6 (A * K) Y) :
    Fb 4 (10 ^ 7 * A ^ 4 * K * (α + 1)) (EH α Y) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hAK : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  have hM00 : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  set M : ℝ := A ^ 4 * K * (α + 1) with hM
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; exact hM00
  -- ## the coefficient data
  have hRho6 : F0 6 A Rho := F0_congr (fun z θ _ _ _ => by
    show (z + 1)⁻¹ = (1 + z)⁻¹
    rw [add_comm 1 z]) hci
  have hRho4 : F0 4 A Rho := hRho6.mono (by norm_num) le_rfl
  have hSqs4 : F0 4 A Sqs := hsq.mono (by norm_num) le_rfl
  have hSin4 : F0 4 A Sin2 := hsi.mono (by norm_num) le_rfl
  have hCos24 : F0 4 A (fun _ θ => Real.cos (2 * θ)) := hc2.mono (by norm_num) le_rfl
  have hDSq6 : F0 6 A DSq := F0_congr (fun z θ _ _ _ => by
    show 2 * Real.sin θ * Real.cos θ = Real.sin (2 * θ)
    rw [Real.sin_two_mul]) hsi
  have hDSq4 : F0 4 A DSq := hDSq6.mono (by norm_num) le_rfl
  have hDCos2 : F0 4 (2 * A) DCos2 := by
    have h := F0_const_mul (2 : ℝ) hCos24
    have hc : |(2 : ℝ)| * A = 2 * A := by norm_num
    rw [hc] at h
    exact h
  have hY4 : Fb 4 (A * K) Y := hY.mono (by norm_num) le_rfl
  have hY5f0 : F0 5 (A * K) Y := hY.f0.mono (by norm_num) le_rfl
  have hPY4 : F0 4 (A * K) (Work.Spaces.pth Y) := hY4.fd
  have hPY5 : F0 5 (A * K) (Work.Spaces.pth Y) := hY.fd.mono (by norm_num) le_rfl
  -- ## smoothness
  have sRho : EllipticEst.SmoothOpen Rho := smooth_Rho
  have sSqs : EllipticEst.SmoothOpen Sqs := smooth_Sqs
  have sSin : EllipticEst.SmoothOpen Sin2 := smooth_Sin2
  have sDSq : EllipticEst.SmoothOpen DSq := smooth_DSq
  have sDCos2 : EllipticEst.SmoothOpen DCos2 := smooth_DCos2
  have sYrho : EllipticEst.SmoothOpen (Yrho Y) := Fbq_smoothOpen_mul hYs sRho
  have sYblk : EllipticEst.SmoothOpen (Yblk Y) := hYs.Dz
  have sZ : EllipticEst.SmoothOpen (Zfun Y) := SmoothOpen.add sYrho sYblk
  have sG : EllipticEst.SmoothOpen (Gfun Y) := Fbq_smoothOpen_mul sSqs sZ
  have sPY : EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hYs.pth
  have sPYRho : EllipticEst.SmoothOpen (fun z θ => Work.Spaces.pth Y z θ * Rho z θ) :=
    Fbq_smoothOpen_mul sPY sRho
  have sYblkP : EllipticEst.SmoothOpen (Yblk (Work.Spaces.pth Y)) := sPY.Dz
  have sSqsYrhoP : EllipticEst.SmoothOpen
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)) :=
    Fbq_smoothOpen_mul sSqs sPYRho
  have sSqsYblkP : EllipticEst.SmoothOpen
      (fun z θ => Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) :=
    Fbq_smoothOpen_mul sSqs sYblkP
  have sIn34 : EllipticEst.SmoothOpen
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
        + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) :=
    SmoothOpen.add sSqsYrhoP sSqsYblkP
  have sQ2 : EllipticEst.SmoothOpen (fun z θ => DSq z θ * Zfun Y z θ) :=
    Fbq_smoothOpen_mul sDSq sZ
  have sInner : EllipticEst.SmoothOpen (Inner Y) := by
    show EllipticEst.SmoothOpen (fun z θ => DSq z θ * Zfun Y z θ
      + (Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
        + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ))
    exact SmoothOpen.add sQ2 sIn34
  have sQ56 : EllipticEst.SmoothOpen
      (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
    SmoothOpen.add (Fbq_smoothOpen_mul sDCos2 sPY) sPY.Dth
  have sEH1 : EllipticEst.SmoothOpen (EH1 Y) := SmoothOpen.const_mul hYs 2
  have sEH2 : EllipticEst.SmoothOpen (EH2 α Y) := SmoothOpen.const_mul sG (2 * α)
  have sEH3 : EllipticEst.SmoothOpen (EH3 Y) := Fbq_smoothOpen_mul sSin sPY
  have sEH12 : EllipticEst.SmoothOpen (EH12 α Y) := SmoothOpen.add sEH1 sEH2
  -- ## auxiliary flat bounds
  have hYblk4 : F0 4 (5 * (A * K)) (Yblk Y) := by
    have hc : ((↑(4 : ℕ) : ℝ) + 1) * (A * K) = 5 * (A * K) := by norm_num
    exact (F0_zpz (n := 4) hAK hYs hY5f0).mono le_rfl (le_of_eq hc)
  have hYrho4 : F0 4 (16 * A ^ 2 * K) (Yrho Y) := by
    have h := F0_mul (Fbq_nonneg_of_F0 hY4.f0) (Fbq_nonneg_of_F0 hRho4) hYs sRho hY4.f0 hRho4
    have hc : (2 : ℝ) ^ 4 * (A * K) * A = 16 * A ^ 2 * K := by ring
    rw [hc] at h
    exact h
  have hZ4 : F0 4 (16 * A ^ 2 * K + 5 * (A * K)) (Zfun Y) := by
    have h := F0_add sYrho sYblk hYrho4 hYblk4
    exact h
  have hG4 : F0 4 (256 * A ^ 3 * K + 80 * A ^ 2 * K) (Gfun Y) := by
    have h := F0_mul (Fbq_nonneg_of_F0 hSqs4) (Fbq_nonneg_of_F0 hZ4) sSqs sZ hSqs4 hZ4
    have hc : (2 : ℝ) ^ 4 * A * (16 * A ^ 2 * K + 5 * (A * K))
        = 256 * A ^ 3 * K + 80 * A ^ 2 * K := by ring
    rw [hc] at h
    exact h
  have hPYrho4 : F0 4 (16 * A ^ 2 * K)
      (fun z θ => Work.Spaces.pth Y z θ * Rho z θ) := by
    have h := F0_mul (Fbq_nonneg_of_F0 hPY4) (Fbq_nonneg_of_F0 hRho4) sPY sRho hPY4 hRho4
    have hc : (2 : ℝ) ^ 4 * (A * K) * A = 16 * A ^ 2 * K := by ring
    rwa [hc] at h
  have hYblkP4 : F0 4 (5 * (A * K)) (Yblk (Work.Spaces.pth Y)) := by
    have hc : ((↑(4 : ℕ) : ℝ) + 1) * (A * K) = 5 * (A * K) := by norm_num
    exact (F0_zpz (n := 4) hAK sPY hPY5).mono le_rfl (le_of_eq hc)
  -- ## the first half: `F0 4 (EH α Y)`
  have hEH1 : F0 4 (1000 * M) (EH1 Y) := by
    have h : F0 4 (2 * A * K) (EH1 Y) := by
      have h0 := F0_const_mul (2 : ℝ) hY4.f0
      have hc : |(2 : ℝ)| * (A * K) = 2 * A * K := by ring
      rw [hc] at h0
      exact h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 2) (by norm_num) (p := 1) (by norm_num)
    have hlt : (2 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
      nlinarith [hM00]
    exact le_trans (by simpa only [pow_one] using hb) hlt
  have hEH2 : F0 4 (1000 * M) (EH2 α Y) := by
    have h : F0 4 (2 * α * (256 * A ^ 3 * K + 80 * A ^ 2 * K)) (EH2 α Y) := by
      have h0 := F0_const_mul (2 * α) hG4
      have hc : |2 * α| = 2 * α := abs_of_nonneg (by linarith)
      rw [hc] at h0
      exact h0
    refine h.mono le_rfl ?_
    rw [hM]
    exact alpha_one hA hK hα
  have hEH3 : F0 4 (1000 * M) (EH3 Y) := by
    have h : F0 4 (16 * A ^ 2 * K) (EH3 Y) := by
      have h0 := F0_mul (Fbq_nonneg_of_F0 hSin4) (Fbq_nonneg_of_F0 hPY4) sSin sPY hSin4 hPY4
      have hc : (2 : ℝ) ^ 4 * A * (A * K) = 16 * A ^ 2 * K := by ring
      rw [hc] at h0
      exact h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 16) (by norm_num) (p := 2) (by norm_num)
    linarith [hb, hM00]
  have hF0EH : F0 4 ((1000 * M + 1000 * M) + 1000 * M) (EH α Y) := by
    have h12 : F0 4 (1000 * M + 1000 * M) (EH12 α Y) := by
      have h := F0_add sEH1 sEH2 hEH1 hEH2
      exact h
    have h123 : F0 4 ((1000 * M + 1000 * M) + 1000 * M)
        (fun z θ => EH12 α Y z θ + EH3 Y z θ) := F0_add sEH12 sEH3 h12 hEH3
    exact F0_congr (fun z θ _ _ _ => EH_split z θ) h123
  -- ## the second half: `F0 4 (∂_θ(EH α Y))`
  have q1 : F0 4 (1000 * M) (fun z θ => 2 * Work.Spaces.pth Y z θ) := by
    have h : F0 4 (2 * A * K) (fun z θ => 2 * Work.Spaces.pth Y z θ) := by
      have h0 := F0_const_mul (2 : ℝ) hPY4
      have hc : |(2 : ℝ)| * (A * K) = 2 * A * K := by ring
      rwa [hc] at h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 2) (by norm_num) (p := 1) (by norm_num)
    have hlt : (2 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
      nlinarith [hM00]
    exact le_trans (by simpa only [pow_one] using hb) hlt
  have q2n : F0 4 (256 * A ^ 3 * K + 80 * A ^ 2 * K)
      (fun z θ => DSq z θ * Zfun Y z θ) := by
    have h0 := F0_mul (Fbq_nonneg_of_F0 hDSq4) (Fbq_nonneg_of_F0 hZ4) sDSq sZ hDSq4 hZ4
    have hc : (2 : ℝ) ^ 4 * A * (16 * A ^ 2 * K + 5 * (A * K))
        = 256 * A ^ 3 * K + 80 * A ^ 2 * K := by ring
    rwa [hc] at h0
  have q3n : F0 4 (256 * A ^ 3 * K)
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)) := by
    have h0 := F0_mul (Fbq_nonneg_of_F0 hSqs4) (Fbq_nonneg_of_F0 hPYrho4)
      sSqs sPYRho hSqs4 hPYrho4
    have hc : (2 : ℝ) ^ 4 * A * (16 * A ^ 2 * K) = 256 * A ^ 3 * K := by ring
    rwa [hc] at h0
  have q4n : F0 4 (80 * A ^ 2 * K)
      (fun z θ => Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) := by
    have h0 := F0_mul (Fbq_nonneg_of_F0 hSqs4) (Fbq_nonneg_of_F0 hYblkP4)
      sSqs sYblkP hSqs4 hYblkP4
    have hc : (2 : ℝ) ^ 4 * A * (5 * (A * K)) = 80 * A ^ 2 * K := by ring
    rwa [hc] at h0
  have h34n : F0 4 (256 * A ^ 3 * K + 80 * A ^ 2 * K)
      (fun z θ => Sqs z θ * (Work.Spaces.pth Y z θ * Rho z θ)
        + Sqs z θ * Yblk (Work.Spaces.pth Y) z θ) :=
    F0_add sSqsYrhoP sSqsYblkP q3n q4n
  have hInnerNat : F0 4 ((256 * A ^ 3 * K + 80 * A ^ 2 * K)
      + (256 * A ^ 3 * K + 80 * A ^ 2 * K)) (Inner Y) := by
    have h := F0_add sQ2 sIn34 q2n h34n
    exact h
  have hB : F0 4 (2000 * M) (fun z θ => (2 * α) * Inner Y z θ) := by
    have h0 : F0 4 (|2 * α| * ((256 * A ^ 3 * K + 80 * A ^ 2 * K)
        + (256 * A ^ 3 * K + 80 * A ^ 2 * K)))
        (fun z θ => (2 * α) * Inner Y z θ) := F0_const_mul (2 * α) hInnerNat
    have h2 : |2 * α| = 2 * α := abs_of_nonneg (by linarith)
    rw [h2] at h0
    refine h0.mono le_rfl ?_
    rw [hM]
    exact alpha_pair hA hK hα
  have q5 : F0 4 (1000 * M) (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ) := by
    have h : F0 4 (32 * A ^ 2 * K) (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ) := by
      have h0 := F0_mul (Fbq_nonneg_of_F0 hDCos2) (Fbq_nonneg_of_F0 hPY4)
        sDCos2 sPY hDCos2 hPY4
      have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * K) = 32 * A ^ 2 * K := by ring
      rwa [hc] at h0
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 32) (by norm_num) (p := 2) (by norm_num)
    linarith [hb, hM00]
  have q6 : F0 4 (1000 * M) (Work.Spaces.Dth (Work.Spaces.pth Y)) := by
    have h : F0 4 (A * K) (Work.Spaces.Dth (Work.Spaces.pth Y)) := F0_Dth hPY5
    refine h.mono le_rfl ?_
    rw [hM]
    have hb := absorb_le hA hK hα (c := 1) (by norm_num) (p := 1) (by norm_num)
    have hlt : (1 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ 1000 * (A ^ 4 * K * (α + 1)) := by
      nlinarith [hM00]
    exact le_trans (by simpa only [one_mul, pow_one] using hb) hlt
  have h56 : F0 4 (1000 * M + 1000 * M)
      (fun z θ => DCos2 z θ * Work.Spaces.pth Y z θ
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) := F0_add (Fbq_smoothOpen_mul sDCos2 sPY) sPY.Dth q5 q6
  have hDsum : F0 4 ((1000 * M + 2000 * M) + (1000 * M + 1000 * M)) (Dsum α Y) := by
    have hAB : F0 4 (1000 * M + 2000 * M)
        (fun z θ => 2 * Work.Spaces.pth Y z θ + (2 * α) * Inner Y z θ) :=
      F0_add (SmoothOpen.const_mul sPY 2) (SmoothOpen.const_mul sInner (2 * α)) q1 hB
    have h := F0_add (SmoothOpen.add (SmoothOpen.const_mul sPY 2)
        (SmoothOpen.const_mul sInner (2 * α))) sQ56 hAB h56
    exact h
  have hF0D : F0 4 ((1000 * M + 2000 * M) + (1000 * M + 1000 * M))
      (Work.Spaces.pth (EH α Y)) :=
    F0_congr (fun z θ hz hθ hθ' => pth_EH_eq hYs z θ hz hθ hθ') hDsum
  -- ## absorption of the total constants
  have hb1 : ((1000 * M + 1000 * M) + 1000 * M) ≤ 10 ^ 7 * A ^ 4 * K * (α + 1) := by
    rw [hM]
    nlinarith [hM00]
  have hb2 : ((1000 * M + 2000 * M) + (1000 * M + 1000 * M))
      ≤ 10 ^ 7 * A ^ 4 * K * (α + 1) := by
    rw [hM]
    nlinarith [hM00]
  exact ⟨hF0EH.mono le_rfl hb1, hF0D.mono le_rfl hb2⟩

/-- **The flat bound for `EH`.**  There is a universal constant `C` with: whenever `Y` is
`C^∞` on the open quadrant, `A ≥ 1`, `K ≥ 0`, `α ≥ 0`, the six coefficient functions are
`F0 6 A` and `Fb 6 (A·K) Y`, then `Fb 4 (C·A⁴·K·(α+1)) (EH α Y)`. -/
theorem FbEH : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EH α Y) := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro α K A Y hα hK hA hYs hsq _hccs hc2 hsi _hcz hci hY
  exact FbEH_aux hα hK hA hYs hsq hc2 hsi hci hY

end Work.FTS.PhiStar.StarPkgo2Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `D_z`-slot weight and the index set of the mixed slots -/

/-- The weight factor of the pure `D_z`-slots of `HkIntegrand`: `w z / sin(2θ)^{η/2}`. -/
def wE (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The index set of the mixed slots at level `k`: the pairs `(θ-order, z-order)` with
`θ-order ≥ 1` and `θ-order + z-order ≤ k`. -/
def slots (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
    (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k)

theorem mem_slots {k : ℕ} {q : ℕ × ℕ} :
    q ∈ slots k ↔ 1 ≤ q.1 ∧ q.1 + q.2 ≤ k ∧ q.1 ≤ k ∧ q.2 ≤ k := by
  simp only [slots, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h3, h4, by omega, by omega⟩
  · rintro ⟨h3, h4, h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4⟩

/-- The `D_z`-part of `HkIntegrand`, written with the weight `wE`. -/
theorem HkZPart_eq (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkSqAux.HkZPart k f z θ
      = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * wE z θ) ^ 2 := rfl

/-- The mixed part of `HkIntegrand`, as a sum over the index set `slots k`. -/
theorem HkMPartF_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkSqAux.HkMPartF α k f z θ
      = ∑ q ∈ slots k, (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := rfl

/-- `HkIntegrand` as the sum of its two explicit slot sums. -/
theorem HkIntegrand_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ
      = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * wE z θ) ^ 2)
        + ∑ q ∈ slots k, (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  rw [HkSqAux.HkIntegrand_eq_parts, HkSqAux.HkMPart_eq_HkMPartF]
  rfl

/-! ## The level-`k+1` shadow of the level-`k` slots -/

/-- The **level-`k+1` shadow** of the level-`k` slot sum of `J_ε f - f`.  When the difference
estimate is applied to the slot `D_z^i h` (`h = J_ε f - f`) of `D_z^i f`, the two derivatives
`D_z` and `D_θ` that appear produce the level-`k+1` slots `(i+1, 0)` and `(i, 1)`; the mixed slot
`(j, i)` produces `(j+1, i)` and `(j, i+1)`.  This is the sum of those produced slots, written
with the *level-`k+1`* weights (`wE` for the pure `D_z`-slots, `Wt α` for the mixed ones).  The
`1/4` on the two `D_θ`-groups is the factor produced by the elementary inequality
`(a + b)² ≤ 2a² + 2b²` (with `b = (p₂/2) D_θ`). -/
def shadow (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * wE z θ) ^ 2)
    + (1 / 4) * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.mixed i 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
    + (∑ q ∈ slots k, (Work.Spaces.mixed (q.2 + 1) q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
    + (1 / 4) * (∑ q ∈ slots k,
        (Work.Spaces.mixed q.2 (q.1 + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)

/-! ## Elementary positivity and comparison of the weights -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

theorem wE_nonneg {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 ≤ wE z θ := by
  rw [wE]
  exact div_nonneg (w_nonneg z)
    (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos hθ)) _)

theorem Wt_nonneg {α : ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    0 ≤ Work.Spaces.Wt α z θ := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_nonneg (w_nonneg z)
    (Real.rpow_nonneg (Work.FTS.StrongEps.sin_two_nonneg hθ) _)

/-- **The two weights of the paper are ordered**: `w / sin(2θ)^{η/2} ≤ w · sin(2θ)^{-γ/2}`,
because `η ≤ γ` and `sin(2θ) ≤ 1` on `[0, π/2]`. -/
theorem wE_le_Wt {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    wE z θ ≤ Work.Spaces.Wt α z θ := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.eta, Work.Spaces.gam]
    linarith [hα.1]
  have hkey : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  rw [wE, Work.Spaces.Wt, Work.Spaces.wTheta]
  have hL : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs)]
  rw [hL]
  exact mul_le_mul_of_nonneg_left hkey (w_nonneg z)

/-! ## Vanishing of the two weights on the boundary of the domain -/



end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSBlocks =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The block sums of the majorant -/

/-- The `L₁₂`-slot sum at level `n`. -/
noncomputable def LSlotSum (n : ℕ) (f : Fn) : ℝ → ℝ := fun z =>
  ∑ i ∈ Finset.range (n + 1),
    (Work.Elliptic.DzdIter i (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- The angular-moment slot sum at level `n`. -/
noncomputable def QSlotSum (n : ℕ) (f : Fn) : ℝ → ℝ := fun z =>
  ∑ i ∈ Finset.range (n + 1), (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- The `ampB`-slot sum at level `n`. -/
noncomputable def BSlotSum (n : ℕ) (α : ℝ) : ℝ → ℝ := fun z =>
  ∑ i ∈ Finset.range (n + 1),
    (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2

/-- The projector constant of the third block of the majorant. -/
noncomputable def SConst (α : ℝ) (f : Fn) : ℝ :=
  (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2

/-- The sum of the squared binomial coefficients is at most `4^j`. -/
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

/-- The block sums are nonnegative. -/
theorem LSlotSum_nonneg (n : ℕ) (f : Fn) (z : ℝ) : 0 ≤ LSlotSum n f z := by
  simp only [LSlotSum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem QSlotSum_nonneg (n : ℕ) (f : Fn) (z : ℝ) : 0 ≤ QSlotSum n f z := by
  simp only [QSlotSum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem BSlotSum_nonneg (n : ℕ) (α : ℝ) (z : ℝ) : 0 ≤ BSlotSum n α z := by
  simp only [BSlotSum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem SConst_nonneg (α : ℝ) (f : Fn) : 0 ≤ SConst α f := by
  rw [SConst]; exact sq_nonneg _

/-! ## The per-`j` bound of the majorant -/

/-- **Each summand of the majorant is dominated by the three block sums.** -/
theorem SmajA_le_blocks (α : ℝ) {f : Fn} {n : ℕ} (hn : n ≤ 3) {KA : ℝ} (hKA2 : 0 ≤ KA ^ 2)
    {j : ℕ} (hj : j ≤ n) {z : ℝ} :
    Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z
      ≤ 771 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z) := by
  have hj3 : j ≤ 3 := by omega
  have hAj : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 64 := by
    calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 4 ^ j := sum_choose_sq_le j
      _ ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) hj3
      _ = 64 := by norm_num
  have hS1 : (∑ b ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ ((j : ℝ) + 1) * LSlotSum n f z := by
    have hb : ∀ b ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2 ≤ LSlotSum n f z := by
      intro b hb
      have hbj : j - b ≤ n := by have := Finset.mem_range.mp hb; omega
      have hmem : (j - b) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      simp only [LSlotSum]
      exact Finset.single_le_sum (f := fun i => (Work.Elliptic.DzdIter i
          (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmem
    calc (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), LSlotSum n f z := Finset.sum_le_sum hb
      _ = ((j : ℝ) + 1) * LSlotSum n f z := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hS2 : (∑ b ∈ Finset.range (j + 1),
        (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ((j : ℝ) + 1) * QSlotSum n f z := by
    have hb : ∀ b ∈ Finset.range (j + 1),
        (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ QSlotSum n f z := by
      intro b hb
      have hbj : j - b ≤ n := by have := Finset.mem_range.mp hb; omega
      have hmem : (j - b) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      simp only [QSlotSum]
      exact Finset.single_le_sum (f := fun i => (Work.Elliptic.Qang f i z) ^ 2
          * (Work.Spaces.w z) ^ 2)
        (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmem
    calc (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), QSlotSum n f z := Finset.sum_le_sum hb
      _ = ((j : ℝ) + 1) * QSlotSum n f z := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hS3 : (Work.Elliptic.DzdIter (j + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ BSlotSum n α z := by
    have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    simp only [BSlotSum]
    exact Finset.single_le_sum (f := fun i => (Work.Elliptic.DzdIter (i + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmem
  have hS1nn : 0 ≤ (∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS2nn : 0 ≤ (∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have e1 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
      ≤ 256 * (KA ^ 2 * LSlotSum n f z) := by
    have h1 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        ≤ 64 * KA ^ 2 := mul_le_mul_of_nonneg_right hAj hKA2
    have hj4 : ((j : ℝ) + 1) ≤ 4 := by
      have : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
      linarith
    calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        ≤ (64 * KA ^ 2) * (((j : ℝ) + 1) * LSlotSum n f z) :=
          mul_le_mul h1 hS1 hS1nn (by positivity)
      _ ≤ (64 * KA ^ 2) * (4 * LSlotSum n f z) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hj4 (LSlotSum_nonneg n f z)
      _ = 256 * (KA ^ 2 * LSlotSum n f z) := by ring
  have e2 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 256 * (KA ^ 2 * QSlotSum n f z) := by
    have h1 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        ≤ 64 * KA ^ 2 := mul_le_mul_of_nonneg_right hAj hKA2
    have hj4 : ((j : ℝ) + 1) ≤ 4 := by
      have : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
      linarith
    calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (64 * KA ^ 2) * (((j : ℝ) + 1) * QSlotSum n f z) :=
          mul_le_mul h1 hS2 hS2nn (by positivity)
      _ ≤ (64 * KA ^ 2) * (4 * QSlotSum n f z) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hj4 (QSlotSum_nonneg n f z)
      _ = 256 * (KA ^ 2 * QSlotSum n f z) := by ring
  have e3 : SConst α f * ((Work.Elliptic.DzdIter (j + 1)
          (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 64 * (SConst α f * BSlotSum n α z) := by
    have h1 : SConst α f * ((Work.Elliptic.DzdIter (j + 1)
          (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ SConst α f * BSlotSum n α z := mul_le_mul_of_nonneg_left hS3 (SConst_nonneg α f)
    have hnn : 0 ≤ SConst α f * BSlotSum n α z :=
      mul_nonneg (SConst_nonneg α f) (BSlotSum_nonneg n α z)
    linarith [h1, hnn]
  have hLnn : 0 ≤ LSlotSum n f z := LSlotSum_nonneg n f z
  have hQnn : 0 ≤ QSlotSum n f z := QSlotSum_nonneg n f z
  have hBnn : 0 ≤ BSlotSum n α z := BSlotSum_nonneg n α z
  have hD2nn : 0 ≤ SConst α f := SConst_nonneg α f
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA]
  have hgoal : 3 * ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
      + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + SConst α f * ((Work.Elliptic.DzdIter (j + 1)
          (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ 771 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z) := by
    have hX : 0 ≤ KA ^ 2 * LSlotSum n f z := mul_nonneg hKA2 hLnn
    have hY : 0 ≤ KA ^ 2 * QSlotSum n f z := mul_nonneg hKA2 hQnn
    have hZ : 0 ≤ SConst α f * BSlotSum n α z := mul_nonneg hD2nn hBnn
    nlinarith [e1, e2, e3, hX, hY, hZ]
  exact hgoal

/-! ## The sum-level pointwise bound -/

/-- **The level-`n` slot sum of `radS` is dominated by the three block sums.** -/
theorem radS_sum_le (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} (hn : n ≤ 3)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) {KA : ℝ} (hKAnn : 0 ≤ KA)
    (hKbd : ∀ b ≤ 4, ∀ z ∈ IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ KA) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ 3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
            + SConst α f * BSlotSum n α z) := by
  have hKA2 : 0 ≤ KA ^ 2 := sq_nonneg KA
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by
    simp only [Work.Spaces.w]; norm_num
  have hL0 : LSlotSum n f 0 = 0 := by
    simp only [LSlotSum, hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      Finset.sum_const_zero]
  have hQ0 : QSlotSum n f 0 = 0 := by
    simp only [QSlotSum, hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      Finset.sum_const_zero]
  have hB0 : BSlotSum n α 0 = 0 := by
    simp only [BSlotSum, hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      Finset.sum_const_zero]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [hL0, hQ0, hB0]
    simp only [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero,
      mul_assoc, mul_zero, add_zero, le_refl]
  · have h1 : (∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ j ∈ Finset.range (n + 1),
            Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z :=
      Finset.sum_le_sum (fun j hj =>
        radS_sq_le_SmajA_O α hα hα1 hO hmem5 hl12
          (by have := Finset.mem_range.mp hj; omega) hKAnn hKbd z hzpos)
    have h2 : (∑ j ∈ Finset.range (n + 1),
            Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z)
        ≤ 3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
            + SConst α f * BSlotSum n α z) := by
      have hsum : (∑ j ∈ Finset.range (n + 1),
              Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z)
          ≤ ∑ _j ∈ Finset.range (n + 1), 771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z) :=
        Finset.sum_le_sum (fun j hj =>
          SmajA_le_blocks α hn hKA2 (by have := Finset.mem_range.mp hj; omega))
      have hconst : (∑ _j ∈ Finset.range (n + 1), 771 * (KA ^ 2 * LSlotSum n f z
            + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z))
          = ((n : ℝ) + 1) * (771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      have hn4 : ((n : ℝ) + 1) ≤ 4 := by
        have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
        linarith
      have hYnn : 0 ≤ 771 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z) := by
        have h1 : 0 ≤ KA ^ 2 * LSlotSum n f z := mul_nonneg hKA2 (LSlotSum_nonneg n f z)
        have h2 : 0 ≤ KA ^ 2 * QSlotSum n f z := mul_nonneg hKA2 (QSlotSum_nonneg n f z)
        have h3 : 0 ≤ SConst α f * BSlotSum n α z :=
          mul_nonneg (SConst_nonneg α f) (BSlotSum_nonneg n α z)
        linarith
      calc (∑ j ∈ Finset.range (n + 1),
              Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z)
          ≤ ∑ _j ∈ Finset.range (n + 1), 771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z) := hsum
        _ = ((n : ℝ) + 1) * (771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z)) := hconst
        _ ≤ 4 * (771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z)) :=
            mul_le_mul_of_nonneg_right hn4 hYnn
        _ = 3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
              + SConst α f * BSlotSum n α z) := by ring
    linarith [h1, h2]

end Work.FTS.StrongEps.EpsE4Thr.E2O
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.MajorantIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the majorant `G ∘ thShift` on `Iθ × [-ε,ε]`

For the smoothness of `Fstar (Jeps ρ ε W)` in the log-coordinate scheme one needs that an
angular majorant `G`, merely *integrable* on `(0,π/2)` (not measurable in any stronger sense),
can be pushed through the angular shift `thShift θ p = arctan (tan θ · e^{-p})`:

  `(θ,p) ↦ G (thShift θ p)` and `(θ,p) ↦ sin θ cos²θ · G (thShift θ p)`

are integrable for the product measure `(volume.restrict Iθ).prod (volume.restrict (Icc (-ε) ε))`,
`Iθ = [0,π/2]`.

## The route

`G` is integrable on `(0,π/2)`, hence *a.e.* strongly measurable there: take a strongly measurable
representative `G'` (`AEStronglyMeasurable` is by definition the existence of such a
representative).  Then

* `G'` is strongly measurable, integrable on `(0,π/2)` and equals `G` a.e. there — the first
  three conjuncts;
* `G' ∘ thShift` is integrable: its a.e. measurability comes from `G'` measurable together with
  the a.e. measurability of the shift (`aemeasurable_thShift_prod`), and the finiteness of the
  `lintegral` of its norm from the `θ`-substitution bound `JepsHkMem.lintegral_thShift_le`
  (which is *measurability free*) integrated against the finite `p`-measure
  (`LintegralProdThShiftLe`), applied to the measurable representative of `G'` — the passage
  between the two needs the null-preimage statement `thShift_null_preimage`
  (`ae_eq_comp_thShift`);
* multiplying by the bounded continuous factor `sinCos2` preserves integrability
  (`Integrable.mono'` with `‖sinCos2 θ‖ ≤ 1`);
* replacing `G'` by `G` inside the product is again the a.e. equality `G' ∘ thShift = G ∘ thShift`.

All the null sets involved (`Iθ \ (0,π/2)`, the preimage of a null set under `θ ↦ thShift θ p`)
are those of `ThShiftAEMeasurable` / `thShift_null_preimage`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallLimAux

open Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two reductions about the composition with the angular shift -/

/-- **A.e. equality is preserved by `thShift`.**  If `F = g` a.e. on `(0,π/2)`, then
`F ∘ thShift = g ∘ thShift` a.e. for the product measure on `Iθ × [-ε,ε]`: the shift maps a.e.
`(θ,p)` (namely those with `θ ∈ (0,π/2)`) into `(0,π/2)` (`thShift_mem`), and the preimage of a
null set is null (`thShift_null_preimage`). -/
theorem ae_eq_comp_thShift {ε : ℝ} (hε : 0 < ε) {F g : ℝ → ℝ}
    (h : F =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] g) :
    (fun x : ℝ × ℝ => F (Work.FTS.StrongEps.thShift x.1 x.2))
      =ᵐ[((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))]
      (fun x : ℝ × ℝ => g (Work.FTS.StrongEps.thShift x.1 x.2)) := by
  have hν0 : (volume.restrict (Set.Ioo 0 (π / 2))) {θ : ℝ | F θ ≠ g θ} = 0 :=
    ae_iff.mp h
  obtain ⟨Z, hZsub, hZmeas, hZ0'⟩ := exists_measurable_superset_of_null hν0
  have hZvol : (volume : Measure ℝ) (Z ∩ Set.Ioo 0 (π / 2)) = 0 := by
    rw [← Measure.restrict_apply hZmeas]
    exact hZ0'
  have hZn : ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))
      {x : ℝ × ℝ | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z ∩ Set.Ioo 0 (π / 2)} = 0 :=
    thShift_null_preimage hε (hZmeas.inter measurableSet_Ioo) hZvol
  have hA : ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))
      {x : ℝ × ℝ | x.1 ∉ Set.Ioo 0 (π / 2)} = 0 := by
    rw [show {x : ℝ × ℝ | x.1 ∉ Set.Ioo 0 (π / 2)}
        = (Set.Ioo 0 (π / 2))ᶜ ×ˢ (Set.univ : Set ℝ) from by ext x; simp]
    rw [Measure.prod_prod, measure_Iθ_compl_Ioo_eq_zero, zero_mul]
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ (measure_union_null hA hZn)
  intro x hx
  by_cases hxI : x.1 ∈ Set.Ioo 0 (π / 2)
  · right
    exact ⟨hZsub hx, Work.FTS.StrongEps.thShift_mem hxI⟩
  · exact Or.inl hxI

/-- **Integrability of `θ ↦ F (thShift θ p)` as a function of `(θ,p)`.**  For `F` integrable on
`(0,π/2)` the composite with the angular shift is integrable for the product measure on
`Iθ × [-ε,ε]`.

A.e. strong measurability: `F` has a strongly measurable representative `g` (a.e. measurable),
and `g ∘ thShift` is a.e. strongly measurable because `thShift` is a.e. (strongly) measurable
(`aemeasurable_thShift_prod`); the a.e. equality `F ∘ thShift = g ∘ thShift` is
`ae_eq_comp_thShift`.

Finiteness of the `lintegral` of the norm: replace `F` by `g` (a.e. equality), split `‖·‖ₑ` into
`ofReal |·|`, apply `LintegralProdThShiftLe` to `U θ = ofReal |g θ|`, and identify the remaining
`θ`-integral with `ofReal (∫_{(0,π/2)} |g|) < ∞` (`lintegral_Iθ_eq_Ioo`,
`ofReal_integral_eq_lintegral_ofReal`). -/
theorem integrable_comp_thShift {ε : ℝ} (hε : 0 < ε) {F : ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (π / 2))) :
    MeasureTheory.Integrable (fun x : ℝ × ℝ => F (Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
  obtain ⟨g, hgmeas, hgae⟩ := hF.aestronglyMeasurable.aemeasurable
  have hgint : MeasureTheory.IntegrableOn g (Set.Ioo 0 (π / 2)) := hF.congr hgae
  have haeeq := ae_eq_comp_thShift hε hgae
  refine ⟨?_, ?_⟩
  · exact ((hgmeas.comp_aemeasurable aemeasurable_thShift_prod).congr haeeq.symm).aestronglyMeasurable
  · have hmeas_abs : Measurable (fun θ : ℝ => ENNReal.ofReal |g θ|) :=
      ENNReal.measurable_ofReal.comp hgmeas.abs
    calc ∫⁻ x : ℝ × ℝ, ‖F (Work.FTS.StrongEps.thShift x.1 x.2)‖ₑ
            ∂((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))
        = ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |F (Work.FTS.StrongEps.thShift x.1 x.2)|
            ∂((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) :=
          lintegral_congr fun x => by
            rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]; norm_cast
      _ = ∫⁻ x : ℝ × ℝ, ENNReal.ofReal |g (Work.FTS.StrongEps.thShift x.1 x.2)|
            ∂((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [haeeq] with x hx
          rw [hx]
      _ ≤ ENNReal.ofReal (Real.exp (3 * ε) * (2 * ε)) *
            ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g θ| :=
          LintegralProdThShiftLe hε hmeas_abs
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          rw [lintegral_Iθ_eq_Ioo,
            ← ofReal_integral_eq_lintegral_ofReal hgint.abs
              (Filter.Eventually.of_forall fun θ => abs_nonneg (g θ))]
          exact ENNReal.ofReal_lt_top

/-! ## The target -/

theorem MajorantIntegrable {G : ℝ → ℝ} (hG : MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G' : ℝ → ℝ, MeasureTheory.StronglyMeasurable G' ∧ MeasureTheory.IntegrableOn G' (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), G' θ = G θ) ∧
      MeasureTheory.Integrable (fun x : ℝ × ℝ => G' (Work.FTS.StrongEps.thShift x.1 x.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) ∧
      MeasureTheory.Integrable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G' (Work.FTS.StrongEps.thShift x.1 x.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) ∧
      MeasureTheory.Integrable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
  obtain ⟨G', hG'sm, hG'ae⟩ := hG.aestronglyMeasurable
  have hG'int : MeasureTheory.IntegrableOn G' (Set.Ioo 0 (Real.pi / 2)) := hG.congr hG'ae
  have hcomp' : (fun x : ℝ × ℝ => G' (Work.FTS.StrongEps.thShift x.1 x.2))
      =ᵐ[((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε)))]
      (fun x : ℝ × ℝ => G (Work.FTS.StrongEps.thShift x.1 x.2)) :=
    (ae_eq_comp_thShift hε hG'ae).symm
  have h1 : MeasureTheory.Integrable (fun x : ℝ × ℝ => G' (Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) :=
    integrable_comp_thShift hε hG'int
  have hsinCos2_cont : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
    rw [show Work.Elliptic.sinCos2 = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 from rfl]
    fun_prop
  have hsinCos2 : ∀ θ : ℝ, ‖Work.Elliptic.sinCos2 θ‖ ≤ 1 := by
    intro θ
    rw [Work.Elliptic.sinCos2, Real.norm_eq_abs, abs_mul]
    have hc : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ)
    calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one θ) hc (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  have h2 : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G' (Work.FTS.StrongEps.thShift x.1 x.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Icc (-ε) ε))) := by
    refine MeasureTheory.Integrable.mono' h1.norm ?_ ?_
    · exact (hsinCos2_cont.measurable.comp measurable_fst).aestronglyMeasurable.mul
        h1.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      calc |Work.Elliptic.sinCos2 x.1| * |G' (Work.FTS.StrongEps.thShift x.1 x.2)|
          ≤ 1 * |G' (Work.FTS.StrongEps.thShift x.1 x.2)| :=
            mul_le_mul_of_nonneg_right (hsinCos2 x.1) (abs_nonneg _)
        _ = |G' (Work.FTS.StrongEps.thShift x.1 x.2)| := one_mul _
  refine ⟨G', hG'sm, hG'int, hG'ae.symm, h1, h2, h2.congr ?_⟩
  filter_upwards [hcomp'] with x hx
  rw [hx]

end Work.FTS.StrongEps.EpsE4Thr.XBallLimAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.HkMemAKGeneral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ⁴`-honesty of `AK α` for every `α > 0`

`Work.FTS.NonlinRows.NAux3.HkMem_AK` proves `Work.Spaces.HkMem α 4 (Work.Construction.AK α)`
under the extra hypothesis `α ≤ 1`.  The only place that hypothesis enters is the *numerical*
control of the angular majorant: for `α ≤ 1` the exponent `17α/30 - 1` of the dominating
`sin(2θ)`-power is `≤ 0`, so the delivered `angMaj_mem` (which uses `Work.Spaces.sin_two_rpow`
in its stated range `-1 < p ≤ 0`) applies.

This file removes the restriction.  The mathematical content is unchanged and in fact slightly
sharper: the pointwise angular inequality

`Γ(θ)² sin(2θ)^{-γ} ≤ 2^{-2α/3} sin(2θ)^{17α/30-1}`

holds for every `α > 0` (its proof never used `α ≤ 1`; only the *integrability* of the
majorant `sin(2θ)^{17α/30-1}` needs a case distinction on the sign of `17α/30 - 1`, the
positive case being trivial because `sin(2θ) ≤ 1`).  Consequently `angMaj α` is integrable on
`Iθ` for every `α > 0`, and the separable-datum majorant
`LocDataExt.HkIntegrand_sepGam_le` (which is stated for arbitrary `α > 0`) finishes the job.

The remaining two inputs are

* the *radial* jet bound `AkRhoJetBasic.akRho_jet_bound` for `2z²/(1+z)³`, transported to the
  normalised factor `2z²/((1+z)³c(α))` by `DzIter_const_mul` — no lower bound on `c(α)` is
  needed (the factor enters only through its square);
* the *angular* jet bound `|D_θ^i Γ| ≤ C·Γ` on `Iθ` (`Spaces.dthU_iter_Gam_abs_bound`,
  available for every `α > 0`), which produces the constant `Rθ` of the majorant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## `c α ≠ 0` for every `α > 0` -/

/-- The normalisation constant `c α = ∫_{Iθ} Γ(θ)K(θ) dθ` is positive (hence nonzero) for every
`α > 0`: the integrand is nonnegative everywhere and `≥ 3(1/4)^{α/3+1}` on `[π/6, π/4]`,
where `sin θ cos²θ ≥ 1/4`. -/
theorem c_ne_zero_of_pos (α : ℝ) (hα : 0 < α) : Work.Spaces.c α ≠ 0 := by
  have hsub : Set.Icc (π / 6) (π / 4) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hint : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK α hα
  have hnonneg : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (0 : ℝ) ≤ Work.Spaces.Gam α θ * Work.Spaces.K θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (Work.Spaces.gamK_bounds α θ hα hθ).1
  have hle : ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam α θ * Work.Spaces.K θ
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ :=
    MeasureTheory.setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall hsub)
  have hconst_le : ∀ θ ∈ Set.Icc (π / 6) (π / 4),
      3 * (1 / 4 : ℝ) ^ (α / 3 + 1) ≤ Work.Spaces.Gam α θ * Work.Spaces.K θ := by
    intro θ hθ
    have hs : (1 / 2 : ℝ) ≤ Real.sin θ := by
      have h1 : Real.sin (π / 6) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos]) hθ.1
      rwa [Real.sin_pi_div_six] at h1
    have hc2 : (1 / 2 : ℝ) ≤ Real.cos θ ^ 2 := by
      have h1 : Real.cos (π / 4) ≤ Real.cos θ :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [Real.pi_pos]) hθ.2
      rw [Real.cos_pi_div_four] at h1
      have hsq : (√2 / 2) ^ 2 = (1 / 2 : ℝ) := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h2 : (√2 / 2) ^ 2 ≤ (Real.cos θ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      linarith [h2, hsq]
    have hsin0 : (0 : ℝ) ≤ Real.sin θ := le_trans (by norm_num) hs
    have hu : (1 / 4 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := by
      have h1 := mul_le_mul hs hc2 (by norm_num : (0 : ℝ) ≤ 1 / 2) hsin0
      rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num] at h1
      exact h1
    have hp : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := le_trans (by norm_num) hu
    have hGam : (1 / 4 : ℝ) ^ (α / 3 + 1)
        ≤ (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) :=
      Real.rpow_le_rpow (by norm_num) hu (by linarith)
    have hprod : Work.Spaces.Gam α θ * Work.Spaces.K θ
        = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) := by
      rw [Work.Spaces.Gam, Work.Spaces.K]
      have hsplit : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
            * (3 * Real.sin θ * Real.cos θ ^ 2)
          = 3 * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
              * (Real.sin θ * Real.cos θ ^ 2) ^ (1 : ℝ)) := by
        rw [Real.rpow_one]; ring
      rw [hsplit, ← Real.rpow_add' hp (show α / 3 + 1 ≠ 0 by linarith)]
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hGam (by norm_num)
  have hge : 3 * (1 / 4 : ℝ) ^ (α / 3 + 1) * volume.real (Set.Icc (π / 6) (π / 4))
      ≤ ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam α θ * Work.Spaces.K θ :=
    MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hconst_le
      (hint.mono_set hsub)
  have hvol : volume.real (Set.Icc (π / 6) (π / 4)) = π / 12 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hpos : 0 < 3 * (1 / 4 : ℝ) ^ (α / 3 + 1) * volume.real (Set.Icc (π / 6) (π / 4)) := by
    have hb : 0 < (1 / 4 : ℝ) ^ (α / 3 + 1) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hvol]
    positivity
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le hpos (le_trans hge hle)
  exact ne_of_gt hcpos

/-! ## Smoothness of `AK α` on the open quadrant, for every `α > 0` -/

/-- `AK α = (Γ(θ)/c α)·2z²/(1+z)³` is `C⁴` on the open quadrant for every `α > 0`
(the `α ≤ 1` in `Work.FTS.OpenPkg.contDiffOn_four_AK` was only used to see `c α ≠ 0`). -/
theorem contDiffOn_four_AK_gen (α : ℝ) (hα : 0 < α) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.AK α)) Work.FTS.EllipticEst.Q0 := by
  have hcne : Work.Spaces.c α ≠ 0 := c_ne_zero_of_pos α hα
  have hGam := (Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 4).div contDiffOn_const
    (fun p hp => hcne)
  have hrad : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (contDiffOn_fst.pow 2)).div
      ((contDiffOn_const.add contDiffOn_fst).pow 3)
      (fun p hp => pow_ne_zero 3 (ne_of_gt
        (by linarith [Set.mem_Ioi.mp hp.1] : (0 : ℝ) < 1 + p.1)))
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)) = Function.uncurry (Work.Construction.AK α) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.AK]
  rw [← hfun]
  exact hGam.mul hrad

/-! ## The angular pointwise bound, for every `α > 0` -/

/-- **The sharp angular bound**: `Γ(θ)² sin(2θ)^{-γ(α)} ≤ 2^{-2α/3} sin(2θ)^{17α/30-1}` on `Iθ`,
for every `α > 0`.  (This is `Work.FTS.LocData.GamSq_sin_neg_gam_le` without the hypothesis
`α ≤ 1`, which its proof never used: the only step needing care is the multiplicative identity
`X^{2α/3}·X^{-γ} = X^{17α/30-1}`, which is handled below by the case `X = 0`.) -/
theorem GamSq_sin_neg_gam_le_gen (α : ℝ) (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = 17 * α / 30 - 1 := by
    simp only [Work.Spaces.gam]; ring
  have hΓ2 : Work.Spaces.Gam α θ ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
    rw [Work.Spaces.Gam]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2)]
    congr 1
    ring
  have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, Real.cos_le_one θ]
  have hYle : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
    mul_le_mul_of_nonneg_left hc2 hs0
  have hstat : Work.Spaces.Gam α θ ^ 2 ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3) := by
    rw [hΓ2]
    exact Real.rpow_le_rpow (by positivity) hYle (by linarith : (0 : ℝ) ≤ 2 * α / 3)
  rcases eq_or_lt_of_le hX0 with hXeq | hXpos
  · -- `sin(2θ) = 0`: both sides are `0 ≤ ·`
    have hz : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) = 0 := by
      rw [← hXeq]
      exact Real.zero_rpow (by simp only [Work.Spaces.gam]; linarith)
    rw [hz, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hX0 _)
  · have hstep2 : (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
      have hY : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
        rw [Real.sin_two_mul]; ring
      rw [hY, Work.FTS.LocData.angMaj_div_two_rpow _ hX0, mul_assoc,
        ← Real.rpow_add hXpos, hexp]
    calc Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hstat (Real.rpow_nonneg hX0 _)
      _ = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hstep2

/-! ## Integrability of the angular majorants for every `α > 0` -/

/-- `sin(2θ)^p` is integrable on `Iθ` as soon as `p > -1` (for `p > 0` it is bounded by `1`). -/
theorem integrableOn_sinTwo_rpow (p : ℝ) (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ := by
  by_cases hp0 : p ≤ 0
  · exact (Work.Spaces.sin_two_rpow p hp hp0).1
  · have hp0' : 0 < p := not_le.mp hp0
    have hbdd : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    refine hbdd.mono' ?_ ?_
    · exact (Measurable.pow_const
        (Real.measurable_sin.comp (measurable_const.mul measurable_id)) p).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hX0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hX0 _)]
      exact Real.rpow_le_one hX0 (Real.sin_le_one _) hp0'.le

/-- Integrability of `Γ(θ)² sin(2θ)^{-γ}` on `Iθ`, for every `α > 0`. -/
theorem integrableOn_gamSq_sin_neg_gam (α : ℝ) (hα : 0 < α) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIntX : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ :=
    integrableOn_sinTwo_rpow (17 * α / 30 - 1) (by linarith)
  refine (hIntX.const_mul (2 ^ (-(2 * α / 3)))).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem hmeas] with θ hθ
    have hX0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hX0 _))]
    exact GamSq_sin_neg_gam_le_gen α hα hθ

/-- Integrability of `Γ(θ)² sin(2θ)^{-η}` on `Iθ`, for every `α > 0`. -/
theorem integrableOn_gamSq_sin_neg_eta (α : ℝ) (hα : 0 < α) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIntX : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by simp only [Work.Spaces.eta]; norm_num)
      (by simp only [Work.Spaces.eta]; norm_num)).1
  refine hIntX.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem hmeas] with θ hθ
    have hX0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hX0 _))]
    exact Work.FTS.LocData.GamSq_sin_neg_eta_le α hα hθ

/-- **`angMaj α` is integrable on `Iθ` for every `α > 0`** (the `α ≤ 1` of
`Work.FTS.LocData.angMaj_mem` was only used to keep the exponent `17α/30-1` nonpositive). -/
theorem integrableOn_angMaj_of_pos (α : ℝ) (hα : 0 < α) :
    IntegrableOn (fun θ => Work.FTS.LocData.angMaj α θ) Work.Spaces.Iθ := by
  have hInt0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (integrableOn_gamSq_sin_neg_gam α hα).add (integrableOn_gamSq_sin_neg_eta α hα)
  have hangMaj : (fun θ : ℝ => Work.FTS.LocData.angMaj α θ) = fun θ : ℝ =>
      (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) + 1 := by
    funext θ
    rw [Work.FTS.LocData.angMaj_apply]
  rw [hangMaj]
  exact hsum.add hInt0

/-! ## The angular jet bound for `Γ`, for every `α > 0` -/

/-- `|D_θ^i Γ| ≤ C·Γ` on all of `Iθ`, for every `i` and every `α > 0`. -/
theorem GamJetBound (α : ℝ) (hα : 0 < α) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ C * (Work.Spaces.Gam α θ) ^ 2 := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    refine ⟨1, zero_le_one, fun θ _ => ?_⟩
    simp
  · obtain ⟨M, hM0, hM⟩ :=
      Work.FTS.StrongEps.EpsE4Thr.TracesAux.exists_Tfun_bound α (i - 1)
    refine ⟨(α * M) ^ 2, sq_nonneg _, fun θ hθ => ?_⟩
    rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.Spaces.Gam α θ') 0 θ]
    have hb := Work.Spaces.dthU_iter_Gam_abs_bound i hpos α hα M hM θ hθ
    have h2 : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ) ^ 2
        ≤ (α * M * Work.Spaces.Gam α θ) ^ 2 := by
      rw [← sq_abs (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ) ^ 2
        ≤ (α * M * Work.Spaces.Gam α θ) ^ 2 := h2
      _ = (α * M) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring

/-! ## The `ℋ⁴`-membership -/

theorem HkMemAKGeneral (α : ℝ) (hα : 0 < α) : Work.Spaces.HkMem α 4 (Work.Construction.AK α) := by
  obtain ⟨R₀, hR₀0, hB₀⟩ := Work.FTS.NonlinRows.AkRhoJetBasic.akRho_jet_bound
  choose C hC using fun i : ℕ => GamJetBound α hα i
  set Rθ : ℝ := ∑ i ∈ Finset.range 5, C i with hRθdef
  have hRθ : 0 ≤ Rθ := by
    rw [hRθdef]
    exact Finset.sum_nonneg (fun i _ => (hC i).1)
  have hJet : ∀ i ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2 := by
    intro i hi θ hθ
    have h1 := (hC i).2 θ hθ
    have h2 : C i ≤ Rθ := by
      rw [hRθdef]
      exact Finset.single_le_sum (fun j _ => (hC j).1) (Finset.mem_range.mpr (by omega))
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
  set R : ℝ := R₀ * (1 / Work.Spaces.c α) ^ 2 with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]; positivity
  have hB : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) z θ'
        * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
    intro j hj z hz θ'
    have hfun : (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α)
        = fun z _ : ℝ => (1 / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := by
      funext z θ''
      rw [one_div]
      ring
    have hmult := congrFun (congrFun (Work.FTS.LocDataExt.DzIter_const_mul
      (1 / Work.Spaces.c α) (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) j) z) θ'
    have hsq : (Work.Spaces.DzIter j
          (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) z θ'
        * Work.Spaces.w z) ^ 2
        = (1 / Work.Spaces.c α) ^ 2
          * (Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
            * Work.Spaces.w z) ^ 2 := by
      rw [hfun]
      rw [hmult]
      ring
    rw [hsq]
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      have hz0' : Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) 0 θ'
          * Work.Spaces.w 0 = 0 := by rw [hw0, mul_zero]
      rw [hz0']
      have hsq0 : (1 / Work.Spaces.c α) ^ 2 * (0 : ℝ) ^ 2 = 0 := by ring
      rw [hsq0]
      exact div_nonneg hR0 (by norm_num)
    · have h1 := hB₀ j hj hz0 θ'
      calc (1 / Work.Spaces.c α) ^ 2
            * (Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
              * Work.Spaces.w z) ^ 2
          ≤ (1 / Work.Spaces.c α) ^ 2 * (R₀ / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = R / (1 + z) ^ 2 := by rw [hRdef]; ring
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := Work.Construction.AK α)
    (M := fun z θ => (((5 : ℝ) + 25 * Rθ) * R / (1 + z) ^ 2)
      * Work.FTS.LocData.angMaj α θ)
    (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn (F := Work.Construction.AK α) α
      (n := 4) (k := 4) le_rfl (contDiffOn_four_AK_gen α hα)) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable
    intro z _hz
    exact (integrableOn_angMaj_of_pos α hα).const_mul
      (((5 : ℝ) + 25 * Rθ) * R / (1 + z) ^ 2)
  · -- the `z`-integral of the majorant is integrable
    have hkey : IntegrableOn (fun z : ℝ => (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ioi 0) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ))
    have hkeyIz : IntegrableOn (fun z : ℝ => (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ici 0) :=
      hkey.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have heqfun : (fun z : ℝ => (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (((5 : ℝ) + 25 * Rθ) * R / (1 + z) ^ 2) * Work.FTS.LocData.angMaj α θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
      rw [one_div, inv_pow, div_eq_mul_inv]
      ring
    rw [← heqfun]
    exact hkeyIz
  · -- the pointwise domination
    intro z hz θ hθ
    have hAK : Work.Construction.AK α
        = fun z θ => (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
      funext z θ
      rw [Work.Construction.AK]
      ring
    rw [hAK]
    have h1 := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 4
      (ρ := fun z => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) hR0 hRθ hB hJet hz hθ
    refine le_trans h1 (le_of_eq ?_)
    push_cast
    ring

end Work.FTS.StrongEps.EpsRLX
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.Chain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- On the boundary of the closed quadrant (`z = 0`, `θ = 0` or `θ = π/2`) the `H^k`-integrand
vanishes: the radial weight `w` or the angular weight `sin(2θ)^{-η/2}` is `0` there. -/
theorem HkIntegrand_boundary_zero {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {f : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    (hq : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.Iz] at hz
  rw [Work.Spaces.Iθ] at hθ
  have hη : (Work.Spaces.eta / 2 : ℝ) ≠ 0 := by
    rw [Work.Spaces.eta]; norm_num
  have hγ : (-(Work.Spaces.gam α / 2) : ℝ) ≠ 0 := by
    rw [Work.Spaces.gam]
    intro h
    have h1 : 1 + α / 10 = 0 := by linarith
    linarith [hα.1]
  rcases not_and_or.mp hq with hz0 | hθbad
  · have hz' : z = 0 := le_antisymm (not_lt.mp hz0) hz
    subst hz'
    simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
    simp
  · have hθbad' : θ ≤ 0 ∨ π / 2 ≤ θ := by
      rcases not_and_or.mp hθbad with h | h
      · exact Or.inl (not_lt.mp h)
      · exact Or.inr (not_lt.mp h)
    have hsin : Real.sin (2 * θ) = 0 := by
      rcases hθbad' with h | h
      · have h' : θ = 0 := le_antisymm h hθ.1
        subst h'
        simp
      · have h' : θ = π / 2 := le_antisymm hθ.2 h
        subst h'
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, hsin,
      Real.zero_rpow hη, Real.zero_rpow hγ]
    simp

theorem Jker_support_abs {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {p : ℝ × ℝ} (hp : Jker ρ ε p ≠ 0) : |p.1| + |p.2| ≤ 2 * ε := by
  have h := Jker_ne_zero_support hρ hε hp
  have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
  have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
  have ha : |p.1| ≤ ε := by
    rw [sq_le_sq] at h1
    rwa [abs_of_nonneg hε.le] at h1
  have hb : |p.2| ≤ ε := by
    rw [sq_le_sq] at h2
    rwa [abs_of_nonneg hε.le] at h2
  linarith

/-- **The pointwise bound in `ℝ≥0∞`**: at every point of the closed quadrant, the `H^k`-integrand
of `J_ε f` is dominated by `e^{2cε}` times the `p`-integral of the shifted `H^k`-integrand of `f`
against the kernel density. -/
theorem ofReal_GJ_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {c : ℝ}
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) (k : ℕ) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
      ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) := by
  by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · obtain ⟨hzpos, hθIoo⟩ := hq
    have hpt := HkIntegrand_Jeps_le_integral (f := f) ρ hρ hε hα hf (c := c) hzpos hθIoo k
      (hWη z θ hzpos hθIoo) (hWγ z θ hzpos hθIoo)
    have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad :=
      continuousOn_HkIntegrand_Quad α k hf
    have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by
      refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
      refine Continuous.add ?_ ?_
      · exact continuous_abs.comp continuous_fst
      · exact continuous_abs.comp continuous_snd
    have hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
        * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) := by
      simpa only [mul_assoc] using integrable_Jker_mul ρ hρ hε
        (A := fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2))
        (hexp.continuousOn.mul (continuousOn_shift_ball hzpos hθIoo
          (A := fun z' θ' => Work.Spaces.HkIntegrand α k f z' θ')
          (hcont.mono (Kz_prod_Kth_subset_Quad hzpos hε hθIoo))))
    have hnonneg : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
        * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2) := fun p =>
      mul_nonneg (mul_nonneg (Jker_nonneg ρ hρ ε p) (Real.exp_pos _).le)
        (Work.Spaces.HkIntegrand_nonneg α k f _ _)
    calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
        ≤ ENNReal.ofReal (∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
            * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) :=
          ENNReal.ofReal_le_ofReal hpt
      _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
              * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnonneg)
      _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                  (thShift θ p.2)) := by
          refine lintegral_congr fun p => ?_
          rw [ENNReal.ofReal_mul (mul_nonneg (Jker_nonneg ρ hρ ε p) (Real.exp_pos _).le),
            ENNReal.ofReal_mul (Jker_nonneg ρ hρ ε p)]
  · rw [HkIntegrand_boundary_zero hα hz hθ hq, ENNReal.ofReal_zero]
    exact zero_le

theorem ofReal_exp_mul (a b : ℝ) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b)
      = ENNReal.ofReal (Real.exp (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos a).le, ← Real.exp_add]

/-- **Tonelli's theorem for the shifted slots**: exchanging the `(z,θ)`-integration with the
`p`-integration in the pointwise bound of `ofReal_GJ_le`. -/
theorem fubini_shift {ρ : ℝ × ℝ → ℝ} (hρc : Continuous ρ) {ε c : ℝ} {α : ℝ} {k : ℕ}
    {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)))
      = ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|))))
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2))) := by
  have hpair : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2) * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift q.1.1 q.2.1)
            (thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
    have h0 := aemeasurable_shift_pair (G := fun z θ => Work.Spaces.HkIntegrand α k f z θ)
      hcont ρ hρc ε
    have hm : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|))) := by
      refine ENNReal.measurable_ofReal.comp ?_
      refine Real.continuous_exp.measurable.comp ?_
      have h1 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.2.1| :=
        continuous_abs.measurable.comp measurable_snd.fst
      have h2 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.2.2| :=
        continuous_abs.measurable.comp measurable_snd.snd
      exact (h1.add h2).const_mul (2 * c)
    refine (h0.mul hm.aemeasurable).congr (Eventually.of_forall fun q => ?_)
    simp only [Pi.mul_apply]
    ring
  -- the iterated `(z,θ)`-integral as an integral over the product space
  have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)))
      = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
          * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift q.1 p.1) (thShift q.2 p.2))
        ∂MeasureTheory.volume
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) _ _]
    exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift q.1 p.1) (thShift q.2 p.2)))
      (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
        rw [← Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)]
        exact hpair.lintegral_prod_right')).symm
  rw [hL]
  -- Tonelli
  rw [MeasureTheory.lintegral_lintegral_swap
    (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) (ν := MeasureTheory.volume) hpair]
  -- back to the iterated form, for each `p`
  refine lintegral_congr fun p => ?_
  have hXne : (ENNReal.ofReal (Jker ρ ε p)
      * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [MeasureTheory.lintegral_const_mul' _ _ hXne]
  have hAB : (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
        (zShift q.1 p.1) (thShift q.2 p.2))
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) := by
    rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) _ _]
    exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal
      (Work.Spaces.HkIntegrand α k f (zShift q.1 p.1) (thShift q.2 p.2)))
      (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
        rw [← Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)]
        exact aemeasurable_shift_slice hcont p)
  rw [hAB]

theorem Jker_exp_integral_le {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε c δ : ℝ} (hε : 0 < ε)
    (hc0 : 0 ≤ c) (hδ0 : 0 ≤ δ) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
        * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
      ≤ ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε)) := by
  have hexp : Continuous fun p : ℝ × ℝ => Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) := by
    refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
    refine Continuous.add ?_ ?_
    · exact continuous_abs.comp continuous_fst
    · exact continuous_abs.comp continuous_snd
  have hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) :=
    integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) hexp.continuousOn
  have hint2 : Integrable (fun p : ℝ × ℝ => Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p) := by
    simpa only [mul_comm] using integrable_Jker_mul ρ hρ hε
      (A := fun _ : ℝ × ℝ => Real.exp ((4 * c + 2 * δ) * ε)) continuousOn_const
  have hpoint : ∀ p : ℝ × ℝ, Jker ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))
      ≤ Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p := by
    intro p
    by_cases hp : Jker ρ ε p = 0
    · rw [hp, zero_mul, mul_zero]
    · have hb := Jker_support_abs hρ hε hp
      calc Jker ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))
          ≤ Jker ρ ε p * Real.exp ((2 * c + δ) * (2 * ε)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Jker_nonneg ρ hρ ε p)
            exact mul_le_mul_of_nonneg_left hb (by linarith)
        _ = Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p := by
            rw [show Jker ρ ε p * Real.exp ((2 * c + δ) * (2 * ε))
                = Real.exp ((2 * c + δ) * (2 * ε)) * Jker ρ ε p from by rw [mul_comm]]
            congr 1
            ring
  rw [show (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
        * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p
          * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) from by
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_mul (Jker_nonneg ρ hρ ε p)]]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun p => mul_nonneg (Jker_nonneg ρ hρ ε p) (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
      ≤ ∫ p : ℝ × ℝ, Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p :=
        integral_mono hint hint2 hpoint
    _ = Real.exp ((4 * c + 2 * δ) * ε) * ∫ p : ℝ × ℝ, Jker ρ ε p := by
        rw [MeasureTheory.integral_const_mul]
    _ = Real.exp ((4 * c + 2 * δ) * ε) := by
        rw [Jker_integral_eq_one ρ hρ hε, mul_one]

/-- **The weighted `H^k`-bound for `J_ε`** in `ℝ≥0∞`: assembling the pointwise slot sum, Tonelli
and the shift step. -/
theorem ofReal_HkSq_Jeps_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hF : Work.Spaces.HkMem α k f) (hFJ : Work.Spaces.HkMem α k (Jeps ρ ε f))
    {c δ : ℝ} (hc0 : 0 ≤ c) (hδ0 : 0 ≤ δ)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
    (hJac : ∀ s ζ p₁ p₂ : ℝ, logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * logJac (s - p₁) (ζ - p₂)) :
    ENNReal.ofReal (Work.Spaces.HkSq α k (Jeps ρ ε f))
      ≤ ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad :=
    continuousOn_HkIntegrand_Quad α k hf
  set C : ENNReal := ENNReal.ofReal (Work.Spaces.HkSq α k f) with hC
  set E1 : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
    with hE1
  set E2 : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
    with hE2
  set E3 : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
    with hE3
  set K : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Jker ρ ε p) with hK
  set Φ : ℝ → ℝ → ENNReal := fun z θ =>
    ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ) with hΦ
  set Ψ : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal
    (Real.exp (δ * (|p.1| + |p.2|))) * C with hΨ
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k (Jeps ρ ε f))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ := by
    rw [hΦ]
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFJ.2 (Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ)]
    exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici (fun z hz =>
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hFJ.1 z hz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ))
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
      ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
              (thShift θ p.2))) := by
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z hz =>
      MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ => ?_
    rw [hΦ, hK, hE1]
    exact ofReal_GJ_le ρ hρ hε hα hf hWη hWγ hz hθ k
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)))
      = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                (thShift θ p.2)))) := by
    rw [hK, hE1]
    exact fubini_shift hρ.cont hcont
  have h4 : (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                (thShift θ p.2))))
      ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (E2 p * C)) := by
    refine lintegral_mono fun p => mul_le_mul_right ?_ _
    rw [hE2, hC]
    exact integral_shift_le hJac hF hcont p
  have h5 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
      = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := by
    have hAB : ∀ p : ℝ × ℝ, E1 p * E2 p = E3 p := by
      intro p
      rw [hE1, hE2, hE3, ofReal_exp_mul]
      congr 2
      ring
    have hstep1 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
        = ∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C :=
      lintegral_congr fun p => by ring
    have hstep2 : (∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C)
        = (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) * C :=
      MeasureTheory.lintegral_mul_const' C _ ENNReal.ofReal_ne_top
    have hstep3 : (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) = ∫⁻ p : ℝ × ℝ, K p * E3 p :=
      lintegral_congr fun p => by rw [hAB p]
    rw [hstep1, hstep2, hstep3, mul_comm]
  have h6 : (∫⁻ p : ℝ × ℝ, K p * E3 p) ≤ ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε)) := by
    rw [hK, hE3]
    exact Jker_exp_integral_le hρ hε hc0 hδ0
  calc ENNReal.ofReal (Work.Spaces.HkSq α k (Jeps ρ ε f))
      = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ) := h1
    _ ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
              (thShift θ p.2))) := h2
    _ = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                (thShift θ p.2)))) := h3
    _ ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C)) := h4
    _ = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := h5
    _ ≤ C * ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε)) :=
        mul_le_mul_right h6 C
    _ = ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by rw [hC, mul_comm]

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.slot_route_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- context: namespace Work.FTS.StrongEps.StepFacts. `mixed j i = D_z^j D_θ^i`, `DthIter i = D_θ^i`,
-- `Wt α z θ = w z * sin(2θ)^{-γ/2}` with `w z = (1+z)²/z²`; the conclusions are stated as a triple conjunction.
theorem slot_route_bounds (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) :
    (∀ {α c z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
      {j i : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i)
      (hcomm : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = ∫ p : ℝ × ℝ,
            deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
            * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))
      (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)),
      (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ (∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
          * ∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
    ∧ (∀ {c z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
      {j : ℕ} (hj : 1 ≤ j)
      (hcomm : Work.Spaces.DzIter j (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = ∫ p : ℝ × ℝ,
            deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
            * Work.Spaces.DzIter (j - 1) f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))
      (hW : ∀ p : ℝ × ℝ,
        Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          ≤ Real.exp (c * (|p.1| + |p.2|))
            * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                  ^ (Work.Spaces.eta / 2))),
      (Work.Spaces.DzIter j (Work.FTS.StrongEps.Jeps ρ ε f) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|)
          * ∫ p : ℝ × ℝ,
              |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.DzIter (j - 1) f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                    / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                      ^ (Work.Spaces.eta / 2))) ^ 2)
    ∧ (∀ {α c z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
      {i : ℕ} (hi : 2 ≤ i)
      (hcomm : Work.Spaces.DthIter i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = 2 * ∫ p : ℝ × ℝ,
            deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2
            * Work.Spaces.DthIter (i - 1) f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))
      (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)),
      (Work.Spaces.DthIter i (Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ 4 * (∫ p : ℝ × ℝ,
              |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|)
          * ∫ p : ℝ × ℝ,
              |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.DthIter (i - 1) f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the mixed `z`-slots, with the `Wt`-weight
    intro α c z θ hz hθ j i hj hi hcomm hW
    have hKint : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|) := by
      simpa only [mul_one] using
        srb_integrable_abs_deriv_fst_mul ρ hρ hε
          (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    have hG : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.mixed (j - 1) i f x y)
        (HkSqAux.continuousOn_mixed_region hz hε hθ hf (j - 1) i)
    have hWc : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ (A := fun x y => Work.Spaces.Wt α x y)
        (HkSqAux.continuousOn_Wt_region hz hε hθ)
    have hQ : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
      have hB : ContinuousOn (fun p : ℝ × ℝ =>
          Real.exp (2 * c * (|p.1| + |p.2|))
            * (Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2)
                * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
          (Metric.closedBall (0 : ℝ × ℝ) ε) :=
        (srb_continuous_exp_two c).continuousOn.mul ((hG.mul hWc).pow 2)
      simpa only [mul_assoc] using srb_integrable_abs_deriv_fst_mul ρ hρ hε hB
    have hK2 : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * (Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α z θ) ^ 2) :=
      srb_integrable_abs_deriv_fst_mul ρ hρ hε
        ((hG.mul continuousOn_const).pow 2)
    exact srb_cs_core
      (K := fun p : ℝ × ℝ => deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1)
      (G := fun p : ℝ × ℝ =>
        Work.Spaces.mixed (j - 1) i f (zShift z p.1) (thShift θ p.2))
      (W := fun p : ℝ × ℝ => Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
      (W₀ := Work.Spaces.Wt α z θ) (c := c)
      (M := Work.Spaces.mixed j i (Jeps ρ ε f) z θ)
      (srb_Wt_nonneg α hz hθ) hW hKint hQ hK2 hcomm
  · -- the pure `z`-slots, with the `η`-weight
    intro c z θ hz hθ j hj hcomm hW
    have hKint : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|) := by
      simpa only [mul_one] using
        srb_integrable_abs_deriv_fst_mul ρ hρ hε
          (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    have hG : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.DzIter (j - 1) f x y)
        (HkSqAux.continuousOn_DzIter_region hz hε hθ hf (j - 1))
    have hWc : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.w (zShift z p.1)
          / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.w x / (Real.sin (2 * y)) ^ (Work.Spaces.eta / 2))
        (HkSqAux.continuousOn_wdiv_region hz hε hθ)
    have hQ : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w (zShift z p.1)
                  / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      have hB : ContinuousOn (fun p : ℝ × ℝ =>
          Real.exp (2 * c * (|p.1| + |p.2|))
            * (Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2)
                * (Work.Spaces.w (zShift z p.1)
                    / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
          (Metric.closedBall (0 : ℝ × ℝ) ε) :=
        (srb_continuous_exp_two c).continuousOn.mul ((hG.mul hWc).pow 2)
      simpa only [mul_assoc] using srb_integrable_abs_deriv_fst_mul ρ hρ hε hB
    have hK2 : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1|
          * (Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      srb_integrable_abs_deriv_fst_mul ρ hρ hε
        ((hG.mul continuousOn_const).pow 2)
    exact srb_cs_core
      (K := fun p : ℝ × ℝ => deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1)
      (G := fun p : ℝ × ℝ => Work.Spaces.DzIter (j - 1) f (zShift z p.1) (thShift θ p.2))
      (W := fun p : ℝ × ℝ =>
        Work.Spaces.w (zShift z p.1)
          / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2))
      (W₀ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) (c := c)
      (M := Work.Spaces.DzIter j (Jeps ρ ε f) z θ)
      (srb_wdiv_nonneg hz hθ) hW hKint hQ hK2 hcomm
  · -- the pure `θ`-slots, with the `Wt`-weight and the factor `2` of the routed identity
    intro α c z θ hz hθ i hi hcomm hW
    have hKint : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2|) := by
      simpa only [mul_one] using
        srb_integrable_abs_deriv_snd_mul ρ hρ hε
          (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    have hG : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ
        (A := fun x y => Work.Spaces.DthIter (i - 1) f x y)
        (HkSqAux.continuousOn_mixed_region hz hε hθ hf 0 (i - 1))
    have hWc : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall (0 : ℝ × ℝ) ε) :=
      HkSqAux.continuousOn_shift_ball hz hθ (A := fun x y => Work.Spaces.Wt α x y)
        (HkSqAux.continuousOn_Wt_region hz hε hθ)
    have hQ : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2|
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * (Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
      have hB : ContinuousOn (fun p : ℝ × ℝ =>
          Real.exp (2 * c * (|p.1| + |p.2|))
            * (Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2)
                * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
          (Metric.closedBall (0 : ℝ × ℝ) ε) :=
        (srb_continuous_exp_two c).continuousOn.mul ((hG.mul hWc).pow 2)
      simpa only [mul_assoc] using srb_integrable_abs_deriv_snd_mul ρ hρ hε hB
    have hK2 : Integrable (fun p : ℝ × ℝ =>
        |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2|
          * (Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2)
              * Work.Spaces.Wt α z θ) ^ 2) :=
      srb_integrable_abs_deriv_snd_mul ρ hρ hε
        ((hG.mul continuousOn_const).pow 2)
    rw [hcomm]
    exact srb_cs_core_four
      (K := fun p : ℝ × ℝ => deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2)
      (G := fun p : ℝ × ℝ =>
        Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2))
      (W := fun p : ℝ × ℝ => Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
      (W₀ := Work.Spaces.Wt α z θ) (c := c)
      (I := ∫ p : ℝ × ℝ, deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2
        * Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2))
      (srb_Wt_nonneg α hz hθ) hW hKint hQ hK2 rfl

end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.PerTerm.perTermWlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.PerTerm

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono canonW_zero_z)

/-! ## Measure-theoretic bookkeeping on `Iθ` and `Iz` -/

private theorem restrict_Iθ_eq_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2))).symm

private theorem restrict_Iz_eq_Ioi :
    MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Set.Ici (0 : ℝ) :=
    MeasureTheory.Ioi_ae_eq_Ici
  simpa [Work.Spaces.Iz] using (MeasureTheory.Measure.restrict_congr_set h).symm

private theorem integral_Iθ_mono_ae {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), f θ ≤ g θ)
    (h0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ f θ)
    (hg : MeasureTheory.IntegrableOn g Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, g θ := by
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h0
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

private theorem integral_Iz_mono_ae {f g : ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), f z ≤ g z)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ f z)
    (hg : MeasureTheory.IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iz_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h0
  · rw [restrict_Iz_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-- If `F` is continuous on the open quadrant, vanishes at `z = 0`, and is dominated on the
open quadrant by `H` whose angular slices and marginal are integrable, then the angular slices
and the marginal of `F` are integrable. -/
private theorem integrableConjuncts {F H : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hH : MeasureTheory.AEStronglyMeasurable (Function.uncurry H)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hzero : ∀ θ : ℝ, F 0 θ = 0)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => H z θ) Work.Spaces.Iθ)
    (hmarg : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, H z θ) Work.Spaces.Iz)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |F z θ| ≤ H z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz := by
  have hslF : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      rw [show (fun θ : ℝ => F 0 θ) = fun _ => (0 : ℝ) from funext fun θ => hzero θ]
      exact integrableOn_zero
    · refine Integrable.mono' (hsl z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hF hzpos) ?_
      rw [restrict_Iθ_eq_Ioo]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs]
      exact hpt z θ hzpos hθ.1 hθ.2
  refine ⟨hslF, ?_⟩
  refine Integrable.mono' hmarg
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd _ hF)) ?_
  rw [restrict_Iz_eq_Ioi]
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  rw [Real.norm_eq_abs]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  refine integral_mono_ae ((hslF z (Set.mem_Ici.mpr hz.le)).abs)
    (hsl z (Set.mem_Ici.mpr hz.le)) ?_
  rw [restrict_Iθ_eq_Ioo]
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  exact hpt z θ hz hθ.1 hθ.2

/-! ## Continuity of the canonical weight on the open quadrant -/

private theorem continuousOn_canonW (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
    have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
    have h0 : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)), p.1 ^ 2 ≠ 0 :=
      fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
    have h3 := ContinuousOn.div₀ (f := fun p : ℝ × ℝ => (1 + p.1) ^ 2)
      (g := fun p : ℝ × ℝ => p.1 ^ 2)
      (s := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) h1 h2 h0
    simpa only [Work.Spaces.w] using h3
  have hs : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  have hspos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 < Real.sin (2 * p.2) :=
    fun p hp => Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hs' := ContinuousOn.rpow_const (f := fun p : ℝ × ℝ => Real.sin (2 * p.2)) (p := -q) hs
    (fun p hp => Or.inl (ne_of_gt (hspos p hp)))
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * Real.sin (2 * p.2) ^ (-q))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hw.pow 2).mul hs'
  simpa only [canonW] using hmain

/-! ## Pointwise bounds for the leaf weights -/


/-- For `α > 0` one has `η ≤ γ`. -/
private theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

/-! ## The lemma -/


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDthW.PerTerm
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.RowFlatAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option quotPrecheck false in
local notation "PM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

/-! ## Elementary facts about the open quadrant and the leaf weights -/



theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _


theorem leafEta_eq_canonW : Work.FTS.TransportS.leafEta
    = Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta := rfl

theorem leafGam_eq_canonW (α : ℝ) : Work.FTS.TransportS.leafGam α
    = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) := rfl

theorem leafOne_eq_canonW_zero : Work.FTS.TransportS.leafOne
    = Work.FTS.TransportS.SlotT2.canonW 0 := by
  funext z θ
  simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, Real.rpow_zero]


/-! ## Dominations of the `f`-slots by the `ℋ⁶`-integrand, at a reduced weight -/




/-- Measurability of a `mixed` derivative on `PM`. -/
theorem aesm_mixed {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) PM :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf j i)













end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.divz_DzIter_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open Set Filter

/-!
# `|D_z^b (z/(1+z))| ≤ 10^6 · z/(1+z)` for `b ≤ 6`

`D_z = z ∂_z` expands in terms of the ordinary derivatives as
`D_z^b φ = ∑_{k ≤ b} S(b,k) z^k ∂_z^k φ` (`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`),
where `S(b,k)` is the Stirling number of the second kind.  For `φ(z) = z/(1+z) = t`
the two ingredients are

* `|z^k ∂_z^k φ| ≤ k! · t` for `k ≤ 6` (the closed form of `∂_z^k φ` is
  `(-1)^{k-1} k! / (1+z)^{k+1}`, so `|z^k ∂_z^k φ| = k! z^k/(1+z)^{k+1} ≤ k! t`),
* `∑_k S(b,k) = bell b ≤ 1000` for `b ≤ 6` (Bell numbers `1,1,2,5,15,52,203`).

Hence `|D_z^b φ| ≤ 1000 · 720 · t ≤ 10^6 · t`.
-/

/-- `z ↦ z/(1+z)` is `C^∞` (in the honest smooth order) on `(0,∞)`. -/
private lemma contDiffOn_divz :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z / (1 + z)) (Set.Ioi 0) := by
  refine ContDiffOn.div contDiffOn_id (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
  positivity

/-- `k! · z^k/(1+z)^{k+1} ≤ 720 · z/(1+z)` for `1 ≤ k ≤ 6`, `z > 0`. -/
private lemma fact_div_le (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (z : ℝ) (hz : 0 < z) :
    (k.factorial : ℝ) * z ^ k / (1 + z) ^ (k + 1) ≤ 720 * (z / (1 + z)) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : (k.factorial : ℝ) ≤ 720 := by
    have h : k.factorial ≤ 720 := by interval_cases k <;> norm_num
    exact_mod_cast h
  have hzk : z ^ k = z * z ^ (k - 1) := by
    nth_rewrite 1 [show k = (k - 1) + 1 from by omega]
    rw [pow_succ']
  have hzpk : z ^ (k - 1) ≤ (1 + z) ^ k := by
    calc z ^ (k - 1) ≤ (1 + z) ^ (k - 1) := pow_le_pow_left₀ hz.le (by linarith) (k - 1)
      _ ≤ (1 + z) ^ k := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + z) (by omega)
  have hkey : (k.factorial : ℝ) * (z * z ^ (k - 1)) ≤ 720 * (z * (1 + z) ^ k) := by
    calc (k.factorial : ℝ) * (z * z ^ (k - 1)) = z * ((k.factorial : ℝ) * z ^ (k - 1)) := by ring
      _ ≤ z * (720 * (1 + z) ^ k) := by
          refine mul_le_mul_of_nonneg_left ?_ hz.le
          calc (k.factorial : ℝ) * z ^ (k - 1) ≤ 720 * z ^ (k - 1) :=
                mul_le_mul_of_nonneg_right hfac (pow_nonneg hz.le _)
            _ ≤ 720 * (1 + z) ^ k := mul_le_mul_of_nonneg_left hzpk (by norm_num)
      _ = 720 * (z * (1 + z) ^ k) := by ring
  have hpow : (1 + z) ^ (k + 1) = (1 + z) ^ k * (1 + z) := pow_succ _ _
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ (k + 1))]
  rw [show 720 * (z / (1 + z)) * (1 + z) ^ (k + 1) = 720 * (z * (1 + z) ^ k) from by
    rw [hpow]
    field_simp]
  rw [hzk]
  exact hkey

/-- The closed form of `∂_z^k (z/(1+z))`: for `k ≥ 1`,
`∂_z^k (z/(1+z)) = (-1)^{k-1} k!/(1+z)^{k+1}`. -/
private lemma pzIter_divz_closed (k : ℕ) (hk1 : 1 ≤ k) (z θ : ℝ) (hz : 0 < z) :
    Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ
      = (-1 : ℝ) ^ (k - 1) * (k.factorial : ℝ) / (1 + z) ^ (k + 1) := by
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.FTS.NonlinRows.pzIter_radial_fn (fun z => z / (1 + z)) k z θ]
  exact Work.FTS.NonlinRows.iter_deriv_u15_pos k hk1 z hz1

/-- `|z^k ∂_z^k (z/(1+z))| ≤ 720 · z/(1+z)` for `1 ≤ k ≤ 6`, `z > 0`. -/
private lemma pzIter_divz_bound (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (z θ : ℝ) (hz : 0 < z) :
    |z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ| ≤ 720 * (z / (1 + z)) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [pzIter_divz_closed k hk1 z θ hz]
  have habs : |z ^ k * ((-1 : ℝ) ^ (k - 1) * (k.factorial : ℝ) / (1 + z) ^ (k + 1))|
      = (k.factorial : ℝ) * z ^ k / (1 + z) ^ (k + 1) := by
    rw [show z ^ k * ((-1 : ℝ) ^ (k - 1) * (k.factorial : ℝ) / (1 + z) ^ (k + 1))
        = (-1 : ℝ) ^ (k - 1) * ((k.factorial : ℝ) * z ^ k / (1 + z) ^ (k + 1)) from by ring]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (by positivity)
  rw [habs]
  exact fact_div_le k hk1 hk6 z hz

/-- The `k = 0` case of the weighted bound. -/
private lemma pzIter_divz_bound_zero (z θ : ℝ) (hz : 0 < z) :
    |z ^ 0 * Work.Spaces.pzIter 0 (fun z _ => z / (1 + z)) z θ| ≤ 720 * (z / (1 + z)) := by
  have ht : 0 < z / (1 + z) := by positivity
  simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero]
  rw [abs_of_pos ht]
  linarith

/-- The Bell numbers of the rows `b ≤ 6` are `1,1,2,5,15,52,203`, all `≤ 1000`. -/
private lemma bell_le_1000 (b : ℕ) (hb : b ≤ 6) : Work.Spaces.bell b ≤ 1000 := by
  interval_cases b <;> decide

theorem divz_DzIter_le :
    ∀ b : ℕ, b ≤ 6 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ 1000000 * (z / (1 + z)) := by
  intro b hb z θ hz
  have ht : 0 ≤ z / (1 + z) := by positivity
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' : ℝ => (fun z _ => z / (1 + z)) z' θ) (Set.Ioi 0) := contDiffOn_divz
  rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := fun z _ => z / (1 + z)) (θ := θ)
    hsmooth b z hz]
  have hbound : ∀ k ≤ b,
      |z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ| ≤ 720 * (z / (1 + z)) := by
    intro k hk
    rcases eq_or_ne k 0 with hk0 | hk0
    · subst hk0
      exact pzIter_divz_bound_zero z θ hz
    · exact pzIter_divz_bound k (Nat.one_le_iff_ne_zero.mpr hk0) (le_trans hk hb) z θ hz
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (720 * (z / (1 + z)))
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ) hbound
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 1000 := by
    exact_mod_cast bell_le_1000 b hb
  calc |∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k (fun z _ => z / (1 + z)) z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * (720 * (z / (1 + z))) := hsum
    _ ≤ 1000 * (720 * (z / (1 + z))) := mul_le_mul_of_nonneg_right hbell (by positivity)
    _ = 720000 * (z / (1 + z)) := by ring
    _ ≤ 1000000 * (z / (1 + z)) := mul_le_mul_of_nonneg_right (by norm_num) ht

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowA1SmallPair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology

/-! ## The `a₁ = a` half of the `A1`-small row

The row `rowA1SmallPair` pairs a leaf weight `ρ` of the transport unfolding with the two
slots `D_z^{b+1-b₁}D_θ^{a-a₁} f` and `D_z^bD_θ^a f` of the level-six datum `f`, under the
"small pair" constraints `a₁ + b₁ ≤ 2`, `a₁ ≥ 1`, `a₁ ≤ a`, `b₁ ≤ b`, `a + b ≤ 6`.

Both slots have total order `≤ 6`: the first because
`(a - a₁) + (b + 1 - b₁) = a + b + 1 - (a₁ + b₁) ≤ a + b ≤ 6`, the second by `hab`.

* In the case `1 ≤ a - a₁` the first slot carries a `θ`-derivative and the statement is
  exactly the already-proved `slotWeightBound` (the leaf weight is dominated by the slot
  weight `slotW α a` of the *second* slot, and both slots are dominated by `HkIntegrand`).
* In the remaining case `a - a₁ = 0` (i.e. `a = a₁`, so `a ≥ 1`) the first slot is a pure
  `D_z`-slot, whose weight is `Whz` rather than `Wm`.  The hypothesis `hne` excludes
  precisely the only combination in which this fails: the leaf weight `w² sin(2θ)^{-γ}`
  (`= leafGam α`, admissible here because `a ≥ 1`) with `a₁ = a`; the exponent `-γ` of that
  leaf weight is then *larger* than the exponent `-(η+γ)/2` available from the AM–GM over
  the two slots.  For the two surviving leaf weights (`w² sin(2θ)^{-η}` and `w²`) the
  `Whz`-route closes exactly as in `slotWeightBound`, the second slot being compared with
  its `Wm`-square via `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}`. -/

/-- `w z ≥ 0` for every real `z` (`w z = (1+z)²/z²` is a quotient of squares). -/
private theorem w_nonneg_l (z : ℝ) : 0 ≤ Work.Spaces.w z :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `Whz z θ ≥ 0` on the closed quadrant. -/
private theorem Whz_nonneg_l {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.H2.Whz z θ := by
  rw [Work.FTS.H2.Whz_eq]
  exact div_nonneg (w_nonneg_l z)
    (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **AM–GM for two slots sharing the weight `W`**: if the two weighted slots are each
dominated by `H` then so is the product of the two slots times `W²`. -/
private theorem amgm_mul_le {X Y W H : ℝ} (hW : 0 ≤ W)
    (hX : (X * W) ^ 2 ≤ H) (hY : (Y * W) ^ 2 ≤ H) :
    |X| * |Y| * W ^ 2 ≤ H := by
  have h1 : |X| * |Y| * W ^ 2 = |X * W| * |Y * W| := by
    simp only [abs_mul, abs_of_nonneg hW]
    ring
  rw [h1]
  nlinarith [sq_nonneg (|X * W| - |Y * W|), sq_abs (X * W), sq_abs (Y * W), hX, hY]

theorem rowA1SmallPair {α : ℝ} {f : ℝ → ℝ → ℝ} {a b a₁ b₁ : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (ha₁ : 1 ≤ a₁) (ha₁a : a₁ ≤ a) (hb₁ : b₁ ≤ b) (hab₁ : a₁ + b₁ ≤ 2) (hab : a + b ≤ 6)
    (hne : ¬ (a₁ = a ∧ ρ = Work.FTS.TransportS.leafGam α)) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ|
        * |Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  intro z θ _hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  by_cases hcase : 1 ≤ a - a₁
  · -- the first slot carries a `θ`-derivative: `slotWeightBound`
    have huv : (a - a₁) + (b + 1 - b₁) ≤ 6 := by omega
    exact Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub.slotWeightBound hα a b
      (a - a₁) (b + 1 - b₁) hab hcase huv hleaf z θ _hz hθ0 hθ1
  · -- the first slot is a pure `D_z`-slot: `a₁ = a`, and `hne` rules out `leafGam`
    have hane : a - a₁ = 0 := by omega
    have haneq : a = a₁ := by omega
    have ha1 : 1 ≤ a := by omega
    -- the leaf weight is dominated by `(Whz)²`
    have hρWhz : ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
      have hsq := (Work.FTS.H2.Whz_Wm_sq α hα z θ hθI).1
      rcases hleaf with h | h | ⟨_, hg⟩
      · rw [h]
        exact le_of_eq hsq.symm
      · simp only [h, Work.FTS.TransportS.leafOne]
        rw [hsq]
        have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg ⟨hθ0, hθ1⟩
        simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.w z))
      · exact absurd ⟨haneq.symm, hg⟩ hne
    -- the two slots, weighted by `Whz`, are dominated by `HkIntegrand α 6 f`
    have hb6 : b + 1 - b₁ ≤ 6 := by omega
    have hX : (Work.Spaces.mixed (b + 1 - b₁) 0 f z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ (b + 1 - b₁) hb6
      simpa only [Work.Spaces.mixed_zero_right, Work.FTS.H2.Whz_eq] using h
    have hWm2 : (Work.FTS.H2.Whz z θ) ^ 2 ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
      have hsq := Work.FTS.H2.Whz_Wm_sq α hα z θ hθI
      rw [hsq.1, hsq.2]
      exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
    have hY : (Work.Spaces.mixed b a f z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have hY1 := Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b ha1 hab
      have h2 : (Work.Spaces.mixed b a f z θ * Work.FTS.H2.Whz z θ) ^ 2
          ≤ (Work.Spaces.mixed b a f z θ * Work.FTS.H2.Wm α z θ) ^ 2 := by
        rw [mul_pow, mul_pow]
        exact mul_le_mul_of_nonneg_left hWm2 (sq_nonneg _)
      exact le_trans h2 (by simpa only [Work.FTS.H2.Wm_eq] using hY1)
    have hamgm : |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ| * |Work.Spaces.mixed b a f z θ|
        * (Work.FTS.H2.Whz z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      amgm_mul_le (Whz_nonneg_l hθI) hX hY
    rw [hane]
    calc ρ z θ * |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ|
            * |Work.Spaces.mixed b a f z θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hρWhz (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ| * |Work.Spaces.mixed b a f z θ|
            * (Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := hamgm

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.phiDzdIter6_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology ContDiff
open Set Filter

/-!
# `|D_z^b (z/(1+z))| ≤ 10000` for `b ≤ 6` on `[0,∞)`

The multiplier `φ(z) = z/(1+z)` is smooth on `(-1,∞)`.  Writing `D_z = z ∂_z` and expanding
`D_z^b` in the Stirling numbers of the second kind,

    D_z^b φ = ∑_{k ≤ b} S(b,k) z^k ∂_z^k φ ,

while `z/(1+z) = 1 - (1+z)⁻¹` gives `∂_z^k φ = ± k! (1+z)^{-(k+1)}` for `k ≥ 1`, hence the
weighted slots obey `|z^k ∂_z^k φ(z)| ≤ k!` on `z ≥ 0`.  Therefore

    |D_z^b φ(z)| ≤ ∑_{k ≤ b} S(b,k) k! ,

and the numerical values of the last sum for `b ≤ 6` are `1, 1, 3, 13, 75, 541, 4683`,
all of them at most `10000`.
-/

/-- `z/(1+z)` is smooth (analytic) on `(-1,∞)`. -/
theorem contDiffOn_div_one_add : ContDiffOn ℝ ⊤ (fun z : ℝ => z / (1 + z)) (Set.Ioi (-1)) := by
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 : ℝ) + z) (Set.Ioi (-1)) := by fun_prop
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => z) (Set.Ioi (-1)) := by fun_prop
  refine ContDiffOn.div hnum hden ?_
  intro z hz
  simp only [Set.mem_Ioi] at hz
  linarith

/-- The Stirling-weighted factorial mass `∑_{k ≤ b} S(b,k) k!` is at most `10000` for `b ≤ 6`
(the values being `1, 1, 3, 13, 75, 541, 4683`). -/
theorem scoef_fact_sum_le (b : ℕ) (hb : b ≤ 6) :
    (∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (k.factorial : ℝ)) ≤ 10000 := by
  have hnat : (∑ k ∈ Finset.range (b + 1), Work.Spaces.scoef b k * k.factorial) ≤ 10000 := by
    interval_cases b <;> decide
  exact_mod_cast hnat

/-- The weighted derivative slots of `z/(1+z)`: `|z^k ∂_z^k (z/(1+z))| ≤ k!` for `z ≥ 0`. -/
theorem zpow_iteratedDeriv_div_le (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |z ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z| ≤ (k.factorial : ℝ) := by
  have h1z : 0 < 1 + z := by linarith
  have hge : 0 ≤ z / (1 + z) := div_nonneg hz h1z.le
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have hfac : ((0 : ℕ).factorial : ℝ) = 1 := by norm_num
    rw [iteratedDeriv_zero, pow_zero, one_mul, abs_of_nonneg hge, hfac]
    rw [div_le_one h1z]
    linarith
  · have hz1 : -1 < z := by linarith
    have hw := Work.FTS.PhiStar.StarPkgo2Aux.weighted_iteratedDeriv_div k hk z hz1
    have hzle : |z| ^ k ≤ (z + 1) ^ k := by
      rw [abs_of_nonneg hz]
      exact pow_le_pow_left₀ hz (by linarith) k
    have h2 : |z| ^ k * |iteratedDeriv k (fun z : ℝ => z / (1 + z)) z|
        ≤ (z + 1) ^ k * |iteratedDeriv k (fun z : ℝ => z / (1 + z)) z| :=
      mul_le_mul_of_nonneg_right hzle (abs_nonneg _)
    have h3 : (z + 1) ^ k * |iteratedDeriv k (fun z : ℝ => z / (1 + z)) z|
        = |(z + 1) ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
    have h4 : |(z + 1) ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z|
        = (k.factorial : ℝ) * (1 + z)⁻¹ := by
      rw [hw, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (Nat.cast_nonneg k.factorial),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z)⁻¹)]
    have h5 : (k.factorial : ℝ) * (1 + z)⁻¹ ≤ (k.factorial : ℝ) := by
      have hle : (1 + z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ 1 + z)
      have := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg k.factorial : (0 : ℝ) ≤ (k.factorial : ℝ))
      simpa using this
    rw [abs_mul, abs_pow]
    linarith [h2, h3.le, h3.ge, h4.le, h4.ge, h5]

theorem phiDzdIter6_bound (b : ℕ) (hb : b ≤ 6) (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z| ≤ 10000 := by
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    have h0 := zpow_iteratedDeriv_div_le 0 z hz
    have h0' : |(fun z : ℝ => z / (1 + z)) z| ≤ 1 := by simpa using h0
    simp only [Work.Elliptic.DzdIter_zero]
    linarith
  · have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have hz' : z ∈ Set.Ioi (-1) := by
      simp only [Set.mem_Ioi]
      linarith
    have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
        ContDiffOn ℝ ⊤ (fun z' => (fun z _ : ℝ => z / (1 + z)) z' θ) (Set.Ioi (-1)) :=
      fun θ _ => contDiffOn_div_one_add
    have hDz : Work.Elliptic.DzdIter b (fun z : ℝ => z / (1 + z)) z
        = Work.Spaces.DzIter b (fun z _ : ℝ => z / (1 + z)) z 0 :=
      (Work.Elliptic.DzIter_rad (fun z : ℝ => z / (1 + z)) b z 0).symm
    rw [hDz, Work.Spaces.DzIter_eq_sum_scoef hsmooth b z hz' 0 h0I]
    have hterm : ∀ k ∈ Finset.range (b + 1),
        |(Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k
            (fun z _ : ℝ => z / (1 + z)) z 0)|
          ≤ (Work.Spaces.scoef b k : ℝ) * (k.factorial : ℝ) := by
      intro k hk
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef b k))]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (Work.Spaces.scoef b k))
      rw [Work.Spaces.pzIter_eq_iteratedDeriv k (fun z _ : ℝ => z / (1 + z)) z 0]
      exact zpow_iteratedDeriv_div_le k z hz
    calc |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (z ^ k *
            Work.Spaces.pzIter k (fun z _ : ℝ => z / (1 + z)) z 0)|
        ≤ ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (k.factorial : ℝ) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
      _ ≤ 10000 := scoef_fact_sum_le b hb

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupOpenH2A =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false


theorem zavg_A {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) {z₀ : ℝ} (hz₀ : 0 < z₀) :
    (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
        (h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 9 * Work.Spaces.HkSq α 2 h := by
  set sl0 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.DzIter 0 h z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hsl0def
  set sl1 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.DzIter 1 h z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hsl1def
  set Φ : ℝ → ℝ → ℝ := fun z θ => h z θ * (Work.Spaces.w z * Real.sqrt z)
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) with hΦdef
  set Φ' : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)
    + h z θ * dWsq z) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) with hΦ'def
  have hsl0c : ContinuousOn (Function.uncurry sl0) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hsl0def]
    exact (hso.continuousOn_summand 0).pow 2
  have hsl1c : ContinuousOn (Function.uncurry sl1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hsl1def]
    exact (hso.continuousOn_summand 1).pow 2
  have hSle0 : ∀ z θ, sl0 z θ ≤ Work.Spaces.HkIntegrand α 2 h z θ := by
    intro z θ; rw [hsl0def]
    exact Work.Spaces.sq_le_HkIntegrand_z α 2 h z θ 0 (by norm_num)
  have hSle1 : ∀ z θ, sl1 z θ ≤ Work.Spaces.HkIntegrand α 2 h z θ := by
    intro z θ; rw [hsl1def]
    exact Work.Spaces.sq_le_HkIntegrand_z α 2 h z θ 1 (by norm_num)
  have hinner0 : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => sl0 z θ) Work.Spaces.Iθ :=
    slot_inner hsl0c hmem (fun _ _ => sq_nonneg _) hSle0
  have hinner1 : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => sl1 z θ) Work.Spaces.Iθ :=
    slot_inner hsl1c hmem (fun _ _ => sq_nonneg _) hSle1
  have houter0 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sl0 z θ) Work.Spaces.Iz :=
    slot_outer hsl0c hmem (fun _ _ => sq_nonneg _) hSle0
  have houter1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sl1 z θ) Work.Spaces.Iz :=
    slot_outer hsl1c hmem (fun _ _ => sq_nonneg _) hSle1
  have hIS0 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sl0 z θ) (Set.Ioi 0) :=
    houter0.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hIS1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sl1 z θ) (Set.Ioi 0) :=
    houter1.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hL2Sq0 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sl0 z θ)
      ≤ Work.Spaces.HkSq α 2 h := by
    have h := Work.Spaces.L2Sq_DzIter_le_HkSq α 2 h hmem 0 (by norm_num)
    simpa only [Work.Spaces.L2Sq, hsl0def] using h
  have hL2Sq1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sl1 z θ)
      ≤ Work.Spaces.HkSq α 2 h := by
    have h := Work.Spaces.L2Sq_DzIter_le_HkSq α 2 h hmem 1 (by norm_num)
    simpa only [Work.Spaces.L2Sq, hsl1def] using h
  -- ## continuity and differentiability of `Φ`, `Φ'`
  have hΦcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hΦdef]
    show ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2 * (Work.Spaces.w p.1 * Real.sqrt p.1)
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta / 2))) _
    exact (hso.continuousOn.mul continuousOn_w_mul_sqrt).mul (continuousOn_sin_pow _)
  have hΦ'cont : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hΦ'def]
    show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pz h p.1 p.2 * (Work.Spaces.w p.1 * Real.sqrt p.1)
      + h p.1 p.2 * dWsq p.1) * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta / 2))) _
    exact (((hso.pz).continuousOn.mul continuousOn_w_mul_sqrt).add
      (hso.continuousOn.mul continuousOn_dWsq)).mul (continuousOn_sin_pow _)
  have hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ z ∈ Set.Ioi 0,
      HasDerivAt (fun z' => Φ z' θ) (Φ' z θ) z := by
    intro θ hθ z hz
    rw [hΦdef, hΦ'def]
    exact ((hso.hasDerivAt_slice hθ hz).mul (hasDerivAt_dWsq hz)).mul_const _
  -- ## the pointwise bound for `Φ'`
  have hbnd : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ, Φ' z θ ^ 2
      ≤ (2 / z) * sl1 z θ + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sl0 z θ := by
    intro z hz θ hθ
    rw [hΦ'def, hsl0def, hsl1def]
    have hsplit : ((Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)
          + h z θ * dWsq z) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        ≤ 2 * (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
          + 2 * (h z θ * dWsq z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2 := by
      nlinarith [sq_nonneg (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
        - h z θ * dWsq z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))]
    refine hsplit.trans ?_
    have h2 : 2 * (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = (2 / z) * (Work.Spaces.DzIter 1 h z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [pz_term_unfold h hz hθ, slot1_unfold h hθ]
      field_simp
      try ring
    have h3 : 2 * (h z θ * dWsq z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * (Work.Spaces.DzIter 0 h z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [d_term_unfold h hz hθ, slot0_unfold h hθ]
      field_simp
      try ring
    rw [h2, h3]
  have hG_pt : ∀ z ∈ Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, sl1 z θ) + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sl0 z θ) := by
    intro z hz
    have hmaj : IntegrableOn (fun θ => (2 / z) * sl1 z θ
        + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sl0 z θ) Work.Spaces.Iθ :=
      ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _).add
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
    have hle : (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((2 / z) * sl1 z θ
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sl0 z θ) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hmaj
        (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
          fun θ hθ => hbnd z hz θ hθ)
    rw [MeasureTheory.integral_add ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul] at hle
    have h1 : (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z
        ≤ ((2 / z) * (∫ θ in Work.Spaces.Iθ, sl1 z θ)
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, sl0 z θ)) * z :=
      mul_le_mul_of_nonneg_right hle hz.le
    have h2 : ((2 / z) * (∫ θ in Work.Spaces.Iθ, sl1 z θ)
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, sl0 z θ)) * z
        = 2 * (∫ θ in Work.Spaces.Iθ, sl1 z θ)
          + (z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))) * (∫ θ in Work.Spaces.Iθ, sl0 z θ) := by
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hz1 : (1 + z) ≠ 0 := by
        have : (0:ℝ) < 1 + z := by linarith [show (0:ℝ) < z from hz]
        exact ne_of_gt this
      field_simp
      try ring
    rw [h2] at h1
    have hzC : z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) ≤ 9 / 2 := by
      have h := abs_div_ge_le hz
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hz1 : (1 + z) ≠ 0 := by
        have : (0:ℝ) < 1 + z := by linarith [show (0:ℝ) < z from hz]
        exact ne_of_gt this
      have hkey : z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))
          = ((z - 3) ^ 2 / (1 + z) ^ 2) / 2 := by
        field_simp
        try ring
      rw [hkey]
      linarith
    have hb0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, sl0 z θ := integral_nonneg fun θ => sq_nonneg _
    have hb1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, sl1 z θ := integral_nonneg fun θ => sq_nonneg _
    nlinarith [h1, hzC, hb0, hb1]
  -- ## integrability of `Φ` and `Φ'` and their `z`-integrals
  have hF_eq : ∀ z ∈ Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z
      = ∫ θ in Work.Spaces.Iθ, sl0 z θ := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) = z * (∫ θ in Work.Spaces.Iθ, sl0 z θ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      simp only [hΦdef, hsl0def]
      rw [PhiA_sq_unfold h hz hθ, slot0_unfold h hθ]
      ring
    rw [h1, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  have hFin : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Φ z θ ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) = z * (∫ θ in Work.Spaces.Iθ, sl0 z θ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      simp only [hΦdef, hsl0def]
      rw [PhiA_sq_unfold h hz hθ, slot0_unfold h hθ]
      ring
    have heq : ∀ θ ∈ Work.Spaces.Iθ, Φ z θ ^ 2 = z * sl0 z θ := by
      intro θ hθ
      simp only [hΦdef, hsl0def]
      rw [PhiA_sq_unfold h hz hθ, slot0_unfold h hθ]
      ring
    have hbase : IntegrableOn (fun θ => z * sl0 z θ) Work.Spaces.Iθ :=
      (hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul z
    exact IntegrableOn.congr_fun hbase (fun θ hθ => (heq θ hθ).symm) measurableSet_Icc
  have hGin : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Φ' z θ ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hmaj : IntegrableOn (fun θ => (2 / z) * sl1 z θ
        + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sl0 z θ) Work.Spaces.Iθ :=
      ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _).add ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
    refine Integrable.mono' hmaj ?_ ?_
    · have h2 := Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ') hΦ'cont hz
      exact h2.pow 2
    · rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      exact Eventually.of_forall fun θ hθ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hbnd z hz θ hθ
  have hFint : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z) (Set.Ioi 0) :=
    IntegrableOn.congr_fun hIS0 (fun z hz => (hF_eq z hz).symm) measurableSet_Ioi
  have hGint : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) (Set.Ioi 0) := by
    have hmaj : IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ, sl1 z θ)
        + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sl0 z θ)) (Set.Ioi 0) :=
      ((hIS1.const_mul 2).add (hIS0.const_mul (9 / 2)))
    have haesm : AEStronglyMeasurable (fun z => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
        (volume.restrict (Set.Ioi 0)) := by
      have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ' p.1 p.2 ^ 2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
        have h3 := (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry Φ') hΦ'cont).pow 2
        have heq : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
          rw [Work.Spaces.Iz]
          exact MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
        rwa [heq]
      have h4 := hjoint.integral_prod_right'
      have heq2 : (fun z => ∫ θ, Φ' z θ ^ 2 ∂(volume.restrict Work.Spaces.Iθ))
          = (fun z => ∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) := by
        funext z; rfl
      rw [heq2] at h4
      exact h4.mul aestronglyMeasurable_id
    refine Integrable.mono' hmaj haesm ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun z hz => by
      rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun θ => sq_nonneg _) hz.le)]
      exact hG_pt z hz
  -- ## conclusion
  have hZ := SupOpenH2Z (z₀ := z₀) hz₀ hΦcont hΦ'cont hderiv hFin hGin hFint hGint
  have hLHS : (∫ θ in Work.Spaces.Iθ, Φ z₀ θ ^ 2)
      = (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
          (h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    simp only [hΦdef]
    rw [PhiA_sq_unfold h hz₀ hθ]
    try ring
  have hR1 : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
      ≤ Work.Spaces.HkSq α 2 h := by
    rw [show (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
        = ∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sl0 z θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun z hz => hF_eq z hz]
    rw [show (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sl0 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sl0 z θ) from
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    exact hL2Sq0
  have hR2 : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
      ≤ (13 / 2) * Work.Spaces.HkSq α 2 h := by
    have hle : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
        ≤ ∫ z in Set.Ioi 0, (2 * (∫ θ in Work.Spaces.Iθ, sl1 z θ)
            + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sl0 z θ)) :=
      MeasureTheory.integral_mono_of_nonneg
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz =>
          mul_nonneg (integral_nonneg fun θ => sq_nonneg _) hz.le)
        (((hIS1.const_mul 2).add (hIS0.const_mul (9 / 2))))
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => hG_pt z hz)
    have hsplit : (∫ z in Set.Ioi 0, (2 * (∫ θ in Work.Spaces.Iθ, sl1 z θ)
          + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sl0 z θ)))
        = 2 * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sl1 z θ))
          + (9 / 2) * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sl0 z θ)) := by
      rw [MeasureTheory.integral_add (hIS1.const_mul 2) (hIS0.const_mul (9 / 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hsplit] at hle
    have hA : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sl1 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sl1 z θ) :=
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
    have hB : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sl0 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sl0 z θ) :=
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
    rw [hA, hB] at hle
    linarith [hle, hL2Sq0, hL2Sq1]
  have hnn : 0 ≤ Work.Spaces.HkSq α 2 h := Work.Spaces.HkSq_nonneg α 2 h
  calc (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
        (h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (∫ θ in Work.Spaces.Iθ, Φ z₀ θ ^ 2) := hLHS.symm
    _ ≤ 2 * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
          + (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) := hZ
    _ ≤ 2 * Work.Spaces.HkSq α 2 h + (13 / 2) * Work.Spaces.HkSq α 2 h := by
        linarith [hR1, hR2]
    _ ≤ 9 * Work.Spaces.HkSq α 2 h := by linarith

-- the pointwise bound used above, stated separately to keep the main proof readable

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupOpenH2B =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem zavg_B {α : ℝ} {h : ℝ → ℝ → ℝ} (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) {z₀ : ℝ} (hz₀ : 0 < z₀) :
    (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dth h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ 9 * Work.Spaces.HkSq α 2 h := by
  have hγne : Work.Spaces.gam α ≠ 0 := gam_ne_zero hα
  set sm0 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 with hsm0def
  set sm1 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.mixed 1 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 with hsm1def
  set Φ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.Dth h z θ * (Work.Spaces.w z * Real.sqrt z)
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) with hΦdef
  set Φ' : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.pz (Work.Spaces.Dth h) z θ
    * (Work.Spaces.w z * Real.sqrt z) + Work.Spaces.Dth h z θ * dWsq z)
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) with hΦ'def
  have hsm0c : ContinuousOn (Function.uncurry sm0) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hsm0def]
    exact (((hso.mixed 0 1).continuousOn).mul (continuousOn_Wt α)).pow 2
  have hsm1c : ContinuousOn (Function.uncurry sm1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hsm1def]
    exact (((hso.mixed 1 1).continuousOn).mul (continuousOn_Wt α)).pow 2
  have hSle0 : ∀ z θ, sm0 z θ ≤ Work.Spaces.HkIntegrand α 2 h z θ := by
    intro z θ; rw [hsm0def]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 h z θ 1 0 (by norm_num) (by norm_num)
  have hSle1 : ∀ z θ, sm1 z θ ≤ Work.Spaces.HkIntegrand α 2 h z θ := by
    intro z θ; rw [hsm1def]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 2 h z θ 1 1 (by norm_num) (by norm_num)
  have hinner0 : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => sm0 z θ) Work.Spaces.Iθ :=
    slot_inner hsm0c hmem (fun _ _ => sq_nonneg _) hSle0
  have hinner1 : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => sm1 z θ) Work.Spaces.Iθ :=
    slot_inner hsm1c hmem (fun _ _ => sq_nonneg _) hSle1
  have houter0 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm0 z θ) Work.Spaces.Iz :=
    slot_outer hsm0c hmem (fun _ _ => sq_nonneg _) hSle0
  have houter1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm1 z θ) Work.Spaces.Iz :=
    slot_outer hsm1c hmem (fun _ _ => sq_nonneg _) hSle1
  have hIS0 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm0 z θ) (Set.Ioi 0) :=
    houter0.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hIS1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, sm1 z θ) (Set.Ioi 0) :=
    houter1.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hL2Sq0 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sm0 z θ)
      ≤ Work.Spaces.HkSq α 2 h := by
    have h := Work.Spaces.L2Sq_mixed_le_HkSq α 2 h hmem 1 0 (by norm_num) (by norm_num)
    simpa only [Work.Spaces.L2Sq, hsm0def] using h
  have hL2Sq1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sm1 z θ)
      ≤ Work.Spaces.HkSq α 2 h := by
    have h := Work.Spaces.L2Sq_mixed_le_HkSq α 2 h hmem 1 1 (by norm_num) (by norm_num)
    simpa only [Work.Spaces.L2Sq, hsm1def] using h
  have hΦcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hΦdef]
    show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth h p.1 p.2
      * (Work.Spaces.w p.1 * Real.sqrt p.1) * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) _
    exact (((hso.Dth).continuousOn.mul continuousOn_w_mul_sqrt)).mul (continuousOn_sin_pow _)
  have hΦ'cont : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hΦ'def]
    show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.Dth h) p.1 p.2
      * (Work.Spaces.w p.1 * Real.sqrt p.1) + Work.Spaces.Dth h p.1 p.2 * dWsq p.1)
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) _
    exact (((((hso.Dth).pz).continuousOn.mul continuousOn_w_mul_sqrt).add
      (((hso.Dth).continuousOn).mul continuousOn_dWsq))).mul (continuousOn_sin_pow _)
  have hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ z ∈ Set.Ioi 0,
      HasDerivAt (fun z' => Φ z' θ) (Φ' z θ) z := by
    intro θ hθ z hz
    rw [hΦdef, hΦ'def]
    exact (((hso.Dth).hasDerivAt_slice hθ hz).mul (hasDerivAt_dWsq hz)).mul_const _
  -- unfold identities
  have hsm0u : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.Dth h z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro z hz θ hθ
    rw [show Work.Spaces.mixed 0 1 h z θ = Work.Spaces.Dth h z θ from rfl]
    rw [sm_unfold_gen (Work.Spaces.Dth h z θ) hθ hγne]
  have hsm1u : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed 1 1 h z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * z ^ 2 * ((Work.Spaces.pz (Work.Spaces.Dth h) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro z hz θ hθ
    rw [show Work.Spaces.mixed 1 1 h z θ = z * Work.Spaces.pz (Work.Spaces.Dth h) z θ from rfl]
    rw [sm_unfold_gen (z * Work.Spaces.pz (Work.Spaces.Dth h) z θ) hθ hγne]
    ring
  have hbnd : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ, Φ' z θ ^ 2
      ≤ (2 / z) * sm1 z θ + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ := by
    intro z hz θ hθ
    rw [hΦ'def, hsm0def, hsm1def]
    have hsplit : ((Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
          + Work.Spaces.Dth h z θ * dWsq z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        ≤ 2 * (Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          + 2 * (Work.Spaces.Dth h z θ * dWsq z
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
      nlinarith [sq_nonneg (Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
        - Work.Spaces.Dth h z θ * dWsq z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))]
    refine hsplit.trans ?_
    have hpu := sqmul_unfold (Work.Spaces.pz (Work.Spaces.Dth h) z θ) hz hθ hγne
    have hdu : (Work.Spaces.Dth h z θ * dWsq z
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((z - 3) ^ 2 / (4 * z * (1 + z) ^ 2))
            * ((Work.Spaces.Dth h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      rw [mul_sin_neg_half_sq (x := Work.Spaces.Dth h z θ * dWsq z) hθ hγne,
          show (Work.Spaces.Dth h z θ * dWsq z) ^ 2
            = (Work.Spaces.Dth h z θ) ^ 2 * (dWsq z) ^ 2 from by ring,
          dWsq_sq_id hz]
      ring
    have h2 : 2 * (Work.Spaces.pz (Work.Spaces.Dth h) z θ * (Work.Spaces.w z * Real.sqrt z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (2 / z) * (Work.Spaces.mixed 1 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hpu]
      rw [show Work.Spaces.mixed 1 1 h z θ = z * Work.Spaces.pz (Work.Spaces.Dth h) z θ from rfl]
      rw [sm_unfold_gen (z * Work.Spaces.pz (Work.Spaces.Dth h) z θ) hθ hγne]
      field_simp
      try ring
    have h3 : 2 * (Work.Spaces.Dth h z θ * dWsq z
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))
            * (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hdu]
      rw [show Work.Spaces.mixed 0 1 h z θ = Work.Spaces.Dth h z θ from rfl]
      rw [sm_unfold_gen (Work.Spaces.Dth h z θ) hθ hγne]
      field_simp
      try ring
    rw [h2, h3]
  -- ## the `h`-slot conclusion
  have hG_pt : ∀ z ∈ Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ) + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ) := by
    intro z hz
    have hmaj : IntegrableOn (fun θ => (2 / z) * sm1 z θ
        + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ) Work.Spaces.Iθ :=
      ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _).add
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
    have hle : (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((2 / z) * sm1 z θ
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hmaj
        (ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
          fun θ hθ => hbnd z hz θ hθ)
    rw [MeasureTheory.integral_add ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul] at hle
    have h1 : (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z
        ≤ ((2 / z) * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) * z :=
      mul_le_mul_of_nonneg_right hle hz.le
    have h2 : ((2 / z) * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
            + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) * z
        = 2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
          + (z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))) * (∫ θ in Work.Spaces.Iθ, sm0 z θ) := by
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hz1 : (1 + z) ≠ 0 := by
        have : (0:ℝ) < 1 + z := by linarith [show (0:ℝ) < z from hz]
        exact ne_of_gt this
      field_simp
      try ring
    rw [h2] at h1
    have hzC : z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) ≤ 9 / 2 := by
      have h := abs_div_ge_le hz
      have hz0 : z ≠ 0 := ne_of_gt hz
      have hz1 : (1 + z) ≠ 0 := by
        have : (0:ℝ) < 1 + z := by linarith [show (0:ℝ) < z from hz]
        exact ne_of_gt this
      have hkey : z * ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2))
          = ((z - 3) ^ 2 / (1 + z) ^ 2) / 2 := by
        field_simp
        try ring
      rw [hkey]
      linarith
    have hb0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, sm0 z θ := integral_nonneg fun θ => sq_nonneg _
    have hb1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, sm1 z θ := integral_nonneg fun θ => sq_nonneg _
    nlinarith [h1, hzC, hb0, hb1]
  have hF_eq : ∀ z ∈ Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z
      = ∫ θ in Work.Spaces.Iθ, sm0 z θ := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) = z * (∫ θ in Work.Spaces.Iθ, sm0 z θ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      simp only [hΦdef, hsm0def]
      rw [sqmul_unfold (Work.Spaces.Dth h z θ) hz hθ hγne, hsm0u z hz θ hθ]
      ring
    rw [h1, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  have hFin : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Φ z θ ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have heq : ∀ θ ∈ Work.Spaces.Iθ, Φ z θ ^ 2 = z * sm0 z θ := by
      intro θ hθ
      simp only [hΦdef, hsm0def]
      rw [sqmul_unfold (Work.Spaces.Dth h z θ) hz hθ hγne, hsm0u z hz θ hθ]
      ring
    have hbase : IntegrableOn (fun θ => z * sm0 z θ) Work.Spaces.Iθ :=
      (hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul z
    exact IntegrableOn.congr_fun hbase (fun θ hθ => (heq θ hθ).symm) measurableSet_Icc
  have hGin : ∀ z ∈ Set.Ioi 0, IntegrableOn (fun θ => Φ' z θ ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hmaj : IntegrableOn (fun θ => (2 / z) * sm1 z θ
        + ((z - 3) ^ 2 / (2 * z * (1 + z) ^ 2)) * sm0 z θ) Work.Spaces.Iθ :=
      ((hinner1 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _).add
        ((hinner0 z (Set.mem_Ici.mpr (le_of_lt hz))).const_mul _)
    refine Integrable.mono' hmaj ?_ ?_
    · have h2 := Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ') hΦ'cont hz
      exact h2.pow 2
    · rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      exact Eventually.of_forall fun θ hθ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hbnd z hz θ hθ
  have hFint : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z) (Set.Ioi 0) :=
    IntegrableOn.congr_fun hIS0 (fun z hz => (hF_eq z hz).symm) measurableSet_Ioi
  have hGint : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) (Set.Ioi 0) := by
    have hmaj : IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
        + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) (Set.Ioi 0) :=
      ((hIS1.const_mul 2).add (hIS0.const_mul (9 / 2)))
    have haesm : AEStronglyMeasurable (fun z => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
        (volume.restrict (Set.Ioi 0)) := by
      have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ' p.1 p.2 ^ 2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
        have h3 := (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry Φ') hΦ'cont).pow 2
        have heq : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
          rw [Work.Spaces.Iz]
          exact MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
        rwa [heq]
      have h4 := hjoint.integral_prod_right'
      have heq2 : (fun z => ∫ θ, Φ' z θ ^ 2 ∂(volume.restrict Work.Spaces.Iθ))
          = (fun z => ∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) := by
        funext z; rfl
      rw [heq2] at h4
      exact h4.mul aestronglyMeasurable_id
    refine Integrable.mono' hmaj haesm ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun z hz => by
      rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun θ => sq_nonneg _) hz.le)]
      exact hG_pt z hz
  have hZ := SupOpenH2Z (z₀ := z₀) hz₀ hΦcont hΦ'cont hderiv hFin hGin hFint hGint
  have hLHS : (∫ θ in Work.Spaces.Iθ, Φ z₀ θ ^ 2)
      = (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    simp only [hΦdef]
    rw [sqmul_unfold (Work.Spaces.Dth h z₀ θ) hz₀ hθ hγne]
    try ring
  have hR1 : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
      ≤ Work.Spaces.HkSq α 2 h := by
    rw [show (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
        = ∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun z hz => hF_eq z hz]
    rw [show (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sm0 z θ) from
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))]
    exact hL2Sq0
  have hR2 : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
      ≤ (13 / 2) * Work.Spaces.HkSq α 2 h := by
    have hle : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z)
        ≤ ∫ z in Set.Ioi 0, (2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
            + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)) :=
      MeasureTheory.integral_mono_of_nonneg
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz =>
          mul_nonneg (integral_nonneg fun θ => sq_nonneg _) hz.le)
        (((hIS1.const_mul 2).add (hIS0.const_mul (9 / 2))))
        (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => hG_pt z hz)
    have hsplit : (∫ z in Set.Ioi 0, (2 * (∫ θ in Work.Spaces.Iθ, sm1 z θ)
          + (9 / 2) * (∫ θ in Work.Spaces.Iθ, sm0 z θ)))
        = 2 * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm1 z θ))
          + (9 / 2) * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ)) := by
      rw [MeasureTheory.integral_add (hIS1.const_mul 2) (hIS0.const_mul (9 / 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hsplit] at hle
    have hA : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm1 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sm1 z θ) :=
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
    have hB : (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, sm0 z θ))
        = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, sm0 z θ) :=
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
    rw [hA, hB] at hle
    linarith [hle, hL2Sq0, hL2Sq1]
  have hnn : 0 ≤ Work.Spaces.HkSq α 2 h := Work.Spaces.HkSq_nonneg α 2 h
  calc (Work.Spaces.w z₀) ^ 2 * z₀ * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dth h z₀ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (∫ θ in Work.Spaces.Iθ, Φ z₀ θ ^ 2) := hLHS.symm
    _ ≤ 2 * (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z)
          + (∫ z in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) := hZ
    _ ≤ 2 * Work.Spaces.HkSq α 2 h + (13 / 2) * Work.Spaces.HkSq α 2 h := by
        linarith [hR1, hR2]
    _ ≤ 9 * Work.Spaces.HkSq α 2 h := by linarith

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN0.N0_slice_sq_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

/-- (namespace `Work.FTS.MuLipC.RowN0`) **The squared angular slice of the `N₀`-field is
integrable** for every `r > 0`, for a `SmoothOpen` and `ℋ⁴`-honest datum `g` with `0 < α ≤ 1`.

Proof (the `hsl` block of `Work.FTS.MuLamOK.Rows.Rl0Open`): the pointwise bound
`(N₀ α (F_*+g) g r θ)²·w r ≤ 7(A₀ α |g|_{ℋ⁴}·HkIntegrand α 4 g r θ + B₀ α |g|_{ℋ⁴}/(1+r)²)` for
`r > 0`, `θ ∈ (0,π/2)` (`Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open`, whose `|L₁₂ g| ≤
3|g|_{ℋ⁴}` hypothesis is `Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open`) together with
`w r ≥ 1` dominates the slice by the integrable
`θ ↦ 7(A₀ α |g|_{ℋ⁴}·HkIntegrand α 4 g r θ + B₀ α |g|_{ℋ⁴}/(1+r)²)` (`HkMem α 4 g`), and the
slice is a.e. strongly measurable on `Iθ` because `N₀ α (F_*+g) g` is continuous on the open
quadrant (`Work.FTS.StrongPersist.H6Pair6Aux.contN0_open`,
`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
theorem N0_slice_sq_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2)
      Work.Spaces.Iθ := by
  intro r hr
  have hr0 : (0 : ℝ) < r := hr
  have hzr : r ∈ Work.Spaces.Iz := by
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
  have hW1 : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
    nlinarith
  have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  -- the uniform bound `|L₁₂(g)| ≤ 3|g|_{ℋ⁴}` feeding into the pointwise estimate
  have hsup : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g :=
    Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hso hmem
  -- the pointwise weighted bound for `N₀`
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) :=
    Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open hα hα1 hso hsup
  -- joint continuity of `N₀` on the open quadrant
  have hcont : ContinuousOn
      (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α g) g))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hso hmem
  have hslice : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hr0
  -- the integrable majorant
  have hmaj : MeasureTheory.Integrable
      (fun θ : ℝ => 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
          * Work.Spaces.HkIntegrand α 4 g r θ
        + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
          * (1 / (1 + r)) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (((hmem.1 r hzr).const_mul _).add ?_).const_mul 7
    refine MeasureTheory.integrableOn_const ?_
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono' hmaj (hslice.pow 2) ?_
  rw [hIoo2]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2
      ≤ (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r := by
        nlinarith [hW1,
          sq_nonneg (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ)]
    _ ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) := hpt r hr θ hθ

end Work.FTS_MuLipC.RowN0
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN0.N0_weighted_energy_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

open scoped Real Topology
open MeasureTheory Set Filter

/-- (namespace `Work.FTS_MuLipC.RowN0`) **The Hardy-weighted angular energy of the `N₀`-field is
dominated by an explicit integrable function**: for a.e. `r > 0`,
`(∫_θ (N₀ α (F_*+g) g r θ)²)·((1+r)/r)²
   ≤ 7·(A₀(α,|g|_{ℋ⁴})·Ψ(r) + (π/2)·B₀(α,|g|_{ℋ⁴})·(1/(1+r))²)` where `Ψ(r) = ∫_θ HkIntegrand α 4 g r θ`.

Proof (the `hbd` block of `Work.FTS.MuLamOK.Rows.Rl0Open`): integrate in `θ` the pointwise bound
`(N₀ α (F_*+g) g r θ)²·w r ≤ 7(A₀·HkIntegrand α 4 g r θ + B₀/(1+r)²)` of
`Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open` over `Iθ` (both sides are integrable there: the
first by `HkMem α 4 g`, the constant piece because `Iθ` is compact), using
`MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul` and `∫_θ 1 = π/2` (so the
`π/2` factor multiplies only the constant `B₀`-term); the set `Iθ` and the open interval
`(0,π/2)` differ by the two null endpoints, so the pointwise bound only has to hold a.e. in `θ`.
The hypothesis `|L₁₂ g| ≤ 3|g|_{ℋ⁴}` of `N0_sq_w_open` is
`Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open`. -/
theorem N0_weighted_energy_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2)
          * ((1 + r) / r) ^ 2
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
            + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
              * (1 / (1 + r)) ^ 2) := by
  -- ## the two delivered analytic inputs
  have hsup : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g :=
    Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hso hmem
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) :=
    Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open hα hα1 hso hsup
  -- ## the pointwise bound integrated in `θ`
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0 : ℝ) < r := hr
  have hzr : r ∈ Work.Spaces.Iz := by
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
  have hW1 : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
    nlinarith
  have hweq : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by rw [Work.Spaces.w, div_pow]
  rw [hweq, ← MeasureTheory.integral_mul_const]
  have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2
          * Work.Spaces.w r)
      ≤ ∫ θ in Work.Spaces.Iθ,
        7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
              * Work.Spaces.HkIntegrand α 4 g r θ
            + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
              * (1 / (1 + r)) ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (fun θ =>
        mul_nonneg (sq_nonneg _) (le_trans zero_le_one hW1))
    · refine (((hmem.1 r hzr).const_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g))).add ?_).const_mul 7
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · rw [hIoo2]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => hpt r hr θ hθ)
  refine hstep.trans ?_
  have hintA : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
        * Work.Spaces.HkIntegrand α 4 g r θ) Work.Spaces.Iθ :=
    (hmem.1 r hzr).const_mul (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g))
  have hintB : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
        * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.integrableOn_const ?_
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintA hintB,
    MeasureTheory.integral_const_mul, Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra]
  exact le_of_eq (by ring)

end Work.FTS_MuLipC.RowN0
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN0.integrableOn_L12dens_of_energy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

/-- (namespace `Work.FTS_MuLipC.RowN0`) **The `L₁₂`-density of a datum whose Hardy-weighted
angular energy is dominated by an integrable function is integrable.**  Writing
`Ψ(r) = ∫_θ X(r,θ)²` and `W(r) = ((1+r)/r)²`, the hypothesis is `Ψ(r)·W(r) ≤ Φ(r)` for a.e.
`r > 0` with `Φ ≥ 0` integrable on `(0,∞)`.  Then `L₁₂dens X` is integrable on `(0,∞)`: the
angular Cauchy–Schwarz bound `(L₁₂dens X r)² ≤ 3 Ψ(r)/r²`
(`Work.Coercivity.L12dens_sq_slice` with `Work.Coercivity.integral_Itheta_K`) together with
`Ψ(r)·W(r) ≤ Φ(r)` gives `√Ψ(r) ≤ √(Φ(r))·r/(1+r)`, hence `|L₁₂dens X r| ≤ √(3Φ(r))/(1+r)`;
and `r ↦ √(3Φ(r))` and `r ↦ 1/(1+r)` are both `L²` on `(0,∞)` (the first because its square is
`3Φ`), so their product is `L¹` (`MeasureTheory.MemLp.integrable_mul`), and `haesm` converts the
a.e. domination into integrability (`MeasureTheory.Integrable.mono'`). -/
theorem integrableOn_L12dens_of_energy {X : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ}
    (hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (X r θ) ^ 2) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens X)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦ : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hΦ0 : ∀ r : ℝ, 0 ≤ Φ r)
    (hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (X r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ r) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens X) (Set.Ioi (0 : ℝ)) := by
  -- Gather the two a.e. hypotheses over `(0,∞)` together with the positivity of the point.
  have hae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      r ∈ Set.Ioi (0 : ℝ) ∧ MeasureTheory.IntegrableOn (fun θ : ℝ => (X r θ) ^ 2) Work.Spaces.Iθ
        ∧ (∫ θ in Work.Spaces.Iθ, (X r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ r := by
    filter_upwards [hsl, hbd, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr1 hr2 hr3
    exact ⟨hr3, hr1, hr2⟩
  -- Slicewise: `|L₁₂dens X r| ≤ √(3Φ(r)) · (1/(1+r))`, and AM–GM turns this into the
  -- integrable domination `≤ (3Φ(r) + (1/(1+r))²)/2`.
  have hbdae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.Construction.L12dens X r‖ ≤ (3 * Φ r + (1 / (1 + r)) ^ 2) / 2 := by
    filter_upwards [hae] with r ⟨hr, hslr, hbdr⟩
    have hslice : |Work.Construction.L12dens X r|
        ≤ Real.sqrt (3 * Φ r) * (1 / (1 + r)) :=
      Work.FTS.StrongPersist.H6Pair6Aux.l12sup_dens_le hr hslr hbdr
    rw [Real.norm_eq_abs]
    have hAM : 2 * (Real.sqrt (3 * Φ r) * (1 / (1 + r))) ≤ 3 * Φ r + (1 / (1 + r)) ^ 2 := by
      have hsq : Real.sqrt (3 * Φ r) ^ 2 = 3 * Φ r :=
        Real.sq_sqrt (by linarith [hΦ0 r])
      nlinarith [sq_nonneg (Real.sqrt (3 * Φ r) - 1 / (1 + r)), hsq]
    linarith
  -- The dominating function is integrable on `(0,∞)`.
  have hg : MeasureTheory.Integrable (fun r : ℝ => (3 * Φ r + (1 / (1 + r)) ^ 2) / 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : MeasureTheory.Integrable (fun r : ℝ => 3 * Φ r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hΦ.const_mul 3
    have h2 : MeasureTheory.Integrable (fun r : ℝ => (1 / (1 + r)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := (Work.FTS.H2.InvOneAddSq).1
    exact (h1.add h2).div_const 2
  exact hg.mono' haesm hbdae

end Work.FTS_MuLipC.RowN0
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_starUop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Slots.v2_starUop`

The pointwise regularity of the coefficient `𝒰(Φ̃_*)/sin 2θ` of the self-similar vorticity
equation, in the form consumed by the regularity-export (`RXT`) cone.

The field `UszW` of the star package `Work.FTS.VocabO2.StarPkgo2 α Cs Φs` bounds the
*weighted* coefficient

  `W = ((z+1)/z)·𝒰(Φ̃_*)/sin 2θ`,   `𝒰 = Uop α (PhiTs α Φs)`,

in `𝒲^{4,∞}` (`WlInfMem α 4 W`, `WlInf α 4 W ≤ Cs·α`), whereas the consumer asks for a
pointwise bound on the mixed derivatives `D_z^j D_θ^i (𝒰/sin 2θ)`, `j + i ≤ 2`, **carrying a
`min z 1` factor** — i.e. the vanishing of `𝒰/sin 2θ` and its low-order derivatives at
`z = 0⁺`.

The two are related by the elementary `z`-only factor `A(z) = z/(1+z)`:

  `𝒰/sin 2θ = A(z)·W`      on `z ≠ 0`

(trivially, since `A(z)·((z+1)/z) = 1`), so that every `z`-derivative acquires either the
factor `A`, or one of the Stirling factors `z·A' = z/(1+z)²`, `z·(z·A')' = z(1-z)/(1+z)³`, all
of which are `≤ min z 1` in modulus for `z > 0` (`RXT/StarVopAux.lean`,
`affine_bound`/`quad_bound`/`cubic_bound`):

* `D_θ^i (𝒰/sin 2θ) = A·D_θ^i W`                                       (`DthIter_eq_mul`),
* `D_z D_θ^i (𝒰/sin 2θ) = (z/(1+z)²)·D_θ^i W + A·D_z D_θ^i W`           (`DzIter_one_eq_mul`),
* `D_z² D_θ^i (𝒰/sin 2θ) = (z(1-z)/(1+z)³)·D_θ^i W + 2(z/(1+z)²)·D_z D_θ^i W + A·D_z²D_θ^i W`
                                                                        (`DzIter_two_eq_mul`),

while the `W`-side is bounded uniformly by `mixed_two_le_WlInf` (`RXT/StarVopWlInf.lean`):

  `|D_z^k D_θ^i W| ≤ 4·WlInf α 4 W`   for `k ≤ 2`, `i ≤ 2`.

Each `W`-derivative contributes `4·WlInf α 4 W ≤ 4·Cs·α ≤ 4·max Cs 1·α` and each `A`/`B`/`C`
factor contributes `min z 1`, giving the constant `16`.

This is the `𝒰`-analogue of `Work.FTS_RegExport.RXT.starVop` (which treats `𝒱(Φ̃_*)`), and the
proof follows that file line by line.  The smoothness on the open quadrant used by the product
rules comes from `Work.FTS.PhiStar.CoreAux.fields_smooth`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false

/-- the coefficient `𝒰(Φ̃_*)/sin 2θ` of the self-similar vorticity equation (rows 14, 15) -/
def Uof (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)

/-- the weighted coefficient `((z+1)/z)·𝒰(Φ̃_*)/sin 2θ` whose `𝒲^{4,∞}`-norm is the field
`UszW` of `VocabO2.StarPkgo2` -/
def WU (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => (z + 1) / z * Uof α Φs z θ

theorem v2_starUop {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)) z θ|
        ≤ C * (max Cs 1 * α) * min z 1 := by
  have hsm := Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hS.smooth
  have hWsm : Work.FTS.EllipticEst.SmoothOpen (WU α Φs) := hsm.2.2.2.2.2.1
  have hWmem : Work.Spaces.WlInfMem α 4 (WU α Φs) := hS.UszW.1
  have hWle : Work.Spaces.WlInf α 4 (WU α Φs) ≤ Cs * α := hS.UszW.2
  have hCs : Cs ≤ max Cs 1 := le_max_left _ _
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Uof α Φs z θ = z / (1 + z) * WU α Φs z θ := by
    intro z θ hz hθ0 hθ1
    have h1 : (z : ℝ) ≠ 0 := ne_of_gt hz
    have h2 : (1 + z : ℝ) ≠ 0 := by linarith
    have hcoef : z / (1 + z) * ((z + 1) / z) = 1 := by
      rw [div_mul_div_comm, show (z : ℝ) * (z + 1) = (1 + z) * z from by ring]
      exact div_self (mul_ne_zero h2 h1)
    have hgoal : ∀ a : ℝ, a = z / (1 + z) * ((z + 1) / z * a) := by
      intro a
      rw [← mul_assoc, hcoef, one_mul]
    exact hgoal _
  refine ⟨16, by norm_num, ?_⟩
  intro j i hji z θ hz hθ0 hθ1
  have hj2 : j ≤ 2 := by omega
  have hi2 : i ≤ 2 := by omega
  have hminnn : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hA := Work.FTS_RegExport.RXT.affine_bound hz
  have hB := Work.FTS_RegExport.RXT.quad_bound hz
  have hC := Work.FTS_RegExport.RXT.cubic_bound hz
  have hmax1 : (1 : ℝ) ≤ max Cs 1 := le_max_right _ _
  have hmaxnn : 0 ≤ max Cs 1 * α := mul_nonneg (by linarith) hα.le
  have hWleM : 4 * Work.Spaces.WlInf α 4 (WU α Φs) ≤ 4 * (max Cs 1 * α) := by
    have h2 : 4 * (Cs * α) ≤ 4 * (max Cs 1 * α) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCs hα.le) (by norm_num)
    linarith [hWle, h2]
  have hWle16 : 4 * Work.Spaces.WlInf α 4 (WU α Φs) ≤ 16 * (max Cs 1 * α) := by
    nlinarith [hWleM, hmaxnn]
  have hWle8 : 8 * Work.Spaces.WlInf α 4 (WU α Φs) ≤ 16 * (max Cs 1 * α) := by
    nlinarith [hWleM, hmaxnn]
  have hmix := Work.FTS_RegExport.RXT.mixed_two_le_WlInf hα hα1 hWsm hWmem
  show |Work.Spaces.mixed j i (Uof α Φs) z θ| ≤ 16 * (max Cs 1 * α) * min z 1
  interval_cases j
  · -- j = 0: `D_θ^i (𝒰/sin 2θ) = A·D_θ^i W`
    interval_cases i
    · have h1 := Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm 0 (by norm_num)
        z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 0 (WU α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 0 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 0 (Uof α Φs) z θ
          = Work.Spaces.DthIter 0 (Uof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 0 (WU α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 0 (WU α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm 1 (by norm_num)
        z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 1 (WU α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 1 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 1 (Uof α Φs) z θ
          = Work.Spaces.DthIter 1 (Uof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 1 (WU α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 1 (WU α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm 2 (by norm_num)
        z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 2 (WU α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 2 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 2 (Uof α Φs) z θ
          = Work.Spaces.DthIter 2 (Uof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 2 (WU α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 2 (WU α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 1: `D_z D_θ^i (𝒰/sin 2θ) = B·D_θ^i W + A·D_z D_θ^i W`
    have hi1 : i ≤ 1 := by omega
    have hid' : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        Work.Spaces.DthIter i (Uof α Φs) z' θ'
          = z' / (1 + z') * Work.Spaces.DthIter i (WU α Φs) z' θ' :=
      fun z' θ' hz' hθ' hθ'' =>
        Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm i hi2 z' θ' hz' hθ' hθ''
    have h1 := Work.FTS_RegExport.RXT.DzIter_one_eq_mul hid' (hWsm.DthIter i)
      z θ hz hθ0 hθ1
    have h2 : |Work.Spaces.DthIter i (WU α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 i (by norm_num) hi2
          z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 1 i (by norm_num) hi2
          z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 1 i (Uof α Φs) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Uof α Φs)) z θ from rfl]
    rw [h1]
    calc |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (WU α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ|
        ≤ |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (WU α Φs) z θ|
            + |z / (1 + z)
                * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ| := abs_add_le _ _
      _ = |z / (1 + z) ^ 2| * |Work.Spaces.DthIter i (WU α Φs) z θ|
            + |z / (1 + z)|
              * |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
          add_le_add (mul_le_mul hB h2 (abs_nonneg _) hminnn)
            (mul_le_mul hA h3 (abs_nonneg _) hminnn)
      _ = (8 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
          mul_le_mul_of_nonneg_right hWle8 hminnn
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 2, hence i = 0
    have hi0 : i = 0 := by omega
    subst hi0
    have h1 := Work.FTS_RegExport.RXT.DzIter_two_eq_mul hid hWsm z θ hz hθ0 hθ1
    have h2 : |WU α Φs z θ| ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) :=
      hmix 0 0 (by norm_num) (by norm_num) z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (WU α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 1 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    have h4 : |Work.Spaces.DzIter 2 (WU α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 2 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 2 0 (Uof α Φs) z θ = Work.Spaces.DzIter 2 (Uof α Φs) z θ
        from rfl]
    rw [h1]
    calc |z * (1 - z) / (1 + z) ^ 3 * WU α Φs z θ
            + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (WU α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 2 (WU α Φs) z θ|
        ≤ |z * (1 - z) / (1 + z) ^ 3 * WU α Φs z θ|
            + |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (WU α Φs) z θ|
            + |z / (1 + z) * Work.Spaces.DzIter 2 (WU α Φs) z θ| := by
          refine le_trans (abs_add_le _ _) ?_
          exact add_le_add (abs_add_le _ _) (le_refl _)
      _ = |z * (1 - z) / (1 + z) ^ 3| * |WU α Φs z θ|
            + |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (WU α Φs) z θ|
            + |z / (1 + z)| * |Work.Spaces.DzIter 2 (WU α Φs) z θ| := by
          have habs1 : |z * (1 - z) / (1 + z) ^ 3 * WU α Φs z θ|
              = |z * (1 - z) / (1 + z) ^ 3| * |WU α Φs z θ| := abs_mul _ _
          have habs2 : |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (WU α Φs) z θ|
              = |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (WU α Φs) z θ| :=
            abs_mul _ _
          have habs3 : |z / (1 + z) * Work.Spaces.DzIter 2 (WU α Φs) z θ|
              = |z / (1 + z)| * |Work.Spaces.DzIter 2 (WU α Φs) z θ| := abs_mul _ _
          rw [habs1, habs2, habs3]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs))
            + (2 * min z 1) * (4 * Work.Spaces.WlInf α 4 (WU α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul hC h2 (abs_nonneg _) hminnn
          · refine mul_le_mul ?_ h3 (abs_nonneg _) (by positivity)
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left hB (by norm_num)
          · exact mul_le_mul hA h4 (abs_nonneg _) hminnn
      _ = (16 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 := by
          refine mul_le_mul_of_nonneg_right ?_ hminnn
          linarith [hWleM]
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring

end Work.FTS_RegExport.RXT.Slots
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.starVop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- the coefficient `𝒱(Φ̃_*)` of the self-similar vorticity equation (row 19) -/
def Vof (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)

/-- the weighted coefficient `((z+1)/z)·𝒱(Φ̃_*)` whose `𝒲^{4,∞}`-norm is the field `VzW` of
`VocabO2.StarPkgo2` -/
def Wof (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => (z + 1) / z * Vof α Φs z θ

theorem starVop {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ C * (max Cs 1 * α) * min z 1 := by
  have hsm := Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hS.smooth
  have hWsm : Work.FTS.EllipticEst.SmoothOpen (Wof α Φs) := hsm.2.2.2.1
  have hWmem : Work.Spaces.WlInfMem α 4 (Wof α Φs) := hS.VzW.1
  have hWle : Work.Spaces.WlInf α 4 (Wof α Φs) ≤ Cs * α := hS.VzW.2
  have hW₀nn : 0 ≤ Work.Spaces.WlInf α 4 (Wof α Φs) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 (Wof α Φs) hWmem)
      (Work.Spaces.wlThSum_nonneg α 4 (Wof α Φs) hWmem)
  have hCs : Cs ≤ max Cs 1 := le_max_left _ _
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Vof α Φs z θ = z / (1 + z) * Wof α Φs z θ := by
    intro z θ hz hθ0 hθ1
    show Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        = z / (1 + z) * ((z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    field_simp
    try ring
  refine ⟨16, by norm_num, ?_⟩
  intro j i hji z θ hz hθ0 hθ1
  have hj2 : j ≤ 2 := by omega
  have hi2 : i ≤ 2 := by omega
  have hminnn : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hA := affine_bound hz
  have hB := quad_bound hz
  have hC := cubic_bound hz
  have hWle16 : 4 * Work.Spaces.WlInf α 4 (Wof α Φs) ≤ 16 * (max Cs 1 * α) := by
    nlinarith [hWle, hCs, hα.le]
  have hmix := mixed_two_le_WlInf hα hα1 hWsm hWmem
  show |Work.Spaces.mixed j i (Vof α Φs) z θ| ≤ 16 * (max Cs 1 * α) * min z 1
  interval_cases j
  · -- j = 0: `D_θ^i 𝒱 = A·D_θ^i W`
    interval_cases i
    · have h1 := DthIter_eq_mul hid hWsm 0 (by norm_num) z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 0 (Wof α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 0 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 0 (Vof α Φs) z θ
          = Work.Spaces.DthIter 0 (Vof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 0 (Wof α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 0 (Wof α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := DthIter_eq_mul hid hWsm 1 (by norm_num) z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 1 (Wof α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 1 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 1 (Vof α Φs) z θ
          = Work.Spaces.DthIter 1 (Vof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 1 (Wof α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 1 (Wof α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := DthIter_eq_mul hid hWsm 2 (by norm_num) z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 2 (Wof α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 2 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 2 (Vof α Φs) z θ
          = Work.Spaces.DthIter 2 (Vof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 2 (Wof α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 2 (Wof α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 1: `D_z D_θ^i 𝒱 = B·D_θ^i W + A·D_z D_θ^i W`
    have hi1 : i ≤ 1 := by omega
    have hid' : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        Work.Spaces.DthIter i (Vof α Φs) z' θ'
          = z' / (1 + z') * Work.Spaces.DthIter i (Wof α Φs) z' θ' :=
      fun z' θ' hz' hθ' hθ'' => DthIter_eq_mul hid hWsm i hi2 z' θ' hz' hθ' hθ''
    have h1 := DzIter_one_eq_mul hid' (hWsm.DthIter i) z θ hz hθ0 hθ1
    have h2 : |Work.Spaces.DthIter i (Wof α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 i (by norm_num) hi2 z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 1 i (by norm_num) hi2 z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 1 i (Vof α Φs) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Vof α Φs)) z θ from rfl]
    rw [h1]
    calc |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (Wof α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ|
        ≤ |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (Wof α Φs) z θ|
            + |z / (1 + z)
                * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ| := abs_add_le _ _
      _ = |z / (1 + z) ^ 2| * |Work.Spaces.DthIter i (Wof α Φs) z θ|
            + |z / (1 + z)|
              * |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
          add_le_add (mul_le_mul hB h2 (abs_nonneg _) hminnn)
            (mul_le_mul hA h3 (abs_nonneg _) hminnn)
      _ = (8 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 := by
          refine mul_le_mul_of_nonneg_right ?_ hminnn
          nlinarith [hWle, hCs, hα.le]
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 2, hence i = 0
    have hi0 : i = 0 := by omega
    subst hi0
    have h1 := DzIter_two_eq_mul hid hWsm z θ hz hθ0 hθ1
    have h2 : |Wof α Φs z θ| ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) :=
      hmix 0 0 (by norm_num) (by norm_num) z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (Wof α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 1 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    have h4 : |Work.Spaces.DzIter 2 (Wof α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 2 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 2 0 (Vof α Φs) z θ = Work.Spaces.DzIter 2 (Vof α Φs) z θ
        from rfl]
    rw [h1]
    calc |z * (1 - z) / (1 + z) ^ 3 * Wof α Φs z θ
            + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (Wof α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 2 (Wof α Φs) z θ|
        ≤ |z * (1 - z) / (1 + z) ^ 3 * Wof α Φs z θ|
            + |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (Wof α Φs) z θ|
            + |z / (1 + z) * Work.Spaces.DzIter 2 (Wof α Φs) z θ| := by
          refine le_trans (abs_add_le _ _) ?_
          exact add_le_add (abs_add_le _ _) (le_refl _)
      _ = |z * (1 - z) / (1 + z) ^ 3| * |Wof α Φs z θ|
            + |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (Wof α Φs) z θ|
            + |z / (1 + z)| * |Work.Spaces.DzIter 2 (Wof α Φs) z θ| := by
          have habs1 : |z * (1 - z) / (1 + z) ^ 3 * Wof α Φs z θ|
              = |z * (1 - z) / (1 + z) ^ 3| * |Wof α Φs z θ| := abs_mul _ _
          have habs2 : |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (Wof α Φs) z θ|
              = |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (Wof α Φs) z θ| :=
            abs_mul _ _
          have habs3 : |z / (1 + z) * Work.Spaces.DzIter 2 (Wof α Φs) z θ|
              = |z / (1 + z)| * |Work.Spaces.DzIter 2 (Wof α Φs) z θ| := abs_mul _ _
          rw [habs1, habs2, habs3]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs))
            + (2 * min z 1) * (4 * Work.Spaces.WlInf α 4 (Wof α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul hC h2 (abs_nonneg _) hminnn
          · refine mul_le_mul ?_ h3 (abs_nonneg _) (by positivity)
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left hB (by norm_num)
          · exact mul_le_mul hA h4 (abs_nonneg _) hminnn
      _ = (16 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 := by
          refine mul_le_mul_of_nonneg_right ?_ hminnn
          nlinarith [hWle, hCs, hα.le]
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring

end Work.FTS_RegExport.RXT
end
end
