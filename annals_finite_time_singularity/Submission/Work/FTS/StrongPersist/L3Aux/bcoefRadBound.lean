import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllSol.ShiftFT.uTrAone.derivPhiTrGcLe
import Submission.Work.FTS.EllSol.Trunc.PassAux2
import Submission.Work.FTS.EllipticEst.H2W.slot20A
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.aeSliceAesm
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.n4norm_exists
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.Instantiate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-- **The level-`1` algebraic inputs**: congruence (membership-free), additivity on
`RegQ α 1`, and the two commutator identities of `Lhat`. -/
theorem Comm2_L1 (α : ℝ) (hα : 0 < α) : Comm2 α 1 (Work.Coercivity.H1IP α) where
  congr := fun _f _f' _g h => Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd α h
  add := fun f₁ f₂ g h₁ h₂ hg =>
    (H1IP_core_Q α hα).1 f₁ f₂ g h₁ h₂ hg
  dthC := fun f hf z θ hzθ =>
    Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat hf hzθ.1 hzθ.2.1 hzθ.2.2
  dzC := fun f hf z θ hzθ =>
    Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat hf hzθ.1 hzθ.2.1 hzθ.2.2




end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.wip_T4_ge_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The interior integrability of the two `D_θ`-blocks used below -/



/-! ## The scalar arithmetic closing the constant `1/200` -/

/-- If `J² ≤ 120/(17α)` with `0 < α ≤ 10⁻⁹`, then `40αJ ≤ 1/200`.  This is the numerical
step converting the angular bound `T4J α ≤ 120/(17α)` into the constant of the target.  (The
numeric content: `40α√(120/(17α)) ≤ 1/200` is equivalent to `7.68·10⁹·α ≤ 17`, and
`7.68·10⁹·10⁻⁹ = 7.68 < 17`.) -/
theorem T4Q_arith (α J : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 9) (hJ : 0 ≤ J)
    (hJle : J ^ 2 ≤ 120 / (17 * α)) : 40 * α * J ≤ 1 / 200 := by
  have h17 : (0 : ℝ) < 17 * α := by linarith
  have hJ' : J ≤ Real.sqrt (120 / (17 * α)) := by
    calc J = Real.sqrt (J ^ 2) := (Real.sqrt_sq hJ).symm
      _ ≤ Real.sqrt (120 / (17 * α)) := Real.sqrt_le_sqrt hJle
  have h1 : Real.sqrt (120 / (17 * α)) ≤ 1 / (8000 * α) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e : (1 / (8000 * α)) ^ 2 = 1 / (64000000 * α ^ 2) := by
      rw [div_pow, one_pow]
      rw [show (8000 * α) ^ 2 = 64000000 * α ^ 2 by ring]
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hα1, hα]
  have h2 : 40 * α * Real.sqrt (120 / (17 * α)) ≤ 1 / 200 := by
    calc 40 * α * Real.sqrt (120 / (17 * α))
        ≤ 40 * α * (1 / (8000 * α)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 200 := by field_simp; ring
  have h3 : 40 * α * J ≤ 40 * α * Real.sqrt (120 / (17 * α)) :=
    mul_le_mul_of_nonneg_left hJ' (by positivity)
  linarith

/-! ## A.e. strong measurability of the `L²` factors in the interior class -/



/-! ## Integrability and the value of the `L²` norm of `T4B` -/




/-! ## The target -/


end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm =====
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

/-- The open quadrant, on which every function of the transfer is differentiable. -/
abbrev Qd : Set (ℝ × ℝ) := Work.Construction.Qd

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-- **The finite-order smooth class on the open quadrant.**  `Q0Sm k X` says that the
uncurried profile `X` is `C^k` on `Qd`.  It is the transfer's replacement for
`Work.FTS.LocData.SmoothQuad`, which is not available for `E1`, `E2`. -/
def Q0Sm (k : ℕ) (X : Fn) : Prop :=
  ContDiffOn ℝ (((k : ℕ)) : WithTop ℕ∞) (Function.uncurry X) Qd

theorem q0Sm_iff (k : ℕ) (X : Fn) :
    Q0Sm k X ↔ ContDiffOn ℝ (((k : ℕ)) : WithTop ℕ∞) (Function.uncurry X) Qd := Iff.rfl

/-! ## The order calculus -/

theorem Q0Sm.mono {k l : ℕ} {X : Fn} (h : Q0Sm k X) (hl : l ≤ k) : Q0Sm l X :=
  h.of_le (m := (((l : ℕ)) : WithTop ℕ∞)) (by exact_mod_cast hl)

theorem Q0Sm.dth {k : ℕ} {X : Fn} (h : Q0Sm (k + 1) X) : Q0Sm k (Work.Spaces.Dth X) :=
  contDiffOn_Dth_nat isOpen_Qd h

theorem Q0Sm.dz {k : ℕ} {X : Fn} (h : Q0Sm (k + 1) X) : Q0Sm k (Work.Spaces.Dz X) :=
  contDiffOn_Dz_nat isOpen_Qd h

/-! ## Continuity of the blocks -/

/-- Every block `D_z^bD_θ^a X` of total order `a + b ≤ k` is continuous on the open
quadrant. -/
theorem Q0Sm.mixed_continuousOn {k : ℕ} {X : Fn} (h : Q0Sm k X) {a b : ℕ} (hab : a + b ≤ k) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed b a X)) Qd :=
  contDiffOn_mixed_nat isOpen_Qd (m := k) h (a := a) (b := b) hab

/-- The block-continuity package of `Assembly.Comm2w`, from `Q0Sm`. -/
theorem Q0Sm.blocksCont {k : ℕ} {X : Fn} (h : Q0Sm k X) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont k X :=
  fun a b hab => h.mixed_continuousOn (a := a) (b := b) hab

/-- Continuity of the `ℋ^k`-integrand of `X` on the open quadrant. -/
theorem Q0Sm.continuousOn_HkIntegrand {k : ℕ} {X : Fn} (h : Q0Sm k X) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k X p.1 p.2) Qd :=
  Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont
    h.blocksCont α

/-! ## Additivity of the two derivatives on the open quadrant -/

/-- The `z`-slice of a `C^1` profile on the open quadrant is differentiable. -/
theorem Q0Sm.differentiableAt_slice_z {X : Fn} (h : Q0Sm 1 X) {z θ : ℝ} (hzθ : (z, θ) ∈ Qd) :
    DifferentiableAt ℝ (fun z' : ℝ => X z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hzθ)
  have hproj : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z :=
    (differentiableAt_id.prodMk (differentiableAt_const θ))
  simpa only [Function.uncurry, Function.comp_def] using hd.comp z hproj

/-- The `θ`-slice of a `C^1` profile on the open quadrant is differentiable. -/
theorem Q0Sm.differentiableAt_slice_θ {X : Fn} (h : Q0Sm 1 X) {z θ : ℝ} (hzθ : (z, θ) ∈ Qd) :
    DifferentiableAt ℝ (fun θ' : ℝ => X z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (h.differentiableOn (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hzθ)
  have hproj : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ :=
    (differentiableAt_const z).prodMk differentiableAt_id
  simpa only [Function.uncurry, Function.comp_def] using hd.comp θ hproj

/-- **`D_θ` is additive on the open quadrant** for `C^1` summands. -/
theorem Q0Sm.dth_add {f₁ f₂ : Fn} (h₁ : Q0Sm 1 f₁) (h₂ : Q0Sm 1 f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.Dth (f₁ + f₂) z θ = Work.Spaces.Dth f₁ z θ + Work.Spaces.Dth f₂ z θ := by
  intro z θ hzθ
  have d1 := h₁.differentiableAt_slice_θ hzθ
  have d2 := h₂.differentiableAt_slice_θ hzθ
  have hderiv : deriv (fun θ' : ℝ => f₁ z θ' + f₂ z θ') θ
      = deriv (fun θ' : ℝ => f₁ z θ') θ + deriv (fun θ' : ℝ => f₂ z θ') θ :=
    deriv_add d1 d2
  simp only [Work.Spaces.Dth, Work.Spaces.pth, Pi.add_apply]
  rw [hderiv]
  ring

/-- **`D_z` is additive on the open quadrant** for `C^1` summands. -/
theorem Q0Sm.dz_add {f₁ f₂ : Fn} (h₁ : Q0Sm 1 f₁) (h₂ : Q0Sm 1 f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Work.Spaces.Dz (f₁ + f₂) z θ = Work.Spaces.Dz f₁ z θ + Work.Spaces.Dz f₂ z θ := by
  intro z θ hzθ
  have d1 := h₁.differentiableAt_slice_z hzθ
  have d2 := h₂.differentiableAt_slice_z hzθ
  have hderiv : deriv (fun z' : ℝ => f₁ z' θ + f₂ z' θ) z
      = deriv (fun z' : ℝ => f₁ z' θ) z + deriv (fun z' : ℝ => f₂ z' θ) z :=
    deriv_add d1 d2
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Pi.add_apply]
  rw [hderiv]
  ring



end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixed_conv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

local notation "Iθ" => Work.Spaces.Iθ

/-- **Fubini for the angular kernel `KJ` and a compactly supported radial kernel.**

For a radial kernel `k` and a function `v` whose product against `k (σ - ·)` is jointly
integrable for the product measure `volume × (volume ↾ Iθ)`, the two iterated integrals of
`k (σ - t) · KJ ε θ s · v t s` agree.  This is the `KJ`-analogue of `swapFubini` (which is
stated for the folded kernel `Kern (sKer ε)`); both are the same computation, namely that each
side is the product integral of the single joint integrand
(`MeasureTheory.integral_prod` / `MeasureTheory.integral_prod_symm`), after moving the constants
`k (σ - t)` resp. `KJ ε θ s` in and out of the inner integral
(`MeasureTheory.integral_const_mul`). -/
theorem swapFubini_KJ {k : ℝ → ℝ} {v : ℝ → ℝ → ℝ} {ε θ σ : ℝ}
    (h : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => k (σ - p.1) * (Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * v p.1 p.2))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ))) :
    (∫ t : ℝ, k (σ - t) * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * v t s))
      = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * (∫ t : ℝ, k (σ - t) * v t s) := by
  set F : ℝ × ℝ → ℝ := fun p => k (σ - p.1) * (Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * v p.1 p.2)
    with hFdef
  have hlhs : (∫ t : ℝ, k (σ - t) * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ)) := by
    rw [MeasureTheory.integral_prod F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (k (σ - t))
      (fun s => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * v t s)]
  have hrhs : (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * (∫ t : ℝ, k (σ - t) * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ)) := by
    rw [MeasureTheory.integral_prod_symm F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (Work.FTS.EllSol.EllPkgAux.KJ ε θ s)
      (fun t => k (σ - t) * v t s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [F]
    ring
  exact hlhs.trans hrhs.symm

theorem zmoll_mixed_conv (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ
        = ∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
            * Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z := by
  intro z hz θ hθ
  -- the mixed derivative, with the two differentiations detached
  rw [Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixed_id G hT hF δ ε hP z hz θ hθ]
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  -- unfold the Schur operator on the right-hand side
  rw [show (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
        * Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z)
      = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
          * (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
              * Work.Spaces.pth G (Real.exp t) s) from rfl]
  -- the angular derivative of the angular mollification, as the `KJ`-fold
  have hstep1 : (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
        * Work.Spaces.pth (fun z' θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z' θ')
            (Real.exp t) θ)
      = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
          * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s
              * Work.Spaces.pth G (Real.exp t) s) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [Work.FTS.EllSol.EllPkgAux.MollDom.thMoll_pth_fold G hT ε hε0 hε1
      (Real.exp t) (Real.exp_pos t) θ hθ]
    simp only [Work.FTS.EllSol.EllPkgAux.KJ]
  -- exchange the two integrations
  have hstep2 := swapFubini_KJ (k := Work.FTS.EllSol.EllPkgAux.sKerd δ)
    (v := fun t s => Work.Spaces.pth G (Real.exp t) s) (ε := ε) (θ := θ) (σ := Real.log z)
    (Work.FTS.EllSol.EllPkgAux.MollDom.ZmollMix.integrable_sKerd_KJ_pth G hT hF δ ε
      hδ0 hδ1 hε0 hε1 hz hθ)
  exact hstep1.trans hstep2

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.Flat2DAgmonNiceBPrelim3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open Work.Spaces

local notation "thEta" => Work.FTS.EllipticEst.thEta
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1000000


end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTr_Aone =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The shifted `A₁` slot of the truncation `uTr`

`Work.FTS.EllSol.ShiftFT.uTr N b u = phiTr N · Gc N b u` is the truncated data used in
`Work.FTS.EllSol.ShiftFT.shiftedFlat_of_nice`: `Gc N b u` is the (backward) primitive of
`chi N · L_b u` (`L_b = ∂_t - b`) and `phiTr N = chi (4096·N)` cuts off the exponentially
decaying tail `e^{bt}·A(θ)` of `Gc`, which is a `b`-harmonic mode and hence invisible to `L_b`.

This file proves the `A₁`-slot bound: the `L_b`-energy of `uTr N b u` is controlled by the
`L_b`-energy of `u` itself, uniformly in `N ≥ 2`,

`∫∫ (L_b (uTr N b u))² σ_η ≤ K · ∫∫ (L_b u)² σ_η`.

The proof is `(a+b)² ≤ 2a² + 2b²` applied to the product rule
`L_b (phiTr N · Gc) = (phiTr N)' · Gc + phiTr N · L_b (Gc)` together with
`L_b (Gc) = chi N · L_b u` (`Work.FTS.EllSol.ShiftFT.Gc_sh`).  The first slot is bounded by
`∫∫(L_b u)²σ_η` (`phiTr`, `chi ∈ [0,1]`), the second – the truncation error – is the content of
`derivPhiTrGcLe`, which uses the support of `(phiTr N)'` and the fact that off the truncation
window `Gc` is controlled by `L_b u` (`GcAbsLe`).
-/

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-! ## §1  Elementary facts about the cutoffs -/





/-- The integration domain `ℝ × Iθ` differs from the open strip by a null set. -/
theorem uTrAone_SI_ae_eq_strip :
    (Set.univ ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume] ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm

/-! ## §2  The `t`-derivative of the primitive `Gc` -/

/-- `t ↦ Gc N b u t θ` has `t`-derivative `b·Gc + chi N t·(L_b u)` on the open strip.

This is the `HasDerivAt` form of `Work.FTS.EllSol.ShiftFT.Gc_sh`
(`L_b (Gc N b u) = chi N · L_b u`), obtained by the product rule applied to
`Gc = chi N · u + e^{bt}·∫_t^{2N} e^{-bs}(chi N)' u` together with the fundamental theorem of
calculus for the variable lower limit. -/
theorem uTrAone_Gc_hasDerivAt (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun t' => Gc N b u t' θ)
        (b * Gc N b u t θ
          + Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ)) t := by
  intro t θ hθ
  have hchi2 : ContDiff ℝ 2 (Trunc.chi N) := Trunc.chi_contDiff 2 N
  have hchiD : DifferentiableAt ℝ (Trunc.chi N) t := hchi2.differentiable (by norm_num) t
  have hchic : Continuous (deriv (Trunc.chi N)) := hchi2.continuous_deriv (by norm_num)
  have hmap : Set.MapsTo (fun s : ℝ => (s, θ)) Set.univ
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
  have hpair : ContDiffOn ℝ 2 (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  have hslice : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) Set.univ := by
    have h := hu.comp hpair hmap
    simpa [Function.comp_def, Function.uncurry] using h
  have hsliceDiff : DifferentiableAt ℝ (fun s : ℝ => u s θ) t :=
    (hslice.differentiableOn (by norm_num)).differentiableAt (by simp)
  have hsliceC : Continuous (fun s : ℝ => u s θ) := continuousOn_univ.mp hslice.continuousOn
  have hslice_deriv : HasDerivAt (fun s : ℝ => u s θ) (deriv (fun s : ℝ => u s θ) t) t :=
    hsliceDiff.hasDerivAt
  have hFd : HasDerivAt (fun s : ℝ => Trunc.chi N s * u s θ)
      (deriv (Trunc.chi N) t * u t θ
        + Trunc.chi N t * deriv (fun s : ℝ => u s θ) t) t :=
    hchiD.hasDerivAt.mul hslice_deriv
  have hexpD : HasDerivAt (fun s : ℝ => Real.exp (b * s)) (b * Real.exp (b * t)) t := by
    have h : HasDerivAt (fun s : ℝ => b * s) b t := by
      have h' := (hasDerivAt_id t).const_mul b
      simpa using h'
    simpa [mul_comm] using h.exp
  have hint_cont : Continuous (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ) := by
    have h1 : Continuous (fun s : ℝ => Real.exp (-(b * s))) := by fun_prop
    exact (h1.mul hchic).mul hsliceC
  have hH : HasDerivAt (fun v : ℝ => ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
      (-(Real.exp (-(b * t)) * deriv (Trunc.chi N) t * u t θ)) t :=
    intervalIntegral.integral_hasDerivAt_left (hint_cont.intervalIntegrable t (2 * N))
      (hint_cont.stronglyMeasurableAtFilter volume (𝓝 t)) hint_cont.continuousAt
  have hEHd : HasDerivAt (fun v : ℝ => Real.exp (b * v) * ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
      (b * Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
        + Real.exp (b * t) * (-(Real.exp (-(b * t))
            * deriv (Trunc.chi N) t * u t θ))) t :=
    hexpD.mul hH
  have hsumd : HasDerivAt (fun v : ℝ => Trunc.chi N v * u v θ
        + Real.exp (b * v) * ∫ s in v..(2 * N),
          Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
      ((deriv (Trunc.chi N) t * u t θ
          + Trunc.chi N t * deriv (fun s : ℝ => u s θ) t)
        + (b * Real.exp (b * t) * (∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
          + Real.exp (b * t) * (-(Real.exp (-(b * t))
              * deriv (Trunc.chi N) t * u t θ)))) t :=
    hFd.add hEHd
  have hexpneg : Real.exp (b * t) * Real.exp (-(b * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  refine hsumd.congr_deriv ?_
  have hGct : Gc N b u t θ = Trunc.chi N t * u t θ
      + Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ := rfl
  have hpzt : Work.Spaces.pz u t θ = deriv (fun s : ℝ => u s θ) t := rfl
  rw [hGct, hpzt]
  linear_combination (-(deriv (Trunc.chi N) t * u t θ)) * hexpneg

/-! ## §3  The product rule for `uTr` -/

/-- The shifted operator applied to the truncation: for `θ ∈ (0,π/2)`,
`L_b (uTr N b u) = (phiTr N)' · Gc + phiTr N · chi N · L_b u`. -/
theorem uTrAone_uTr_sh (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (uTr N b u) t θ - b * uTr N b u t θ
        = deriv (phiTr N) t * Gc N b u t θ
          + phiTr N t * (Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ)) := by
  intro t θ hθ
  have hphi : HasDerivAt (fun v : ℝ => phiTr N v) (deriv (phiTr N) t) t :=
    ((phiTr_contDiff 1 N).differentiable (by norm_num) t).hasDerivAt
  have hGc := uTrAone_Gc_hasDerivAt N b u hu t θ hθ
  have hmul := hphi.mul hGc
  have hmain : deriv (fun v : ℝ => phiTr N v * Gc N b u v θ) t
      = deriv (phiTr N) t * Gc N b u t θ
        + phiTr N t * (b * Gc N b u t θ
            + Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ)) := hmul.deriv
  have hkey : Work.Spaces.pz (uTr N b u) t θ - b * uTr N b u t θ
      = deriv (fun v : ℝ => phiTr N v * Gc N b u v θ) t
        - b * (phiTr N t * Gc N b u t θ) := by
    show deriv (fun v : ℝ => uTr N b u v θ) t - b * uTr N b u t θ = _
    rfl
  rw [hkey, hmain]
  ring

/-! ## §4  The `phiTr · chi N · L_b u` slot -/

/-- The `chi N · L_b u` slot of `L_b (uTr N b u)`: its weighted energy is at most that of
`L_b u` itself, because `0 ≤ phiTr N ≤ 1` and `0 ≤ chi N ≤ 1`. -/
theorem uTrAone_B_slot (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hI : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ =>
        (phiTr N p.1 * (Trunc.chi N p.1
          * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) ∧
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (phiTr N p.1 * (Trunc.chi N p.1
          * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      ≤ (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2) := by
  have hSI : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hwEnn : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      0 ≤ FlatFT.wE p.2 := by
    filter_upwards [ae_restrict_mem (μ := volume) hSI] with p hp
    exact FlatFT.wE_nonneg hp.2
  have hv_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (Trunc.aesm_strip (Trunc.continuousOn_uncurry_pz hu)).sub
      ((Trunc.aesm_strip hu.continuousOn).const_mul b)
  have hB_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have hphi : AEStronglyMeasurable (fun p : ℝ × ℝ => phiTr N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((phiTr_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hchi : AEStronglyMeasurable (fun p : ℝ × ℝ => Trunc.chi N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((Trunc.chi_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hwE : AEStronglyMeasurable (fun p : ℝ × ℝ => FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip Trunc.continuousOn_wE_comp
    exact ((hphi.mul (hchi.mul hv_aesm)).pow 2).mul hwE
  have hBnn : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      0 ≤ (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2 := by
    filter_upwards [hwEnn] with p hp
    exact mul_nonneg (sq_nonneg _) hp
  have hle : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2
      ≤ (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2 := by
    filter_upwards [hwEnn] with p hp
    set w : ℝ := Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2 with hw
    have h1 : (0 : ℝ) ≤ phiTr N p.1 := phiTr_nonneg N p.1
    have h2 : phiTr N p.1 ≤ 1 := phiTr_le_one N p.1
    have h3 : (0 : ℝ) ≤ Trunc.chi N p.1 := Trunc.chi_nonneg N p.1
    have h4 : Trunc.chi N p.1 ≤ 1 := Trunc.chi_le_one N p.1
    have h5 : (0 : ℝ) ≤ phiTr N p.1 * Trunc.chi N p.1 := mul_nonneg h1 h3
    have h6 : phiTr N p.1 * Trunc.chi N p.1 ≤ 1 := by nlinarith
    have h7 : (phiTr N p.1 * Trunc.chi N p.1) ^ 2 ≤ 1 := by nlinarith
    calc (phiTr N p.1 * (Trunc.chi N p.1 * w)) ^ 2 * FlatFT.wE p.2
        = (phiTr N p.1 * Trunc.chi N p.1) ^ 2 * (w ^ 2 * FlatFT.wE p.2) := by ring
      _ ≤ 1 * (w ^ 2 * FlatFT.wE p.2) :=
          mul_le_mul_of_nonneg_right h7 (mul_nonneg (sq_nonneg _) hp)
      _ = w ^ 2 * FlatFT.wE p.2 := by ring
  have hBint : IntegrableOn (fun p : ℝ × ℝ =>
      (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    refine Integrable.mono' hI hB_aesm ?_
    filter_upwards [hBnn, hle] with p hnn hleq
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hleq
  refine ⟨hBint, ?_⟩
  refine integral_mono_ae hBint hI ?_
  filter_upwards [hle] with p hple
  exact hple

/-! ## §5  The `A₁` slot: assembly -/

theorem uTr_Aone (b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hI : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N ≥ (2 : ℝ),
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
          - b * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
            - b * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ K * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) := by
  obtain ⟨Ktk, hKtk0, hKtkbd⟩ := Trunc.exists_bound_deriv_tk
  refine ⟨2 + 2 * Ktk ^ 2, by nlinarith [sq_nonneg Ktk], fun N hN => ?_⟩
  have hNpos : 0 < N := by linarith
  have hSI : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hwEnn : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      0 ≤ FlatFT.wE p.2 := by
    filter_upwards [ae_restrict_mem (μ := volume) hSI] with p hp
    exact FlatFT.wE_nonneg hp.2
  -- ### the a.e. product rule on the integration domain
  have hrule : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2
        = deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2)) := by
    rw [Measure.restrict_congr_set uTrAone_SI_ae_eq_strip]
    filter_upwards [ae_restrict_mem Trunc.isOpen_strip.measurableSet] with p hp
    exact uTrAone_uTr_sh N b u hu p.1 p.2 hp.2
  -- ### the two slots
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Gc N b u p.1 p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllSol.ShiftFT.uTrAone.GcAesm N b u hu
  obtain ⟨hAint, hAle⟩ :=
    Work.FTS.EllSol.ShiftFT.uTrAone.derivPhiTrGcLe N b Ktk u hN hKtkbd hu hI hmeas
      (Work.FTS.EllSol.ShiftFT.uTrAone.GcAbsLe N b u hNpos hb hu)
  obtain ⟨hBint, hBle⟩ := uTrAone_B_slot N b u hu hI
  have hF0eq : (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2) ^ 2
          * FlatFT.wE p.2)
      =ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ =>
        (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    filter_upwards [hrule] with p hp
    rw [hp]
  -- ### pointwise `(a+b)² ≤ 2a² + 2b²`
  have hF1le : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2
      ≤ 2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    filter_upwards [hwEnn] with p hp
    set X : ℝ := deriv (phiTr N) p.1 * Gc N b u p.1 p.2 with hX
    set Y : ℝ := phiTr N p.1 * (Trunc.chi N p.1
      * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2)) with hY
    have hsq : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by nlinarith [sq_nonneg (X - Y)]
    calc (X + Y) ^ 2 * FlatFT.wE p.2
        ≤ (2 * X ^ 2 + 2 * Y ^ 2) * FlatFT.wE p.2 :=
          mul_le_mul_of_nonneg_right hsq hp
      _ = 2 * (X ^ 2 * FlatFT.wE p.2) + 2 * (Y ^ 2 * FlatFT.wE p.2) := by ring
  have h2A2Bint : IntegrableOn (fun p : ℝ × ℝ =>
      2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2))
      (Set.univ ×ˢ Work.Spaces.Iθ) :=
    (hAint.const_mul 2).add (hBint.const_mul 2)
  have hF1_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have hdphi : AEStronglyMeasurable (fun p : ℝ × ℝ => deriv (phiTr N) p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      (((phiTr_contDiff 1 N).continuous_deriv le_rfl).comp continuous_fst).aestronglyMeasurable
    have hphi : AEStronglyMeasurable (fun p : ℝ × ℝ => phiTr N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((phiTr_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hchi : AEStronglyMeasurable (fun p : ℝ × ℝ => Trunc.chi N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((Trunc.chi_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hpz : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip (Trunc.continuousOn_uncurry_pz hu)
    have hu' : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip hu.continuousOn
    have hwE : AEStronglyMeasurable (fun p : ℝ × ℝ => FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip Trunc.continuousOn_wE_comp
    exact (((hdphi.mul hmeas).add
      (hphi.mul (hchi.mul (hpz.sub (hu'.const_mul b))))).pow 2).mul hwE
  have hF1norm : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      ‖(deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2‖
      ≤ 2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    filter_upwards [hF1le, hwEnn] with p hpl hpm
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpm)]
    exact hpl
  have hF1int : IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) :=
    Integrable.mono' h2A2Bint hF1_aesm hF1norm
  have hF0int : IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2) ^ 2
        * FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
    Integrable.congr hF1int hF0eq.symm
  refine ⟨hF0int, ?_⟩
  have hmain : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2) ^ 2
          * FlatFT.wE p.2)
      = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2 :=
    integral_congr_ae hF0eq
  have hmono : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
          + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)) :=
    integral_mono_ae hF1int h2A2Bint hF1le
  have hsplit : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
          + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)))
      = 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    rw [MeasureTheory.integral_add (hAint.const_mul 2) (hBint.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have harith : 2 * (Ktk ^ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2))
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2)
      = (2 + 2 * Ktk ^ 2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2) := by ring
  linarith [hmain.le, hmono, hsplit.le, hAle, hBle, harith]

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.SpecAux.ShiftSlot11Idents =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.SpecAux

open MeasureTheory Set Filter
open scoped Real Topology ContDiff ENNReal
open Work.Spaces
open Work.FTS.EllSol.FlatFT

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The shifted frequency weight `μ(ξ) = (2πξ)² + b² = ‖2πiξ - b‖²`. -/
abbrev muW (b ξ : ℝ) : ℝ := (2 * Real.pi * ξ) ^ 2 + b ^ 2

theorem muW_nonneg (b ξ : ℝ) : 0 ≤ muW b ξ := by
  unfold muW
  positivity

theorem measurable_muW (b : ℝ) : Measurable (muW b) := by
  unfold muW
  fun_prop

/-! ## The fixed-`ξ` slice integrabilities -/

/-- The slice integrabilities of the five slots appearing in the shifted estimate, for
`NiceFlat` data whose `θ`-slot is integrable against `wE`. -/
theorem slotSliceFacts {u : ℝ → ℝ → ℝ} (α : ℝ) (hα1 : α ≤ 1) (hg : NiceFlat u)
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (pth (pth u) p.1 p.2) ^ 2 * wE p.2) (Set.univ ×ˢ Iθ)) :
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ) ∧
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wE θ) Iθ) ∧
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wA α θ)
      Iθ) ∧
    (∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) Iθ) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pth : ContDiffOn ℝ 1 (Function.uncurry (pth u)) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_u
  have hcd_pthpth : ContDiffOn ℝ 0 (Function.uncurry (pth (pth u))) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_pth
  have hsupp_pth : ∀ t θ : ℝ, M < |t| → pth u t θ = 0 := supp_pth hM
  have hsupp_pthpth : ∀ t θ : ℝ, M < |t| → pth (pth u) t θ = 0 := supp_pthpth hM
  have hwEnn : ∀ θ ∈ Iθ, 0 ≤ wE θ := fun θ hθ => wE_nonneg hθ
  have hwAnn : ∀ θ ∈ Iθ, 0 ≤ wA α θ := fun θ hθ => wA_nonneg hθ
  have hwAle : ∀ θ ∈ Iθ, wA α θ ≤ wE θ := fun θ hθ => wA_le_wE hα1 hθ
  have hslice_u : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice u ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => (sliceContDiffOn (n := 2) (by norm_num) hcd_u ⟨M, hM0, hM⟩ ξ).continuousOn
  have hslice_pth : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice (pth u) ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => (sliceContDiffOn (n := 1) (by norm_num) hcd_pth
      ⟨M, hM0, hsupp_pth⟩ ξ).continuousOn
  have hslice_q : ∀ ξ : ℝ,
      ContinuousOn (fun θ : ℝ => slice (pth (pth u)) ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun ξ => (sliceContDiffOn (n := 0) (by norm_num) hcd_pthpth
      ⟨M, hM0, hsupp_pthpth⟩ ξ).continuousOn
  have hdth := dthBound u hg hQ
  have hA1 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (pth u p.1 p.2) ^ 2 * wE p.2) (Set.univ ×ˢ Iθ) := hdth.1
  have hA0 : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2 * wE p.2) (Set.univ ×ˢ Iθ) := hdth.2
  have he0 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (u t θ) ^ 2) * wE θ) Iθ :=
    integrableOn_energy_mul measurable_wE hA0
  have he1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (pth u t θ) ^ 2) * wE θ) Iθ :=
    integrableOn_energy_mul measurable_wE hA1
  have heq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (∫ t : ℝ, (pth (pth u) t θ) ^ 2) * wE θ) Iθ :=
    integrableOn_energy_mul measurable_wE hQ
  have hJg : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_u.continuousOn hM hwEnn measurable_wE
      (hslice_u ξ) he0
  have hJpth : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_pth.continuousOn hsupp_pth hwEnn measurable_wE
      (hslice_pth ξ) he1
  have hJq : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul hM0 hcd_pthpth.continuousOn hsupp_pthpth hwEnn
      measurable_wE (hslice_q ξ) heq
  have hJpthA : ∀ ξ : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wA α θ) Iθ :=
    fun ξ => integrableOn_slice_sq_mul_le hwAnn hwEnn hwAle (hslice_pth ξ) (measurable_wA α)
      (hJpth ξ)
  exact ⟨hJg, hJpth, hJpthA, hJq⟩

/-! ## The four Plancherel identifications -/

/-- Identification of the shifted first heavy slot. -/
theorem hidShiftOne {u : ℝ → ℝ → ℝ} {b : ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ)
    (hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => muW b ξ * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, muW b ξ * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pz u t θ - b * u t θ) ^ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (muW b ξ
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hsupp_sp : ∀ t θ : ℝ, M < |t| → pz u t θ - b * u t θ = 0 :=
    fun t θ ht => by rw [supp_pz hM t θ ht, hM t θ ht]; ring
  have hcont_sp : ContinuousOn
      (Function.uncurry (fun t θ : ℝ => pz u t θ - b * u t θ)) flStrip :=
    ((pz_contDiffOn_succ flStrip_isOpen hcd_u).continuousOn).sub
      (hcd_u.continuousOn.const_mul b)
  have hsl_u : ContinuousOn (fun p : ℝ × ℝ => slice u p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_u.continuousOn ⟨M, hM0, hM⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (pz u t θ - b * u t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_sp hsupp_sp hθ)
  exact lintegral_slice_plancherel u (fun t θ : ℝ => pz u t θ - b * u t θ) (muW b) wE
    (muW_nonneg b) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_u (measurable_muW b) measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_sp measurable_wE)

/-- Identification of the shifted second heavy slot. -/
theorem hidShiftTwo {u : ℝ → ℝ → ℝ} {b : ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice u ξ θ‖ ^ 2 * wE θ) Iθ)
    (hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => (muW b ξ) ^ 2 * ‖slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (muW b ξ) ^ 2 * ‖slice u ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ) ^ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((muW b ξ) ^ 2
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2
            * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pz : ContDiffOn ℝ 1 (Function.uncurry (pz u)) flStrip :=
    pz_contDiffOn_succ flStrip_isOpen hcd_u
  have hsupp_spp : ∀ t θ : ℝ, M < |t| →
      pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ = 0 := by
    intro t θ ht
    rw [supp_pzpz hM t θ ht, supp_pz hM t θ ht, hM t θ ht]
    ring
  have hcont_spp : ContinuousOn
      (Function.uncurry (fun t θ : ℝ =>
        pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ)) flStrip :=
    (((pz_contDiffOn_succ flStrip_isOpen hcd_pz).continuousOn).sub
      (hcd_pz.continuousOn.const_mul (2 * b))).add
      (hcd_u.continuousOn.const_mul (b ^ 2))
  have hsl_u : ContinuousOn (fun p : ℝ × ℝ => slice u p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_u.continuousOn ⟨M, hM0, hM⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ =>
        (pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_spp hsupp_spp hθ)
  exact lintegral_slice_plancherel u
    (fun t θ : ℝ => pz (pz u) t θ - 2 * b * pz u t θ + b ^ 2 * u t θ)
    (fun ξ : ℝ => (muW b ξ) ^ 2) wE
    (fun ξ => by positivity) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_u ((measurable_muW b).pow_const 2) measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_spp measurable_wE)

/-- Identification of the (unshifted) third heavy slot. -/
theorem hidShiftThree {u : ℝ → ℝ → ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) Iθ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 : ℝ)
        * ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pth (pth u) p.1 p.2) ^ 2 * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pth : ContDiffOn ℝ 1 (Function.uncurry (pth u)) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_u
  have hcd_pthpth : ContDiffOn ℝ 0 (Function.uncurry (pth (pth u))) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_pth
  have hsupp_pthpth : ∀ t θ : ℝ, M < |t| → pth (pth u) t θ = 0 := supp_pthpth hM
  have hcont_pthpth : ContinuousOn (Function.uncurry (pth (pth u))) flStrip :=
    hcd_pthpth.continuousOn
  have hsl_q : ContinuousOn (fun p : ℝ × ℝ => slice (pth (pth u)) p.1 p.2) flStrip :=
    continuousOn_slice_joint hcont_pthpth ⟨M, hM0, hsupp_pthpth⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (pth (pth u) t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_pthpth hsupp_pthpth hθ)
  have hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => (1 : ℝ) * ‖slice (pth (pth u)) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (1 : ℝ) * ‖slice (pth (pth u)) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pth (pth u) t θ) ^ 2 := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    obtain ⟨h1, h2⟩ := plancherel_pthpth hg hθ
    refine ⟨h1.congr (Eventually.of_forall fun ξ => by simp), ?_⟩
    rw [show (∫ ξ : ℝ, (1 : ℝ) * ‖slice (pth (pth u)) ξ θ‖ ^ 2)
        = ∫ ξ : ℝ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 from
      integral_congr_ae (Eventually.of_forall fun ξ => by simp)]
    exact h2
  exact lintegral_slice_plancherel (pth (pth u)) (pth (pth u)) (fun _ : ℝ => (1 : ℝ)) wE
    (fun _ => zero_le_one) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_q measurable_const measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_pthpth measurable_wE)


end

end Work.FTS.EllSol.SpecAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.InteriorSmoothQ0_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology SchwartzMap
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The repaired chain -/


/-! ## The generic interior-regularity step -/

/-- **Interior regularity, generic form.**  A pair `(V, G)` with `V` locally integrable and `G`
smooth on the strip, satisfying the weak identity `∫ V · Kop ψ = ∫ G · ψ`, has a local `C^m`
representative near every interior point of the strip. -/
theorem localSmooth_generic_fts {V G : E2 → ℂ}
    (hV : MeasureTheory.LocallyIntegrableOn V stripE)
    (hG : MeasureTheory.LocallyIntegrableOn G stripE)
    (hGs : ∀ n : ℕ, ContDiffOn ℝ n G stripE)
    (hSW : StripWeakC V G) :
    ∀ (x₀ : E2) (m : ℕ), x₀ ∈ stripE →
      ∃ r : ℝ, 0 < r ∧ Metric.ball x₀ r ⊆ stripE ∧
        ∃ g : E2 → ℂ, ContDiffOn ℝ m g (Metric.ball x₀ r) ∧
          V =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r)] g := by
  intro x₀ m hx₀
  obtain ⟨h1, h2⟩ : 0 < x₀ 1 ∧ x₀ 1 < Real.pi / 2 := hx₀
  set δ : ℝ := min (x₀ 1) (Real.pi / 2 - x₀ 1) with hδdef
  have hδ : 0 < δ := lt_min h1 (by linarith [Real.pi_pos, h2])
  have hxδ : δ ≤ x₀ 1 := min_le_left _ _
  have hyδ : δ ≤ Real.pi / 2 - x₀ 1 := min_le_right _ _
  have hr8 : 0 < δ / 8 := by linarith
  -- the outer cut-off: supported in the strip, `1` on a neighbourhood of `x₀`
  set χout : E2 → ℂ := Work.EllipticEst.InteriorRegularity.VT.cfun x₀ (δ / 8) hr8 with hχoutdef
  have hout_s : ∀ n : ℕ, ContDiff ℝ n χout :=
    fun n => Work.EllipticEst.InteriorRegularity.VT.cfun_contDiff x₀ (δ / 8) hr8 n
  have hout_c : HasCompactSupport χout :=
    Work.EllipticEst.InteriorRegularity.VT.cfun_hasCompactSupport x₀ (δ / 8) hr8
  have hout_ts : tsupport χout ⊆ stripE := by
    intro x hx
    have hx' : x ∈ Metric.closedBall x₀ (2 * (δ / 8)) := by
      rw [hχoutdef, Work.EllipticEst.InteriorRegularity.VT.cfun_tsupport] at hx
      exact hx
    rw [Work.EllipticEst.InteriorRegularity.VT.mem_stripE]
    exact Work.EllipticEst.InteriorRegularity.VT.mem_Ioo_of_mem_ball hδ hxδ hyδ
      (Metric.closedBall_subset_ball (by linarith) hx')
  -- the cut-off pair is integrable and its source is smooth
  have hVt : Integrable (fun x : E2 => χout x * V x) :=
    integrable_mul_of_locallyIntegrableOn hV (hout_s 0).continuous hout_c hout_ts
  have hGt : Integrable (fun x : E2 => χout x * G x) :=
    integrable_mul_of_locallyIntegrableOn hG (hout_s 0).continuous hout_c hout_ts
  have hGts' : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => χout x * G x) :=
    fun n => contDiff_mul_of_tsupport_subset (U := stripE) (f := χout) (g := G)
      (hGs n) Work.EllipticEst.InteriorRegularity.VT.isOpen_stripE hout_s hout_ts
  have hweak : ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ {x : E2 | χout x = 1} →
      ∫ x, (χout x * V x) * Kop ψ x = ∫ x, (χout x * G x) * ψ x :=
    weakLocQ0 hSW hout_s hout_ts
  have hWball : Metric.closedBall x₀ (δ / 8) ⊆ {x : E2 | χout x = 1} := by
    intro x hx
    rw [hχoutdef]
    exact Work.EllipticEst.InteriorRegularity.VT.cfun_one hr8 hx
  -- the Sobolev tower
  obtain ⟨χ, hχs, hχc, ⟨ρ, hρ, hχ1⟩, hT⟩ :=
    Work.EllipticEst.InteriorRegularity.VT.tower (V := fun x : E2 => χout x * V x)
      (G := fun x : E2 => χout x * G x) hVt hGt hGts' hweak hδ hxδ hyδ hWball m
  have hIntχ : Integrable (fun x : E2 => χ x * (χout x * V x)) :=
    Work.EllipticEst.InteriorRegularity.VT.integrable_mul_of_cc hVt hχc hχs
  have hTχ : TemperedDistribution.MemSobolev (((m + 2 : ℕ) : ℝ)) 2
      (Work.EllipticEst.InteriorRegularity.VT.Td
        (fun x : E2 => χ x * (χout x * V x)) hIntχ) := by
    have h := hT hIntχ
    push_cast at h ⊢
    exact h
  -- the Sobolev embedding
  obtain ⟨r, hr, Φ, hΦ, hpairEmb⟩ :=
    Work.EllipticEst.InteriorRegularity.exists_contDiffOn_of_memSobolev (E := E2)
      (u := Work.EllipticEst.InteriorRegularity.VT.Td
        (fun x : E2 => χ x * (χout x * V x)) hIntχ) (k := m) (m := m + 2)
      (by rw [Work.EllipticEst.InteriorRegularity.VT.finrank_E2]; push_cast; linarith)
      hTχ x₀
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Work.EllipticEst.InteriorRegularity.VT.isOpen_stripE.mem_nhds
      (show x₀ ∈ stripE from ⟨h1, h2⟩))
  -- shrink the ball so that all the cut-offs are `1` on it
  set ρ' : ℝ := min (min ρ r) (δ / 8) / 2 with hρ'def
  have hminpos : 0 < min (min ρ r) (δ / 8) := lt_min (lt_min hρ hr) hr8
  have hρ' : 0 < ρ' := by
    rw [hρ'def]; linarith
  have hρ'ρ : ρ' < ρ := by
    rw [hρ'def]
    have h2 : min (min ρ r) (δ / 8) ≤ min ρ r := min_le_left _ _
    have h3 : min ρ r ≤ ρ := min_le_left _ _
    linarith
  have hρ'r : ρ' < r := by
    rw [hρ'def]
    have h2 : min (min ρ r) (δ / 8) ≤ min ρ r := min_le_left _ _
    have h3 : min ρ r ≤ r := min_le_right _ _
    linarith
  have hρ'δ : ρ' < δ / 8 := by
    rw [hρ'def]
    have h2 : min (min ρ r) (δ / 8) ≤ δ / 8 := min_le_right _ _
    linarith
  set r₀ : ℝ := min ρ' ε with hr₀def
  have hr₀ : 0 < r₀ := lt_min hρ' hε
  have hr₀sub : Metric.ball x₀ r₀ ⊆ stripE :=
    (Metric.ball_subset_ball (min_le_right ρ' ε)).trans hεsub
  have hr₀r : r₀ ≤ r := le_of_lt (lt_of_le_of_lt (min_le_left ρ' ε) hρ'r)
  have hr₀ρ : Metric.ball x₀ r₀ ⊆ Metric.closedBall x₀ ρ :=
    (Metric.ball_subset_ball (le_of_lt (lt_of_le_of_lt (min_le_left ρ' ε) hρ'ρ))).trans
      Metric.ball_subset_closedBall
  have hr₀δ : Metric.ball x₀ r₀ ⊆ Metric.closedBall x₀ (δ / 8) :=
    (Metric.ball_subset_ball (le_of_lt (lt_of_le_of_lt (min_le_left ρ' ε) hρ'δ))).trans
      Metric.ball_subset_closedBall
  -- the pairings of `Φ` and of the localized unknown
  have hpair : ∀ ψ : 𝓢(E2, ℂ), (∀ y, ψ y ≠ 0 → y ∈ Metric.ball x₀ r₀) →
      ∫ y, ψ y • Φ y = ∫ y, ψ y • (χout y * V y) := by
    intro ψ hψ
    have hψr : ∀ y, ψ y ≠ 0 → y ∈ Metric.ball x₀ r := fun y hy =>
      Metric.ball_subset_ball hr₀r (hψ y hy)
    have h1 : ∫ y, ψ y • Φ y = ∫ y, ψ y • (χ y * (χout y * V y)) := by
      rw [← hpairEmb ψ hψr]
      exact Work.EllipticEst.InteriorRegularity.VT.Td_apply _ _ ψ
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : ψ y = 0
    · simp [hy]
    · have hy2 : χ y = 1 := hχ1 y (hr₀ρ (hψ y hy))
      simp only [hy2, one_mul]
  have hVV : (fun x : E2 => χout x * V x)
      =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r₀)] Φ :=
    Work.EllipticEst.InteriorRegularity.VT.ae_eq_of_pairing
      (hΦ.mono (Metric.ball_subset_ball hr₀r)).continuousOn hVt hpair
  have hχ1ball : (fun x : E2 => χout x * V x)
      =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r₀)] V := by
    rw [Filter.EventuallyEq]
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr ?_
    refine Eventually.of_forall fun x hx => ?_
    show χout x * V x = V x
    rw [hWball (hr₀δ hx), one_mul]
  exact ⟨r₀, hr₀, hr₀sub, Φ, hΦ.mono (Metric.ball_subset_ball hr₀r),
    hχ1ball.symm.trans hVV⟩

/-! ## The requested theorem -/

theorem localRep_fts {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hsw : Work.EllipticEst.InteriorRegularity.Q0.StripWeakC
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Gf α F x : ℂ))) :
    ∀ (x₀ : E2) (m : ℕ), x₀ ∈ Work.EllipticEst.InteriorRegularity.stripE →
      ∃ r : ℝ, 0 < r ∧ Metric.ball x₀ r ⊆ Work.EllipticEst.InteriorRegularity.stripE ∧
        ∃ g : E2 → ℂ, ContDiffOn ℝ m g (Metric.ball x₀ r) ∧
          (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
            =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r)] g := by
  refine localSmooth_generic_fts ?_ ?_ ?_ hsw
  · exact locallyIntegrable_Vf hα.ne' hΨ
  · exact locallyIntegrableOn_Gf hα hF
  · exact smoothOn_Gf hα hF

/-- The real part of a complex number divided by a real one. -/
theorem div_ofReal_re_fts (z : ℂ) (r : ℝ) : (z / (r : ℂ)).re = z.re / r := by
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    simp
  · rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_im,
      Complex.ofReal_re]
    simp only [mul_zero, sub_zero]
    rw [div_eq_mul_inv]

/-- The quotient of a `C^∞` function of the strip by the (smooth, nonvanishing) weight is `C^∞`
on the quadrant. -/
theorem smoothOpen_final_fts {α : ℝ} (hα : 0 < α) {Φt : E2 → ℂ}
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φt stripE) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Φt (coords ((1 / α) * Real.log z) θ)).re
        / wt α (coords ((1 / α) * Real.log z) θ)) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have hlog' : ContDiffOn ℝ n (fun t : ℝ => (1 / α) * Real.log t) (Set.Ioi 0) :=
    contDiffOn_const.mul (Real.contDiffOn_log.mono (by
      intro t ht
      simpa using ne_of_gt ht))
  have hlog : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 / α) * Real.log p.1)
      Work.FTS.EllipticEst.Q0 := by
    have h := ContDiffOn.comp hlog' contDiff_fst.contDiffOn
      (fun p (hp : p ∈ Work.FTS.EllipticEst.Q0) => hp.1)
    simpa [Function.comp_def] using h
  have hth : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.2) Work.FTS.EllipticEst.Q0 :=
    contDiff_snd.contDiffOn
  have hpair : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 / α) * Real.log p.1, p.2))
      Work.FTS.EllipticEst.Q0 := hlog.prodMk hth
  have hchart : ContDiffOn ℝ n (fun p : ℝ × ℝ => coords ((1 / α) * Real.log p.1) p.2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_coords n).comp_contDiffOn hpair
  have hmap : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      coords ((1 / α) * Real.log p.1) p.2 ∈ stripE := by
    intro p hp
    rw [mem_stripE_iff]
    exact ⟨hp.2.1, hp.2.2⟩
  have hnum : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      (Φt (coords ((1 / α) * Real.log p.1) p.2)).re) Work.FTS.EllipticEst.Q0 :=
    Complex.reCLM.contDiff.comp_contDiffOn ((hΦ n).comp hchart hmap)
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      wt α (coords ((1 / α) * Real.log p.1) p.2)) Work.FTS.EllipticEst.Q0 :=
    (wt_contDiff α n).comp_contDiffOn hchart
  change ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      (Φt (coords ((1 / α) * Real.log p.1) p.2)).re
        / wt α (coords ((1 / α) * Real.log p.1) p.2)) Work.FTS.EllipticEst.Q0
  exact ContDiffOn.div (𝕜 := ℝ) (n := n) hnum hden (fun p hp => wt_ne_zero hα (hmap p hp))

/-! ## The final assembly -/

/-- **Weyl's lemma for `bslOp α` on the quadrant** (weight `(5-α)/α`): a locally integrable weak
solution agrees a.e. with a `C^∞` function. -/
theorem interiorSmoothQ0_fts {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) :
    ∃ Φ : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen Φ ∧
      (fun p : ℝ × ℝ => Ψ p.1 p.2)
        =ᵐ[MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0]
          (fun p : ℝ × ℝ => Φ p.1 p.2) := by
  classical
  -- the transported weak identity
  have hsw : StripWeakC (fun x : E2 => (Vf α Ψ x : ℂ)) (fun x : E2 => (Gf α F x : ℂ)) :=
    stripWeakQ0_of_RR (transportWeakRR hα hΨ hweak)
  -- local `C^m` representatives
  have hrep := localRep_fts hα hF hΨ hsw
  -- gluing
  obtain ⟨Φt, hΦt, hVfeq⟩ :=
    glueAll isOpen_stripE_fts (fun x hx => hrep x 0 hx) (fun x m hx => hrep x m hx)
  refine ⟨fun z θ => (Φt (coords ((1 / α) * Real.log z) θ)).re
      / wt α (coords ((1 / α) * Real.log z) θ), smoothOpen_final_fts hα hΦt, ?_⟩
  -- transport the a.e. equality back to `Q0`
  have h1 := ae_eq_of_ae_eq_Vf hα hVfeq
  filter_upwards [h1] with p hp
  have h2 : (Ψ p.1 p.2 : ℂ).re
      = (Φt (coords ((1 / α) * Real.log p.1) p.2)
          / (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ)).re := by rw [hp]
  rw [Complex.ofReal_re, div_ofReal_re_fts] at h2
  exact h2

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.S20SrcAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.s20_honesty =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rstar_WlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Rstar_WlInf`: de-weighting the `𝒲^{4,∞}`-bound on `ℛ(Φ̃_*)`

`Work.FTS.Nonlin.StarPkg α Cs Φs` controls the *weighted* coefficient
`H := ((z+1)/z)·ℛ(Φ̃_*)` of the self-similar vorticity equation in `𝒲^{4,∞}`, with
`|H|_{𝒲^{4,∞}} ≤ Cs·α` (`StarPkg.R`).  Row 10 of the design table needs the same control for
the *unweighted* coefficient `ℛ(Φ̃_*)`, truncated off the open quadrant in the angle.

Since `ℛ(Φ̃_*) = φ·H` with the de-weighting factor `φ z = z/(1+z)`, and the weighted
derivatives of `φ` are bounded on `[0,∞)` by `m!` (`phi_deriv_bound`), the Leibniz rule for
`∂_z^k` (`Work.FTS.H2.Q.pzIter_mul_local_sm`) gives

`|(z+1)^k ∂_z^k ℛ(Φ̃_*)| ≤ (∑_{c≤k} C(k,c) c!) · |H|_{𝒲^{4,∞}}` for `z > 0`,

and the same bound at `z = 0` by continuity of the `z`-derivatives of the `D_θ`-iterates of a
`SmoothQuad` function (`Work.FTS.H2.sqm_dthIter_zslice_contDiffAt`).  On the two angular
boundary lines the truncation vanishes (radial part) resp. the `𝒲^{4,∞}`-weight kills the
mixed part.
-/

noncomputable section

open scoped Real Topology ContDiff
open Set Filter MeasureTheory

namespace Work.FTS.Nonlinear.Pieces.RNP.row10aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The de-weighting factor `z ↦ z/(1+z)` and its derivatives -/

/-- The `m`-th derivative of `z ↦ (1+z)⁻¹` is `(-1)^m m! (1+z)^{-(m+1)}` on `(-1,∞)`. -/
lemma iteratedDeriv_inv_one_add_eqOn (m : ℕ) :
    Set.EqOn (iteratedDeriv m (fun z : ℝ => (1 + z)⁻¹))
      (fun z => (-1) ^ m * (m.factorial : ℝ) * ((1 + z)⁻¹) ^ (m + 1))
      (Set.Ioi (-1)) := by
  induction m with
  | zero => intro z hz; simp
  | succ m ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz)
        (fun w hw => ih hw))]
      rw [deriv_const_mul_field]
      have hψ : HasDerivAt (fun w : ℝ => (1 + w)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
        have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
        have hne : (1 : ℝ) + z ≠ 0 := by
          have := Set.mem_Ioi.mp hz; linarith
        have h := h1.inv hne
        rw [inv_pow]
        convert h using 1
        ring
      rw [show deriv (fun w : ℝ => (1 + w)⁻¹ ^ (m + 1)) z
            = ((m + 1 : ℕ) : ℝ) * (1 + z)⁻¹ ^ (m + 1 - 1) * (-((1 + z)⁻¹) ^ 2)
          from (hψ.pow (m + 1)).deriv]
      rw [Nat.add_sub_cancel]
      change (-1) ^ m * ↑m.factorial
            * (↑(m + 1) * (1 + z)⁻¹ ^ m * -(1 + z)⁻¹ ^ 2)
          = (-1) ^ (m + 1) * ↑((m + 1).factorial) * (1 + z)⁻¹ ^ (m + 1 + 1)
      have hxR : (1 + z)⁻¹ ^ (m + 1 + 1) = (1 + z)⁻¹ ^ m * (1 + z)⁻¹ ^ 2 := by
        rw [pow_succ, pow_succ, pow_two]; ring
      rw [hxR]
      rw [show (-1 : ℝ) ^ (m + 1) = (-1) ^ m * (-1) from by rw [pow_succ]]
      rw [show (((m + 1).factorial : ℕ) : ℝ) = (m.factorial : ℝ) * ((m + 1 : ℕ) : ℝ) from by
            rw [Nat.factorial_succ, Nat.cast_mul]; ring]
      ring

/-- The `m`-th derivative of `φ z = z/(1+z)` for `m ≥ 1`:
`φ^{(m)}(z) = (-1)^{m+1} m! (1+z)^{-(m+1)}`. -/
lemma iteratedDeriv_phi (m : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (hm : 1 ≤ m) :
    iteratedDeriv m (fun z : ℝ => z / (1 + z)) z
      = (-1) ^ (m + 1) * (m.factorial : ℝ) * ((1 + z)⁻¹) ^ (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hz_ne : z ≠ -1 := by
    have := Set.mem_Ioi.mp hz; linarith
  have hmem : {w : ℝ | w ≠ -1} ∈ 𝓝 z :=
    isOpen_compl_singleton.mem_nhds (by simpa using hz_ne)
  have hcongr : (fun w : ℝ => w / (1 + w)) =ᶠ[𝓝 z] (fun w : ℝ => 1 - (1 + w)⁻¹) :=
    Filter.eventually_of_mem hmem (fun w hw => by
      have h1 : (1 : ℝ) + w ≠ 0 := by
        intro hc; exact hw (by linarith)
      rw [eq_sub_iff_add_eq, add_comm]
      field_simp)
  rw [Filter.EventuallyEq.iteratedDeriv_eq (k + 1) hcongr]
  rw [iteratedDeriv_const_sub (by omega : 0 < k + 1) (1 : ℝ), iteratedDeriv_neg]
  rw [iteratedDeriv_inv_one_add_eqOn (k + 1) hz]
  rw [show (-1 : ℝ) ^ (k + 1 + 1) = (-1) ^ (k + 1) * (-1) from by rw [pow_succ]]
  ring

/-- **The weighted derivatives of the de-weighting factor are bounded by `m!`** on `[0,∞)`:
`(z+1)^m |φ^{(m)}(z)| ≤ m!` for `φ z = z/(1+z)`. -/
theorem phi_deriv_bound (m : ℕ) {z : ℝ} (hz : z ∈ Set.Ici (0 : ℝ)) :
    (z + 1) ^ m * |iteratedDeriv m (fun z : ℝ => z / (1 + z)) z| ≤ (m.factorial : ℝ) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hx1 : (0 : ℝ) < 1 + z := by linarith
  have hzI : z ∈ Set.Ioi (-1) := by
    simp only [Set.mem_Ioi]; linarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one]
    rw [abs_of_nonneg (by positivity), div_le_one hx1]
    linarith
  · rw [iteratedDeriv_phi m hzI hm]
    have h1 : |(-1 : ℝ) ^ (m + 1)| = 1 := by rw [abs_pow]; simp
    have h2 : |((1 + z)⁻¹) ^ (m + 1)| = ((1 + z)⁻¹) ^ (m + 1) :=
      abs_of_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hx1)) _)
    rw [abs_mul, abs_mul, h1, abs_of_nonneg (Nat.cast_nonneg m.factorial), h2, one_mul]
    have hkey : (z + 1) ^ m * ((1 + z)⁻¹) ^ (m + 1) = (1 + z)⁻¹ := by
      have hzeq : (z + 1) = (1 + z) := by ring
      rw [hzeq, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hx1), one_pow,
        one_mul]
    have hxle : (1 + z)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hx1]
      linarith
    calc (z + 1) ^ m * ((m.factorial : ℝ) * ((1 + z)⁻¹) ^ (m + 1))
        = (m.factorial : ℝ) * ((z + 1) ^ m * ((1 + z)⁻¹) ^ (m + 1)) := by ring
      _ = (m.factorial : ℝ) * (1 + z)⁻¹ := by rw [hkey]
      _ ≤ (m.factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left hxle (Nat.cast_nonneg _)
      _ = (m.factorial : ℝ) := by ring

/-- The arithmetic constant of the de-weighting: `∑_{c≤k} C(k,c) c! ≤ 65` for `k ≤ 4`
(the values are `1, 2, 5, 16, 65` for `k = 0,1,2,3,4`). -/
lemma choose_fact_sum_le_nat (k : ℕ) (hk : k ≤ 4) :
    ∑ c ∈ Finset.range (k + 1), k.choose c * c.factorial ≤ 65 := by
  interval_cases k <;> decide

lemma choose_fact_sum_le (k : ℕ) (hk : k ≤ 4) :
    ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ) * (c.factorial : ℝ) ≤ 65 := by
  have h := choose_fact_sum_le_nat k hk
  have hcast : ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ) * (c.factorial : ℝ)
      = ((∑ c ∈ Finset.range (k + 1), k.choose c * c.factorial : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun c _ => by rw [Nat.cast_mul])
  rw [hcast]
  exact_mod_cast h

/-! ## `D_θ`-iterates of a product with a factor depending only on `z` -/

/-- `D_θ^j` of a product with a `z`-only factor: the factor comes out. -/
theorem DthIter_mul_radial (j : ℕ) (φ : ℝ → ℝ) (G : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (fun z θ => φ z * G z θ)
      = fun z θ => φ z * Work.Spaces.DthIter j G z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field (φ z)]
      ring

/-- The `z/(1+z)` instance of `DthIter_mul_radial`. -/
lemma DthIter_mul_phi (j : ℕ) (H : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (fun z θ => z / (1 + z) * H z θ)
      = fun z θ => z / (1 + z) * Work.Spaces.DthIter j H z θ := by
  simpa using DthIter_mul_radial j (fun z : ℝ => z / (1 + z)) H

/-- `D_θ^j` of two functions which agree on an open subset of the quadrant agree there. -/
theorem DthIter_congr_nhds {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ∀ p ∈ V, u p.1 p.2 = v p.1 p.2) :
    ∀ j z θ, (z, θ) ∈ V → Work.Spaces.DthIter j u z θ = Work.Spaces.DthIter j v z θ := by
  intro j
  induction j with
  | zero => intro z θ hzθ; exact h (z, θ) hzθ
  | succ n ih =>
      intro z θ hzθ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      have hmaps : Tendsto (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (𝓝 θ) (𝓝 (z, θ)) :=
        (continuous_const.prodMk continuous_id).continuousAt
      refine Filter.eventually_of_mem (hmaps.eventually (hV.mem_nhds hzθ)) (fun θ' hθ' => ?_)
      exact ih z θ' hθ'

/-! ## Two general tools: a limit bound at `z = 0`, and vanishing of a zero slice -/


/-- A function whose `θ`-slice vanishes identically has vanishing `z`-derivatives there. -/
lemma pzIter_eq_zero_of_slice_zero {u : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, u z θ = 0)
    (k : ℕ) (z : ℝ) : Work.Spaces.pzIter k u z θ = 0 := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  rw [show (fun z' : ℝ => u z' θ) = fun _ => (0 : ℝ) from funext h,
    Work.Spaces.iteratedDeriv_zero_fun]

/-- Nonnegativity of the `𝒲^{l,∞}`-norm. -/
lemma wlInf_nonneg_of_mem {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.WlInfMem α l f) : 0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  refine add_nonneg (Finset.sum_nonneg fun k hk => ?_)
    (Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_)
  · exact Work.Spaces.supAbs_nonneg (h.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  · by_cases hcond : 1 ≤ j ∧ k + j ≤ l
    · rw [if_pos hcond]
      exact Work.Spaces.supAbs_nonneg (h.2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hcond.1 hcond.2)
    · rw [if_neg hcond]

/-! ## The de-weighting Leibniz bound -/

/-- **The de-weighting Leibniz bound.**  If `|(z+1)^m ∂_z^m X|·σ ≤ W` for every `m ≤ k`, then
the same holds for the Leibniz expansion of `∂_z^k ((z/(1+z))·X)`, with the constant
`∑_{c≤k} C(k,c) c! ≤ 65`. -/
lemma deweight_leibniz_sum_le {k : ℕ} (hk : k ≤ 4) {X : ℝ → ℝ → ℝ} {W σ z θ : ℝ}
    (hσnn : 0 ≤ σ) (hzz : (0 : ℝ) ≤ z) (hWnn : 0 ≤ W)
    (hper : ∀ c ≤ k, |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) X z θ * σ| ≤ W) :
    |(z + 1) ^ k * (∑ c ∈ Finset.range (k + 1),
        (k.choose c : ℝ) * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
          * Work.Spaces.pzIter (k - c) X z θ)) * σ| ≤ 65 * W := by
  have hpc0 : (0 : ℝ) ≤ z + 1 := by linarith
  rw [Finset.mul_sum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs
    (fun c => (z + 1) ^ k * ((k.choose c : ℝ)
      * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
        * Work.Spaces.pzIter (k - c) X z θ)) * σ) _) ?_
  have hterm : ∀ c ∈ Finset.range (k + 1),
      |(z + 1) ^ k * ((k.choose c : ℝ)
          * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
            * Work.Spaces.pzIter (k - c) X z θ)) * σ|
        ≤ ((k.choose c : ℝ) * (c.factorial : ℝ)) * W := by
    intro c hc
    have hcle : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hch : (0 : ℝ) ≤ (k.choose c : ℝ) := Nat.cast_nonneg _
    have hfac : (0 : ℝ) ≤ (c.factorial : ℝ) := Nat.cast_nonneg _
    have hpc : (0 : ℝ) ≤ (z + 1) ^ c := pow_nonneg hpc0 c
    have hqc : (0 : ℝ) ≤ (z + 1) ^ (k - c) := pow_nonneg hpc0 _
    have hβ : Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
        = iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    have hφb : (z + 1) ^ c * |iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z|
        ≤ (c.factorial : ℝ) := phi_deriv_bound c (Set.mem_Ici.mpr hzz)
    have hsplit : (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) := by
      rw [← pow_add, Nat.add_sub_cancel' hcle]
    have hkey : |(z + 1) ^ k * ((k.choose c : ℝ)
          * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
            * Work.Spaces.pzIter (k - c) X z θ)) * σ|
        = ((z + 1) ^ c * |iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z|)
          * ((k.choose c : ℝ)
            * ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) X z θ| * σ)) := by
      rw [hβ, hsplit]
      simp only [abs_mul, abs_of_nonneg hpc, abs_of_nonneg hqc, abs_of_nonneg hch,
        abs_of_nonneg hσnn]
      ring
    rw [hkey]
    have hper' := hper c hcle
    have habsper : |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) X z θ * σ|
        = (z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) X z θ| * σ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hqc, abs_of_nonneg hσnn]
    rw [habsper] at hper'
    calc ((z + 1) ^ c * |iteratedDeriv c (fun z' : ℝ => z' / (1 + z')) z|)
          * ((k.choose c : ℝ)
            * ((z + 1) ^ (k - c) * |Work.Spaces.pzIter (k - c) X z θ| * σ))
        ≤ (c.factorial : ℝ) * ((k.choose c : ℝ) * W) :=
          mul_le_mul hφb (mul_le_mul_of_nonneg_left hper' hch)
            (mul_nonneg hch (mul_nonneg (mul_nonneg hqc (abs_nonneg _)) hσnn)) hfac
      _ = ((k.choose c : ℝ) * (c.factorial : ℝ)) * W := by ring
  calc ∑ c ∈ Finset.range (k + 1),
        |(z + 1) ^ k * ((k.choose c : ℝ)
          * (Work.Spaces.pzIter c (fun z θ => z / (1 + z)) z θ
            * Work.Spaces.pzIter (k - c) X z θ)) * σ|
      ≤ ∑ c ∈ Finset.range (k + 1), ((k.choose c : ℝ) * (c.factorial : ℝ)) * W :=
        Finset.sum_le_sum hterm
    _ = (∑ c ∈ Finset.range (k + 1), ((k.choose c : ℝ) * (c.factorial : ℝ))) * W := by
        rw [Finset.sum_mul]
    _ ≤ 65 * W := mul_le_mul_of_nonneg_right (choose_fact_sum_le k hk) hWnn

/-! ## The smoothness of the de-weighted function on the open half-quadrant `z > 0` -/

/-- The de-weighting factor is `C^∞` at every `z > 0`. -/
lemma contDiffAt_phi {z : ℝ} (hz : (0 : ℝ) < z) :
    ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => z' / (1 + z')) z :=
  contDiffAt_id.div (contDiffAt_const.add contDiffAt_id) (by linarith)





end Work.FTS.Nonlinear.Pieces.RNP.row10aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.AClassDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Polynomial

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

/-- The coefficient family `c_{j,r}` of the recursion
`D_θ^{j+1}ψ = 4 cos²θ · D_θ^j P + ∑_{r ≤ j} c_{j,r} · D_θ^r ψ`.
For `r > j` the value is irrelevant (it is never used). -/
noncomputable def cVec : ℕ → ℕ → (ℝ → ℝ)
  | 0 => fun r => if r = 0 then (fun θ => 2 * Real.cos (2 * θ)) else 0
  | (j + 1) => fun r =>
      if r = j + 1 then (fun θ => cVec j j θ - 4 * Real.sin θ ^ 2)
      else if r = 0 then
        (fun θ => Work.Spaces.dthU (cVec j 0) θ + 4 * Real.sin θ ^ 2 * cVec j 0 θ)
      else
        (fun θ => Work.Spaces.dthU (cVec j r) θ + 4 * Real.sin θ ^ 2 * cVec j r θ
          + cVec j (r - 1) θ)

@[simp] theorem cVec_zero_zero : cVec 0 0 = fun θ => 2 * Real.cos (2 * θ) := by
  simp only [cVec]
  norm_num

theorem cVec_zero_of_ne (r : ℕ) (hr : r ≠ 0) : cVec 0 r = 0 := by
  simp only [cVec]
  rw [if_neg hr]

theorem cVec_succ_self (j : ℕ) :
    cVec (j + 1) (j + 1) = fun θ => cVec j j θ - 4 * Real.sin θ ^ 2 := by
  simp only [cVec]
  norm_num

theorem cVec_succ_zero (j : ℕ) :
    cVec (j + 1) 0 = fun θ => Work.Spaces.dthU (cVec j 0) θ
      + 4 * Real.sin θ ^ 2 * cVec j 0 θ := by
  cases j with
  | zero => simp only [cVec]; norm_num
  | succ j => simp only [cVec]; norm_num

theorem cVec_succ_of_ne (j r : ℕ) (h1 : r ≠ j + 1) (h0 : r ≠ 0) :
    cVec (j + 1) r = fun θ => Work.Spaces.dthU (cVec j r) θ
      + 4 * Real.sin θ ^ 2 * cVec j r θ + cVec j (r - 1) θ := by
  simp only [cVec]
  rw [if_neg h1, if_neg h0]

/-- A function of the shape `A(sin θ) + cos θ · B(sin θ)` with `A, B` polynomials.  The class is
closed under `+`, `·`, multiplication by a fixed trigonometric polynomial, and under
`D_θ = dthU`; every element is bounded (uniformly on `ℝ`). -/
def IsCoef (f : ℝ → ℝ) : Prop :=
  ∃ A B : Polynomial ℝ, ∀ θ : ℝ,
    f θ = A.eval (Real.sin θ) + Real.cos θ * B.eval (Real.sin θ)

/-! ## Closure properties of `IsCoef` -/

theorem IsCoef_zero : IsCoef (0 : ℝ → ℝ) :=
  ⟨0, 0, fun θ => by simp⟩

theorem IsCoef_add {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f + g) := by
  obtain ⟨A₁, B₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, h₂⟩ := hg
  refine ⟨A₁ + A₂, B₁ + B₂, fun θ => ?_⟩
  rw [Pi.add_apply, h₁ θ, h₂ θ]
  simp only [Polynomial.eval_add]
  ring


theorem IsCoef_sub {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f - g) := by
  obtain ⟨A₁, B₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, h₂⟩ := hg
  refine ⟨A₁ - A₂, B₁ - B₂, fun θ => ?_⟩
  rw [Pi.sub_apply, h₁ θ, h₂ θ]
  simp only [Polynomial.eval_sub]
  ring


theorem IsCoef_mul {f g : ℝ → ℝ} (hf : IsCoef f) (hg : IsCoef g) : IsCoef (f * g) := by
  obtain ⟨A₁, B₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, h₂⟩ := hg
  refine ⟨A₁ * A₂ + (1 - Polynomial.X ^ 2) * (B₁ * B₂), A₁ * B₂ + A₂ * B₁, fun θ => ?_⟩
  rw [Pi.mul_apply, h₁ θ, h₂ θ]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring_nf
  linear_combination (B₁.eval (Real.sin θ) * B₂.eval (Real.sin θ)) * Real.sin_sq_add_cos_sq θ

theorem IsCoef_two_cos_two : IsCoef (fun θ : ℝ => 2 * Real.cos (2 * θ)) := by
  refine ⟨Polynomial.C 2 - Polynomial.C 4 * Polynomial.X ^ 2, 0, fun θ => ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_zero, mul_zero, add_zero]
  rw [Real.cos_two_mul, Real.cos_sq']
  ring

theorem IsCoef_four_sin_sq : IsCoef (fun θ : ℝ => 4 * Real.sin θ ^ 2) :=
  ⟨Polynomial.C 4 * Polynomial.X ^ 2, 0, fun θ => by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_zero, mul_zero, add_zero]⟩


/-- `dthU` preserves the class `IsCoef` (note the extra `cos θ`-factor coming from
`d/dθ (cos θ · B(sin θ)) = - sin θ · B + cos θ · B' · cos θ`). -/
theorem IsCoef_dthU {f : ℝ → ℝ} (hf : IsCoef f) : IsCoef (Work.Spaces.dthU f) := by
  obtain ⟨A, B, h⟩ := hf
  refine ⟨Polynomial.C 2 * Polynomial.X * (1 - Polynomial.X ^ 2) * Polynomial.derivative A,
    Polynomial.C 2 * Polynomial.X * (1 - Polynomial.X ^ 2) * Polynomial.derivative B
      - Polynomial.C 2 * Polynomial.X ^ 2 * B, fun θ => ?_⟩
  have hfun : f = fun φ : ℝ => A.eval (Real.sin φ) + Real.cos φ * B.eval (Real.sin φ) :=
    funext h
  rw [hfun]
  have hsin : HasDerivAt (fun φ : ℝ => Real.sin φ) (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have hcos : HasDerivAt (fun φ : ℝ => Real.cos φ) (-(Real.sin θ)) θ := Real.hasDerivAt_cos θ
  have hA : HasDerivAt (fun φ : ℝ => A.eval (Real.sin φ))
      (A.derivative.eval (Real.sin θ) * Real.cos θ) θ :=
    (Polynomial.hasDerivAt A (Real.sin θ)).comp θ hsin
  have hB : HasDerivAt (fun φ : ℝ => B.eval (Real.sin φ))
      (B.derivative.eval (Real.sin θ) * Real.cos θ) θ :=
    (Polynomial.hasDerivAt B (Real.sin θ)).comp θ hsin
  have hcB : HasDerivAt (fun φ : ℝ => Real.cos φ * B.eval (Real.sin φ))
      ((-(Real.sin θ)) * B.eval (Real.sin θ)
        + Real.cos θ * (B.derivative.eval (Real.sin θ) * Real.cos θ)) θ := hcos.mul hB
  have hfd : HasDerivAt (fun φ : ℝ => A.eval (Real.sin φ) + Real.cos φ * B.eval (Real.sin φ))
      (A.derivative.eval (Real.sin θ) * Real.cos θ
        + ((-(Real.sin θ)) * B.eval (Real.sin θ)
          + Real.cos θ * (B.derivative.eval (Real.sin θ) * Real.cos θ))) θ := hA.add hcB
  rw [Work.Spaces.dthU_apply, hfd.deriv]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_pow, Real.sin_two_mul]
  ring_nf
  linear_combination (2 * Real.sin θ * A.derivative.eval (Real.sin θ)
    + 2 * Real.sin θ * Real.cos θ * B.derivative.eval (Real.sin θ))
    * Real.sin_sq_add_cos_sq θ

theorem IsCoef_differentiableAt {f : ℝ → ℝ} (hf : IsCoef f) (θ : ℝ) :
    DifferentiableAt ℝ f θ := by
  obtain ⟨A, B, h⟩ := hf
  rw [show f = fun θ => A.eval (Real.sin θ) + Real.cos θ * B.eval (Real.sin θ) from funext h]
  exact (((Polynomial.hasDerivAt A (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)).add
    ((Real.hasDerivAt_cos θ).mul
      ((Polynomial.hasDerivAt B (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)))).differentiableAt

theorem IsCoef_bounded {f : ℝ → ℝ} (hf : IsCoef f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : ℝ, |f θ| ≤ M := by
  obtain ⟨A, B, h⟩ := hf
  obtain ⟨MA, hMA⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) (Polynomial.continuous A).continuousOn
  obtain ⟨MB, hMB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) (Polynomial.continuous B).continuousOn
  refine ⟨max MA 0 + max MB 0, add_nonneg (le_max_right _ _) (le_max_right _ _), fun θ => ?_⟩
  rw [h θ]
  have hsin : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hA : |A.eval (Real.sin θ)| ≤ max MA 0 :=
    le_trans (by simpa [Real.norm_eq_abs] using hMA _ hsin) (le_max_left _ _)
  have hB : |Real.cos θ * B.eval (Real.sin θ)| ≤ max MB 0 := by
    rw [abs_mul]
    calc |Real.cos θ| * |B.eval (Real.sin θ)|
        ≤ 1 * max MB 0 :=
          mul_le_mul (Real.abs_cos_le_one θ)
            (le_trans (by simpa [Real.norm_eq_abs] using hMB _ hsin) (le_max_left _ _))
            (abs_nonneg _) (by norm_num)
      _ = max MB 0 := one_mul _
  calc |A.eval (Real.sin θ) + Real.cos θ * B.eval (Real.sin θ)|
      ≤ |A.eval (Real.sin θ)| + |Real.cos θ * B.eval (Real.sin θ)| := abs_add_le _ _
    _ ≤ max MA 0 + max MB 0 := add_le_add hA hB

/-! ## The coefficients `cVec j r` are in the class -/

theorem cVec_isCoef : ∀ j r : ℕ, IsCoef (cVec j r) := by
  intro j
  induction j with
  | zero =>
      intro r
      rcases eq_or_ne r 0 with h | h
      · subst h; exact IsCoef_two_cos_two
      · rw [cVec_zero_of_ne r h]; exact IsCoef_zero
  | succ j ih =>
      intro r
      rcases eq_or_ne r (j + 1) with h | h
      · rw [h, cVec_succ_self]
        exact IsCoef_sub (ih j) IsCoef_four_sin_sq
      · rcases eq_or_ne r 0 with h0 | h0
        · subst h0
          rw [cVec_succ_zero]
          exact IsCoef_add (IsCoef_dthU (ih 0)) (IsCoef_mul IsCoef_four_sin_sq (ih 0))
        · rw [cVec_succ_of_ne j r h h0]
          exact IsCoef_add (IsCoef_add (IsCoef_dthU (ih r))
            (IsCoef_mul IsCoef_four_sin_sq (ih r))) (ih (r - 1))

/-- A uniform bound for the coefficients `cVec j r`. -/
noncomputable def cB (j r : ℕ) : ℝ :=
  Classical.choose (IsCoef_bounded (cVec_isCoef j r))



end Work.FTS.PhiStar.Psi0Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

/-! ## The model functions -/

/-- `q = P/sin²θ = w₀'`, extended to all of `ℝ` by totalisation: `qfun α 0 = 0` and
`qfun α (π/2) = Pfun α (π/2)/1 = 0`. -/
def qfun (α : ℝ) (θ : ℝ) : ℝ := Pfun α θ / Real.sin θ ^ 2

/-- The explicit model for the first derivative of `psiSol α`:
`M1 α θ = 2cos(2θ)(Kc + w₀) + sin(2θ)·q`. -/
def M1 (α : ℝ) (θ : ℝ) : ℝ :=
  2 * Real.cos (2 * θ) * (Kc α + wZer α θ) + Real.sin (2 * θ) * qfun α θ

@[simp] lemma qfun_apply (α θ : ℝ) : qfun α θ = Pfun α θ / Real.sin θ ^ 2 := rfl

@[simp] lemma M1_apply (α θ : ℝ) :
    M1 α θ = 2 * Real.cos (2 * θ) * (Kc α + wZer α θ) + Real.sin (2 * θ) * qfun α θ :=
  rfl

/-! ## Separation of variables for `z`-independent functions -/

/-- `∂_z^{k}` of a function of `θ` alone vanishes for `k ≥ 1`. -/
theorem pzIter_theta_only_succ (g : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter (k + 1) (fun _ θ => g θ) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero =>
      funext z θ
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      simp
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      rw [Work.Spaces.pz]
      simp

/-- `D_θ^j` of a function of `θ` alone is the `dthU`-iterate of that function. -/
theorem DthIter_theta_only (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun _ θ => g θ) = fun _ θ => Work.Spaces.dthU^[j] g θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      rw [Work.Spaces.Dth, Work.Spaces.pth, ← Work.Spaces.dthU_apply,
        Function.iterate_succ_apply']


/-! ## Vanishing of the `dthU`-iterates at the angular boundary -/

lemma dthU_apply_zero (f : ℝ → ℝ) : Work.Spaces.dthU f 0 = 0 := by
  simp [Work.Spaces.dthU_apply]

lemma dthU_apply_pi_half (f : ℝ → ℝ) : Work.Spaces.dthU f (Real.pi / 2) = 0 := by
  rw [Work.Spaces.dthU_apply, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
    zero_mul]

lemma dthU_iter_apply_zero (f : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.dthU^[j] f 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + k = k + 1 from by omega, Function.iterate_succ_apply']
  exact dthU_apply_zero _

lemma dthU_iter_apply_pi_half (f : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.dthU^[j] f (Real.pi / 2) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + k = k + 1 from by omega, Function.iterate_succ_apply']
  exact dthU_apply_pi_half _

end Work.FTS.PhiStar.Psi0Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.exists_WBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option maxHeartbeats 1600000

namespace WB

/-! ## `dthU` on an open set: smoothness, differentiability, germ-locality and linearity -/

/-- `dthU φ = sin(2·) · φ'` as a function equality. -/
lemma dthU_eq_fun (φ : ℝ → ℝ) :
    Work.Spaces.dthU φ = fun θ : ℝ => Real.sin (2 * θ) * deriv φ θ := by
  funext θ
  rw [Work.Spaces.dthU_apply]

/-- `dthU` preserves `C^∞`-smoothness on an open set. -/
lemma dthU_contDiffOn {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU f) U := by
  have hone : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by simp
  have hd : ContDiffOn ℝ (∞ : ℕ∞ω) (deriv f) U :=
    hf.deriv_of_isOpen hU (m := (∞ : ℕ∞ω)) hone
  have hsin : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
  rw [dthU_eq_fun]
  exact hsin.mul hd

/-- Every iterate of `dthU` preserves `C^∞`-smoothness on an open set. -/
lemma dthU_iter_contDiffOn {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (m : ℕ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU^[m] f) U := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact dthU_contDiffOn hU ih

/-- Interior differentiability of the `dthU`-iterates of a `C^∞`-function. -/
lemma dthU_iter_differentiableAt {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (m : ℕ) {θ : ℝ} (hθ : θ ∈ U) :
    DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
  ((dthU_iter_contDiffOn hU hf m).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)

/-- Germ-locality of the `dthU`-iterates. -/
lemma dthU_iter_congr {f g : ℝ → ℝ} {θ : ℝ}
    (h : Filter.EventuallyEq (nhds θ) f g) (m : ℕ) :
    Work.Spaces.dthU^[m] f θ = Work.Spaces.dthU^[m] g θ := by
  have hmain : ∀ m : ℕ, Filter.EventuallyEq (nhds θ) (Work.Spaces.dthU^[m] f)
      (Work.Spaces.dthU^[m] g) := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
        have hd : Filter.EventuallyEq (nhds θ) (deriv (Work.Spaces.dthU^[m] f))
            (deriv (Work.Spaces.dthU^[m] g)) := ih.deriv
        have hm :=
          (Filter.EventuallyEq.refl (nhds θ) (fun θ' : ℝ => Real.sin (2 * θ'))).mul hd
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dthU_eq_fun, dthU_eq_fun]
        exact hm
  exact (hmain m).eq_of_nhds

/-- The derivative of the three-term combination. -/
lemma deriv_three {Uf Ug Uh : ℝ → ℝ} {θ : ℝ}
    (hdf : DifferentiableAt ℝ Uf θ) (hdg : DifferentiableAt ℝ Ug θ)
    (hdh : DifferentiableAt ℝ Uh θ) :
    deriv (fun x => 2 * Uf x - 4 * Ug x - Uh x) θ
      = 2 * deriv Uf θ - 4 * deriv Ug θ - deriv Uh θ := by
  have h := ((hdf.hasDerivAt.const_mul 2).sub (hdg.hasDerivAt.const_mul 4)).sub hdh.hasDerivAt
  exact h.deriv

/-- Linearity of the `dthU`-iterates on an open set (the three-term form used below). -/
lemma dthU_iter_three_eqOn {U : Set ℝ} (hU : IsOpen U) {f g h : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (hg : ContDiffOn ℝ (∞ : ℕ∞ω) g U)
    (hh : ContDiffOn ℝ (∞ : ℕ∞ω) h U) (m : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[m] (fun θ => 2 * f θ - 4 * g θ - h θ))
      (fun θ => 2 * Work.Spaces.dthU^[m] f θ - 4 * Work.Spaces.dthU^[m] g θ
        - Work.Spaces.dthU^[m] h θ) U := by
  induction m with
  | zero => intro θ hθ; simp
  | succ m ih =>
      intro θ hθ
      have hev : Filter.EventuallyEq (nhds θ)
          (Work.Spaces.dthU^[m] (fun θ => 2 * f θ - 4 * g θ - h θ))
          (fun θ => 2 * Work.Spaces.dthU^[m] f θ - 4 * Work.Spaces.dthU^[m] g θ
            - Work.Spaces.dthU^[m] h θ) :=
        ih.eventuallyEq_of_mem (hU.mem_nhds hθ)
      have hder : deriv (Work.Spaces.dthU^[m] (fun θ => 2 * f θ - 4 * g θ - h θ)) θ
          = deriv (fun x => 2 * Work.Spaces.dthU^[m] f x - 4 * Work.Spaces.dthU^[m] g x
              - Work.Spaces.dthU^[m] h x) θ := hev.deriv_eq
      have hdf : DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
        dthU_iter_differentiableAt hU hf m hθ
      have hdg : DifferentiableAt ℝ (Work.Spaces.dthU^[m] g) θ :=
        dthU_iter_differentiableAt hU hg m hθ
      have hdh : DifferentiableAt ℝ (Work.Spaces.dthU^[m] h) θ :=
        dthU_iter_differentiableAt hU hh m hθ
      have hstep : Work.Spaces.dthU (Work.Spaces.dthU^[m]
            (fun θ => 2 * f θ - 4 * g θ - h θ)) θ
          = 2 * Work.Spaces.dthU (Work.Spaces.dthU^[m] f) θ
            - 4 * Work.Spaces.dthU (Work.Spaces.dthU^[m] g) θ
            - Work.Spaces.dthU (Work.Spaces.dthU^[m] h) θ := by
        rw [Work.Spaces.dthU_apply, hder, Work.Spaces.dthU_apply, Work.Spaces.dthU_apply,
          Work.Spaces.dthU_apply, deriv_three hdf hdg hdh]
        ring
      rw [Function.iterate_succ_apply' (Work.Spaces.dthU) m
            (fun θ => 2 * f θ - 4 * g θ - h θ),
        Function.iterate_succ_apply' (Work.Spaces.dthU) m f,
        Function.iterate_succ_apply' (Work.Spaces.dthU) m g,
        Function.iterate_succ_apply' (Work.Spaces.dthU) m h]
      exact hstep

/-! ## The value of `D_θ^j ψ''` via the two-term identity -/

/-- On `(0,π/2)` the `dthU`-iterates of `ψ''` split as `2 D_θ^j P − 4 D_θ^j ψ − D_θ^j Γ̄`. -/
lemma sndDeriv_dthU_iter
    (hident : ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 (psiSol α) θ
        = 2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.dthU^[j] (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ') θ
      = 2 * Work.Spaces.dthU^[j] (Pfun α) θ - 4 * Work.Spaces.dthU^[j] (psiSol α) θ
        - Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have heq : Set.EqOn (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ')
      (fun θ' : ℝ => 2 * Pfun α θ' - 4 * psiSol α θ' - Work.FTS.VocabO.GamBar α θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun θ' hθ' => hident α hα hα1 θ' hθ'
  have hev : Filter.EventuallyEq (nhds θ) (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ')
      (fun θ' : ℝ => 2 * Pfun α θ' - 4 * psiSol α θ' - Work.FTS.VocabO.GamBar α θ') :=
    heq.eventuallyEq_of_mem (hU.mem_nhds hθ)
  rw [dthU_iter_congr hev j]
  have hGam : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ' : ℝ => Work.FTS.VocabO.GamBar α θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show (fun θ' : ℝ => Work.FTS.VocabO.GamBar α θ')
        = fun θ' => Work.Spaces.Gam α θ' * (1 / Work.Spaces.c α) - (5 / 4) * Real.sin (2 * θ')
      from by funext t; rw [Work.FTS.VocabO.GamBar]; ring]
    exact ((contDiffOn_Gam α).mul contDiffOn_const).sub (contDiffOn_const.mul (by fun_prop))
  exact dthU_iter_three_eqOn hU (contDiffOn_Pfun α (le_of_lt hα))
    (contDiffOn_psiSol α hα hα1) hGam j hθ

/-! ## The weighted bounds -/

/-- The angular weight `w = sin(2θ)^{-α/5}/(α + sin 2θ)` is nonnegative on the open quadrant. -/
lemma weight_nonneg (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) := by
  have h2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  exact div_nonneg (Real.rpow_nonneg (le_of_lt h2θ) _) (le_of_lt hden)

/-- `α · sin²θ · cos^{2α/3}θ · w ≤ 1`. -/
lemma weight_P_mul_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
  have h2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt hθ.2⟩
  have hF := sin_sq_cos_rpow_mul_rpow_le α θ hα hα1 hθ
  have hFnn : 0 ≤ Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hcos _))
      (Real.rpow_nonneg (le_of_lt h2θ) _)
  have hfrac : α / (α + Real.sin (2 * θ)) ≤ 1 := by
    rw [div_le_one hden]; linarith [h2θ]
  calc α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (α / (α + Real.sin (2 * θ)))
          * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)
            * (Real.sin (2 * θ)) ^ (-(α / 5))) := by ring
    _ ≤ 1 * 1 := mul_le_mul hfrac hF hFnn (by norm_num)
    _ = 1 := by norm_num

/-- `sin(2θ) · w ≤ 2`. -/
lemma weight_sin_mul_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin (2 * θ) * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 2 := by
  have h2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hkey : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
      = (Real.sin (2 * θ)) ^ (1 - α / 5) := by
    have h := Real.rpow_add h2θ 1 (-(α / 5))
    rw [Real.rpow_one] at h
    exact h.symm
  have h2 := sin_two_rpow_div_le α (Real.sin (2 * θ)) hα hα1 h2θ (Real.sin_le_one _)
  have hsplit : Real.sin (2 * θ)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (Real.sin (2 * θ)) ^ (1 - α / 5) / (α + Real.sin (2 * θ)) := by
    rw [← mul_div_assoc, hkey]
  rw [hsplit]
  exact h2

/-- `α · Γ(θ) · w ≤ 1`. -/
lemma weight_Gam_mul_le (α θ : ℝ) (hα : 0 < α)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    α * Work.Spaces.Gam α θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
  have h := Work.Spaces.Gam_mul_weight_le α θ hα (Set.Ioo_subset_Icc_self hθ)
  rwa [show α * Work.Spaces.Gam α θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) from by rw [mul_div_assoc]]

/-- The weighted bound for a combination of the three class bounds. -/
lemma weighted_comb_le (κ ℓ ν cc dd : ℕ → ℝ)
    (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) (hν0 : ∀ j, 0 ≤ ν j)
    (hcc0 : ∀ j, 0 ≤ cc j) (hdd0 : ∀ j, 0 ≤ dd j)
    {j : ℕ} {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {A B C : ℝ}
    (hA : A ≤ κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
      + ℓ j * Real.sin (2 * θ))
    (hB : B ≤ ν j * Real.sin (2 * θ))
    (hC : C ≤ cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ)) :
    (2 * A + 4 * B + C)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 2 * κ j + 4 * ℓ j + 8 * ν j + cc j + 2 * dd j := by
  have hwnn := weight_nonneg α θ hα hθ
  have hPw := weight_P_mul_le α θ hα hα1 hθ
  have hSw := weight_sin_mul_le α θ hα hα1 hθ
  have hGw := weight_Gam_mul_le α θ hα hθ
  have hAw : A * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ κ j + 2 * ℓ j := by
    have h1 : A * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
            + ℓ j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right hA hwnn
    have h2 : (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
            + ℓ j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ κ j * 1 + ℓ j * 2 := by
      have he : (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
            + ℓ j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = κ j * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            + ℓ j * (Real.sin (2 * θ)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      rw [he]
      exact add_le_add (mul_le_mul_of_nonneg_left hPw (hκ0 j))
        (mul_le_mul_of_nonneg_left hSw (hℓ0 j))
    linarith
  have hBw : B * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ ν j * 2 := by
    have h1 : B * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ ν j * Real.sin (2 * θ)
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right hB hwnn
    have h2 : ν j * Real.sin (2 * θ)
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ ν j * 2 := by
      have he : ν j * Real.sin (2 * θ)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = ν j * (Real.sin (2 * θ)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hSw (hν0 j)
    linarith
  have hCw : C * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ cc j + 2 * dd j := by
    have h1 : C * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ (cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right hC hwnn
    have h2 : (cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ cc j * 1 + dd j * 2 := by
      have he : (cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = cc j * (α * Work.Spaces.Gam α θ
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            + dd j * (Real.sin (2 * θ)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      rw [he]
      exact add_le_add (mul_le_mul_of_nonneg_left hGw (hcc0 j))
        (mul_le_mul_of_nonneg_left hSw (hdd0 j))
    linarith
  have he : (2 * A + 4 * B + C)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = 2 * (A * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        + 4 * (B * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        + C * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by ring
  rw [he]
  linarith [hAw, hBw, hCw]

end WB

theorem exists_WBound
    (hident : ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 (psiSol α) θ = 2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ)
    (hZ : ∃ κ ell : ℕ → ℝ, ZClass κ ell) (hA : ∃ ν : ℕ → ℝ, AClass ν)
    (hH : ∃ cc dd : ℕ → ℝ, HClass cc dd) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |iteratedDeriv 2 (psiSol α) θ| ≤ C ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 5 →
        |Work.Spaces.dthU^[j] (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ') θ|
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ C) := by
  obtain ⟨κ, ℓ, hκ0, hℓ0, hZb⟩ := hZ
  obtain ⟨ν, hν0, hAb⟩ := hA
  obtain ⟨cc, dd, hcc0, hdd0, hHb⟩ := hH
  set S : ℝ := ∑ j ∈ Finset.range 6, (κ j + ℓ j + ν j + cc j + dd j) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun j _ => by
      have h1 := hκ0 j; have h2 := hℓ0 j; have h3 := hν0 j
      have h4 := hcc0 j; have h5 := hdd0 j
      linarith)
  refine ⟨1000 + 4 * ν 0 + 1000 * S, by have := hν0 0; linarith, ?_⟩
  intro α hα hα1 θ hθ
  have h2θpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have h2θle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  constructor
  · -- the pointwise bound on `ψ''`
    have hid := hident α hα hα1 θ hθ
    have hP := Pfun_abs_le α hα hα1 (Set.Ioo_subset_Icc_self hθ)
    have hψ : |psiSol α θ| ≤ ν 0 * Real.sin (2 * θ) := by
      have := hAb α hα hα1 0 (by norm_num) θ hθ
      simpa using this
    have hΓ := abs_GamBar_le α θ hα (by linarith) (Set.Ioo_subset_Icc_self hθ)
    have hcinv : 1 / Work.Spaces.c α ≤ 10 := by
      have hc := (Work.Spaces.c_bounds α hα (by linarith : α ≤ 1)).1
      calc 1 / Work.Spaces.c α ≤ 1 / (1 / 10 : ℝ) := one_div_le_one_div_of_le (by norm_num) hc
        _ = 10 := by norm_num
    have habs : |2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ|
        ≤ 2 * |Pfun α θ| + 4 * |psiSol α θ| + |Work.FTS.VocabO.GamBar α θ| := by
      have h1 : |2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ|
          ≤ |2 * Pfun α θ - 4 * psiSol α θ| + |Work.FTS.VocabO.GamBar α θ| := abs_sub _ _
      have h2 : |2 * Pfun α θ - 4 * psiSol α θ| ≤ |2 * Pfun α θ| + |4 * psiSol α θ| :=
        abs_sub _ _
      have h3 : |(2 : ℝ) * Pfun α θ| = 2 * |Pfun α θ| := by rw [abs_mul]; norm_num
      have h4 : |(4 : ℝ) * psiSol α θ| = 4 * |psiSol α θ| := by rw [abs_mul]; norm_num
      linarith
    rw [hid]
    calc |2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ|
        ≤ 2 * |Pfun α θ| + 4 * |psiSol α θ| + |Work.FTS.VocabO.GamBar α θ| := habs
      _ ≤ 2 * 20 + 4 * (ν 0 * Real.sin (2 * θ)) + (1 / Work.Spaces.c α + 5 / 4) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hP (by norm_num))
            (mul_le_mul_of_nonneg_left hψ (by norm_num))) hΓ
      _ ≤ 1000 + 4 * ν 0 + 1000 * S := by
          have h1 : 4 * (ν 0 * Real.sin (2 * θ)) ≤ 4 * (ν 0 * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2θle (hν0 0)) (by norm_num)
          linarith [h1, hcinv, hSnn]
  · -- the weighted bounds for `1 ≤ j ≤ 5`
    intro j hj1 hj5
    have hjmem : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
    have hSterm : κ j + ℓ j + ν j + cc j + dd j ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (s := Finset.range 6)
        (f := fun i => κ i + ℓ i + ν i + cc i + dd i) (a := j) (fun i _ => by
          have h1 := hκ0 i; have h2 := hℓ0 i; have h3 := hν0 i
          have h4 := hcc0 i; have h5 := hdd0 i
          linarith) hjmem
    have hP := hZb α hα hα1 j hj1 hj5 θ hθ
    have hψ : |Work.Spaces.dthU^[j] (psiSol α) θ| ≤ ν j * Real.sin (2 * θ) :=
      hAb α hα hα1 j (by omega) θ hθ
    have hΓ := hHb α hα hα1 j hj1 hj5 θ hθ
    rw [mul_div_assoc]
    have hid := WB.sndDeriv_dthU_iter hident α hα hα1 j hθ
    rw [hid]
    have habs : |2 * Work.Spaces.dthU^[j] (Pfun α) θ
          - 4 * Work.Spaces.dthU^[j] (psiSol α) θ
          - Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
        ≤ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
          + 4 * |Work.Spaces.dthU^[j] (psiSol α) θ|
          + |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ| := by
      have h1 : |2 * Work.Spaces.dthU^[j] (Pfun α) θ
            - 4 * Work.Spaces.dthU^[j] (psiSol α) θ
            - Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
          ≤ |2 * Work.Spaces.dthU^[j] (Pfun α) θ
              - 4 * Work.Spaces.dthU^[j] (psiSol α) θ|
            + |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ| := abs_sub _ _
      have h2 : |2 * Work.Spaces.dthU^[j] (Pfun α) θ
            - 4 * Work.Spaces.dthU^[j] (psiSol α) θ|
          ≤ |2 * Work.Spaces.dthU^[j] (Pfun α) θ|
            + |4 * Work.Spaces.dthU^[j] (psiSol α) θ| := abs_sub _ _
      have h3 : |(2 : ℝ) * Work.Spaces.dthU^[j] (Pfun α) θ|
          = 2 * |Work.Spaces.dthU^[j] (Pfun α) θ| := by rw [abs_mul]; norm_num
      have h4 : |(4 : ℝ) * Work.Spaces.dthU^[j] (psiSol α) θ|
          = 4 * |Work.Spaces.dthU^[j] (psiSol α) θ| := by rw [abs_mul]; norm_num
      linarith
    have hw := WB.weight_nonneg α θ hα hθ
    refine le_trans (mul_le_mul_of_nonneg_right habs hw) ?_
    have hcomb := WB.weighted_comb_le κ ℓ ν cc dd hκ0 hℓ0 hν0 hcc0 hdd0 hα hα1 hθ
      (j := j) hP hψ hΓ
    refine le_trans hcomb ?_
    have h1 := hκ0 j; have h2 := hℓ0 j; have h3 := hν0 j
    have h4 := hcc0 j; have h5 := hdd0 j
    have h00 : (0 : ℝ) ≤ ν 0 := hν0 0
    have h6 : 2 * κ j + 4 * ℓ j + 8 * ν j + cc j + 2 * dd j
        ≤ 8 * (κ j + ℓ j + ν j + cc j + dd j) := by linarith
    have h7 : 8 * (κ j + ℓ j + ν j + cc j + dd j)
        ≤ 1000 * (κ j + ℓ j + ν j + cc j + dd j) := by linarith
    have h8 : 1000 * (κ j + ℓ j + ν j + cc j + dd j) ≤ 1000 * S := by linarith
    linarith

end Work.FTS.PhiStar.Psi0Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.fourCosSqBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open Work.FTS.PhiStar

/-- The universal bound `4 cos²θ |P(θ)| ≤ 200 sin 2θ` for `0 < α ≤ 1/4`, `θ ∈ (0,π/2)`. -/
lemma fourCosSq_mul_Pfun_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ 200 * Real.sin (2 * θ) := by
  have hθ1 := hθ.1
  have hθ2 := hθ.2
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ1, Real.pi_pos], hθ2⟩
  have hcos2_le : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  rcases le_or_gt θ (1 / 2) with hle | hgt
  · -- small `θ`: `|P| ≤ 30θ²` and `sin 2θ ≥ θ`
    have hP := Pfun_abs_le_sq α hα hα1 (le_of_lt hθ1) hle
    have hstep1 : 4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ 120 * θ ^ 2 := by
      nlinarith [hP, hcos2_le, abs_nonneg (Pfun α θ), sq_nonneg θ]
    have hs2 : θ ≤ Real.sin (2 * θ) := by
      have hms := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ1])
        (by linarith [hle, Real.pi_gt_three])
      have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
      have hthis := mul_le_mul_of_nonneg_right h4 (le_of_lt hθ1)
      rw [one_mul] at hthis
      have hEq : (4 / Real.pi) * θ = 2 / Real.pi * (2 * θ) := by ring
      linarith [hms, hthis, hEq]
    have hstep2 : 120 * θ ^ 2 ≤ 60 * θ := by nlinarith [hle, hθ1]
    linarith [hstep1, hstep2, hs2, hθ1]
  · -- large `θ`: `|P| ≤ 20` and `sin θ ≥ 1/4`
    have hP := Pfun_abs_le α hα hα1 ⟨le_of_lt hθ1, le_of_lt hθ2⟩
    have hsin_ge : (1 : ℝ) / 4 ≤ Real.sin θ := by
      have hms := Real.mul_le_sin (x := (1 : ℝ) / 2) (by norm_num)
        (by linarith [Real.pi_gt_three])
      have hpi4 : (1 : ℝ) / 4 ≤ 2 / Real.pi * (1 / 2) := by
        rw [show 2 / Real.pi * (1 / 2) = 1 / Real.pi from by ring]
        exact one_div_le_one_div_of_le Real.pi_pos (le_of_lt Real.pi_lt_four)
      have hsin_mono : Real.sin (1 / 2) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (le_of_lt hθ2)
          (le_of_lt hgt)
      linarith [hms, hpi4, hsin_mono]
    have hL : 4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ 80 * Real.cos θ := by
      nlinarith [hP, hcos_pos, Real.cos_le_one θ, hcos2_le, abs_nonneg (Pfun α θ)]
    have hR : 100 * Real.cos θ ≤ 200 * Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      nlinarith [hsin_ge, hcos_pos]
    linarith [hL, hR]

/-- The `ZClass` divisibility: `4 cos²θ |D_θ^j P(θ)| ≤ (κ_j/4 + 4 λ_j) sin 2θ`. -/
lemma fourCosSq_mul_dthU_le (j : ℕ) (hj1 : 1 ≤ j) (hj5 : j ≤ 5) (κ ℓ : ℕ → ℝ)
    (hZ : ZClass κ ℓ) (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ (κ j / 4 + 4 * ℓ j) * Real.sin (2 * θ) := by
  have hθ1 := hθ.1
  have hθ2 := hθ.2
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ1, Real.pi_pos], hθ2⟩
  have hcos2_le : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hs_pos : 0 < Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hs_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc_le : Real.cos θ ^ (2 * α / 3) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hcos_pos) (Real.cos_le_one θ) (by linarith [hα])
  have hb := hZ.2.2 α hα hα1 j hj1 hj5 θ hθ
  -- the absorption `α · sin 2θ · cos^{2α/3}θ ≤ 1/4`
  have hkey : α * Real.sin (2 * θ) * Real.cos θ ^ (2 * α / 3) ≤ 1 / 4 := by
    have h1 : α * Real.sin (2 * θ) ≤ 1 / 4 := by
      have := mul_le_mul hα1 hs_le (le_of_lt hs_pos) (by norm_num)
      simpa using this
    have h2 := mul_le_mul h1 hc_le (Real.rpow_nonneg (le_of_lt hcos_pos) _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa using h2
  -- `4 cos²θ · (α sin²θ cos^{2α/3}θ) = (α sin 2θ cos^{2α/3}θ) · sin 2θ`
  have hA : 4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)))
      ≤ (1 / 4) * Real.sin (2 * θ) := by
    have heq : 4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)))
        = (α * Real.sin (2 * θ) * Real.cos θ ^ (2 * α / 3)) * Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hkey (le_of_lt hs_pos)
  have hB : 4 * Real.cos θ ^ 2 * Real.sin (2 * θ) ≤ 4 * Real.sin (2 * θ) := by
    have h4 : 4 * Real.cos θ ^ 2 ≤ 4 := by linarith [hcos2_le]
    exact mul_le_mul_of_nonneg_right h4 (le_of_lt hs_pos)
  have hstep : 4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ 4 * Real.cos θ ^ 2 * (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
          + ℓ j * Real.sin (2 * θ)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hsplit : 4 * Real.cos θ ^ 2 * (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
        + ℓ j * Real.sin (2 * θ))
      = κ j * (4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))))
        + ℓ j * (4 * Real.cos θ ^ 2 * Real.sin (2 * θ)) := by ring
  have hA' : κ j * (4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))))
      ≤ κ j * ((1 / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hA (hZ.1 j)
  have hB' : ℓ j * (4 * Real.cos θ ^ 2 * Real.sin (2 * θ))
      ≤ ℓ j * (4 * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hB (hZ.2.1 j)
  calc 4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ 4 * Real.cos θ ^ 2 * (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
          + ℓ j * Real.sin (2 * θ)) := hstep
    _ = κ j * (4 * Real.cos θ ^ 2 * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))))
        + ℓ j * (4 * Real.cos θ ^ 2 * Real.sin (2 * θ)) := hsplit
    _ ≤ κ j * ((1 / 4) * Real.sin (2 * θ)) + ℓ j * (4 * Real.sin (2 * θ)) := add_le_add hA' hB'
    _ = (κ j / 4 + 4 * ℓ j) * Real.sin (2 * θ) := by ring

theorem fourCosSqBounds :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        4 * Real.cos θ ^ 2 * |Work.FTS.PhiStar.Pfun α θ| ≤ C * Real.sin (2 * θ)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ κ ℓ : ℕ → ℝ, Work.FTS.PhiStar.ZClass κ ℓ → ∀ α : ℝ,
        0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[j] (Work.FTS.PhiStar.Pfun α) θ|
          ≤ (κ j / 4 + 4 * ℓ j) * Real.sin (2 * θ)) :=
  ⟨⟨200, by norm_num, fun α hα hα1 θ hθ => fourCosSq_mul_Pfun_le α θ hα hα1 hθ⟩,
   fun j hj1 hj5 κ ℓ hZ α hα hα1 θ hθ =>
     fourCosSq_mul_dthU_le j hj1 hj5 κ ℓ hZ α θ hα hα1 hθ⟩

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The two measures on the quadrant -/

/-- `(0, π/2)` and `Iθ` carry the same restricted Lebesgue measure. -/
theorem restrict_Ioo_eq_Iθ :
    (volume.restrict (Set.Ioo 0 (π / 2)) : Measure ℝ) = volume.restrict Work.Spaces.Iθ := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [Work.Spaces.Iθ, ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]
  · rw [Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)

/-- The restricted measure of the quadrant is the product of the two restricted one-dimensional
measures. -/
theorem restrict_Q0_eq_prod :
    (volume.restrict Work.FTS.EllipticEst.Q0 : Measure (ℝ × ℝ))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
  rw [Work.FTS.EllipticEst.Q0, MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.Measure.prod_restrict]

/-! ## Integrability against the box indicator -/

theorem continuousOn_absPhi_mode {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => |Φ p.1 p.2|) Work.FTS.EllipticEst.Q0 :=
  ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr hsm).continuousOn.abs

/-- **Product-measure integrability of `|Φ|` against a box indicator in `z`.** -/
theorem integrableOn_absPhi_box {Φ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) Work.FTS.EllipticEst.Q0 := by
  rw [MeasureTheory.IntegrableOn, restrict_Q0_eq_prod]
  refine (MeasureTheory.integrable_prod_iff ?_).mpr ⟨?_, ?_⟩
  · -- a.e. strong measurability
    have hcont := (continuousOn_absPhi_mode hsm).aestronglyMeasurable
      (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    rw [← restrict_Q0_eq_prod]
    exact hcont.mul (Measurable.aestronglyMeasurable
      (measurable_const.indicator measurableSet_Icc |>.comp measurable_fst))
  · -- the per-slice integrability
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
    have h1 := (hΦint z hz).integrable
    rw [← restrict_Ioo_eq_Iθ] at h1
    have h2 := h1.const_mul ((Set.Icc a b).indicator (fun _ => (1 : ℝ)) z)
    refine h2.congr (Eventually.of_forall fun y => ?_)
    show (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * |Φ z y|
      = |Φ z y| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
    ring
  · -- the outer integrability
    have hEq : (fun z : ℝ => ∫ θ, ‖|Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z‖
          ∂((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))))
        = fun z => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
            * ∫ θ in Work.Spaces.Iθ, |Φ z θ| := by
      funext z
      rw [show (fun θ => ‖|Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z‖)
          = fun θ => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * |Φ z θ| from by
        funext θ
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (indicator_one_nonneg z), abs_abs, mul_comm]]
      rw [MeasureTheory.integral_const_mul, ← restrict_Ioo_eq_Iθ]
    rw [hEq]
    have h3 : MeasureTheory.Integrable ((Set.Icc a b).indicator
        (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)) volume :=
      hEint.integrable_indicator measurableSet_Icc
    have h4 : MeasureTheory.Integrable ((Set.Icc a b).indicator
        (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)) (volume.restrict (Set.Ioi 0)) :=
      h3.mono_measure MeasureTheory.Measure.restrict_le_self
    refine h4.congr (Eventually.of_forall fun z => ?_)
    show (Set.Icc a b).indicator (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) z
      = (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
        * ∫ θ in Work.Spaces.Iθ, |Φ z θ|
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hz : z ∈ Set.Icc a b <;> simp [hz]

/-! ## Derivatives of a function vanishing near a point -/

/-- If `f` vanishes in a neighbourhood of `z`, then so do its first two derivatives at `z`. -/
theorem deriv_deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] 0) :
    deriv f z = 0 ∧ deriv (deriv f) z = 0 := by
  obtain ⟨V, hVf, hVopen, hzV⟩ := mem_nhds_iff.mp h
  have hVeq : f =ᶠ[𝓝 z] (fun _ => 0) := Filter.mem_of_superset (hVopen.mem_nhds hzV) hVf
  have h1 : deriv f z = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hVeq]
    simp
  have hd : deriv f =ᶠ[𝓝 z] (fun _ : ℝ => 0) := by
    filter_upwards [hVopen.mem_nhds hzV] with y hy
    have hyeq : f =ᶠ[𝓝 y] (fun _ => 0) := Filter.mem_of_superset (hVopen.mem_nhds hy) hVf
    rw [Filter.EventuallyEq.deriv_eq hyeq]
    simp
  have h2 : deriv (deriv f) z = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hd]
    simp
  exact ⟨h1, h2⟩

/-! ## The pointwise bounds on the two factors of the mode integrand -/

/-- A bound on the Dirichlet eigenfunction on `Iθ`. -/
theorem exists_bound_eFam (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Work.FTS.ClassC.contDiff_eFam_nat m 0).continuous.continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h2 := hC θ hθ
  rw [Real.norm_eq_abs] at h2
  exact h2.trans (le_max_left _ _)

/-- The mode coefficient of `ρ` is bounded by a constant times the box indicator (it vanishes off
the support of `ρ`). -/
theorem exists_bound_modeCoef {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ)
    {a b : ℝ} (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ,
      |Work.FTS.PhiStar.Gegenbauer.lam m * ρ z - radOp α ρ z|
        ≤ C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z := by
  have hd1 : Continuous (deriv ρ) := (hρ 2).continuous_deriv (by norm_num)
  have hd2 : Continuous (deriv (deriv ρ)) := by
    have h := (hρ 2).continuous_iteratedDeriv' 2
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h
  have hc : Continuous (fun z : ℝ => Work.FTS.PhiStar.Gegenbauer.lam m * ρ z - radOp α ρ z) := by
    change Continuous (fun z : ℝ => Work.FTS.PhiStar.Gegenbauer.lam m * ρ z
      - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))
    exact (continuous_const.mul (hρ 0).continuous).sub
      (((continuous_const.mul (continuous_id.pow 2)).mul hd2).add
        ((continuous_const.mul continuous_id).mul hd1))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · rw [Set.indicator_of_mem hz, mul_one]
    have h2 := hC z hz
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hz, mul_zero]
    have hev : ρ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hz (hsub h)
    obtain ⟨h1, h2⟩ := deriv_deriv_eq_zero_of_eventuallyEq_zero hev
    have hρz : ρ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hsub h)
    simp only [radOp, hρz, h1, h2, mul_zero]
    norm_num

/-- **The bound on `bslOp α (ρ ⊗ e_m)`**: a constant times the box indicator in `z`. -/
theorem exists_bound_bslOp_Psi {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ)
    {a b : ℝ} (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          p.1 p.2| ≤ B * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_modeCoef (α := α) hρ hsub
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_eFam m
  refine ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, fun p hp => ?_⟩
  have hcos : Real.cos p.2 ≠ 0 := by
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  rw [bslOp_sepMode (α := α) hcos, abs_mul]
  calc |Work.FTS.PhiStar.Gegenbauer.lam m * ρ p.1 - radOp α ρ p.1|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m p.2|
      ≤ (C₁ * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) * C₂ := by
        refine mul_le_mul (hC₁ p.1) ?_ (abs_nonneg _)
          (mul_nonneg hC₁0 (indicator_one_nonneg p.1))
        exact hC₂ p.2 ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp).2.1.le,
          (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2.le⟩
    _ = C₁ * C₂ * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by ring

/-- **The product bound**: `|bslOp α (ρ ⊗ e_m)| · |wgt|` is bounded by a constant times the box
indicator (both factors vanish off the support box, and are bounded on it). -/
theorem abs_bslOp_mul_bslWeight_le {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ} (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          p.1 p.2| * |bslWeight α p|
        ≤ C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_bslOp_Psi (α := α) hρ hsub
  obtain ⟨W, hW0, hW⟩ := exists_bound_bslWeight (α := α) ha
  obtain ⟨C₁, -, hC₁⟩ := exists_bound_modeCoef (α := α) hρ hsub
  refine ⟨B * W, mul_nonneg hB0 hW0, fun p hp => ?_⟩
  by_cases hpI : p.1 ∈ Set.Icc a b
  · have h1 : |Work.Elliptic.bslOp α (fun z θ => ρ z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| ≤ B := by
      have h := hB p hp
      rwa [Set.indicator_of_mem hpI, mul_one] at h
    have h2 : |bslWeight α p| ≤ W := hW p hpI
    calc |Work.Elliptic.bslOp α (fun z θ => ρ z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| * |bslWeight α p|
        ≤ B * W := mul_le_mul h1 h2 (abs_nonneg _) hB0
      _ = B * W * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
          rw [Set.indicator_of_mem hpI, mul_one]
  · have hcos : Real.cos p.2 ≠ 0 := by
      obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
    have hz0 : |Work.FTS.PhiStar.Gegenbauer.lam m * ρ p.1 - radOp α ρ p.1| = 0 := by
      have h := hC₁ p.1
      rw [Set.indicator_of_notMem hpI, mul_zero] at h
      exact le_antisymm h (abs_nonneg _)
    rw [bslOp_sepMode (α := α) hcos, abs_mul, hz0, Set.indicator_of_notMem hpI]
    simp

/-- The weight against the box indicator is bounded by a constant times the indicator. -/
theorem abs_bslWeight_mul_indicator_le {α : ℝ} {a b : ℝ} (ha : 0 < a) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ p : ℝ × ℝ,
      |bslWeight α p| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
        ≤ W * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 := by
  obtain ⟨W, hW0, hW⟩ := exists_bound_bslWeight (α := α) ha
  refine ⟨W, hW0, fun p => ?_⟩
  by_cases hp : p.1 ∈ Set.Icc a b
  · simp only [Set.indicator_of_mem hp, mul_one]
    exact hW p hp
  · simp only [Set.indicator_of_notMem hp, mul_zero, le_refl]

/-! ## Integrability of the mode integrand -/

/-- **Product-measure integrability of the un-cut mode integrand**
`Φ·(bslOp (ρ ⊗ e_m))·z^((5-α)/α)cos θ`. -/
theorem integrableOn_modeIntegrand {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ} (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b)
    (hbox : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => |Φ p.1 p.2|
      * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * bslWeight α p) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨C, hC0, hC⟩ := abs_bslOp_mul_bslWeight_le (α := α) hρ ha hsub
  have hψ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun k =>
      ((Work.FTS.ClassC.contDiffOn_uncurry_fst (s := Set.Ioi 0)
          (t := Set.Ioo 0 (π / 2)) ((hρ k).contDiffOn)).mul
        (Work.FTS.ClassC.contDiffOn_uncurry_snd (s := Set.Ioi 0)
          (t := Set.Ioo 0 (π / 2)) (Work.FTS.ClassC.contDiff_eFam_nat m k)))
  refine Integrable.mono' (hbox.const_mul C) ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2)
        (volume.restrict Work.FTS.EllipticEst.Q0) :=
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr hsm).continuousOn.aestronglyMeasurable
        (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2)
        (volume.restrict Work.FTS.EllipticEst.Q0) :=
      (continuousOn_bslOp_of_smoothOpen hψ).aestronglyMeasurable
        (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => bslWeight α p)
        (volume.restrict Work.FTS.EllipticEst.Q0) :=
      (continuousOn_weight α).aestronglyMeasurable
        (μ := volume) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact (h1.mul h2).mul h3
  · refine MeasureTheory.ae_restrict_of_forall_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet fun p hp => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |Φ p.1 p.2| * |Work.Elliptic.bslOp α (fun z θ => ρ z *
          Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| * |bslWeight α p|
        = |Φ p.1 p.2| * (|Work.Elliptic.bslOp α (fun z θ => ρ z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2| * |bslWeight α p|) := by ring
      _ ≤ |Φ p.1 p.2| * (C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) :=
          mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg _)
      _ = C * (|Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) := by ring

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

set_option maxHeartbeats 1600000

/-! ## Product rule and linearity for `D_z` and `D_θ`

These are the pointwise derivatives of the two operators; the differentiability
hypotheses are the slices of the factors at the point under consideration. -/


private lemma cd6_Dz_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ) := by
  show z * deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
      = cc * (z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z))
  rw [show deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
        = deriv (fun y => cc * ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) y) z from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma cd6_Dz_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => A i z' θ) z) :
    Work.Spaces.Dz (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dz (A i) z θ := by
  have hfun : (fun z' : ℝ => ∑ i ∈ s, A i z' θ) = (∑ i ∈ s, fun z' : ℝ => A i z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  show z * deriv (fun z' : ℝ => ∑ i ∈ s, A i z' θ) z
      = ∑ i ∈ s, z * deriv (fun z' : ℝ => A i z' θ) z
  rw [hfun, deriv_sum h, Finset.mul_sum]


private lemma cd6_Dth_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ) := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
      = cc * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ))
  rw [show deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
        = deriv (fun y => cc * ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) y) θ from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma cd6_Dth_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => A i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (A i) z θ := by
  have hfun : (fun θ' : ℝ => ∑ i ∈ s, A i z θ') = (∑ i ∈ s, fun θ' : ℝ => A i z θ') := by
    funext θ'
    rw [Finset.sum_apply]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => ∑ i ∈ s, A i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' : ℝ => A i z θ') θ
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma cd6_differentiableAt_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {z : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) z) :
    DifferentiableAt ℝ (fun z' => ∑ i ∈ s, A i z') z := by
  have hfun : (fun z' => ∑ i ∈ s, A i z') = (∑ i ∈ s, A i) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

private lemma cd6_differentiableAt_sum_θ {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) θ) :
    DifferentiableAt ℝ (fun θ' => ∑ i ∈ s, A i θ') θ := by
  have hfun : (fun θ' => ∑ i ∈ s, A i θ') = (∑ i ∈ s, A i) := by
    funext θ'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

/-! ## Congruence of `D_z` and `D_θ` under eventual equality of a slice

This is what makes the induction work in the local setting: the induction hypothesis is
available at *every* point of the open quadrant, hence on a whole slice through the
point under consideration, and `deriv` only sees an eventual equality
(`Filter.EventuallyEq.deriv_eq`, which needs no differentiability hypothesis). -/

private lemma cd6_Dz_congr {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun z' => u z' θ) =ᶠ[𝓝 z] (fun z' => v z' θ)) :
    Work.Spaces.Dz u z θ = Work.Spaces.Dz v z θ := by
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [Filter.EventuallyEq.deriv_eq h]

private lemma cd6_Dth_congr {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun θ' => u z θ') =ᶠ[𝓝 θ] (fun θ' => v z θ')) :
    Work.Spaces.Dth u z θ = Work.Spaces.Dth v z θ := by
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [Filter.EventuallyEq.deriv_eq h]

/-! ## The slices of the open quadrant through a point -/

private lemma cd6_zslice_mem {z θ : ℝ} (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    {z' : ℝ | (z', θ) ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 z := by
  have hset : {z' : ℝ | (z', θ) ∈ Work.FTS.EllipticEst.Q0} = Set.Ioi 0 := by
    ext z'
    rw [Set.mem_ofPred_eq, Work.FTS.EllipticEst.mem_Q0, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, hp.2.1, hp.2.2⟩⟩
  rw [hset]; exact isOpen_Ioi.mem_nhds hp.1

private lemma cd6_θslice_mem {z θ : ℝ} (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    {θ' : ℝ | (z, θ') ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 θ := by
  have hset : {θ' : ℝ | (z, θ') ∈ Work.FTS.EllipticEst.Q0} = Set.Ioo 0 (π / 2) := by
    ext θ'
    rw [Set.mem_ofPred_eq, Work.FTS.EllipticEst.mem_Q0, Set.mem_Ioo]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hp.1, h.1, h.2⟩⟩
  rw [hset]; exact isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩

/-! ## The Leibniz rule -/

theorem mixedMul_cd6 {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ a b : ℕ, a + b ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) *
            (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
  have hQ0 : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  -- The mixed blocks of total order `≤ 5` have differentiable slices at every point of `Q0`.
  have hfz : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j f z' θ) z := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hf
    exact Work.Spaces.differentiableAt_slice_fst
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have hfθ : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j f z θ') θ := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hf
    exact Work.Spaces.differentiableAt_slice_snd
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have hgz : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j g z' θ) z := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hg
    exact Work.Spaces.differentiableAt_slice_fst
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have hgθ : ∀ i j : ℕ, i + j ≤ 5 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j g z θ') θ := by
    intro i j hij z θ hp
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      (n := 6) hQ0 j i 1 (by omega) hg
    exact Work.Spaces.differentiableAt_slice_snd
      ((h1.contDiffAt (hQ0.mem_nhds hp)).differentiableAt (by norm_num))
  have key : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → a + b ≤ 6 →
      ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) *
            (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
    intro n
    induction n with
    | zero =>
        intro a b hsum h6 z θ hp
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha
        subst hb
        simp [Work.Spaces.mixed]
    | succ n ih =>
        intro a b hsum h6 z θ hp
        rcases Nat.eq_zero_or_pos a with ha | ha
        · -- `a = 0`: differentiate in `θ`
          subst ha
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb
            simp [Work.Spaces.mixed]
          · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            have hs : 0 + b' ≤ n := by omega
            have h6' : 0 + b' ≤ 6 := by omega
            have hslice := cd6_θslice_mem (z := z) (θ := θ) hp
            have hL : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ) z θ
                = Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                    ∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ := by
              have h1 : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ)
                  = Work.Spaces.Dth (Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ)) := by
                simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero]
              rw [h1]
              apply cd6_Dth_congr
              exact Filter.eventually_of_mem hslice (fun θ' hθ' => ih 0 b' hs h6' z θ' hθ')
            rw [hL]
            have hstep1 : Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                  ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) z θ
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i (j + 1) f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ) := by
              rw [cd6_Dth_sum (Finset.range (0 + 1))
                    (fun i z θ => ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun i hi => cd6_differentiableAt_sum_θ (Finset.range (b' + 1))
                      (fun j θ' => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ' * Work.Spaces.mixed (0 - i) (b' - j) g z θ'))
                      (fun j hj => ((hfθ i j (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hp).mul
                        (hgθ (0 - i) (b' - j) (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ hp)).const_mul _))]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [cd6_Dth_sum (Finset.range (b' + 1))
                    (fun j z θ => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun j hj => ((hfθ i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp).mul
                      (hgθ (0 - i) (b' - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp)).const_mul _)]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hi0 : i = 0 := by have := Finset.mem_range.mp hi; omega
              rw [cd6_Dth_cmul (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ))
                    (hfθ i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp)
                    (hgθ (0 - i) (b' - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp)]
              rw [show Work.Spaces.Dth (Work.Spaces.mixed i j f) z θ
                    = Work.Spaces.mixed i (j + 1) f z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero],
                  show Work.Spaces.Dth (Work.Spaces.mixed (0 - i) (b' - j) g) z θ
                    = Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero, Nat.sub_zero]]
            have hstep2 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1 + 1),
                    (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              have h1 : (∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                  = ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1), (b'.choose j : ℝ) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              rw [h1, Work.Spaces.leibniz_step b' (fun j => Work.Spaces.mixed i j f z θ)
                    (fun m => Work.Spaces.mixed (0 - i) m g z θ)]
              have h2 : ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1 + 1),
                    ((b' + 1).choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ))
                  = ∑ j ∈ Finset.range (b' + 1 + 1),
                      (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              exact h2
            rw [hstep1, hstep2]
        · -- `a ≥ 1`: differentiate in `z`
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hs : a' + b ≤ n := by omega
          have h6' : a' + b ≤ 6 := by omega
          have hslice := cd6_zslice_mem (z := z) (θ := θ) hp
          have hL : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ) z θ
              = Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                  ∑ j ∈ Finset.range (b + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ := by
            have h1 : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ)
                = Work.Spaces.Dz (Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ)) := by
              simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
            rw [h1]
            apply cd6_Dz_congr
            exact Filter.eventually_of_mem hslice (fun z' hz' => ih a' b hs h6' z' θ hz')
          rw [hL]
          have hstep1 : Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ)) z θ
              = ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed (i + 1) j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ
                    + Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ) := by
            rw [cd6_Dz_sum (Finset.range (a' + 1))
                  (fun i z θ => ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun i hi => cd6_differentiableAt_sum (Finset.range (b + 1))
                    (fun j z' => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z' θ * Work.Spaces.mixed (a' - i) (b - j) g z' θ))
                    (fun j hj => ((hfz i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp).mul
                      (hgz (a' - i) (b - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ hp)).const_mul _))]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [cd6_Dz_sum (Finset.range (b + 1))
                  (fun j z θ => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun j hj => ((hfz i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp).mul
                    (hgz (a' - i) (b - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ hp)).const_mul _)]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [cd6_Dz_cmul ((a'.choose i : ℝ) * (b.choose j : ℝ))
                  (hfz i j (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hp)
                  (hgz (a' - i) (b - j) (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ hp)]
            rw [show Work.Spaces.Dz (Work.Spaces.mixed i j f) z θ
                  = Work.Spaces.mixed (i + 1) j f z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ],
                show Work.Spaces.Dz (Work.Spaces.mixed (a' - i) (b - j) g) z θ
                  = Work.Spaces.mixed (a' - i + 1) (b - j) g z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]]
          have hstep2 : (∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
              = ∑ i ∈ Finset.range (a' + 1 + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
            have hkey1 := Finset.sum_comm (s := Finset.range (a' + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                (Work.Spaces.mixed (i + 1) j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ
                  + Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
            have hkey2 := Finset.sum_comm (s := Finset.range (a' + 1 + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                (Work.Spaces.mixed i j f z θ
                  * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
            rw [hkey1, hkey2]
            refine Finset.sum_congr rfl fun j hj => ?_
            have h1 : (∑ i ∈ Finset.range (a' + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
                = (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1), (a'.choose i : ℝ) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [h1, Work.Spaces.leibniz_step a' (fun i => Work.Spaces.mixed i j f z θ)
                  (fun m => Work.Spaces.mixed m (b - j) g z θ)]
            have h2 : (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1 + 1),
                  ((a' + 1).choose i : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
                = ∑ i ∈ Finset.range (a' + 1 + 1),
                    ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            exact h2
          rw [hstep1, hstep2]
  intro a b hab z θ hz hθ0 hθ1
  exact key (a + b) a b le_rfl hab z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.bcoefPoint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## E. The pointwise bound for the `ℋ³`-integrand -/

/-- The sum of the squares of the weighted `D_z`-iterates of the radial profile. -/
def radSnorm (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 4, ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2

/-- The radial part of the constant, chosen large enough for the termwise bounds. -/
def radC0 : ℝ := max 400 (25600 * radTB ^ 2)

/-- The angular integrand whose integral bounds the angular part. -/
def radAngInt (α : ℝ) (θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The pointwise majorant of the `ℋ³`-integrand. -/
def radAMaj (α : ℝ) (θ : ℝ) : ℝ := 16 * radC0 * radAngInt α θ

/-! ## Unfolding lemmas for the four definitions above -/

lemma radSnorm_apply (z : ℝ) :
    radSnorm z = ∑ j ∈ Finset.range 4,
      ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 := rfl


lemma radAngInt_apply (α θ : ℝ) :
    radAngInt α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl


lemma sq_le_radSnorm {z : ℝ} {j : ℕ} (hj : j ≤ 3) :
    ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ radSnorm z :=
  Finset.single_le_sum (f := fun j : ℕ => ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))

lemma radSnorm_nonneg (z : ℝ) : 0 ≤ radSnorm z :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma radSnorm_zero : radSnorm 0 = 0 := by
  rw [radSnorm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Work.Spaces.w]
  norm_num

lemma radC0_ge_hundred : (100 : ℝ) ≤ radC0 := le_trans (by norm_num) (le_max_left _ _)

lemma radC0_ge_radTB : 100 * radTB ^ 2 ≤ radC0 :=
  le_trans (by nlinarith [sq_nonneg radTB]) (le_max_right _ _)

lemma radC0_nonneg : 0 ≤ radC0 := le_trans (by norm_num) radC0_ge_hundred

lemma radAngInt_nonneg {α θ : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) : 0 ≤ radAngInt α θ := by
  rw [radAngInt]
  refine add_nonneg (Real.rpow_nonneg hs _) ?_
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)

/-- The pure `D_z`-family summand of the `ℋ³`-integrand. -/
lemma term_A_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) (hi : i ≤ 3) :
    (Work.Spaces.DzIter i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hdz : Work.Spaces.DzIter i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
      = gamCoefAng α θ * (Work.Spaces.Zop^[i] bcoefRad) z := by
    rw [DzIter_ang_rad i bcoefRad (gamCoefAng α)]
  rw [hdz]
  have hkey : (gamCoefAng α θ * (Work.Spaces.Zop^[i] bcoefRad) z
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (gamCoefAng α θ) ^ 2 * (((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    rw [show gamCoefAng α θ * (Work.Spaces.Zop^[i] bcoefRad) z
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = gamCoefAng α θ * (((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z)
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) from by ring]
    rw [mul_pow, div_sin_eta_sq _ hs]
  rw [hkey]
  have h1 : (gamCoefAng α θ) ^ 2 ≤ 100 := gamCoefAng_sq_le hα hα1 hθ
  have h2 : ((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ radSnorm z :=
    sq_le_radSnorm (by omega)
  have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
  have h4 : 0 ≤ radSnorm z := radSnorm_nonneg z
  have h5 : (100 : ℝ) ≤ radC0 := radC0_ge_hundred
  calc (gamCoefAng α θ) ^ 2 * (((Work.Spaces.Zop^[i] bcoefRad) z * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 100 * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 h3) (mul_nonneg (sq_nonneg _) h3)
          (by norm_num)
    _ ≤ radC0 * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right h5 (mul_nonneg h4 h3)
    _ = radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring

/-- The mixed summand of the `ℋ³`-integrand. -/
lemma term_B_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ)
    (i j : ℕ) :
    (if 1 ≤ i ∧ i + j ≤ 3 then
        (Work.Spaces.mixed j i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0)
      ≤ radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  by_cases hp : 1 ≤ i ∧ i + j ≤ 3
  · rw [if_pos hp]
    have hi1 : 1 ≤ i := hp.1
    have hi3 : i ≤ 3 := by omega
    have hj3 : j ≤ 3 := by omega
    have hmix : Work.Spaces.mixed j i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
        = (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) * (Work.Spaces.Zop^[j] bcoefRad) z := by
      rw [mixed_ang_rad j i bcoefRad (gamCoefAng α)]
    rw [hmix]
    have hWt := Wt_sq_of_nonneg (α := α) (z := z) (θ := θ) hα hs
    have hkey : ((Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ
          * (Work.Spaces.Zop^[j] bcoefRad) z) * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
          * (((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      rw [mul_pow, hWt]
      ring
    rw [hkey]
    have h1 : (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
        ≤ 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) :=
      dthU_gamCoefAng_sq_le hα hα1 hθ hi1 hi3
    have h2 : ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ radSnorm z := sq_le_radSnorm hj3
    have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs _
    have h4 : 0 ≤ radSnorm z := radSnorm_nonneg z
    have h5 : 0 ≤ 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg radTB)) (mul_nonneg (sq_nonneg α) (sq_nonneg _))
    have h6 : 100 * radTB ^ 2 ≤ radC0 := radC0_ge_radTB
    have h7 : 0 ≤ α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (radSnorm z
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
      mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg _)) (mul_nonneg h4 h3)
    calc (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
          * (((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ (100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2)) * (radSnorm z
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 h3) (mul_nonneg (sq_nonneg _) h3) h5
      _ ≤ radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
          calc (100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2)) * (radSnorm z
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              = (100 * radTB ^ 2) * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
            _ ≤ radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (radSnorm z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
                mul_le_mul_of_nonneg_right h6 h7
      _ = radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by ring
  · rw [if_neg hp]
    refine mul_nonneg (radSnorm_nonneg z) ?_
    exact mul_nonneg radC0_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg hs _))

/-- **The pointwise bound for the `ℋ³`-integrand of the projector coefficient.** -/
lemma hkIntegrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) z θ ≤ radSnorm z * radAMaj α θ := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst, radSnorm_zero, zero_mul]
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 3 _ z θ hsin]
    have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
      rw [hsin, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
    have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) = 0 := by
      rw [hsin, Real.zero_rpow (by rw [Work.Spaces.gam]; intro h; linarith)]
    have h0 : radSnorm z * radAMaj α θ = 0 := by
      rw [radAMaj, radAngInt, h1, h2]; ring
    rw [h0]
  · have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
    have hSsum : (∑ i ∈ Finset.range 4,
          (Work.Spaces.DzIter i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 4,
            radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
      Finset.sum_le_sum fun i hi => term_A_le hα hα1 hθ i
        (by have := Finset.mem_range.mp hi; omega)
    have hMsum : (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          if 1 ≤ i ∧ i + j ≤ 3 then
            (Work.Spaces.mixed j i (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range 4, ∑ _j ∈ Finset.range 4,
            radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => term_B_le hα hα1 hθ i j
    rw [Work.Spaces.HkIntegrand]
    refine le_trans (add_le_add hSsum hMsum) ?_
    have hAe : (∑ _i ∈ Finset.range 4,
          radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        = 4 * (radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have hMe : (∑ _i ∈ Finset.range 4, ∑ _j ∈ Finset.range 4,
          radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
        = 16 * (radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hAe, hMe, radAMaj, radAngInt]
    have hA0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
    have hB0 : 0 ≤ α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)
    have hS0 : 0 ≤ radSnorm z := radSnorm_nonneg z
    have hradC0 : 0 ≤ radC0 := radC0_nonneg
    have hkey : radSnorm z * (16 * radC0 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          - (4 * (radSnorm z * (radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
            + 16 * (radSnorm z * (radC0 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))))
        = 12 * (radSnorm z * radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    have hnn : 0 ≤ 12 * (radSnorm z * radC0 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hS0 hradC0) hA0)
    linarith [hkey, hnn]


end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary bounds for monic polynomials on `z ≥ 0` -/

lemma abs_le_lin (z b : ℝ) (hz : 0 ≤ z) : |z + b| ≤ (1 + |b|) * (1 + z) := by
  have h1 : |z| ≤ 1 + z := by rw [abs_of_nonneg hz]; linarith
  have h2 : (1 : ℝ) ≤ 1 + z := by linarith
  have hb : |b| ≤ |b| * (1 + z) := by
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
    linarith
  calc |z + b| ≤ |z| + |b| := abs_add_le _ _
    _ ≤ (1 + |b|) * (1 + z) := by linarith

lemma abs_le_quad (z b c : ℝ) (hz : 0 ≤ z) :
    |z ^ 2 + b * z + c| ≤ (1 + |b| + |c|) * (1 + z) ^ 2 := by
  have hz' : |z| = z := abs_of_nonneg hz
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have h2 : (1 : ℝ) ≤ (1 + z) ^ 2 := one_le_pow₀ h1z
  have hz2 : |z| ^ 2 ≤ (1 + z) ^ 2 := by
    rw [hz']; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hz1 : |z| ≤ (1 + z) ^ 2 := by rw [hz']; nlinarith
  have h3 : |z ^ 2 + b * z + c| ≤ |z ^ 2| + |b * z| + |c| := by
    have h := abs_add_le (z ^ 2 + b * z) c
    have h' := abs_add_le (z ^ 2) (b * z)
    linarith
  have h4 : |z ^ 2| + |b * z| + |c| = |z| ^ 2 + |b| * |z| + |c| := by
    rw [abs_pow, abs_mul]
  have hb : |b| * |z| ≤ |b| * (1 + z) ^ 2 := mul_le_mul_of_nonneg_left hz1 (abs_nonneg b)
  have hc : |c| ≤ |c| * (1 + z) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
    linarith
  have hmain : |z| ^ 2 + |b| * |z| + |c| ≤ (1 + |b| + |c|) * (1 + z) ^ 2 := by
    nlinarith [hz2, hb, hc, h2, abs_nonneg b, abs_nonneg c]
  calc |z ^ 2 + b * z + c| ≤ |z ^ 2| + |b * z| + |c| := h3
    _ = |z| ^ 2 + |b| * |z| + |c| := h4
    _ ≤ (1 + |b| + |c|) * (1 + z) ^ 2 := hmain

lemma abs_le_cubic (z b c d : ℝ) (hz : 0 ≤ z) :
    |z ^ 3 + b * z ^ 2 + c * z + d| ≤ (1 + |b| + |c| + |d|) * (1 + z) ^ 3 := by
  have hz' : |z| = z := abs_of_nonneg hz
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have h3 : (1 : ℝ) ≤ (1 + z) ^ 3 := one_le_pow₀ h1z
  have hz3 : |z| ^ 3 ≤ (1 + z) ^ 3 := by
    rw [hz']; exact pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hz2 : |z| ^ 2 ≤ (1 + z) ^ 3 := by
    rw [hz']
    have h : z ^ 2 ≤ (1 + z) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h' : (1 + z) ^ 2 ≤ (1 + z) ^ 3 := by nlinarith [h3, h1z]
    linarith
  have hz1 : |z| ≤ (1 + z) ^ 3 := by rw [hz']; nlinarith [h3, hz]
  have h5 : |z ^ 3 + b * z ^ 2 + c * z + d|
      ≤ |z ^ 3| + |b * z ^ 2| + |c * z| + |d| := by
    have h := abs_add_le (z ^ 3 + b * z ^ 2 + c * z) d
    have h' := abs_add_le (z ^ 3 + b * z ^ 2) (c * z)
    have h'' := abs_add_le (z ^ 3) (b * z ^ 2)
    linarith
  have h6 : |z ^ 3| + |b * z ^ 2| + |c * z| + |d|
      = |z| ^ 3 + |b| * |z| ^ 2 + |c| * |z| + |d| := by
    rw [abs_pow, abs_mul, abs_pow, abs_mul]
  have hb : |b| * |z| ^ 2 ≤ |b| * (1 + z) ^ 3 := mul_le_mul_of_nonneg_left hz2 (abs_nonneg b)
  have hc : |c| * |z| ≤ |c| * (1 + z) ^ 3 := mul_le_mul_of_nonneg_left hz1 (abs_nonneg c)
  have hd : |d| ≤ |d| * (1 + z) ^ 3 := by
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg d)
    linarith
  have hmain : |z| ^ 3 + |b| * |z| ^ 2 + |c| * |z| + |d|
      ≤ (1 + |b| + |c| + |d|) * (1 + z) ^ 3 := by
    nlinarith [hz3, hb, hc, hd, h3, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  calc |z ^ 3 + b * z ^ 2 + c * z + d| ≤ |z ^ 3| + |b * z ^ 2| + |c * z| + |d| := h5
    _ = |z| ^ 3 + |b| * |z| ^ 2 + |c| * |z| + |d| := h6
    _ ≤ (1 + |b| + |c| + |d|) * (1 + z) ^ 3 := hmain

/-! ## The derivatives of the rational profiles -/

lemma deriv1 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 / (1 + y) ^ 3) (2 * z * (2 - z) / (1 + z) ^ 4) z := by
  have hdenne : (1 + z) ^ 3 ≠ 0 := by
    intro h
    exact hz (by have := pow_eq_zero_iff (by norm_num : 3 ≠ 0) |>.mp h; linarith)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * z) z := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := (hasDerivAt_id z).pow 2
      have hfun : (id : ℝ → ℝ) ^ 2 = fun y : ℝ => y ^ 2 := by funext y; simp
      rw [hfun] at h
      convert h using 1
      simp
    have h2 := h1.const_mul (2 : ℝ)
    convert h2 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 3) (3 * (1 + z) ^ 2) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h1.pow 3
    have hfun : ((fun y : ℝ => 1 + y) ^ 3) = fun y : ℝ => (1 + y) ^ 3 := by funext y; simp
    rw [hfun] at h2
    convert h2 using 1
    ring
  have h := hnum.div hden hdenne
  have hval : (4 * z * (1 + z) ^ 3 - 2 * z ^ 2 * (3 * (1 + z) ^ 2)) / ((1 + z) ^ 3) ^ 2
      = 2 * z * (2 - z) / (1 + z) ^ 4 := by
    field_simp
    ring
  rw [hval] at h
  exact h

lemma deriv2 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (2 - y) / (1 + y) ^ 4)
      (2 * z * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5) z := by
  have hdenne : (1 + z) ^ 4 ≠ 0 := by
    intro h
    exact hz (by have := pow_eq_zero_iff (by norm_num : 4 ≠ 0) |>.mp h; linarith)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (2 - y)) (8 * z - 6 * z ^ 2) z := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := (hasDerivAt_id z).pow 2
      have hfun : (id : ℝ → ℝ) ^ 2 = fun y : ℝ => y ^ 2 := by funext y; simp
      rw [hfun] at h
      convert h using 1
      simp
    have h2 := h1.const_mul (2 : ℝ)
    have h3 : HasDerivAt (fun y : ℝ => 2 - y) (-1) z := by
      have h := (hasDerivAt_const (x := z) (2 : ℝ)).sub (hasDerivAt_id z)
      have hf : ((fun _ : ℝ => (2 : ℝ)) - id) = fun y : ℝ => 2 - y := by
        funext y; simp
      rw [hf] at h
      convert h using 1
      ring
    have h4 := h2.mul h3
    convert h4 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + z) ^ 3) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h1.pow 4
    have hfun : ((fun y : ℝ => 1 + y) ^ 4) = fun y : ℝ => (1 + y) ^ 4 := by funext y; simp
    rw [hfun] at h2
    convert h2 using 1
    ring
  have h := hnum.div hden hdenne
  have hval : ((8 * z - 6 * z ^ 2) * (1 + z) ^ 4 - 2 * z ^ 2 * (2 - z) * (4 * (1 + z) ^ 3))
        / ((1 + z) ^ 4) ^ 2 = 2 * z * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
    field_simp
    ring
  rw [hval] at h
  exact h

lemma deriv3 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 2 - 7 * y + 4) / (1 + y) ^ 5)
      (2 * z * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6) z := by
  have hdenne : (1 + z) ^ 5 ≠ 0 := by
    intro h
    exact hz (by have := pow_eq_zero_iff (by norm_num : 5 ≠ 0) |>.mp h; linarith)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 2 - 7 * y + 4))
      (8 * z ^ 3 - 42 * z ^ 2 + 16 * z) z := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := (hasDerivAt_id z).pow 2
      have hfun : (id : ℝ → ℝ) ^ 2 = fun y : ℝ => y ^ 2 := by funext y; simp
      rw [hfun] at h
      convert h using 1
      simp
    have h2 := h1.const_mul (2 : ℝ)
    have hq : HasDerivAt (fun y : ℝ => y ^ 2 - 7 * y + 4) (2 * z - 7) z := by
      have h3 : HasDerivAt (fun y : ℝ => y ^ 2 - 7 * y) (2 * z - 7 * 1) z :=
        h1.sub ((hasDerivAt_id z).const_mul 7)
      have h4 := h3.add_const 4
      convert h4 using 1
      ring
    have h5 := h2.mul hq
    convert h5 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 5) (5 * (1 + z) ^ 4) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h1.pow 5
    have hfun : ((fun y : ℝ => 1 + y) ^ 5) = fun y : ℝ => (1 + y) ^ 5 := by funext y; simp
    rw [hfun] at h2
    convert h2 using 1
    ring
  have h := hnum.div hden hdenne
  have hval : ((8 * z ^ 3 - 42 * z ^ 2 + 16 * z) * (1 + z) ^ 5
        - 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) * (5 * (1 + z) ^ 4)) / ((1 + z) ^ 5) ^ 2
      = 2 * z * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6 := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-! ## The `Zop`-iterates of the radial profile -/

lemma Zop_one_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop bcoefRad z = 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 := by
  have hzne : z ≠ -1 := by linarith
  show z * deriv (fun y : ℝ => 2 * y ^ 2 / (1 + y) ^ 3) z
    = 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4
  rw [(deriv1 z hzne).deriv]
  field_simp
  try ring

lemma Zop_two_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[2] bcoefRad z = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (2 - y) / (1 + y) ^ 4) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_one_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop bcoefRad) z
    = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
  show z * deriv (Work.Spaces.Zop bcoefRad) z
    = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
  rw [hev.deriv_eq, (deriv2 z hzne).deriv]
  field_simp
  try ring

lemma Zop_three_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[3] bcoefRad z
      = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[2] bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (y ^ 2 - 7 * y + 4) / (1 + y) ^ 5) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_two_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[2] bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
  show z * deriv (Work.Spaces.Zop^[2] bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
  rw [hev.deriv_eq, (deriv3 z hzne).deriv]
  field_simp
  try ring

/-! ## The weighted bound -/

/-- **The weighted `D_z`-iterates of `2z²/(1+z)³` are bounded by `120/(1+z)`.** -/
theorem bcoefRad_zop_bound : ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ), j ≤ 3 → ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z| ≤ K / (1 + z) := by
  refine ⟨120, by norm_num, fun j hj z hz => ?_⟩
  have hz0 : (0 : ℝ) ≤ z := hz
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  by_cases hz0' : z = 0
  · rw [hz0']
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0, mul_zero, abs_zero]
    norm_num
  have hpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz0')
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  rw [hw, le_div_iff₀ h1z]
  interval_cases j
  · -- `j = 0`
    show |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    have hval : |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) = 2 := by
      have hAB : bcoefRad z * ((1 + z) ^ 2 / z ^ 2) * (1 + z) = 2 := by
        rw [bcoefRad_eq]
        field_simp
        try ring
      calc |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
          = |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by rw [abs_of_pos h1z]
        _ = |bcoefRad z * ((1 + z) ^ 2 / z ^ 2) * (1 + z)| := (abs_mul _ _).symm
        _ = |2| := by rw [hAB]
        _ = 2 := by norm_num
    rw [hval]
    norm_num
  · -- `j = 1`
    show |Work.Spaces.Zop bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    rw [Zop_one_eq hzIoi]
    have hAB : 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2) * (1 + z)
        = 2 * (2 - z) / (1 + z) := by
      field_simp
      try ring
    calc |2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
        = |2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by
          rw [abs_of_pos h1z]
      _ = |2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2) * (1 + z)| :=
          (abs_mul _ _).symm
      _ = |2 * (2 - z) / (1 + z)| := by rw [hAB]
      _ ≤ 120 := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h1z]
          rw [div_le_iff₀ h1z]
          have hb : |2 - z| ≤ 3 * (1 + z) := by
            have h := abs_le_lin z (-2) hz0
            have he : z + (-2) = -(2 - z) := by ring
            rw [he, abs_neg] at h
            have h2 : (1 : ℝ) + |(-2 : ℝ)| = 3 := by norm_num
            rwa [h2] at h
          linarith [abs_nonneg (2 - z)]
  · -- `j = 2`
    show |Work.Spaces.Zop^[2] bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    rw [Zop_two_eq hzIoi]
    have hAB : 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)
        * (1 + z) = 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 2 := by
      field_simp
      try ring
    calc |2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
        = |2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by
          rw [abs_of_pos h1z]
      _ = |2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)
            * (1 + z)| := (abs_mul _ _).symm
      _ = |2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 2| := by rw [hAB]
      _ ≤ 120 := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (pow_pos h1z 2)]
          rw [div_le_iff₀ (pow_pos h1z 2)]
          have hb : |z ^ 2 - 7 * z + 4| ≤ 12 * (1 + z) ^ 2 := by
            have h := abs_le_quad z (-7) 4 hz0
            have he : z ^ 2 + (-7) * z + 4 = z ^ 2 - 7 * z + 4 := by ring
            rw [he] at h
            have h2 : (1 : ℝ) + |(-7 : ℝ)| + |(4 : ℝ)| = 12 := by norm_num
            rwa [h2] at h
          linarith [abs_nonneg (z ^ 2 - 7 * z + 4)]
  · -- `j = 3`
    show |Work.Spaces.Zop^[3] bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    rw [Zop_three_eq hzIoi]
    have hAB : 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
        * ((1 + z) ^ 2 / z ^ 2) * (1 + z)
        = 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 3 := by
      field_simp
      try ring
    calc |2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
          * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
        = |2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
            * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by rw [abs_of_pos h1z]
      _ = |2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
            * ((1 + z) ^ 2 / z ^ 2) * (1 + z)| := (abs_mul _ _).symm
      _ = |2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 3| := by rw [hAB]
      _ ≤ 120 := by
          have he : 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8)
              = -(2 * (z ^ 3 - 18 * z ^ 2 + 33 * z - 8)) := by ring
          rw [he, abs_div, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (pow_pos h1z 3)]
          rw [div_le_iff₀ (pow_pos h1z 3)]
          have hb : |z ^ 3 - 18 * z ^ 2 + 33 * z - 8| ≤ 60 * (1 + z) ^ 3 := by
            have h := abs_le_cubic z (-18) 33 (-8) hz0
            have he2 : z ^ 3 + (-18) * z ^ 2 + 33 * z + (-8)
                = z ^ 3 - 18 * z ^ 2 + 33 * z - 8 := by ring
            rw [he2] at h
            have h2 : (1 : ℝ) + |(-18 : ℝ)| + |(33 : ℝ)| + |(-8 : ℝ)| = 60 := by norm_num
            rwa [h2] at h
          linarith [abs_nonneg (z ^ 3 - 18 * z ^ 2 + 33 * z - 8)]

end Work.FTS.StrongPersist.L3Aux
end
end
