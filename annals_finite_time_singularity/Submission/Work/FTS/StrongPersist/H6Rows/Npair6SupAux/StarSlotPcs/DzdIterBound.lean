import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Thickening
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.aeSliceAesm
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.EllSol.EllAux1 =====
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

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2
local notation "Kθ" => Work.Elliptic.Ktheta

/-! ## Elementary facts about the angle interval -/

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval. -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
  Work.Elliptic.ae_restrict_Iθ_of_Ioo fun θ h0 h1 => ⟨h0, h1⟩

/-! ## Smoothness on the open quadrant from `SmoothQuad` -/

/-- `SmoothQuad` (smoothness on the open strip `z > -1`) implies `SmoothOpen` (smoothness on the
open quadrant `z > 0`). -/
theorem smoothOpen_of_smoothQuad {g : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad g) : Work.FTS.EllipticEst.SmoothOpen g :=
  h.mono fun p hp => by
    obtain ⟨h1, h2, h3⟩ := hp
    exact ⟨Set.mem_Ioi.mpr (by linarith [show (0 : ℝ) < p.1 from h1]), Set.mem_Ioo.mpr ⟨h2, h3⟩⟩

/-- `C²` at a point of the open quadrant, from `SmoothOpen`. -/
theorem smoothOpen_contDiffAt_two {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    ContDiffAt ℝ 2 (Function.uncurry F) (z, θ) :=
  (h.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩))).of_le (by simp [Work.Stability.smoothOrder])

/-- `SmoothOpen` is closed under multiplication by `z`. -/
theorem smoothOpen_z_mul {A : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * A z θ) := by
  have hfun : Function.uncurry (fun z θ => z * A z θ)
      = fun p : ℝ × ℝ => p.1 * A p.1 p.2 := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => A p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    hA.comp contDiffOn_id fun p hp => hp
  exact h1.mul h2

/-! ## Linearity and locality of the iterated derivatives -/

/-- `∂_z` is additive on `SmoothOpen` data. -/
theorem pz_add_open {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Spaces.pz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz g z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_add (hf.hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt
    (hg.hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt

/-- `∂_z`-iterates are additive on `SmoothOpen` data. -/
theorem pzIter_add_open {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pzIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pzIter i f z θ + Work.Spaces.pzIter i g z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h0 h1
      simp only [Work.Spaces.pzIter_succ]
      rw [Work.Spaces.pz, Work.Spaces.pz, Work.Spaces.pz]
      have hev : (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter n f z' θ + Work.Spaces.pzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h0 h1
      rw [Filter.EventuallyEq.deriv_eq hev]
      exact deriv_add ((hf.pzIter n).hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt
        ((hg.pzIter n).hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt

/-- `∂_z`-iterates only see the values on an open set. -/
theorem pzIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry u) (Function.uncurry v) V) (j : ℕ) :
    ∀ z θ, (z, θ) ∈ V → Work.Spaces.pzIter j u z θ = Work.Spaces.pzIter j v z θ := by
  induction j with
  | zero => intro z θ hz; exact h hz
  | succ n ih =>
      intro z θ hz
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
      exact Work.Spaces.pz_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-- `∂_θ`-iterates only see the values on an open set. -/
theorem pthIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry u) (Function.uncurry v) V) (j : ℕ) :
    ∀ z θ, (z, θ) ∈ V → Work.Spaces.pthIter j u z θ = Work.Spaces.pthIter j v z θ := by
  induction j with
  | zero => intro z θ hz; exact h hz
  | succ n ih =>
      intro z θ hz
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ]
      exact Work.Spaces.pth_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-! ## Linearity of the angular moment `F_*` -/

/-- **`F_*` is additive** (with a scalar) on slices whose product with `sinθcos²θ` is
integrable. -/
theorem Fstar_add_mul {f h : ℝ → ℝ → ℝ} {c z : ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => f z θ * sg θ) Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => h z θ * sg θ) Iθ) :
    Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Fstar f z + c * Work.Elliptic.Fstar h z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (∫ θ in Iθ, (f z θ + c * h z θ) * sg θ)
      = ∫ θ in Iθ, (f z θ * sg θ + c * (h z θ * sg θ)) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_add hf (hh.const_mul c), MeasureTheory.integral_const_mul]

/-- **`F_*` is homogeneous** (no integrability hypothesis: the Bochner integral is total). -/
theorem Fstar_const_mul (f : ℝ → ℝ → ℝ) (c z : ℝ) :
    Work.Elliptic.Fstar (fun z θ => c * f z θ) z = c * Work.Elliptic.Fstar f z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar,
    show (∫ θ in Iθ, (c * f z θ) * sg θ) = ∫ θ in Iθ, c * (f z θ * sg θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## The elements of the Galerkin class

`GalClass α g` is a structure whose `reg` field is `RegQ α 6 g = SmoothQuad g ∧ HkMem α 6 g ∧
BdryTraces α 6 g`. -/

theorem GalClass.smoothQuad {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.LocData.SmoothQuad g := hg.reg.1

theorem GalClass.hkMem_six {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.Spaces.HkMem α 6 g := hg.reg.2.1

theorem GalClass.smoothOpen {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.EllipticEst.SmoothOpen g := smoothOpen_of_smoothQuad (GalClass.smoothQuad hg)

theorem GalClass.contDiffOn_uncurry {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp (GalClass.smoothOpen hg)

theorem GalClass.hkMem_le {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) {k : ℕ}
    (hk : k ≤ 6) : Work.Spaces.HkMem α k g :=
  Work.FTS.EllipticEst.TT.HkMem_descend_open hk (GalClass.contDiffOn_uncurry hg)
    (GalClass.hkMem_six hg)

theorem GalClass.hkMem_zero {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.Spaces.HkMem α 0 g := GalClass.hkMem_le hg (by norm_num)



/-- The angular slice of a Galerkin datum is integrable against `sinθcos²θ` for every `z > 0`. -/
theorem GalClass.slice_sinCos2_integrable {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => g z θ * sg θ) Iθ :=
  Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 (GalClass.smoothOpen hg).continuousOn
    (GalClass.hkMem_zero hg) hz

/-! ## Slice integrability of the `ℋ⁴`-slots -/

/-- **The square of the angular slice** of an `ℋ⁴`-function is integrable: the `D_z⁰`-slot of
`HkIntegrand α 4 g` dominates `g²` on the open angle interval. -/
theorem slice_sq_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2) Iθ := by
  have hHs : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Iθ :=
    hmem.1 s (Set.mem_Ici.mpr hs.le)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => (g s θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hcont hs).pow 2
  refine MeasureTheory.Integrable.mono' hHs haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := Real.rpow_pos_of_pos hsin _
  have hSle : S ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 2)]
    nlinarith
  have hA : 1 ≤ Work.Spaces.w s / S := by
    rw [le_div_iff₀ hSpos, one_mul]
    exact le_trans hSle hw1
  have hsq : (g s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  calc (g s θ) ^ 2 = (g s θ) ^ 2 * 1 := by ring
    _ ≤ (g s θ) ^ 2 * (Work.Spaces.w s / S) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [hA, hSpos]
    _ = (g s θ * (Work.Spaces.w s / S)) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := hsq

/-- The slice `θ ↦ K(θ)·g(s,θ)/s` of the `L₁₂`-density is integrable for `s > 0`. -/
theorem L12dens_slice_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Kθ θ * g s θ / s) Iθ := by
  have hsq : MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2) Iθ :=
    slice_sq_integrable hcont hmem hs
  have hK : MeasureTheory.IntegrableOn (fun θ => (Kθ θ) ^ 2) Iθ :=
    ((Work.Elliptic.continuous_ktheta.pow 2).continuousOn).integrableOn_compact
      (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => ((Kθ θ) ^ 2 + (g s θ) ^ 2) / (2 * s)) Iθ :=
    (hK.add hsq).div_const (2 * s)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Kθ θ * g s θ / s)
      (MeasureTheory.volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Kθ p.2 * g p.1 p.2 / p.1)
      ((Work.Elliptic.continuous_ktheta.comp continuous_snd).continuousOn.mul hcont |>.div
        continuousOn_fst (fun _ hp => ne_of_gt hp.1)) hs
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hKnn : 0 ≤ Kθ θ := by
    rw [Work.Elliptic.Ktheta]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    positivity
  have hAM : 2 * (Kθ θ * |g s θ|) ≤ (Kθ θ) ^ 2 + (g s θ) ^ 2 := by
    nlinarith [sq_nonneg (Kθ θ - |g s θ|), sq_abs (g s θ)]
  rw [Real.norm_eq_abs, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * s)]
  have hval : |Kθ θ * g s θ / s| * (2 * s) = 2 * (Kθ θ * |g s θ|) := by
    rw [abs_div, abs_of_pos hs, abs_mul, abs_of_nonneg hKnn]
    field_simp
  rw [hval]
  exact hAM

/-! ## Linearity of the `L₁₂`-density and of `L₁₂` -/

/-- The density is additive (with a scalar) on integrable slices. -/
theorem L12dens_add_mul {f h : ℝ → ℝ → ℝ} {c s : ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => Kθ θ * f s θ / s) Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => Kθ θ * h s θ / s) Iθ) :
    Work.Elliptic.L12dens (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.L12dens f s + c * Work.Elliptic.L12dens h s := by
  rw [Work.Elliptic.L12dens, Work.Elliptic.L12dens, Work.Elliptic.L12dens,
    show (∫ θ in Iθ, Kθ θ * (f s θ + c * h s θ) / s)
        = ∫ θ in Iθ, (Kθ θ * f s θ / s + c * (Kθ θ * h s θ / s)) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_add hf (hh.const_mul c), MeasureTheory.integral_const_mul]

/-- The density is homogeneous (no integrability hypothesis). -/
theorem L12dens_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.Elliptic.L12dens (fun z θ => c * f z θ) s
      = c * Work.Elliptic.L12dens f s := by
  rw [Work.Elliptic.L12dens, Work.Elliptic.L12dens,
    show (∫ θ in Iθ, Kθ θ * (c * f s θ) / s)
        = ∫ θ in Iθ, c * (Kθ θ * f s θ / s) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_const_mul]

/-- `L₁₂` is homogeneous in the profile (no integrability hypothesis). -/
theorem L12_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12 (fun z θ => c * f z θ) z = c * Work.Elliptic.L12 f z := by
  rw [Work.Elliptic.L12, Work.Elliptic.L12,
    show (fun r => Work.Elliptic.L12dens (fun z θ => c * f z θ) r)
        = fun r => c * Work.Elliptic.L12dens f r from
      funext fun r => L12dens_const_mul c f r]
  rw [MeasureTheory.integral_const_mul]

/-! ## Linearity of the orthogonalised source -/

/-- `orthSource` is additive (with a scalar), given the additivity of `F_*` at the radial
parameter `z`. -/
theorem orthSource_add_mul_apply {f h : ℝ → ℝ → ℝ} {c z θ : ℝ}
    (heq : Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Fstar f z + c * Work.Elliptic.Fstar h z) :
    Work.Elliptic.orthSource (fun z θ => f z θ + c * h z θ) z θ
      = Work.Elliptic.orthSource f z θ + c * Work.Elliptic.orthSource h z θ := by
  rw [Work.Elliptic.orthSource, Work.Elliptic.orthSource, Work.Elliptic.orthSource, heq]
  ring


/-! ## Congruence of `F_*` along agreement on the open angle interval -/

theorem Fstar_congr_Ioo {f h : ℝ → ℝ → ℝ} {z : ℝ}
    (hfh : ∀ θ, 0 < θ → θ < π / 2 → f z θ = h z θ) :
    Work.Elliptic.Fstar f z = Work.Elliptic.Fstar h z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  exact MeasureTheory.integral_congr_ae
    (Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ => f z θ * sg θ = h z θ * sg θ)
      (fun θ h0 h1 => by rw [hfh θ h0 h1]))

end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeCrux.AeMixedAeMemOfCrux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeCrux

/-
The glue that turns the two crux statements into the tree's `aeMixedAe_mem` (the leaf
`Cores/AeStep2Aux/aeMixedAe_mem`, both call sites having the same conclusion): the gaps are the
null-set transfers `Ioo 0 (π/2) → Iθ` and `Ioi 0 → Iz`, plus `1 ≤ w z` on `z > 0`
(`w z = (1+z)^2/z^2`) for the outer conjunct.  Purely measure-theoretic; `h` and `hU` are unused.
-/
theorem AeMixedAeMemOfCrux {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hsl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hout : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi (0 : ℝ))) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz := by
  -- `Iθ = Icc 0 (π/2)` differs from `Ioo 0 (π/2)` by two points, and `Iz = Ici 0` from
  -- `Ioi 0` by one, so the corresponding restricted measures agree.
  have hIcc : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).symm
  have hIci : MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm
  constructor
  · -- first conjunct: transfer the a.e. slice honesty from `(0,π/2)` to `Iθ`
    filter_upwards [hsl] with z hz
    show MeasureTheory.Integrable
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
    rw [hIcc]
    exact hz
  · -- second conjunct: transfer the outer integrability from `(0,∞)` to `Iz` and from the
    -- open angular interval to `Iθ`; the weight satisfies `1 ≤ w z` on `z > 0`.
    have hfuneq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        = (fun z : ℝ => ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by
      funext z
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2)).symm
    show MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))
    rw [hIci, hfuneq]
    refine MeasureTheory.Integrable.mono hout ?_ ?_
    · -- a.e. strong measurability of the unweighted slice functional: divide by `w z ^ 2`
      have hb : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => (Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                  * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hout.aestronglyMeasurable
      have hwcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
        have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 * (z ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
          (((continuous_const.add continuous_id).pow 2).continuousOn).mul
            (((continuous_id.pow 2).continuousOn).inv₀
              (fun z hz => pow_ne_zero 2 (ne_of_gt hz)))
        refine h1.congr (fun z hz => ?_)
        simp only [Work.Spaces.w, div_eq_mul_inv]
      have hc : ContinuousOn (fun z : ℝ => ((Work.Spaces.w z) ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
        (hwcont.pow 2).inv₀ (fun z hz => by
          have hzpos : 0 < z := hz
          have hw : Work.Spaces.w z ≠ 0 := by
            rw [Work.Spaces.w]
            exact div_ne_zero (pow_ne_zero 2 (by linarith [hzpos]))
              (pow_ne_zero 2 (ne_of_gt hzpos))
          exact pow_ne_zero 2 hw)
      refine ((hc.aestronglyMeasurable measurableSet_Ioi).mul hb).congr ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
      show ((Work.Spaces.w z) ^ 2)⁻¹
            * ((Work.Spaces.w z) ^ 2
              * ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                    * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
          = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
      have hzpos : 0 < z := hz
      have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
        have h1 : Work.Spaces.w z ≠ 0 := by
          rw [Work.Spaces.w]
          exact div_ne_zero (pow_ne_zero 2 (by linarith [hzpos]))
            (pow_ne_zero 2 (ne_of_gt hzpos))
        exact pow_ne_zero 2 h1
      rw [inv_mul_cancel_left₀ hw]
    · -- a.e. norm bound: `1 ≤ w z ^ 2` on `z > 0`
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
      have hzpos : 0 < z := hz
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        have h1 : 1 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w, le_div_iff₀ (pow_pos hzpos 2)]
          nlinarith
        nlinarith [h1]
      have hwnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwnn]
      have hX : 0 ≤ |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))| := abs_nonneg _
      simpa using mul_le_mul_of_nonneg_right hw1 hX

end Work.FTS.EllipticEst.AeCrux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut.TTAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts.TendstoTermsCut.TTAux`

The analytic toolbox for the four `k → ∞` limits of the doubly truncated `I₁` identity
(`AeI1Fts.TendstoTermsCut.tendsto_terms_cut`): the two dominated-convergence limits that remove
the radial cut-off `cut k` and the angular cut-off `SliceMixedAux.cut (1/(k+1))` *simultaneously*
on the product measure `nuQ`, and the joint integrability of the four untruncated slots.

The marginal finiteness `ntFin` of the `N`-term (`z ↦ w²∫_θ U²cos²(2θ)σ₂`) is derived from
`hardy_slice_ae` (`∫_θ U²cos²(2θ)σ₂ ≤ (1+η)⁻²∫_θ V²σ` a.e.) together with a.e. strong
measurability of the marginal (`TT.aeSliceAesm`) and the `ℋ⁰`-honesty of `V u`.
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

/-- The sequential angular cut-off parameter `δ_k = 1/(k+1)`. -/
abbrev dk (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-! ## Elementary facts -/

/-- `|cw z| ≤ 2` for `z ≥ 0` (`cw z = 2(z-1)/(1+z)`). -/
theorem abs_cw_le_two {z : ℝ} (hz : 0 ≤ z) : |cwt z| ≤ 2 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [Work.FTS.EllipticEst.AngSecond.cw, abs_div, abs_of_pos h1]
  rw [show |2 * (z - 1)| = 2 * |z - 1| by rw [abs_mul]; norm_num]
  rw [div_le_iff₀ h1]
  have h : |z - 1| ≤ z + 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith






/-! ## The two dominated-convergence limits on `nuQ` -/



/-! ## The truncated integrands are integrable -/



/-! ## Joint integrability of the untruncated slots -/




/-! ## Finiteness of the marginal of the `N`-term -/


end

end Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut
end
-- ===== merged: Submission.Work.FTS.EllipticEst.alphaDzW_Hk_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## `L₀` and the radial multiples of `sin 2θ` -/


/-! ## Additivity of `D_z^j` on functions smooth on an open set -/


/-! ## The `D_z`-derivative of the residual -/


/-! ## The identity for `α D_z W` -/


/-! ## The identity (☆) of `alphaDzEllResid_eq`, discharged from `EllHyp`

The pointwise hypotheses of `alphaDzEllResid_eq` are supplied from the data class `EllHyp`
(the smoothness of `Ψ` on a neighbourhood of the closed quadrant, the elliptic law
`bslOp α Ψ = F`, the smoothness of `F_*`/`Gsing` and the ODE for `Gsing`); the public
statement is `alphaDzEllResid_eq_of_EllHyp_local`.  (This is the content of the module
`alphaDzEllResid_eq_of_Hyp`, inlined here because that module imports this one; its helper
lemmas are `private`, so inlining them creates no name clashes.) -/


/-! ## `C²` of `Φ(z,θ) = G(z) sin 2θ` at a point -/


/-! ## The `z`-slices of `Ψ` -/


/-! ## The product rule along a `z`-slice -/


/-! ## Additivity of `D_z` and `D_z²` from the product rule

`D_z^j` is a composition of derivatives, so it is additive on functions that are
differentiable at the point; the analyticity demanded by the general additivity lemmas of the
workspace (`DzIter_add_of_isOpen`) is not available for `G = Gsing α F`, so the two additivity
statements needed below are proved from the product rule instead. -/




/-! ## The target identity -/


/-! ## The first link: `α D_z W` as a multiple of the right-hand side of (☆)

The identity `alphaDzEllResid_eq` is a pointwise statement on the open quadrant; because the
`ℋ^k`-norm only sees the quadrant up to a null set, it can be transported to a statement about
`HkSq` (`HkSq_congr_open`), and the constant factor taken out of the norm
(`HkNorm_const_mul`).  This reduces the estimate to the sub-additivity chain. -/

/-- `HkSq` is homogeneous of degree two: `HkSq α k (β·f) = β² HkSq α k f`. -/
theorem HkSq_const_mul (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => β * f z θ) = β ^ 2 * Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  have hslice : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => Work.FTS.LocData.HkIntegrand_const_mul α k β f z θ)
  have hout : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
      = ∫ z in Work.Spaces.Iz,
          β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
    MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iz) measurableSet_Ici
      (fun z _ => hslice z)
  rw [hout, MeasureTheory.integral_const_mul]






/-! ## The straightened solution `Ψ + Gsing α F · sin 2θ` and the transfer identities

Write `Ψ̂ := fun z θ => Ψ z θ + Gsing α F z * Real.sin (2 * θ)` (the `Straight` of
Theorem `RemovingL12`) and `W := EllResid α F Ψ`.  Since `EllResid α F Ψ = Ψ + Gstar α F · sin 2θ`
and `Gsing = Gstar + Gbar`, one has the pointwise identity

  `W = Ψ̂ - Gbar α F · sin 2θ`,

and the three identities below record the effect of this on the derivatives used by the
estimate: the `D_z`-transfer (`α D_zΨ̂ = α D_zΨ - 5 Ḡ sin 2θ`), the `∂_θθ`-transfer
(`∂_θθW = ∂_θθΨ̂ + 4 Ḡ sin 2θ`) and the `z²∂_zz`-transfer
(`α² z²∂_zzΨ̂ = α²z²∂_zzΨ + (15/4) sin 2θ · F_* + 5(5+α) sin 2θ · Ḡ`). -/

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
theorem deriv_sin_two (θ : ℝ) : deriv (fun θ' => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ (by simpa using (hasDerivAt_id θ).const_mul (2 : ℝ))
  rw [h.deriv]; ring

/-- `∂_θ(cos 2θ) = -2 sin 2θ`. -/
theorem deriv_cos_two (θ : ℝ) : deriv (fun θ' => Real.cos (2 * θ')) θ = -2 * Real.sin (2 * θ) := by
  have h : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ)) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ (by simpa using (hasDerivAt_id θ).const_mul (2 : ℝ))
  rw [h.deriv]; ring


/-- **`∂_θθ` of a radial multiple of `sin 2θ`**: `∂_θθ(g(z) sin 2θ) = -4 g(z) sin 2θ`. -/
theorem pthIter2_radial_sin_two (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = -(4 * (g z * Real.sin (2 * θ))) := by
  have hbase : Work.Spaces.pthIter 2 (fun z θ => g z * Real.sin (2 * θ)) z θ
      = deriv (fun θ' => deriv (fun θ'' => g z * Real.sin (2 * θ'')) θ') θ := rfl
  rw [hbase]
  have h1 : (fun θ' => deriv (fun θ'' => g z * Real.sin (2 * θ'')) θ')
      = fun θ' => g z * (2 * Real.cos (2 * θ')) := by
    funext θ'
    rw [deriv_const_mul (g z)
      (by fun_prop : DifferentiableAt ℝ (fun θ'' : ℝ => Real.sin (2 * θ'')) θ')]
    rw [deriv_sin_two]
  rw [h1]
  have h2 : deriv (fun θ' : ℝ => g z * (2 * Real.cos (2 * θ'))) θ
      = g z * (2 * (-(Real.sin (2 * θ)) * 2)) := by
    rw [deriv_const_mul (g z)
      (by fun_prop : DifferentiableAt ℝ (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ)]
    congr 1
    exact ((Real.hasDerivAt_cos (2 * θ)).comp θ
      (by simpa using (hasDerivAt_id θ).const_mul (2 : ℝ))).const_mul 2 |>.deriv
  rw [h2]; ring


/-! ## Differentiability of the slices of a `SmoothOpen` function -/

/-- The `θ`-slice of a function of class `C^n` on the open quadrant is `C^n` on `(0,π/2)`. -/
theorem contDiffOn_slice_theta_nat {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ n (fun θ => f z θ) (Set.Ioo 0 (π / 2)) :=
  (hf.comp ((contDiffOn_const (c := z)).prodMk
      (contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) (Set.Ioo 0 (π / 2))))
    (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The `z`-slice of a function of class `C^n` on the open quadrant is `C^n` on `(0,∞)`. -/
theorem contDiffOn_slice_z_nat {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ n (fun z => f z θ) (Set.Ioi 0) :=
  (hf.comp ((contDiffOn_id : ContDiffOn ℝ n (fun z : ℝ => z) (Set.Ioi 0)).prodMk
      (contDiffOn_const (c := θ))) (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a `SmoothOpen` function is differentiable at every interior angle. -/
theorem SmoothOpen.differentiableAt_slice_theta {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
  ((contDiffOn_slice_theta_nat (hf.forall 2) hz).differentiableOn
    (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩)

/-- The `z`-slice of a `SmoothOpen` function is differentiable at every interior radius. -/
theorem SmoothOpen.differentiableAt_slice_z {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun z' : ℝ => f z' θ) z :=
  ((contDiffOn_slice_z_nat (hf.forall 2) ⟨hθ1, hθ2⟩).differentiableOn
    (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- `SmoothOpen` is closed under addition. -/
theorem SmoothOpen.add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine smoothOpen_of_forall fun n => ?_
  have h1 : Function.uncurry (fun z θ => f z θ + g z θ)
      = (Function.uncurry f) + (Function.uncurry g) := by
    funext p; rfl
  rw [h1]
  exact (hf.forall n).add (hg.forall n)

/-! ## Additivity of the slice derivatives on `SmoothOpen` data -/


/-- `∂_θθ` is additive on `SmoothOpen` data, subtraction form. -/
theorem pthIter2_sub {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pthIter 2 (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.pthIter 2 f z θ - Work.Spaces.pthIter 2 g z θ := by
  have hnb : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩
  have hfun : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.pth (fun z θ => f z θ - g z θ) z θ'
        = Work.Spaces.pth f z θ' - Work.Spaces.pth g z θ' := by
    intro θ' hθ'
    rw [Work.Spaces.pth, Work.Spaces.pth, Work.Spaces.pth]
    have heq : (fun θ'' : ℝ => f z θ'' - g z θ'')
        =ᶠ[𝓝 θ'] ((fun θ'' : ℝ => f z θ'') - fun θ'' : ℝ => g z θ'') :=
      Filter.Eventually.of_forall fun _ => rfl
    rw [Filter.EventuallyEq.deriv_eq heq, deriv_sub
      (hf.differentiableAt_slice_theta hz hθ'.1 hθ'.2)
      (hg.differentiableAt_slice_theta hz hθ'.1 hθ'.2)]
  have hev : Work.Spaces.pth (fun z θ => f z θ - g z θ) z
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pth f z θ' - Work.Spaces.pth g z θ') :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hnb, hfun⟩
  have hbase : Work.Spaces.pthIter 2 (fun z θ => f z θ - g z θ) z θ
      = deriv (Work.Spaces.pth (fun z θ => f z θ - g z θ) z) θ := rfl
  rw [hbase, Filter.EventuallyEq.deriv_eq hev]
  have heq2 : (fun θ' : ℝ => Work.Spaces.pth f z θ' - Work.Spaces.pth g z θ')
      =ᶠ[𝓝 θ] ((Work.Spaces.pth f z) - Work.Spaces.pth g z) :=
    Filter.Eventually.of_forall fun _ => rfl
  rw [Filter.EventuallyEq.deriv_eq heq2, deriv_sub
    (hf.pth.differentiableAt_slice_theta hz hθ1 hθ2)
    (hg.pth.differentiableAt_slice_theta hz hθ1 hθ2)]
  rfl

/-- `∂_z` is additive on `SmoothOpen` data. -/
theorem pz_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.pz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz g z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz, Work.Spaces.pz]
  have heq : (fun z' : ℝ => f z' θ + g z' θ) =ᶠ[𝓝 z] ((fun z' : ℝ => f z' θ)
      + fun z' : ℝ => g z' θ) := Filter.Eventually.of_forall fun _ => rfl
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_add (hf.differentiableAt_slice_z hz hθ1 hθ2)
    (hg.differentiableAt_slice_z hz hθ1 hθ2)]

/-- `D_z` is additive on `SmoothOpen` data. -/
theorem Dz_add {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Spaces.Dz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.Dz f z θ + Work.Spaces.Dz g z θ := by
  rw [Work.Spaces.Dz, Work.Spaces.Dz, Work.Spaces.Dz, pz_add hf hg hz hθ1 hθ2]
  ring


/-! ## The transfer identities -/





/-! ## The assembly of the estimate -/


/-! ## The estimate -/




/-!

## Status, and how to finish `alphaDzW_Hk_le`

**Proved in this file.**  `Lzero_radial_sin_two`, `DzIter_add_eq`, `Dz_EllResid`,
`alphaDzEllResid_eq` (the algebraic identity (☆)), `HkSq_const_mul`,
`HkNorm_alphaDzEllResid_eq`, `HkNorm_sum4_le`, `alphaDzW_Hk_le_first_link` (the "first
link"), the calculus lemmas `deriv_sin_two`, `deriv_cos_two`, `deriv_deriv_sin_two`,
`pthIter2_radial_sin_two`, `pzIter2_radial_mul`, the `SmoothOpen` slice/additivity API
(`SmoothOpen.differentiableAt_slice_theta/z`, `SmoothOpen.add`, `pthIter2_add/sub`,
`pzIter2_add`, `pz_add`, `Dz_add`), the transfer identities (`EllResid_eq_Straight_sub`,
`alpha_Dz_Straight_eq`, `pthIter2_EllResid_eq`, `alpha_sq_zsq_pzIter2_Straight_eq`) — all
`sorry`-free — and the **assembly** `alphaDzW_Hk_le_assembly`, which derives the target
estimate from the first link, the single input `hZ`

  `α²|D_z²Ψ̂| + 5α|D_zΨ̂| ≤ K (|F| + |∂_θθW| + α²|z²∂_zzΨ|)`,

the bound `|sin 2θ · F_*| ≤ C₄|F|` (`Fstar_Hk_le_open`, proved) and the sub-additivity /
homogeneity parameters `hadd` (`HkNorm_add_le`) and `hcm` (`HkNorm_const_mul`).

**What remains.**  Only the wiring: import
`alphaDzEllResid_eq_of_Hyp` (proved: supplies `hid`), `HkNorm_add_fts` (i.e.
`HkNorm_add_le`), `Fstar_Hk_le_open` (proved), `Straight_DzHk_le` (supplies `hZ`),
`EllHyp_F_smoothOpen` (open-quadrant smoothness of `F` from the equation),
`EllHyp_certificates` / `Straight_certs_open` / `HkMem_FstarSin_open` (the `∀n ContDiffOn`
and `HkMem` certificates for the four pieces of the first link and their partial sums,
the latter via `HkMem_add_smoothOpen`), and then instantiate the assembly with `K` from
`Straight_DzHk_le` and `C₄` from `Fstar_Hk_le_open`.  Note the multiplication order:
`Fstar_Hk_le_open` bounds `fun z θ => Fstar F z * sin 2θ`, whereas `hFS` above uses
`fun z θ => sin 2θ * Fstar F z`; convert with `HkSq_congr_open` and `ring`.

**Workspace note (blocks the wiring, not this file).**
`Submission/Work/FTS/EllipticEst/IntegrableOn_Fstar_div_of_HkMem.lean` declares
`Work.FTS.EllipticEst.HkIntegrand_zero`, a name that already exists in
`Submission/Work/FTS/EllipticEst/Defs.lean` with a different signature.  Any module importing
both therefore fails with

  `import ...IntegrableOn_Fstar_div_of_HkMem failed, environment already contains
   'Work.FTS.EllipticEst.HkIntegrand_zero' from ...Defs`

— this is what currently breaks `alphaDzEllResid_eq_of_Hyp.lean` and `Straight_DzHk_le.lean`
(both `sorry`-free) and, transitively, everything of the node that imports them.  Renaming the
copy in `IntegrableOn_Fstar_div_of_HkMem.lean` (e.g. to `HkIntegrand_zero_k0`) repairs the
whole neighbourhood.
-/

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkIntegrand_perz_RHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.bdryTraces_of_suppIn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

set_option maxHeartbeats 400000


end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.CutEst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Two elementary arithmetic lemmas -/

/-- `a²·b² ≤ K²·(c·H)` from `a² ≤ K²c`, `b² ≤ H`, `0 ≤ c`. -/
private lemma mul_sq_le {a b c H K : ℝ} (ha : a ^ 2 ≤ K ^ 2 * c) (hb : b ^ 2 ≤ H)
    (hc : 0 ≤ c) : a ^ 2 * b ^ 2 ≤ K ^ 2 * (c * H) := by
  calc a ^ 2 * b ^ 2 ≤ (K ^ 2 * c) * H :=
        mul_le_mul ha hb (sq_nonneg b) (mul_nonneg (sq_nonneg K) hc)
    _ = K ^ 2 * (c * H) := by ring


/-! ## The localised product bound

The Leibniz expansion `mulSlotRHS` of the `ℋ⁴`-integrand of `χ · f` is dominated by two explicit
localised quantities: the `ℋ⁴`-mass of `f` carried by the region `U` where the mixed derivatives
of `χ` can be non-zero, and the *wrong-weight* slots `D_z^b f · Wt α` (i.e. the `γ`-weighted
`D_z`-slots) carried by the angular layer `L` — the terms of the expansion in which every
`θ`-derivative falls on the multiplier. -/


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.radA_slotSum4_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.Norm


end Work.FTS.GalFields.Norm
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow15T2Aux.BoundA =====
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

/-! ## The factorization of `N₂^{ss}` on the open quadrant -/

theorem N2ss_open_eq {α : ℝ} {Φs : Fn} (hα : 0 < α) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.FTS.Nonlin.N2ss α Φs z θ = psi15 z * (2 * C15 α θ * G15 α Φs z θ) := by
  have hs2 : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.FTS.Nonlin.N2ss, Work.Construction.pth_Fstar_eq hα]
  rw [C15_apply, Work.Spaces.dthU, Work.FM.Fstar, psi15_eq, G15_apply]
  field_simp
  rw [Work.Construction.s2_eq]
  ring

/-! ## Functorial evaluations of the iterated operators on one-variable functions -/

theorem pzIter_thetaFn (A : ℝ → ℝ) (d : ℕ) :
    Work.Spaces.pzIter d (fun _ (θ : ℝ) => A θ) = fun _ θ => if d = 0 then A θ else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      show deriv (fun z' : ℝ => (if d = 0 then A θ else (0 : ℝ))) z
        = (if d + 1 = 0 then A θ else 0)
      rw [deriv_const]
      simp

theorem pzIter_DthIter_thetaFn (A : ℝ → ℝ) (e d : ℕ) :
    Work.Spaces.pzIter d (Work.Spaces.DthIter e (fun _ (θ : ℝ) => A θ))
      = fun _ θ => if d = 0 then Work.Spaces.dthU^[e] A θ else 0 := by
  rw [DthIter_theta_only, pzIter_thetaFn]

theorem pzIter_thetaFn_apply (A : ℝ → ℝ) (d : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter d (fun _ (θ : ℝ) => A θ) z θ = if d = 0 then A θ else 0 := by
  rw [pzIter_thetaFn]

theorem pzIter_DthIter_thetaFn_apply (A : ℝ → ℝ) (e d : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter d (Work.Spaces.DthIter e (fun _ (θ : ℝ) => A θ)) z θ
      = if d = 0 then Work.Spaces.dthU^[e] A θ else 0 := by
  rw [pzIter_DthIter_thetaFn]

theorem DthIter_zFn (r : ℝ → ℝ) (a : ℕ) (ha : 1 ≤ a) :
    Work.Spaces.DthIter a (fun z _ => r z) = fun _ _ => (0 : ℝ) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  induction b with
  | zero =>
      funext z θ
      rw [Nat.zero_add, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
      show Real.sin (2 * θ) * Work.Spaces.pth (fun z _ => r z) z θ = 0
      simp [Work.Spaces.pth]
  | succ b ih =>
      have hb : 1 ≤ b + 1 := by omega
      rw [show b + 1 + 1 = (b + 1) + 1 from by ring, Work.Spaces.DthIter_succ, ih hb]
      funext z θ
      show Real.sin (2 * θ) * Work.Spaces.pth (fun _ _ => (0 : ℝ)) z θ = 0
      simp [Work.Spaces.pth]

theorem pzIter_DthIter_zFn (r : ℝ → ℝ) (a c : ℕ) (ha : 1 ≤ a) :
    Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z _ => r z)) = fun _ _ => (0 : ℝ) := by
  rw [DthIter_zFn r a ha]
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.pz]

/-! ## The angular factor `A = 2·C15` and the product `A·G` -/

/-- The angular factor `A = 2·C15 α` of row 15.  Since `C15 α = -2(α/c)·D_θΓ`, `A` carries
two factors of `α` and, like `D_θΓ`, vanishes at the two angular endpoints. -/
def A15 (α : ℝ) : ℝ → ℝ := fun θ => 2 * C15 α θ

/-- The product `A·G` of the angular factor with the weighted star coefficient. -/
def AG15 (α : ℝ) (Φs : Fn) : Fn := fun z θ => 2 * C15 α θ * G15 α Φs z θ

/-- The open-quadrant representative `ψ·A·G` of `N₂^{ss}`. -/
def N2ssO (α : ℝ) (Φs : Fn) : Fn := fun z θ => psi15 z * AG15 α Φs z θ

/-! ## A constant double range sum -/

theorem sum_range_range_const (n m : ℕ) (C : ℝ) :
    (∑ _c ∈ Finset.range (n + 1), ∑ _a ∈ Finset.range (m + 1), C)
      ≤ (((n + 1 : ℕ)) : ℝ) * (((m + 1 : ℕ)) : ℝ) * C := by
  have hinner : ∀ c ∈ Finset.range (n + 1),
      (∑ _a ∈ Finset.range (m + 1), C) ≤ (((m + 1 : ℕ)) : ℝ) * C := by
    intro c hc
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (∑ _c ∈ Finset.range (n + 1), ∑ _a ∈ Finset.range (m + 1), C)
      ≤ ∑ _c ∈ Finset.range (n + 1), (((m + 1 : ℕ)) : ℝ) * C :=
        Finset.sum_le_sum hinner
    _ ≤ (((n + 1 : ℕ)) : ℝ) * ((((m + 1 : ℕ)) : ℝ) * C) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (((n + 1 : ℕ)) : ℝ) * (((m + 1 : ℕ)) : ℝ) * C := by ring

/-- Pulling a constant out of a double range sum. -/
theorem mul_sum_sum_const {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ℝ)
    (f : ι → κ → ℝ) :
    c * (∑ i ∈ s, ∑ j ∈ t, f i j) = ∑ i ∈ s, ∑ j ∈ t, c * f i j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-! ## The weighted angular bound `α Γ ≤ (α + sin 2θ) sin(2θ)^{α/5}` -/

theorem alpha_Gam_le_weight (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ
      ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsin2 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hgam := Work.Spaces.Gam_mul_weight_le α θ hα hθ
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have h1 : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ α + Real.sin (2 * θ) := (div_le_one hden).mp hgam
  have h2 : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        * (Real.sin (2 * θ)) ^ (α / 5)
      ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hsin2 _)
  have hsq : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        * (Real.sin (2 * θ)) ^ (α / 5) = α * Work.Spaces.Gam α θ := by
    rcases eq_or_lt_of_le hsin2 with h | h
    · have hΓ : Work.Spaces.Gam α θ = 0 := by
        have hle := Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_le_sin_two_rpow α θ hα hθ
        rw [← h, Real.zero_rpow (by linarith : α / 5 ≠ 0)] at hle
        linarith [(Work.Spaces.Gam_bounds α θ hα hθ).1]
      rw [hΓ]; ring
    · have h3 : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
        rw [← Real.rpow_add h, show -(α / 5) + α / 5 = 0 by ring, Real.rpow_zero]
      calc α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * (Real.sin (2 * θ)) ^ (α / 5)
          = (α * Work.Spaces.Gam α θ)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
        _ = (α * Work.Spaces.Gam α θ) * 1 := by rw [h3]
        _ = α * Work.Spaces.Gam α θ := by ring
  rw [hsq] at h2
  exact h2

/-! ## The two angular jet bounds of `A = 2·C15` -/

/-- Flat angular jet bound of `A = 2·C15`: `|D_θ^a A| ≤ K α² Γ` for `a ≤ 4`. -/
theorem dthU_iter_A_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ| ≤ K * α ^ 2 * Work.Spaces.Gam α θ := by
  obtain ⟨K, hK, hKb⟩ := dthU_iter_C15_le
  refine ⟨2 * K, by positivity, ?_⟩
  intro α hα hα1 a ha θ hθ
  rw [show (fun θ => 2 * C15 α θ) = fun θ => (2 : ℝ) * C15 α θ from rfl,
    Work.Spaces.dthU_iter_const_mul]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc (2 : ℝ) * |Work.Spaces.dthU^[a] (C15 α) θ|
      ≤ 2 * (K * α ^ 2 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left (hKb α hα hα1 a ha θ hθ) (by norm_num)
    _ = 2 * K * α ^ 2 * Work.Spaces.Gam α θ := by ring

theorem dthU_iter_A_flat_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ| ≤ K * α ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := dthU_iter_A_le
  refine ⟨max K 1, lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
  intro α hα hα1 a ha θ hθ
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have h1 := hKb α hα hα1 a ha θ hθ
  have hKα : (0 : ℝ) ≤ K * α ^ 2 := mul_nonneg hK.le (sq_nonneg α)
  have h2 : K * α ^ 2 * Work.Spaces.Gam α θ ≤ K * α ^ 2 := by
    calc K * α ^ 2 * Work.Spaces.Gam α θ ≤ K * α ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hG1 hKα
      _ = K * α ^ 2 := by ring
  exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_right (le_max_left K 1) (sq_nonneg α)))

theorem dthU_iter_A_weight_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ|
        ≤ K * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  refine ⟨40 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1), ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    linarith
  · intro α hα hα1 a ha θ hθ
    have hTB : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin2 : 0 ≤ Real.sin (2 * θ) := by
      have hs0 : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      have hc0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      rw [Real.sin_two_mul]; positivity
    have hw0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hsin2 _)
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
    have htb : Work.Spaces.tBound a 0 ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.single_le_sum (f := fun a => Work.Spaces.tBound a 0)
        (fun a _ => Work.Spaces.tBound_nonneg a 0) (Finset.mem_range.mpr (by omega))
    have hdth := Work.Spaces.dthU_Gam_le (a + 1) (by omega) α hα hα1 θ hθ
    rw [show a + 1 - 1 = a from by omega] at hdth
    have hGamw := alpha_Gam_le_weight α θ hα hθ
    rw [show (fun θ => 2 * C15 α θ) = fun θ => (2 : ℝ) * C15 α θ from rfl,
      Work.Spaces.dthU_iter_const_mul, dthU_iter_C15]
    rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num,
      show |(-2 * (α / Work.Spaces.c α))| = 2 * |α / Work.Spaces.c α| from by
        rw [abs_mul]; norm_num]
    rw [show (2 : ℝ) * (2 * |α / Work.Spaces.c α|
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|)
        = (2 : ℝ) * (2 * |α / Work.Spaces.c α|)
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ| from by ring]
    have h1 : |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ :=
      hdth.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htb hα.le) hGam0)
    have h2 : (2 : ℝ) * (2 * |α / Work.Spaces.c α|)
        * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (2 : ℝ) * (2 * (10 * α))
          * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ) := by
      refine mul_le_mul ?_ h1 (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (by norm_num))
        (by norm_num)
    refine le_trans h2 ?_
    have h5 : (2 : ℝ) * (2 * (10 * α))
          * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ)
        = 40 * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
            * (α * (α * Work.Spaces.Gam α θ)) := by ring
    rw [h5]
    have h6 : α * (α * Work.Spaces.Gam α θ)
        ≤ α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
      mul_le_mul_of_nonneg_left hGamw hα.le
    have h7 : (40 : ℝ) * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
          * (α * (α * Work.Spaces.Gam α θ))
        ≤ 40 * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
          * (α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    refine le_trans h7 ?_
    have h8 : (40 : ℝ) * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
        ≤ 40 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1) := by linarith
    have h9 : (40 : ℝ) * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
          * (α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        ≤ 40 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1)
          * (α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
      mul_le_mul_of_nonneg_right h8 (mul_nonneg hα.le hw0)
    refine le_trans h9 (le_of_eq ?_)
    ring

/-! ## Named constants

The final constant `KW15` of the row must be *nameable* (it is the `K` of the row statement),
so the four numerical constants of the lemmas above are extracted with `Classical.choose`. -/

noncomputable def KA15 : ℝ := Classical.choose dthU_iter_A_flat_le

theorem KA15_pos : 0 < KA15 := (Classical.choose_spec dthU_iter_A_flat_le).1

theorem KA15_bd : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ| ≤ KA15 * α ^ 2 :=
  (Classical.choose_spec dthU_iter_A_flat_le).2

noncomputable def KB15 : ℝ := Classical.choose dthU_iter_A_weight_le

theorem KB15_pos : 0 < KB15 := (Classical.choose_spec dthU_iter_A_weight_le).1

theorem KB15_bd : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ|
      ≤ KB15 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
  (Classical.choose_spec dthU_iter_A_weight_le).2

noncomputable def Cp15 : ℝ := Classical.choose pzIter_psi15_le

theorem Cp15_pos : 0 < Cp15 := (Classical.choose_spec pzIter_psi15_le).1

theorem Cp15_bd : ∀ (c m : ℕ), c ≤ m → m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
    (1 + z) * Work.Spaces.w z * z ^ m * |Work.Spaces.pzIter c (fun z _ => psi15 z) z θ|
      ≤ Cp15 * (1 + z) ^ (m - c) :=
  (Classical.choose_spec pzIter_psi15_le).2

/-- The constant of the flat `z`-jet bound of `A·G`. -/
noncomputable def KAG15 : ℝ := 257 * 5 * KA15

/-- The constant of the weighted mixed jet bound of `A·G`. -/
noncomputable def KAGd15 : ℝ := 257 * 25 * (KA15 + KB15 + 1)

theorem KAG15_pos : 0 < KAG15 := by
  rw [KAG15]; exact mul_pos (by norm_num) KA15_pos

theorem KAGd15_pos : 0 < KAGd15 := by
  rw [KAGd15]
  have := KA15_pos
  have := KB15_pos
  positivity

/-- **The final constant of row 15**: `W = KW15·α·|G15|_{𝒲^{4,∞}}`. -/
noncomputable def KW15 : ℝ := 10 ^ 6 * (Cp15 * (KAG15 + KAGd15 + 1) + 1) + 1

theorem KW15_pos : 0 < KW15 := by
  rw [KW15]
  have := Cp15_pos
  have := KAG15_pos
  have := KAGd15_pos
  positivity

/-! ## Smoothness of the two factors on the open quadrant -/

theorem smoothOpen_A15' (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => 2 * C15 α θ) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 2 (smoothOpen_C15_bsl α)

theorem smoothOpen_AG15 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (AG15 α Φs) := by
  have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
    (smoothOpen_A15' α) (smoothOpen_G15 hα hα1 hs)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h ?_
  intro z θ _ _ _
  simp [AG15]

theorem smoothOpen_N2ssO {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (N2ssO α Φs) := by
  have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
    (show Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => psi15 z) from smoothOpen_psi15)
    (smoothOpen_AG15 hα hα1 hs)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h ?_
  intro z θ _ _ _
  simp [N2ssO]

/-! ## The `z`-jets of the two factors

The Leibniz inequality `sqm_pz_DthIter_mul_le_4_open` is applied to the pair `(A, G)`; because
`A` is `θ`-only, the `D_z^c`-sum over `A` collapses to `c = 0`. -/
end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow19T2Parts.Eta =====
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

/-- The (`z`-only) Leibniz bound for `K₁₉ = A·H₂`: the `D_θ^b`-derivative always lands on `A`,
and the `∂_z^k`-derivative splits by the binomial rule against `H₂`. -/
theorem K19_pz_Dth_le {α : ℝ} {Φs : Fn}
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs))
    {k b : ℕ} (hk : k ≤ 4) (hb : b ≤ 4) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.pzIter k (Work.Spaces.DthIter b (K19 α Φs)) z θ|
        ≤ 257 * ∑ c ∈ Finset.range (k + 1),
            |Work.Spaces.pzIter c (Work.Spaces.DthIter b (A19 α Φs)) z θ|
              * |deriv^[k - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| := by
  intro z hz θ hθ
  have h := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open k b hk hb
    (A19 α Φs) H2f hAsm smoothOpen_H2f z hz θ hθ
  have h' : |Work.Spaces.pzIter k (Work.Spaces.DthIter b (K19 α Φs)) z θ|
      ≤ 257 * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (b + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a (A19 α Φs)) z θ|
            * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a) H2f) z θ| := by
    rw [show K19 α Φs = (fun z θ => A19 α Φs z θ * H2f z θ) from rfl]
    exact h
  refine h'.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum fun c _ => ?_
  have hH2 : H2f = (fun z θ => Work.FTS.Nonlinear.Open.Row19Prep.H2b z) := rfl
  have hsingle : (∑ a ∈ Finset.range (b + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (A19 α Φs)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a) H2f) z θ|)
      = |Work.Spaces.pzIter c (Work.Spaces.DthIter b (A19 α Φs)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - b) H2f) z θ| :=
    Finset.sum_eq_single b (fun a ha hne => by
      obtain ⟨n, hn⟩ : ∃ n, b - a = n + 1 := by
        rw [Finset.mem_range] at ha
        exact ⟨b - a - 1, by omega⟩
      have hz0 : Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a) H2f) z θ = 0 := by
        rw [hH2, hn, Work.FTS.Nonlinear.Open.Row19Prep.DthIter_succ_z_only
          Work.FTS.Nonlinear.Open.Row19Prep.H2b n]
        exact congrFun (congrFun (pzIter_zero_fun (k - c)) z) θ
      rw [hz0, abs_zero, mul_zero]) (fun hmem => by
        rw [Finset.mem_range] at hmem
        omega)
  rw [hsingle]
  have hb0 : b - b = 0 := by omega
  rw [hb0, Work.Spaces.DthIter_zero, hH2, pzIter_zOnly]

/-- **The (η)-family**: the weighted `∂_z^m`-bound for `Z₁₉`. -/
theorem Z19_eta_bound {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs))
    (hAmem : Work.Spaces.WlInfMem α 4 (A19 α Φs)) {C2 : ℝ}
    (hC2 : ∀ m j : ℕ, m ≤ 4 → j ≤ m → ∀ z : ℝ, 0 < z →
      (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * |deriv^[j] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2)
    (hC2nn : 0 ≤ C2) :
    ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (Z19 α Φs) z θ|
        ≤ 200000 * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by
  intro m hm z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hL0 : 0 ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := WlInf_nonneg' α 4 _ hAmem
  -- `pzIter m Z19 = c19 θ · pzIter m K19`
  have hZeq : Work.Spaces.pzIter m (Z19 α Φs) z θ
      = c19 α θ * Work.Spaces.pzIter m (K19 α Φs) z θ := by
    rw [show Z19 α Φs = (fun z θ => c19 α θ * K19 α Φs z θ) from rfl,
      Work.FTS.H2.pzIter_const_mul]
  have hKleib := K19_pz_Dth_le hAsm hm (by norm_num : (0:ℕ) ≤ 4) z hz θ hθ
  rw [Work.Spaces.DthIter_zero] at hKleib
  -- `|c19 θ| ≤ 10α`
  have hc19 : |c19 α θ| ≤ 10 * α := by
    have hc : (0 : ℝ) < Work.Spaces.c α := by
      have := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hcf : c19 α θ = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ := rfl
    rw [hcf, abs_mul]
    have hk : |α / Work.Spaces.c α| ≤ 10 * α := by
      rw [abs_of_nonneg (div_nonneg hα.le hc.le), div_le_iff₀ hc]
      nlinarith [(Work.Spaces.c_bounds α hα hα1).1]
    have hG1 : |Work.Spaces.Gam α θ| ≤ 1 := by
      rw [abs_of_nonneg (Gam_nonneg' hα hθI)]
      exact Gam_le_one' hα hθI
    calc |α / Work.Spaces.c α| * |Work.Spaces.Gam α θ|
        ≤ (10 * α) * 1 := mul_le_mul hk hG1 (abs_nonneg _) (by positivity)
      _ = 10 * α := by ring
  -- the weight
  have hAw : (1 + z) * Work.Spaces.w z * z ^ m = (1 + z) ^ 3 * z ^ m / z ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
  have hAraw0 : 0 ≤ (1 + z) ^ 3 * z ^ m / z ^ 2 := by positivity
  have h257 : (0 : ℝ) ≤ 257 := by norm_num
  have h5nn : (0 : ℝ) ≤ 5 := by norm_num
  have h10a : (0 : ℝ) ≤ 10 * α := by linarith
  -- termwise bound
  have hterm : ∀ c ∈ Finset.range (m + 1),
      (1 + z) ^ 3 * z ^ m / z ^ 2
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
        ≤ Work.Spaces.WlInf α 4 (A19 α Φs) * C2 := by
    intro c hc
    have hc_le : c ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hc4 : c ≤ 4 := by omega
    have hzc : (0 : ℝ) ≤ (1 + z) ^ c := by positivity
    have hsplit : (1 + z) ^ 3 * z ^ m / z ^ 2
        = (1 + z) ^ c * ((1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c) := by
      have h1 : (0 : ℝ) < 1 + z := by linarith
      have h2 : (0 : ℝ) < (1 + z) ^ c := pow_pos h1 c
      field_simp
    rw [hsplit]
    have h1 : (1 + z) ^ c * ((1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c)
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
        = ((1 + z) ^ c * |Work.Spaces.pzIter c (A19 α Φs) z θ|)
          * ((1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|) := by ring
    rw [h1]
    have hA := Work.Spaces.WlInf_z_bound α 4 (A19 α Φs) hAmem c hc4 z θ hzI hθI
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (z + 1) ^ c by positivity)] at hA
    have hA' : (1 + z) ^ c * |Work.Spaces.pzIter c (A19 α Φs) z θ|
        ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := by
      rw [show (1 : ℝ) + z = z + 1 by ring]
      exact hA
    have hB := hC2 m (m - c) hm (by omega) z hz
    have hmc : m - (m - c) = c := by omega
    rw [hmc] at hB
    have hB' : (1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c
        * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2 := by
      rwa [← hAw]
    have hden0 : 0 ≤ (1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c := by positivity
    have hB0 : 0 ≤ (1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c
        * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| :=
      mul_nonneg hden0 (abs_nonneg _)
    exact mul_le_mul hA' hB' hB0 hL0
  have hsum : (∑ c ∈ Finset.range (m + 1),
        (1 + z) ^ 3 * z ^ m / z ^ 2
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
      ≤ 5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2) := by
    have hs : (∑ c ∈ Finset.range (m + 1),
          (1 + z) ^ 3 * z ^ m / z ^ 2
            * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
        ≤ ∑ _c ∈ Finset.range (m + 1),
            Work.Spaces.WlInf α 4 (A19 α Φs) * C2 := Finset.sum_le_sum hterm
    refine hs.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hL0 hC2nn)
    exact_mod_cast (show m + 1 ≤ 5 by omega)
  have hS0 : 0 ≤ ∑ c ∈ Finset.range (m + 1),
      |Work.Spaces.pzIter c (A19 α Φs) z θ|
        * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| :=
    Finset.sum_nonneg fun c _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKleib' : |Work.Spaces.pzIter m (K19 α Φs) z θ|
      ≤ 257 * ∑ c ∈ Finset.range (m + 1),
          |Work.Spaces.pzIter c (A19 α Φs) z θ|
            * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| := hKleib
  have hstep1 : |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (Z19 α Φs) z θ|
      = ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * (|c19 α θ| * |Work.Spaces.pzIter m (K19 α Φs) z θ|) := by
    rw [hZeq, hAw, abs_mul, abs_of_nonneg hAraw0, abs_mul]
  have hstep2 : ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * (|c19 α θ| * |Work.Spaces.pzIter m (K19 α Φs) z θ|)
      ≤ ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * ((10 * α) * (257 * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))) := by
    refine mul_le_mul_of_nonneg_left ?_ hAraw0
    refine mul_le_mul hc19 ?_ (abs_nonneg _) h10a
    exact hKleib'
  have hstep3 : ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * ((10 * α) * (257 * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)))
      = 10 * α * 257 * (∑ c ∈ Finset.range (m + 1),
          (1 + z) ^ 3 * z ^ m / z ^ 2
            * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)) := by
    rw [show ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * ((10 * α) * (257 * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)))
        = 10 * α * 257 * (((1 + z) ^ 3 * z ^ m / z ^ 2)
            * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)) from by ring,
      Finset.mul_sum]
  have hstep4 : 10 * α * 257 * (∑ c ∈ Finset.range (m + 1),
        (1 + z) ^ 3 * z ^ m / z ^ 2
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
      ≤ 200000 * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by
    refine (mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 10 * α * 257)).trans ?_
    have hαΛ : 0 ≤ α * Work.Spaces.WlInf α 4 (A19 α Φs) := mul_nonneg hα.le hL0
    have hcoef : 10 * α * 257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))
        = 12850 * C2 * (α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by ring
    have hcoef2 : 200000 * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))
        = (200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)))
            * (α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by
      rw [CZ19]; ring
    rw [hcoef, hcoef2]
    have hle : 12850 * C2 ≤ 200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)) := by
      nlinarith [hC2nn, TB19_nonneg]
    exact mul_le_mul_of_nonneg_right hle hαΛ
  exact hstep1.le.trans (hstep2.trans (hstep3.le.trans hstep4))


end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row1 =====
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
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Splits =====
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
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.F0_to_CoefTh =====
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
set_option maxHeartbeats 800000

/-! ## The radial half of the flat class -/

/-- **The radial flat class on the open quadrant**: `|(z+1)^k ∂_z^k g| ≤ K` for `k ≤ m`
and all `(z,θ) ∈ (0,∞) × (0,π/2)`.  This is `Work.FTS.PhiStar.F0` with the angular slot
forgotten. -/
def RadB (m : ℕ) (K : ℝ) (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ k ≤ m, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |(z + 1) ^ k * Work.Spaces.pzIter k g z θ| ≤ K

/-- Monotonicity of `RadB` in the constant. -/
theorem RadB.mono {m : ℕ} {K K' : ℝ} {g : ℝ → ℝ → ℝ} (hK : K ≤ K') (h : RadB m K g) :
    RadB m K' g :=
  fun k hk z θ hz hθ hθ' => le_trans (h k hk z θ hz hθ hθ') hK

/-! ## One step of the product rule for `z ∂_z` -/

/-- **One step**: if `RadB m K g` holds with `m ≥ 1` and `g` is `C^∞` on the open quadrant,
then the radial derivatives of `z ∂_z g` obey the same flat bounds up to order `m - 1`, with
the constant `((m:ℝ)+1)K`.

This is the radial half of `F0_zpz`, with the proof of `F0_zpz` verbatim. -/
theorem RadB_zpz {m : ℕ} (hm : 1 ≤ m) {K : ℝ} {g : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (h : RadB m K g) :
    RadB (m - 1) (((m : ℝ) + 1) * K) (fun z θ => z * Work.Spaces.pz g z θ) := by
  intro k hk z θ hz hθ hθ'
  have hkm : k ≤ m := le_trans hk (Nat.sub_le m 1)
  have hk1 : k + 1 ≤ m := by omega
  have hzk : (0 : ℝ) < z + 1 := by linarith
  -- the `k`-fold product rule for the new function
  have hexp := pzIter_zpz_expand (A := fun z θ => z * Work.Spaces.pz g z θ) (B := g)
    (fun z' θ' _ _ _ => rfl) hg k z θ hz hθ hθ'
  have hb1 : (z + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) g z θ| ≤ K := by
    have h' := h (k + 1) hk1 z θ hz hθ hθ'
    rwa [abs_mul, abs_of_pos (pow_pos hzk (k + 1))] at h'
  have hb0 : (z + 1) ^ k * |Work.Spaces.pzIter k g z θ| ≤ K := by
    have h' := h k hkm z θ hz hθ hθ'
    rwa [abs_mul, abs_of_pos (pow_pos hzk k)] at h'
  have htri : |z * Work.Spaces.pzIter (k + 1) g z θ
        + (k : ℝ) * Work.Spaces.pzIter k g z θ|
      ≤ (z + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
        + (k : ℝ) * |Work.Spaces.pzIter k g z θ| := by
    have h1 : |z * Work.Spaces.pzIter (k + 1) g z θ|
        ≤ (z + 1) * |Work.Spaces.pzIter (k + 1) g z θ| := by
      rw [abs_mul, abs_of_pos hz]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h2 : |(k : ℝ) * Work.Spaces.pzIter k g z θ|
        = (k : ℝ) * |Work.Spaces.pzIter k g z θ| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    calc |z * Work.Spaces.pzIter (k + 1) g z θ
          + (k : ℝ) * Work.Spaces.pzIter k g z θ|
        ≤ |z * Work.Spaces.pzIter (k + 1) g z θ|
          + |(k : ℝ) * Work.Spaces.pzIter k g z θ| := abs_add_le _ _
      _ ≤ (z + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
          + (k : ℝ) * |Work.Spaces.pzIter k g z θ| := by
          rw [h2]; exact add_le_add h1 le_rfl
  rw [hexp, abs_mul, abs_of_pos (pow_pos hzk k)]
  calc (z + 1) ^ k * |z * Work.Spaces.pzIter (k + 1) g z θ
        + (k : ℝ) * Work.Spaces.pzIter k g z θ|
      ≤ (z + 1) ^ k * ((z + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
        + (k : ℝ) * |Work.Spaces.pzIter k g z θ|) :=
        mul_le_mul_of_nonneg_left htri (pow_nonneg hzk.le k)
    _ = (z + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
        + (k : ℝ) * ((z + 1) ^ k * |Work.Spaces.pzIter k g z θ|) := by
        rw [pow_succ]; ring
    _ ≤ K + (k : ℝ) * K :=
        add_le_add hb1 (mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg k))
    _ ≤ ((m : ℝ) + 1) * K := by
        have hkm' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
        nlinarith [hK]

/-! ## Iterating the step: `D_z^b` is controlled by the flat data -/

/-- **`D_z^b` is controlled by the radial flat data.**  If `RadB m K g` holds and `g` is
`C^∞` on the open quadrant, then for every `b ≤ m` the iterate `D_z^b g` obeys the radial flat
bounds up to order `m - b` with the constant `((m:ℝ)+1)^b K`. -/
theorem RadB_DzIter {m : ℕ} {K : ℝ} {g : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ b ≤ m, RadB m K g → RadB (m - b) (((m : ℝ) + 1) ^ b * K) (Work.Spaces.DzIter b g) := by
  intro b
  induction b with
  | zero =>
      intro _ h
      simpa using h
  | succ b ih =>
      intro hb h
      have hbm : b ≤ m := by omega
      have hrec : RadB (m - b) (((m : ℝ) + 1) ^ b * K) (Work.Spaces.DzIter b g) := ih hbm h
      have hm1 : 1 ≤ m - b := by omega
      have hKb : 0 ≤ ((m : ℝ) + 1) ^ b * K := mul_nonneg (pow_nonneg (by positivity) b) hK
      have hstep := RadB_zpz hm1 hKb (hg.DzIter b) hrec
      have hsub : m - (b + 1) = m - b - 1 := by omega
      rw [hsub]
      refine RadB.mono ?_ hstep
      have hle : (((m - b : ℕ) : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
        have : ((m - b : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m b
        linarith
      calc (((m - b : ℕ) : ℝ) + 1) * (((m : ℝ) + 1) ^ b * K)
          ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ b * K) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg (pow_nonneg (by positivity) b) hK)
        _ = ((m : ℝ) + 1) ^ (b + 1) * K := by rw [pow_succ]; ring

/-! ## The bridge to `CoefTh` -/

/-- Auxiliary exponent identity. -/
private theorem pow_two_mul_pow (a : ℝ) (n : ℕ) : a ^ 2 * a ^ n = a ^ (n + 2) := by
  rw [← pow_add]
  congr 1
  omega

theorem F0_to_CoefTh (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (f : ℝ → ℝ → ℝ), 0 ≤ K → Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.PhiStar.F0 n K (Work.Spaces.pth f) → Work.FTS.VocabO.CoefThMem n f ∧ Work.FTS.VocabO.CoefTh n f ≤ C * K := by
  refine ⟨((n : ℝ) + 1) ^ (n + 2) + 1, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 2) := pow_nonneg (by positivity) _
    linarith
  intro K f hK hsf hf
  -- the pointwise bound on every slot of the coefficient norm
  have key : ∀ b i : ℕ, b + i ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ ((n : ℝ) + 1) ^ n * K := by
    intro b i hbi z θ hz hθ hθ'
    have hbm : b ≤ n - i := by omega
    have hrad : RadB (n - i) K (Work.Spaces.DthIter i (Work.Spaces.pth f)) := by
      intro k hk z' θ' hz' hθ' hθ''
      exact hf k i (by omega) z' θ' hz' hθ' hθ''
    have hDz := RadB_DzIter (m := n - i) (K := K)
      (g := Work.Spaces.DthIter i (Work.Spaces.pth f)) hK ((hsf.pth).DthIter i) b hbm hrad
    have h0 := hDz 0 (Nat.zero_le _) z θ hz hθ hθ'
    simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul] at h0
    refine h0.trans ?_
    have hbase : (((n - i : ℕ) : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : ((n - i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n i
      linarith
    have h2 : (((n - i : ℕ) : ℝ) + 1) ^ b ≤ ((n : ℝ) + 1) ^ b :=
      pow_le_pow_left₀ (by positivity) hbase b
    have h3 : ((n : ℝ) + 1) ^ b ≤ ((n : ℝ) + 1) ^ n :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) (by omega)
    exact mul_le_mul_of_nonneg_right (h2.trans h3) hK
  refine ⟨fun b i hbi => ⟨((n : ℝ) + 1) ^ n * K, fun z θ hz hθ hθ' =>
    key b i hbi z θ hz hθ hθ'⟩, ?_⟩
  have hterm : ∀ b ∈ Finset.range (n + 1), ∀ i ∈ Finset.range (n + 1),
      (if b + i ≤ n then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
        else 0) ≤ ((n : ℝ) + 1) ^ n * K := by
    intro b _ i _
    split_ifs with hbi
    · exact Work.FTS.H2.supAbsO_le (fun z θ hz hθ hθ' => key b i hbi z θ hz hθ hθ')
    · exact mul_nonneg (pow_nonneg (by positivity) n) hK
  calc Work.FTS.VocabO.CoefTh n f
      = ∑ b ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
          (if b + i ≤ n then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
            else 0) := rfl
    _ ≤ ∑ b ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
          ((n : ℝ) + 1) ^ n * K :=
        Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun i hi => hterm b hb i hi
    _ = ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1) ^ n * K) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((n : ℝ) + 1) ^ (n + 2) * K := by
        rw [← mul_assoc, pow_two_mul_pow]
    _ ≤ (((n : ℝ) + 1) ^ (n + 2) + 1) * K :=
        mul_le_mul_of_nonneg_right (by linarith) hK

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.fields_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The substituted unknown `Ψ` and the auxiliary function `sin 2θ · Ψ` -/

/-- `Ψ = (z/(z+1))·Ŷ`; on the open quadrant `sin 2θ · Ψ = Φ̃_*` and `Ψ = (z/(z+1))·Φ̆`. -/
abbrev fiSubs (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => z / (z + 1) * Work.FTS.VocabO2.Ycheck α Φs z θ

/-- `sin 2θ · Ψ`: the function to which the `sin 2θ`-substitution identities apply. -/
abbrev fiPsiF (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Real.sin (2 * θ) * fiSubs α Φs z θ

/-! ## Elementary facts on the open quadrant -/

theorem fi_sin_two_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

theorem fi_cos_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-! ## Locality of `∂_z`, `∂_θ` on the open quadrant -/

theorem fi_pz_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_left θ).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hs : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h z' θ hz'.1 hz'.2.1 hz'.2.2
  simp only [Work.Spaces.pz]
  exact hs.deriv_eq

theorem fi_pth_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' hz hθ'.1 hθ'.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

/-! ## The pointwise identity `sin 2θ · Ψ = Φ̃_*` on the open quadrant -/

theorem fi_PsiF_eq_phi {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ := by
  have hs : Real.sin (2 * θ) ≠ 0 := fi_sin_two_ne_zero ⟨hθ0, hθ1⟩
  simp only [fiPsiF, fiSubs, Work.FTS.VocabO2.Ycheck, Work.Construction.s2]
  field_simp

/-! ## Transporting `ℛ`, `𝒱`, `𝒰` from `Φ̃_*` to `sin 2θ · Ψ` -/

theorem fi_Rop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.Construction.Rop α (fiPsiF α Φs) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  have h1 := fi_pz_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h2 := fi_pth_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h3 := hloc z θ hz hθ.1 hθ.2
  simp only [Work.Construction.Rop, ← h1, ← h2, h3]

theorem fi_Vop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.Construction.Vop (fiPsiF α Φs) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  have h2 := fi_pth_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h3 := hloc z θ hz hθ.1 hθ.2
  simp only [Work.Construction.Vop, ← h2, h3]

theorem fi_Uop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.Construction.Uop α (fiPsiF α Φs) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  have h1 := fi_pz_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ
  have h3 := hloc z θ hz hθ.1 hθ.2
  simp only [Work.Construction.Uop, ← h1, h3]

theorem fi_pth_Uop_transfer {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) z θ
      = Work.Spaces.pth (Work.Construction.Uop α (fiPsiF α Φs)) z θ := by
  have hloc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      fiPsiF α Φs z θ = Work.FTS.VocabO2.PhiTs α Φs z θ :=
    fun z θ hz h0 h1 => fi_PsiF_eq_phi hz h0 h1
  refine fi_pth_congr (f := Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))
    (g := Work.Construction.Uop α (fiPsiF α Φs)) ?_ hz hθ
  intro z θ hz h0 h1
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h0, h1⟩
  have h1' := fi_pz_congr (f := fiPsiF α Φs) (g := Work.FTS.VocabO2.PhiTs α Φs) hloc hz hθ'
  have h3 := hloc z θ hz h0 h1
  simp only [Work.Construction.Uop, ← h1', ← h3]

/-! ## `SmoothOpen` of `z/(z+1)` and of `Ψ` -/

theorem fi_smoothOpen_selfun :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => z / (z + 1)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h : Function.uncurry (fun z θ : ℝ => z / (z + 1))
      = fun p : ℝ × ℝ => p.1 / (p.1 + 1) := rfl
  rw [h]
  exact ContDiffOn.div contDiffOn_fst (contDiffOn_fst.add contDiffOn_const)
    (fun p hp => by
      have hz := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      positivity)

theorem fi_smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [h]
  exact (hf.forall n).mul (hg.forall n)

theorem fi_smoothOpen_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs)) :
    Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) :=
  fi_smoothOpen_mul fi_smoothOpen_selfun hY

/-- The `θ`-slice of `Ψ` is differentiable at an interior angle (from `SmoothOpen`). -/
theorem fi_diffAt_theta_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => fiSubs α Φs z θ') θ :=
  ((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-! ## The two product rules for `Ψ = (z/(z+1))·Ŷ` -/

/-- `∂_θΨ = (z/(z+1))·∂_θŶ` (the coefficient is constant in `θ`). -/
theorem fi_pth_Subs_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    Work.Spaces.pth (fiSubs α Φs) z θ
      = z / (z + 1) * Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  simp only [Work.Spaces.pth, fiSubs]
  exact deriv_const_mul_field (z / (z + 1))

/-- The same identity, at the level of functions. -/
theorem fi_pth_Subs (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) :
    Work.Spaces.pth (fiSubs α Φs)
      = fun z θ => z / (z + 1) * Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  funext z θ
  exact fi_pth_Subs_apply α Φs z θ

theorem fi_hasDerivAt_zdiv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => z' / (z' + 1)) (1 / (z + 1) ^ 2) z := by
  have h : HasDerivAt (fun z' : ℝ => z' / (z' + 1))
      ((1 * (z + 1) - z * 1) / (z + 1) ^ 2) z :=
    (hasDerivAt_id z).div ((hasDerivAt_id z).add_const 1) (by linarith)
  convert h using 1
  ring

/-- Product rule for the multiplier `z/(z+1)`. -/
theorem fi_pz_zdiv_mul {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hF : HasDerivAt (fun z' : ℝ => F z' θ) (Work.Spaces.pz F z θ) z) :
    Work.Spaces.pz (fun z θ => z / (z + 1) * F z θ) z θ
      = 1 / (z + 1) ^ 2 * F z θ + z / (z + 1) * Work.Spaces.pz F z θ := by
  have hmul := (fi_hasDerivAt_zdiv hz).mul hF
  simp only [Work.Spaces.pz]
  exact hmul.deriv

/-- `∂_zΨ = (1/(z+1)²)Ŷ + (z/(z+1))·∂_zŶ`. -/
theorem fi_pz_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (fiSubs α Φs) z θ
      = 1 / (z + 1) ^ 2 * Work.FTS.VocabO2.Ycheck α Φs z θ
        + z / (z + 1) * Work.Spaces.pz (Work.FTS.VocabO2.Ycheck α Φs) z θ :=
  fi_pz_zdiv_mul hz (hY.hasDerivAt_slice hθ hz)

/-- `∂_θ(D_zΨ) = (z/(z+1))·(∂_θŶ/(z+1) + z·∂_z∂_θŶ)` (Clairaut + product rule). -/
theorem fi_pth_Dz_Subs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.Dz (fiSubs α Φs)) z θ
      = z / (z + 1) * (Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs) z θ / (z + 1)
          + z * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.VocabO2.Ycheck α Φs)) z θ) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry (fiSubs α Φs)) (z, θ) :=
    (hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  -- `∂_θ(D_zΨ) = z·∂_θ(∂_zΨ)`
  have h1 : Work.Spaces.pth (Work.Spaces.Dz (fiSubs α Φs)) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz (fiSubs α Φs)) z θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pth]
    exact deriv_const_mul_field z
  rw [h1, (Work.Spaces.pz_pth_comm hcd).symm]
  -- `∂_z(∂_θΨ) = ∂_z((z/(z+1))·∂_θŶ)`
  rw [fi_pth_Subs]
  rw [fi_pz_zdiv_mul hz ((hY.pth).hasDerivAt_slice hθ hz)]
  field_simp
  try ring

/-! ## The `∂_θ`-substitution identity for `𝒰`, without the unused `∀θ'`-hypothesis -/

theorem fi_pth_Uop_sin_two_mul (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : DifferentiableAt ℝ (fun θ' => Φ z θ') θ)
    (hzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz Φ z θ') θ) :
    Work.Spaces.pth (Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ)) z θ
      = -(2 * Real.cos (2 * θ) * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)
          + Real.sin (2 * θ) * (3 * Work.Spaces.pth Φ z θ
            + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ)) := by
  have hU : (fun θ' : ℝ =>
        Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ')
      = fun θ' => -(Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')) := by
    funext θ'
    exact Work.FTS.H2.StarPkg.Uop_sin_two_mul α Φ z θ'
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have hinner : HasDerivAt (fun θ' : ℝ => 3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')
      (3 * Work.Spaces.pth Φ z θ + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Φ z θ') (Work.Spaces.pth Φ z θ) θ := hθ.hasDerivAt
    have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.Dz Φ z θ')
        (Work.Spaces.pth (Work.Spaces.Dz Φ) z θ) θ := hzθ.hasDerivAt
    exact ((h1.const_mul 3).add (h2.const_mul α))
  have hprod : HasDerivAt
      (fun θ' : ℝ => Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ'))
      (Real.cos (2 * θ) * 2 * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)
        + Real.sin (2 * θ) * (3 * Work.Spaces.pth Φ z θ
          + α * Work.Spaces.pth (Work.Spaces.Dz Φ) z θ)) θ :=
    hsin2'.mul hinner
  rw [Work.Spaces.pth, hU]
  have hneg : (fun θ' : ℝ => -(Real.sin (2 * θ')
        * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ'))) = -(fun θ' : ℝ =>
      Real.sin (2 * θ') * (3 * Φ z θ' + α * Work.Spaces.Dz Φ z θ')) := by
    funext θ'; rfl
  rw [hneg, deriv.neg, hprod.deriv]
  simp only [Work.Spaces.Dz]
  ring_nf

/-! ## The six identities -/

theorem fi_EH {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.FTS.PhiStar.EH α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hcos := fi_cos_ne_zero hθ
  rw [fi_Rop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Rop_sin_two_mul α (fiSubs α Φs) z θ hcos hdθ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ, fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EH, Work.FTS.PhiStar.Tblk, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EV {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.FTS.PhiStar.EV (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hcos := fi_cos_ne_zero hθ
  rw [fi_Vop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Vop_sin_two_mul (fiSubs α Φs) z θ hcos hdθ]
  rw [fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EV, Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EVz {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = Work.FTS.PhiStar.EVz (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hcos := fi_cos_ne_zero hθ
  rw [fi_Vop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Vop_sin_two_mul (fiSubs α Φs) z θ hcos hdθ]
  rw [fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EU {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ
      = Work.FTS.PhiStar.EU α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hs2 := fi_sin_two_ne_zero hθ
  rw [fi_Uop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Uop_sin_two_mul α (fiSubs α Φs) z θ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ]
  simp only [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EUz {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)
      = Work.FTS.PhiStar.EUz α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hs2 := fi_sin_two_ne_zero hθ
  rw [fi_Uop_transfer hz hθ]
  rw [Work.FTS.H2.StarPkg.Uop_sin_two_mul α (fiSubs α Φs) z θ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ]
  simp only [Work.FTS.PhiStar.EUz, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

theorem fi_EPU {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) z θ
      = Work.FTS.PhiStar.EPU α (Work.FTS.VocabO2.Ycheck α Φs) z θ := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fiSubs α Φs) := fi_smoothOpen_Subs hY
  have hdθ := fi_diffAt_theta_Subs hsm hz hθ
  have hdθ₂ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz (fiSubs α Φs) z θ') θ :=
    (((hsm.Dz).curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  rw [fi_pth_Uop_transfer hz hθ]
  rw [fi_pth_Uop_sin_two_mul α (fiSubs α Φs) z θ hdθ hdθ₂]
  rw [fi_pth_Dz_Subs hY hz hθ]
  simp only [Work.Spaces.Dz]
  rw [fi_pz_Subs hY hz hθ, fi_pth_Subs_apply]
  simp only [Work.FTS.PhiStar.EPU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, fiSubs,
    Work.Construction.s2]
  field_simp
  try ring

/-! ## The target -/

theorem fields_ident {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen Φs) : (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ = Work.FTS.PhiStar.EH α (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = Work.FTS.PhiStar.EV (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = Work.FTS.PhiStar.EVz (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ = Work.FTS.PhiStar.EU α (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) = Work.FTS.PhiStar.EUz α (Work.FTS.VocabO2.Ycheck α Φs) z θ) ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) z θ = Work.FTS.PhiStar.EPU α (Work.FTS.VocabO2.Ycheck α Φs) z θ) := by
  obtain ⟨-, -, hY⟩ := smoothOpen_PhiTs hα hα1 hsm
  exact ⟨fun z θ hz h0 h1 => fi_EH hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EV hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EVz hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EU hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EUz hY hz ⟨h0, h1⟩,
    fun z θ hz h0 h1 => fi_EPU hY hz ⟨h0, h1⟩⟩

end

end Work.FTS.PhiStar.CoreAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.fields_vanish =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/PhiStar/CoreAux/fields_vanish.lean` — the fields vanish off the open quadrant

`PhiTs α Φs = Φ̃_*` is extended by `0` off the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`StarCore.zeroOff`).  The transport coefficients `Rop, Vop, Uop` of `Work.Construction`
are built from `Ψ`, `∂_zΨ` and `∂_θΨ`; because the vanishing of `Φ̃_*` holds on a whole
half-plane in each variable, its *derivatives* vanish too at every point off `Q0`, and the
same then holds for every expression built from them.  Here we record that for all ten
fields consumed by `CoreAux/Assembly.lean` (`F0c_of_boundary`).

The analytic input is the "one-sided" fact for `deriv` in the sibling files
`CoreAux/iterate_deriv_eq_zero_of_eqOn_Iic.deriv_eq_zero_of_eqOn_Iic'` and
`CoreAux/iterate_deriv_eq_zero_of_eqOn_Ici.deriv_eq_zero_of_eqOn_Ici'`: a function vanishing
on `Iic a` (resp. `Ici a`) has derivative `0` at every point of that half-line (the right
half is needed at the edge `θ = π/2` of the quadrant).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The off-quadrant condition -/

/-- The disjunction `z ≤ 0 ∨ θ ≤ 0 ∨ π/2 ≤ θ` puts the point outside the open quadrant. -/
theorem not_mem_Q0_of {z θ : ℝ} (h : z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) :
    ¬ ((z, θ) ∈ Work.FTS.EllipticEst.Q0) := by
  rw [Work.FTS.EllipticEst.Q0]
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  rintro ⟨hz, hθ0, hθ1⟩
  rcases h with h | h | h
  · exact absurd hz (not_lt.mpr h)
  · exact absurd hθ0 (not_lt.mpr h)
  · exact absurd h (not_le.mpr hθ1)

/-! ## Derivatives of a function vanishing off the quadrant

The hypothesis is exactly the shape of the pointwise vanishing consumed by
`CoreAux/Assembly.lean`: `f` is `0` at every point of the closed complement of the open
quadrant, **slicewise** (the same `f`, not just its values).  Then `pz f` and `pth f`
vanish there as well: along the variable that is fixed, `f` is `0` on a half-line, and the
only possibly non-local point `z = 0` (resp. `θ = 0`) is handled by the `Iic` lemma. -/

/-- If `f` vanishes off the open quadrant then so does `pz f = ∂_z f`. -/
theorem pz_eq_zero_of_vanishing {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → f z θ = 0) :
    ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pz f z θ = 0 := by
  intro z θ h
  simp only [Work.Spaces.pz]
  by_cases hθ : 0 < θ ∧ θ < Real.pi / 2
  · -- `0 < θ < π/2`, so the disjunction forces `z ≤ 0`: the `z`-slice vanishes on `Iic 0`
    have hz : z ≤ 0 := by
      rcases h with h | h | h
      · exact h
      · exact absurd hθ.1 (not_lt.mpr h)
      · exact absurd h (not_le.mpr hθ.2)
    exact deriv_eq_zero_of_eqOn_Iic' (f := fun z' => f z' θ)
      (fun y hy => hf y θ (Or.inl hy)) z hz
  · -- the whole `z`-slice vanishes
    have hzero : ∀ z' : ℝ, f z' θ = 0 := by
      intro z'
      rcases not_and_or.mp hθ with h1 | h2
      · exact hf z' θ (Or.inr (Or.inl (not_lt.mp h1)))
      · exact hf z' θ (Or.inr (Or.inr (not_lt.mp h2)))
    rw [show (fun z' => f z' θ) = fun _ => (0 : ℝ) from funext hzero]
    simp

/-- If `f` vanishes off the open quadrant then so does `pth f = ∂_θ f`. -/
theorem pth_eq_zero_of_vanishing {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → f z θ = 0) :
    ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth f z θ = 0 := by
  intro z θ h
  simp only [Work.Spaces.pth]
  by_cases hθ : θ ≤ 0
  · exact deriv_eq_zero_of_eqOn_Iic' (f := fun θ' => f z θ')
      (fun y hy => hf z y (Or.inr (Or.inl hy))) θ hθ
  · have hθ' : 0 < θ := not_le.mp hθ
    by_cases h2 : Real.pi / 2 ≤ θ
    · exact deriv_eq_zero_of_eqOn_Ici' (f := fun θ' => f z θ')
        (fun y hy => hf z y (Or.inr (Or.inr hy))) θ h2
    · -- `0 < θ < π/2`, so the disjunction forces `z ≤ 0`: the `θ`-slice vanishes entirely
      have h2' : θ < Real.pi / 2 := not_le.mp h2
      have hz : z ≤ 0 := by
        rcases h with h | h | h
        · exact h
        · exact absurd h (not_le.mpr hθ')
        · exact absurd h (not_le.mpr h2')
      have hzero : ∀ θ' : ℝ, f z θ' = 0 := fun θ' => hf z θ' (Or.inl hz)
      rw [show (fun θ' => f z θ') = fun _ => (0 : ℝ) from funext hzero]
      simp

/-! ## The ten fields -/

theorem fields_vanish {α Cs : ℝ} (hα : 0 < α) {Φs : Work.FTS.Galerkin.Fn} (hcore : Work.FTS.VocabO2.StarCore α Cs Φs) : (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) z θ = 0) ∧ (∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Work.Spaces.pth (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)) z θ = 0) := by
  set Ψ : ℝ → ℝ → ℝ := Work.FTS.VocabO2.PhiTs α Φs with hΨdef
  -- pointwise vanishing of `Ψ = Φ̃_*`
  have hΨ : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) → Ψ z θ = 0 := by
    intro z θ h
    rw [hΨdef]
    exact hcore.zeroOff z θ (not_mem_Q0_of h)
  have hpz := pz_eq_zero_of_vanishing hΨ
  have hpth := pth_eq_zero_of_vanishing hΨ
  -- pointwise vanishing of the five basic fields
  have hR : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      (z + 1) / z * Work.Construction.Rop α Ψ z θ = 0 := by
    intro z θ h
    simp [Work.Construction.Rop, hΨ z θ h, hpz z θ h, hpth z θ h]
  have hV : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      Work.Construction.Vop Ψ z θ = 0 := by
    intro z θ h
    simp [Work.Construction.Vop, hΨ z θ h, hpth z θ h]
  have hVz : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      (z + 1) / z * Work.Construction.Vop Ψ z θ = 0 := by
    intro z θ h
    rw [hV z θ h, mul_zero]
  have hU : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ = 0 := by
    intro z θ h
    have h1 : Work.Construction.Uop α Ψ z θ = 0 := by
      simp [Work.Construction.Uop, hΨ z θ h, hpz z θ h]
    rw [h1, zero_div]
  have hUz : ∀ z θ : ℝ, (z ≤ 0 ∨ θ ≤ 0 ∨ Real.pi / 2 ≤ θ) →
      (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) = 0 := by
    intro z θ h
    rw [hU z θ h, mul_zero]
  exact ⟨hR, hV, hVz, hU, hUz,
    pth_eq_zero_of_vanishing hR, pth_eq_zero_of_vanishing hV,
    pth_eq_zero_of_vanishing hVz, pth_eq_zero_of_vanishing hU,
    pth_eq_zero_of_vanishing hUz⟩

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.CoeffF0 =====
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

/-! ## `θ`-independent data

For `f z θ = c z` the angular operator `D_θ = sin(2θ)∂_θ` kills everything from order one on,
and the radial part is the ordinary iterated derivative of `c`. -/

/-- The `D_θ`-iterate of the zero function is again zero. -/
theorem Dth_zero_fun : Work.Spaces.Dth (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ
  simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- **`D_θ^{i+1}` of a `θ`-independent function vanishes identically.**

The `θ`-slice of such a function is constant, so its derivative is `0`; from the second
order on the function is already zero, so all further `D_θ`-iterates vanish too. -/
theorem DthIter_succ_eq_zero_of_theta_indep {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ θ', f z θ = f z θ') (i : ℕ) :
    Work.Spaces.DthIter (i + 1) f = fun _ _ => 0 := by
  induction i with
  | zero =>
    funext z θ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    rw [Work.Spaces.Dth, Work.Spaces.pth]
    rw [show (fun θ' => f z θ') = fun _ => f z 0 from funext (fun θ' => hf z θ' 0),
      deriv_const, mul_zero]
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih, Dth_zero_fun]

/-- **`D_θ^i` of a `θ`-independent function vanishes** for `i ≥ 1`. -/
theorem DthIter_eq_zero_of_theta_indep {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ θ', f z θ = f z θ') {i : ℕ} (hi : 1 ≤ i) :
    Work.Spaces.DthIter i f = fun _ _ => 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact DthIter_succ_eq_zero_of_theta_indep hf j

/-- Every `z`-iterate of the zero function vanishes. -/
theorem pzIter_zero_fun (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv k (fun _ _ : ℝ => (0 : ℝ)) z θ]
  exact Work.Spaces.iteratedDeriv_zero_fun k z

/-- **A `z`-only coefficient belongs to the flat class as soon as its weighted iterated
derivatives are bounded.**

If `|(z+1)^k ∂_z^k c z| ≤ A` for all `k ≤ n` and `z > 0`, then
`F0 n A (fun z _ => c z)`: the slots with an angular derivative vanish, and the purely radial
slots are the weighted iterated derivatives of `c`. -/
theorem F0_of_iteratedDeriv_bound {n : ℕ} {A : ℝ} {c : ℝ → ℝ}
    (hc : ∀ k ≤ n, ∀ z : ℝ, 0 < z → |(z+1)^k * iteratedDeriv k c z| ≤ A) :
    Work.FTS.PhiStar.F0 n A (fun z _ => c z) := by
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rw [Work.Spaces.DthIter_zero, Work.Spaces.pzIter_eq_iteratedDeriv k (fun z _ => c z) z θ]
    exact hc k hki z hz
  · rw [DthIter_eq_zero_of_theta_indep (f := fun z _ => c z) (fun z θ θ' => rfl) hipos,
        pzIter_zero_fun, mul_zero, abs_zero]
    exact le_trans (abs_nonneg _) (hc 0 (Nat.zero_le n) z hz)

/-! ## The two radial coefficients -/

/-- **The `k`-th derivative of `(1+z)⁻¹`.**

On `(-1,∞)`, `∂_z^k (1+z)⁻¹ = (-1)^k k! (1+z)^{-(k+1)}`.  The proof is an induction on `k`:
the induction hypothesis identifies the `k`-th derivative near `z` with the explicit
expression (`Filter.EventuallyEq.iteratedDeriv`), whose derivative is computed by the chain
rule (`HasDerivAt.inv`, `HasDerivAt.fun_pow`). -/
theorem iteratedDeriv_inv_one_add (k : ℕ) :
    ∀ z : ℝ, -1 < z →
      iteratedDeriv k (fun z : ℝ => (1 + z)⁻¹) z
        = (-1 : ℝ) ^ k * (k.factorial : ℝ) * ((1 + z)⁻¹) ^ (k + 1) := by
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    have hne : (1 : ℝ) + z ≠ 0 := by linarith
    rw [iteratedDeriv_succ]
    have hcongr : iteratedDeriv k (fun y : ℝ => (1 + y)⁻¹) =ᶠ[𝓝 z]
        (fun y : ℝ => (-1 : ℝ) ^ k * (k.factorial : ℝ) * ((1 + y)⁻¹) ^ (k + 1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih y hy
    rw [hcongr.deriv_eq]
    have h1 : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-(((1 : ℝ) + z)⁻¹) ^ 2) z := by
      have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) + y) 1 z := by
        simpa using (hasDerivAt_id z).const_add (1 : ℝ)
      have h3 : HasDerivAt (fun y : ℝ => ((1 : ℝ) + y)⁻¹) (-(((1 + z) ^ 2)⁻¹) * 1) z :=
        (hasDerivAt_inv hne).comp z h2
      simpa [mul_one, inv_pow] using h3
    have h4 : HasDerivAt (fun y : ℝ => ((1 + y)⁻¹) ^ (k + 1))
        (((k : ℝ) + 1) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))) z := by
      have := h1.fun_pow (k + 1)
      simpa using this
    have h5 := h4.const_mul ((-1 : ℝ) ^ k * (k.factorial : ℝ))
    rw [h5.deriv]
    have hpow : ((k : ℝ) + 1) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))
        = -(((k : ℝ) + 1) * ((1 + z)⁻¹) ^ (k + 2)) := by
      have hA : ((k : ℝ) + 1) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))
          = -(((k : ℝ) + 1) * (((1 + z)⁻¹) ^ k * ((1 + z)⁻¹) ^ 2)) := by ring
      rw [hA, ← pow_add]
    rw [hpow]
    have hfac : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hneg : (-1 : ℝ) ^ (k + 1) = (-1 : ℝ) ^ k * (-1) := by rw [pow_succ]
    rw [hneg, hfac]
    ring

/-- **The weighted inverse power.**  For `z > -1` and every `k`,
`(z+1)^k (1+z)^{-(k+1)} = (1+z)⁻¹`. -/
theorem weighted_inv (k : ℕ) (z : ℝ) (hz : -1 < z) :
    (z + 1) ^ k * (((1 + z)⁻¹) ^ (k + 1)) = (1 + z)⁻¹ := by
  have h1 : z + 1 = 1 + z := by ring
  rw [h1]
  have hne : (1 : ℝ) + z ≠ 0 := by linarith
  have hk : ((1 : ℝ) + z) ^ k ≠ 0 := pow_ne_zero k hne
  rw [inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ hk, one_mul]

/-- **The weighted derivative slots of `(1+z)⁻¹`.**  They are all equal to `± k! /(1+z)`. -/
theorem weighted_iteratedDeriv_inv (k : ℕ) (z : ℝ) (hz : -1 < z) :
    (z + 1) ^ k * iteratedDeriv k (fun z : ℝ => (1 + z)⁻¹) z
      = (-1 : ℝ) ^ k * (k.factorial : ℝ) * (1 + z)⁻¹ := by
  rw [iteratedDeriv_inv_one_add k z hz]
  have hstep : (z + 1) ^ k * ((-1 : ℝ) ^ k * (k.factorial : ℝ) * (((1 + z)⁻¹) ^ (k + 1)))
      = (-1 : ℝ) ^ k * (k.factorial : ℝ) * ((z + 1) ^ k * (((1 + z)⁻¹) ^ (k + 1))) := by
    ring
  rw [hstep, weighted_inv k z hz]

/-- **The weighted derivative slots of `z/(1+z)`**, for `k ≥ 1`.

On `(-1,∞)` one has `z/(1+z) = 1 - (1+z)⁻¹`; the constant `1` has no derivatives of order
`≥ 1`, so the slots are minus those of `(1+z)⁻¹`. -/
theorem weighted_iteratedDeriv_div (k : ℕ) (hk : 1 ≤ k) (z : ℝ) (hz : -1 < z) :
    (z + 1) ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z
      = (-1 : ℝ) ^ (k + 1) * (k.factorial : ℝ) * (1 + z)⁻¹ := by
  have heq : Set.EqOn (fun z : ℝ => z / (1 + z)) (fun z : ℝ => 1 - (1 + z)⁻¹)
      (Set.Ioi (-1)) := by
    intro y hy
    have hy' : (-1 : ℝ) < y := hy
    have hne : (1 : ℝ) + y ≠ 0 := by linarith
    field_simp
    ring
  rw [heq.iteratedDeriv_of_isOpen isOpen_Ioi k hz]
  rw [iteratedDeriv_const_sub (n := k) (by omega : 0 < k) (1 : ℝ)]
  simp only [iteratedDeriv_neg]
  rw [iteratedDeriv_inv_one_add k z hz]
  have hstep : (z + 1) ^ k * (-((-1 : ℝ) ^ k * (k.factorial : ℝ) * (((1 + z)⁻¹) ^ (k + 1))))
      = -((-1 : ℝ) ^ k * (k.factorial : ℝ) * ((z + 1) ^ k * (((1 + z)⁻¹) ^ (k + 1)))) := by
    ring
  rw [hstep, weighted_inv k z hz, pow_succ]
  ring

/-! ## The two radial coefficients are in `F0 6`, with the common constant `720` -/

/-- `(1+z)⁻¹ ∈ F0 6` with the universal constant `720` (`= 6!`). -/
theorem F0_inv_one_add : Work.FTS.PhiStar.F0 6 720 (fun z _ => (1 + z)⁻¹) := by
  apply F0_of_iteratedDeriv_bound
  intro k hk z hz
  have hz' : -1 < z := by linarith
  rw [weighted_iteratedDeriv_inv k z hz']
  have hHpos : 0 < (1 + z)⁻¹ := by positivity
  have hHle : (1 + z)⁻¹ ≤ 1 := by
    have h1z : (1 : ℝ) ≤ 1 + z := by linarith
    exact inv_le_one_of_one_le₀ h1z
  have habs : |(-1 : ℝ) ^ k * (k.factorial : ℝ) * (1 + z)⁻¹|
      = (k.factorial : ℝ) * (1 + z)⁻¹ := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)), abs_of_nonneg hHpos.le]
  rw [habs]
  have hfac : (k.factorial : ℝ) ≤ 720 := by interval_cases k <;> norm_num
  calc (k.factorial : ℝ) * (1 + z)⁻¹ ≤ 720 * 1 :=
        mul_le_mul hfac hHle hHpos.le (by norm_num)
    _ = 720 := by norm_num

/-- `z/(1+z) ∈ F0 6` with the universal constant `720` (`= 6!`); the slot `k = 0` is
`z/(1+z) ∈ [0,1]` for `z > 0`. -/
theorem F0_div_one_add : Work.FTS.PhiStar.F0 6 720 (fun z _ => z / (1 + z)) := by
  apply F0_of_iteratedDeriv_bound
  intro k hk z hz
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [pow_zero, one_mul, iteratedDeriv_zero]
    have h1z : 0 < 1 + z := by linarith
    have hle : z / (1 + z) ≤ 1 := by
      rw [div_le_one h1z]; linarith
    have hge : 0 ≤ z / (1 + z) := div_nonneg hz.le h1z.le
    rw [abs_of_nonneg hge]
    linarith
  · rw [weighted_iteratedDeriv_div k hkpos z (by linarith)]
    have hHpos : 0 < (1 + z)⁻¹ := by positivity
    have hHle : (1 + z)⁻¹ ≤ 1 := by
      have h1z : (1 : ℝ) ≤ 1 + z := by linarith
      exact inv_le_one_of_one_le₀ h1z
    have habs : |(-1 : ℝ) ^ (k + 1) * (k.factorial : ℝ) * (1 + z)⁻¹|
        = (k.factorial : ℝ) * (1 + z)⁻¹ := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)), abs_of_nonneg hHpos.le]
    rw [habs]
    have hfac : (k.factorial : ℝ) ≤ 720 := by interval_cases k <;> norm_num
    calc (k.factorial : ℝ) * (1 + z)⁻¹ ≤ 720 * 1 :=
          mul_le_mul hfac hHle hHpos.le (by norm_num)
      _ = 720 := by norm_num

/-! ## The assembly -/

/-- **All six coefficient functions of the `StarPkgo2` assembly lie in `F0 6` for a single
constant `A ≥ 1`.**  The four angular coefficients come from
`CoreAux.F0_theta_coefs 6` (constant `C > 0`), the two radial ones from `F0_div_one_add` and
`F0_inv_one_add` (constant `720`), and `A = C + 720 + 1` dominates both. -/
theorem CoeffF0 : ∃ A : ℝ, 1 ≤ A ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) := by
  obtain ⟨C, hCpos, h1, h2, h3, h4⟩ := Work.FTS.PhiStar.CoreAux.F0_theta_coefs 6
  refine ⟨C + 720 + 1, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h1
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h2
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h3
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h4
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) F0_div_one_add
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) F0_inv_one_add

end Work.FTS.PhiStar.StarPkgo2Aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldIdents =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.StarPkgo2Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary derivative facts -/

/-- `∂_θ sin 2θ = 2 cos 2θ`. -/
private lemma hasDerivAt_s2 (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Work.Construction.s2 θ') (2 * Real.cos (2 * θ)) θ := by
  have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have h' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    convert h using 1
    ring
  show HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ
  exact h'

/-- `sin 2θ ≠ 0` for an interior angle. -/
private lemma s2_ne_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  have hp : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  simpa [Work.Construction.s2] using ne_of_gt hp

/-- `∂_z (Ψ/sin 2θ) = ∂_zΨ/sin 2θ`. -/
private lemma pz_div_s2 (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = Work.Spaces.pz Ψ z θ / Work.Construction.s2 θ := by
  show deriv (fun z' : ℝ => Ψ z' θ / Work.Construction.s2 θ) z
      = deriv (fun z' : ℝ => Ψ z' θ) z / Work.Construction.s2 θ
  have h : (fun z' : ℝ => Ψ z' θ / Work.Construction.s2 θ)
      = fun z' : ℝ => (Work.Construction.s2 θ)⁻¹ * Ψ z' θ := by
    funext z'; rw [div_eq_mul_inv, mul_comm]
  rw [h, deriv_const_mul_field, div_eq_mul_inv]
  exact mul_comm _ _

/-- `∂_θ (Ψ/sin 2θ) = (∂_θΨ·sin 2θ − Ψ·2cos 2θ)/sin 2θ²`. -/
private lemma pth_div_s2 {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ)
    (hs2 : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = (Work.Spaces.pth Ψ z θ * Work.Construction.s2 θ
          - Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 := by
  have h := hd.hasDerivAt.div (hasDerivAt_s2 θ) hs2
  show deriv ((fun θ' : ℝ => Ψ z θ') / (fun θ' : ℝ => Work.Construction.s2 θ')) θ = _
  exact h.deriv

/-- `∂_z ((z+1)/z) = -1/z²`. -/
private lemma hasDerivAt_zfac (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun z' : ℝ => (z' + 1) / z') (-1 / z ^ 2) z := by
  have h0 := ((hasDerivAt_id z).add_const 1).div (hasDerivAt_id z) hz
  have h1 : HasDerivAt (fun z' : ℝ => (z' + 1) / z')
      ((1 * z - (z + 1) * 1) / z ^ 2) z := h0
  have hd : (1 * z - (z + 1) * 1) / z ^ 2 = -1 / z ^ 2 := by ring
  simpa only [hd] using h1

/-- `∂_z ((z+1)/z·g) = -g/z² + ((z+1)/z)·∂_zg`. -/
private lemma pz_zfac_mul {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0)
    (hd : DifferentiableAt ℝ (fun z' => g z' θ) z) :
    Work.Spaces.pz (fun z θ => (z + 1) / z * g z θ) z θ
      = -g z θ / z ^ 2 + (z + 1) / z * Work.Spaces.pz g z θ := by
  have h := (hasDerivAt_zfac z hz).mul hd.hasDerivAt
  show deriv ((fun z' : ℝ => (z' + 1) / z') * (fun z' : ℝ => g z' θ)) z
      = -g z θ / z ^ 2 + (z + 1) / z * deriv (fun z' => g z' θ) z
  rw [h.deriv]
  ring

/-- `∂_θ ((z+1)/z·g) = ((z+1)/z)·∂_θg`. -/
private lemma pth_zfac_mul (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => (z + 1) / z * g z θ) z θ
      = (z + 1) / z * Work.Spaces.pth g z θ := by
  show deriv (fun θ' : ℝ => (z + 1) / z * g z θ') θ = (z + 1) / z * deriv (fun θ' => g z θ') θ
  rw [deriv_const_mul_field]

/-! ## Congruence of `∂_z`, `∂_θ` of `Ψ` with `sin 2θ·(Ψ/sin 2θ)` -/

/-- On `Q0` the `z`-derivative of `Ψ` and of `sin 2θ·(Ψ/sin 2θ)` agree. -/
private lemma pz_mul_s2_div (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hs2 : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pz Ψ z θ
      = Work.Spaces.pz (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))
        z θ := by
  refine Work.FTS.EllipticEst.pz_congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun z' => (mul_div_cancel₀ _ hs2).symm

/-- On `Q0` the `θ`-derivative of `Ψ` and of `sin 2θ·(Ψ/sin 2θ)` agree. -/
private lemma pth_mul_s2_div (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hs2 : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pth Ψ z θ
      = Work.Spaces.pth (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))
        z θ := by
  refine Work.FTS.EllipticEst.pth_congr_of_eventuallyEq ?_
  have hcont : ContinuousAt (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : (fun θ' : ℝ => Work.Construction.s2 θ') = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]; fun_prop
  filter_upwards [hcont.eventually_ne hs2] with θ' hne
  exact (mul_div_cancel₀ _ hne).symm

/-- `ℛ(Ψ) = ℛ(sin 2θ·(Ψ/sin 2θ))` on `Q0`. -/
private lemma Rop_AgreeOnQ (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Construction.Rop α Ψ)
      (Work.Construction.Rop α
        (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))) := by
  intro z θ hz hθ hlt
  have hs2 : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo ⟨hθ, hlt⟩
  have hval : Ψ z θ = Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ) :=
    (mul_div_cancel₀ _ hs2).symm
  simp only [Work.Construction.Rop]
  conv_lhs => rw [hval, pz_mul_s2_div Ψ hs2, pth_mul_s2_div Ψ hs2]

/-- `𝒱(Ψ) = 𝒱(sin 2θ·(Ψ/sin 2θ))` on `Q0`. -/
private lemma Vop_AgreeOnQ (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Construction.Vop Ψ)
      (Work.Construction.Vop
        (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))) := by
  intro z θ hz hθ hlt
  have hs2 : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo ⟨hθ, hlt⟩
  have hval : Ψ z θ = Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ) :=
    (mul_div_cancel₀ _ hs2).symm
  simp only [Work.Construction.Vop]
  conv_lhs => rw [hval, pth_mul_s2_div Ψ hs2]

/-- `𝒰(Ψ) = 𝒰(sin 2θ·(Ψ/sin 2θ))` on `Q0`. -/
private lemma Uop_AgreeOnQ (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Construction.Uop α Ψ)
      (Work.Construction.Uop α
        (fun z θ => Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ))) := by
  intro z θ hz hθ hlt
  have hs2 : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo ⟨hθ, hlt⟩
  have hval : Ψ z θ = Work.Construction.s2 θ * (Ψ z θ / Work.Construction.s2 θ) :=
    (mul_div_cancel₀ _ hs2).symm
  simp only [Work.Construction.Uop]
  conv_lhs => rw [hval, pz_mul_s2_div Ψ hs2]

/-! ## The derivatives of `Y = ((z+1)/z)·(Ψ/sin 2θ)` in terms of `Φ = Ψ/sin 2θ` -/

/-- `∂_zY = -(Ψ/sin 2θ)/z² + ((z+1)/z)·∂_z(Ψ/sin 2θ)`. -/
private lemma pz_AgreeOnQ_zfac {Ψ Y : ℝ → ℝ → ℝ}
    (hY : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hd : DifferentiableAt ℝ (fun z' => Ψ z' θ) z) :
    Work.Spaces.pz Y z θ
      = -(Ψ z θ / Work.Construction.s2 θ) / z ^ 2
        + (z + 1) / z * Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ := by
  rw [hY.pz z θ hz hθ.1 hθ.2]
  exact pz_zfac_mul (g := fun z θ => Ψ z θ / Work.Construction.s2 θ) (ne_of_gt hz)
    (hd.div_const _)

/-- `∂_θY = ((z+1)/z)·∂_θ(Ψ/sin 2θ)`. -/
private lemma pth_AgreeOnQ_zfac {Ψ Y : ℝ → ℝ → ℝ}
    (hY : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth Y z θ
      = (z + 1) / z * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ := by
  rw [hY.pth z θ hz hθ.1 hθ.2]
  exact pth_zfac_mul (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ

/-- `∂_z∂_θY = -∂_θ(Ψ/sin 2θ)/z² + ((z+1)/z)·∂_z∂_θ(Ψ/sin 2θ)`. -/
private lemma pz_pth_AgreeOnQ_zfac {Ψ Y : ℝ → ℝ → ℝ}
    (hY : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hd : DifferentiableAt ℝ
      (fun z' => Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ) z) :
    Work.Spaces.pz (Work.Spaces.pth Y) z θ
      = -(Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ) / z ^ 2
        + (z + 1) / z
          * Work.Spaces.pz (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ)) z θ := by
  have hpt : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pth Y)
      (fun z θ => (z + 1) / z
        * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ) := by
    intro z' θ' hz' hθ' hlt'
    exact (hY.pth z' θ' hz' hθ' hlt').trans
      (pth_zfac_mul (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ')
  rw [hpt.pz z θ hz hθ.1 hθ.2]
  exact pz_zfac_mul (g := fun z θ =>
      Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ) (ne_of_gt hz) hd

/-! ## The mixed derivative of `Φ = Ψ/sin 2θ` -/

/-- `∂_z((A·a − B·b)/a²) = (∂_zA·a − ∂_zB·b)/a²` for `a`, `b` functions of `θ` only. -/
private lemma pz_explicit_div {A B : ℝ → ℝ → ℝ} {ac bc : ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB : DifferentiableAt ℝ (fun z' => B z' θ) z) :
    Work.Spaces.pz (fun z θ => (A z θ * ac θ - B z θ * bc θ) / (ac θ) ^ 2) z θ
      = (Work.Spaces.pz A z θ * ac θ - Work.Spaces.pz B z θ * bc θ) / (ac θ) ^ 2 := by
  have h := (((hA.hasDerivAt).mul_const (ac θ)).sub ((hB.hasDerivAt).mul_const (bc θ))).div_const
    ((ac θ) ^ 2)
  exact h.deriv

/-- `∂_z∂_θ(Ψ/sin 2θ) = (∂_z∂_θΨ·sin 2θ − ∂_zΨ·2cos 2θ)/sin 2θ²`. -/
private lemma pz_pth_div_s2 {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ)) z θ
      = (Work.Spaces.pz (Work.Spaces.pth Ψ) z θ * Work.Construction.s2 θ
          - Work.Spaces.pz Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 := by
  have hpt : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ))
      (fun z θ => (Work.Spaces.pth Ψ z θ * Work.Construction.s2 θ
          - Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2) := by
    intro z' θ' hz' hθ' hlt'
    have hd : DifferentiableAt ℝ (fun θ'' => Ψ z' θ'') θ' :=
      ((hsm.curry_θ hz').differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds ⟨hθ', hlt'⟩)
    exact pth_div_s2 hd (s2_ne_of_mem_Ioo ⟨hθ', hlt'⟩)
  rw [hpt.pz z θ hz hθ.1 hθ.2]
  exact pz_explicit_div (A := Work.Spaces.pth Ψ) (B := Ψ) (ac := Work.Construction.s2)
    (bc := fun θ => 2 * Real.cos (2 * θ))
    ((hsm.pth).hasDerivAt_slice hθ hz).differentiableAt
    (hsm.hasDerivAt_slice hθ hz).differentiableAt

/-- The `z`-slice of `∂_θ(Ψ/sin 2θ)` is differentiable at an interior point. -/
private lemma diff_z_pth_div_s2 {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ
      (fun z' => Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ) z := by
  have hev : (fun z' => Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => (Work.Spaces.pth Ψ z' θ * Work.Construction.s2 θ
          - Ψ z' θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pth_div_s2 (((hsm.curry_θ hz').differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)) (s2_ne_of_mem_Ioo hθ)
  have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ) z :=
    ((hsm.pth).hasDerivAt_slice hθ hz).differentiableAt
  have hdB : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hsm.hasDerivAt_slice hθ hz).differentiableAt
  have hdex : DifferentiableAt ℝ (fun z' => (Work.Spaces.pth Ψ z' θ * Work.Construction.s2 θ
      - Ψ z' θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2) z :=
    ((hdA.mul_const _).sub (hdB.mul_const _)).div_const _
  exact hdex.congr_of_eventuallyEq hev

/-! ## The six field identities -/

theorem FieldIdents (α : ℝ) (Ψ Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hY : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Y z θ = (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.PhiStar.EH α Y z θ = (z + 1) / z * Work.Construction.Rop α Ψ z θ ∧
      Work.FTS.PhiStar.EV Y z θ = Work.Construction.Vop Ψ z θ ∧
      Work.FTS.PhiStar.EVz Y z θ = (z + 1) / z * Work.Construction.Vop Ψ z θ ∧
      Work.FTS.PhiStar.EU α Y z θ = Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ ∧
      Work.FTS.PhiStar.EUz α Y z θ
        = (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) ∧
      Work.FTS.PhiStar.EPU α Y z θ = Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ := by
  intro z θ hz
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz
  have hzne : z ≠ 0 := ne_of_gt hz0
  have hz1ne : (1 : ℝ) + z ≠ 0 := by positivity
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hs2ne : Work.Construction.s2 θ ≠ 0 := s2_ne_of_mem_Ioo hθI
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  -- `Y` as an `AgreeOnQ`-statement
  have hAg : Work.FTS.EllipticEst.AgreeOnQ Y
      (fun z θ => (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ)) :=
    fun z θ hz' hθ' hlt' => hY z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩)
  -- differentiability of the relevant slices
  have hdzΨ : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hsm.hasDerivAt_slice hθI hz0).differentiableAt
  have hdθΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
    ((hsm.curry_θ hz0).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
  have hdθΦ : DifferentiableAt ℝ (fun θ' => Ψ z θ' / Work.Construction.s2 θ') θ :=
    hdθΨ.div (hasDerivAt_s2 θ).differentiableAt hs2ne
  -- the value of `Y` and its derivatives, in terms of `Φ = Ψ/sin 2θ`
  have hval : Y z θ = (z + 1) / z * (Ψ z θ / Work.Construction.s2 θ) := hY z θ hz
  have hpzY := pz_AgreeOnQ_zfac hAg hz0 hθI hdzΨ
  have hpthY := pth_AgreeOnQ_zfac hAg hz0 hθI
  have hpzpthY := pz_pth_AgreeOnQ_zfac hAg hz0 hθI (diff_z_pth_div_s2 hsm hz0 hθI)
  -- the derivatives of `Φ` in terms of `Ψ`
  have hpzΦ : Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = Work.Spaces.pz Ψ z θ / Work.Construction.s2 θ := pz_div_s2 Ψ z θ
  have hpthΦ : Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ
      = (Work.Spaces.pth Ψ z θ * Work.Construction.s2 θ
          - Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 :=
    pth_div_s2 hdθΨ hs2ne
  have hpzpthΦ : Work.Spaces.pz (Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ)) z θ
      = (Work.Spaces.pz (Work.Spaces.pth Ψ) z θ * Work.Construction.s2 θ
          - Work.Spaces.pz Ψ z θ * (2 * Real.cos (2 * θ))) / (Work.Construction.s2 θ) ^ 2 :=
    pz_pth_div_s2 hsm hz0 hθI
  -- the transport coefficients, in terms of `Φ`
  have hRop : Work.Construction.Rop α Ψ z θ
      = 2 * (Ψ z θ / Work.Construction.s2 θ)
        + 2 * α * Real.sin θ ^ 2
          * (z * Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ)
        + Work.Construction.s2 θ
          * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ :=
    (Rop_AgreeOnQ α Ψ z θ hz0 hθ0 hθ1).trans
      (Work.FTS.H2.StarPkg.Rop_sin_two_mul α (fun z θ => Ψ z θ / Work.Construction.s2 θ)
        z θ hcos hdθΦ)
  have hVop : Work.Construction.Vop Ψ z θ
      = 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * (Ψ z θ / Work.Construction.s2 θ)
        + Work.Construction.s2 θ
          * Work.Spaces.pth (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ :=
    (Vop_AgreeOnQ Ψ z θ hz0 hθ0 hθ1).trans
      (Work.FTS.H2.StarPkg.Vop_sin_two_mul (fun z θ => Ψ z θ / Work.Construction.s2 θ)
        z θ hcos hdθΦ)
  have hUop : Work.Construction.Uop α Ψ z θ
      = -(Work.Construction.s2 θ
          * (3 * (Ψ z θ / Work.Construction.s2 θ)
            + α * (z * Work.Spaces.pz (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ))) :=
    (Uop_AgreeOnQ α Ψ z θ hz0 hθ0 hθ1).trans
      (Work.FTS.H2.StarPkg.Uop_sin_two_mul α (fun z θ => Ψ z θ / Work.Construction.s2 θ) z θ)
  -- `𝒰` and `∂_θ𝒰`
  have hEU : Work.FTS.PhiStar.EU α Y z θ
      = Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ := by
    rw [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, hUop]
    rw [hval, hpzY, hpzΦ]
    field_simp; ring
  have hcd : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
    (hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hz)
  have hdθpzΨ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz Ψ z θ') θ :=
    ((hsm.pz).curry_θ hz0).differentiableOn (by simp) |>.differentiableAt
      (isOpen_Ioo.mem_nhds hθI)
  have hpthUop : Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      = -3 * Work.Spaces.pth Ψ z θ - α * z * Work.Spaces.pz (Work.Spaces.pth Ψ) z θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Ψ z θ') (Work.Spaces.pth Ψ z θ) θ := hdθΨ.hasDerivAt
    have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pz Ψ z θ')
        (Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) θ := hdθpzΨ.hasDerivAt
    have h3 : HasDerivAt (fun θ' : ℝ => -3 * Ψ z θ' - α * z * Work.Spaces.pz Ψ z θ')
        (-3 * Work.Spaces.pth Ψ z θ - α * z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) θ :=
      (h1.const_mul (-3)).sub (h2.const_mul (α * z))
    have hcl : Work.Spaces.pth (Work.Spaces.pz Ψ) z θ
        = Work.Spaces.pz (Work.Spaces.pth Ψ) z θ := (Work.Spaces.pz_pth_comm hcd).symm
    show deriv (fun θ' : ℝ => -3 * Ψ z θ' - α * z * Work.Spaces.pz Ψ z θ') θ = _
    rw [h3.deriv, hcl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(z+1)/z·ℛ(Ψ) = EH(Y)`
    rw [Work.FTS.PhiStar.EH, Work.FTS.PhiStar.Yblk, Work.FTS.PhiStar.Tblk, hRop]
    rw [hval, hpzY, hpthY]
    field_simp; ring
  · -- `𝒱(Ψ) = EV(Y)`
    rw [Work.FTS.PhiStar.EV, Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, hVop]
    rw [hval, hpthY]
    field_simp
  · -- `(z+1)/z·𝒱(Ψ) = EVz(Y)`
    rw [Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, hVop]
    rw [hval, hpthY]
    field_simp
  · -- `𝒰(Ψ)/sin 2θ = EU(Y)`
    exact hEU
  · -- `(z+1)/z·(𝒰(Ψ)/sin 2θ) = EUz(Y)`
    rw [Work.FTS.PhiStar.EUz, ← hEU, Work.FTS.PhiStar.EU]
    field_simp
  · -- `∂_θ𝒰(Ψ) = EPU(Y)`
    rw [Work.FTS.PhiStar.EPU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, hpthUop]
    rw [hval, hpzY, hpthY, hpzpthY]
    rw [hpzΦ, hpthΦ, hpzpthΦ]
    field_simp; ring

end Work.FTS.PhiStar.StarPkgo2Aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.StarPkgo2Aux

/-!
# Regularity of the coefficient fields `ℛ(Ψ)`, `𝒱(Ψ)`, `𝒰(Ψ)`, `𝒰(Ψ)/sin 2θ`

The fields of the self-similar vorticity equation (`Work.Construction.Rop`, `.Vop`, `.Uop`) are
rational expressions in `Ψ`, `∂_zΨ`, `∂_θΨ` and the angular functions `sin θ`, `cos θ`,
`tan θ`; on the open quadrant `Q0 = (0,∞) × (0,π/2)` all of these are `C^∞` whenever `Ψ` is,
and the two denominators that appear (`cos θ` in `ℛ`, `sin 2θ` in `𝒰/sin 2θ`) do not vanish
there.  Together with the radial factor `(z+1)/z` (whose only singularity `z = 0` lies outside
`Q0`), this gives `Work.FTS.EllipticEst.SmoothOpen` of all six fields, plus the angular
derivative `∂_θ 𝒰(Ψ)`.

All inputs are already-delivered, `sorry`-free facts:

* `Work.FTS.NonlinRows.smoothOpen_Rop` (`ℛ` preserves `SmoothOpen`),
* `Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open`, `…smoothOpen_Vop_open` (`𝒰`, `𝒱` preserve
  `SmoothOpen`),
* `Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul`,
  `Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z`,
* `Work.FTS.EllipticEst.SmoothOpen.pth` (the angular derivative preserves `SmoothOpen`),
* the local lemma `smoothOpen_div_sin2` below (division by `sin 2θ` preserves `SmoothOpen`).
-/

/-- Division by `sin 2θ` preserves `C^∞` on the open quadrant (`sin 2θ > 0` for
`0 < θ < π/2`).  Copy of `Work.Blocks.smoothOpen_div_sin2`, kept local so that this module
depends only on the two smoothness-API imports. -/
theorem smoothOpen_div_sin2 {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / Real.sin (2 * θ)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact h1.div h2 (fun p hp => by
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))

theorem FieldRegularity (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Rop α Ψ z θ) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Vop Ψ z θ) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * (Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ)) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Construction.Uop α Ψ)) := by
  have hR : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hsm
  have hV : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Vop_open hsm
  have hU : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α Ψ) :=
    Work.FTS.NonlinRows.Rl1.smoothOpen_Uop_open hsm
  have hfac : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z
  have hdiv : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ) := by
    simpa only [Work.Construction.s2] using
      smoothOpen_div_sin2 (f := Work.Construction.Uop α Ψ) hU
  exact ⟨Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hfac hR, hV,
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hfac hV, hdiv,
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hfac hdiv, hU.pth⟩

end Work.FTS.PhiStar.StarPkgo2Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.lintegral_shift_le_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.DiffAux

theorem lintegral_shift_le_gen {δ : ℝ}
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂))
    {V : ℝ → ℝ → ℝ} (p : ℝ × ℝ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (V z θ)) := by
  -- the two shifts in the log coordinates are the translations `s ↦ s - p₁`, `ζ ↦ ζ - p₂`
  have hz : ∀ s : ℝ, Work.FTS.StrongEps.zShift (Real.exp s) p.1 = Real.exp (s - p.1) := by
    intro s
    rw [Work.FTS.StrongEps.zShift, ← Real.exp_add, sub_eq_add_neg]
  have hth : ∀ ζ : ℝ, Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) p.2
      = Real.arctan (Real.exp (ζ - p.2)) := by
    intro ζ
    rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]
  -- the same integral, without the shift, in log coordinates
  have hgen : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (V z θ))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    have hIθ0 : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (V z θ))
        = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (V z θ) :=
      funext fun z => (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ => ENNReal.ofReal (V z θ))
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
    rw [hIθ0]
    have hIz0 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (V z θ))
        = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (V z θ) :=
      (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (V z θ))
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
    rw [hIz0]
    exact Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst (fun z θ => ENNReal.ofReal (V z θ))
  set r : ENNReal := ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) with hr
  have hrne : r ≠ ⊤ := by rw [hr]; exact ENNReal.ofReal_ne_top
  -- replace the closed intervals by the open ones on the left-hand side (null sets)
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
    funext fun z => (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ =>
      ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
  rw [hIθ]
  have hIz : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
    (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  rw [hIz]
  -- the log-coordinate substitution, which is *exactly* the shift in the new variables
  rw [Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst (fun z θ =>
      ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))]
  simp only [hz, hth]
  -- translation invariance of the plane integral: move the shift onto the Jacobian weight
  rw [Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift_mul
        (fun s ζ => ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ))
        (fun s ζ => ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) p.1 p.2]
  -- the pointwise comparison coming from `hJac`
  have hpt : ∀ s ζ : ℝ,
      ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac (s + p.1) (ζ + p.2))
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))
        ≤ r * (ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) := by
    intro s ζ
    have h := hJac (s + p.1) (ζ + p.2) p.1 p.2
    rw [add_sub_cancel_right, add_sub_cancel_right] at h
    have h1 : ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac (s + p.1) (ζ + p.2))
        ≤ r * ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ) := by
      rw [hr, ← ENNReal.ofReal_mul (Real.exp_pos (δ * (|p.1| + |p.2|))).le]
      exact ENNReal.ofReal_le_ofReal h
    calc ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac (s + p.1) (ζ + p.2))
            * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))
        ≤ (r * ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ))
            * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ))) :=
          mul_le_mul_of_nonneg_right h1 bot_le
      _ = r * (ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
            * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) := by ring
  refine le_trans (MeasureTheory.lintegral_mono fun s =>
    MeasureTheory.lintegral_mono fun ζ => hpt s ζ) ?_
  -- pull the constant `r` out of the two integrals
  rw [show (∫⁻ s, ∫⁻ ζ, r * (ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))))
      = r * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ))) from ?_]
  · -- identify the remaining plane integral with the quadrant integral of `V`
    rw [hgen]
  · rw [← MeasureTheory.lintegral_const_mul' r
        (fun s => ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) hrne]
    refine MeasureTheory.lintegral_congr fun s => ?_
    exact MeasureTheory.lintegral_const_mul' r
      (fun ζ => ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) hrne

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `integral_quad_log_subst` — the log-coordinate substitution for Bochner integrals

The Bochner-integral form of the two-dimensional change of variables
`(z, θ) = (e^s, arctan (e^ζ))` on the quadrant `(0,∞) × (0,π/2)`:

  `∫_{z>0} ∫_{0<θ<π/2} F z θ = ∫_s ∫_ζ logJac s ζ · F (e^s) (arctan (e^ζ))`,

where `logJac s ζ = e^s · kappa ζ` is the Jacobian of the substitution
(`Work.FTS.StrongEps.HkSqAux.logJac`).  The `lintegral` version is the sibling
`Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst`; here we need the signed (Bochner) version.

The proof applies the one-dimensional change-of-variables formula for injective differentiable
maps, `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, twice: for `ζ ↦ arctan (e^ζ)`
(whose range is `(0,π/2)`, with derivative `kappa ≥ 0`) slice by slice, and then for `z = e^s`
(whose range is `(0,∞)`, with derivative `e^s ≥ 0`).
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open MeasureTheory Set
open scoped Real

theorem integral_quad_log_subst {F : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
          * F (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  classical
  -- Step 1: the angular substitution `θ = arctan (e^ζ)`, for each slice `z`.
  have hsubθ : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ)
      = ∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ * F z (Real.arctan (Real.exp ζ)) := by
    intro z
    have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) (f := fun ζ : ℝ => Real.arctan (Real.exp ζ))
      (f' := Work.FTS.StrongEps.HkSqAux.kappa) MeasurableSet.univ
      (fun ζ _ => (Work.FTS.StrongEps.HkSqAux.hasDerivAt_arctan_exp ζ).hasDerivWithinAt)
      (Work.FTS.StrongEps.HkSqAux.strictMono_arctan_exp.injective.injOn)
      (fun θ => F z θ)
    rw [Work.FTS.StrongEps.HkSqAux.range_arctan_exp, MeasureTheory.setIntegral_univ] at h
    have habs : ∀ ζ : ℝ, |Work.FTS.StrongEps.HkSqAux.kappa ζ|
        = Work.FTS.StrongEps.HkSqAux.kappa ζ :=
      fun ζ => abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.kappa_nonneg ζ)
    simpa [habs, smul_eq_mul] using h
  have h1 : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ)
      = ∫ z in Set.Ioi 0, (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
          * F z (Real.arctan (Real.exp ζ))) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => hsubθ z)
  -- Step 2: the radial substitution `z = e^s` in the outer integral.
  have h2 : (∫ z in Set.Ioi 0, (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
        * F z (Real.arctan (Real.exp ζ))))
      = ∫ s, Real.exp s * (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
          * F (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn
      (fun z => ∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ * F z (Real.arctan (Real.exp ζ)))
    rw [Work.FTS.StrongEps.HkSqAux.range_exp, MeasureTheory.setIntegral_univ] at h
    have habs : ∀ x : ℝ, |Real.exp x| = Real.exp x := fun x => abs_of_pos (Real.exp_pos x)
    simpa [habs, smul_eq_mul] using h
  -- Step 3: move the constant `e^s` inside the `ζ`-integral and identify `logJac`.
  have h3 : ∀ s : ℝ, Real.exp s * (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
        * F (Real.exp s) (Real.arctan (Real.exp ζ)))
      = ∫ ζ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
          * F (Real.exp s) (Real.arctan (Real.exp ζ)) := by
    intro s
    rw [show (∫ ζ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
            * F (Real.exp s) (Real.arctan (Real.exp ζ)))
        = ∫ ζ, Real.exp s * (Work.FTS.StrongEps.HkSqAux.kappa ζ
            * F (Real.exp s) (Real.arctan (Real.exp ζ))) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ζ => by
          show Work.FTS.StrongEps.HkSqAux.logJac s ζ * F (Real.exp s) (Real.arctan (Real.exp ζ))
            = Real.exp s * (Work.FTS.StrongEps.HkSqAux.kappa ζ
              * F (Real.exp s) (Real.arctan (Real.exp ζ)))
          rw [Work.FTS.StrongEps.HkSqAux.logJac.eq_1]; ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [h1, h2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h3)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.angBlk_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux (angBlk Kf GQjet_bound gamQfun_angBlk Kf_pos)

set_option maxHeartbeats 800000

/-! ## The auxiliary exponent `q` and the majorant -/

/-- The exponent `q(α) = 1 - 17α/30` of the angular majorant: `Γ(θ)² sin(2θ)^{-γ(α)}`
is dominated by `sin(2θ)^{-q(α)}` because `2α/3 - γ(α) = -q(α)`. -/
noncomputable def qang (α : ℝ) : ℝ := 1 - 17 * α / 30

lemma qang_pos {α : ℝ} (hα : α ≤ 1) : 0 < qang α := by rw [qang]; linarith

lemma qang_lt_one {α : ℝ} (hα : 0 < α) : qang α < 1 := by rw [qang]; linarith

/-- The angular majorant of `angBlk α a / a²`. -/
noncomputable def majBlk (α : ℝ) : ℝ → ℝ := fun θ =>
  Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α))

lemma eta_pos : 0 < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num

lemma eta_lt_one : Work.Spaces.eta < 1 := by rw [Work.Spaces.eta]; norm_num

lemma sin_two_nonneg_of_mem_Iθ (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## Nonnegativity -/

lemma angBlk_nonneg (α a : ℝ) : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ angBlk α a θ := by
  intro θ hθ
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  simp only [angBlk]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
  refine Finset.sum_nonneg (fun i _ => ?_)
  by_cases h1 : 1 ≤ i
  · rw [if_pos h1]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  · rw [if_neg h1]

/-! ## The two pointwise block bounds -/

/-- The `η`-slot: `(a·Γ·q)² sin(2θ)^{-η} ≤ a² Kf² sin(2θ)^{-η}`. -/
lemma eta_term_le {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hjet := GQjet_bound (i := 0) hα hα1 (by norm_num : |(1 : ℝ)| ≤ 20) (Nat.zero_le 6) hθ
  have hjet' : |Work.Spaces.Gam α θ * Work.Spaces.qfun θ| ≤ Kf * Work.Spaces.Gam α θ := by
    simpa using hjet
  have hsq : (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2 ≤ Kf ^ 2 := by
    have h1 : (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
      calc (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
          = |Work.Spaces.Gam α θ * Work.Spaces.qfun θ| ^ 2 := by rw [sq_abs]
        _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hjet' 2
    calc (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := h1
      _ = Kf ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ Kf ^ 2 * 1 ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hG.1, hG.2]) (sq_nonneg Kf)
      _ = Kf ^ 2 := by ring
  have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
  calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = a ^ 2 * ((Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    _ ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hw) (sq_nonneg a)

/-- The `γ`-slots: for `i ≤ 6`, `(D_θ^i (a·Γ·q))² sin(2θ)^{-γ} ≤ a² Kf² sin(2θ)^{-q(α)}`. -/
lemma jet_term_le {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi : i ≤ 6) :
    (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α))) := by
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = -(qang α) := by
    rw [Work.Spaces.gam, qang]; ring
  have hne : 2 * α / 3 + -(Work.Spaces.gam α) ≠ 0 := by
    rw [hexp]; have := qang_pos hα1; linarith
  have hjet := GQjet_bound (i := i) hα hα1 (by norm_num : |(1 : ℝ)| ≤ 20) hi hθ
  rw [Work.Spaces.dthU_iter_const_mul] at hjet
  have hjet' : |Work.Spaces.dthU^[i]
      (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ| ≤ Kf * Work.Spaces.Gam α θ := by
    simpa using hjet
  have hsq : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
      ≤ Kf ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) := by
    have h1 : (Work.Spaces.dthU^[i]
        (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
      calc (Work.Spaces.dthU^[i]
            (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
          = |Work.Spaces.dthU^[i]
              (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ| ^ 2 := by rw [sq_abs]
        _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hjet' 2
    calc (Work.Spaces.dthU^[i]
            (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := h1
      _ = Kf ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ Kf ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) :=
          mul_le_mul_of_nonneg_left (Work.Coercivity.Gam_sq_le_sin_two α hα θ hθ) (sq_nonneg _)
  have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hprod : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (-(qang α)) := by
    rw [← Real.rpow_add' hs0 hne, hexp]
  calc (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = a ^ 2 * ((Work.Spaces.dthU^[i]
          (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [Work.Spaces.dthU_iter_const_mul]; ring
    _ ≤ a ^ 2 * ((Kf ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3))
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hw) (sq_nonneg a)
    _ = a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α))) := by
        rw [mul_assoc, hprod]

/-- **The pointwise majorant.**  `angBlk α a θ ≤ a² · majBlk α θ` on `Iθ`. -/
lemma angBlk_le_maj {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ, angBlk α a θ ≤ a ^ 2 * majBlk α θ := by
  intro θ hθ
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  simp only [angBlk, majBlk]
  have hsum : (∑ i ∈ Finset.range 7,
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0))
      ≤ ∑ _i ∈ Finset.range 7, a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α))) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1]
      exact jet_term_le hα hα1 hθ (by have := Finset.mem_range.mp hi; omega)
    · rw [if_neg h1]
      exact mul_nonneg (sq_nonneg a) (mul_nonneg (sq_nonneg Kf) (Real.rpow_nonneg hs0 _))
  calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then
              (Work.Spaces.dthU^[i]
                (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
             else 0)
      ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∑ _i ∈ Finset.range 7, a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α)))) :=
        add_le_add (eta_term_le hα hα1 hθ) hsum
    _ = a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 7 * (a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α))) := by ring

/-! ## Integration of the majorant -/

lemma majBlk_integrable {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ => a ^ 2 * majBlk α θ) Work.Spaces.Iθ := by
  have hEta := Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta eta_pos eta_lt_one
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (qang α)
    (qang_pos hα1) (qang_lt_one hα)
  have h1 : IntegrableOn (fun θ => Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hEta.1.const_mul _
  have h2 : IntegrableOn (fun θ => (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α)))
      Work.Spaces.Iθ := hQ.1.const_mul _
  have h3 := h1.add h2
  exact h3.const_mul (a ^ 2)

lemma majBlk_integral_le {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Work.Spaces.Iθ, a ^ 2 * majBlk α θ
      ≤ a ^ 2 * (Kf ^ 2 * (400 : ℝ) + (7 * Kf ^ 2) * (120 / (17 * α))) := by
  have hEta := Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta eta_pos eta_lt_one
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (qang α)
    (qang_pos hα1) (qang_lt_one hα)
  have h1 : IntegrableOn (fun θ => Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hEta.1.const_mul _
  have h2 : IntegrableOn (fun θ => (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α)))
      Work.Spaces.Iθ := hQ.1.const_mul _
  have hval : ∫ θ in Work.Spaces.Iθ, a ^ 2 * majBlk α θ
      = a ^ 2 * (Kf ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (7 * Kf ^ 2) * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(qang α)))) := by
    simp only [majBlk]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have heta : Kf ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ Kf ^ 2 * 400 := by
    have h4 : (4 : ℝ) / (1 - Work.Spaces.eta) = 400 := by
      rw [Work.Spaces.eta]; norm_num
    simpa only [h4] using mul_le_mul_of_nonneg_left hEta.2 (sq_nonneg Kf)
  have hq : (7 * Kf ^ 2) * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(qang α)))
      ≤ (7 * Kf ^ 2) * (120 / (17 * α)) := by
    have h17 : (1 : ℝ) - qang α = 17 * α / 30 := by rw [qang]; ring
    have h4 : (4 : ℝ) / (1 - qang α) = 120 / (17 * α) := by
      rw [h17]
      have hαne : α ≠ 0 := ne_of_gt hα
      field_simp
      ring
    simpa only [h4] using mul_le_mul_of_nonneg_left hQ.2 (by positivity)
  rw [hval]
  exact mul_le_mul_of_nonneg_left (add_le_add heta hq) (sq_nonneg a)

/-! ## The main theorem -/

theorem angBlk_bound : ∃ Aang : ℝ, 0 < Aang ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ a : ℝ, |a| ≤ 20 →
    MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α a)
        Work.Spaces.Iθ ∧
      α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α a θ) ≤ Aang * a ^ 2 := by
  obtain ⟨_, _, hang⟩ := gamQfun_angBlk
  refine ⟨500 * Kf ^ 2 + 1, by positivity, fun α hαIoc a ha => ?_⟩
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hint : MeasureTheory.IntegrableOn (angBlk α a) Work.Spaces.Iθ :=
    hang α hαIoc a ha
  refine ⟨hint, ?_⟩
  -- the integral is dominated by the integral of the majorant
  have hmono : ∫ θ in Work.Spaces.Iθ, angBlk α a θ
      ≤ ∫ θ in Work.Spaces.Iθ, a ^ 2 * majBlk α θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (majBlk_integrable hα hα1) ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact angBlk_nonneg α a θ hθ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact angBlk_le_maj hα hα1 θ hθ
  have hInt : ∫ θ in Work.Spaces.Iθ, angBlk α a θ
      ≤ a ^ 2 * (Kf ^ 2 * (400 : ℝ) + (7 * Kf ^ 2) * (120 / (17 * α))) :=
    le_trans hmono (majBlk_integral_le hα hα1)
  -- arithmetic
  have hαsq1 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
  have hkey : α ^ 2 * (120 / (17 * α)) ≤ 120 / 17 := by
    have hαne : α ≠ 0 := ne_of_gt hα
    have he : α ^ 2 * (120 / (17 * α)) = 120 * α / 17 := by
      field_simp
    rw [he, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 17) (by norm_num : (0 : ℝ) < 17)]
    nlinarith [hα1]
  have hnum : Kf ^ 2 * (400 : ℝ) * 1 + (7 * Kf ^ 2) * (120 / 17) ≤ 500 * Kf ^ 2 + 1 := by
    nlinarith [sq_nonneg Kf]
  calc α ^ 2 * (∫ θ in Work.Spaces.Iθ, angBlk α a θ)
      ≤ α ^ 2 * (a ^ 2 * (Kf ^ 2 * (400 : ℝ) + (7 * Kf ^ 2) * (120 / (17 * α)))) :=
        mul_le_mul_of_nonneg_left hInt (sq_nonneg α)
    _ = a ^ 2 * (Kf ^ 2 * (400 : ℝ) * α ^ 2 + (7 * Kf ^ 2) * (α ^ 2 * (120 / (17 * α)))) := by
        ring
    _ ≤ a ^ 2 * (Kf ^ 2 * (400 : ℝ) * 1 + (7 * Kf ^ 2) * (120 / 17)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (sq_nonneg a)
        · exact mul_le_mul_of_nonneg_left hαsq1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ (500 * Kf ^ 2 + 1) * a ^ 2 := by
        calc a ^ 2 * (Kf ^ 2 * (400 : ℝ) * 1 + (7 * Kf ^ 2) * (120 / 17))
            ≤ a ^ 2 * (500 * Kf ^ 2 + 1) := mul_le_mul_of_nonneg_left hnum (sq_nonneg a)
          _ = (500 * Kf ^ 2 + 1) * a ^ 2 := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row2u =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row2`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory

/-- **Honest row 2 of the §8 table.**  `N₀₃ = (1/α)L₁₂(g)·g` is `ℋ⁴`-honest and
`Xn α (N₀₃) ≤ K α^{-1} (Xn α g)²`, in the *honest* (open-quadrant) class of the route:
`SmoothOpen g`, `HkMem α 4 g`, `HkMem α 5 g`, `L₁₂(g)(0) = 0`, `DecayAll 4 g`.

This is the open-quadrant port of `Work.FTS.NonlinRows.NRow2`: the growth and moment bounds on
`L₁₂(g)` come from the honest lemmas `L12_sq_le_growth_honest` / `L12_dzdIter_moment_honest`,
the angular-moment bound from `Qang_sq_le_const_open`, and the radial Leibniz rule from
`radial_leibniz_open`. -/
theorem n0row2u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N03g α g)
          ≤ K * (α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hK1def
  set Kc : ℝ := max (K1 / 3) K1 + 1 with hKcdef
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  refine ⟨Real.sqrt (200000 * Kc) + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hsm hmem hmem5 h0 hdecay hs hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hhqo : Work.FTS.VocabO.HQo α 4 g := ⟨hsm, hmem⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hHk : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  obtain ⟨hmom, hdiff⟩ :=
    Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest α hα hα1 hsm hmem h0
  -- the uniform bound on the iterates of `L₁₂(g)`
  have hgrowth := Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest α hα hα1 hsm hmem h0
  have hCg1 : ∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
      ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3 := by
    intro z hz
    have h := hgrowth.1 z hz
    rw [show (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) = Kc from by
      rw [hKcdef, hK1def]] at h
    exact h
  have hCg2 : ∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
      ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z := by
    intro z hz
    have h := hgrowth.2 z hz
    rw [show (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) = Kc from by
      rw [hKcdef, hK1def]] at h
    exact h
  have hb1 : ∀ b : ℕ, 1 ≤ b → b ≤ 4 → ∀ z : ℝ, 0 < z →
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z) ^ 2
        ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    intro b hb1 hb4 z hz
    have hq := Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open hα hα1 hsm hmem
      (i := b - 1) (by omega) hz
    have h1 : Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g (b - 1) z := by
      have h := hmom (b - 1) (by omega) z hz
      rwa [show b - 1 + 1 = b from by omega] at h
    rw [h1, neg_sq]
    calc (Work.Elliptic.Qang g (b - 1) z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α 4 g := hq
      _ = K1 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by rw [← hK1def, hHk]
      _ ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
          mul_le_mul_of_nonneg_right (by
            rw [hKcdef]
            exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one))
            (sq_nonneg _)
  have hb0 : ∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
      ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    intro z hz
    have hKX : 0 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
      mul_nonneg hKcpos.le (sq_nonneg _)
    by_cases h1 : z ≤ 1
    · refine (hCg1 z hz).trans ?_
      have hz3 : z ^ 3 ≤ 1 := by
        calc z ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hz.le h1 3
          _ = 1 := by norm_num
      calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3
          ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hz3 hKX
        _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    · refine (hCg2 z hz).trans ?_
      have hz1 : 1 / z ≤ 1 := by
        rw [div_le_one hz]
        linarith
      have h2 : Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z
          = (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (1 / z) := by
        rw [div_eq_mul_one_div]
      calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z
          = (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (1 / z) := h2
        _ ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hz1 hKX
        _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
  have hx : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z) ^ 2
        ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    intro b hb z hz
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      rw [Work.Elliptic.DzdIter_zero]
      exact hb0 z hz
    · exact hb1 b h (by omega) z hz
  -- the pointwise Leibniz rules
  have hleib : ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DzIter i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
              * Work.Spaces.DzIter (i - b) g z θ) := by
    intro i hi z θ hz hθ
    rw [← Work.Spaces.mixed_zero_right i
      (fun z θ => Work.Construction.L12 g z * g z θ)]
    exact Work.FTS.StrongEps.E4R3.radial_leibniz_open (fun z => Work.Construction.L12 g z) g
      i 0 (by omega) hz hθ hsm
      (fun b hb z' hz' => hdiff b (by omega) z' hz')
  have hleibm : ∀ j i : ℕ, i ≤ 4 → j ≤ 4 → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
              * Work.Spaces.mixed (j - b) i g z θ) :=
    fun j i _ hj z θ hz hθ =>
      Work.FTS.StrongEps.E4R3.radial_leibniz_open (fun z => Work.Construction.L12 g z) g
        j i hj hz hθ hsm (fun b hb z' hz' => hdiff b (by omega) z' hz')
  -- the pointwise bound on the `ℋ⁴`-integrand
  have hbin : ∀ i ≤ 4, ∀ b ∈ Finset.range (i + 1), ((i.choose b : ℕ) : ℝ) ≤ 16 :=
    fun i hi b _ => Work.FTS.Nonlinear.RadialProd.choose_le_sixteen hi
  have hpt : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 4 (fun z θ => Work.Construction.L12 g z * g z θ) z θ
        ≤ 200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2
          * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z θ hz hθ
    have hX2 : 0 ≤ (Work.FTS.Nonlin.Xn α g) ^ 2 := sq_nonneg _
    have hK2nn : 0 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := mul_nonneg hKcpos.le hX2
    set B : ℝ := Work.Spaces.HkIntegrand α 4 g z θ with hBdef
    have hBnn : 0 ≤ B := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have hpure : ∀ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by
      intro i hi
      have hi4 : i ≤ 4 := by have := Finset.mem_range.mp hi; omega
      rw [hleib i hi4 z θ hz hθ,
        show (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                * Work.Spaces.DzIter (i - b) g z θ))
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) from by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring]
      have hCS := Work.FTS.StrongEps.E4R3.slot_sum_sq_le (Finset.range (i + 1))
        (fun b => (i.choose b : ℝ))
        (fun b => Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z)
        (fun b => Work.Spaces.DzIter (i - b) g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (Kc := Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) hK2nn
        (fun b hb => by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          exact hbin i hi4 b hb)
        (fun b hb => hx b (by have := Finset.mem_range.mp hb; omega) z hz)
      have hy : ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ 5 * B := by
        have h1 : ∀ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ B := by
          intro b hb
          have hb4 : i - b ≤ 4 := by have := Finset.mem_range.mp hb; omega
          exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) hb4
        calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ ∑ _b ∈ Finset.range (i + 1), B := Finset.sum_le_sum h1
          _ = ((i + 1 : ℕ) : ℝ) * B := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ 5 * B := by
              have hi5 : i + 1 ≤ 5 := by have := Finset.mem_range.mp hi; omega
              have hc : ((i + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hi5
              exact mul_le_mul_of_nonneg_right hc hBnn
      have hcard : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
        rw [Finset.card_range]
        have hi5 : i + 1 ≤ 5 := by have := Finset.mem_range.mp hi; omega
        exact_mod_cast hi5
      have hA : 256 * ((Finset.range (i + 1)).card : ℝ) ≤ 256 * 5 :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      have hC : (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B) :=
        mul_le_mul_of_nonneg_left hy hK2nn
      have hS0 : 0 ≤ ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        Finset.sum_nonneg fun b _ => sq_nonneg _
      refine hCS.trans ?_
      have h1 := mul_le_mul hA hC (mul_nonneg hK2nn hS0) (by norm_num : (0 : ℝ) ≤ 256 * 5)
      have h2 : (256 * ((Finset.range (i + 1)).card : ℝ))
            * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
              * (∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
          = 256 * ((Finset.range (i + 1)).card : ℝ) * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by ring
      have h3 : (256 * 5) * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B))
          = 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by ring
      rw [h2, h3] at h1
      exact h1
    have hmix : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
        rw [hleibm j i (by omega) hj4 z θ hz hθ,
          show (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                  * Work.Spaces.mixed (j - b) i g z θ)) * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                  * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) from by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun b _ => by ring]
        have hCS := Work.FTS.StrongEps.E4R3.slot_sum_sq_le (Finset.range (j + 1))
          (fun b => (j.choose b : ℝ))
          (fun b => Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z)
          (fun b => Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)
          (Kc := Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) hK2nn
          (fun b hb => by
            rw [abs_of_nonneg (Nat.cast_nonneg _)]
            exact hbin j hj4 b hb)
          (fun b hb => hx b (by have := Finset.mem_range.mp hb; omega) z hz)
        have hy : ∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
              * Work.Spaces.Wt α z θ) ^ 2 ≤ 5 * B := by
          have h1 : ∀ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2 ≤ B := by
            intro b hb
            have hb4 : i + (j - b) ≤ 4 := by have := Finset.mem_range.mp hb; omega
            exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i (j - b) hc.1 hb4
          calc ∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2
              ≤ ∑ _b ∈ Finset.range (j + 1), B := Finset.sum_le_sum h1
            _ = ((j + 1 : ℕ) : ℝ) * B := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ 5 * B := by
                have hj5 : j + 1 ≤ 5 := by have := Finset.mem_range.mp hj; omega
                have hc5 : ((j + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hj5
                exact mul_le_mul_of_nonneg_right hc5 hBnn
        have hcard : ((Finset.range (j + 1)).card : ℝ) ≤ 5 := by
          rw [Finset.card_range]
          have hj5 : j + 1 ≤ 5 := by have := Finset.mem_range.mp hj; omega
          exact_mod_cast hj5
        have hA : 256 * ((Finset.range (j + 1)).card : ℝ) ≤ 256 * 5 :=
          mul_le_mul_of_nonneg_left hcard (by norm_num)
        have hC : (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
              * (∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B) :=
          mul_le_mul_of_nonneg_left hy hK2nn
        have hS0 : 0 ≤ ∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
              * Work.Spaces.Wt α z θ) ^ 2 := Finset.sum_nonneg fun b _ => sq_nonneg _
        refine hCS.trans ?_
        have h1 := mul_le_mul hA hC (mul_nonneg hK2nn hS0) (by norm_num : (0 : ℝ) ≤ 256 * 5)
        have h2 : (256 * ((Finset.range (j + 1)).card : ℝ))
              * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
                * (∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                  * Work.Spaces.Wt α z θ) ^ 2))
            = 256 * ((Finset.range (j + 1)).card : ℝ) * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
              * (∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2) := by ring
        have h3 : (256 * 5) * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B))
            = 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by ring
        rw [h2, h3] at h1
        exact h1
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hBnn
    rw [Work.Spaces.HkIntegrand]
    have hsum1 : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i
          (fun z θ => Work.Construction.L12 g z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
      calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i
            (fun z θ => Work.Construction.L12 g z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 5, 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B :=
            Finset.sum_le_sum fun i hi => hpure i hi
        _ = 5 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ 25 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
      calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
              6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hmix i hi j hj
        _ = 25 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    refine (add_le_add hsum1 hsum2).trans ?_
    have h3 : 5 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B)
        + 25 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B)
        ≤ 200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * B := by
      nlinarith [hBnn, hK2nn]
    exact h3
  -- integration
  have hptint : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 g z * g z θ)
      ≤ (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * Work.Spaces.HkSq α 4 g := by
    rw [Work.Spaces.HkSq]
    have hEq : (∫ z in Work.Spaces.Iz, (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
        = (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * Work.Spaces.HkSq α 4 g := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    rw [← hEq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      (hmem.2.const_mul _) ?_
    have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    rw [← hmeas]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    change (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => Work.Construction.L12 g z * g z θ) z θ)
        ≤ (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ
    rw [show (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        = ∫ θ in Work.Spaces.Iθ, (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * Work.Spaces.HkIntegrand α 4 g z θ from
      (MeasureTheory.integral_const_mul _ _).symm]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      ((hmem.1 z (by simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz)).const_mul _) ?_
    filter_upwards [Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hθ
    exact (hpt z θ hz hθ).trans (le_of_eq (by ring))
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * g z θ)
      ≤ Real.sqrt (200000 * Kc) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h := hptint
    rw [hHk] at h
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * g z θ)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 g z * g z θ)) := rfl
      _ ≤ Real.sqrt ((200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (Work.FTS.Nonlin.Xn α g) ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt (200000 * Kc) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
          have h1 : (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
                * (Work.FTS.Nonlin.Xn α g) ^ 2
              = (200000 * Kc) * ((Work.FTS.Nonlin.Xn α g) ^ 2
                  * (Work.FTS.Nonlin.Xn α g) ^ 2) := by ring
          rw [h1, Real.sqrt_mul (by positivity)]
          congr 1
          rw [show (Work.FTS.Nonlin.Xn α g) ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2
              = ((Work.FTS.Nonlin.Xn α g) ^ 2) ^ 2 from by ring,
            Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hfun : Work.FTS.Nonlin.N03g α g
      = fun z θ => (1 / α) * (Work.Construction.L12 g z * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  -- the `ℋ⁴`-honesty of `N₀₃`: the primed product rule applied to the radial factor `L₁₂(g)`
  -- and `g`, then the constant `1/α` pulled out.
  have hL12pkg := hN.l12H α hIoc g hhqo h0
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hprod := hN.prod α hIoc (fun z _ => Work.Construction.L12 g z) g
    ⟨hL12sm, hL12pkg.1⟩ hhqo
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hprod.1
  · rw [hfun, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)]
    calc (1 / α) * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * g z θ)
        ≤ (1 / α) * (Real.sqrt (200000 * Kc) * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
          mul_le_mul_of_nonneg_left hXn (by positivity)
      _ ≤ (Real.sqrt (200000 * Kc) + 1)
            * (α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
          rw [Real.rpow_neg_one, inv_eq_one_div]
          have h1 : (0 : ℝ) ≤ (1 / α) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by positivity
          have h2 : Real.sqrt (200000 * Kc) ≤ Real.sqrt (200000 * Kc) + 1 := by linarith
          nlinarith [mul_le_mul_of_nonneg_right h2 h1]

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row6u =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row6`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular profile `3 sin 2θ` and its basic calculus

(verbatim from `Work.FTS.NonlinRows.NRow6`, where the corresponding declarations are private). -/

private def Aang : ℝ → ℝ := fun θ => 3 * Real.sin (2 * θ)

private theorem hasDerivAt_Aang (θ : ℝ) : HasDerivAt Aang (6 * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * (2 * 1)) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
  have h3 : HasDerivAt (fun t : ℝ => 3 * Real.sin (2 * t))
      (3 * (Real.cos (2 * θ) * (2 * 1))) θ := h.const_mul 3
  have h3' : HasDerivAt Aang (3 * (Real.cos (2 * θ) * (2 * 1))) θ := h3
  rwa [show (3 : ℝ) * (Real.cos (2 * θ) * (2 * 1)) = 6 * Real.cos (2 * θ) from by ring] at h3'

private theorem abs_Aang_le (θ : ℝ) : |Aang θ| ≤ 3 := by
  have h : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  simp only [Aang, abs_mul]
  have h3 : |(3 : ℝ)| = 3 := by norm_num
  rw [h3]
  linarith

private theorem abs_dthU_Aang_le (θ : ℝ) : |Work.Spaces.dthU Aang θ| ≤ 6 := by
  have hd : deriv Aang θ = 6 * Real.cos (2 * θ) := (hasDerivAt_Aang θ).deriv
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  show |Real.sin (2 * θ) * deriv Aang θ| ≤ 6
  rw [hd, abs_mul, abs_mul]
  have h6 : |(6 : ℝ)| = 6 := by norm_num
  rw [h6]
  nlinarith [abs_nonneg (Real.sin (2 * θ)), abs_nonneg (Real.cos (2 * θ))]

/-! ## The angular smoothness of `c2m` -/

private theorem contDiff_c2m (n : WithTop ℕ∞) : ContDiff ℝ n Work.Construction.c2m := by
  show ContDiff ℝ n (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
  exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub (Real.contDiff_sin.pow 2)

private theorem differentiableAt_c2m (θ : ℝ) : DifferentiableAt ℝ Work.Construction.c2m θ := by
  show DifferentiableAt ℝ (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2) θ
  fun_prop

private theorem smoothOpen_c2m_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0
  exact (contDiff_c2m Work.Stability.smoothOrder).contDiffOn.comp contDiffOn_snd
    (fun p _ => Set.mem_univ p.2)

/-! ## The coefficient `fcoef = -c2m(θ)·L₁₂(g)(z)` -/

/-- The `θ`-dependent coefficient of `N₀₅ᵇ`. -/
private abbrev coeff6 (g : Fn) : Fn :=
  fun z θ => (-1 : ℝ) * (Work.Construction.c2m θ * Work.Construction.L12 g z)

/-- `∂_θ` of an angular `×` radial product. -/
private theorem pth_ang_rad (a : ℝ → ℝ) (r : ℝ → ℝ) (ha : ∀ θ, DifferentiableAt ℝ a θ) :
    Work.Spaces.pth (fun z θ => a θ * r z) = fun z θ => deriv a θ * r z := by
  funext z θ
  show deriv (fun θ' => a θ' * r z) θ = deriv a θ * r z
  exact deriv_mul_const (ha θ) (r z)

/-- `∂_θ (coeff6 g) = 3 sin(2θ)·L₁₂(g)(z)`. -/
private theorem pth_coeff6 (g : Fn) :
    Work.Spaces.pth (coeff6 g) = fun z θ => Aang θ * Work.Construction.L12 g z := by
  have hcongr : coeff6 g = fun z θ =>
      (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ') θ
        * (fun z' => Work.Construction.L12 g z') z := by
    funext z θ
    simp only [coeff6]
    ring
  rw [hcongr, pth_ang_rad (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ')
    (fun z' => Work.Construction.L12 g z')
    (fun θ => (differentiableAt_c2m θ).const_mul (-1))]
  funext z θ
  show deriv (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ') θ
      * Work.Construction.L12 g z = Aang θ * Work.Construction.L12 g z
  rw [deriv_const_mul (-1) (differentiableAt_c2m θ),
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_deriv θ]
  simp only [Aang]
  ring

/-- The mixed iterates of `∂_θ (coeff6 g)`. -/
private theorem mixed_pth_coeff6 (g : Fn) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.pth (coeff6 g)) z θ
      = Work.Spaces.DthIter i (fun _ θ' => Aang θ') 0 θ
        * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 g z) z := by
  rw [pth_coeff6]
  exact Work.FTS.Nonlinear.Pieces.mixed_ang_rad Aang
    (fun z => Work.Construction.L12 g z) j i z θ

/-- The pointwise bound of the constituents of `CoefTh 1 (coeff6 g)`. -/
private theorem mixed_pth_coeff6_le {M : ℝ} (hM : 0 ≤ M) {g : Fn}
    (hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M)
    {b i : ℕ} (hbi : b + i ≤ 1) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    |Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g)) z θ| ≤ 6 * M := by
  have hDi : |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Aang θ') 0 θ| ≤ 6 := by
    have hi1 : i ≤ 1 := by omega
    interval_cases i
    · simp only [Work.Spaces.DthIter_zero]
      exact le_trans (abs_Aang_le θ) (by norm_num)
    · rw [Work.FTS.LocData.DthIter_rad_eq 1 Aang 0 θ, Function.iterate_one]
      exact abs_dthU_Aang_le θ
  have hDj : |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M :=
    hLpt b (by omega) z hz
  rw [mixed_pth_coeff6]
  rw [abs_mul]
  exact mul_le_mul hDi hDj (abs_nonneg _) (by norm_num)

/-- The `supAbsO`-bound of the constituents of `CoefTh 1 (coeff6 g)`. -/
private theorem sup_mixed_pth_coeff6 {M : ℝ} (hM : 0 ≤ M) {g : Fn}
    (hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M)
    {b i : ℕ} (hbi : b + i ≤ 1) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g))) ≤ 6 * M :=
  Work.FTS.H2.supAbsO_le (fun z θ hz hθ0 hθ1 => mixed_pth_coeff6_le hM hLpt hbi hz hθ0 hθ1)

/-- `CoefTh 1 f ≤ 4 K` from a uniform bound `K` on the three constituents. -/
private theorem coefTh_one_le_of_sup {f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ b i : ℕ, b + i ≤ 1 →
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) ≤ K) :
    Work.FTS.VocabO.CoefTh 1 f ≤ 4 * K := by
  have hterm : ∀ b ∈ Finset.range 2, ∀ i ∈ Finset.range 2,
      (if b + i ≤ 1 then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) ≤ K := by
    intro b _ i _
    by_cases hc : b + i ≤ 1
    · rw [if_pos hc]; exact h b i hc
    · rw [if_neg hc]; exact hK
  unfold Work.FTS.VocabO.CoefTh
  refine le_trans (Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun i hi =>
    hterm b hb i hi) ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-! ## Row 6 -/

theorem n0row6u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g) ∧
        |IP α (Work.FTS.Nonlin.N05bF α g) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCi, _hα₂pos⟩ := hN.pos
  obtain ⟨hCt, _⟩ := hE.pos
  obtain ⟨Cam, hCampos, hCam⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨KL, hKLpos, hKLb⟩ := L12_dzdIter_abs_le_open
  refine ⟨Ct * (Cam * 1000 * Ci + 24 * KL) + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hsmg hmem4 hmem5 hL120 hdec hells hellg
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨hLmem, hLle⟩ :=
    hN.l12H α hIoc g (show Work.FTS.VocabO.HQo α 4 g from ⟨hsmg, hmem4⟩) hL120
  -- the uniform bound of the `D_z`-iterates of `L₁₂(g)` (honest version)
  have hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
        ≤ KL * Work.FTS.Nonlin.Xn α g :=
    fun b hb z hz => hKLb hα hα1 hsmg hmem4 hL120 b hb z hz
  -- smoothness of the radial factor and of the coefficient
  have hLsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hellg.smooth hellg.V.1.1
  have hc2mLsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_c2m_L12 hα hellg.smooth hellg.V.1.1
  have hfSm : Work.FTS.EllipticEst.SmoothOpen (coeff6 g) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hc2mLsm
  -- the angular-multiplication package for `c2m`
  have ham := hCam α hα hα1 Work.Construction.c2m
    (fun z _ => Work.Construction.L12 g z) 1000
    smoothOpen_c2m_ang
    (fun θ hθ => by
      have h := Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ
      linarith)
    (fun i hi hi4 θ hθ => by
      have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hstep : 1000 * (Real.sin (2 * θ)) ^ (2 : ℝ) ≤ 1000 * Real.sin (2 * θ) := by
        rw [Real.rpow_two]
        nlinarith [hsin0, hsin1, sq_nonneg (Real.sin (2 * θ))]
      exact h.trans hstep)
    hLsm hLmem
  have hfMem : Work.Spaces.HkMem α 4 (coeff6 g) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-1) ham.1
  -- the norm bound of the coefficient
  have hXn_f : Work.FTS.Nonlin.Xn α (coeff6 g)
      ≤ (Cam * 1000 * Ci) * Work.FTS.Nonlin.Xn α g := by
    have h1 : Work.FTS.Nonlin.Xn α (coeff6 g)
        = Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) := by
      simp only [coeff6, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_neg, abs_one,
        one_mul]
    rw [h1]
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z)
        ≤ Cam * 1000 * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.L12 g z) := ham.2
      _ ≤ Cam * 1000 * (Ci * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_left hLle (by positivity)
      _ = (Cam * 1000 * Ci) * Work.FTS.Nonlin.Xn α g := by ring
  -- the flat angular coefficient
  have hsup : ∀ b i : ℕ, b + i ≤ 1 →
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g)))
        ≤ 6 * (KL * Work.FTS.Nonlin.Xn α g) :=
    fun b i hbi => sup_mixed_pth_coeff6 (by positivity) hLpt hbi
  have hcoef : Work.FTS.VocabO.CoefTh 1 (coeff6 g)
      ≤ (24 * KL) * Work.FTS.Nonlin.Xn α g := by
    refine (coefTh_one_le_of_sup (by positivity) hsup).trans (le_of_eq ?_)
    ring
  have hcoefThMem : Work.FTS.VocabO.CoefThMem 1 (coeff6 g) :=
    fun b i hbi => ⟨6 * (KL * Work.FTS.Nonlin.Xn α g),
      fun z θ hz hθ0 hθ1 => mixed_pth_coeff6_le (by positivity) hLpt hbi hz hθ0 hθ1⟩
  -- the `ℋ⁴`-honesty
  have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 4) (f := g) hsmg hmem5
  have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hsmg.Dz
  have hprod := hN.prod α hIoc (coeff6 g) (Work.Spaces.Dz g)
    ⟨hfSm, hfMem⟩ ⟨hDzSm, hDzMem⟩
  have hfun : Work.FTS.Nonlin.N05bF α g
      = fun z θ => coeff6 g z θ * Work.Spaces.Dz g z θ := by
    funext z θ
    simp only [coeff6, Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hprod.1
  · rw [hfun]
    have ht2 := hE.t2 α hIoc (coeff6 g) g hfSm hfMem hcoefThMem hsmg hmem4 hmem5 hdec
    refine ht2.trans ?_
    have hsum : Work.FTS.Nonlin.Xn α (coeff6 g) + Work.FTS.VocabO.CoefTh 1 (coeff6 g)
        ≤ (Cam * 1000 * Ci + 24 * KL) * Work.FTS.Nonlin.Xn α g := by
      have hPQ : (Cam * 1000 * Ci + 24 * KL) * Work.FTS.Nonlin.Xn α g
          = (Cam * 1000 * Ci) * Work.FTS.Nonlin.Xn α g
            + (24 * KL) * Work.FTS.Nonlin.Xn α g := by ring
      rw [hPQ]
      linarith [hXn_f, hcoef]
    calc Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α (coeff6 g) + Work.FTS.VocabO.CoefTh 1 (coeff6 g))
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ))
          * ((Cam * 1000 * Ci + 24 * KL) * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g ^ 2 := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum ?_) (by positivity)
          exact mul_nonneg hCt.le (Real.rpow_nonneg hα.le _)
      _ = (Ct * (Cam * 1000 * Ci + 24 * KL))
          * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by ring
      _ ≤ (Ct * (Cam * 1000 * Ci + 24 * KL) + 1)
          * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The `z = ∞` decay of the profile and of its `D`-derivatives of order `≤ 4`. -/
theorem CtxT.hdecay {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.DecayAll 4 g := decayAll_of_classC h.hα h.hg h.hco




end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.jeps_tendstoUniformlyOn_of_continuousOn_of_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

open scoped Real Topology
open MeasureTheory Set Filter

theorem jeps_tendstoUniformlyOn_of_continuousOn_of_shift {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {X : ℝ → ℝ → ℝ} {ε : ℕ → ℝ}
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hXc : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Work.FTS.StrongEps.Quad)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.StrongEps.Quad)
    (hshift : ∀ η > 0, ∃ δ > 0, ∀ p ∈ K, ∀ q : ℝ × ℝ, ‖q‖ ≤ δ →
      dist (Work.FTS.StrongEps.sPhi p.1 p.2 q) p ≤ η) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ (ε n) X p.1 p.2)
      (fun p : ℝ × ℝ => X p.1 p.2) Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hη2 : (0 : ℝ) < η / 2 := by linarith
  -- ## A compact halo of `K` inside the open quadrant
  obtain ⟨r₁, hr₁, hL₁⟩ := hK.exists_cthickening_subset_open isOpen_Quad hKQ
  obtain ⟨r₂, hr₂, hcomp₂⟩ := hK.exists_isCompact_cthickening
  set d : ℝ := min r₁ r₂ with hddef
  have hdpos : 0 < d := by rw [hddef]; exact lt_min hr₁ hr₂
  have hdle₁ : d ≤ r₁ := by rw [hddef]; exact min_le_left _ _
  have hdle₂ : d ≤ r₂ := by rw [hddef]; exact min_le_right _ _
  have hLsub : Metric.cthickening d K ⊆ Quad :=
    (Metric.cthickening_mono hdle₁ K).trans hL₁
  have hLcomp : IsCompact (Metric.cthickening d K) :=
    hcomp₂.of_isClosed_subset Metric.isClosed_cthickening (Metric.cthickening_mono hdle₂ K)
  -- ## `X` is uniformly continuous on the halo
  obtain ⟨δc, hδcpos, hδc⟩ := Metric.uniformContinuousOn_iff.mp
    (hLcomp.uniformContinuousOn_of_continuous (hXc.mono hLsub)) (η / 2) hη2
  -- ## The shift threshold, small compared with `η/2`, `δc` and the halo radius
  set η₁ : ℝ := min (min (η / 2) δc) d / 2 with hη₁def
  have hη₁pos : 0 < η₁ := by
    rw [hη₁def]
    have h : 0 < min (min (η / 2) δc) d := lt_min (lt_min hη2 hδcpos) hdpos
    linarith
  have hη₁η : η₁ ≤ η / 2 := by
    rw [hη₁def]
    have h : min (min (η / 2) δc) d ≤ η / 2 :=
      (min_le_left (min (η / 2) δc) d).trans (min_le_left (η / 2) δc)
    linarith
  have hη₁δc : η₁ < δc := by
    rw [hη₁def]
    have h₁ : min (min (η / 2) δc) d ≤ min (η / 2) δc := min_le_left _ _
    have h₂ : min (η / 2) δc ≤ δc := min_le_right _ _
    linarith
  have hη₁d : η₁ < d := by
    rw [hη₁def]
    have h : min (min (η / 2) δc) d ≤ d := min_le_right _ _
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := hshift η₁ hη₁pos
  -- ## Eventually `ε n ≤ δ`
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ δ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hε0 δ hδpos
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos n)] at h
    exact h.le
  filter_upwards [hev] with n hεn p hp
  have hpQ : 0 < p.1 ∧ p.2 ∈ Set.Ioo 0 (π / 2) := hKQ hp
  -- ## On the ball of radius `ε n`, the shifted profile is within `η/2` of `X p`
  have hbound : ∀ q : ℝ × ℝ, ‖q‖ ≤ ε n →
      |X (Work.FTS.StrongEps.zShift p.1 q.1) (Work.FTS.StrongEps.thShift p.2 q.2)
        - X p.1 p.2| ≤ η / 2 := by
    intro q hq
    have hqδ : ‖q‖ ≤ δ := hq.trans hεn
    have hdist : dist (sPhi p.1 p.2 q) p ≤ η₁ := hδ p hp q hqδ
    have hmem : sPhi p.1 p.2 q ∈ Metric.cthickening d K :=
      Metric.mem_cthickening_of_dist_le _ p d K hp (le_of_lt (lt_of_le_of_lt hdist hη₁d))
    have hpL : p ∈ Metric.cthickening d K :=
      Metric.mem_cthickening_of_dist_le p p d K hp (by rw [dist_self]; exact hdpos.le)
    have hclose := hδc _ hmem _ hpL (lt_of_le_of_lt hdist hη₁δc)
    rw [Real.dist_eq] at hclose
    exact le_of_lt (by simpa only [sPhi, zShift, thShift] using hclose)
  -- ## The peak estimate
  have hpeak :=
    abs_Jeps_sub_le_of_bound_of_continuousOn ρ hρ hpQ.1 hpQ.2 (hεpos n) hXc hbound
  rw [Real.dist_eq, abs_sub_comm]
  linarith

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.Jeps_tendsto_of_modulus =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.E5G

theorem Jeps_tendsto_of_modulus {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {Y : ℕ → Work.FTS.Galerkin.Fn} {Yl : Work.FTS.Galerkin.Fn} {ε : ℕ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (Y n)) Work.FTS.StrongEps.Quad)
    (hequi : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p : ℝ × ℝ, ‖p‖ ≤ δ →
      |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ| ≤ η)
    (hlim : Filter.Tendsto (fun n : ℕ => Y n z θ) Filter.atTop (nhds (Yl z θ))) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.StrongEps.Jeps ρ (ε n) (Y n) z θ) Filter.atTop
      (nhds (Yl z θ)) := by
  -- The equicontinuity modulus `δ` of `hequi` is independent of `n`; since `ε n → 0`, for all
  -- large `n` the ball `‖p‖ ≤ ε n` on which the kernel `Jker ρ (ε n)` lives is contained in the
  -- ball `‖p‖ ≤ δ`, so the profiles are uniformly within `η` of their value at `(z,θ)` there.
  have huc : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ p : ℝ × ℝ, ‖p‖ ≤ ε n →
      |Y n (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - Y n z θ| ≤ η := by
    intro η hη
    obtain ⟨δ, hδpos, hδ⟩ := hequi η hη
    have hsmall : ∀ᶠ n in Filter.atTop, ε n < δ := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hε0 δ hδpos
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have h := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos n)] at h
      exact h
    filter_upwards [hsmall] with n hn p hp
    exact hδ n p (le_trans hp hn.le)
  -- The peak estimate for the mollifier turns the uniform closeness on the shrinking ball into
  -- the sequential convergence of the mollified profiles to their pointwise limit.
  exact Work.FTS.StrongEps.tendsto_Jeps_of_continuousOn ρ hρ hz hθ
    (fun n => hcont n) hεpos huc hlim

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.Assembly_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E1Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The squared `ℋⁿ`-bound for `E1`, open class, given the radial slot bound.** -/
theorem E1_hkSq_le_O_of
    (hSLOT : ∃ Cs : ℝ, 0 < Cs ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cs * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cs, hCspos, hS⟩ := hSLOT
  obtain ⟨Ca, hCapos, hA⟩ :=
    Work.FTS.CoercivityFix.Transfer.E1Norm.E1_angRad_le
  refine ⟨Ca * Cs + 1, by positivity, ?_⟩
  intro α hα hα1 n hn f hf
  obtain ⟨hint, hbound⟩ := hS α hα hα1 f hf n hn
  have h1 := hA α n f hα hα1 hn hint
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have h2 : Ca * α ^ 2 * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ Ca * α ^ 2 * (Cs * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have h3 : (0 : ℝ) ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
    have := Work.Spaces.HkSq_nonneg α n f
    have := Work.Spaces.HkSq_nonneg α n (Work.Spaces.Dth f)
    linarith
  calc Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
      ≤ Ca * α ^ 2 * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := h1
    _ ≤ Ca * α ^ 2 * (Cs * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) := h2
    _ = (Ca * Cs) * α ^ 2 * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
    _ ≤ (Ca * Cs + 1) * α ^ 2 * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
        rw [show (Ca * Cs) * α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
            = (Ca * Cs) * (α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) from by ring,
          show (Ca * Cs + 1) * α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
            = (Ca * Cs + 1) * (α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) from by ring]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg hα2 h3)

/-- **The `ℋⁿ`-norm bound for `E1`, open class, given the radial slot bound.** -/
theorem E1_norm_O_of
    (hSLOT : ∃ Cs : ℝ, 0 < Cs ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cs * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  obtain ⟨C, hCpos, hC⟩ := E1_hkSq_le_O_of hSLOT
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro α hα hα1 n hn f hf
  have hkey := hC α hα hα1 n hn f hf
  have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hNd : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
  -- the elementary inequality `Nf + Nd ≤ (√Nf + √Nd)²`
  have hsum : Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
      ≤ (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2 := by
    have h1 := Real.sq_sqrt hNf
    have h2 := Real.sq_sqrt hNd
    have h3 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α n f) := Real.sqrt_nonneg _
    have h4 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := Real.sqrt_nonneg _
    nlinarith [h1, h2, h3, h4]
  have hbound : C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      ≤ (α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))) ^ 2 := by
    have h1 : C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        ≤ C * α ^ 2 * ((Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hCpos.le]
    ring
  calc Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
      = Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)) := rfl
    _ ≤ Real.sqrt ((α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))) ^ 2) :=
        Real.sqrt_le_sqrt (le_trans hkey hbound)
    _ = α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_sq (by positivity)
    _ = α * Real.sqrt C * (Work.Spaces.HkNorm α n f
          + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := rfl

end Work.FTS.StrongEps.EpsE4Thr.E1Open
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSMaj =====
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



/-- **The pointwise bound** `(D_z^j (radS α f)(z))² w(z)² ≤ SmajA α f j K z` on `(0,∞)`. -/
theorem radS_sq_le_SmajA_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) {j : ℕ} (hj : j ≤ 3) {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b ≤ 4, ∀ z ∈ IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) :
    ∀ z ∈ IoiA, (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
      * (Work.Spaces.w z) ^ 2 ≤ Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j K z := by
  have hC0 : ∀ b, ((j.choose b : ℕ) : ℝ) ^ 2 = ((j.choose b : ℝ)) ^ 2 := by
    intro b; push_cast; ring
  intro z hz
  rw [radS_DzdIter_eq_O α hα hα1 hO hmem5 hl12 hj z hz,
    Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA]
  set S1 : ℝ := Work.FTS.CoercivityFix.Transfer.E2pkg.W1 α f j z with hS1
  set S2 : ℝ := Work.FTS.CoercivityFix.Transfer.E2pkg.W2 α f j z with hS2
  set S3 : ℝ := Work.FTS.CoercivityFix.Transfer.E2pkg.W3 α f j z with hS3
  have hsq : (-S1 + S2 + S3) ^ 2 ≤ 3 * (S1 ^ 2 + S2 ^ 2 + S3 ^ 2) := by
    nlinarith [sq_nonneg (S1 - S2), sq_nonneg (S2 - S3), sq_nonneg (S3 + S1)]
  have hw_nn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hS1b : S1 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
      * (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := by
    have hcs : S1 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter (b + 1)
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := by
      rw [hS1, Work.FTS.CoercivityFix.Transfer.E2pkg.W1]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hK1 : (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter (b + 1)
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b hb => ?_
      have hbj : b + 1 ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hb1 : |Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd (b + 1) hbj z hz
      rw [mul_pow, hC0 b]
      exact mul_le_mul_of_nonneg_left
        (sq_le_sq' (abs_le.mp hb1).1 (abs_le.mp hb1).2) (sq_nonneg _)
    have hSnn : 0 ≤ (∑ b ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    calc S1 ^ 2 ≤ _ * (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) := hcs
      _ ≤ ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2) :=
          mul_le_mul_of_nonneg_right hK1 hSnn
  have hS2b : S2 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
      * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := by
    have hcs : S2 ^ 2 ≤ (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := by
      rw [hS2, Work.FTS.CoercivityFix.Transfer.E2pkg.W2]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hK2 : (∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b
            (Work.FTS.CoercivityFix.Transfer.ampA α) z)) ^ 2)
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b hb => ?_
      have hbj : b ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hb1 : |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd b hbj z hz
      rw [mul_pow, hC0 b]
      exact mul_le_mul_of_nonneg_left
        (sq_le_sq' (abs_le.mp hb1).1 (abs_le.mp hb1).2) (sq_nonneg _)
    have hSnn : 0 ≤ (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    calc S2 ^ 2 ≤ _ * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) := hcs
      _ ≤ ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
          * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2) :=
          mul_le_mul_of_nonneg_right hK2 hSnn
  have hS3b : S3 ^ 2 = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
      * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2) := by
    rw [hS3, Work.FTS.CoercivityFix.Transfer.E2pkg.W3]; ring
  have h1 : (S1 ^ 2 + S2 ^ 2 + S3 ^ 2) * (Work.Spaces.w z) ^ 2
      ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := by
    have e1 : (S1 ^ 2) * (Work.Spaces.w z) ^ 2
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
      calc S1 ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2))
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hS1b hw_nn
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * ((∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2) := by rw [← Finset.sum_mul]
    have e2 : (S2 ^ 2) * (Work.Spaces.w z) ^ 2
        ≤ (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      calc S2 ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2))
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hS2b hw_nn
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * ((∑ b ∈ Finset.range (j + 1), (Work.Elliptic.Qang f (j - b) z) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
        _ = ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * K ^ 2)
              * (∑ b ∈ Finset.range (j + 1),
                  (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
            rw [← Finset.sum_mul]
    have e3 : (S3 ^ 2) * (Work.Spaces.w z) ^ 2
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
          * ((Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) := by
      rw [hS3b]; ring
    linarith [e1, e2, e3.le]
  have h2 := mul_le_mul_of_nonneg_right hsq hw_nn
  linarith [h1, h2]

end Work.FTS.StrongEps.EpsE4Thr.E2O
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HkIntegrand_sqrt_add_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr

theorem HkIntegrand_sqrt_add_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
          + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) := by
  intro z hz θ hθ
  -- The right-hand side is nonnegative, so the two degenerate cases are immediate.
  have hRHS : 0 ≤ Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
      + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
  · -- `z = 0`: the integrand vanishes (the radial weight is `0` there).
    subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst, Real.sqrt_zero]
    exact hRHS
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h1 | hθpos
  · -- `θ = 0`: `sin (2θ) = 0`, and the integrand vanishes there identically.
    subst h1
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
        (fun z θ => f z θ + g z θ) z 0 (by norm_num), Real.sqrt_zero]
    exact hRHS
  rcases lt_or_eq_of_le hθ.2 with h2 | h2
  · -- The open quadrant: the pointwise Euclidean triangle inequality of the slot vector.
    exact Work.FTS.GalFields.Norm.hk5_sqrt_HkIntegrand_add_le α k
      (Work.FTS.EllipticEst.smoothOpen_of_forall hf)
      (Work.FTS.EllipticEst.smoothOpen_of_forall hg)
      z θ hzpos hθpos h2
  · -- `θ = π/2`: `sin (2θ) = 0`, and the integrand vanishes there identically.
    subst h2
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
        (fun z θ => f z θ + g z θ) z (π / 2)
        (by rw [show 2 * (π / 2) = π by ring]; exact Real.sin_pi), Real.sqrt_zero]
    exact hRHS

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimAux.ThShiftNullPreimage =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XBallLimAux

set_option autoImplicit false

/-- **The angular shift pulls back product-null sets to null sets.**  For `ε > 0` and a null
measurable set `Z ⊆ ℝ`, the set of `(θ,p) ∈ Iθ × [-ε,ε]` with `thShift θ p ∈ Z` has vanishing
product measure. -/
theorem thShift_null_preimage {ε : ℝ} (hε : 0 < ε) {Z : Set ℝ} (hZ : MeasurableSet Z)
    (hZ0 : (MeasureTheory.volume : MeasureTheory.Measure ℝ) Z = 0) :
    ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)))
      {x : ℝ × ℝ | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z} = 0 := by
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
      (MeasureTheory.volume.restrict (Set.Icc (-ε) ε)) with hμ
  -- the indicator of `Z`, as a measurable `ℝ≥0∞`-valued function
  have hU : Measurable (Z.indicator (fun _ : ℝ => (1 : ENNReal))) :=
    measurable_const.indicator hZ
  -- its angular lintegral vanishes
  have hZ01 : (∫⁻ θ in Work.Spaces.Iθ, Z.indicator (fun _ : ℝ => (1 : ENNReal)) θ) = 0 := by
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, Z.indicator (fun _ : ℝ => (1 : ENNReal)) θ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iθ) Z := by
      rw [MeasureTheory.lintegral_indicator hZ, MeasureTheory.setLIntegral_const, one_mul]
    rw [h1, MeasureTheory.Measure.restrict_apply hZ]
    exact measure_mono_null Set.inter_subset_left hZ0
  -- the shift bound, applied to the indicator
  have hAEM : AEMeasurable
      (fun x : ℝ × ℝ => Z.indicator (fun _ : ℝ => (1 : ENNReal))
        (Work.FTS.StrongEps.thShift x.1 x.2)) μ :=
    hU.aemeasurable.comp_aemeasurable
      (Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.aemeasurable_thShift_prod (ε := ε))
  have hInt0 : (∫⁻ x, Z.indicator (fun _ : ℝ => (1 : ENNReal))
      (Work.FTS.StrongEps.thShift x.1 x.2) ∂μ) = 0 := by
    have h := Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.LintegralProdThShiftLe
      (ε := ε) hε hU
    rw [hZ01, mul_zero] at h
    exact le_antisymm h bot_le
  -- hence the indicator vanishes a.e.
  have hae : (fun x : ℝ × ℝ => Z.indicator (fun _ : ℝ => (1 : ENNReal))
      (Work.FTS.StrongEps.thShift x.1 x.2)) =ᵐ[μ] 0 :=
    (MeasureTheory.lintegral_eq_zero_iff' hAEM).mp hInt0
  -- rewrite the preimage as the set where the indicator does not vanish
  have hset : {x : ℝ × ℝ | Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z}
      = {x : ℝ × ℝ | Z.indicator (fun _ : ℝ => (1 : ENNReal))
          (Work.FTS.StrongEps.thShift x.1 x.2) ≠ 0} := by
    ext x
    by_cases hx : Work.FTS.StrongEps.thShift x.1 x.2 ∈ Z <;> simp [hx]
  rw [hset]
  exact ae_iff.mp hae

end Work.FTS.StrongEps.EpsE4Thr.XBallLimAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSrc.lintegral_logSubst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSrc

theorem lintegral_logSubst (U : ℝ → ℝ → ENNReal) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, U z θ)
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * U (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  -- The closed intervals `Iz = [0,∞)`, `Iθ = [0,π/2]` differ from the open ones only by
  -- null sets, so the iterated integral may be taken over the open quadrant `(0,∞) × (0,π/2)`,
  -- and `HkSqAux.lintegral_quad_log_subst` is exactly the log-coordinate substitution there.
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ, U z θ)
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U z θ := by
    funext z
    exact (MeasureTheory.setLIntegral_congr
      (f := fun θ : ℝ => U z θ) (MeasureTheory.Ioo_ae_eq_Icc)).symm
  rw [Work.Spaces.Iz, hIθ]
  rw [(MeasureTheory.setLIntegral_congr
    (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U z θ)
    (MeasureTheory.Ioi_ae_eq_Ici)).symm]
  exact Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst U

end Work.FTS.StrongEps.EpsSrc
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWPContDiffOnQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.HkIntegrand_Jeps_le_integral =====
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

set_option maxHeartbeats 1000000

/-! ## The two parts of `HkIntegrand` -/

/-- The `D_z`-part of `HkIntegrand`: the sum of the squared weighted `D_z`-slots. -/
def HkZPart (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (Work.Spaces.DzIter i f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed part of `HkIntegrand`: the sum over the admissible pairs `(i,j)` of the squared
weighted mixed slots (`i ≥ 1`, `i + j ≤ k`), the inadmissible pairs contributing `0`. -/
def HkMPart (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    if 1 ≤ i ∧ i + j ≤ k then
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0

/-- The mixed part of `HkIntegrand` as a sum over the *filtered* set of admissible pairs
`(i,j)`: the form in which the per-slot bounds apply (no `if`). -/
def HkMPartF (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ q ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
      (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k),
    (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2

theorem HkIntegrand_eq_parts (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ = HkZPart k f z θ + HkMPart α k f z θ := rfl

theorem HkMPart_eq_HkMPartF (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkMPart α k f z θ = HkMPartF α k f z θ := by
  simp only [HkMPart, HkMPartF]
  rw [Finset.sum_filter, Finset.sum_product]

/-! ## Two elementary `Finset`-versus-integral lemmas -/

/-- **Summation of finitely many slot bounds.**  If the slots `a i` are dominated by the
integrals of `K · F i`, and each of those integrands is integrable, then the sum of the slots is
dominated by `∫ p, K p · ∑ i, F i p`.

This is `Finset.sum_le_sum` followed by the exchange of the finite sum with the integral
(`integral_finsetSum`) and `Finset.mul_sum` to pull the factor `K p` out of the finite sum. -/
theorem sum_le_integral_of_slots {ι : Type*} (K : ℝ × ℝ → ℝ) (s : Finset ι) (a : ι → ℝ)
    (F : ι → ℝ × ℝ → ℝ)
    (h : ∀ i ∈ s, a i ≤ ∫ p : ℝ × ℝ, K p * F i p)
    (hint : ∀ i ∈ s, Integrable (fun p : ℝ × ℝ => K p * F i p)) :
    ∑ i ∈ s, a i ≤ ∫ p : ℝ × ℝ, K p * ∑ i ∈ s, F i p := by
  calc ∑ i ∈ s, a i ≤ ∑ i ∈ s, ∫ p : ℝ × ℝ, K p * F i p := Finset.sum_le_sum h
    _ = ∫ p : ℝ × ℝ, ∑ i ∈ s, K p * F i p :=
        (MeasureTheory.integral_finsetSum s hint).symm
    _ = ∫ p : ℝ × ℝ, K p * ∑ i ∈ s, F i p := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        exact (Finset.mul_sum s (fun i => F i p) (K p)).symm

/-- Integrability of `p ↦ K p · ∑ i ∈ s, F i p` from the integrability of each of the terms.
The proof exchanges the finite sum with the integral (as a sum of functions). -/
theorem integrable_kernel_mul_slot_sum {ι : Type*} (K : ℝ × ℝ → ℝ) (s : Finset ι)
    (F : ι → ℝ × ℝ → ℝ) (hint : ∀ i ∈ s, Integrable (fun p : ℝ × ℝ => K p * F i p)) :
    Integrable (fun p : ℝ × ℝ => K p * ∑ i ∈ s, F i p) := by
  have h : (fun p : ℝ × ℝ => K p * ∑ i ∈ s, F i p)
      = fun p : ℝ × ℝ => ∑ i ∈ s, K p * F i p := by
    funext p
    exact Finset.mul_sum s (fun i => F i p) (K p)
  rw [h]
  exact MeasureTheory.integrable_finsetSum s hint

/-! ## Integrability of the two slot integrands -/

/-- The right-hand integrand of `slot_z_exp` is integrable: it is
`Jker ρ ε p · (e^{2c|p|} · (weighted slot)²)`, and the second factor is continuous on the
compact ball of radius `ε` (`integrable_Jker_mul`). -/
theorem integrable_slot_z_exp (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ c : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (i : ℕ) :
    Integrable (fun p : ℝ × ℝ => (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
            * (Work.Spaces.w (zShift z p.1)
                / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  refine (integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|))
        * (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
            * (Work.Spaces.w (zShift z p.1)
                / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2) ?_).congr
    (Eventually.of_forall fun p => by ring)
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
        * (Work.Spaces.w (zShift z p.1)
            / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2)))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.DzIter i f z' θ'
        * (Work.Spaces.w z' / (Real.sin (2 * θ')) ^ (Work.Spaces.eta / 2)))
      ((continuousOn_DzIter_region hz hε hθ hf i).mul
        (continuousOn_wdiv_region (z := z) (ε := ε) hz hε hθ))
  have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
  exact hexp.continuousOn.mul (hcont.pow 2)

/-- The right-hand integrand of `slot_mixed_exp` is integrable (companion of
`integrable_slot_z_exp`). -/
theorem integrable_slot_mixed_exp (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {α z θ c : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j i : ℕ) :
    Integrable (fun p : ℝ × ℝ => (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
            * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) := by
  refine (integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|))
        * (Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
            * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2) ?_).congr
    (Eventually.of_forall fun p => by ring)
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.mixed j i f (zShift z p.1) (thShift θ p.2)
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    continuousOn_shift_ball (ε := ε) hz hθ
      (A := fun z' θ' => Work.Spaces.mixed j i f z' θ' * Work.Spaces.Wt α z' θ')
      ((continuousOn_mixed_region hz hε hθ hf j i).mul
        (continuousOn_Wt_region (z := z) (ε := ε) (α := α) hz hε hθ))
  have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by fun_prop
  exact hexp.continuousOn.mul (hcont.pow 2)

/-! ## The estimate -/

theorem HkIntegrand_Jeps_le_integral (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) {z θ c : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (k : ℕ)
    (hWη : ∀ p : ℝ × ℝ, Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
            / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ
      ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :
    Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      ≤ ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
  -- the `D_z`-half: sum the single-slot bounds `slot_z_exp`
  have hZ : HkZPart k (Jeps ρ ε f) z θ ≤ ∫ p : ℝ × ℝ,
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkZPart k f (zShift z p.1) (thShift θ p.2) :=
    sum_le_integral_of_slots
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := Finset.range (k + 1))
      (a := fun i => (Work.Spaces.DzIter i (Jeps ρ ε f) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (F := fun i p => (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i _ => slot_z_exp (ρ := ρ) (ε := ε) (f := f) hρ hε hf hWη hz hθ i)
      (fun i _ => integrable_slot_z_exp ρ hρ hε hf hz hθ i)
  -- the mixed half: sum the single-slot bounds `slot_mixed_exp` over the admissible pairs
  have hM : HkMPartF α k (Jeps ρ ε f) z θ ≤ ∫ p : ℝ × ℝ,
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkMPartF α k f (zShift z p.1) (thShift θ p.2) :=
    sum_le_integral_of_slots
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
        (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k))
      (a := fun q : ℕ × ℕ =>
        (Work.Spaces.mixed q.2 q.1 (Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2)
      (F := fun q : ℕ × ℕ => fun p : ℝ × ℝ =>
        (Work.Spaces.mixed q.2 q.1 f (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
      (fun q _ => slot_mixed_exp (ρ := ρ) (ε := ε) (f := f) hρ hε hf hα hWγ hz hθ q.2 q.1)
      (fun q _ => integrable_slot_mixed_exp ρ hρ hε hf hz hθ q.2 q.1)
  -- integrability of the two assembled integrands
  have hintZ : Integrable (fun p : ℝ × ℝ =>
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkZPart k f (zShift z p.1) (thShift θ p.2)) :=
    integrable_kernel_mul_slot_sum
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := Finset.range (k + 1))
      (F := fun i p => (Work.Spaces.DzIter i f (zShift z p.1) (thShift θ p.2)
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * (thShift θ p.2))) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i _ => integrable_slot_z_exp ρ hρ hε hf hz hθ i)
  have hintM : Integrable (fun p : ℝ × ℝ =>
      (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
        * HkMPartF α k f (zShift z p.1) (thShift θ p.2)) :=
    integrable_kernel_mul_slot_sum
      (K := fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
      (s := (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter
        (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k))
      (F := fun q : ℕ × ℕ => fun p : ℝ × ℝ =>
        (Work.Spaces.mixed q.2 q.1 f (zShift z p.1) (thShift θ p.2)
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2)) ^ 2)
      (fun q _ => integrable_slot_mixed_exp ρ hρ hε hf hz hθ q.2 q.1)
  calc Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ
      = HkZPart k (Jeps ρ ε f) z θ + HkMPartF α k (Jeps ρ ε f) z θ := by
        rw [HkIntegrand_eq_parts, HkMPart_eq_HkMPartF]
    _ ≤ (∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkZPart k f (zShift z p.1) (thShift θ p.2))
        + ∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkMPartF α k f (zShift z p.1) (thShift θ p.2) := add_le_add hZ hM
    _ = ∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkZPart k f (zShift z p.1) (thShift θ p.2)
          + (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
            * HkMPartF α k f (zShift z p.1) (thShift θ p.2) :=
        (MeasureTheory.integral_add hintZ hintM).symm
    _ = ∫ p : ℝ × ℝ, (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)))
          * (HkZPart k f (zShift z p.1) (thShift θ p.2)
              + HkMPartF α k f (zShift z p.1) (thShift θ p.2)) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
    _ = ∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        dsimp only
        rw [← HkMPart_eq_HkMPartF, HkIntegrand_eq_parts]

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.integral_shift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.HkSqAux

theorem integral_shift_le {α : ℝ} {k : ℕ} {δ : ℝ}
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂))
    {f : ℝ → ℝ → ℝ} (hF : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  set r : ENNReal := ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) with hr
  have hrne : r ≠ ⊤ := by rw [hr]; exact ENNReal.ofReal_ne_top
  -- the two shifts in the log coordinates
  have hz : ∀ s : ℝ, Work.FTS.StrongEps.zShift (Real.exp s) p.1 = Real.exp (s - p.1) := by
    intro s
    rw [Work.FTS.StrongEps.zShift, ← Real.exp_add, sub_eq_add_neg]
  have hth : ∀ ζ : ℝ, Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) p.2
      = Real.arctan (Real.exp (ζ - p.2)) := by
    intro ζ
    rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]
  -- Step 1: replace the closed intervals by the open ones (null sets)
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) :=
    funext fun z => (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
  rw [hIθ]
  have hIz : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) :=
    (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  rw [hIz]
  -- Step 2: the log-coordinate substitution
  rw [lintegral_quad_log_subst (fun z θ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2)))]
  -- Step 3: the shifts become translations
  simp only [hz, hth]
  -- Step 4: translation invariance of the Lebesgue integral
  rw [lintegral_prod_shift_mul (fun s ζ => ENNReal.ofReal (logJac s ζ))
        (fun s ζ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
          (Real.arctan (Real.exp ζ)))) p.1 p.2]
  -- Step 5: the pointwise comparison coming from `hJac`
  have hpt : ∀ s ζ : ℝ,
      ENNReal.ofReal (logJac (s + p.1) (ζ + p.2))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))
        ≤ r * (ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))) := by
    intro s ζ
    have h := hJac (s + p.1) (ζ + p.2) p.1 p.2
    rw [add_sub_cancel_right, add_sub_cancel_right] at h
    have h1 : ENNReal.ofReal (logJac (s + p.1) (ζ + p.2))
        ≤ r * ENNReal.ofReal (logJac s ζ) := by
      rw [hr, ← ENNReal.ofReal_mul (Real.exp_pos (δ * (|p.1| + |p.2|))).le]
      exact ENNReal.ofReal_le_ofReal h
    calc ENNReal.ofReal (logJac (s + p.1) (ζ + p.2))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
                (Real.arctan (Real.exp ζ)))
        ≤ (r * ENNReal.ofReal (logJac s ζ))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
                (Real.arctan (Real.exp ζ))) := mul_le_mul_of_nonneg_right h1 bot_le
      _ = r * (ENNReal.ofReal (logJac s ζ)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
                (Real.arctan (Real.exp ζ)))) := by ring
  refine le_trans (MeasureTheory.lintegral_mono fun s =>
    MeasureTheory.lintegral_mono fun ζ => hpt s ζ) ?_
  -- Step 6: pull the constant `r` out of the two integrals
  rw [show (∫⁻ s, ∫⁻ ζ, r * (ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))))
        = r * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ))) from ?_]
  · -- Step 7: identify the remaining integral with `ofReal (HkSq α k f)`
    rw [← ofReal_HkSq_eq_logIntegral α k hF hcont]
  · rw [← MeasureTheory.lintegral_const_mul' r
        (fun s => ∫⁻ ζ, ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))) hrne]
    refine MeasureTheory.lintegral_congr fun s => ?_
    exact MeasureTheory.lintegral_const_mul' r
      (fun ζ => ENNReal.ofReal (logJac s ζ)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
            (Real.arctan (Real.exp ζ)))) hrne

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.LogSubstLintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.L12Sub4

/-- **The log-coordinate substitution in `lintegral` form** (unconditional, for nonnegative `u`):
the angular weight `K(θ) dθ` pushes forward to `Glw(ζ) dζ` and the radial weight `dr/r` to `ds`,
so the quadrant `∫⁻` (measure `dθ dr`, weight `K(θ)/r`) equals the plane `∫⁻` with weight `Glw`:

  `∫⁻_s ∫⁻_ζ ofReal (Glw ζ · u (e^s) (arctan (e^ζ))) = ∫⁻_z∈(0,∞) ∫⁻_θ∈Iθ ofReal (K(θ) u(z,θ)/z)`.

Hints: the angular part is `HkSqAux.lintegral_arctan_exp_subst_gen` (or
`HkSqAux.lintegral_quad_log_subst`), the radial part `HkSqAux.lintegral_exp_subst_gen`; combine with
`ENNReal.ofReal_mul` and the `kappa`/`logJac` algebra exactly as
`HkSqAux.ofReal_HkSq_eq_logIntegral` does, and replace `Ioo 0 (π/2)` by `Iθ` by a null-set change
(`MeasureTheory.Ioo_ae_eq_Icc`, `setLIntegral_congr`). -/
theorem LogSubstLintegral (u : ℝ → ℝ → ℝ) (hu : ∀ z θ, 0 ≤ u z θ) :
    (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Glw ζ * u (Real.exp s) (Real.arctan (Real.exp ζ))))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.K θ * u z θ / z) := by
  -- The pointwise identification of the two Jacobian-weighted integrands.
  have hpt : ∀ s ζ : ℝ,
      ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (Work.Spaces.K (Real.arctan (Real.exp ζ))
            * u (Real.exp s) (Real.arctan (Real.exp ζ)) / Real.exp s)
      = ENNReal.ofReal (Glw ζ * u (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    intro s ζ
    rw [← ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.logJac_nonneg s ζ)]
    congr 1
    have h1 : Real.exp s ≠ 0 := Real.exp_ne_zero s
    have h2 : (1 : ℝ) + Real.exp (2 * ζ) ≠ 0 := by positivity
    simp only [Glw, Work.FTS.StrongEps.HkSqAux.logJac, Work.FTS.StrongEps.HkSqAux.kappa]
    field_simp
  -- Replace `Iθ = Icc 0 (π/2)` by the open interval `Ioo 0 (π/2)` (a null-set change).
  rw [show (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.K θ * u z θ / z))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.K θ * u z θ / z) from
    lintegral_congr fun z => (setLIntegral_congr
      (f := fun θ : ℝ => ENNReal.ofReal (Work.Spaces.K θ * u z θ / z))
      (Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))).symm]
  -- Apply the two-dimensional log-coordinate substitution.
  rw [Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
    (fun z θ => ENNReal.ofReal (Work.Spaces.K θ * u z θ / z))]
  exact lintegral_congr fun s => lintegral_congr fun ζ => (hpt s ζ).symm

end Work.FTS.StrongEps.L12Sub4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.SlotAux.RouteAux =====
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

/-! ## Auxiliary facts for `slot_route_bounds`

The target is a pure weighted Cauchy–Schwarz estimate: the routed integral identity
(`hcomm`) writes `M = ∫ p, K p · G p` with `K` a derivative of the mollifier kernel `Jker ρ ε`
and `G` a shifted slot of the profile `f`; the hypothesis (`hW`) compares the weight at the base
point `(z,θ)` with the shifted one.  Then

  `(M · W)² ≤ (∫ |K|) · ∫ |K| · e^{2c|p|} · (G · W)²`

is `|∫ K G W| ≤ ∫ |K| |G W|` followed by Cauchy–Schwarz with respect to the (nonnegative,
compactly supported) weight `|K|`, and the pointwise comparison
`W₀² ≤ e^{2c|p|}·W²`.

The lemmas below supply (i) the integrability of `p ↦ |K p| · B p` for `B` continuous on the
ball of radius `ε` (`K` is supported there, being a derivative of the compactly supported
`Jker ρ ε`), and (ii) the nonnegativity of the two weights. -/

section Helpers

/-- `p ↦ e^{2c(|p₁|+|p₂|)}` is continuous. -/
lemma srb_continuous_exp_two (c : ℝ) :
    Continuous (fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))) := by
  refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
  exact (continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)

/-- The derivative of the second-coordinate slice of a `C¹` function is the Fréchet derivative
applied to the direction `(0,1)`. -/
private lemma srb_deriv_slice_snd_eq_fderiv {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    deriv (fun t : ℝ => F (z, t)) θ = fderiv ℝ F (z, θ) (0, 1) := by
  have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun t : ℝ => F (z, t))
      ((fderiv ℝ F (z, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
    (h.hasFDerivAt.comp θ h2).hasDerivAt
  rw [h3.deriv]; simp

/-- The derivative of the second-coordinate slice of a `C¹` function is continuous. -/
private lemma srb_continuous_deriv_slice_snd {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ F p (0, 1)) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p =>
    (srb_deriv_slice_snd_eq_fderiv (hF.differentiable_one.differentiableAt)).symm)

/-- Off the closed ball of radius `ε` the derivative of the first-coordinate slice of
`Jker ρ ε` vanishes. -/
private lemma srb_deriv_Jker_fst_eq_zero_of_notMem {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) :
    deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1 = 0 := by
  have hmax : ε < max |p.1| |p.2| := by
    by_contra hcon
    exact hp (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact not_lt.mp hcon)
  rcases lt_or_ge ε |p.1| with h1 | h1
  · -- `ε < |p₁|`: a whole neighbourhood of `p₁` consists of points with `|s| > ε`
    have hev : (fun s : ℝ => Jker ρ ε (s, p.2)) =ᶠ[𝓝 p.1] (fun _ => (0 : ℝ)) := by
      change ∀ᶠ s in 𝓝 p.1, Jker ρ ε (s, p.2) = 0
      rw [Metric.eventually_nhds_iff]
      refine ⟨(|p.1| - ε) / 2, by linarith, fun s hs => ?_⟩
      have hs' : |s - p.1| < (|p.1| - ε) / 2 := by simpa [Real.dist_eq] using hs
      have hgt : ε < |s| := by
        have h3 : |p.1| ≤ |s| + |s - p.1| := by
          calc |p.1| = |s + (p.1 - s)| := by ring_nf
            _ ≤ |s| + |p.1 - s| := abs_add_le _ _
            _ = |s| + |s - p.1| := by rw [abs_sub_comm]
        linarith
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |s| ≤ ε := le_trans (le_max_left _ _) hmem
      linarith
    rw [hev.deriv_eq, deriv_const]
  · -- `|p₁| ≤ ε`, hence `|p₂| > ε`: the whole slice vanishes
    have h2ε : ε < |p.2| := by
      rcases lt_or_ge ε |p.2| with h | h
      · exact h
      · exact absurd (max_le h1 h) (not_le.mpr hmax)
    have hev : (fun s : ℝ => Jker ρ ε (s, p.2)) = fun _ => (0 : ℝ) := by
      funext s
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |p.2| ≤ ε := le_trans (le_max_right _ _) hmem
      linarith
    rw [hev, deriv_const]

/-- Off the closed ball of radius `ε` the derivative of the second-coordinate slice of
`Jker ρ ε` vanishes. -/
private lemma srb_deriv_Jker_snd_eq_zero_of_notMem {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ} (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) :
    deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2 = 0 := by
  have hmax : ε < max |p.1| |p.2| := by
    by_contra hcon
    exact hp (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact not_lt.mp hcon)
  rcases lt_or_ge ε |p.2| with h1 | h1
  · have hev : (fun t : ℝ => Jker ρ ε (p.1, t)) =ᶠ[𝓝 p.2] (fun _ => (0 : ℝ)) := by
      change ∀ᶠ t in 𝓝 p.2, Jker ρ ε (p.1, t) = 0
      rw [Metric.eventually_nhds_iff]
      refine ⟨(|p.2| - ε) / 2, by linarith, fun t ht => ?_⟩
      have ht' : |t - p.2| < (|p.2| - ε) / 2 := by simpa [Real.dist_eq] using ht
      have hgt : ε < |t| := by
        have h3 : |p.2| ≤ |t| + |t - p.2| := by
          calc |p.2| = |t + (p.2 - t)| := by ring_nf
            _ ≤ |t| + |p.2 - t| := abs_add_le _ _
            _ = |t| + |t - p.2| := by rw [abs_sub_comm]
        linarith
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |t| ≤ ε := le_trans (le_max_right _ _) hmem
      linarith
    rw [hev.deriv_eq, deriv_const]
  · have h2ε : ε < |p.1| := by
      rcases lt_or_ge ε |p.1| with h | h
      · exact h
      · exact absurd (max_le h h1) (not_le.mpr hmax)
    have hev : (fun t : ℝ => Jker ρ ε (p.1, t)) = fun _ => (0 : ℝ) := by
      funext t
      refine Jker_eq_zero_of_not_mem hρ hε ?_
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs]
      intro hmem
      have : |p.1| ≤ ε := le_trans (le_max_left _ _) hmem
      linarith
    rw [hev, deriv_const]

/-- **Integrability against a function continuous on the ball**: the first slice-derivative of
`Jker ρ ε` times a function continuous on the ball of radius `ε` is integrable on all of `ℝ²`
(the derivative factor is supported in that ball). -/
lemma srb_integrable_abs_deriv_fst_mul (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {B : ℝ × ℝ → ℝ}
    (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1| * B p) := by
  have hJ : ContDiff ℝ 1 (Jker ρ ε) := Jker_smooth (n := 1) hρ ε
  have hcont : Continuous
      (fun p : ℝ × ℝ => deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1) :=
    Work.FTS.StrongEps.KernAux.continuous_deriv_slice_fst hJ
  have hon : IntegrableOn (fun p : ℝ × ℝ =>
      |deriv (fun s : ℝ => Jker ρ ε (s, p.2)) p.1| * B p) (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    ((hcont.abs.continuousOn).mul hB).integrableOn_compact (isCompact_closedBall 0 ε)
  exact hon.integrable_of_forall_notMem_eq_zero (fun p hp => by
    rw [srb_deriv_Jker_fst_eq_zero_of_notMem hρ.moll hε hp, abs_zero, zero_mul])

/-- **Integrability against a function continuous on the ball**: the second slice-derivative of
`Jker ρ ε` times a function continuous on the ball of radius `ε` is integrable on all of `ℝ²`. -/
lemma srb_integrable_abs_deriv_snd_mul (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {B : ℝ × ℝ → ℝ}
    (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2| * B p) := by
  have hJ : ContDiff ℝ 1 (Jker ρ ε) := Jker_smooth (n := 1) hρ ε
  have hcont : Continuous
      (fun p : ℝ × ℝ => deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2) :=
    srb_continuous_deriv_slice_snd hJ
  have hon : IntegrableOn (fun p : ℝ × ℝ =>
      |deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2| * B p) (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    ((hcont.abs.continuousOn).mul hB).integrableOn_compact (isCompact_closedBall 0 ε)
  exact hon.integrable_of_forall_notMem_eq_zero (fun p hp => by
    rw [srb_deriv_Jker_snd_eq_zero_of_notMem hρ.moll hε hp, abs_zero, zero_mul])

/-- The weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is nonnegative on the open quadrant. -/
lemma srb_Wt_nonneg (α : ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Work.Spaces.Wt α z θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩)
  simp only [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
  exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hsin _)

/-- The `η`-weight `w z / sin(2θ)^{η/2}` is nonnegative on the open quadrant. -/
lemma srb_wdiv_nonneg {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩)
  refine div_nonneg ?_ (Real.rpow_nonneg hsin _)
  simp only [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The weighted Cauchy–Schwarz core.**  If `M = ∫ p, K p · G p`, the weight `W₀` is
nonnegative and dominated by `e^{c|p|} · W` at every `p`, and the three relevant functions are
integrable, then

  `(M · W₀)² ≤ (∫ |K|) · ∫ |K| · e^{2c|p|} · (G · W)²`.

Proof: `M · W₀ = ∫ p, K p · (G p · W₀)`; `|∫ f| ≤ ∫ |f|`; the pointwise domination
`W₀² ≤ e^{2c|p|} W²` converts `|K|·(G W₀)²` into the majorant; and Cauchy–Schwarz for the
`L²`-pair `√|K|`, `√(|K| (G W₀)²)` gives the two `∫ |K|`-factors. -/
theorem srb_cs_core {K G W : ℝ × ℝ → ℝ} {W₀ c M : ℝ}
    (hW₀ : 0 ≤ W₀)
    (hW : ∀ p : ℝ × ℝ, W₀ ≤ Real.exp (c * (|p.1| + |p.2|)) * W p)
    (hKint : Integrable fun p : ℝ × ℝ => |K p|)
    (hQ : Integrable fun p : ℝ × ℝ =>
      |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2)
    (hK2 : Integrable fun p : ℝ × ℝ => |K p| * (G p * W₀) ^ 2)
    (hM : M = ∫ p : ℝ × ℝ, K p * G p) :
    (M * W₀) ^ 2 ≤ (∫ p : ℝ × ℝ, |K p|) *
      ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
  -- the pointwise comparison of the two weighted squares
  have hpt : ∀ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2
      ≤ |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
    intro p
    have hE : (0 : ℝ) < Real.exp (c * (|p.1| + |p.2|)) := Real.exp_pos _
    have hEW : 0 ≤ Real.exp (c * (|p.1| + |p.2|)) * W p := le_trans hW₀ (hW p)
    have hWnn : 0 ≤ W p := by
      have := hEW
      rw [mul_comm] at this
      exact nonneg_of_mul_nonneg_left this hE
    have hsq : W₀ ^ 2 ≤ Real.exp (2 * c * (|p.1| + |p.2|)) * (W p) ^ 2 := by
      have h1 : W₀ ^ 2 ≤ (Real.exp (c * (|p.1| + |p.2|)) * W p) ^ 2 :=
        pow_le_pow_left₀ hW₀ (hW p) 2
      have h2 : (Real.exp (c * (|p.1| + |p.2|)) * W p) ^ 2
          = Real.exp (2 * c * (|p.1| + |p.2|)) * (W p) ^ 2 := by
        rw [mul_pow, sq, ← Real.exp_add]
        congr 1
        ring
      rwa [h2] at h1
    calc |K p| * (G p * W₀) ^ 2
        = |K p| * ((G p) ^ 2 * W₀ ^ 2) := by ring_nf
      _ ≤ |K p| * ((G p) ^ 2 * (Real.exp (2 * c * (|p.1| + |p.2|)) * (W p) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))
            (abs_nonneg _)
      _ = |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by ring
  -- `M · W₀` is the integral against the weight `W₀`
  have hMW : M * W₀ = ∫ p : ℝ × ℝ, K p * (G p * W₀) := by
    rw [hM, ← integral_mul_const W₀ (fun p : ℝ × ℝ => K p * G p)]
    exact integral_congr_ae (Eventually.of_forall fun p => by ring)
  -- Cauchy–Schwarz
  have hcs : |∫ p : ℝ × ℝ, K p * (G p * W₀)|
      ≤ Real.sqrt (∫ p : ℝ × ℝ, |K p|)
        * Real.sqrt (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2) := by
    have hfm : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.sqrt |K p|) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hKint.aestronglyMeasurable
    have hgm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Real.sqrt (|K p| * (G p * W₀) ^ 2)) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hK2.aestronglyMeasurable
    have hf2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt |K p|) ^ 2) volume :=
      hKint.congr (Eventually.of_forall fun p => (Real.sq_sqrt (abs_nonneg _)).symm)
    have hg2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt (|K p| * (G p * W₀) ^ 2)) ^ 2) volume :=
      hK2.congr (Eventually.of_forall fun p =>
        (Real.sq_sqrt (mul_nonneg (abs_nonneg _) (sq_nonneg _))).symm)
    have h := Work.Blocks.IMC.cs_integral_mul_le volume hfm hgm hf2 hg2
    have hkey : ∀ p : ℝ × ℝ, Real.sqrt |K p| * Real.sqrt (|K p| * (G p * W₀) ^ 2)
        = |K p * (G p * W₀)| := by
      intro p
      have hs : Real.sqrt (|K p| * (G p * W₀) ^ 2) = Real.sqrt |K p| * |G p * W₀| := by
        rw [Real.sqrt_mul (abs_nonneg (K p)), Real.sqrt_sq_eq_abs]
      rw [hs, ← mul_assoc, Real.mul_self_sqrt (abs_nonneg (K p))]
      simp only [abs_mul]
    rw [show (fun p : ℝ × ℝ => Real.sqrt |K p| * Real.sqrt (|K p| * (G p * W₀) ^ 2))
        = fun p : ℝ × ℝ => |K p * (G p * W₀)| from funext hkey] at h
    have e1 : (∫ x : ℝ × ℝ, (Real.sqrt |K x|) ^ 2) = ∫ x : ℝ × ℝ, |K x| :=
      integral_congr_ae (Eventually.of_forall fun x => Real.sq_sqrt (abs_nonneg _))
    have e2 : (∫ x : ℝ × ℝ, (Real.sqrt (|K x| * (G x * W₀) ^ 2)) ^ 2)
        = ∫ x : ℝ × ℝ, |K x| * (G x * W₀) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun x =>
        Real.sq_sqrt (mul_nonneg (abs_nonneg _) (sq_nonneg _)))
    rw [e1, e2] at h
    have h' : |(∫ p : ℝ × ℝ, K p * (G p * W₀))|
        ≤ |(∫ p : ℝ × ℝ, |K p * (G p * W₀)|)| := by
      rw [abs_of_nonneg (integral_nonneg fun p => abs_nonneg _)]
      exact abs_integral_le_integral_abs
    exact le_trans h' h
  -- the monotonicity of the second factor
  have hA0 : 0 ≤ ∫ p : ℝ × ℝ, |K p| := integral_nonneg fun p => abs_nonneg _
  have hB0 : 0 ≤ ∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2 :=
    integral_nonneg fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hmono : (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2)
      ≤ ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hQ
      (Eventually.of_forall hpt)
  calc (M * W₀) ^ 2 = |M * W₀| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ p : ℝ × ℝ, |K p|)
          * Real.sqrt (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2)) ^ 2 := by
        rw [hMW]
        exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
    _ = (∫ p : ℝ × ℝ, |K p|) * (∫ p : ℝ × ℝ, |K p| * (G p * W₀) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ ≤ (∫ p : ℝ × ℝ, |K p|)
          * ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 :=
        mul_le_mul_of_nonneg_left hmono hA0

end Helpers

/-- **The `θ`-slot form of the core bound.**  When the routed identity carries a factor `2`
(`D_θ^i(J_ε f) = 2 ∫ K · G`), the bound of `srb_cs_core` acquires a factor `4`. -/
theorem srb_cs_core_four {K G W : ℝ × ℝ → ℝ} {W₀ c I : ℝ}
    (hW₀ : 0 ≤ W₀)
    (hW : ∀ p : ℝ × ℝ, W₀ ≤ Real.exp (c * (|p.1| + |p.2|)) * W p)
    (hKint : Integrable fun p : ℝ × ℝ => |K p|)
    (hQ : Integrable fun p : ℝ × ℝ =>
      |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2)
    (hK2 : Integrable fun p : ℝ × ℝ => |K p| * (G p * W₀) ^ 2)
    (hI : I = ∫ p : ℝ × ℝ, K p * G p) :
    ((2 * I) * W₀) ^ 2 ≤ 4 * (∫ p : ℝ × ℝ, |K p|) *
      ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
  have key := srb_cs_core hW₀ hW hKint hQ hK2 hI
  calc ((2 * I) * W₀) ^ 2 = 4 * (I * W₀) ^ 2 := by ring
    _ ≤ 4 * ((∫ p : ℝ × ℝ, |K p|) *
          ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 4 * (∫ p : ℝ × ℝ, |K p|) *
          ∫ p : ℝ × ℝ, |K p| * Real.exp (2 * c * (|p.1| + |p.2|)) * (G p * W p) ^ 2 := by
        ring

end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.AK_Mem6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

theorem AK_Mem6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.HkMem α 6 (Work.Construction.AK α) ∧
    Work.Spaces.HkNorm α 6 (Work.Construction.AK α) ≤ C := by
  obtain ⟨R, hR0, hrad⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  refine ⟨max 1 (Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700))), ?_, ?_⟩
  · exact lt_max_of_lt_left one_pos
  · intro α hα hα1
    refine ⟨Work.FTS.StrongPersist.AK6.HkMem_AK6 α hα hα1 hR0 hrad, ?_⟩
    have hpt := Work.FTS.StrongPersist.AK6.AK_integrand_le6 hR0 hrad α hα hα1
    have hsq := Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 (α := α)
      (A := 700 * R) (B := 49 * 10 ^ 12 * R) hα hα1 (by positivity) (by positivity)
      (fun z hz θ hθ => hpt z hz θ hθ)
    calc Work.Spaces.HkNorm α 6 (Work.Construction.AK α)
        = Real.sqrt (Work.Spaces.HkSq α 6 (Work.Construction.AK α)) := rfl
      _ ≤ Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) :=
          Real.sqrt_le_sqrt hsq
      _ ≤ max 1 (Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700))) :=
          le_max_right _ _

end Work.FTS.StrongPersist
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Two bookkeeping lemmas about the Hardy weight `w`

(`private` copies of the identically named lemmas of `Work.FTS.Nonlinear.Pieces.rowsAux`,
which are not exported.) -/

/-- The exact cancellation `(r/(1+r)²)²·w r = (1/(1+r))²`. -/
private lemma n0sw_sq_div_shape_eq {c r : ℝ} (hr : 0 < r) :
    c ^ 2 * (r / (1 + r) ^ 2) ^ 2 * Work.Spaces.w r = c ^ 2 * (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-- The bound `(r²/(1+r)⁴)²·w r ≤ (1/(1+r))²`. -/
private lemma n0sw_sq_div_shape_le {c r : ℝ} (hr : 0 < r) :
    c ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * Work.Spaces.w r ≤ c ^ 2 * (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  have h1r : 0 < 1 + r := by linarith
  have h4 : r ^ 2 ≤ (1 + r) ^ 4 := by
    nlinarith [sq_nonneg r, sq_nonneg (1 + r), hr.le, sq_nonneg ((1 + r) ^ 2 - r)]
  have hgoal : r ^ 2 / (1 + r) ^ 6 ≤ (1 / (1 + r)) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + r) ^ 6)]
    have hsimp : (1 / (1 + r)) ^ 2 * (1 + r) ^ 6 = (1 + r) ^ 4 := by field_simp
    rw [hsimp]
    exact h4
  calc c ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * ((1 + r) ^ 2 / r ^ 2)
      = c ^ 2 * (r ^ 2 / (1 + r) ^ 6) := by field_simp
    _ ≤ c ^ 2 * (1 / (1 + r)) ^ 2 := mul_le_mul_of_nonneg_left hgoal (sq_nonneg _)

/-! ## The pointwise bound -/

theorem N0_sq_w_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen g)
    (hL12g : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) := by
  -- two global facts about the data
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hFstar : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  -- the explicit shape of `F_*` and its first derivatives
  have hDthF : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ 40 * α ^ 2 * (z / (1 + z) ^ 2) :=
    (Work.FTS.Nonlinear.Pieces.Fstar_shape hα hα1).2.1
  have hDzF : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 40 * α * (z / (1 + z) ^ 2) :=
    (Work.FTS.Nonlinear.Pieces.Fstar_shape hα hα1).2.2
  have hc2m : ∀ θ : ℝ, |Work.Construction.c2m θ| ≤ 2 := fun θ => by
    have hs1 : Real.sin θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
    rw [Work.Construction.c2m, abs_le]
    constructor
    · nlinarith [Real.neg_one_le_cos (2 * θ), hs1]
    · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]
  -- the collapse of the two `F_*`-only terms of `N₀`
  have hN0bd : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        ≤ 160 * α ^ 2 * (z ^ 2 / (1 + z) ^ 4) := by
    intro z hz θ hθ
    have hz0 : 0 ≤ z := le_of_lt hz
    have h1z : 0 < 1 + z := by linarith
    have hden : 0 < Work.Spaces.c α * (1 + z) ^ 4 := mul_pos hc0 (pow_pos h1z 4)
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα ⟨hθ.1.le, hθ.2.le⟩
    have hnum : |8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ|
        ≤ 16 * α ^ 2 * z ^ 2 := by
      have hΓ : |Work.Spaces.Gam α θ| ≤ 1 := by rw [abs_of_nonneg hG0]; exact hG1
      calc |8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ|
          = 8 * α ^ 2 * |Work.Construction.c2m θ| * z ^ 2 * |Work.Spaces.Gam α θ| := by
            rw [show 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
                = (8 * α ^ 2) * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
                  from by ring]
            simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * α ^ 2),
              abs_of_nonneg (sq_nonneg z)]
            try ring
        _ ≤ 8 * α ^ 2 * 2 * z ^ 2 * 1 := by
            calc 8 * α ^ 2 * |Work.Construction.c2m θ| * z ^ 2 * |Work.Spaces.Gam α θ|
                ≤ 8 * α ^ 2 * 2 * z ^ 2 * |Work.Spaces.Gam α θ| :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hc2m θ) (by positivity)) (sq_nonneg z))
                    (abs_nonneg _)
              _ ≤ 8 * α ^ 2 * 2 * z ^ 2 * 1 := mul_le_mul_of_nonneg_left hΓ (by positivity)
        _ = 16 * α ^ 2 * z ^ 2 := by ring
    have hfin : 160 * α ^ 2 * (z ^ 2 / (1 + z) ^ 4) * (Work.Spaces.c α * (1 + z) ^ 4)
        = 160 * α ^ 2 * z ^ 2 * Work.Spaces.c α := by
      field_simp
      try ring
    rw [Work.Construction.N0_first_two_eq' (α := α) (z := z) (θ := θ) hα hα1 hz0
        ⟨hθ.1.le, hθ.2.le⟩,
      abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rw [hfin]
    have hnn : (0 : ℝ) ≤ α ^ 2 * z ^ 2 := by positivity
    nlinarith [hnum, hc1, hnn, sq_nonneg α, sq_nonneg z, hα.le]
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have h1r : 0 < 1 + r := by linarith
  have hw1 : 1 ≤ Work.Spaces.w r := by
    have hr' : (0 : ℝ) < r := hr
    rw [Work.Spaces.w, one_le_div (sq_pos_of_pos hr')]
    nlinarith
  -- the two additivity identities on the open quadrant
  have hpth : Work.Spaces.pth (Work.Construction.Ftot α g) r θ
      = Work.Spaces.pth (Work.Construction.Fstar α) r θ + Work.Spaces.pth g r θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hFstar hso hr hθ
  have hI2 : Work.Spaces.Dz (Work.Construction.Ftot α g) r θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) r θ + Work.Spaces.Dz g r θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hFstar hso hr hθ)
  have hL12F : Work.Construction.L12 (Work.Construction.Fstar α) r = 2 * α / (1 + r) :=
    Work.Construction.L12_Fstar_eq hα hα1 hr0
  -- the numerical size of `|g|_{ℋ⁴}`
  set X : ℝ := Work.FTS.Nonlin.Xn α g with hX
  have hL12gX : |Work.Construction.L12 g r| ≤ 3 * X := by
    rw [hX]
    exact hL12g r hr0
  -- ## the decomposition and the seven termwise bounds
  set W : ℝ := Work.Spaces.w r with hWdef
  have hW1 : 1 ≤ W := by rw [hWdef]; exact hw1
  have hW0 : 0 ≤ W := le_trans zero_le_one hW1
  set Hk : ℝ := Work.Spaces.HkIntegrand α 4 g r θ with hHkdef
  set T0 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ
      - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) r
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ with hT0def
  set T1 : ℝ := (1 / α) * Work.Construction.L12 g r * g r θ with hT1def
  set T2 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ with hT2def
  set T3 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g r
        * Work.Spaces.pth g r θ with hT3def
  set T4 : ℝ := -(Work.Construction.c2m θ) * Work.Construction.L12 g r
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ with hT4def
  set T5 : ℝ := -(Work.Construction.c2m θ) * Work.Construction.L12 g r
        * Work.Spaces.Dz g r θ with hT5def
  set T6 : ℝ := -(Work.Construction.c2m θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) r
        * Work.Spaces.Dz g r θ with hT6def
  have hexp : Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ
      = T0 + T1 + T2 + T3 + T4 + T5 + T6 := by
    rw [hT0def, hT1def, hT2def, hT3def, hT4def, hT5def, hT6def]
    simp only [Work.Construction.N0]
    rw [hpth, hI2]
    ring
  have h3L : (Work.Construction.L12 g r) ^ 2 ≤ (3 * X) ^ 2 := by
    nlinarith [hL12gX, abs_nonneg (Work.Construction.L12 g r),
      sq_abs (Work.Construction.L12 g r)]
  have hc2sq : (Work.Construction.c2m θ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    nlinarith [hc2m θ, abs_nonneg (Work.Construction.c2m θ),
      sq_abs (Work.Construction.c2m θ)]
  have hb0 : T0 ^ 2 * W ≤ (160 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
    have h := hN0bd r hr θ hθ
    rw [← hT0def] at h
    have h2 : T0 ^ 2 ≤ (160 * α ^ 2 * (r ^ 2 / (1 + r) ^ 4)) ^ 2 := by
      nlinarith [h, abs_nonneg T0, sq_abs T0]
    calc T0 ^ 2 * W ≤ (160 * α ^ 2 * (r ^ 2 / (1 + r) ^ 4)) ^ 2 * W :=
          mul_le_mul_of_nonneg_right h2 hW0
      _ = (160 * α ^ 2) ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * W := by ring
      _ ≤ (160 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
          rw [hWdef]
          exact n0sw_sq_div_shape_le hr
  have hb1 : T1 ^ 2 * W ≤ (9 * X ^ 2 / α ^ 2) * Hk := by
    rw [hT1def]
    have hg2 : (g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.g_sq_mul_w_sq_le_HkIntegrand α g hr hθ
      rw [← hWdef, ← hHkdef] at h
      have hWsq : W ≤ W ^ 2 := by nlinarith [hW1]
      have hstep : (g r θ) ^ 2 * W ≤ (g r θ) ^ 2 * W ^ 2 :=
        mul_le_mul_of_nonneg_left hWsq (sq_nonneg (g r θ))
      linarith [h, hstep]
    have hkey : ((1 / α) * Work.Construction.L12 g r * g r θ) ^ 2 * W
        = (1 / α) ^ 2 * (Work.Construction.L12 g r) ^ 2 * ((g r θ) ^ 2 * W) := by ring
    rw [hkey]
    calc (1 / α) ^ 2 * (Work.Construction.L12 g r) ^ 2 * ((g r θ) ^ 2 * W)
        ≤ (1 / α) ^ 2 * (3 * X) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hg2
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (1 / α)) (sq_nonneg (3 * X)))
      _ = (9 * X ^ 2 / α ^ 2) * Hk := by ring_nf
  have hb2 : T2 ^ 2 * W ≤ (180 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
    have hw : (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W
        ≤ (40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := hDthF r hr0 θ ⟨hθ.1.le, hθ.2.le⟩
      have h5 : (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
          ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 := by
        nlinarith [h, abs_nonneg (Work.Spaces.Dth (Work.Construction.Fstar α) r θ),
          sq_abs (Work.Spaces.Dth (Work.Construction.Fstar α) r θ)]
      calc (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W
          ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 * W :=
            mul_le_mul_of_nonneg_right h5 hW0
        _ = (40 * α ^ 2) ^ 2 * (r / (1 + r) ^ 2) ^ 2 * W := by ring
        _ ≤ (40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
            rw [hWdef]
            exact le_of_eq (n0sw_sq_div_shape_eq (c := 40 * α ^ 2) hr)
    have hkey : T2 ^ 2 * W = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W) := by
      rw [hT2def]
      simp only [Work.Spaces.Dth, Work.Construction.s2]
      ring
    rw [hkey]
    calc (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W)
        ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2 * ((40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (3 / (2 * α))) (sq_nonneg (3 * X)))
      _ = (180 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
          have hαne : α ≠ 0 := ne_of_gt hα
          field_simp
          ring
  have hb3 : T3 ^ 2 * W ≤ (81 * X ^ 2 / (4 * α ^ 2)) * Hk := by
    have hw : (Work.Spaces.Dth g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.dth_sq_mul_w_le_HkIntegrand α g hα hr hθ
      rw [← hWdef, ← hHkdef] at h
      exact h
    have hkey : T3 ^ 2 * W = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dth g r θ) ^ 2 * W) := by
      rw [hT3def]
      simp only [Work.Spaces.Dth, Work.Construction.s2]
      ring
    rw [hkey]
    calc (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dth g r θ) ^ 2 * W)
        ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (3 / (2 * α))) (sq_nonneg (3 * X)))
      _ = (81 * X ^ 2 / (4 * α ^ 2)) * Hk := by ring_nf
  have hb4 : T4 ^ 2 * W ≤ (240 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
    have hw : (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W
        ≤ (40 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := hDzF r hr0 θ ⟨hθ.1.le, hθ.2.le⟩
      have h5 : (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
          ≤ (40 * α * (r / (1 + r) ^ 2)) ^ 2 := by
        nlinarith [h, abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) r θ),
          sq_abs (Work.Spaces.Dz (Work.Construction.Fstar α) r θ)]
      calc (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W
          ≤ (40 * α * (r / (1 + r) ^ 2)) ^ 2 * W :=
            mul_le_mul_of_nonneg_right h5 hW0
        _ = (40 * α) ^ 2 * (r / (1 + r) ^ 2) ^ 2 * W := by ring
        _ ≤ (40 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
            rw [hWdef]
            exact le_of_eq (n0sw_sq_div_shape_eq (c := 40 * α) hr)
    have hkey : T4 ^ 2 * W = (Work.Construction.c2m θ) ^ 2
          * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W) := by
      rw [hT4def]
      ring
    rw [hkey]
    calc (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W)
        ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * ((40 * α) ^ 2 * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul (mul_le_mul hc2sq h3L (sq_nonneg _) (by norm_num)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (3 * X)))
      _ = (240 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by ring_nf
  have hb5 : T5 ^ 2 * W ≤ (36 * X ^ 2) * Hk := by
    have hw : (Work.Spaces.Dz g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.dz_sq_mul_w_le_HkIntegrand α g hr hθ
      rw [← hWdef, ← hHkdef] at h
      exact h
    have hkey : T5 ^ 2 * W = (Work.Construction.c2m θ) ^ 2
          * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dz g r θ) ^ 2 * W) := by
      rw [hT5def]
      ring
    rw [hkey]
    calc (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dz g r θ) ^ 2 * W)
        ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul hc2sq h3L (sq_nonneg _) (by norm_num)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (3 * X)))
      _ = (36 * X ^ 2) * Hk := by ring
  have hb6 : T6 ^ 2 * W ≤ (16 * α ^ 2) * Hk := by
    have hw : (Work.Spaces.Dz g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.dz_sq_mul_w_le_HkIntegrand α g hr hθ
      rw [← hWdef, ← hHkdef] at h
      exact h
    have h2a : (2 * α / (1 + r)) ^ 2 ≤ (2 * α) ^ 2 := by
      have h0 : 0 ≤ 1 / (1 + r) := div_nonneg zero_le_one h1r.le
      have hle : 1 / (1 + r) ≤ 1 := by rw [div_le_one h1r]; linarith
      have hsq : (1 / (1 + r)) ^ 2 ≤ 1 := by nlinarith [h0, hle]
      calc (2 * α / (1 + r)) ^ 2 = (2 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by ring_nf
        _ ≤ (2 * α) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (2 * α) ^ 2 := by ring
    have hkey : T6 ^ 2 * W = (Work.Construction.c2m θ) ^ 2 * (2 * α / (1 + r)) ^ 2
          * ((Work.Spaces.Dz g r θ) ^ 2 * W) := by
      rw [hT6def, hL12F]
      ring
    rw [hkey]
    calc (Work.Construction.c2m θ) ^ 2 * (2 * α / (1 + r)) ^ 2
            * ((Work.Spaces.Dz g r θ) ^ 2 * W)
        ≤ (2 : ℝ) ^ 2 * (2 * α) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul hc2sq h2a (sq_nonneg _) (by norm_num)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (2 * α)))
      _ = (16 * α ^ 2) * Hk := by ring
  -- ## the sum of seven squares
  have hcs7 : (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2
      ≤ 7 * (T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin 7 => ![T0, T1, T2, T3, T4, T5, T6] i)
    simpa [Fin.sum_univ_seven, Matrix.cons_val_zero, Matrix.cons_val_succ] using h
  -- ## the final assembly
  have hmain : (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * W
      ≤ 7 * (A₀ α X * Hk + B₀ α X * (1 / (1 + r)) ^ 2) := by
    calc (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * W
        = (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2 * W := by rw [hexp]
      _ ≤ 7 * ((T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) * W) := by
          calc (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2 * W
              ≤ (7 * (T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2)) * W :=
                mul_le_mul_of_nonneg_right hcs7 hW0
            _ = 7 * ((T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) * W) := by
                ring
      _ ≤ 7 * (A₀ α X * Hk + B₀ α X * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [A₀, B₀]
          nlinarith [hb0, hb1, hb2, hb3, hb4, hb5, hb6]
  exact hmain

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.NSBasic =====
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

/-! ## Elementary facts -/

/-- `sin 2θ ≠ 0` on the open angular interval. -/
theorem nzs_s2_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  have h : Work.Construction.s2 θ = Real.sin (2 * θ) := rfl
  rw [h]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

/-- `∂_θ f = D_θf / sin 2θ` on the open angular interval. -/
theorem nzs_pth_eq_Dth_div {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth f z θ = Work.Spaces.Dth f z θ / Work.Construction.s2 θ := by
  have hs : Work.Construction.s2 θ ≠ 0 := nzs_s2_ne_zero hθ
  have hD : Work.Spaces.Dth f z θ
      = Work.Construction.s2 θ * Work.Spaces.pth f z θ := rfl
  rw [hD, eq_div_iff hs]
  ring

/-- **The exact shape of `N` used below.**  On the open quadrant, with
`Ξ = PhiTil α F Ψ`, `A₁ = ℛ(Ξ)`, `A₂ = U(Ξ)/sin 2θ`, `A₃ = V(Ξ)`, the nonlinear term reads

`N α F Ψ = 2 A₁ F − 2 A₂ D_θF − 2α A₃ D_zF − (1/2) (F,K) D_θF − sin²θ (F,K) F`. -/
theorem nzs_N_form (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Construction.N α F Ψ z θ
        = 2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ) z θ * F z θ
          - 2 * (Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ
              / Work.Construction.s2 θ) * Work.Spaces.Dth F z θ
          - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z θ
              * Work.Spaces.Dz F z θ
          - (1 / 2) * Work.Construction.FK F z * Work.Spaces.Dth F z θ
          - (Real.sin θ) ^ 2 * Work.Construction.FK F z * F z θ := by
  intro z θ hzθ
  obtain ⟨_hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hs : Work.Construction.s2 θ ≠ 0 := nzs_s2_ne_zero hθ
  have h1 : Work.Construction.N α F Ψ z θ
      = 2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ) z θ * F z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ
            * Work.Spaces.pth F z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z θ
            * Work.Spaces.Dz F z θ
        - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
            * Work.Spaces.pth F z θ
        - (Real.sin θ) ^ 2 * Work.Construction.FK F z * F z θ := rfl
  rw [h1, nzs_pth_eq_Dth_div (f := F) hθ]
  field_simp

/-! ## The straightened stream function and its first partials -/

/-- `∂_z(Φ̃)` in terms of `∂_zΨ` and `(L₁₂ F)'`. -/
theorem nzs_pz_PhiTil (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (hg : DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z) :
    Work.Spaces.pz (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pz Ψ z θ
        - (1 / (4 * α)) * Work.Construction.s2 θ
            * deriv (fun z' => Work.Construction.L12 F z') z := by
  have hfun : Work.Construction.PhiTil α F Ψ
      = fun z' θ' => Ψ z' θ'
          - (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z' := rfl
  rw [hfun, Work.Spaces.pz]
  rw [show (fun z' => Ψ z' θ - (1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 F z')
      = (fun z' => Ψ z' θ)
        - (fun z' => (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z')
      from rfl,
    deriv_sub hΨ (hg.const_mul ((1 / (4 * α)) * Work.Construction.s2 θ))]
  rw [Work.Spaces.pz]
  have h2 : deriv (fun z' => (1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 F z') z
      = ((1 / (4 * α)) * Work.Construction.s2 θ)
        * deriv (fun z' => Work.Construction.L12 F z') z := by
    rw [show (fun z' => (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z')
        = fun z' => (((1 / (4 * α)) * Work.Construction.s2 θ))
            * Work.Construction.L12 F z' from rfl]
    exact deriv_const_mul (((1 / (4 * α)) * Work.Construction.s2 θ)) hg
  rw [h2]

/-- `∂_θ(Φ̃)` in terms of `∂_θΨ` and `L₁₂ F`. -/
theorem nzs_pth_PhiTil (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Spaces.pth (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pth Ψ z θ
        - (1 / (4 * α)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
  have hfun : Work.Construction.PhiTil α F Ψ
      = fun z' θ' => Ψ z' θ'
          - (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z' := rfl
  have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hderiv : deriv (fun θ' : ℝ => Work.Construction.s2 θ') θ
      = 2 * Real.cos (2 * θ) := by
    have h := Work.FTS.EllipticEst.UopHk.deriv_sin_two θ
    rw [show Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') from rfl]
    exact h
  have hd : DifferentiableAt ℝ (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ'
      * Work.Construction.L12 F z) θ :=
    (hs2.const_mul (1 / (4 * α))).mul_const (Work.Construction.L12 F z)
  rw [hfun, Work.Spaces.pth]
  rw [show (fun θ' => Ψ z θ'
        - (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z)
      = (fun θ' => Ψ z θ')
        - (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ' * Work.Construction.L12 F z)
      from rfl,
    deriv_sub hΨ hd]
  rw [Work.Spaces.pth]
  have h2 : deriv (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ'
        * Work.Construction.L12 F z) θ
      = (1 / (4 * α)) * (deriv (fun θ' : ℝ => Work.Construction.s2 θ') θ)
        * Work.Construction.L12 F z := by
    rw [show (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 F z)
        = fun θ' => (((1 / (4 * α)) * Work.Construction.s2 θ')
            * Work.Construction.L12 F z) from rfl]
    have h := deriv_mul_const (x := θ)
      (c := fun θ' : ℝ => (1 / (4 * α)) * Work.Construction.s2 θ')
      ((hs2.const_mul (1 / (4 * α)))) (Work.Construction.L12 F z)
    rw [h]
    have h3 : deriv (fun θ' : ℝ => (1 / (4 * α)) * Work.Construction.s2 θ') θ
        = (1 / (4 * α)) * deriv (fun θ' : ℝ => Work.Construction.s2 θ') θ :=
      deriv_const_mul (1 / (4 * α)) hs2
    rw [h3]
  rw [h2, hderiv]



end Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.MismatchSummand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The mismatch summand, pointwise.**  For a coefficient `A` whose angular derivative is
priced by `Kθ`, the level-six integrand of the obstructed index `(1,5,1,0)` is `≤ Kθ/2` times
`HkIntegrand α 6 f`. -/
theorem mismatch_pt {α Kθ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {A f : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hK : |Work.Spaces.pth A z θ| ≤ Kθ) :
    |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ
        * Work.Spaces.DzIter 6 f z θ * Work.Spaces.mixed 5 1 f z θ|
      ≤ Kθ / 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  set s := Real.sin (2 * θ) with hsdef
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs1 : s ≤ 1 := Real.sin_le_one _
  have hK0 : 0 ≤ Kθ := (abs_nonneg _).trans hK
  set Y := Work.Spaces.DzIter 6 f z θ
  set Z := Work.Spaces.mixed 5 1 f z θ
  set p := Work.Spaces.pth A z θ
  set W := Work.Spaces.w z with hWdef
  have hγ : Work.Spaces.gam α = 1 + α / 10 := rfl
  have hη : Work.Spaces.eta = 99 / 100 := rfl
  set a := Y * (W / s ^ (Work.Spaces.eta / 2)) with ha
  set b := Z * Work.Spaces.Wt α z θ with hb
  -- the two slots of `HkIntegrand α 6 f`
  have hI : a ^ 2 + b ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    unfold Work.Spaces.HkIntegrand
    have h1 : a ^ 2 ≤ ∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      Finset.single_le_sum (f := fun i => (Work.Spaces.DzIter i f z θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (fun i _ => sq_nonneg _) (by simp)
    have hnn : ∀ i j : ℕ, 0 ≤ (if 1 ≤ i ∧ i + j ≤ 6 then
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i j; split_ifs <;> positivity
    have h2 : b ^ 2 ≤ ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
        if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0 := by
      have hin : b ^ 2 ≤ ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ 1 ∧ 1 + j ≤ 6 then (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) := by
        have := Finset.single_le_sum (f := fun j => if 1 ≤ 1 ∧ 1 + j ≤ 6 then
          (Work.Spaces.mixed j 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          (fun j _ => hnn 1 j) (show (5 : ℕ) ∈ Finset.range (6 + 1) by simp)
        simpa using this
      exact hin.trans (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (6 + 1),
          if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
          (show (1 : ℕ) ∈ Finset.range (6 + 1) by simp))
    exact add_le_add h1 h2
  -- the weight comparison `s^{1-γ} ≤ s^{-η/2} s^{-γ/2}`
  have hexp : s ^ (-(Work.Spaces.gam α)) * s
      ≤ s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.gam α / 2)) := by
    rw [← Real.rpow_add_one hs.ne', ← Real.rpow_add hs]
    apply Real.rpow_le_rpow_of_exponent_ge hs hs1
    rw [hγ, hη]; linarith
  have hW0 : 0 ≤ W := by
    rw [show W = (1 + z) ^ 2 / z ^ 2 from rfl]; positivity
  have hab : W ^ 2 * (s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.gam α / 2)))
      * (|Y| * |Z|) = |a| * |b| := by
    rw [ha, hb, abs_mul, abs_mul, Work.Spaces.Wt, Work.Spaces.wTheta, abs_mul,
      abs_div, abs_of_nonneg hW0, abs_of_pos (Real.rpow_pos_of_pos hs _),
      abs_of_pos (Real.rpow_pos_of_pos hs _), Real.rpow_neg hs.le]
    field_simp
  have hL : |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.Dth A z θ * Y * Z|
      = W ^ 2 * (s ^ (-(Work.Spaces.gam α)) * s) * |p| * (|Y| * |Z|) := by
    have hD : Work.Spaces.Dth A z θ = s * p := rfl
    rw [hD, Work.FTS.TransportS.leafGam]
    simp only [abs_mul]
    rw [← hsdef, ← hWdef, abs_of_nonneg (sq_nonneg W), abs_of_pos (Real.rpow_pos_of_pos hs _),
      abs_of_pos hs]
    ring
  rw [hL]
  have hAM : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hYZ : 0 ≤ |Y| * |Z| := by positivity
  calc W ^ 2 * (s ^ (-(Work.Spaces.gam α)) * s) * |p| * (|Y| * |Z|)
      ≤ W ^ 2 * (s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.gam α / 2))) * Kθ
          * (|Y| * |Z|) := by
        apply mul_le_mul_of_nonneg_right _ hYZ
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)) hK (abs_nonneg _)
          (by positivity)
    _ = Kθ * (|a| * |b|) := by rw [← hab]; ring
    _ ≤ Kθ * ((a ^ 2 + b ^ 2) / 2) := mul_le_mul_of_nonneg_left hAM hK0
    _ ≤ Kθ / 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
        have := mul_le_mul_of_nonneg_left hI hK0
        linarith


/-- Order-0 pointwise reading of the flat norm. -/
theorem abs_pth_le_coefTh {l : ℕ} {V : Fn} (hmem : Work.FTS.VocabO.CoefThMem l V) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pth V z θ| ≤ Work.FTS.VocabO.CoefTh l V := by
  intro z θ hz hθ hθ'
  obtain ⟨K, hKb⟩ := hmem 0 0 (by omega)
  have h1 := Work.FTS.H2.le_supAbsO (g := Work.Spaces.mixed 0 0 (Work.Spaces.pth V))
    hz hθ hθ' hKb
  have hnn : ∀ b i : ℕ, 0 ≤ (if b + i ≤ l then
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth V)) else 0) := by
    intro b i
    split_ifs
    · exact Real.sSup_nonneg (by rintro y ⟨_, _, _, _, _, rfl⟩; exact abs_nonneg _)
    · exact le_rfl
  have h2 : Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 0 (Work.Spaces.pth V))
      ≤ Work.FTS.VocabO.CoefTh l V := by
    unfold Work.FTS.VocabO.CoefTh
    have hin : Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 0 (Work.Spaces.pth V))
        ≤ ∑ i ∈ Finset.range (l + 1), (if 0 + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 i (Work.Spaces.pth V)) else 0) := by
      have := Finset.single_le_sum (f := fun i => if 0 + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed 0 i (Work.Spaces.pth V)) else 0)
        (fun i _ => hnn 0 i) (show 0 ∈ Finset.range (l + 1) by simp)
      simpa using this
    exact hin.trans (Finset.single_le_sum (f := fun b => ∑ i ∈ Finset.range (l + 1),
        if b + i ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth V))
        else 0) (fun b _ => Finset.sum_nonneg fun i _ => hnn b i)
        (show 0 ∈ Finset.range (l + 1) by simp))
  exact h1.trans h2

end Work.FTS.StrongPersist.H6Rows

namespace Work.FTS.StrongPersist.L6Ctx

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


end Work.FTS.StrongPersist.L6Ctx
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `𝒲^{6,∞}`-membership and `α`-linear `𝒲^{6,∞}`-bound for `-(2α/(1+z))·c2m(θ)`

The transport coefficient of the `N₀`/`𝓛_Γ^T` rows is the angular coefficient
`c2m(θ) = cos 2θ − sin²θ` times the radial profile `2α/(1+z)`.  The sibling module
`Work.FTS.StrongPersist.c2m_L12Fstar_W6` treats `c2m·L₁₂(F_*) = c2m·2α/(1+z)`; the present
lemma is the *explicit* version of the same function with the two factors written in the
opposite order and with the overall sign `-`, which is the form in which the coefficient is
requested (`N0pair6Aux.N0coefA6_WlInf6`).

The two pointwise inputs are `c2mSix_inv_points` and `c2mSix_inv_mixed` of the sibling module,
applied to `Hn0 α = c2m(θ)·2α/(1+z)`; the sign `-` is transported through the iterated
derivatives with the elementary commutation lemmas `pzIter_neg_fun` / `DthIter_neg_fun`, and
`|−x| = |x|` makes the two functions have the same bounds.  The smoothness is
`SmoothOpen.sep_mul`-style: `C^∞` on `(0,∞)` in `z` times `C^∞` in `θ`.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open Work.Spaces
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The coefficient of the statement, with the factors in the statement's order. -/
def Fn0 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ

/-- The same function with the `c2m` factor first; this is the shape treated by
`Work.FTS.StrongPersist.c2mSix_inv_points` / `c2mSix_inv_mixed`. -/
def Hn0 (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))

/-! ## Negation commutes with the iterated operators -/

/-- Negation commutes with the iterated plain `z`-derivative. -/
theorem pzIter_neg_fun (k : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter k (fun z θ => -(X z θ)) = fun z θ => -Work.Spaces.pzIter k X z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz]
      rw [show (fun z' : ℝ => -(Work.Spaces.pzIter k X) z' θ)
            = -((fun z' : ℝ => Work.Spaces.pzIter k X z' θ)) from rfl,
        deriv.neg]

/-- Negation commutes with the iterated `D_θ`-derivative. -/
theorem DthIter_neg_fun (j : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (fun z θ => -(X z θ)) = fun z θ => -Work.Spaces.DthIter j X z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [show (fun θ' : ℝ => -(Work.Spaces.DthIter j X) z θ')
            = -(fun θ' : ℝ => Work.Spaces.DthIter j X z θ') from rfl, deriv.neg]
      ring

/-! ## Smoothness on the open quadrant -/

/-- `-(2α/(1+z))·c2m(θ)` is `C^∞` on the open quadrant.  This is the `sep_mul` shape: a
product of a function of `z` which is `C^∞` on `(0,∞)` and a function of `θ` which is `C^∞`
everywhere. -/
theorem Fn0_smoothOpen (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => -(2 * α / (1 + p.1)) * Work.Construction.c2m p.2)
    Work.FTS.EllipticEst.Q0
  rw [show (fun p : ℝ × ℝ => -(2 * α / (1 + p.1)) * Work.Construction.c2m p.2)
      = (fun p : ℝ × ℝ => -(2 * α / (1 + p.1)))
        * (fun p : ℝ × ℝ => Work.Construction.c2m p.2) from rfl]
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ => -(2 * α / (1 + z)))
      (Set.Ioi 0) := by
    apply contDiffOn_infty.mpr
    intro m
    have hone : ContDiffOn ℝ m (fun z : ℝ => 1 + z) (Set.Ioi 0) := by fun_prop
    have hd : ContDiffOn ℝ m (fun z : ℝ => (2 * α) / (1 + z)) (Set.Ioi 0) := by
      apply ContDiffOn.div
      · exact contDiffOn_const
      · exact hone
      · intro z hz
        simp only [Set.mem_Ioi] at hz
        linarith
    exact hd.neg
  have hχ : ContDiff ℝ ⊤ Work.Construction.c2m := by
    rw [show Work.Construction.c2m = fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2 from rfl]
    fun_prop
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => -(2 * α / (1 + p.1))) Work.FTS.EllipticEst.Q0 :=
    hg.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0 := by
    change ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Construction.c2m ∘ Prod.snd)
      Work.FTS.EllipticEst.Q0
    exact (hχ.of_le le_top).comp_contDiffOn (s := Work.FTS.EllipticEst.Q0)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) contDiffOn_snd
  exact h1.mul h2

/-! ## The two pointwise bounds -/

/-- The weighted radial bound: `|(z+1)^k ∂_z^k (Fn0 α)| ≤ 4α k!` on the domain. -/
theorem Fn0_z_bound (α z θ : ℝ) (hα : 0 < α) (hz : z ∈ Iz) (k : ℕ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Fn0 α) z θ| ≤ 4 * α * (k.factorial : ℝ) := by
  have hf : Fn0 α = fun z θ => -(Hn0 α z θ) := by
    funext z θ; simp only [Fn0, Hn0]; ring
  rw [hf, pzIter_neg_fun]
  rw [show (z + 1) ^ k * -Work.Spaces.pzIter k (Hn0 α) z θ
      = -((z + 1) ^ k * Work.Spaces.pzIter k (Hn0 α) z θ) by ring, abs_neg]
  exact Work.FTS.StrongPersist.c2mSix_inv_points α z θ hα hz k

/-- The weighted mixed bound: the angular summand of `WlInf` for `Fn0 α` is `≤ C α`,
uniformly in `0 < α ≤ 1`, `z ∈ Iz`, `θ ∈ Iθ` and the orders `1 ≤ j ≤ 6`, `k ≤ 6`. -/
theorem Fn0_mixed_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → z ∈ Iz → θ ∈ Iθ →
    ∀ j k : ℕ, 1 ≤ j → j ≤ 6 → k ≤ 6 →
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Fn0 α)) z θ
      * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * α := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.StrongPersist.c2mSix_inv_mixed
  refine ⟨K, hKpos, ?_⟩
  intro α z θ hα hα1 hz hθ j k hj1 hj6 hk
  have hz0 : (0 : ℝ) ≤ z := hz
  have hf : Fn0 α = fun z θ => -(Hn0 α z θ) := by
    funext z θ; simp only [Fn0, Hn0]; ring
  rw [hf, DthIter_neg_fun, pzIter_neg_fun]
  rw [show (z + 1) ^ k * -Work.Spaces.pzIter k (Work.Spaces.DthIter j (Hn0 α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      = -((z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Hn0 α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) by ring, abs_neg]
  exact hK α z θ hα hα1 hz0 hθ j k hj1 hj6 hk

/-! ## The `𝒲^{6,∞}`-membership and the norm estimate -/

/-- Every one of the finitely many suprema of `WlInf α 6 (Fn0 α)` is bounded. -/
theorem Fn0_WlInfMem (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 6 (Fn0 α) := by
  obtain ⟨K, hKpos, hK⟩ := Fn0_mixed_bound
  constructor
  · intro k hk
    exact ⟨4 * α * (k.factorial : ℝ), fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact Fn0_z_bound α z θ hα hz k⟩
  · intro j hj k hk hj1 hjk
    exact ⟨K * α, fun y hy => by
      rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact hK α z θ hα hα1 hz hθ j k hj1 hj hk⟩

/-- The `𝒲^{6,∞}`-norm of `Fn0 α` is bounded by a universal constant times `α`. -/
theorem Fn0_WlInf_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInf α 6 (Fn0 α) ≤ C * α := by
  obtain ⟨K, hKpos, hK⟩ := Fn0_mixed_bound
  refine ⟨Work.FTS.StrongPersist.c2mSixCW K,
    Work.FTS.StrongPersist.c2mSixCW_pos K hKpos, ?_⟩
  intro α hα hα1
  have hzsum : (∑ k ∈ Finset.range 7, Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Fn0 α) z θ))
      ≤ ∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact Work.Spaces.supAbs_le fun z hz θ _ => Fn0_z_bound α z θ hα hz k
  have hmsum : (∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
        (if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Fn0 α)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
      ≤ ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7, K * α := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    by_cases hc : 1 ≤ j ∧ k + j ≤ 6
    · rw [ite_eq_left hc]
      exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        hK α z θ hα hα1 hz hθ j k hc.1 (by omega) (by omega)
    · rw [ite_eq_right hc]
      exact mul_nonneg hKpos.le hα.le
  calc Work.Spaces.WlInf α 6 (Fn0 α)
      = (∑ k ∈ Finset.range 7, Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k (Fn0 α) z θ))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
            (if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
              (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Fn0 α)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := rfl
    _ ≤ (∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7, K * α := add_le_add hzsum hmsum
    _ = (∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ)) * α + 49 * (K * α) := by
      rw [Work.FTS.StrongPersist.c2mSix_sum_fact_mul,
        Work.FTS.StrongPersist.c2mSix_sum_const_mul]
    _ ≤ Work.FTS.StrongPersist.c2mSixCW K * α := by
      rw [Work.FTS.StrongPersist.c2mSixCW]
      nlinarith [hα.le, hKpos.le]

/-! ## The requested statement -/

theorem N0coefA6_WlInf6 : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) ∧
    Work.Spaces.WlInfMem α 6 (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) ∧
    Work.Spaces.WlInf α 6 (fun z θ => -(2 * α / (1 + z)) * Work.Construction.c2m θ) ≤ C * α := by
  obtain ⟨C, hC, hCb⟩ := Fn0_WlInf_le
  refine ⟨C, hC, fun α hα hα1 => ⟨Fn0_smoothOpen α, ?_, hCb α hα hα1⟩⟩
  exact Fn0_WlInfMem α hα hα1

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.NA6sig =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

-- The σ-decay hypothesis of `RowAdz`, verified for the actual coefficient
-- `A = c₂ₘ(θ)·L₁₂(F_*)(z)` of the `N₀`-row (this is `H6Pair6Aux.NA6 α` up to unfolding).
--
-- ROUTE.  `L₁₂(F_*) = 2α/(1+z)` on `(-1,∞)` (`Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH`),
-- so `A = c₂ₘ(θ)·(2α/(1+z))` up to that equality, and the function is separable:
-- `D_θ^i A = c₂ₘ^{(i)}(θ)·(2α/(1+z))` and `mixed j i A = D_z^j(D_θ^i A)
--  = c₂ₘ^{(i)}(θ)·(D_z^j(2α/(1+z)))`.
--   * Angular (`1 ≤ i ≤ 6`): `|D_θ^i c₂ₘ| ≤ 100000·sin(2θ)²` by
--     `Work.FTS.StrongPersist.dthU_c2m_bound6` (with `DthIter i c₂ₘ = dthU^[i] c₂ₘ`).
--   * Radial: `|(z+1)^k·pzIter k (c₂ₘ(θ)·2α/(1+z))| ≤ 4α k!` for `z ≥ 0`
--     (`Work.FTS.StrongPersist.c2mSix_inv_points`), so `|pzIter k (2α/(1+z))| ≤ 4α k!`;
--     `DzIter j` is a finite combination of `z^k ∂_z^k` (`DzIter_eq_sum_scoef_of_contDiffOn`,
--     or an induction from `Spaces.Dz`), and `z^k/(1+z)^k ≤ 1`.
--   * `i = 0`: `|mixed j 0 A| = |c₂ₘ θ|·|DzIter j L₁₂| ≤ 2·Cα` (using `FstarPkg.abs_c2m_le_two`).
--   * `i ≥ 1`: `|mixed j i A| ≤ 100000·sin(2θ)²·Cα ≤ Cα·sin(2θ)` since `sin(2θ) ≤ 1`.
--
-- IMPLEMENTATION.  The separability is formalised as the pointwise identity
-- `mixed_eq` below: for `z > 0`, `θ ∈ Iθ`,
-- `mixed j i A z θ = (dthU^[i] c2m θ) · ∑_{k≤j} S(j,k) z^k (L₁₂(F_*))^{(k)}(z)`,
-- obtained from `DthIter_decomp` (angular separation), the Stirling expansion of
-- `D_z^j` (`Spaces.DzIter_eq_sum_scoef`, which needs the `z`-slices to be `C^∞` on
-- `(-1,∞)` — supplied by transporting `eqOn_L12_invH` through `ContDiffOn.congr`)
-- and the radial separation `Spaces.pzIter_decomp`.  The radial sum is bounded by
-- `1440000·α` in `radial_sum_bound`, using `deriv_iter_eqOn` + `c2mInv_radial`
-- (`|(z+1)^k (2α/(1+z))^{(k)}| ≤ 2α k!`), `z^k ≤ (z+1)^k`, `k! ≤ 720` and the
-- Bell-number bound `bell j ≤ 1000` for `j ≤ 6`.
private lemma bell_le_thousand (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 1000 := by
  interval_cases n <;> decide

/-- `z ↦ 2α/(1+z)` is `C^∞` on `(-1,∞)`. -/
private lemma contDiffOn_invH (α : ℝ) :
    ContDiffOn ℝ ⊤ (Work.FTS.Nonlinear.FstarPkg.invH α) (Set.Ioi (-1)) := by
  have h : Work.FTS.Nonlinear.FstarPkg.invH α = fun z : ℝ => (2 * α) * (1 + z)⁻¹ := by
    funext z; rw [Work.FTS.Nonlinear.FstarPkg.invH_apply, div_eq_mul_inv]
  rw [h]
  refine ContDiffOn.mul (contDiffOn_const (c := 2 * α) (s := Set.Ioi (-1)) (n := ⊤)) ?_
  refine ContDiffOn.inv ?_ ?_
  · simpa using (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi (-1)) (n := ⊤)).add
      (contDiffOn_id (s := Set.Ioi (-1)) (n := ⊤))
  · intro x hx
    have hx' : (-1 : ℝ) < x := hx
    exact ne_of_gt (by linarith)

/-- `z ↦ L₁₂(F_*)(z)` is `C^∞` on `(-1,∞)` (it agrees there with `2α/(1+z)`). -/
private lemma contDiffOn_L12Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ ⊤
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi (-1)) :=
  (contDiffOn_invH α).congr
    (fun z hz => Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1 hz)

/-- For a radial function, `pzIter` is the plain iterate of `deriv`. -/
private lemma pzIter_radial (B : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => B z) z θ = deriv^[k] B z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ]
    simp only [Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.pzIter k (fun z _ => B z) z' θ)
          = fun z' => deriv^[k] B z' from by
      funext z'; exact ih z']
    exact congrFun (Function.iterate_succ_apply' deriv k B).symm z

/-- The Stirling-weighted `z`-jet of `L₁₂(F_*)` is `O(α)` at order `≤ 6`. -/
private lemma radial_sum_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ j ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ),
      |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
          * (z ^ k * deriv^[k]
              (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
        ≤ 1440000 * α := by
  intro j hj z hz
  have hz0 : (0 : ℝ) < z := hz
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hterm : ∀ k ≤ j,
      |z ^ k * deriv^[k] (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
        ≤ 2 * α * 720 := by
    intro k hk
    have hk6 : k ≤ 6 := le_trans hk hj
    have hkB : deriv^[k] (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
        = deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z :=
      Work.FTS.Nonlinear.FstarPkg.deriv_iter_eqOn
        (Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1) k hz1
    rw [hkB]
    have h := Work.FTS.Nonlinear.FstarPkg.c2mInv_radial α hα k z (le_of_lt hz)
    have hfact : (k.factorial : ℝ) ≤ 720 := by
      interval_cases k <;> norm_num
    calc |z ^ k * deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z|
        = z ^ k * |deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hz) k)]
      _ ≤ (z + 1) ^ k * |deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) k
      _ = |(z + 1) ^ k * deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
      _ ≤ 2 * α * (k.factorial : ℝ) := h
      _ ≤ 2 * α * 720 := by nlinarith [hα]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le j (2 * α * 720)
    (fun k => z ^ k * deriv^[k]
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z) hterm
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 1000 := by exact_mod_cast bell_le_thousand j hj
  calc |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
        * (z ^ k * deriv^[k] (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
      ≤ (Work.Spaces.bell j : ℝ) * (2 * α * 720) := hsum
    _ ≤ 1000 * (2 * α * 720) := mul_le_mul_of_nonneg_right hbell (by positivity)
    _ = 1440000 * α := by ring

/-- **Separation of variables for the `N₀`-coefficient.**  For `z > 0`, `θ ∈ Iθ`,
`mixed j i A z θ = (dthU^[i] c2m θ) · ∑_{k≤j} S(j,k) z^k (∂_z^k L₁₂(F_*))(z)`. -/
private lemma mixed_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (j i : ℕ) (z θ : ℝ) (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed j i (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
      = (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
        * ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
            * (z ^ k * deriv^[k]
                (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z) := by
  have hB := contDiffOn_L12Fstar α hα hα1
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    simp only [Set.mem_Ioi] at hz ⊢; linarith
  have hsmooth : ∀ θ' ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z' => (Work.Spaces.dthU^[i] Work.Construction.c2m) θ'
        * Work.Construction.L12 (Work.Construction.Fstar α) z') (Set.Ioi (-1)) :=
    fun θ' _ => (contDiffOn_const (c := (Work.Spaces.dthU^[i] Work.Construction.c2m) θ')
      (s := Set.Ioi (-1)) (n := ⊤)).mul hB
  have hDth : Work.Spaces.DthIter i (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z)
      = fun z θ => (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp i Work.Construction.c2m
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
  rw [Work.Spaces.mixed, hDth,
    Work.Spaces.DzIter_eq_sum_scoef hsmooth j z hz1 θ hθ]
  have hpt : ∀ k ∈ Finset.range (j + 1),
      (Work.Spaces.scoef j k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k (fun z θ =>
              (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
                * Work.Construction.L12 (Work.Construction.Fstar α) z) z θ)
      = (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
        * ((Work.Spaces.scoef j k : ℝ)
            * (z ^ k * deriv^[k]
                (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)) := by
    intro k hk
    rw [Work.Spaces.pzIter_decomp k (Work.Spaces.dthU^[i] Work.Construction.c2m)
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z θ]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.mul_sum]

theorem NA6sig : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (z θ : ℝ), 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i
          (fun z θ => Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z) z θ|
        ≤ C * α * (if i = 0 then 1 else Real.sin (2 * θ)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  refine ⟨max (2 * 1440000) (C0 * 1440000) + 1, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ max (2 * 1440000) (C0 * 1440000) :=
      le_max_of_le_left (by norm_num)
    linarith
  · intro α hαmem z θ hz hθ0 hθ1 j i hij
    obtain ⟨hαpos, hαle⟩ := hαmem
    have hzI : z ∈ Set.Ioi (0 : ℝ) := hz
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) := by
      apply Real.sin_nonneg_of_mem_Icc
      rw [Set.mem_Icc]
      constructor <;> linarith [hθ0, hθ1, Real.pi_pos]
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hji : j ≤ 6 := by omega
    have hii : i ≤ 6 := by omega
    rw [mixed_eq α hαpos hαle j i z θ hzI hθI, abs_mul]
    have hsum := radial_sum_bound α hαpos hαle j hji z hzI
    by_cases hi0 : i = 0
    · rw [if_pos hi0, mul_one]
      have hC : |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ| ≤ 2 := by
        rw [hi0]
        simpa using Work.FTS.Nonlinear.FstarPkg.abs_c2m_le_two θ
      calc |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ|
            * |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
                * (z ^ k * deriv^[k]
                    (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
          ≤ 2 * (1440000 * α) := mul_le_mul hC hsum (abs_nonneg _) (by norm_num)
        _ = 2880000 * α := by ring
        _ ≤ (max (2 * 1440000) (C0 * 1440000) + 1) * α := by
            have h2 : (2880000 : ℝ) ≤ max (2 * 1440000) (C0 * 1440000) + 1 := by
              have := le_max_left (2 * 1440000) (C0 * 1440000); linarith
            nlinarith [hαpos]
    · rw [if_neg hi0]
      have hi1 : 1 ≤ i := by omega
      have hC : |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ|
          ≤ C0 * (Real.sin (2 * θ)) ^ 2 := hC0 i hi1 hii θ
      have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ Real.sin (2 * θ) := by
        nlinarith [hsin0, hsin1]
      have hcoe : C0 * 1440000 ≤ max (2 * 1440000) (C0 * 1440000) + 1 := by
        have := le_max_right (2 * 1440000) (C0 * 1440000); linarith
      have hnn : (0 : ℝ) ≤ C0 * 1440000 * α :=
        mul_nonneg (mul_nonneg hC0pos.le (by norm_num)) hαpos.le
      calc |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ|
            * |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
                * (z ^ k * deriv^[k]
                    (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
          ≤ (C0 * (Real.sin (2 * θ)) ^ 2) * (1440000 * α) :=
            mul_le_mul hC hsum (abs_nonneg _) (by positivity)
        _ = C0 * 1440000 * α * (Real.sin (2 * θ)) ^ 2 := by ring
        _ ≤ C0 * 1440000 * α * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left hs2 hnn
        _ ≤ (max (2 * 1440000) (C0 * 1440000) + 1) * α * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoe hαpos.le) hsin0

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

theorem leibniz_rad_Dz_cd6 {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hr : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => r z)) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {j : ℕ} (hj : j ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ) := by
  intro z θ hz hθ0 hθ1
  have h := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.DzIter_mul_cd6
    (f := fun z (_ : ℝ) => r z) (g := g) hr hg hj hz hθ0 hθ1
  rw [h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Work.Elliptic.DzIter_rad]

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The Bell numbers of the rows `n ≤ 6`. -/
theorem bell_le_six_local {n : ℕ} (hn : n ≤ 6) : Work.Spaces.bell n ≤ 250 := by
  interval_cases n <;> decide

/-- The `k`-th derivative of `X y = (1-y)/(1+y)`, `k ≥ 1`, is that of `2(1+y)⁻¹`. -/
theorem deriv_iter_oneSubOneAdd : ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, -1 < z →
    deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) z
      = 2 * Work.FTS.Nonlinear.FstarPkg.nInvClosed m z := by
  intro m
  induction m with
  | zero => intro hm z hz; omega
  | succ m ih =>
    intro hm z hz
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      rw [Function.iterate_one]
      have hbase : HasDerivAt (fun y : ℝ => 2 * (1 + y)⁻¹ - 1)
          (2 * Work.FTS.Nonlinear.FstarPkg.nInvClosed 1 z) z := by
        have h0' : HasDerivAt (fun y : ℝ => (1 + y)⁻¹)
            (Work.FTS.Nonlinear.FstarPkg.nInvClosed 1 z) z := by
          have h := Work.FTS.Nonlinear.FstarPkg.hasDerivAt_nInvClosed 0 (z := z) (by linarith)
          have hfun : Work.FTS.Nonlinear.FstarPkg.nInvClosed 0 = fun y : ℝ => (1 + y)⁻¹ := by
            funext y
            simp [Work.FTS.Nonlinear.FstarPkg.nInvClosed]
          rwa [hfun] at h
        simpa using (h0'.const_mul 2).sub_const 1
      have hX : (fun y : ℝ => (1 - y) / (1 + y)) =ᶠ[𝓝 z]
          (fun y : ℝ => 2 * (1 + y)⁻¹ - 1) := by
        filter_upwards [isOpen_ne.mem_nhds (show z ≠ (-1 : ℝ) by linarith)] with y hy
        have hy' : (1 + y) ≠ 0 := by
          intro h; exact hy (by linarith)
        field_simp
        ring
      rw [Filter.EventuallyEq.deriv_eq hX, hbase.deriv]
    · rw [Function.iterate_succ_apply']
      have hev : deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) =ᶠ[𝓝 z]
          (fun y : ℝ => 2 * Work.FTS.Nonlinear.FstarPkg.nInvClosed m y) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact ih hpos y hy
      rw [hev.deriv_eq]
      exact ((Work.FTS.Nonlinear.FstarPkg.hasDerivAt_nInvClosed m (z := z)
        (by linarith)).const_mul 2).deriv

/-- `|z^m ∂_z^m X z| ≤ 1440` for `z ≥ 0`, `m ≤ 6`, `X y = (1-y)/(1+y)`. -/
theorem zpow_deriv_oneSubOneAdd_le (m : ℕ) (hm : m ≤ 6) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ m * deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) z| ≤ 1440 := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp only [pow_zero, one_mul, Function.iterate_zero_apply]
    have h1 : |1 - z| ≤ 1 + z := by
      rw [abs_le]; constructor <;> linarith
    have h2 : |(1 - z) / (1 + z)| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + z),
        div_le_one (by linarith : (0 : ℝ) < 1 + z)]
      exact h1
    linarith
  · rw [deriv_iter_oneSubOneAdd m hpos z (by linarith : (-1 : ℝ) < z),
      abs_mul, abs_of_nonneg (pow_nonneg hz m), abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hmono : z ^ m ≤ (z + 1) ^ m := by
      apply pow_le_pow_left₀ hz; linarith
    have hb : z ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z|
        ≤ ((m.factorial : ℕ) : ℝ) := by
      have h2 : z ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z|
          ≤ (z + 1) ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z| :=
        mul_le_mul_of_nonneg_right hmono (abs_nonneg _)
      have h3 : (z + 1) ^ m * |Work.FTS.Nonlinear.FstarPkg.nInvClosed m z|
          = |(z + 1) ^ m * Work.FTS.Nonlinear.FstarPkg.nInvClosed m z| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) m)]
      rw [h3] at h2
      exact le_trans h2 (Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted m z hz)
    have h5 : ((m.factorial : ℕ) : ℝ) ≤ 720 := by
      interval_cases m <;> norm_num
    nlinarith [hb, h5]

/-- **The `D_z`-iterates of `z ↦ (1-z)/(1+z)` are uniformly bounded on `[0,∞)`.** -/
theorem DzdIter_oneSubOneAdd_le_local :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter k (fun y : ℝ => (1 - y) / (1 + y)) z| ≤ B := by
  let hfun : ℝ → ℝ → ℝ := fun y (_ : ℝ) => (1 - y) / (1 + y)
  refine ⟨250 * 1440, by norm_num, ?_⟩
  intro k hk z hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z' : ℝ => hfun z' θ) (Set.Ioi (-1)) := by
    intro θ hθ
    have hfun' : (fun z' : ℝ => hfun z' θ) = fun z' : ℝ => (1 - z') / (1 + z') := rfl
    rw [hfun']
    exact (contDiffOn_const.sub contDiffOn_id).div (contDiffOn_const.add contDiffOn_id)
      (fun y hy => by
        have hy2 : (-1 : ℝ) < y := hy
        linarith)
  have hsum := Work.Spaces.DzIter_eq_sum_scoef (h := hfun) hsmooth k z hz1 0
    (by refine ⟨le_rfl, ?_⟩; linarith [Real.pi_pos])
  rw [← Work.Elliptic.DzIter_rad (fun y : ℝ => (1 - y) / (1 + y)) k z 0, hsum]
  have hb := Work.Spaces.abs_sum_scoef_mul_le k 1440
    (fun m => z ^ m * Work.Spaces.pzIter m hfun z 0)
    (fun m hm => by
      rw [show Work.Spaces.pzIter m hfun z 0
          = deriv^[m] (fun y : ℝ => (1 - y) / (1 + y)) z from
        Work.FTS.NonlinRows.pzIter_radial_fn
          (fun y : ℝ => (1 - y) / (1 + y)) m z 0]
      exact zpow_deriv_oneSubOneAdd_le m (le_trans hm hk) hz)
  have hbell : (Work.Spaces.bell k : ℝ) ≤ 250 := by exact_mod_cast bell_le_six_local hk
  calc |∑ m ∈ Finset.range (k + 1), (Work.Spaces.scoef k m : ℝ)
        * (z ^ m * Work.Spaces.pzIter m hfun z 0)|
      ≤ (Work.Spaces.bell k : ℝ) * 1440 := hb
    _ ≤ 250 * 1440 := mul_le_mul_of_nonneg_right hbell (by norm_num)

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
