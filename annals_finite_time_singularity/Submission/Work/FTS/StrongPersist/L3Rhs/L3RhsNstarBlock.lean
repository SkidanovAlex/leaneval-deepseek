import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_Vs0_mul_Gs_eq_zero
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.Gsing_add_mul_open =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Open-quadrant facts about the ingredients of `Gsing` -/

/-- **The `L₁₂`-density of `SmoothOpen` `ℋ⁴`-data is integrable on `(0,∞)`.**  This is the
density form of `Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk` under
`L12dens = 3·F_*/s` (`Work.Elliptic.L12dens_eq_three_Fstar_div`). -/
theorem integrableOn_L12dens_smoothOpen {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 4 F) :
    MeasureTheory.IntegrableOn (Work.Elliptic.L12dens F) (Set.Ioi 0) := by
  have h := Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk α 4 F hso hmem
  exact MeasureTheory.IntegrableOn.congr_fun (h.const_mul 3)
    (fun r _ => (Work.Elliptic.L12dens_eq_three_Fstar_div F r).symm) measurableSet_Ioi

/-! ## The main theorem -/

/-- **`Gsing` is additive on the open-quadrant class.**  For `α > 0`, `f h` smooth on the open
quadrant with `HkMem α 4`, and `c : ℝ`, the singular term of §'The singular term' is linear:
`Gsing α (f + c·h) z = Gsing α f z + c·Gsing α h z` for every `z > 0`. -/
theorem Gsing_add_mul_open {α : ℝ} (hα : 0 < α) {f h : Work.FTS.Galerkin.Fn} (c : ℝ) {z : ℝ}
    (hz : 0 < z)
    (hsof : Work.FTS.EllipticEst.SmoothOpen f) (hmemf : Work.Spaces.HkMem α 4 f)
    (hsoh : Work.FTS.EllipticEst.SmoothOpen h) (hmemh : Work.Spaces.HkMem α 4 h) :
    Work.Elliptic.Gsing α (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Gsing α f z + c * Work.Elliptic.Gsing α h z := by
  have hmemf0 : Work.Spaces.HkMem α 0 f :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 4) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsof) hmemf
  have hmemh0 : Work.Spaces.HkMem α 0 h :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 4) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h).mp hsoh) hmemh
  -- additivity of `F_*`
  have hFs : ∀ s, 0 < s → Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.Fstar f s + c * Work.Elliptic.Fstar h s := fun s hs =>
    Work.FTS.EllSol.Fstar_add_mul
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsof.continuousOn hmemf0 hs)
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsoh.continuousOn hmemh0 hs)
  -- additivity of the `L₁₂`-densities
  have hdens : ∀ s, 0 < s → Work.Elliptic.L12dens (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.L12dens f s + c * Work.Elliptic.L12dens h s := fun s hs =>
    Work.FTS.EllSol.L12dens_add_mul
      (Work.FTS.EllSol.L12dens_slice_integrable hsof.continuousOn hmemf hs)
      (Work.FTS.EllSol.L12dens_slice_integrable hsoh.continuousOn hmemh hs)
  -- integrability of the densities on `(z,∞)`
  have hDf : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens f) (Set.Ioi z) :=
    (integrableOn_L12dens_smoothOpen (α := α) hsof hmemf).mono_set (Set.Ioi_subset_Ioi hz.le)
  have hDh : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens h) (Set.Ioi z) :=
    (integrableOn_L12dens_smoothOpen (α := α) hsoh hmemh).mono_set (Set.Ioi_subset_Ioi hz.le)
  -- interval integrability of the `Ḡ`-integrands
  have hIf := intervalIntegrable_rpow_Fstar_open α hα f hsof hmemf hz
  have hIh := intervalIntegrable_rpow_Fstar_open α hα h hsoh hmemh hz
  rw [Work.Elliptic.Gsing, Work.Elliptic.Gsing, Work.Elliptic.Gsing]
  rw [show Work.Elliptic.Gstar α (fun z θ => f z θ + c * h z θ) z
      = -(1 / (4 * α)) * Work.Elliptic.L12 (fun z θ => f z θ + c * h z θ) z from rfl]
  rw [Work.FTS.EllSol.L12_add_mul hz.le hdens hDf hDh,
      Work.FTS.EllSol.Gbar_add_mul hz hFs hIf hIh]
  rw [show Work.Elliptic.Gstar α f z = -(1 / (4 * α)) * Work.Elliptic.L12 f z from rfl,
      show Work.Elliptic.Gstar α h z = -(1 / (4 * α)) * Work.Elliptic.L12 h z from rfl]
  ring

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EllExist.Honesty.FarAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist.Honesty

open Work.FTS.PhiStar.RadialWAux (radP radQ radK radP_pos radQ_pos)

/-- `|x - y| ≤ |x| + |y|` (in the form used for the coefficients of the expansion). -/
lemma abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

/-- `radPsi = G2` pointwise (the `u ↦ zu` change of variables). -/
lemma radPsi_eq_G2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.RadialWAux.radPsi α m c z = G2 α m c z := by
  have h := Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow c
    (-(radP α m) - 1) hz
  simp only [G2, Work.FTS.PhiStar.RadialWAux.radPsi, radP] at *
  rw [h]
  ring_nf


/-- `z G2' = s⁺ G2 - c` on `(1,∞)`. -/
lemma G2_hasDerivAt {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi 1, HasDerivAt (G2 α m c)
      ((radP α m * G2 α m c z - c z) / z) z := by
  intro z hz
  have hz0 : 0 < z := lt_trans one_pos hz
  have h := radPsi_hasDerivAt (c := c) hα hα4 m hm hc hinf z hz0
  have hev : Work.FTS.PhiStar.RadialWAux.radPsi α m c =ᶠ[𝓝 z] G2 α m c := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with y hy
    exact radPsi_eq_G2 α m c hy
  have hd : (radP α m * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z
      = (radP α m * G2 α m c z - c z) / z := by
    rw [radPsi_eq_G2 α m c hz0]
  exact (h.congr_of_eventuallyEq hev.symm).congr_deriv hd

/-- `z G1' = s⁻ G1 + c` on `(0,∞)`, assuming the inner integrand converges on `(0,1)`. -/
lemma G1_hasDerivAt_of_intervalIntegrable {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi 0, HasDerivAt (G1 α m c)
      (((-radQ α m) * G1 α m c z + c z) / z) z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hA : HasDerivAt (G1A α m c) (G1f α m c z) z := G1A_hasDerivAt hc hInt z hz
  have hpow : HasDerivAt (fun y : ℝ => y ^ (G1s α m)) (G1s α m * z ^ (G1s α m - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz0)
  have hprod := hpow.mul hA
  have hfun : G1 α m c = fun y => y ^ (G1s α m) * G1A α m c y := by
    funext y
    exact G1_eq_zpow_mul_G1A α m c y
  have hqs : G1s α m = -radQ α m := by
    rw [G1s, radQ, neg_div]
  refine (hprod.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).congr_deriv ?_
  rw [← hqs, eq_div_iff hz0, G1_eq_zpow_mul_G1A]
  have hGf : G1f α m c z = c z * z ^ (G1a α m - 1) := rfl
  have e1 : z ^ (G1s α m - 1) * z = z ^ (G1s α m) := by
    rw [Real.rpow_sub_one hz0 (G1s α m)]
    exact div_mul_cancel₀ _ hz0
  have e2 : z ^ (G1s α m) * z ^ (G1a α m - 1) = z⁻¹ := by
    rw [← Real.rpow_add hz, show G1s α m + (G1a α m - 1) = -1 from by
      simp only [G1s, G1a]; ring, Real.rpow_neg_one]
  calc (G1s α m * z ^ (G1s α m - 1) * G1A α m c z
        + z ^ (G1s α m) * G1f α m c z) * z
      = G1s α m * G1A α m c z * (z ^ (G1s α m - 1) * z)
        + c z * (z ^ (G1s α m) * z ^ (G1a α m - 1)) * z := by
        rw [hGf]; ring
    _ = G1s α m * G1A α m c z * z ^ (G1s α m) + c z * z⁻¹ * z := by rw [e1, e2]
    _ = G1s α m * (z ^ (G1s α m) * G1A α m c z) + c z := by
        have hz1 : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
        linear_combination (c z) * hz1


end Work.FTS.EllExist.Honesty
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow15T2Aux.BoundC =====
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

/-! ## The two pointwise bounds for the open representative of `N₂^{ss}` -/

theorem row15_ptBound {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (G15 α Φs)) :
    (∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (N2ssO α Φs) z θ|
        ≤ 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs))) ∧
    (∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ l
          * Work.Spaces.pzIter l (Work.Spaces.DthIter i (N2ssO α Φs)) z θ|
        ≤ 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
  have hBnn : 0 ≤ Work.Spaces.WlInf α 4 (G15 α Φs) := Work.FTS.H2.WlInf_nonneg hGm
  have hAGs : Work.FTS.EllipticEst.SmoothOpen (AG15 α Φs) := by
    have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl (smoothOpen_A15' α) hGs
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h ?_
    intro z θ _ _ _
    simp [AG15]
  have hNil : N2ssO α Φs
      = fun z θ : ℝ => (fun z θ : ℝ => psi15 z) z θ * AG15 α Φs z θ := rfl
  constructor
  · intro m hm z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hwv : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have hρ : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ m :=
      mul_nonneg (mul_nonneg (by linarith) hwv) (pow_nonneg hz.le m)
    have hleib := sqm_pz_DthIter_mul_le_4_open m 0 hm (by norm_num)
      (fun z θ : ℝ => psi15 z) (AG15 α Φs) smoothOpen_psi15 hAGs z hz θ hθ
    rw [hNil, abs_mul, abs_of_nonneg hρ]
    refine le_trans (mul_le_mul_of_nonneg_left hleib hρ) ?_
    have hterm : ∀ c ∈ Finset.range (m + 1), ∀ a ∈ Finset.range (0 + 1),
        (1 + z) * Work.Spaces.w z * z ^ m
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|)
        ≤ Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) := by
      intro c hc a ha
      have hc4 : c ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have ha0 : a = 0 := by
        have h' := Finset.mem_range.mp ha
        omega
      subst ha0
      have hψ := Cp15_bd c c (le_refl c) (by omega) z hz θ
      rw [Nat.sub_self, pow_zero, mul_one] at hψ
      have hG := pzIter_AG_le hα hα1 hGs hGm (m - c) (by omega) z hz θ hθ
      have hzm : z ^ m = z ^ c * z ^ (m - c) := by rw [← pow_add]; congr 1; omega
      have hsplit : (1 + z) * Work.Spaces.w z * z ^ m
            * (|Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|
              * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|)
          = ((1 + z) * Work.Spaces.w z * z ^ c
              * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
            * (z ^ (m - c) * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|) := by
        rw [hzm]; ring
      have hstep : ((1 + z) * Work.Spaces.w z * z ^ c
              * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
            * (z ^ (m - c) * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|)
          ≤ Cp15 * (z ^ (m - c)
              * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ (m - c))) :=
        mul_le_mul hψ (mul_le_mul_of_nonneg_left hG (pow_nonneg hz.le _))
          (mul_nonneg (pow_nonneg hz.le _) (abs_nonneg _)) Cp15_pos.le
      refine le_trans (le_of_eq hsplit) ?_
      refine le_trans hstep ?_
      have hratio : z ^ (m - c) / (z + 1) ^ (m - c) ≤ 1 := by
        rw [div_le_one (pow_pos hz1 _)]
        exact pow_le_pow_left₀ hz.le (by linarith) _
      have hCKA : (0 : ℝ) ≤ Cp15 * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
        mul_nonneg Cp15_pos.le (mul_nonneg (mul_nonneg KAG15_pos.le (sq_nonneg α)) hBnn)
      calc Cp15 * (z ^ (m - c)
            * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ (m - c)))
          = (Cp15 * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)))
            * (z ^ (m - c) / (z + 1) ^ (m - c)) := by
            rw [div_eq_mul_inv]; ring_nf
        _ ≤ (Cp15 * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs))) * 1 :=
            mul_le_mul_of_nonneg_left hratio hCKA
        _ = Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) := by ring
    have hS : (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
        (1 + z) * Work.Spaces.w z * z ^ m
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|))
        ≤ (((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
      le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
        (sum_range_range_const m 0 _)
    have hexp : (1 + z) * Work.Spaces.w z * z ^ m
          * (257 * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                    z θ|))
        = 257 * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
            (1 + z) * Work.Spaces.w z * z ^ m
              * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                    z θ|)) := by
      rw [show (1 + z) * Work.Spaces.w z * z ^ m
            * (257 * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                      z θ|))
          = 257 * ((1 + z) * Work.Spaces.w z * z ^ m
            * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                      z θ|)) from by ring]
      rw [mul_sum_sum_const]
    rw [hexp]
    have hA5 : (((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ) ≤ 5 := by
      have h2 : m + 1 ≤ 5 := by omega
      have h3 : (((m + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
      have h4 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
      rw [h4, mul_one]
      exact h3
    have hC0 : (0 : ℝ) ≤ Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) :=
      mul_nonneg (mul_nonneg (mul_nonneg Cp15_pos.le KAG15_pos.le) (sq_nonneg α)) hBnn
    have hcore' : 257 * 5 * (Cp15 * KAG15) ≤ 200000 * KW15 := by
      show 257 * 5 * (Cp15 * KAG15)
        ≤ 200000 * (10 ^ 6 * (Cp15 * (KAG15 + KAGd15 + 1) + 1) + 1)
      exact arith_hA_core Cp15 KAG15 KAGd15 Cp15_pos KAG15_pos KAGd15_pos
    have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
    calc (257 : ℝ) * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
          (1 + z) * Work.Spaces.w z * z ^ m
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|))
        ≤ 257 * ((((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
            * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs))) :=
          mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = (257 * ((((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)))
            * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) := by ring
      _ ≤ (257 * 5) * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hC0
      _ = (257 * 5 * (Cp15 * KAG15)) * (α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) := by ring
      _ ≤ (200000 * KW15) * (α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
          mul_le_mul_of_nonneg_right hcore' (mul_nonneg (sq_nonneg α) hBnn)
      _ ≤ (200000 * KW15) * (α * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hα2 hBnn)
            (mul_nonneg (by norm_num) KW15_pos.le)
      _ = 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)) := by ring
  · intro i l hi hli z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hl4 : l ≤ 4 := by omega
    have hi4 : i ≤ 4 := by omega
    have hsin2 : 0 ≤ Real.sin (2 * θ) := by
      have hs0 : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_mem_Icc ⟨hθI.1, by linarith [hθI.2, Real.pi_pos]⟩
      have hc0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
      rw [Real.sin_two_mul]; positivity
    have hw0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hsin2 _)
    have hwv : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have hρ : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ l :=
      mul_nonneg (mul_nonneg (by linarith) hwv) (pow_nonneg hz.le l)
    have hleib := sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
      (fun z θ : ℝ => psi15 z) (AG15 α Φs) smoothOpen_psi15 hAGs z hz θ hθ
    rw [hNil, abs_mul, abs_of_nonneg hρ]
    refine le_trans (mul_le_mul_of_nonneg_left hleib hρ) ?_
    have hterm : ∀ c ∈ Finset.range (l + 1), ∀ a ∈ Finset.range (i + 1),
        (1 + z) * Work.Spaces.w z * z ^ l
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                  z θ|)
        ≤ Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      intro c hc a ha
      have hc4 : c ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      by_cases ha0 : a = 0
      · subst ha0
        have hψ := Cp15_bd c c (le_refl c) (by omega) z hz θ
        rw [Nat.sub_self, pow_zero, mul_one] at hψ
        have hG := pzIter_DthIter_AG_le hα hα1 hGs hGm i (l - c) hi (by omega) z hz θ hθ
        have hzm : z ^ l = z ^ c * z ^ (l - c) := by rw [← pow_add]; congr 1; omega
        have hsplit : (1 + z) * Work.Spaces.w z * z ^ l
              * (|Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs)) z θ|)
            = ((1 + z) * Work.Spaces.w z * z ^ c
                * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
              * (z ^ (l - c)
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs))
                    z θ|) := by
          rw [hzm]; ring
        have hstep : ((1 + z) * Work.Spaces.w z * z ^ c
              * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
              * (z ^ (l - c)
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs)) z θ|)
            ≤ Cp15 * (z ^ (l - c)
                * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    / (z + 1) ^ (l - c))) :=
          mul_le_mul hψ (mul_le_mul_of_nonneg_left hG (pow_nonneg hz.le _))
            (mul_nonneg (pow_nonneg hz.le _) (abs_nonneg _)) Cp15_pos.le
        refine le_trans (le_of_eq hsplit) ?_
        refine le_trans hstep ?_
        have hratio : z ^ (l - c) / (z + 1) ^ (l - c) ≤ 1 := by
          rw [div_le_one (pow_pos hz1 _)]
          exact pow_le_pow_left₀ hz.le (by linarith) _
        have hCW : (0 : ℝ) ≤ Cp15 * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_nonneg Cp15_pos.le
            (mul_nonneg (mul_nonneg (mul_nonneg KAGd15_pos.le hα.le) hBnn) hw0)
        calc Cp15 * (z ^ (l - c)
              * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  / (z + 1) ^ (l - c)))
            = (Cp15 * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * (z ^ (l - c) / (z + 1) ^ (l - c)) := by
              rw [div_eq_mul_inv]; ring_nf
          _ ≤ (Cp15 * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) * 1 :=
              mul_le_mul_of_nonneg_left hratio hCW
          _ = Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      · have hpz : Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z))
            z θ = 0 := by
          simp only [pzIter_DthIter_zFn psi15 a c (by omega)]
        rw [hpz]
        simp only [abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Cp15_pos.le KAGd15_pos.le) hα.le) hBnn)
          hw0
    have hS : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        (1 + z) * Work.Spaces.w z * z ^ l
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                  z θ|))
        ≤ (((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)
          * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
      le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
        (sum_range_range_const l i _)
    have hexp : (1 + z) * Work.Spaces.w z * z ^ l
          * (257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                    z θ|))
        = 257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
            (1 + z) * Work.Spaces.w z * z ^ l
              * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                    z θ|)) := by
      rw [show (1 + z) * Work.Spaces.w z * z ^ l
            * (257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                      z θ|))
          = 257 * ((1 + z) * Work.Spaces.w z * z ^ l
            * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                      z θ|)) from by ring]
      rw [mul_sum_sum_const]
    rw [hexp]
    have hA5 : (((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ) ≤ 25 := by
      have h2 : l + 1 ≤ 5 := by omega
      have h3 : (((l + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
      have h4 : i + 1 ≤ 5 := by omega
      have h5 : (((i + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h4
      nlinarith
    have hC0 : (0 : ℝ) ≤ Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Cp15_pos.le KAGd15_pos.le) hα.le) hBnn)
        hw0
    have hcore' : 257 * 25 * (Cp15 * KAGd15) ≤ 200000 * KW15 := by
      show 257 * 25 * (Cp15 * KAGd15)
        ≤ 200000 * (10 ^ 6 * (Cp15 * (KAG15 + KAGd15 + 1) + 1) + 1)
      exact arith_hB_core Cp15 KAG15 KAGd15 Cp15_pos KAG15_pos KAGd15_pos
    calc (257 : ℝ) * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) * Work.Spaces.w z * z ^ l
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                  z θ|))
        ≤ 257 * ((((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)
            * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
          mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = (257 * ((((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)))
            * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring
      _ ≤ (257 * 25) * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hC0
      _ = (257 * 25 * (Cp15 * KAGd15))
            * (α * (Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by ring
      _ ≤ (200000 * KW15)
            * (α * (Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
          mul_le_mul_of_nonneg_right hcore' (mul_nonneg hα.le (mul_nonneg hBnn hw0))
      _ = 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow19T2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSqZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

namespace HsZ

/-! ## 1. The `D_z`-bound for `D_zF_*` with the angular factor kept

`Gs_bounds` records `|D_z^m D_zF_*| ≤ C·α·z/(1+z)²`; for the pointwise majorant of the row-19
coefficient we need the same bound *without* discarding the angular factor `Γ(θ)` (which is
what makes the resulting `ℋ⁴`-majorant integrable in `θ`).  The bound follows from the
factorisation `D_z^m D_zF_* = (αΓ(θ)/c)·D_z^m Hz` (`DzIter_Gs_factor`) and the α-free radial
bound `abs_DzIter_Hz_le`; `α ≤ 1` is *not* needed because the constant may depend on `α`. -/

theorem Gs_DzIter_le {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, m ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter m (Gs α) z θ|
        ≤ K * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by
  obtain ⟨CH, hCHpos, hCH⟩ := abs_DzIter_Hz_le
  refine ⟨CH, hCHpos, ?_⟩
  intro m hm z hz θ hθ
  have hz' : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  have hcoef : 0 ≤ α * Work.Spaces.Gam α θ / Work.Spaces.c α :=
    div_nonneg (mul_nonneg hα.le hG0) hcpos.le
  rw [Row19GsAux.DzIter_Gs_factor hα m hz']
  have hHz := hCH m hm z hz θ
  calc |α * Work.Spaces.Gam α θ / Work.Spaces.c α
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
          * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ| := by
        rw [abs_mul, abs_of_nonneg hcoef]
    _ ≤ (α * Work.Spaces.Gam α θ / Work.Spaces.c α) * (CH * (z / (1 + z) ^ 2)) :=
        mul_le_mul_of_nonneg_left hHz hcoef
    _ = CH * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by ring

/-- The same bound for the mixed `D_z`-iterates of `D_θ^i (D_zF_*)`, `i ≥ 1`. -/
theorem Gs_DzIter_DthIter_le {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ m : ℕ, m ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter m (Work.Spaces.DthIter i (Gs α)) z θ|
        ≤ K * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by
  obtain ⟨CH, hCHpos, hCH⟩ := abs_DzIter_Hz_le
  obtain ⟨Cg, hCgpos, hCg⟩ := dthIter_Gam_le (α := α) hα
  refine ⟨CH * Cg, by positivity, ?_⟩
  intro i hi1 hi4 m hm z hz θ hθ
  have hz' : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  have hcoef : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  rw [Row19GsAux.DzIter_DthIter_Gs_factor hα i m hz' hθ]
  have hDth : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
      = Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ :=
    Work.FTS.LocData.DthIter_rad_eq i (fun θ => Work.Spaces.Gam α θ) 0 θ
  rw [hDth]
  have hΓ := hCg i hi4 θ hθI
  have hHz := hCH m hm z hz θ
  calc |α / Work.Spaces.c α * Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
      = (α / Work.Spaces.c α) * |Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ|
          * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hcoef]
    _ ≤ (α / Work.Spaces.c α) * (Cg * Work.Spaces.Gam α θ) * (CH * (z / (1 + z) ^ 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hΓ hcoef) hHz (abs_nonneg _) ?_
        exact mul_nonneg hcoef (mul_nonneg hCgpos.le hG0)
    _ = CH * Cg * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by ring

/-! ## 2. The pure `D_z`-bound for the row-19 coefficient -/

theorem DzIter_Vs_mul_Gs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ K : ℝ, 0 < K ∧ ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
        ≤ K * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ := by
  obtain ⟨K1, hK1pos, hK1⟩ := Gs_DzIter_le (α := α) hα
  have hVs : Work.FTS.LocData.SmoothQuad (Vs α Φs) := Vs_smoothQuad hα hs
  have hGs : Work.FTS.LocData.SmoothQuad (Gs α) := smoothQuad_Gs_of_pos hα
  have hmem : Work.Spaces.WlInfMem α 4 (Vs α Φs) := by
    simpa only [Vs, Work.FTS.Nonlin.PhiTs] using hs.V.1
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hΛ0 : 0 ≤ K1 * (α / Work.Spaces.c α) := mul_nonneg hK1pos.le (div_nonneg hα.le hcpos.le)
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 (Vs α Φs) := Work.Spaces.WlInf_nonneg _ _ _ hmem
  refine ⟨16 * 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (K1 * (α / Work.Spaces.c α)) + 1,
    by positivity, ?_⟩
  intro i hi4 z hz θ hθ
  have hLeib := Work.FTS.LocData.DzIter_mul_smoothQuad i (Vs α Φs) (Gs α) hz
    (hVs.curry_z hθ) (hGs.curry_z hθ)
  have hze : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).1
  have hterm : ∀ b ∈ Finset.range (i + 1),
      |(i.choose b : ℝ) * (Work.Spaces.DzIter b (Vs α Φs) z θ
        * Work.Spaces.DzIter (i - b) (Gs α) z θ)|
        ≤ (i.choose b : ℝ)
            * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
                * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hVb : |Work.Spaces.DzIter b (Vs α Φs) z θ| ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) :=
      Work.FTS.H2.WPQ.DzIter_le_WlInf hVs hmem (by omega) hz hθ
    have hGb : |Work.Spaces.DzIter (i - b) (Gs α) z θ|
        ≤ K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) :=
      hK1 (i - b) (by omega) z hz θ hθ
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact mul_le_mul hVb hGb (abs_nonneg _) (by positivity)
  calc |Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
      = |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.DzIter b (Vs α Φs) z θ
            * Work.Spaces.DzIter (i - b) (Gs α) z θ)| := by rw [hLeib]
    _ ≤ ∑ b ∈ Finset.range (i + 1),
          |(i.choose b : ℝ) * (Work.Spaces.DzIter b (Vs α Φs) z θ
            * Work.Spaces.DzIter (i - b) (Gs α) z θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) :=
        Finset.sum_le_sum hterm
    _ = (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ))
          * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
        rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ i * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 16 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 : ℝ) ^ i ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hi4
          _ = 16 := by norm_num
    _ ≤ (16 * 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (K1 * (α / Work.Spaces.c α)) + 1)
          * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ := by
        nlinarith [hW0, hΛ0, hze, hG0]

/-! ## 3. The mixed bound for the row-19 coefficient -/

theorem Mixed_Vs_mul_Gs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ K : ℝ, 0 < K ∧ ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
        ≤ K * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨K1, hK1pos, hK1⟩ := Gs_DzIter_le (α := α) hα
  obtain ⟨K2, hK2pos, hK2⟩ := Gs_DzIter_DthIter_le (α := α) hα
  have hVs : Work.FTS.LocData.SmoothQuad (Vs α Φs) := Vs_smoothQuad hα hs
  have hGs : Work.FTS.LocData.SmoothQuad (Gs α) := smoothQuad_Gs_of_pos hα
  have hmem : Work.Spaces.WlInfMem α 4 (Vs α Φs) := by
    simpa only [Vs, Work.FTS.Nonlin.PhiTs] using hs.V.1
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 (Vs α Φs) := Work.Spaces.WlInf_nonneg _ _ _ hmem
  have hαc0 : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  set A : ℝ := K1 * (α / Work.Spaces.c α) with hA
  set B : ℝ := K2 * (α / Work.Spaces.c α) with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg hK1pos.le hαc0
  have hB0 : 0 ≤ B := by rw [hB]; exact mul_nonneg hK2pos.le hαc0
  refine ⟨6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)) + 1, by positivity, ?_⟩
  intro j i hi1 hij z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hLeib := Work.FTS.H2.WPQ.mixed_mul_eq_smoothQuad (j := j) (i := i)
    (f := Vs α Φs) (g := Gs α) hVs hGs z hz θ hθ
  have hze : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθI).2
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := angW_nonneg hα hθI
  have hbin : ∀ n : ℕ, n ≤ 4 → ∀ a : ℕ, (n.choose a : ℝ) ≤ 16 := by
    intro n hn a
    by_cases ha : a ∈ Finset.range (n + 1)
    · refine le_trans (Finset.single_le_sum (f := fun b => (n.choose b : ℝ))
        (fun _ _ => Nat.cast_nonneg _) ha) ?_
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      calc (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hn
        _ = 16 := by norm_num
    · have hlt : n < a := by
        rw [Finset.mem_range] at ha; omega
      rw [Nat.choose_eq_zero_of_lt hlt]
      norm_num
  have hC0 : 0 ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
      * (z / (1 + z) ^ 2)
      * (Work.Spaces.Gam α θ
        + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by positivity
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      |((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a (Vs α Φs) z θ
              * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|
        ≤ 256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
    intro a ha b hb
    have hai : a ≤ i := by have := Finset.mem_range.mp ha; omega
    have hbj : b ≤ j := by have := Finset.mem_range.mp hb; omega
    have hca : (i.choose a : ℝ) ≤ 16 := hbin i (by omega) a
    have hcb : (j.choose b : ℝ) ≤ 16 := hbin j (by omega) b
    have hca0 : (0 : ℝ) ≤ (i.choose a : ℝ) := Nat.cast_nonneg _
    have hcb0 : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
    have hmid : |Work.Spaces.mixed b a (Vs α Φs) z θ|
        * |Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|
        ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        have hVsb : |Work.Spaces.mixed b 0 (Vs α Φs) z θ|
            ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) := by
          rw [Work.Spaces.mixed_zero_right]
          exact Work.FTS.H2.WPQ.DzIter_le_WlInf hVs hmem (by omega) hz hθ
        have hGsb : |Work.Spaces.mixed (j - b) (i - 0) (Gs α) z θ|
            ≤ B * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by
          rw [Nat.sub_zero]
          exact hK2 i hi1 (by omega) (j - b) (by omega) z hz θ hθ
        refine le_trans (mul_le_mul hVsb hGsb (abs_nonneg _) (by positivity)) ?_
        have h1 : B * Work.Spaces.Gam α θ
            ≤ (A + B + 1) * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
          have h2 : B * Work.Spaces.Gam α θ
              ≤ B * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            mul_le_mul_of_nonneg_left (by linarith) hB0
          have h5 : B * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              ≤ (A + B + 1) * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            have h6 : 0 ≤ Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by linarith
            nlinarith [h6]
          linarith
        calc (15 * Work.Spaces.WlInf α 4 (Vs α Φs))
                * (B * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))
            = (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
                * (B * Work.Spaces.Gam α θ)) * (z / (1 + z) ^ 2) := by ring
          _ ≤ (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
                * ((A + B + 1) * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
                * (z / (1 + z) ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hze
          _ = 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
                * (z / (1 + z) ^ 2)
                * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      · have hVsb : |Work.Spaces.mixed b a (Vs α Φs) z θ|
            ≤ 15 * (Work.Spaces.WlInf α 4 (Vs α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Work.FTS.H2.WPQ.Mixed_le_WlInf hα hVs hmem hapos (by omega) hz hθ
        have hGsb : |Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|
            ≤ max A B * (z / (1 + z) ^ 2) := by
          rcases Nat.eq_zero_or_pos (i - a) with hid | hidpos
          · rw [hid, Work.Spaces.mixed_zero_right]
            have h := hK1 (j - b) (by omega) z hz θ hθ
            refine le_trans (le_trans h ?_) (mul_le_mul_of_nonneg_right (le_max_left A B) hze)
            calc A * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2)
                ≤ A * 1 * (z / (1 + z) ^ 2) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hA0) hze
              _ = A * (z / (1 + z) ^ 2) := by ring
          · have h := hK2 (i - a) hidpos (by omega) (j - b) (by omega) z hz θ hθ
            refine le_trans (le_trans h ?_) (mul_le_mul_of_nonneg_right (le_max_right A B) hze)
            calc B * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2)
                ≤ B * 1 * (z / (1 + z) ^ 2) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hB0) hze
              _ = B * (z / (1 + z) ^ 2) := by ring
        refine le_trans (mul_le_mul hVsb hGsb (abs_nonneg _) (by positivity)) ?_
        have h1 : max A B ≤ A + B + 1 := by
          refine max_le ?_ ?_ <;> linarith [hA0, hB0]
        calc (15 * (Work.Spaces.WlInf α 4 (Vs α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * (max A B * (z / (1 + z) ^ 2))
            ≤ (15 * (Work.Spaces.WlInf α 4 (Vs α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * ((A + B + 1) * (z / (1 + z) ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hze) (by positivity)
          _ = 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
                * (z / (1 + z) ^ 2)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
          _ ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
                * (z / (1 + z) ^ 2)
                * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              linarith
    calc |((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a (Vs α Φs) z θ
              * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|
        = ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (|Work.Spaces.mixed b a (Vs α Φs) z θ|
              * |Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|) := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg hca0 hcb0), abs_mul]
      _ ≤ (16 * 16) * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul (mul_le_mul hca hcb hcb0 (by norm_num)) hmid (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = 256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by norm_num
  have hinner : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|)
        ≤ 5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
    intro a ha
    calc (∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|)
        ≤ ∑ _b ∈ Finset.range (j + 1), 256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
            * (A + B + 1) * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Finset.sum_le_sum (fun b hb => hterm a ha b hb)
      _ ≤ 5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (by omega : j + 1 ≤ 5)
  calc |Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
      = |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)| := by rw [hLeib]
    _ ≤ ∑ a ∈ Finset.range (i + 1), |∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)| :=
        Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a ∈ Finset.range (i + 1), 5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
            * (A + B + 1) * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
        Finset.sum_le_sum hinner
    _ ≤ 5 * (5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (by omega : i + 1 ≤ 5)
    _ = 6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring
    _ ≤ (6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)) + 1)
          * (z / (1 + z) ^ 2)
          * (Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
        rw [show 6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            = 6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1))
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) from by ring]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hze) ?_
        linarith

/-! ## 4. The pointwise `ℋ⁴`-majorant -/

/-- `w z * (z/(1+z)²) = 1/z` for `z > 0`. -/
lemma w_mul_profile {z : ℝ} (hz : 0 < z) :
    Work.Spaces.w z * (z / (1 + z) ^ 2) = 1 / z := by
  have h1 : z ≠ 0 := ne_of_gt hz
  have h2 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  rw [Work.Spaces.w]
  field_simp

/-- At `z = 0` the `ℋ⁴`-integrand vanishes (the radial weight `w 0 = 0` kills both sums). -/
lemma HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-- The pointwise majorant of the `ℋ⁴`-integrand of `V(Φ̃_*)·D_zF_*`: the angular factor
`(Γ + (α+sin 2θ)sin(2θ)^{α/5})²·sin(2θ)^{-γ}` is integrable in `θ` (`theta_majorant_integrable`),
so this gives the integrability of every `θ`-slice of the integrand. -/
theorem Vs_mul_Gs_HkIntegrand_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ K : ℝ → ℝ, (∀ z, 0 ≤ K z) ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
        ≤ K z * ((Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  obtain ⟨K1, hK1pos, hK1⟩ := DzIter_Vs_mul_Gs_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  obtain ⟨K2, hK2pos, hK2⟩ := Mixed_Vs_mul_Gs_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hKfun0 : ∀ z : ℝ, 0 ≤ (5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) + 1 := by
    intro z
    have h : 0 ≤ (5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) :=
      mul_nonneg (by nlinarith [sq_nonneg K1, sq_nonneg K2]) (by positivity)
    linarith
  refine ⟨fun z => (5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) + 1, hKfun0, ?_⟩
  intro z hz θ hθ
  have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R hθ
  have hS0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsin0 _
  have hbracket0 : 0 ≤ (Work.Spaces.Gam α θ
      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) hS0
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    exact mul_nonneg (hKfun0 0) hbracket0
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    by_cases hsin : Real.sin (2 * θ) = 0
    · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 4 _ z θ hsin]
      exact mul_nonneg (hKfun0 z) hbracket0
    · have hθoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        refine ⟨?_, ?_⟩
        · rcases eq_or_lt_of_le hθ.1 with h | h
          · exact absurd (by rw [← h]; simp) hsin
          · exact h
        · rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hsin
      have hsinpos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθoo.1]) (by linarith [hθoo.2, Real.pi_pos])
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := angW_nonneg hα hθ
      have hΓΛ0 : 0 ≤ Work.Spaces.Gam α θ
          + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by linarith
      have hzs : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
      have hwprof : Work.Spaces.w z * (z / (1 + z) ^ 2) = 1 / z := w_mul_profile hzpos
      have hsqw : (z / (1 + z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2 = (1 / z) ^ 2 := by
        rw [mul_comm, ← mul_pow, hwprof]
      -- the pure `D_z` slots
      have htermZ : ∀ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        intro i hi
        have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hb := hK1 i hi4 z hz θ hθoo
        have hpair0 : 0 ≤ K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ :=
          mul_nonneg (mul_nonneg hK1pos.le hzs) hΓ0
        have h2 : (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
            ≤ (K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ) ^ 2 :=
          sq_le_sq.mpr (by rw [abs_of_nonneg hpair0]; exact hb)
        have h3 : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          wdiv_sq_le hα hθ
        have hs2 : (Work.Spaces.Gam α θ) ^ 2 ≤ (Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
          pow_le_pow_left₀ hΓ0 (by linarith) 2
        calc (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
          _ ≤ (K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ) ^ 2
                * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
              mul_le_mul h2 h3 (sq_nonneg _) (by positivity)
          _ = K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
              rw [show (K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ) ^ 2
                    * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                  = K1 ^ 2 * ((z / (1 + z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2)
                    * (Work.Spaces.Gam α θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by ring,
                hsqw]
          _ ≤ K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
              rw [show K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  = (K1 ^ 2 * (1 / z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                    * (Work.Spaces.Gam α θ) ^ 2 from by ring]
              rw [show K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                    + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  = (K1 ^ 2 * (1 / z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                    * (Work.Spaces.Gam α θ
                      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 from by ring]
              exact mul_le_mul_of_nonneg_left hs2 (by positivity)
      have hZ : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 5 * (K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        calc (∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (4 + 1), K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
              Finset.sum_le_sum htermZ
          _ = 5 * (K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
      -- the mixed slots
      have htermM : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
            ≤ K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        intro i hi j hj
        split_ifs with hc
        · have hb := hK2 j i hc.1 hc.2 z hz θ hθoo
          have hpair0 : 0 ≤ K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            mul_nonneg (mul_nonneg hK2pos.le hzs) hΓΛ0
          have h2 : (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
              ≤ (K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2 :=
            sq_le_sq.mpr (by rw [abs_of_nonneg hpair0]; exact hb)
          have h3 : (Work.Spaces.Wt α z θ) ^ 2
              = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            Wt_sq hsin0
          calc (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
              = (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
                * (Work.Spaces.Wt α z θ) ^ 2 := by ring
            _ ≤ (K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2
                * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
                rw [h3]
                exact mul_le_mul h2 le_rfl (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _)) (sq_nonneg _)
            _ = K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
                rw [show (K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
                      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2
                      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                    = K2 ^ 2 * ((z / (1 + z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2)
                      * (Work.Spaces.Gam α θ
                        + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by ring,
                  hsqw]
        · exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
            (sq_nonneg _)) hS0
      have hM : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 25 * (K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (4 + 1), (∑ _j ∈ Finset.range (4 + 1), K2 ^ 2 * (1 / z) ^ 2
                * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
              Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => htermM i hi j hj))
          _ = 25 * (K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul, nsmul_eq_mul]
              norm_num
              ring
      rw [Work.Spaces.HkIntegrand]
      calc (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 5 * (K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            + 25 * (K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := add_le_add hZ hM
        _ = (5 * K1 ^ 2 + 25 * K2 ^ 2) * (1 / z ^ 2) * ((Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [div_pow, one_pow]
              ring
        _ ≤ ((5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) + 1) * ((Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (sq_nonneg _) hS0)
              nlinarith [show (0 : ℝ) ≤ 1 / z ^ 2 by positivity]

/-! ## 5. Integrability of the angular slices -/

theorem integrableOn_slice_Vs_mul_Gs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4
        (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) Work.Spaces.Iθ := by
  obtain ⟨K, hK0, hK⟩ := Vs_mul_Gs_HkIntegrand_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  obtain ⟨hmaj1, hmaj2⟩ := theta_majorant_integrable (α := α) hα
  have hsm : Work.FTS.LocData.SmoothQuad (fun z θ => Vs α Φs z θ * Gs α z θ) :=
    Work.FTS.LocData.smoothQuad_mul (Vs_smoothQuad hα hs) (smoothQuad_Gs_of_pos hα)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (fun z θ => Vs α Φs z θ * Gs α z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 _ hsm
  intro z hz
  have hint : MeasureTheory.IntegrableOn (fun θ => K z * ((Work.Spaces.Gam α θ
      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) Work.Spaces.Iθ :=
    hmaj2.const_mul (K z)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α 4
      (fun z θ => Vs α Φs z θ * Gs α z θ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  refine MeasureTheory.Integrable.mono' hint haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
  exact hK z (le_of_lt hz) θ hθ

/-! ## 6. The lower bound at the origin

For `V(Φ̃_*)` itself (not only its `z = 0` slice) the lower bound `c / z²` is available on a
*small* interval `(0,δ)` of `z` only: the Lipschitz control `|V(z,θ) − V(0,θ)| ≤ M·z` (from
`StarPkg.V`) degrades as `z → 1/2`.  That is all the non-integrability argument needs: `z ↦ 1/z²`
is non-integrable on `(0,δ)` for every `δ > 0`. -/

theorem slice_lower_bound_Vs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (h0 : ∃ θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧ Vs α Φs 0 θ ≠ 0) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ z : ℝ, 0 < z → z < δ →
      c / z ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (fun z θ => Vs α Φs z θ * Gs α z θ) z θ := by
  obtain ⟨θ₀, hθ₀, hne⟩ := h0
  obtain ⟨a, b, c₀, ha0, haθ, hθb, hb, hc₀, hlow⟩ :=
    Vs0_interval_lower (α := α) (Cs := Cs) (Φs := Φs) hα hs hθ₀ hne
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hlip := Vs_lipschitz (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hden : 0 < 2 * (max Cs 0 * α + 1) := by linarith
  have hδpos : 0 < min (1 / 2 : ℝ) (c₀ / (2 * (max Cs 0 * α + 1))) :=
    lt_min (by norm_num) (div_pos hc₀ hden)
  -- the Lipschitz bound gives `|V(z,θ)| ≥ c₀/2` on `(a,b)` as long as `z` is small
  have hlow2 : ∀ z : ℝ, 0 < z → z < min (1 / 2 : ℝ) (c₀ / (2 * (max Cs 0 * α + 1))) →
      ∀ θ : ℝ, θ ∈ Set.Ioo a b → c₀ / 2 ≤ |Vs α Φs z θ| := by
    intro z hz0 hzmin θ hθ
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz0
    have h1 : |Vs α Φs z θ - Vs α Φs 0 θ| ≤ max Cs 0 * α * z :=
      hlip z hzI θ ⟨by linarith [hθ.1, ha0], by linarith [hθ.2, hb]⟩
    have h2 : c₀ ≤ |Vs α Φs 0 θ| := hlow θ hθ
    have h3 : |Vs α Φs 0 θ| ≤ |Vs α Φs z θ - Vs α Φs 0 θ| + |Vs α Φs z θ| := by
      have h := abs_add_le (Vs α Φs 0 θ - Vs α Φs z θ) (Vs α Φs z θ)
      rw [sub_add_cancel] at h
      rwa [abs_sub_comm] at h
    have hzle : z ≤ c₀ / (2 * (max Cs 0 * α + 1)) :=
      le_trans (le_of_lt hzmin) (min_le_right _ _)
    have h4 : max Cs 0 * α * z ≤ c₀ / 2 := by
      refine le_trans (mul_le_mul_of_nonneg_left hzle hM0) ?_
      have h5 : max Cs 0 * α * (c₀ / (2 * (max Cs 0 * α + 1)))
          = (max Cs 0 * α / (max Cs 0 * α + 1)) * (c₀ / 2) := by
        field_simp
      rw [h5]
      refine mul_le_of_le_one_left (by linarith) ?_
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hcb : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hb]⟩
  have hsa0 : 0 ≤ Real.sin a :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha0]) (by linarith [hb, Real.pi_pos])).le
  have hg₀pos : 0 < (Real.sin a * Real.cos b ^ 2) ^ (α / 3) := by
    refine Real.rpow_pos_of_pos ?_ _
    have hsa : 0 < Real.sin a :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ha0]) (by linarith [hb, Real.pi_pos])
    positivity
  have hGam_low : ∀ θ ∈ Set.Ioo a b, (Real.sin a * Real.cos b ^ 2) ^ (α / 3)
      ≤ Work.Spaces.Gam α θ := by
    intro θ hθ
    have hsa0' : 0 ≤ Real.sin a * Real.cos b ^ 2 := mul_nonneg hsa0 (sq_nonneg _)
    have hsb : Real.sin a * Real.cos b ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2 := by
      have hsp : Real.sin a ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (x := a) (y := θ)
          (by linarith [ha0, Real.pi_pos]) (le_of_lt (lt_trans hθ.2 hb)) (le_of_lt hθ.1)
      have hcθ : 0 ≤ Real.cos θ :=
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩).le
      have hc : Real.cos b ^ 2 ≤ Real.cos θ ^ 2 := by
        have h1 : Real.cos b ≤ Real.cos θ :=
          Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := b)
            (le_of_lt (lt_trans ha0 hθ.1)) (by linarith [hb, Real.pi_pos]) (le_of_lt hθ.2)
        nlinarith [h1, hcb.le, hcθ]
      exact mul_le_mul hsp hc (sq_nonneg _)
        (Real.sin_nonneg_of_mem_Icc ⟨le_of_lt (lt_trans ha0 hθ.1),
          by linarith [hθ.2, hb, Real.pi_pos]⟩)
    rw [Work.Spaces.Gam]
    exact Real.rpow_le_rpow hsa0' hsb (by linarith)
  set K₀ : ℝ := (c₀ / 2) * (α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3))
      / Work.Spaces.c α) * (1 / 4) with hK₀def
  have hK₀pos : 0 < K₀ := by
    rw [hK₀def]
    refine mul_pos (mul_pos (by linarith) (div_pos (mul_pos hα hg₀pos) hcpos)) (by norm_num)
  have hb_a : 0 < b - a := by linarith [haθ, hθb]
  refine ⟨(b - a) * K₀ ^ 2, min (1 / 2 : ℝ) (c₀ / (2 * (max Cs 0 * α + 1))),
    mul_pos hb_a (pow_pos hK₀pos 2), hδpos, ?_⟩
  intro z hz0 hzδ
  have hz1 : z < 1 / 2 := lt_of_lt_of_le hzδ (min_le_left _ _)
  have hint := integrableOn_slice_Vs_mul_Gs (α := α) (Cs := Cs) (Φs := Φs) hα hs z hz0
  have hw0z : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_nonneg (by positivity) (by positivity)
  have hpt : ∀ θ ∈ Set.Ioo a b,
      K₀ ^ 2 / z ^ 2 ≤ ((fun z θ => Vs α Φs z θ * Gs α z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ :=
      ⟨le_of_lt (lt_trans ha0 hθ.1), le_of_lt (lt_trans hθ.2 hb)⟩
    have hGamθ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
    have hX0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hX1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsp : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hX0 _
    have hsp1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hX0.le hX1 (by rw [Work.Spaces.eta]; norm_num)
    have hprof : z / 4 ≤ |prof z| := by
      have h1 : 0 ≤ 2 * z * (1 - z) := by nlinarith [hz0, hz1]
      have h2 : 0 < (1 + z) ^ 3 := pow_pos (by linarith) 3
      rw [prof, abs_of_nonneg (div_nonneg h1 h2.le), le_div_iff₀ h2]
      have h3 : (1 + z) ^ 3 ≤ 27 / 8 := by
        have h4 : 1 + z ≤ 3 / 2 := by linarith
        nlinarith [hz0, sq_nonneg (1 + z), h4]
      nlinarith [hz0, hz1, h3]
    have hVslow : c₀ / 2 ≤ |Vs α Φs z θ| := hlow2 z hz0 hzδ θ hθ
    have hGslow : (α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3)) / Work.Spaces.c α) * (z / 4)
        ≤ |Gs α z θ| := by
      rw [Gs_eq_prof hα (by linarith : (-1 : ℝ) < z), abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg hα.le hGamθ0) hcpos.le)]
      have hΓθ : (Real.sin a * Real.cos b ^ 2) ^ (α / 3) ≤ Work.Spaces.Gam α θ :=
        hGam_low θ hθ
      have h1 : α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3)) / Work.Spaces.c α
          ≤ α * Work.Spaces.Gam α θ / Work.Spaces.c α :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΓθ hα.le) hcpos.le
      exact mul_le_mul h1 hprof (by positivity) (by positivity)
    have hw : 1 / z ^ 2
        ≤ |Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| := by
      have hw1 : 1 / z ^ 2 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
        rw [div_mul_cancel₀ 1 (ne_of_gt (by positivity : (0 : ℝ) < z ^ 2))]
        nlinarith [hz0]
      have hprod : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        div_nonneg hw0z hsp.le
      rw [abs_of_nonneg hprod]
      have h2 : Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        rw [le_div_iff₀ hsp]
        nlinarith [hw0z, hsp1]
      linarith
    have hf : K₀ / z
        ≤ |(fun z θ => Vs α Φs z θ * Gs α z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
      have h1 : K₀ * z ≤ |Vs α Φs z θ * Gs α z θ| := by
        rw [abs_mul]
        calc K₀ * z
            = (c₀ / 2) * ((α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3))
                / Work.Spaces.c α) * (z / 4)) := by rw [hK₀def]; ring
          _ ≤ |Vs α Φs z θ| * |Gs α z θ| :=
              mul_le_mul hVslow hGslow (by positivity) (abs_nonneg _)
      calc K₀ / z = (K₀ * z) * (1 / z ^ 2) := by field_simp
        _ ≤ |Vs α Φs z θ * Gs α z θ| * |Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| :=
            mul_le_mul h1 hw (by positivity) (abs_nonneg _)
        _ = |(fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
            simp only [abs_mul]
    have hsq : (K₀ / z) ^ 2
        ≤ ((fun z θ => Vs α Φs z θ * Gs α z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      refine sq_le_sq.mpr ?_
      rw [abs_of_pos (div_pos hK₀pos hz0)]
      exact hf
    rwa [div_pow] at hsq
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Set.Ioo a b).indicator (fun _ => K₀ ^ 2 / z ^ 2) θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => Vs α Φs z θ * Gs α z θ) z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
    · refine Eventually.of_forall fun θ => ?_
      by_cases h : θ ∈ Set.Ioo a b
      · rw [Set.indicator_of_mem h]; positivity
      · rw [Set.indicator_of_notMem h]; exact le_refl 0
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      by_cases h : θ ∈ Set.Ioo a b
      · rw [Set.indicator_of_mem h]
        exact le_trans (hpt θ h)
          (Work.Spaces.sq_le_HkIntegrand_z α 4
            (fun z θ => Vs α Φs z θ * Gs α z θ) z θ 0 (by norm_num))
      · rw [Set.indicator_of_notMem h]
        exact Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
  have hval : (∫ θ in Work.Spaces.Iθ,
        (Set.Ioo a b).indicator (fun _ => K₀ ^ 2 / z ^ 2) θ)
      = (b - a) * (K₀ ^ 2 / z ^ 2) := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    have hsub : Set.Ioo a b ⊆ Work.Spaces.Iθ := fun θ h =>
      ⟨le_of_lt (lt_trans ha0 h.1), le_of_lt (lt_trans h.2 hb)⟩
    rw [MeasureTheory.setIntegral_const]
    have hreal : (MeasureTheory.volume.restrict Work.Spaces.Iθ).real (Set.Ioo a b) = b - a := by
      rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr hsub, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    rw [hreal]
    ring
  rw [hval] at hstep
  simpa only [mul_div_assoc] using hstep

end HsZ

theorem HkSqZero {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (h0 : ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs 0 θ ≠ 0) :
    Work.Spaces.HkSq α 4
      (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
        * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) = 0 := by
  obtain ⟨c, δ, hcpos, hδpos, hclow⟩ :=
    HsZ.slice_lower_bound_Vs (α := α) (Cs := Cs) (Φs := Φs) hα hs h0
  have hnotint : ¬ MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) Work.Spaces.Iz := by
    intro hint
    have h1 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) (Set.Ioo 0 δ) :=
      hint.mono_set (fun z hz => le_of_lt hz.1)
    have h2 : MeasureTheory.IntegrableOn (fun z : ℝ => c / z ^ 2) (Set.Ioo 0 δ) := by
      refine MeasureTheory.Integrable.mono' h1 ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        exact continuousOn_const.div (continuousOn_id.pow 2)
          (fun z hz => pow_ne_zero 2 (ne_of_gt hz.1))
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
        have h0c : 0 ≤ c / z ^ 2 := by positivity
        have h0i : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (fun z θ => Vs α Φs z θ * Gs α z θ) z θ :=
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
        simpa only [Real.norm_of_nonneg h0c, Real.norm_of_nonneg h0i] using hclow z hz.1 hz.2
    have h3 : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-(2 : ℝ))) (Set.Ioo 0 δ) := by
      have h4 : MeasureTheory.IntegrableOn (fun z : ℝ => c⁻¹ * (c / z ^ 2))
          (Set.Ioo 0 δ) := h2.const_mul c⁻¹
      refine h4.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz.1)
      have hcz : c ≠ 0 := ne_of_gt hcpos
      show c⁻¹ * (c / z ^ 2) = z ^ (-(2 : ℝ))
      rw [Real.rpow_neg (le_of_lt hz.1) 2, Real.rpow_two, div_eq_mul_inv]
      field_simp
    have h5 : ¬ MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-(2 : ℝ)))
        (Set.Ioo 0 δ) := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hδpos]
      norm_num
    exact h5 h3
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.integral_undef hnotint

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Fb_EH_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The two shape identities of the `EH`-field

`EhC` is `EH` reassociated (`Y z θ / (z+1)` read as `Y z θ * (1+z)⁻¹`), and `EhD` is the
Leibniz expansion of `∂_θ(EH α Y)`. -/

/-- **`EhC` is `EH`**: a pure reassociation, valid at every point (no quadrant hypothesis). -/
theorem eh_EH_eq_EhC {α : ℝ} {Y : ℝ → ℝ → ℝ} :
    ∀ z θ : ℝ, Work.FTS.PhiStar.EH α Y z θ = EhC α Y z θ := by
  intro z θ
  simp only [Work.FTS.PhiStar.EH, EhC, Work.FTS.PhiStar.Tblk, Work.Construction.s2,
    EhSin2, EhPhi1, EhX, EhRhoInv, div_eq_mul_inv]
  ring

/-- **`EhD` is `∂_θ(EhC)` on the open quadrant**: the product rule for the four factors of
`EhC`, the coefficient derivatives `∂_θ(sin²θ) = sin 2θ` and `∂_θ(sin 2θ) = 2 cos 2θ`, the
vanishing `∂_θ(1+z)⁻¹ = 0` and the two structural identities
`∂_θ(z∂_zY) = z∂_z(∂_θY)` (`pth_zpz_smoothOpen`) and
`sin(2θ)·∂_θ(∂_θY) = D_θ(∂_θY)` (definitional). -/
theorem eh_pth_EhC_eq {α : ℝ} {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EhC α Y) z θ = EhD α Y z θ := by
  intro z θ hz hθ hθ'
  have sP : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 2 * Y z θ) :=
    SmoothOpen.const_mul hY 2
  have sQ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) :=
    SmoothOpen.const_mul (Fbq_smoothOpen_mul eh_smooth_ph1 (eh_smooth_EhX hY)) (2 * α)
  have sR : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
    Fbq_smoothOpen_mul eh_smooth_sin2 hY.pth
  have sQR : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) :=
    SmoothOpen.add sQ sR
  have sV : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => Y z θ * EhRhoInv z θ) :=
    Fbq_smoothOpen_mul hY eh_smooth_rhoinv
  have sU : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hY
  -- additivity
  have h1 : Work.Spaces.pth (EhC α Y) z θ
      = Work.Spaces.pth (fun z θ : ℝ => 2 * Y z θ) z θ
        + Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
            + EhSin2 z θ * Work.Spaces.pth Y z θ) z θ :=
    pth_add_Q0 (f := fun z θ : ℝ => 2 * Y z θ)
      (g := fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) sP sQR z θ hz hθ hθ'
  rw [h1]
  have h2 : Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)
        + EhSin2 z θ * Work.Spaces.pth Y z θ) z θ
      = Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) z θ
        + Work.Spaces.pth (fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) z θ :=
    pth_add_Q0 (f := fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ))
      (g := fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) sQ sR z θ hz hθ hθ'
  rw [h2]
  -- constant factors
  have h3 : Work.Spaces.pth (fun z θ : ℝ => 2 * Y z θ) z θ
      = 2 * Work.Spaces.pth Y z θ :=
    congrFun (congrFun (pth_const_mul (2 : ℝ) Y) z) θ
  rw [h3]
  have h4 : Work.Spaces.pth (fun z θ : ℝ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) z θ
      = (2 * α) * Work.Spaces.pth (fun z θ : ℝ => EhPhi1 z θ * EhX Y z θ) z θ :=
    congrFun (congrFun (pth_const_mul (2 * α)
      (fun z θ : ℝ => EhPhi1 z θ * EhX Y z θ)) z) θ
  rw [h4]
  -- the product rules
  have h5 : Work.Spaces.pth (fun z θ : ℝ => EhPhi1 z θ * EhX Y z θ) z θ
      = Work.Spaces.pth EhPhi1 z θ * EhX Y z θ
        + EhPhi1 z θ * Work.Spaces.pth (EhX Y) z θ :=
    Fbq_pth_mul eh_smooth_ph1 (eh_smooth_EhX hY) z θ hz hθ hθ'
  rw [h5]
  have h6 : Work.Spaces.pth (EhX Y) z θ
      = Work.Spaces.pth (fun z θ : ℝ => Y z θ * EhRhoInv z θ) z θ
        + Work.Spaces.pth (Yblk Y) z θ :=
    pth_add_Q0 (f := fun z θ : ℝ => Y z θ * EhRhoInv z θ) (g := Yblk Y) sV sU
      z θ hz hθ hθ'
  rw [h6]
  have h7 : Work.Spaces.pth (fun z θ : ℝ => Y z θ * EhRhoInv z θ) z θ
      = Work.Spaces.pth Y z θ * EhRhoInv z θ := by
    rw [Fbq_pth_mul (f := Y) (g := EhRhoInv) hY eh_smooth_rhoinv z θ hz hθ hθ',
      eh_pth_rhoinv z θ, mul_zero, add_zero]
  rw [h7]
  have h8 : Work.Spaces.pth (Yblk Y) z θ = Yblk (Work.Spaces.pth Y) z θ :=
    pth_zpz_smoothOpen hY z θ hz hθ hθ'
  rw [h8]
  have h9 : Work.Spaces.pth (fun z θ : ℝ => EhSin2 z θ * Work.Spaces.pth Y z θ) z θ
      = Work.Spaces.pth EhSin2 z θ * Work.Spaces.pth Y z θ
        + EhSin2 z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ :=
    Fbq_pth_mul eh_smooth_sin2 hY.pth z θ hz hθ hθ'
  rw [h9]
  -- the two coefficient derivatives
  have h10 : Work.Spaces.pth EhPhi1 z θ = EhDSinSq z θ := by
    rw [eh_pth_ph1 z θ, eh_sin2_eq_dsinsq z θ]
  rw [h10]
  have h11 : Work.Spaces.pth EhSin2 z θ = EhDSin2 z θ := eh_pth_sin2 z θ
  rw [h11]
  -- compare with `EhD`
  simp only [EhD, EhDX, Work.Spaces.Dth, EhSin2] <;> ring

/-! ## The bookkeeping of the powers of `A`

Every constant produced below is a monomial `c·A^j·(K+1)` or `c·α·A^j·(K+1)` with `j ≤ 4` and
a universal coefficient `c ≤ 4096`; these two lemmas turn each of them into the final
constant `4096·A⁴(K+1)(α+1)`. -/



/-! ## The intermediate constants -/





/-! ## The main theorem -/


end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.JepsSubPointwise =====
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

open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps)

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {g W : ℝ → ℝ → ℝ}

/-! ## The shift path -/

/-- The point reached from `(z,θ)` after the fraction `t` of the log-coordinate shift by `p`:
`(z e^{-t p₁}, arctan (tan θ e^{-t p₂}))`. -/
def shiftPt (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (zShift z (t * p.1), thShift θ (t * p.2))

theorem shiftPt_mem_Quad {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ)
    (t : ℝ) : shiftPt z θ p t ∈ Quad :=
  ⟨zShift_pos hz, thShift_mem hθ⟩

theorem continuous_shiftPt (z θ : ℝ) :
    Continuous fun q : (ℝ × ℝ) × ℝ => shiftPt z θ q.1 q.2 := by
  refine Continuous.prodMk ?_ ?_
  · show Continuous fun q : (ℝ × ℝ) × ℝ => z * Real.exp (-(q.2 * q.1.1))
    fun_prop
  · show Continuous fun q : (ℝ × ℝ) × ℝ =>
      Real.arctan (Real.tan θ * Real.exp (-(q.2 * q.1.2)))
    fun_prop

theorem continuous_shiftPt_slice (z θ : ℝ) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => shiftPt z θ p t := by
  refine Continuous.prodMk ?_ ?_
  · show Continuous fun t : ℝ => z * Real.exp (-(t * p.1))
    fun_prop
  · show Continuous fun t : ℝ => Real.arctan (Real.tan θ * Real.exp (-(t * p.2)))
    fun_prop

/-- The composed slice `t ↦ A (shiftPt z θ p t)` is continuous for `A` continuous on `Quad`. -/
theorem continuous_shiftPt_comp {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => A (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
  hA.comp_continuous (continuous_shiftPt_slice z θ p) (fun t => shiftPt_mem_Quad hz hθ p t)

/-- The composed function `(p,t) ↦ A (shiftPt z θ p t)` is continuous for `A` continuous on
`Quad`. -/
theorem continuous_shiftPt_comp_joint {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Continuous fun q : (ℝ × ℝ) × ℝ =>
      A (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
  hA.comp_continuous (continuous_shiftPt z θ) (fun q => shiftPt_mem_Quad hz hθ q.1 q.2)

/-! ## The two integrands -/

/-- The directional derivative of the shift path: `-(p₁ D_z g + (p₂/2) D_θ g)`. -/
def pathDeriv (g : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ :=
  -(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
    + p.2 / 2 * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))

/-- The bracket of the difference estimate at the shifted point. -/
def bracket (g W : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ :=
  (W (zShift z (t * p.1)) (thShift θ (t * p.2))
      * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2
    + 1 / 4 * (W (zShift z (t * p.1)) (thShift θ (t * p.2))
      * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2

theorem bracket_nonneg (g W : ℝ → ℝ → ℝ) (z θ : ℝ) (p : ℝ × ℝ) (t : ℝ) :
    0 ≤ bracket g W z θ p t := by
  rw [bracket]; positivity

theorem continuous_pathDeriv_joint {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun q : (ℝ × ℝ) × ℝ => pathDeriv g z θ q.1 q.2 := by
  have h1 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      Work.Spaces.Dz g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    continuous_shiftPt_comp_joint hDz hz hθ
  have h2 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      Work.Spaces.Dth g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    continuous_shiftPt_comp_joint hDth hz hθ
  have h3 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      q.1.1 * Work.Spaces.Dz g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    continuous_fst.fst.mul h1
  have h4 : Continuous fun q : (ℝ × ℝ) × ℝ =>
      q.1.2 / 2 * Work.Spaces.Dth g (zShift z (q.2 * q.1.1)) (thShift θ (q.2 * q.1.2)) :=
    (continuous_fst.snd.div_const 2).mul h2
  exact (h3.add h4).neg

theorem continuous_pathDeriv_slice {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => pathDeriv g z θ p t := by
  have h1 : Continuous fun t : ℝ =>
      Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    continuous_shiftPt_comp hDz hz hθ p
  have h2 : Continuous fun t : ℝ =>
      Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    continuous_shiftPt_comp hDth hz hθ p
  have h3 : Continuous fun t : ℝ =>
      p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    continuous_const.mul h1
  have h4 : Continuous fun t : ℝ =>
      p.2 / 2 * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
    (continuous_const.div_const 2).mul h2
  exact (h3.add h4).neg

theorem continuous_bracket_slice {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) (p : ℝ × ℝ) :
    Continuous fun t : ℝ => bracket g W z θ p t := by
  have h1 := continuous_shiftPt_comp (A := fun u v => W u v * Work.Spaces.Dz g u v)
    (hWc.mul hDz) hz hθ p
  have h2 := continuous_shiftPt_comp (A := fun u v => W u v * Work.Spaces.Dth g u v)
    (hWc.mul hDth) hz hθ p
  have h := (h1.pow 2).add
    ((continuous_const : Continuous fun _ : ℝ => (1 / 4 : ℝ)).mul (h2.pow 2))
  refine h.congr fun t => ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, bracket]

theorem continuous_bracket_joint {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun q : (ℝ × ℝ) × ℝ => bracket g W z θ q.1 q.2 := by
  have h1 := continuous_shiftPt_comp_joint (A := fun u v => W u v * Work.Spaces.Dz g u v)
    (hWc.mul hDz) hz hθ
  have h2 := continuous_shiftPt_comp_joint (A := fun u v => W u v * Work.Spaces.Dth g u v)
    (hWc.mul hDth) hz hθ
  have h := (h1.pow 2).add
    ((continuous_const : Continuous fun _ : (ℝ × ℝ) × ℝ => (1 / 4 : ℝ)).mul (h2.pow 2))
  refine h.congr fun q => ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, bracket]

/-! ## Cauchy–Schwarz for the unit interval -/

theorem sq_intervalIntegral_le {X : ℝ → ℝ} (hX : ContinuousOn X (Set.Icc 0 1)) :
    (∫ t in (0 : ℝ)..1, X t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (X t) ^ 2 := by
  set m : ℝ := ∫ t in (0 : ℝ)..1, X t with hm
  have hX' : ContinuousOn X (Set.uIcc (0 : ℝ) 1) := by
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hXint : IntervalIntegrable X volume 0 1 := hX'.intervalIntegrable
  have hX2' : ContinuousOn (fun t => X t ^ 2) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hX.pow 2
  have hX2int : IntervalIntegrable (fun t => X t ^ 2) volume 0 1 := hX2'.intervalIntegrable
  have h2m : IntervalIntegrable (fun t => 2 * m * X t) volume 0 1 := hXint.const_mul (2 * m)
  have hconst : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume 0 1 := intervalIntegrable_const
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, (X t - m) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have hcongr : (∫ t in (0 : ℝ)..1, (X t - m) ^ 2)
      = ∫ t in (0 : ℝ)..1, (X t ^ 2 - 2 * m * X t + m ^ 2) :=
    intervalIntegral.integral_congr (fun t _ => by ring)
  have hcalc : (∫ t in (0 : ℝ)..1, (X t ^ 2 - 2 * m * X t + m ^ 2))
      = (∫ t in (0 : ℝ)..1, X t ^ 2) - m ^ 2 := by
    rw [intervalIntegral.integral_add (hX2int.sub h2m) hconst,
      intervalIntegral.integral_sub hX2int h2m,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, hm]
    simp only [smul_eq_mul]
    ring
  linarith [hnn, hcongr, hcalc]

/-! ## Continuity of the parametric integrals -/

/-- **Continuity of the parametric interval integral on a ball.**  If `F` is jointly continuous and
bounded by `C` on `closedBall 0 ε × [0,1]`, then `p ↦ ∫_0^1 F p t dt` is continuous on that
ball. -/
theorem continuous_integral_pathDeriv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t := by
  have hcont := continuous_pathDeriv_joint hz hθ hDz hDth
  have h1 : Continuous fun p : ℝ × ℝ => ∫ t in Set.Icc (0 : ℝ) 1, pathDeriv g z θ p t :=
    continuous_parametric_integral_of_continuous (μ := volume) hcont isCompact_Icc
  refine h1.congr fun p => ?_
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := 1))).symm

theorem continuous_integral_bracket {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad) :
    Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
  have hcont := continuous_bracket_joint hz hθ hWc hDz hDth
  have h1 : Continuous fun p : ℝ × ℝ => ∫ t in Set.Icc (0 : ℝ) 1, bracket g W z θ p t :=
    continuous_parametric_integral_of_continuous (μ := volume) hcont isCompact_Icc
  refine h1.congr fun p => ?_
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := 1))).symm

/-! ## The pointwise estimate -/

theorem Jeps_sub_sq_le (hρ : IsMollKernel ρ) (hε : 0 < ε) {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hWnn : 0 ≤ W z θ)
    (hW : ∀ q : ℝ × ℝ, W z θ ≤ Real.exp (c * (|q.1| + |q.2|))
      * W (zShift z q.1) (thShift θ q.2)) :
    (W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2
      ≤ 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ p : ℝ × ℝ, Jker ρ ε p
          * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
  have hAcont : Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t :=
    continuous_integral_pathDeriv hz hθ hDz hDth
  have hbcont : Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, bracket g W z θ p t :=
    continuous_integral_bracket hz hθ hWc hDz hDth
  -- the mass-one identity and the fundamental theorem of calculus
  have hsub := Jeps_sub_eq_integral ρ hρ hε (hg 0).continuousOn hz hθ
  have hWsub : W z θ * (Jeps ρ ε g z θ - g z θ)
      = ∫ p : ℝ × ℝ, Jker ρ ε p
          * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) := by
    rw [hsub, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    show W z θ * (Jker ρ ε p * (g (zShift z p.1) (thShift θ p.2) - g z θ))
      = Jker ρ ε p * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t)
    rw [shiftPath_sub hg hz hθ p]
    rw [show (∫ t in (0 : ℝ)..1,
          (-(p.1 * Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))
            + (p.2 / 2) * Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)))))
        = ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t from by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [pathDeriv]]
    ring
  -- Cauchy–Schwarz in the kernel
  have hCS := Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le ρ hρ hε
    (fun p : ℝ × ℝ => W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t)
    ((hAcont.const_mul (W z θ)).continuousOn)
  -- the pointwise bound in `p`
  have hpoint : ∀ p : ℝ × ℝ, Jker ρ ε p
        * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2
      ≤ Jker ρ ε p * (2 * ε ^ 2 * Real.exp (4 * c * ε)
          * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) := by
    intro p
    by_cases hp : Jker ρ ε p = 0
    · rw [hp, zero_mul, zero_mul]
    · have hb := Jker_ne_zero_support hρ hε hp
      have hp1 : |p.1| ≤ ε := by
        have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
        rw [sq_le_sq] at h1
        rwa [abs_of_nonneg hε.le] at h1
      have hp2 : |p.2| ≤ ε := by
        have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
        rw [sq_le_sq] at h2
        rwa [abs_of_nonneg hε.le] at h2
      have htcs := sq_intervalIntegral_le (continuous_pathDeriv_slice hz hθ hDz hDth p).continuousOn
      have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (W z θ) ^ 2 * (pathDeriv g z θ p t) ^ 2
            ≤ 2 * ε ^ 2 * Real.exp (4 * c * ε) * bracket g W z θ p t := by
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have htabs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
        have hWsn : 0 ≤ W (zShift z (t * p.1)) (thShift θ (t * p.2)) := by
          have hsh := hW (t * p.1, t * p.2)
          have hpos : 0 < Real.exp (c * (|t * p.1| + |t * p.2|)) := Real.exp_pos _
          nlinarith [hsh, hWnn, hpos]
        have hexp : Real.exp (c * (|t * p.1| + |t * p.2|)) ≤ Real.exp (2 * c * ε) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : |t * p.1| ≤ ε := by
            rw [abs_mul]
            exact (mul_le_mul htabs hp1 (abs_nonneg _) (by norm_num)).trans_eq (one_mul ε)
          have h2 : |t * p.2| ≤ ε := by
            rw [abs_mul]
            exact (mul_le_mul htabs hp2 (abs_nonneg _) (by norm_num)).trans_eq (one_mul ε)
          nlinarith
        have hWsq : (W z θ) ^ 2 ≤ Real.exp (4 * c * ε)
            * (W (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2 := by
          have h1 : W z θ ≤ Real.exp (2 * c * ε)
              * W (zShift z (t * p.1)) (thShift θ (t * p.2)) :=
            (hW (t * p.1, t * p.2)).trans
              (mul_le_mul_of_nonneg_right hexp hWsn)
          have h2 := pow_le_pow_left₀ hWnn h1 2
          rw [mul_pow] at h2
          have hexp4 : Real.exp (2 * c * ε) ^ 2 = Real.exp (4 * c * ε) := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          rwa [hexp4] at h2
        have hpd : (pathDeriv g z θ p t) ^ 2 ≤ 2 * ε ^ 2
            * ((Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2
              + 1 / 4 * (Work.Spaces.Dth g (zShift z (t * p.1))
                  (thShift θ (t * p.2))) ^ 2) := by
          set X := Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2)) with hX
          set Y := Work.Spaces.Dth g (zShift z (t * p.1)) (thShift θ (t * p.2)) with hY
          have h1 : (p.1 * X + p.2 / 2 * Y) ^ 2 ≤ 2 * p.1 ^ 2 * X ^ 2
              + 2 * (p.2 / 2) ^ 2 * Y ^ 2 := by
            nlinarith [sq_nonneg (p.1 * X - p.2 / 2 * Y)]
          have h2 : p.1 ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hp1 2
          have h3 : p.2 ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hp2 2
          have h4 : 2 * p.1 ^ 2 * X ^ 2 + 2 * (p.2 / 2) ^ 2 * Y ^ 2
              ≤ 2 * ε ^ 2 * (X ^ 2 + 1 / 4 * Y ^ 2) := by
            nlinarith [sq_nonneg X, sq_nonneg Y, sq_nonneg ε]
          rw [pathDeriv]
          calc (-(p.1 * X + p.2 / 2 * Y)) ^ 2 = (p.1 * X + p.2 / 2 * Y) ^ 2 := by ring
            _ ≤ 2 * p.1 ^ 2 * X ^ 2 + 2 * (p.2 / 2) ^ 2 * Y ^ 2 := h1
            _ ≤ 2 * ε ^ 2 * (X ^ 2 + 1 / 4 * Y ^ 2) := h4
        calc (W z θ) ^ 2 * (pathDeriv g z θ p t) ^ 2
            ≤ (Real.exp (4 * c * ε) * (W (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2)
              * (2 * ε ^ 2 * ((Work.Spaces.Dz g (zShift z (t * p.1)) (thShift θ (t * p.2))) ^ 2
                + 1 / 4 * (Work.Spaces.Dth g (zShift z (t * p.1))
                    (thShift θ (t * p.2))) ^ 2)) :=
              mul_le_mul hWsq hpd (sq_nonneg _) (by positivity)
            _ = 2 * ε ^ 2 * Real.exp (4 * c * ε) * bracket g W z θ p t := by
              rw [bracket]; ring
      have hWnnsq : (0 : ℝ) ≤ (W z θ) ^ 2 := sq_nonneg _
      have hmain : (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2
          ≤ 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
       calc (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2
          = (W z θ) ^ 2 * (∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2 := by ring
        _ ≤ (W z θ) ^ 2 * ∫ t in (0 : ℝ)..1, (pathDeriv g z θ p t) ^ 2 :=
            mul_le_mul_of_nonneg_left htcs hWnnsq
        _ = ∫ t in (0 : ℝ)..1, (W z θ) ^ 2 * (pathDeriv g z θ p t) ^ 2 := by
            rw [intervalIntegral.integral_const_mul]
        _ ≤ ∫ t in (0 : ℝ)..1, 2 * ε ^ 2 * Real.exp (4 * c * ε) * bracket g W z θ p t := by
            rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
              intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
            refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc
              (fun t ht => hpt t (Set.Ioc_subset_Icc_self ht))
            · exact (((continuous_pathDeriv_slice hz hθ hDz hDth p).pow 2).continuousOn
                |>.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self |>.const_mul _
            · exact (((continuous_bracket_slice hz hθ hWc hDz hDth p).continuousOn
                |>.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
                |>.const_mul _)
        _ = 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
            rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hmain (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)
  -- the two integrals are integrable
  have hint1 : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2) :=
    Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε
      (((hAcont.const_mul (W z θ)).continuousOn).pow 2)
  have hint2 : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * (2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ t in (0 : ℝ)..1, bracket g W z θ p t)) :=
    Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε (hbcont.const_mul _).continuousOn
  calc (W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2
      = (∫ p : ℝ × ℝ, Jker ρ ε p
          * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t)) ^ 2 := by rw [hWsub]
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p
          * (W z θ * ∫ t in (0 : ℝ)..1, pathDeriv g z θ p t) ^ 2 := hCS
    _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p
          * (2 * ε ^ 2 * Real.exp (4 * c * ε)
            * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
        MeasureTheory.integral_mono hint1 hint2 hpoint
    _ = 2 * ε ^ 2 * Real.exp (4 * c * ε) * ∫ p : ℝ × ℝ, Jker ρ ε p
          * ∫ t in (0 : ℝ)..1, bracket g W z θ p t := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring

/-! ## The `ℝ≥0∞` form -/

theorem ofReal_intervalIntegral {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hnn : ∀ t, 0 ≤ f t) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, f t)
      = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (f t) := by
  have hint : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume := hf.integrableOn_compact isCompact_Icc
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (hint.mono_set Set.Ioc_subset_Icc_self) (Eventually.of_forall hnn)]
  rw [← Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := 1))]

/-- **The `ℝ≥0∞` pointwise bound.** -/
theorem ofReal_Jeps_sub_sq_le (hρ : IsMollKernel ρ) (hε : 0 < ε) {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hWnn : 0 ≤ W z θ)
    (hW : ∀ q : ℝ × ℝ, W z θ ≤ Real.exp (c * (|q.1| + |q.2|))
      * W (zShift z q.1) (thShift θ q.2)) :
    ENNReal.ofReal ((W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2)
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t) := by
  have hreal := Jeps_sub_sq_le hρ hε hc hg hWc hDz hDth hz hθ hWnn hW
  have hbcont : Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, bracket g W z θ p t :=
    continuous_integral_bracket hz hθ hWc hDz hDth
  have hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
    Work.FTS.StrongEps.HkSqAux.integrable_Jker_mul ρ hρ hε hbcont.continuousOn
  have hnnG : ∀ p : ℝ × ℝ, 0 ≤ ∫ t in (0 : ℝ)..1, bracket g W z θ p t := fun p =>
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => bracket_nonneg g W z θ p t)
  have hconv : ENNReal.ofReal (∫ p : ℝ × ℝ, Jker ρ ε p
        * ∫ t in (0 : ℝ)..1, bracket g W z θ p t)
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
          * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p =>
        mul_nonneg (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p) (hnnG p))]
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ ε p)]
    congr 1
    exact ofReal_intervalIntegral ((continuous_bracket_slice hz hθ hWc hDz hDth p).continuousOn)
      (fun t => bracket_nonneg g W z θ p t)
  calc ENNReal.ofReal ((W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2)
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε)
          * ∫ p : ℝ × ℝ, Jker ρ ε p * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * ENNReal.ofReal (∫ p : ℝ × ℝ, Jker ρ ε p
              * ∫ t in (0 : ℝ)..1, bracket g W z θ p t) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
              * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t)) := by
        rw [hconv]

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.Shadow =====
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

/-- A sum of squares over a sub-family of the level-`k+1` mixed slots is dominated by the whole
level-`k+1` mixed part. -/
theorem sum_image_le_HkMPartF {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ} {ι : Type*}
    (s : Finset ι) (e : ι → ℕ × ℕ)
    (he : ∀ i ∈ s, e i ∈ slots (k + 1))
    (hinj : ∀ i ∈ s, ∀ j ∈ s, e i = e j → i = j) :
    (∑ i ∈ s, (Work.Spaces.mixed (e i).2 (e i).1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ := by
  have hkey : (∑ i ∈ s, (Work.Spaces.mixed (e i).2 (e i).1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = ∑ q ∈ s.image e,
          (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    (Finset.sum_image (f := fun q : ℕ × ℕ =>
        (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2) (g := e) hinj).symm
  rw [hkey, HkMPartF_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => sq_nonneg _
  intro q hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  exact he i hi

/-- A sum of squares over a sub-family of the level-`k+1` pure `D_z`-slots is dominated by the
whole level-`k+1` `D_z`-part. -/
theorem sum_image_le_HkZPart {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (e : ℕ → ℕ) (he : ∀ i ∈ Finset.range (k + 1), e i ∈ Finset.range (k + 2))
    (hinj : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1), e i = e j → i = j) :
    (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (e i) f z θ * wE z θ) ^ 2)
      ≤ HkSqAux.HkZPart (k + 1) f z θ := by
  have hkey : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter (e i) f z θ * wE z θ) ^ 2)
      = ∑ m ∈ (Finset.range (k + 1)).image e,
          (Work.Spaces.DzIter m f z θ * wE z θ) ^ 2 :=
    (Finset.sum_image (f := fun m : ℕ => (Work.Spaces.DzIter m f z θ * wE z θ) ^ 2)
      (g := e) hinj).symm
  rw [hkey, HkZPart_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => sq_nonneg _
  intro m hm
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
  exact he i hi

/-- **The shadow bound.**  The level-`k+1` shadow of the level-`k` slot sum of `J_ε f - f` is at
most twice the level-`k+1` integrand. -/
theorem shadow_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    shadow α k f z θ ≤ 2 * Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * wE z θ) ^ 2)
      ≤ HkSqAux.HkZPart (k + 1) f z θ :=
    sum_image_le_HkZPart (k := k) (f := f) (z := z) (θ := θ) (fun i => i + 1)
      (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
      (fun i _ j _ h => by omega)
  have h2 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.mixed i 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ :=
    sum_image_le_HkMPartF (k := k) (f := f) (z := z) (θ := θ) (s := Finset.range (k + 1))
      (e := fun i => (1, i)) (fun i hi => by
        rw [mem_slots]; simp only [Finset.mem_range] at hi; omega)
      (fun i _ j _ h => by simpa using congrArg Prod.snd h)
  have h3 : (∑ q ∈ slots k, (Work.Spaces.mixed (q.2 + 1) q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ :=
    sum_image_le_HkMPartF (k := k) (f := f) (z := z) (θ := θ) (s := slots k)
      (e := fun q => (q.1, q.2 + 1)) (fun q hq => by
        rw [mem_slots] at hq ⊢; omega)
      (fun i hi j hj h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (by omega))
  have h4 : (∑ q ∈ slots k, (Work.Spaces.mixed q.2 (q.1 + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ :=
    sum_image_le_HkMPartF (k := k) (f := f) (z := z) (θ := θ) (s := slots k)
      (e := fun q => (q.1 + 1, q.2)) (fun q hq => by
        rw [mem_slots] at hq ⊢; omega)
      (fun i hi j hj h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (by omega) h.2)
  have hZnn : 0 ≤ HkSqAux.HkZPart (k + 1) f z θ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMnn : 0 ≤ HkSqAux.HkMPartF α (k + 1) f z θ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hparts : Work.Spaces.HkIntegrand α (k + 1) f z θ
      = HkSqAux.HkZPart (k + 1) f z θ + HkSqAux.HkMPartF α (k + 1) f z θ := by
    rw [HkSqAux.HkIntegrand_eq_parts, HkSqAux.HkMPart_eq_HkMPartF]
  rw [hparts, shadow]
  nlinarith [h1, h2, h3, h4, hZnn, hMnn]

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSFinal =====
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

/-- **The level-`n` weighted slot sum of `radS α f`**, in the open class.

For a datum `f` which is `C^∞` on the open quadrant, honest in `ℋ⁵` and whose zero mode
vanishes, the sum of the weighted squares of the `D_z`-iterates of `radS α f` up to order
`n ≤ 3` is integrable and bounded by a multiple of `|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ}`, uniformly in
`α ∈ (0,1]`, `n ≤ 3` and `f`.

The single input on the projector zero mode `C₀ = L₁₂(Transport f)(0)` is the hypothesis
`hC0`. -/
theorem radS_slotSum_le_O
    (hC0 : ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ C * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨KA, hKAnn, hKAbd⟩ :=
    Work.FTS.CoercivityFix.Transfer.E2norm.ampA_dzdIter_bound_uniform
  obtain ⟨KB, hKBnn, hKB⟩ :=
    Work.FTS.CoercivityFix.Transfer.E2norm.ampB_DzdIter_sq_w_sq_le
  obtain ⟨K, hKnn, hKbound⟩ := hC0
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongEps.EpsE4Thr.E1Open.L12f_slot_le_O_of
    (CQ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
    (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
    (fun β m g hβ hβ1 hO hmem i hi =>
      Work.FTS.StrongEps.EpsE4Thr.E1Open.Qang_sq_w_sq_le_HkSq_O m β g hβ hβ1 hO hmem i hi)
  refine ⟨3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      + 400 * KB * K) + 1, by positivity, ?_⟩
  intro α hα hα1 n hn f hO hmem5 hl12
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO n (by omega) hmem5
  -- the angular-moment slot bounds at level `n`
  have hQ : ∀ i ≤ n, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f :=
    fun i hi =>
      Work.FTS.StrongEps.EpsE4Thr.E1Open.Qang_sq_w_sq_le_HkSq_O n α f hα hα1 hO hmemn i hi
  -- the `L₁₂` slot-sum bound at level `n`
  have hL := hCL α ⟨hα, hα1⟩ f hO hmem4 hl12 n hn
  -- the `ampB` slot bounds
  have hB : ∀ j ∈ Finset.range (n + 1), MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter (j + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun j hj => (hKB α hα hα1 (j + 1) (by have := Finset.mem_range.mp hj; omega)).1
  have hBb : ∀ j ∈ Finset.range (n + 1),
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter (j + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) ≤ KB :=
    fun j hj => (hKB α hα hα1 (j + 1) (by have := Finset.mem_range.mp hj; omega)).2
  -- the `α`-uniform Kato bound on the `ampA`-iterates
  have hKbd : ∀ b ≤ 4, ∀ z ∈ IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ KA :=
    fun b hb z hz => hKAbd α hα hα1 b hb z hz
  -- the projector zero-mode bound at level `n`
  have hKC : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f) := hKbound α hα hα1 n hn f hO hmem5 hl12
  have hKA2 : 0 ≤ KA ^ 2 := sq_nonneg KA
  -- integrability of the three block sums
  have hLSumInt : MeasureTheory.IntegrableOn (LSlotSum n f) Work.Spaces.Iz := hL.1
  have hQSumInt : MeasureTheory.IntegrableOn (QSlotSum n f) Work.Spaces.Iz := by
    change MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (n + 1),
      (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
    exact MeasureTheory.integrable_finsetSum _
      (fun i hi => (hQ i (by have := Finset.mem_range.mp hi; omega)).1)
  have hBSumInt : MeasureTheory.IntegrableOn (BSlotSum n α) Work.Spaces.Iz := by
    change MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
    exact MeasureTheory.integrable_finsetSum _ (fun i hi => hB i hi)
  -- integrals of the three block sums
  have hIL : (∫ z in Work.Spaces.Iz, LSlotSum n f z) ≤ CL * Work.Spaces.HkSq α n f := hL.2
  have hIQ : (∫ z in Work.Spaces.Iz, QSlotSum n f z)
      ≤ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f) := by
    change (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ _
    rw [MeasureTheory.integral_finsetSum _
      (fun i hi => (hQ i (by have := Finset.mem_range.mp hi; omega)).1)]
    have h1 : (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1),
            (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f :=
      Finset.sum_le_sum (fun i hi => (hQ i (by have := Finset.mem_range.mp hi; omega)).2)
    have h2 : (∑ _i ∈ Finset.range (n + 1),
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f)
        = ((n : ℝ) + 1) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have h3 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    have h4 : 0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * Work.Spaces.HkSq α n f :=
      mul_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
        (Work.Spaces.HkSq_nonneg α n f)
    calc (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1),
            (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := h1
      _ = ((n : ℝ) + 1) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f) := h2
      _ ≤ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f) := mul_le_mul_of_nonneg_right h3 h4
  have hIB : (∫ z in Work.Spaces.Iz, BSlotSum n α z) ≤ 4 * KB := by
    change (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ _
    rw [MeasureTheory.integral_finsetSum _ (fun i hi => hB i hi)]
    have h1 : (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ ∑ _i ∈ Finset.range (n + 1), KB :=
      Finset.sum_le_sum (fun i hi => hBb i hi)
    have h2 : (∑ _i ∈ Finset.range (n + 1), KB) = ((n : ℝ) + 1) * KB := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have h3 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    calc (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1), KB := h1
      _ = ((n : ℝ) + 1) * KB := h2
      _ ≤ 4 * KB := mul_le_mul_of_nonneg_right h3 hKBnn
  -- ## the pointwise bound
  have hpt := radS_sum_le (n := n) α hα hα1 hn hO hmem5 hl12 hKAnn hKbd
  -- ## integrability of the slot sum
  have hRHSInt : MeasureTheory.IntegrableOn (fun z : ℝ =>
      3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
        + SConst α f * BSlotSum n α z)) Work.Spaces.Iz :=
    (((hLSumInt.const_mul (KA ^ 2)).add (hQSumInt.const_mul (KA ^ 2))).add
      (hBSumInt.const_mul (SConst α f))).const_mul 3084
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hA : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) IoiA :=
      contDiffOn_four_L12f α hα hα1 hO hmem5
    have hsmR : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radS α f) IoiA :=
      Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1 hA
    have hcont : ContinuousOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) IoiA := by
      refine continuousOn_finsetSum _ (fun j hj => ?_)
      have hj3 : j ≤ 3 := by have := Finset.mem_range.mp hj; omega
      have hj1 : ContinuousOn (fun z : ℝ =>
          Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) IoiA := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
        exact Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
          (b := j) (n := 0) (hu := hsmR.of_le (Nat.cast_le.mpr hj3))
      have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) IoiA := by
        have hfun : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
        rw [hfun]
        exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
      exact (hj1.pow 2).mul hw2
    exact Work.H2.T1Q.aesm_Iz_of_continuousOn hcont
  have hint : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine Integrable.mono' hRHSInt haesm ?_
    filter_upwards [hpt] with z hz
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hz
  refine ⟨hint, ?_⟩
  -- ## the integral bound
  have hmono : (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz,
          3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
            + SConst α f * BSlotSum n α z) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun j _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) hRHSInt ?_
    filter_upwards [hpt] with z hz
    exact hz
  refine le_trans hmono ?_
  have hlin : (∫ z in Work.Spaces.Iz,
        3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z))
      = 3084 * (KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
          + KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
          + SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z)) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add
      (f := fun x : ℝ => KA ^ 2 * LSlotSum n f x + KA ^ 2 * QSlotSum n f x)
      (g := fun x : ℝ => SConst α f * BSlotSum n α x)
      ((hLSumInt.const_mul (KA ^ 2)).add (hQSumInt.const_mul (KA ^ 2)))
      (hBSumInt.const_mul (SConst α f))]
    rw [MeasureTheory.integral_add (f := fun x : ℝ => KA ^ 2 * LSlotSum n f x)
      (g := fun x : ℝ => KA ^ 2 * QSlotSum n f x) (hLSumInt.const_mul (KA ^ 2))
      (hQSumInt.const_mul (KA ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hlin]
  -- ## the final arithmetic
  have hHnn : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hH'nn : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
  have hSle : SConst α f ≤ 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    rw [SConst]
    have hc := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hcsq : (1 : ℝ) / 100 ≤ (Work.Spaces.c α) ^ 2 := by nlinarith [hc, hcpos]
    have hinv : ((Work.Spaces.c α) ^ 2)⁻¹ ≤ 100 := by
      rw [inv_eq_one_div, div_le_iff₀ (pow_pos hcpos 2)]
      nlinarith [hcsq]
    calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
            * ((Work.Spaces.c α) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ ≤ (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2 * 100 :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ ≤ (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * 100 :=
          mul_le_mul_of_nonneg_right hKC (by norm_num)
      _ = 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hIBSnn : 0 ≤ (∫ z in Work.Spaces.Iz, BSlotSum n α z) := by
    change 0 ≤ ∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2
    exact MeasureTheory.integral_nonneg fun z => Finset.sum_nonneg fun i _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hT1 : KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
      ≤ KA ^ 2 * (CL * Work.Spaces.HkSq α n f) :=
    mul_le_mul_of_nonneg_left hIL hKA2
  have hT2 : KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
      ≤ KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α n f)) := mul_le_mul_of_nonneg_left hIQ hKA2
  have hT3 : SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z)
      ≤ 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB) :=
    mul_le_mul hSle hIB hIBSnn (by positivity)
  have hYnn : 0 ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
    linarith
  -- the three blocks, each bounded by the target
  have hE1 : 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
      ≤ (3084 * (KA ^ 2 * CL)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hX : (0 : ℝ) ≤ 3084 * (KA ^ 2 * CL) :=
      mul_nonneg (by norm_num) (mul_nonneg hKA2 hCLpos.le)
    have h := mul_le_mul_of_nonneg_left (show Work.Spaces.HkSq α n f
        ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) by linarith) hX
    calc 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
        = (3084 * (KA ^ 2 * CL)) * Work.Spaces.HkSq α n f := by ring
      _ ≤ (3084 * (KA ^ 2 * CL)) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := h
  have hE2 : 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α n f)))
      ≤ (3084 * (4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hX : 0 ≤ 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) := by positivity
    have h := mul_le_mul_of_nonneg_left (show Work.Spaces.HkSq α n f
        ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) by linarith) hX
    calc 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f)))
        = 3084 * ((4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2))
            * Work.Spaces.HkSq α n f) := by ring
      _ ≤ 3084 * ((4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2))
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hE3 : 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
      ≤ (3084 * (400 * KB * K)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hX : 0 ≤ 400 * KB * K := by positivity
    have h := mul_le_mul_of_nonneg_left (show Work.Spaces.HkSq α n (Work.Spaces.Dth f)
        ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) by linarith) hX
    calc 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
        = 3084 * ((400 * KB * K) * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
      _ ≤ 3084 * ((400 * KB * K) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (3084 * (400 * KB * K)) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hcomb : (3084 * (KA ^ 2 * CL)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        + (3084 * (4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        + (3084 * (400 * KB * K)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      = 3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          + 400 * KB * K) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hmain : 3084 * (KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
        + KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
        + SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z))
      ≤ 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f)
        + KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f))
        + 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB)) := by
    have h1 : KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
          + KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
          + SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z)
        ≤ KA ^ 2 * (CL * Work.Spaces.HkSq α n f)
          + KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α n f))
          + 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB) := by
      linarith [hT1, hT2, hT3]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hsplit : 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f)
        + KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f))
        + 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
      = 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
        + 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f)))
        + 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB)) := by ring
  have hbig : 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
        + 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f)))
        + 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
      ≤ 3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          + 400 * KB * K) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    linarith [hE1, hE2, hE3, hcomb]
  have hTgt : 3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        + 400 * KB * K) * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      ≤ (3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          + 400 * KB * K) + 1) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h1 : 3084 * (KA ^ 2 * CL
          + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 400 * KB * K)
        ≤ 3084 * (KA ^ 2 * CL
          + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 400 * KB * K)
          + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h1 hYnn
  linarith [hmain, hsplit, hbig, hTgt]

end Work.FTS.StrongEps.EpsE4Thr.E2O
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsStructP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The regularity class of the `P₀`-scheme's data**: `C^∞` on the open quadrant, honest `ℋ⁶`,
and *the projected mollified profile in class C* — the conjunct that the `P₀` repair makes true. -/
def EpsDatumP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (h : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen h ∧ Work.Spaces.HkMem α 6 h ∧
    Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε h))

/-- The un-projected datum data imply nothing by themselves about the projection; the point of
`EpsDatumP` is exactly that its class-`C` conjunct is the *projected* one.  This lemma records the
trivial implication `EpsDatumP ⟹ SmoothOpen ∧ HkMem α 6`, which is all that the E1/E3 bounds
consume from the datum. -/
theorem EpsDatumP.soft {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {h : Fn} (hd : EpsDatumP α ρ ε h) :
    Work.FTS.EllipticEst.SmoothOpen h ∧ Work.Spaces.HkMem α 6 h := ⟨hd.1, hd.2.1⟩

/-- **The regularity class of `P₀`-solutions on `[0,T]`**: joint `C¹` in `(z,θ,τ)` on the open
quadrant up to the endpoints, and every slice in `EpsDatumP` (what the corrected E2a outputs, what
restarts need, and what E3's energy identity consumes). -/
def EpsRegP (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (g : Fam) : Prop :=
  ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
    ∀ τ ∈ Set.Icc 0 T, EpsDatumP α ρ ε (slice g τ)


/-- `EpsRegP` is monotone in the horizon. -/
theorem EpsRegP.mono {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T T' : ℝ} {g : Fam}
    (h : EpsRegP α ρ ε T' g) (hTT' : T ≤ T') : EpsRegP α ρ ε T g :=
  ⟨h.1.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans hTT'⟩,
    fun τ hτ => h.2 τ ⟨hτ.1, hτ.2.trans hTT'⟩⟩


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3)

/-! ## The shifted family and the scheme's right-hand side -/

/-- The fake-time shift of a family: `(shiftFam G t) z θ τ = G z θ (τ - t)`.  The restart at a
junction at absolute fake time `t` covers `[t, t + δ]` and is used in exactly this shifted form. -/
noncomputable def shiftFam (G : Fam) (t : ℝ) : Fam := fun z θ τ => G z θ (τ - t)

@[simp] theorem shiftFam_apply (G : Fam) (t z θ τ : ℝ) :
    shiftFam G t z θ τ = G z θ (τ - t) := rfl

@[simp] theorem slice_shiftFam (G : Fam) (t τ : ℝ) : slice (shiftFam G t) τ = slice G (τ - t) :=
  rfl

/-- `Ftau` depends on a family only through its slice, at possibly *different* fake times. -/
theorem Ftau_congr' {α : ℝ} {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    Work.Construction.Ftau α W τ = Work.Construction.Ftau α W' τ' := by
  funext z θ
  have hzθ : W z θ τ = W' z θ τ' := congrFun (congrFun h z) θ
  simp only [Work.Construction.Ftau, hzθ]

/-- `PsiCan` depends on a family only through its slice, at possibly *different* fake times. -/
theorem slice_PsiCan_congr' {Φs : Fn} {E : Fn → Fn} {W W' : Fam} {τ τ' : ℝ}
    (h : slice W τ = slice W' τ') :
    slice (Work.FTS.Nonlin.PsiCan Φs E W) τ = slice (Work.FTS.Nonlin.PsiCan Φs E W') τ' := by
  funext z θ
  simp only [Work.FTS.Nonlin.PsiCan, slice]
  rw [h]

/-- `muDyn` depends on a family only through its slice, at possibly *different* fake times. -/
theorem muDyn_congr' {α : ℝ} {Φs : Fn} {E : Fn → Fn} {W W' : Fam} {τ τ' : ℝ}
    (h : slice W τ = slice W' τ') :
    Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E W) W τ
      = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E W') W' τ' := by
  simp only [Work.FTS.Galerkin.muDyn, Ftau_congr' h, slice_PsiCan_congr' h, h]

/-- The right-hand side profile `-𝓛_Γ^T(W) + 𝓖(W)` of the `ε`-scheme at the fake time `τ`, as a
function of `(z,θ)`; `IsEpsSol` says `∂_τ g = J_ε (epsRHSu (J_ε g) τ)`. -/
noncomputable def epsRHSu (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (W : Fam) (τ : ℝ) : Fn :=
  fun z θ => dynLin α W τ z θ + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E W) W τ z θ

/-- **The right-hand side of the scheme depends on a family only through its slice** (and this at
possibly different fake times). -/
theorem epsRHSu_congr {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    epsRHSu α ρ ε Φs E W τ = epsRHSu α ρ ε Φs E W' τ' := by
  funext z θ
  simp only [epsRHSu, dynLin, dynRHS, Work.FTS.Galerkin.lamDyn,
    muDyn_congr' h, Ftau_congr' h, slice_PsiCan_congr' h, h]




/-! ## Component extraction for `HasFDerivWithinAt` on `ℝ × ℝ × ℝ`

For a within-derivative `c` of `f` at `x` on a set `S`, the three coordinate directions of `c` are
the corresponding partial derivatives along the coordinate curves; this is `HasFDerivWithinAt.comp`
with the affine curve (`HasDerivWithinAt`).  The `z`- and `θ`-directions give genuine (two-sided)
`deriv`s because those coordinates are interior to the relevant sets, while the `τ`-direction only
gives a `HasDerivWithinAt` (the fake time lives on a closed interval). -/

theorem hasFDerivWithinAt_apply_fst {f : P3 → ℝ} {c : P3 →L[ℝ] ℝ} {S : Set P3} {x : P3} {r : ℝ}
    (hr : 0 < r) (h : HasFDerivWithinAt f c S x)
    (hS : ∀ s ∈ Set.Ioo (x.1 - r) (x.1 + r), (s, x.2.1, x.2.2) ∈ S) :
    c ((1 : ℝ), 0, 0) = deriv (fun s => f (s, x.2.1, x.2.2)) x.1 := by
  have hcurve : HasDerivWithinAt (fun s : ℝ => (s, x.2.1, x.2.2))
      (((1 : ℝ), 0, 0) : P3) (Set.Ioo (x.1 - r) (x.1 + r)) x.1 :=
    (hasDerivWithinAt_id x.1 _).prodMk
      ((hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_const _ _ _))
  have hcomp := h.comp_hasDerivWithinAt x.1 hcurve hS
  have hderiv : HasDerivAt (fun s : ℝ => f (s, x.2.1, x.2.2)) (c ((1 : ℝ), 0, 0)) x.1 :=
    hcomp.hasDerivAt (Ioo_mem_nhds (by linarith) (by linarith))
  exact hderiv.deriv.symm

theorem hasFDerivWithinAt_apply_snd {f : P3 → ℝ} {c : P3 →L[ℝ] ℝ} {S : Set P3} {x : P3} {r : ℝ}
    (hr : 0 < r) (h : HasFDerivWithinAt f c S x)
    (hS : ∀ s ∈ Set.Ioo (x.2.1 - r) (x.2.1 + r), (x.1, s, x.2.2) ∈ S) :
    c ((0 : ℝ), 1, 0) = deriv (fun s => f (x.1, s, x.2.2)) x.2.1 := by
  have hcurve : HasDerivWithinAt (fun s : ℝ => (x.1, s, x.2.2))
      (((0 : ℝ), 1, 0) : P3) (Set.Ioo (x.2.1 - r) (x.2.1 + r)) x.2.1 :=
    (hasDerivWithinAt_const _ _ _).prodMk
      ((hasDerivWithinAt_id x.2.1 _).prodMk (hasDerivWithinAt_const _ _ _))
  have hcomp := h.comp_hasDerivWithinAt x.2.1 hcurve hS
  have hderiv : HasDerivAt (fun s : ℝ => f (x.1, s, x.2.2)) (c ((0 : ℝ), 1, 0)) x.2.1 :=
    hcomp.hasDerivAt (Ioo_mem_nhds (by linarith) (by linarith))
  exact hderiv.deriv.symm

theorem hasFDerivWithinAt_apply_thd {f : P3 → ℝ} {c : P3 →L[ℝ] ℝ} {S : Set P3} {x : P3}
    {a b : ℝ} (h : HasFDerivWithinAt f c S x)
    (hS : ∀ s ∈ Set.Icc a b, (x.1, x.2.1, s) ∈ S) :
    HasDerivWithinAt (fun s => f (x.1, x.2.1, s)) (c ((0 : ℝ), 0, 1)) (Set.Icc a b) x.2.2 := by
  have hcurve : HasDerivWithinAt (fun s : ℝ => (x.1, x.2.1, s))
      (((0 : ℝ), 0, 1) : P3) (Set.Icc a b) x.2.2 :=
    (hasDerivWithinAt_const _ _ _).prodMk
      ((hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_id x.2.2 _))
  exact h.comp_hasDerivWithinAt x.2.2 hcurve hS

/-! ## Monotonicity in the horizon and elementary consequences -/

/-- A solution on `[0,T']` is a solution on every shorter interval `[0,T]`. -/
theorem IsEpsSol.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSol α ρ ε T' Φs E g₀ g) (hTT' : T ≤ T') :
    IsEpsSol α ρ ε T Φs E g₀ g :=
  ⟨h.1, fun z θ τ hz hθ hτ =>
    (h.2 z θ τ hz hθ ⟨hτ.1, hτ.2.trans hTT'⟩).mono fun s hs => ⟨hs.1, hs.2.trans hTT'⟩⟩


/-- `EpsReg` is monotone in the horizon. -/
theorem EpsReg.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {g : Fam}
    (h : EpsReg α ρ ε T' g) (hTT' : T ≤ T') : EpsReg α ρ ε T g :=
  ⟨h.1.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans hTT'⟩,
    fun τ hτ => h.2 τ ⟨hτ.1, hτ.2.trans hTT'⟩⟩

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.radial_atoms5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false
set_option linter.unusedVariables false



/-- **The `φ`-multiplication atom at level `5`.**  Multiplication by the bounded radial profile
`φ(z) = z/(1+z)` does not change the `ℋ⁵`-norm up to a universal constant.  This is
`NonlinRows.NRow10aux.mul_phi_Hk` one slot higher: the pointwise majorant
`HkIntegrand α 5 (φ·g) ≤ K·Br²·HkIntegrand α 5 g` is `Atoms.radialBounded5_majorant` applied
with the uniform bound `Br = 10⁴` for `|D_z^b φ|`, `b ≤ 5`
(`StrongPersist.H6Rows.Npair6SupAux.phiDzdIter6_bound`), and `hkmem_of_majorant` transports
`HkMem`/`HkSq` along it. -/
theorem phiAtoms5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
        ≤ C * Work.Spaces.HkNorm α 5 g := by
  obtain ⟨K, hKpos, hK⟩ := Atoms.radialBounded5_majorant
  have hphiSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
    simpa [Work.FTS.NonlinRows.NRow10aux.phiF]
      using Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen
  refine ⟨Real.sqrt (K * 10000 ^ 2) + 1, by positivity, ?_⟩
  intro α hα hα1 g hg
  obtain ⟨hgSO, hgm⟩ := hg
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) :=
    Work.FTS.OpenPkg.smoothOpen_sepMul hphiSO hgSO
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.HkIntegrand α 5 (fun z θ => z / (1 + z) * g z θ) z θ
        ≤ (K * 10000 ^ 2) * Work.Spaces.HkIntegrand α 5 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have h1 : Work.Spaces.HkIntegrand α 5 (fun z θ => z / (1 + z) * g z θ) 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      have h2 : Work.Spaces.HkIntegrand α 5 g 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      rw [h1, h2, mul_zero]
    · exact hK α (fun z => z / (1 + z)) g 10000 hphiSO hgSO (by norm_num)
        (fun b hb z hz => Work.FTS.StrongPersist.H6Rows.Npair6SupAux.phiDzdIter6_bound
          b (by omega) z hz) z θ hzpos hθ.1 hθ.2
  obtain ⟨hmem, hsq⟩ :=
    Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 5
      (mul_nonneg hKpos.le (by norm_num : (0 : ℝ) ≤ 10000 ^ 2)) hSO hgm hmaj'
  refine ⟨hmem, ?_⟩
  have hXn : 0 ≤ Work.Spaces.HkNorm α 5 g := Real.sqrt_nonneg _
  have hsqrt : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 5 g := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => z / (1 + z) * g z θ))
        ≤ Real.sqrt ((K * 10000 ^ 2) * Work.Spaces.HkSq α 5 g) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (K * 10000 ^ 2) * Real.sqrt (Work.Spaces.HkSq α 5 g) :=
          Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 5 g := rfl
  calc Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 5 g := hsqrt
    _ ≤ (Real.sqrt (K * 10000 ^ 2) + 1) * Work.Spaces.HkNorm α 5 g := by
        refine mul_le_mul_of_nonneg_right ?_ hXn
        linarith


end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The two facts used by `Pz_l12`

`Pz f = f − (L₁₂ f 0 / pzNorm) • bump`, and `L₁₂` is an integral, hence additive.  The
correction profile `bump` is supported in `[1/2,1] × [π/4,3π/8] ⊂ (0,∞) × (0,π/2)`, so its
`L₁₂`-density is a bounded compactly supported function: `integrableOn_L12dens_bump`.  With
that, the density of the projected profile is the difference of the two densities a.e., and
the set integral splits.

The point of stating the linearity with *a.e.* hypotheses rather than for every `s > 0` is
that this is all the caller has (`hae` of `Pz_l12` is an a.e. statement: the slice of a
`ClassC`/`ℋ⁴` profile is integrable for every `s > 0` only because of the honest-`ℋ⁴`
hypotheses, which `Pz_l12` does not assume). -/

/-- **A.e. additivity-and-homogeneity of `L₁₂` at `z = 0`.** If the `θ`-slices of `f` and of
`h` are integrable on `Iθ` for a.e. `s > 0`, and the densities of `f` and `h` are integrable
on `(0,∞)`, then `L₁₂(f + c·h)(0) = L₁₂ f(0) + c·L₁₂ h(0)`. -/
theorem L12_add_mul_ae {f h : ℝ → ℝ → ℝ} {c : ℝ}
    (hf : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    (hh : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * h s θ / s) Work.Spaces.Iθ)
    (hF : MeasureTheory.IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s) (Set.Ioi 0))
    (hH : MeasureTheory.IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s) (Set.Ioi 0)) :
    Work.Construction.L12 (fun z θ => f z θ + c * h z θ) 0
      = Work.Construction.L12 f 0 + c * Work.Construction.L12 h 0 := by
  have hfm : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Ioi 0 →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hf
  have hhm : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Ioi 0 →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * h s θ / s) Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hh
  have hden : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Ioi 0 →
      Work.FM.L12dens Work.Spaces.K (fun z θ => f z θ + c * h z θ) s
        = Work.FM.L12dens Work.Spaces.K f s + c * Work.FM.L12dens Work.Spaces.K h s := by
    filter_upwards [hfm, hhm] with s hs1 hs2 hs
    exact Work.FTS.EllSol.L12dens_add_mul (hs1 hs) (hs2 hs)
  have hF' : MeasureTheory.Integrable (Work.FM.L12dens Work.Spaces.K f)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hF
  have hH' : MeasureTheory.Integrable (Work.FM.L12dens Work.Spaces.K h)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hH
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi hden]
  rw [MeasureTheory.integral_add hF' (hH'.const_mul c), MeasureTheory.integral_const_mul]

/-- The `θ`-slice of the `L₁₂`-density of `bump` is integrable on `Iθ` for every `s > 0`. -/
theorem integrableOn_slice_bump {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) Work.Spaces.Iθ := by
  have hK : Continuous Work.Spaces.K := by
    show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hb : Continuous (fun θ : ℝ => Work.FTS.StrongEps.bump s θ) := by
    show Continuous fun θ : ℝ => Work.FTS.StrongEps.zCut s * Work.FTS.StrongEps.thCut θ
    exact continuous_const.mul (Work.FTS.StrongEps.contDiff_thCut 0).continuous
  exact ((hK.mul hb).div_const s).continuousOn.integrableOn_compact isCompact_Icc


end Work.FTS.StrongEps.PZeroAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.HkSq_step_of_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option maxHeartbeats 1000000

-- context: namespace Work.FTS.StrongEps.StepFacts. `HkSq α k f = ∫z∈Iz ∫θ∈Iθ HkIntegrand α k f z θ`, `Jeps ρ ε` the
-- log-coordinate mollifier, `zShift z p = z*exp(-p)`, `thShift θ p = arctan(tan θ * exp(-p))`, `Iz = [0,∞)`, `Iθ = [0,π/2]`,
-- `logJac s ζ = exp s * kappa ζ` the Jacobian of the log substitution. `hP` is a pointwise bound on the
-- level-`m` integrand of `Jeps ρ ε u` by an average of the level-`m-1` integrand of `u` against a density `Ψ`.
-- The proof should mirror `Work.FTS.StrongEps.HkSqAux.ofReal_HkSq_Jeps_le` in `HkSqAux/Chain.lean`, using the proved
-- `Work.FTS.StrongEps.HkSqAux.integral_shift_le` for the shift step and `Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad` for continuity.
theorem HkSq_step_of_pointwise
    {ρ : ℝ × ℝ → ℝ} {α c δ B ε : ℝ} {m : ℕ} (hm : 1 ≤ m)
    {u : ℝ → ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ}
    (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hMemJ : Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u))
    (hMem : Work.Spaces.HkMem α (m - 1) u)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad)
    (hAe : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Ψ q.2) * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume))
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
          ≤ ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂)) :
    ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      ≤ ENNReal.ofReal (ε⁻¹ * B)
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α (m - 1) u q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α (m - 1) hu
  -- (1) the weighted `L²`-integral of `J_ε u` as an iterated `lintegral` of its `H^m`-integrand
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMemJ.2
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)]
    exact MeasureTheory.setLIntegral_congr_fun (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
      (fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hMemJ.1 z hz)
        (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
  -- (2) the pointwise bound `hP`, integrated
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
    refine MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
      fun z hz => MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      fun θ hθ => hP z hz θ hθ
  -- (3) the constant `ε⁻¹ B` comes out of the two integrals
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
        = ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
      fun z => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    simp only [hinner]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- (4) Tonelli: the `p`-integration is exchanged with the `(z,θ)`-integration
  have h4 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
        = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2))
          ∂volume ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
      rw [show ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
          = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
        Measure.prod_restrict _ _]
      exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2)))
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := volume) (ν := volume) _ _]
          exact hAe.lintegral_prod_right')).symm
    rw [hL]
    rw [MeasureTheory.lintegral_lintegral_swap (μ := (volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)) (ν := volume) hAe]
    refine lintegral_congr fun p => ?_
    rw [MeasureTheory.lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    have hAB : (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
          (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2))
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) := by
      rw [show ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
          = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
        Measure.prod_restrict _ _]
      exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift q.1 p.1)
          (Work.FTS.StrongEps.thShift q.2 p.2))) (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := volume) (ν := volume) _ _]
          exact Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice hcont p)
    rw [hAB]
  -- (5) the shift step: for each `p` the shifted `H^{m-1}`-integral of `u` is bounded
  have h5 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))))
      ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) := by
    refine lintegral_mono fun p => mul_le_mul_right ?_ _
    exact Work.FTS.StrongEps.HkSqAux.integral_shift_le hJac hMem hcont p
  -- (6) the two exponential factors combine and `HkSq α (m-1) u` comes out of the integral
  have hexp : ∀ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
      * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
      = ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) := by
    intro p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring_nf
  have hPsi : ∀ p : ℝ × ℝ, ENNReal.ofReal (Ψ p)
      * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
      = ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) := by
    intro p
    rw [mul_comm (ENNReal.ofReal (Ψ p)) (ENNReal.ofReal (Real.exp _)),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (Real.exp _) (Ψ p)]
  have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))
      = ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
    intro p
    calc ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))
        = (ENNReal.ofReal (Ψ p) * (ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by ring
      _ = (ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by rw [hexp p]
      _ = _ := by rw [hPsi p]
  have h6 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)))
      = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
    rw [show (fun p : ℝ × ℝ => ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)))
        = fun p : ℝ × ℝ => ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) from funext hpt]
    rw [MeasureTheory.lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ) := h1
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := h2
    _ = ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := h3
    _ = ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))) := by rw [h4]
    _ ≤ ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))) := mul_le_mul_right h5 _
    _ = ENNReal.ofReal (ε⁻¹ * B)
          * ((∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) := by rw [h6]
    _ = ENNReal.ofReal (ε⁻¹ * B)
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by rw [mul_assoc]

end Work.FTS.StrongEps.StepFacts
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.PointwiseStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {ρ : ℝ × ℝ → ℝ} {ε α c z θ : ℝ} {m : ℕ} {u : ℝ → ℝ → ℝ}

/-- The constant multiplying `ε⁻¹` in the pointwise step: `B = 200 Dm`. -/
def Bconst (ρ : ℝ × ℝ → ℝ) : ℝ := 200 * Dm ρ

theorem Bconst_pos (ρ : ℝ × ℝ → ℝ) : 0 < Bconst ρ := by
  have h1 : (1 : ℝ) ≤ Dm ρ := le_max_left _ _
  rw [Bconst]
  linarith

theorem Mmax_nonneg (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : 0 ≤ Mmax ρ ε :=
  le_trans zero_le_one (le_max_left _ _)

theorem one_le_ofReal_Mmax (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Mmax ρ ε) := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- The reference `lintegral` of the pointwise step: the density `Ψ` against the shift gain and
the level-`m-1` integrand of `u` at the shifted point. -/
def Jint (ρ : ℝ × ℝ → ℝ) (ε α c : ℝ) (u : ℝ → ℝ → ℝ) (m : ℕ) (z θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p)
    * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
    * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))

theorem Psi_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) :
    0 ≤ Psi ρ ε p :=
  mul_nonneg (inv_nonneg.mpr hε.le)
    (Jker_nonneg_of_nonneg (rhoTilde_nonneg ρ hρ.moll.nonneg) ε p)

/-- The shift gain is nonnegative. -/
theorem exp_nonneg (c : ℝ) (p : ℝ × ℝ) : 0 ≤ Real.exp (2 * c * (|p.1| + |p.2|)) :=
  (Real.exp_pos _).le

/-! ## The generic `ofReal`-conversion for a real slot bound -/

/-- **The conversion of a real slot bound into an `ℝ≥0∞` bound.**  If `a ≤ K ∫ F` with `K, F`
nonnegative and `K ≤ K'`, `F ≤ F'` pointwise, then `ofReal a ≤ ofReal K' * ∫⁻ ofReal F'`. -/
theorem ofReal_mul_integral_le_lintegral {K K' : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hKK : K ≤ K') {F F' : ℝ × ℝ → ℝ} (hF : ∀ p, 0 ≤ F p) (hF' : ∀ p, 0 ≤ F' p)
    (hFF : ∀ p, F p ≤ F' p) :
    ENNReal.ofReal (K * ∫ p : ℝ × ℝ, F p) ≤ ENNReal.ofReal K' * ∫⁻ p, ENNReal.ofReal (F' p) := by
  have hmid : ENNReal.ofReal (∫ p : ℝ × ℝ, F p) ≤ ∫⁻ p, ENNReal.ofReal (F' p) :=
    (ofReal_integral_le_lintegral_ofReal hF).trans
      (lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hFF p))
  calc ENNReal.ofReal (K * ∫ p : ℝ × ℝ, F p)
      = ENNReal.ofReal K * ENNReal.ofReal (∫ p : ℝ × ℝ, F p) := ENNReal.ofReal_mul hK
    _ ≤ ENNReal.ofReal K * ∫⁻ p, ENNReal.ofReal (F' p) :=
        mul_le_mul_right hmid _
    _ ≤ ENNReal.ofReal K' * ∫⁻ p, ENNReal.ofReal (F' p) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hKK) _

/-- The `lintegral` of `ofReal` of the product `Ψ · e^{2c|p|} · G` is `Jint`. -/
theorem lintegral_prod_eq_Jint (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α c : ℝ}
    (hε0 : 0 < ε) {u : ℝ → ℝ → ℝ} {m : ℕ} {z θ : ℝ} :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
        * Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)))
      ≤ Jint ρ ε α c u m z θ := by
  rw [Jint]
  refine lintegral_mono fun p => ?_
  have hP : 0 ≤ Psi ρ ε p := Psi_nonneg ρ hρ hε0 p
  have he : 0 ≤ Real.exp (2 * c * (|p.1| + |p.2|)) := (Real.exp_pos _).le
  have hG : 0 ≤ Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
      (Work.FTS.StrongEps.thShift θ p.2) := Work.Spaces.HkIntegrand_nonneg α (m - 1) u _ _
  rw [ENNReal.ofReal_mul (mul_nonneg hP he), ENNReal.ofReal_mul hP]


end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `1 ≤ t^{-γ}` for `0 < t ≤ 1`, `0 ≤ γ` (the `α`-power monotonicity used by the arithmetic). -/
theorem one_le_rpow_neg' {t γ : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hg : 0 ≤ γ) :
    1 ≤ t ^ (-γ) := by
  rw [Real.rpow_neg h0.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos h0 γ)).mpr (Real.rpow_le_one h0.le h1 hg)

/-- **The `N₀` zero-mode estimate from its three analytic pieces.**

`hsup` is the pointwise `L₁₂` bound `|L₁₂ g z| ≤ 3|g|_{ℋ⁴}` (the sibling
`Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open`), `hcont` the joint continuity of `N₀` on the
open quadrant (`...contN0_open`) and `hpt` the pointwise domination of `N₀²` by the `ℋ⁴`-integrand
of `g` (`...N0_sq_w_open`).  The conclusion is the requested uniform bound with the explicit
constant `K = 10⁵`, valid for `α ∈ (0,1]`. -/
theorem h6pair_N0_zero_of_pieces
    (hsup : ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g)
    (hcont : ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      ContinuousOn (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α g) g))
        (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hpt : ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g →
      (∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g) →
      ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
          ≤ 7 * (A₀ α (Work.FTS.Nonlin.Xn α g) * Work.Spaces.HkIntegrand α 4 g r θ
              + B₀ α (Work.FTS.Nonlin.Xn α g) * (1 / (1 + r)) ^ 2)) :
    ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        |Work.Construction.L12 (Work.Construction.N0 α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) 0|
          ≤ K * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  refine ⟨10 ^ 5, 1, by norm_num, by norm_num, ?_⟩
  intro α hαI f M hAdm _hmem7 hM
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hAdm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_four_of_six hso hAdm.reg.2
  have hL12g : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 f z| ≤ 3 * Work.FTS.Nonlin.Xn α f :=
    hsup hα hα1 hso hmem4
  have hptf := hpt hα hα1 hso hL12g
  have hcontf := hcont hα hα1 hso hmem4
  set X : ℝ := Work.FTS.Nonlin.Xn α f with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 f
  have hX2 : 0 ≤ X ^ 2 := by positivity
  have hX4 : 0 ≤ X ^ 4 := by positivity
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ with hΨ
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)) :=
    hmem4.2.mono_set Set.Ioi_subset_Ici_self
  set Φ : ℝ → ℝ := fun r =>
    7 * (A₀ α X * Ψ r + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) with hΦ
  -- ## the weighted angular energy of `N₀` is dominated by `Φ`
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
          * ((1 + r) / r) ^ 2
        ≤ Φ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hweq : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by rw [Work.Spaces.w, div_pow]
    have hΦr : Φ r = 7 * (A₀ α X * Ψ r + ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) := by
      rw [hΦ]
    rw [hweq, ← MeasureTheory.integral_mul_const, hΦr]
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hstep : (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
            * Work.Spaces.w r)
        ≤ ∫ θ in Work.Spaces.Iθ,
          7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
            + B₀ α X * (1 / (1 + r)) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun θ =>
          mul_nonneg (sq_nonneg _) (le_trans zero_le_one hW1))
      · refine (((hmem4.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
        refine MeasureTheory.integrableOn_const ?_
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top
      · rw [hIoo2]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => by simpa only [hX] using hptf r hr θ hθ)
    refine hstep.trans ?_
    have hintA : MeasureTheory.IntegrableOn
        (fun θ => A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ) Work.Spaces.Iθ :=
      (hmem4.1 r hzr).const_mul (A₀ α X)
    have hintB : MeasureTheory.IntegrableOn
        (fun θ => B₀ α X * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hvalPsi : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) = Ψ r := rfl
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintA hintB,
      MeasureTheory.integral_const_mul, Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra, hvalPsi]
    exact le_of_eq (by ring)
  -- ## the slice integrability of the squared `N₀`
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
    have hW1 : 1 ≤ Work.Spaces.w r := by
      rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
      nlinarith
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    have hslice : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcontf hr
    have hmaj : MeasureTheory.Integrable
        (fun θ => 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (((hmem4.1 r hzr).const_mul (A₀ α X)).add ?_).const_mul 7
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    refine MeasureTheory.Integrable.mono' hmaj (hslice.pow 2) ?_
    rw [hIoo2]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
        ≤ (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2
          * Work.Spaces.w r := by
          nlinarith [hW1,
            sq_nonneg (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ)]
      _ ≤ 7 * (A₀ α X * Work.Spaces.HkIntegrand α 4 f r θ
          + B₀ α X * (1 / (1 + r)) ^ 2) := by
          simpa only [hX] using hptf r hr θ hθ
  -- ## a.e. strong measurability of the weighted angular energy of `N₀`
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.Nonlinear.Pieces.aesm_weighted_energy_of_continuousOn hcontf
  -- ## integrability of the majorant `Φ`
  have hΦint : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    exact (h1.add h2).const_mul 7
  -- ## the zero-mode bound
  have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound
    (f := fun z θ => Work.Construction.N0 α (Work.Construction.Ftot α f) f z θ)
    hsl hmeas hΦint hbd
  -- ## the size of `Φ`
  have hΨval : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = X ^ 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) = Work.Spaces.HkSq α 4 f := by
      rw [hΨ, Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : X ^ 2 = Work.Spaces.HkSq α 4 f := by
      rw [hX, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    rw [h1, h2]
  have hc2 : (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
  have hci0 : (0 : ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun r _ => by positivity)
  set A : ℝ := α ^ (-(9 : ℝ)) with hA
  have hApos : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos hα _
  have hA0 : 0 ≤ A := le_of_lt hApos
  have hA1 : 1 ≤ A := by rw [hA]; exact one_le_rpow_neg' hα hα1 (by norm_num)
  have h_inv2 : (α ^ 2)⁻¹ ≤ A := by
    rw [← one_div, div_le_iff₀ (pow_pos hα 2), hA, ← Real.rpow_natCast α 2,
      ← Real.rpow_add hα (-(9 : ℝ)) ((2 : ℕ) : ℝ)]
    rw [show (-(9 : ℝ)) + ((2 : ℕ) : ℝ) = -(7 : ℝ) by norm_num]
    exact one_le_rpow_neg' hα hα1 (by norm_num)
  have h_sq : α ^ 2 ≤ A := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(9 : ℝ)) ≤ (2 : ℝ) by norm_num)
    rw [hA, ← Real.rpow_natCast α 2]
    exact h
  have h_4 : α ^ 4 ≤ A := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (show (-(9 : ℝ)) ≤ (4 : ℝ) by norm_num)
    rw [hA, ← Real.rpow_natCast α 4]
    exact h
  have h1X : (1 : ℝ) ≤ 1 + X := by linarith
  have hX4le : X ^ 4 ≤ (1 + X) ^ 4 := pow_le_pow_left₀ hX0 (by linarith : X ≤ 1 + X) 4
  have hX2le : X ^ 2 ≤ (1 + X) ^ 4 := by
    have h1 : X ^ 2 ≤ (1 + X) ^ 2 := pow_le_pow_left₀ hX0 (by linarith : X ≤ 1 + X) 2
    have h2 : (1 + X) ^ 2 ≤ (1 + X) ^ 4 := pow_le_pow_right₀ h1X (by norm_num)
    linarith
  have h1le : (1 : ℝ) ≤ (1 + X) ^ 4 := one_le_pow₀ h1X
  have h01X : (0 : ℝ) ≤ 1 + X := by linarith
  have hAle : A ≤ (1 + X) ^ 4 * A := by
    simpa using mul_le_mul_of_nonneg_right h1le hA0
  have hInt_le : (∫ r in Set.Ioi (0 : ℝ), Φ r) ≤ 10 ^ 7 * A * (1 + X) ^ 4 := by
    set M' : ℝ := 25600 * α ^ 4 + 90000 * (α ^ 2 * X ^ 2) with hM'def
    have hM'0 : 0 ≤ M' := by rw [hM'def]; positivity
    have h1 : MeasureTheory.IntegrableOn (fun r => A₀ α X * Ψ r) (Set.Ioi (0 : ℝ)) :=
      hΨint.const_mul (A₀ α X)
    have h2 : MeasureTheory.IntegrableOn
        (fun r => ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul ((Real.pi / 2) * B₀ α X)
    have hΦval : (∫ r in Set.Ioi (0 : ℝ), Φ r)
        = 7 * (A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
      rw [hΦ, MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hΨval]
    rw [hΦval]
    have hπ4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
    -- the two summands
    have hT1 : A₀ α X * X ^ 2 ≤ 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by
      have h := mul_le_mul_of_nonneg_right (A₀_le (X := X) hα hα1) hX2
      have he : (90 * X ^ 2 / α ^ 2 + 16 * α ^ 2) * X ^ 2
          = 90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2) := by ring
      linarith [h, he.le, he.ge]
    have hT2 : B₀ α X * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 * M' := by
      rw [hM'def]
      have h1' : B₀ α X * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          ≤ (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) :=
        mul_le_mul_of_nonneg_right (B₀_le α X) hci0
      have h2' : (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          ≤ (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hc2 (by positivity)
      have he : (25600 * α ^ 4 + 90000 * α ^ 2 * X ^ 2) * 2
          = 2 * (25600 * α ^ 4 + 90000 * (α ^ 2 * X ^ 2)) := by ring
      linarith [h1', h2', he.le, he.ge]
    have hπB : ((Real.pi / 2) * B₀ α X) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
        ≤ 4 * M' := by
      calc ((Real.pi / 2) * B₀ α X) * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          = (Real.pi / 2) * (B₀ α X * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
            ring
        _ ≤ (Real.pi / 2) * (2 * M') := mul_le_mul_of_nonneg_left hT2 (by positivity)
        _ = Real.pi * M' := by ring
        _ ≤ 4 * M' := mul_le_mul_of_nonneg_right hπ4 hM'0
    -- the termwise bounds, with the `α`-powers pushed into `A`
    have hp1 : 90 * (X ^ 4 / α ^ 2) ≤ 90 * ((1 + X) ^ 4 * A) := by
      have h1' : X ^ 4 / α ^ 2 ≤ X ^ 4 * A := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h_inv2 hX4
      calc 90 * (X ^ 4 / α ^ 2) ≤ 90 * (X ^ 4 * A) :=
            mul_le_mul_of_nonneg_left h1' (by norm_num)
        _ ≤ 90 * ((1 + X) ^ 4 * A) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX4le hA0) (by norm_num)
    have hp2 : 16 * (α ^ 2 * X ^ 2) ≤ 16 * ((1 + X) ^ 4 * A) := by
      have h1' : α ^ 2 * X ^ 2 ≤ X ^ 2 * A := by
        rw [mul_comm (α ^ 2) (X ^ 2)]
        exact mul_le_mul_of_nonneg_left h_sq hX2
      calc 16 * (α ^ 2 * X ^ 2) ≤ 16 * (X ^ 2 * A) :=
            mul_le_mul_of_nonneg_left h1' (by norm_num)
        _ ≤ 16 * ((1 + X) ^ 4 * A) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX2le hA0) (by norm_num)
    have hM'le : M' ≤ 25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A) := by
      have ha : α ^ 4 ≤ (1 + X) ^ 4 * A := le_trans h_4 hAle
      have hb : α ^ 2 * X ^ 2 ≤ (1 + X) ^ 4 * A := by
        refine le_trans ?_ (mul_le_mul_of_nonneg_right hX2le hA0)
        rw [mul_comm (α ^ 2) (X ^ 2)]
        exact mul_le_mul_of_nonneg_left h_sq hX2
      rw [hM'def]
      exact add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    have h4M : 4 * M' ≤ 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A)) :=
      mul_le_mul_of_nonneg_left hM'le (by norm_num)
    have hbound : 7 * (A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
          * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2))
        ≤ 7 * (90 * ((1 + X) ^ 4 * A) + 16 * ((1 + X) ^ 4 * A)
            + 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A))) := by
      have hsum : A₀ α X * X ^ 2 + ((Real.pi / 2) * B₀ α X)
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
          ≤ (90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)) + 4 * M' := by
        linarith [hT1, hπB]
      have hsum2 : (90 * (X ^ 4 / α ^ 2) + 16 * (α ^ 2 * X ^ 2)) + 4 * M'
          ≤ 90 * ((1 + X) ^ 4 * A) + 16 * ((1 + X) ^ 4 * A)
            + 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A)) := by
        linarith [hp1, hp2, h4M]
      exact mul_le_mul_of_nonneg_left (le_trans hsum hsum2) (by norm_num)
    refine hbound.trans ?_
    have hfin : 7 * (90 * ((1 + X) ^ 4 * A) + 16 * ((1 + X) ^ 4 * A)
          + 4 * (25600 * ((1 + X) ^ 4 * A) + 90000 * ((1 + X) ^ 4 * A)))
        = (7 * (90 + 16 + 4 * (25600 + 90000))) * ((1 + X) ^ 4 * A) := by ring
    rw [hfin]
    have hc : 7 * (90 + 16 + 4 * (25600 + 90000)) ≤ (10 : ℝ) ^ 7 := by norm_num
    have hBnn : 0 ≤ (1 + X) ^ 4 * A := mul_nonneg (pow_nonneg h01X 4) hA0
    calc (7 * (90 + 16 + 4 * (25600 + 90000))) * ((1 + X) ^ 4 * A)
        ≤ (10 : ℝ) ^ 7 * ((1 + X) ^ 4 * A) := mul_le_mul_of_nonneg_right hc hBnn
      _ = 10 ^ 7 * A * (1 + X) ^ 4 := by ring
  -- ## the square root and the final constant
  have hΦ0 : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), Φ r := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun r _ => ?_)
    have hΨr0 : 0 ≤ Ψ r := by
      rw [hΨ]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f r θ)
    have h1 : (0 : ℝ) ≤ A₀ α X * Ψ r := mul_nonneg (A₀_nonneg α X) hΨr0
    have h2 : (0 : ℝ) ≤ ((Real.pi / 2) * B₀ α X) * (1 / (1 + r)) ^ 2 :=
      mul_nonneg (mul_nonneg (by positivity) (B₀_nonneg α X)) (sq_nonneg _)
    rw [hΦ]
    exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
  have hsqrt : |Work.Construction.L12
      (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ 3 * Real.sqrt (10 ^ 7 * A * (1 + X) ^ 4) := by
    refine hmain.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact Real.sqrt_le_sqrt hInt_le
  have hbig0 : (0 : ℝ) ≤ 10 ^ 4 * A * (1 + X) ^ 4 := by positivity
  have hsqrtle : Real.sqrt (10 ^ 7 * A * (1 + X) ^ 4) ≤ 10 ^ 4 * A * (1 + X) ^ 4 := by
    rw [Real.sqrt_le_left hbig0]
    have hAB : 1 ≤ A * (1 + X) ^ 4 := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ A * (1 + X) ^ 4 := mul_le_mul hA1 h1le (by norm_num) hA0
    have hAB0 : 0 ≤ A * (1 + X) ^ 4 := mul_nonneg hA0 (pow_nonneg h01X 4)
    have hle1 : 1 ≤ 10 * (A * (1 + X) ^ 4) := by linarith
    have hc0 : 0 ≤ (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hle1 hc0
    have hstep' : (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4)
        ≤ (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) * (10 * (A * (1 + X) ^ 4)) := by
      simpa only [mul_one] using hstep
    calc 10 ^ 7 * A * (1 + X) ^ 4 = (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) := by ring
      _ ≤ (10 : ℝ) ^ 7 * (A * (1 + X) ^ 4) * (10 * (A * (1 + X) ^ 4)) := hstep'
      _ = (10 ^ 4 * A * (1 + X) ^ 4) ^ 2 := by ring
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith [le_trans hX0 hM]
  have hXM : (1 + X) ^ 4 ≤ (1 + M) ^ 4 :=
    pow_le_pow_left₀ h01X (by linarith [hM]) 4
  calc |Work.Construction.L12
        (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ 3 * Real.sqrt (10 ^ 7 * A * (1 + X) ^ 4) := hsqrt
    _ ≤ 3 * (10 ^ 4 * A * (1 + X) ^ 4) := mul_le_mul_of_nonneg_left hsqrtle (by norm_num)
    _ ≤ 10 ^ 5 * A * (1 + M) ^ 4 := by
        have hnn : 0 ≤ A * (1 + X) ^ 4 := mul_nonneg hA0 (pow_nonneg h01X 4)
        have h3 : 3 * (10 ^ 4 * A * (1 + X) ^ 4) ≤ 10 ^ 5 * A * (1 + X) ^ 4 := by
          calc 3 * (10 ^ 4 * A * (1 + X) ^ 4) = (3 * 10 ^ 4) * (A * (1 + X) ^ 4) := by ring
            _ ≤ (10 : ℝ) ^ 5 * (A * (1 + X) ^ 4) :=
                mul_le_mul_of_nonneg_right (by norm_num) hnn
            _ = 10 ^ 5 * A * (1 + X) ^ 4 := by ring
        have h4 : 10 ^ 5 * A * (1 + X) ^ 4 ≤ 10 ^ 5 * A * (1 + M) ^ 4 := by
          have h5 : 0 ≤ 10 ^ 5 * A := by positivity
          have h6 := mul_le_mul_of_nonneg_left hXM h5
          calc 10 ^ 5 * A * (1 + X) ^ 4 = (10 ^ 5 * A) * (1 + X) ^ 4 := by ring
            _ ≤ (10 ^ 5 * A) * (1 + M) ^ 4 := h6
            _ = 10 ^ 5 * A * (1 + M) ^ 4 := by ring
        linarith [h3, h4]

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The level-six `z/(1+z)` radial multiplier does not change the weighted `ℋ⁶`-norm:
the product is again smooth on the open quadrant, again in `HkMem α 6`, and its `HkNorm`
is bounded by a universal (α-independent) constant times the `HkNorm` of the input.

The proof assembles two independent pieces:

* `radialBounded6_majorant` — the pointwise majorant
  `HkIntegrand α 6 (r·g) ≤ K Br² HkIntegrand α 6 g` for a radial factor `r` whose
  `D_z`-iterates of order `≤ 6` are bounded by `Br`;
* `phiDzdIter6_bound` — the numerical bound `|D_z^b (z/(1+z))| ≤ 10000` for `b ≤ 6`, `z ≥ 0`;

applied with `r = z/(1+z)`, `Br = 10000` through `hkmem_of_majorant` (which transports
`HkMem` and `HkSq` along a pointwise majorant) and the square-root arithmetic on `HkNorm`. -/
theorem mulPhi6 : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {g : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) ∧
      Work.Spaces.HkMem α 6 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * g z θ)
        ≤ C * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨K, hKpos, hK⟩ := radialBounded6_majorant
  refine ⟨Real.sqrt (K * 10000 ^ 2) + 1, by positivity, ?_⟩
  intro α g hα hα1 hgSO hgm
  -- smoothness of the radial factor `z/(1+z)` on the open quadrant
  have hphiSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
    simpa [Work.FTS.NonlinRows.NRow10aux.phiF]
      using Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen
  -- smoothness of the product
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) :=
    Work.FTS.OpenPkg.smoothOpen_sepMul hphiSO hgSO
  -- the pointwise majorant on the whole half-strip
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.HkIntegrand α 6 (fun z θ => z / (1 + z) * g z θ) z θ
        ≤ (K * 10000 ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have h1 : Work.Spaces.HkIntegrand α 6 (fun z θ => z / (1 + z) * g z θ) 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      have h2 : Work.Spaces.HkIntegrand α 6 g 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      rw [h1, h2, mul_zero]
    · exact hK α (fun z => z / (1 + z)) g 10000 hphiSO hgSO (by norm_num)
        (fun b hb z hz => phiDzdIter6_bound b hb z hz) z θ hzpos hθ.1 hθ.2
  obtain ⟨hmem, hsq⟩ :=
    Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 6
      (mul_nonneg hKpos.le (by norm_num : (0 : ℝ) ≤ 10000 ^ 2)) hSO hgm hmaj'
  refine ⟨hSO, hmem, ?_⟩
  have hXn : 0 ≤ Work.Spaces.HkNorm α 6 g := Real.sqrt_nonneg _
  have hsqrt : Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 6 g := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => z / (1 + z) * g z θ))
        ≤ Real.sqrt ((K * 10000 ^ 2) * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (K * 10000 ^ 2) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
          Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 6 g := rfl
  calc Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 6 g := hsqrt
    _ ≤ (Real.sqrt (K * 10000 ^ 2) + 1) * Work.Spaces.HkNorm α 6 g := by
        refine mul_le_mul_of_nonneg_right ?_ hXn
        linarith

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsL12zero =====
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

open Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise domination of the weighted datum by the `ℋ⁰`-integrand -/

/-- At `k = 0` the squared weighted datum is (at most, in fact exactly) the `ℋ⁰`-integrand:
the only surviving summand is the `D_z^0`-term `i = 0`. -/
lemma Gaz_sq_le_HkIntegrand_zero (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Gaz h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 h z θ := by
  simpa only [Gaz, Sw, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 0 h z θ 0 (by norm_num)

/-- On the domain, `|Gaz|` is dominated by the square root of the `ℋ⁰`-integrand. -/
lemma abs_Gaz_le_sqrt_HkIntegrand_zero (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    |Gaz h z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 0 h z θ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Gaz_sq_le_HkIntegrand_zero α h z θ)

/-! ## The angular Cauchy–Schwarz step -/

/-- The angular half of the argument, at `k = 0`: the weighted angular profile `K · Sw` is
paired against the weighted datum `Gaz h s` and estimated by Cauchy–Schwarz against the
`ℋ⁰`-integrand.  The only hypothesis is integrability of the slice of the integrand; no
measurability of `h` is needed (the Cauchy–Schwarz step is arranged so that the only
functions whose measurability is used are the continuous profile `K·Sw`, the integrable
square root `√(HkIntegrand α 0 h s ·)`, and `|K·Sw|`). -/
theorem abs_integral_K_S_Gaz_le_zero (α : ℝ) (h : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 h s θ)
      Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      ≤ BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Sw θ with hu
  set v : ℝ → ℝ := fun θ => Gaz h s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 0 h s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 h s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α 0 h s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by
    intro θ; rw [hw]; exact Real.sqrt_nonneg _
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ; rw [hv, hw]; exact abs_Gaz_le_sqrt_HkIntegrand_zero α h s θ
  have hcont_K : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hcont_u : Continuous u := by
    rw [hu]; exact hcont_K.mul continuous_sw
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = BK := by
    rw [BK]
    congr 1
    simp only [hu]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => sq_abs (Work.Spaces.K θ * Sw θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
        rw [hsqrt_u, hsqrt_w]

/-! ## The pointwise bound on the `L₁₂`-density -/

/-- The `L₁₂`-density as a constant multiple of the angular integral of the weighted datum
(specialisation to `k = 0` of the density factorisation; the factorisation itself is
`α`- and `k`-independent and is proved in `Work.FTS.GalBasis.cc`). -/
lemma abs_L12dens_le_zero (α : ℝ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 0 h)
    {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ)) := by
  rw [L12dens_eq_weighted h hs, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_K_S_Gaz_le_zero α h (hmem.1 s hs.le)) (Wlam_nonneg hs.le)

/-! ## The radial Cauchy–Schwarz step -/

/-- **The integrated pointwise bound on the `L₁₂`-density** (`k = 0`).  If
`|L12dens h s| ≤ Wlam s · (BK · √(∫_θ HkIntegrand α 0 h s θ))` for every `s > 0` and
`h ∈ ℋ⁰_α`, then the same bound holds after integrating in `s`:

`∫_{s>0} |L12dens h s| ≤ BK · √W2 · √(HkSq α 0 h)`.

This is Cauchy–Schwarz in the radial variable: `Wlam²` is integrable on `(0,∞)` with
`∫ Wlam² = W2`, and `∫_{(0,∞)} (√(∫_θ HkIntegrand α 0 h s θ))² = HkSq α 0 h` (the two sets
`(0,∞)` and `Iz = [0,∞)` differ by the null set `{0}`). -/
theorem integral_abs_L12dens_le_zero (α : ℝ) (h : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 0 h)
    (hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ))) :
    ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- `H` is integrable on `(0,∞)` (hence so is `A²`)
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi 0)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) := by
    rw [hA]
    exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam` is square-integrable
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi 0)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi 0))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlam_memLp : MemLp Wlam 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- `∫_{(0,∞)} A² = HkSq α 0 h`, up to the null set `{0}`
  have hW2eq : ∫ s in Set.Ioi 0, Wlam s ^ 2 = W2 := rfl
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 0 h := by
    rw [hH]; rfl
  have hA2sq : ∫ s in Set.Ioi 0, A s ^ 2 = Work.Spaces.HkSq α 0 h := by
    have h1 : ∫ s in Set.Ioi 0, A s ^ 2 = ∫ s in Set.Ioi 0, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]; exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    rw [h1, h2, hIz_eq]
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam) (v := A) (s := Set.Ioi 0) hWlam_memLp hA_memLp
    rw [hA2sq, hW2eq] at hcs
    have hnn : 0 ≤ ∫ s in Set.Ioi 0, Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), (0 : ℝ) ≤ Wlam s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs =>
        mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s)
    rwa [abs_of_nonneg hnn] at hcs
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi (0 : ℝ), Wlam s * A s ≤ Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam s ^ 2 + A s ^ 2) (Set.Ioi 0) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => BK * (Wlam s * A s)) (Set.Ioi 0) := by
    refine Integrable.mono' (hsum_int.const_mul BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ BK * (Wlam s * A s) :=
        mul_nonneg BK_nonneg (mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) BK_nonneg
  have h2 : ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      |Work.Construction.L12dens h s| ≤ BK * (Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := by
      simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := hbA
      _ = BK * (Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi 0, BK * (Wlam s * A s)
      = BK * ∫ s in Set.Ioi 0, Wlam s * A s :=
    MeasureTheory.integral_const_mul BK _
  have h4 : BK * ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h)) :=
    mul_le_mul_of_nonneg_left hCS BK_nonneg
  calc ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := h2
    _ = BK * ∫ s in Set.Ioi 0, Wlam s * A s := h3
    _ ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h)) := h4
    _ = BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) := by ring

/-! ## The main theorem -/

/-- **`|L₁₂ u 0|` is bounded by the `ℋ⁰_α`-norm of `u`, uniformly in `α ∈ (0,1]`.**

`L₁₂ u 0 = ∫_{s>0} ∫_θ K θ · u s θ / s`, and with `Gaz u s θ = u s θ · w s / sin(2θ)^{η/2}`
one has the factorisation `K θ u/s = Gaz u · (K θ Sw θ Wlam s)`; two Cauchy–Schwarz steps
(angular against `BK = √(∫_θ (K Sw)²)`, radial against `√W2 = √(∫_s Wlam²)`) give
`|L₁₂ u 0| ≤ BK·√W2 · √(HkSq α 0 u) = BK·√W2 · |u|_{ℋ⁰_α}`.  Both constants are finite,
positive and independent of `α` (and of `u`); the statement's `α` is confined to `(0,1]`
for consistency with the surrounding blocks of `L3Rhs`. -/
theorem L3RhsL12zero : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (u : Work.FTS.Galerkin.Fn),
    Work.Spaces.HkMem α 0 u →
    |Work.Construction.L12 u 0| ≤ C * Work.Spaces.HkNorm α 0 u := by
  refine ⟨BK * Real.sqrt W2 + 1, by nlinarith [BK_nonneg, Real.sqrt_nonneg W2], ?_⟩
  intro α hα h hmem
  have hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ)) :=
    fun s hs => abs_L12dens_le_zero α h hmem hs
  have hL12 : Work.Construction.L12 h 0
      = ∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s := rfl
  calc |Work.Construction.L12 h 0|
      = |∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s| := by rw [hL12]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun s => Work.Construction.L12dens h s))
    _ ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) :=
        integral_abs_L12dens_le_zero α h hmem hbd
    _ = (BK * Real.sqrt W2) * Work.Spaces.HkNorm α 0 h := by
        rw [Work.Spaces.HkNorm]
    _ ≤ (BK * Real.sqrt W2 + 1) * Work.Spaces.HkNorm α 0 h := by
        have hx := Work.Spaces.HkNorm_nonneg α 0 h
        nlinarith

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsN0FixBlock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-!
# The `N₀`-fixed block of the level-three right-hand side

`N0fix α = N₀₁ + N₀₂` depends on the profile `F_*` alone, and on the open quadrant it is the
separable datum `Kfac α · rhoR · psiA α`, whose `ℋ⁴`-norm is `O(α²)`
(`Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound`,
`Work.FTS.NonlinRows.HkMem_N0fix`).  Since `ℋ³ ⊂ ℋ⁴` (both for the membership and for the
norm, `Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen` /
`Work.FTS.StrongLWP.HkNorm_mono_of_mem`), the same block satisfies the level-three clauses of
the level-three right-hand side with the same constant, **provided** one records that it is
`C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`).

The one ingredient that is not a direct citation is that smoothness: on the open quadrant
`L₁₂(F_*(α))(z) = 2α/(1+z)` (`Work.Construction.L12_Fstar_eq`) is an explicit rational
function of `z`, `F_*` is `SmoothOpen` (`Work.FTS.LocData.SmoothQuad_Fstar`), and the angular
factors `sin 2θ`, `cos 2θ - sin²θ` are smooth everywhere, so `N0fix α` is a sum of products of
smooth functions on the quadrant.
-/

/-- **`L₁₂(F_*(α))` is `C^∞` on `(0,∞)`**: on that set it equals the explicit function
`z ↦ 2α/(1+z)` (`Work.Construction.L12_Fstar_eq`). -/
theorem contDiffOn_L12_Fstar_L3 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) :
    ContDiffOn ℝ m (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi 0) := by
  have hbase : ContDiffOn ℝ m (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ m (fun z : ℝ => (1 : ℝ) + z) (Set.Ioi 0) :=
      contDiffOn_const.add contDiffOn_id
    have h2 := (contDiffOn_const (c := 2 * α) :
      ContDiffOn ℝ m (fun _ : ℝ => 2 * α) (Set.Ioi 0)).div h1
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        have : (0 : ℝ) < 1 + z := by linarith
        linarith)
    exact h2
  refine ContDiffOn.congr hbase ?_
  intro z hz
  exact Work.Construction.L12_Fstar_eq hα hα1 hz.le

/-- **`N0fix α` is `C^∞` on the open quadrant.**  Unfolding `N0fix = N₀₁ + N₀₂`, the block is
the sum of the two products

`((3/(2α)) sin 2θ L₁₂(F_*(α))) · ∂_θF_*(α)` and `(-(cos 2θ - sin²θ) L₁₂(F_*(α))) · D_zF_*(α)`,

each a product of an angular factor (smooth everywhere), the radial factor `L₁₂(F_*(α))`
(smooth on `(0,∞)` by `contDiffOn_L12_Fstar_L3`) and a derivative of the `SmoothOpen` profile
`F_*(α)`. -/
theorem smoothOpen_N0fix (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) := by
  have hL12 : ∀ m : ℕ, ContDiffOn ℝ m
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) :=
    contDiffOn_L12_Fstar_L3 α hα hα1
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Real.sin (2 * θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul_swap hL12
      (by fun_prop : ContDiff ℝ ⊤ (fun θ : ℝ => (3 / (2 * α)) * Real.sin (2 * θ)))
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Real.cos (2 * θ) - Real.sin θ ^ 2))
        * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul_swap hL12
      (by fun_prop : ContDiff ℝ ⊤ (fun θ : ℝ => (-(Real.cos (2 * θ) - Real.sin θ ^ 2))))
  have hT1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z)
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ) := hA.mul hFsm.pth
  have hT2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((-(Real.cos (2 * θ) - Real.sin θ ^ 2))
        * Work.Construction.L12 (Work.Construction.Fstar α) z)
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := hB.mul hFsm.Dz
  have hsum : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + ((-(Real.cos (2 * θ) - Real.sin θ ^ 2))
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := hT1.add hT2
  refine Work.FTS.EllipticEst.SmoothOpen.congr hsum ?_
  intro z θ hz hθ hθ2
  simp only [Work.FTS.Nonlin.N0fix, Work.Construction.N01, Work.Construction.N02,
    Work.Construction.s2_eq, Work.Construction.c2m_eq]

theorem L3RhsN0FixBlock : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) ∧
    Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N0fix α) ∧
    Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N0fix α) ≤ C * α ^ 2 := by
  obtain ⟨K, hK, hbnd⟩ := Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound
  refine ⟨K, hK, fun α hα => ?_⟩
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hso : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    smoothOpen_N0fix α hα0 hα1
  have h4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.NonlinRows.HkMem_N0fix α hα0 hα1
  have h3 : Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen (α := α) (k := 3) (k' := 4)
      (by norm_num) hso h4
  have hnorm : Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N0fix α)
      ≤ Work.Spaces.HkNorm α 4 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 4) (k' := 3) (by norm_num) h4
  exact ⟨hso, h3, le_trans hnorm (hbnd α hα0 hα1)⟩

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNggBlock =====
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

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth pth)
open Work.FTS.EllipticEst (SmoothOpen Q0)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary closures -/

/-- `SmoothOpen` is closed under multiplication (the `SmoothOpen`-analogue of
`ContDiffOn.mul`, with the uncurrying made explicit). -/
theorem smoothOpen_mulNgg {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) :
    SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun z θ => F z θ * G z θ)
      = Function.uncurry F * Function.uncurry G := rfl
  rw [h1]
  exact hF.mul hG

/-- The finite-order smoothness class of the open quadrant is implied by `SmoothOpen`
(the two sets `Work.FTS.EllipticEst.Q0` and `Work.Construction.Qd` are the same set). -/
theorem q0Sm_of_smoothOpenNgg {k : ℕ} {F : ℝ → ℝ → ℝ} (h : SmoothOpen F) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm k F :=
  h.forall k

/-- Scalar homogeneity of the `ℋ^k`-norm (the `SmoothOpen`-form used below). -/
theorem hkNorm_const_mulNgg (α : ℝ) (k : ℕ) (c : ℝ) {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) :
    HkNorm α k (fun z θ => c * F z θ) = |c| * HkNorm α k F :=
  Work.FTS.EllipticEst.HkNorm_const_mul α k c hF.forall

/-- `HkNorm` only sees the open quadrant: the `HkNorm`-congruence form of
`Work.FTS.EllipticEst.HkSq_congr_open`. -/
theorem hkNorm_congr_openNgg (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    HkNorm α k f = HkNorm α k g := by
  simp only [HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-! ## The one-level descents of `D_θ` and `D_z` -/

/-- **`D_θf` stays in `ℋ⁴` with `|D_θf|_{ℋ⁴} ≤ |f|_{ℋ⁶}`.**  The membership is
`IPGen.HkMem_Dth_le`, the norm bound is the chain
`HkSq α 4 (D_θf) ≤ HkSq α 5 f ≤ HkSq α 6 f` (`HkSq_Dth_le_ge`, `HkSq_mono_of_mem`). -/
theorem HkMem_HkNorm_Dth_le6 {α : ℝ} (hα : 0 < α) {f : Fn} (hsm : SmoothOpen f)
    (hmem : HkMem α 6 f) :
    HkMem α 4 (Dth f) ∧ HkNorm α 4 (Dth f) ≤ HkNorm α 6 f := by
  have h5 : HkMem α 5 f := Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem
  refine ⟨Work.FTS.IPGen.HkMem_Dth_le (by linarith : -(1 / 10 : ℝ) ≤ α) hsm h5, ?_⟩
  have h1 : HkSq α 4 (Dth f) ≤ HkSq α 5 f :=
    Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α (by linarith : -(1 / 10 : ℝ) ≤ α) 4 h5
  have h2 : HkSq α 5 f ≤ HkSq α 6 f := Work.FTS.StrongLWP.HkSq_mono_of_mem (by norm_num) hmem
  simp only [HkNorm]
  exact le_trans (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)

/-- **`D_zf` stays in `ℋ⁴` with `|D_zf|_{ℋ⁴} ≤ |f|_{ℋ⁶}`.**  The membership is
`IPGen.HkMem_Dz_le`, the norm bound is the chain
`HkSq α 4 (D_zf) ≤ HkSq α 5 f ≤ HkSq α 6 f` (`HkSq_Dz_le_Q0Sm`, `HkSq_mono_of_mem`). -/
theorem HkMem_HkNorm_Dz_le6 {α : ℝ} {f : Fn} (hsm : SmoothOpen f)
    (hmem : HkMem α 6 f) :
    HkMem α 4 (Dz f) ∧ HkNorm α 4 (Dz f) ≤ HkNorm α 6 f := by
  have h5 : HkMem α 5 f := Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem
  refine ⟨Work.FTS.IPGen.HkMem_Dz_le hsm h5, ?_⟩
  have h1 : HkSq α 4 (Dz f) ≤ HkSq α 5 f :=
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 4 (q0Sm_of_smoothOpenNgg hsm) h5
  have h2 : HkSq α 5 f ≤ HkSq α 6 f := Work.FTS.StrongLWP.HkSq_mono_of_mem (by norm_num) hmem
  simp only [HkNorm]
  exact le_trans (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)

/-! ## The level-three product estimate -/

/-- **The `ℋ³` product estimate.**  From two `ℋ⁴`-data `u`, `v` (interior `C^∞` and honest
`ℋ⁴`-membership) the product lies in `ℋ³` with
`|u v|_{ℋ³} ≤ C α^{-1/2}|u|_{ℋ⁴}|v|_{ℋ⁴}`: the level-four product rule
(`Work.FTS.OpenPkg.prod_field`) gives `ℋ⁴`-membership and the `ℋ⁴`-bound, and the `ℋ³`-norm is
dominated by the `ℋ⁴`-one. -/
theorem lvl3_mul_bound {C4 : ℝ}
    (hprod : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
      HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C4 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u v : Fn} (hu : HQo α 4 u) (hv : HQo α 4 v) :
    HkMem α 3 (fun z θ => u z θ * v z θ) ∧
    HkNorm α 3 (fun z θ => u z θ * v z θ)
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 u * HkNorm α 4 v := by
  obtain ⟨hmem4, hbnd⟩ := hprod α hα hα1 u v hu hv
  have hso : SmoothOpen (fun z θ => u z θ * v z θ) := smoothOpen_mulNgg hu.1 hv.1
  refine ⟨Work.FTS.OpenPkg.HkMem_mono_open hso 3 (by norm_num) hmem4, ?_⟩
  exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 4) (k' := 3)
    (by norm_num) hmem4) hbnd

/-! ## The target -/

private theorem smoothOpen_const_mul_loc (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hf ⊢
  have h : (Function.uncurry fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

theorem L3RhsNggBlock : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Ce M : ℝ) (f Φg : Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.EllPkgK α 6 Ce f Φg → Work.FTS.StrongPersist.H6Adm α f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NGgSum α f Φg)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NGgSum α f Φg) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NGgSum α f Φg)
        ≤ C * (1 + |Ce|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  obtain ⟨C4, hC4, hprod0⟩ := Work.FTS.OpenPkg.prod_field
  refine ⟨100 * (C4 + 1), 1 / 2, 1, by positivity, by norm_num, one_pos, ?_⟩
  intro α hαIoc Ce M f Φg hell hadm hM
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the elliptic residual coefficients
  set R : Fn := Work.Construction.Rop α (Work.Construction.PhiTil α f Φg) with hR
  set U : Fn := fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
    / Work.Construction.s2 θ with hU
  set V : Fn := Work.Construction.Vop (Work.Construction.PhiTil α f Φg) with hV
  have hR6 : HQo α 6 R := by rw [hR]; exact hell.R.1
  have hU6 : HQo α 6 U := by rw [hU]; exact hell.U.1
  have hV6 : HQo α 6 V := by rw [hV]; exact hell.V.1
  have hRb : HkNorm α 6 R ≤ Ce * HkNorm α 6 f := by rw [hR]; exact hell.R.2
  have hUb : HkNorm α 6 U ≤ Ce * HkNorm α 6 f := by rw [hU]; exact hell.U.2
  have hVb : HkNorm α 6 V ≤ Ce * HkNorm α 6 f := by rw [hV]; exact hell.V.2
  -- the datum `f`
  have hfso : SmoothOpen f := hadm.reg.1
  have hfmem6 : HkMem α 6 f := hadm.reg.2
  have hfmem4 : HkMem α 4 f := Work.FTS.OpenPkg.HkMem_mono_open hfso 4 (by norm_num) hfmem6
  have hXn4f : HkNorm α 4 f ≤ M := hM
  have hN6nn : (0 : ℝ) ≤ HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hMnn : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXn4f
  -- descent to level four
  have hR4 : HQo α 4 R := ⟨hR6.1, Work.FTS.OpenPkg.HkMem_mono_open hR6.1 4 (by norm_num) hR6.2⟩
  have hU4 : HQo α 4 U := ⟨hU6.1, Work.FTS.OpenPkg.HkMem_mono_open hU6.1 4 (by norm_num) hU6.2⟩
  have hV4 : HQo α 4 V := ⟨hV6.1, Work.FTS.OpenPkg.HkMem_mono_open hV6.1 4 (by norm_num) hV6.2⟩
  have hf4 : HQo α 4 f := ⟨hfso, hfmem4⟩
  have hXn4R : HkNorm α 4 R ≤ Ce * HkNorm α 6 f :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hR6.2) hRb
  have hXn4U : HkNorm α 4 U ≤ Ce * HkNorm α 6 f :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hU6.2) hUb
  have hXn4V : HkNorm α 4 V ≤ Ce * HkNorm α 6 f :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hV6.2) hVb
  -- the elliptic derivative slots of `f`
  obtain ⟨hDthmem, hDthb⟩ := HkMem_HkNorm_Dth_le6 hα hfso hfmem6
  obtain ⟨hDzmem, hDzb⟩ := HkMem_HkNorm_Dz_le6 hfso hfmem6
  have hDth4 : HQo α 4 (Dth f) := ⟨hfso.Dth, hDthmem⟩
  have hDz4 : HQo α 4 (Dz f) := ⟨hfso.Dz, hDzmem⟩
  -- `A`-bookkeeping
  set A : ℝ := 1 + |Ce| with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg Ce]
  have hCenn : Ce ≤ A := by rw [hA]; linarith [le_abs_self Ce]
  have hRA : HkNorm α 4 R ≤ A * HkNorm α 6 f :=
    le_trans hXn4R (mul_le_mul_of_nonneg_right hCenn hN6nn)
  have hUA : HkNorm α 4 U ≤ A * HkNorm α 6 f :=
    le_trans hXn4U (mul_le_mul_of_nonneg_right hCenn hN6nn)
  have hVA : HkNorm α 4 V ≤ A * HkNorm α 6 f :=
    le_trans hXn4V (mul_le_mul_of_nonneg_right hCenn hN6nn)
  -- the three products
  set P1 : Fn := fun z θ => R z θ * f z θ with hP1
  set P2 : Fn := fun z θ => U z θ * Dth f z θ with hP2
  set P3 : Fn := fun z θ => V z θ * Dz f z θ with hP3
  set G1 : Fn := fun z θ => 2 * P1 z θ with hG1
  set G2 : Fn := fun z θ => -2 * P2 z θ with hG2
  set G3 : Fn := fun z θ => (-2 * α) * P3 z θ with hG3
  set Gsum : Fn := fun z θ => G1 z θ + G2 z θ + G3 z θ with hGsum
  have hP1so : SmoothOpen P1 := by rw [hP1]; exact smoothOpen_mulNgg hR6.1 hfso
  have hP2so : SmoothOpen P2 := by rw [hP2]; exact smoothOpen_mulNgg hU6.1 hfso.Dth
  have hP3so : SmoothOpen P3 := by rw [hP3]; exact smoothOpen_mulNgg hV6.1 hfso.Dz
  have hG1so : SmoothOpen G1 := by rw [hG1]; exact smoothOpen_const_mul_loc 2 hP1so
  have hG2so : SmoothOpen G2 := by
    rw [hG2]; exact smoothOpen_const_mul_loc (-2) hP2so
  have hG3so : SmoothOpen G3 := by
    rw [hG3]; exact smoothOpen_const_mul_loc (-2 * α) hP3so
  have hp1 := lvl3_mul_bound hprod0 hα hα1 hR4 hf4
  have hp2 := lvl3_mul_bound hprod0 hα hα1 hU4 hDth4
  have hp3 := lvl3_mul_bound hprod0 hα hα1 hV4 hDz4
  have hP1mem : HkMem α 3 P1 := by rw [hP1]; exact hp1.1
  have hP2mem : HkMem α 3 P2 := by rw [hP2]; exact hp2.1
  have hP3mem : HkMem α 3 P3 := by rw [hP3]; exact hp3.1
  have hP1bnd : HkNorm α 3 P1
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 R * HkNorm α 4 f := by rw [hP1]; exact hp1.2
  have hP2bnd : HkNorm α 3 P2
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 U * HkNorm α 4 (Dth f) := by
    rw [hP2]; exact hp2.2
  have hP3bnd : HkNorm α 3 P3
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 V * HkNorm α 4 (Dz f) := by
    rw [hP3]; exact hp3.2
  have hG1mem : HkMem α 3 G1 := by
    rw [hG1]; exact Work.FTS.LocData.HkMem_const_mul α 3 2 hP1mem
  have hG2mem : HkMem α 3 G2 := by
    rw [hG2]; exact Work.FTS.LocData.HkMem_const_mul α 3 (-2) hP2mem
  have hG3mem : HkMem α 3 G3 := by
    rw [hG3]; exact Work.FTS.LocData.HkMem_const_mul α 3 (-2 * α) hP3mem
  -- the three block bounds
  have hb1 : HkNorm α 3 G1 ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M) := by
    rw [hG1, hkNorm_const_mulNgg α 3 2 hP1so, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    refine le_trans hP1bnd ?_
    have hstep : HkNorm α 4 R * HkNorm α 4 f ≤ A * HkNorm α 6 f * M :=
      mul_le_mul hRA hXn4f (Work.Spaces.HkNorm_nonneg α 4 f)
        (mul_nonneg hAnn hN6nn)
    calc C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 R * HkNorm α 4 f
        = C4 * α ^ (-(1 / 2 : ℝ)) * (HkNorm α 4 R * HkNorm α 4 f) := by ring
      _ ≤ C4 * α ^ (-(1 / 2 : ℝ)) * (A * HkNorm α 6 f * M) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC4.le (Real.rpow_nonneg hα.le _))
      _ = C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M := by ring
  have hb2 : HkNorm α 3 G2 ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
    rw [hG2, hkNorm_const_mulNgg α 3 (-2) hP2so, show |(-2 : ℝ)| = 2 by norm_num]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    refine le_trans hP2bnd ?_
    have hstep : HkNorm α 4 U * HkNorm α 4 (Dth f) ≤ A * HkNorm α 6 f * HkNorm α 6 f :=
      mul_le_mul hUA hDthb (Work.Spaces.HkNorm_nonneg α 4 (Dth f)) (mul_nonneg hAnn hN6nn)
    calc C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 U * HkNorm α 4 (Dth f)
        = C4 * α ^ (-(1 / 2 : ℝ)) * (HkNorm α 4 U * HkNorm α 4 (Dth f)) := by ring
      _ ≤ C4 * α ^ (-(1 / 2 : ℝ)) * (A * HkNorm α 6 f * HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC4.le (Real.rpow_nonneg hα.le _))
      _ = C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f := by ring
  have hb3 : HkNorm α 3 G3 ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
    rw [hG3, hkNorm_const_mulNgg α 3 (-2 * α) hP3so,
      show |(-2 * α : ℝ)| = 2 * α by
        rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]; ring]
    have hP3bnd' : HkNorm α 3 P3
        ≤ C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f := by
      refine le_trans hP3bnd ?_
      have hstep : HkNorm α 4 V * HkNorm α 4 (Dz f) ≤ A * HkNorm α 6 f * HkNorm α 6 f :=
        mul_le_mul hVA hDzb (Work.Spaces.HkNorm_nonneg α 4 (Dz f)) (mul_nonneg hAnn hN6nn)
      calc C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 V * HkNorm α 4 (Dz f)
          = C4 * α ^ (-(1 / 2 : ℝ)) * (HkNorm α 4 V * HkNorm α 4 (Dz f)) := by ring
        _ ≤ C4 * α ^ (-(1 / 2 : ℝ)) * (A * HkNorm α 6 f * HkNorm α 6 f) :=
            mul_le_mul_of_nonneg_left hstep (mul_nonneg hC4.le (Real.rpow_nonneg hα.le _))
        _ = C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f := by ring
    have hαr : α * α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(1 / 2 : ℝ)) := by
      have h1 : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
        have h := Real.rpow_add hα 1 (-(1 / 2))
        rw [Real.rpow_one] at h
        rw [← h]
        congr 1
        norm_num
      rw [h1]
      exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
    have h0 : (0 : ℝ) ≤ 2 * C4 * A * HkNorm α 6 f * HkNorm α 6 f := by positivity
    have hkey : 2 * α * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f)
        ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
      have h2 := mul_le_mul_of_nonneg_left hαr h0
      linarith [h2]
    calc 2 * α * HkNorm α 3 P3
        ≤ 2 * α * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hP3bnd' (by linarith)
      _ ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := hkey
  -- the sum of the three blocks
  have hG12so : SmoothOpen (fun z θ => G1 z θ + G2 z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hG1so hG2so
  have hG12mem : HkMem α 3 (fun z θ => G1 z θ + G2 z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hG1so hG2so hG1mem hG2mem
  have hG12bnd : HkNorm α 3 (fun z θ => G1 z θ + G2 z θ)
      ≤ Real.sqrt 2 * (HkNorm α 3 G1 + HkNorm α 3 G2) :=
    Work.FTS.EllipticEst.HkNorm_add_le α 3 hG1so.forall hG2so.forall hG1mem hG2mem
  have hGsummem : HkMem α 3 Gsum := by
    rw [hGsum]; exact Work.FTS.EllipticEst.HkMem_add_open hG12so hG3so hG12mem hG3mem
  have hGsum_bnd : HkNorm α 3 Gsum
      ≤ Real.sqrt 2 * (HkNorm α 3 (fun z θ => G1 z θ + G2 z θ) + HkNorm α 3 G3) := by
    rw [hGsum]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 hG12so.forall hG3so.forall hG12mem hG3mem
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsum : HkNorm α 3 Gsum
      ≤ 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M)
        + 8 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
    nlinarith [hGsum_bnd, hG12bnd, hb1, hb2, hb3, hsqrt2, hsq2,
      Work.Spaces.HkNorm_nonneg α 3 G1, Work.Spaces.HkNorm_nonneg α 3 G2,
      Work.Spaces.HkNorm_nonneg α 3 G3, Real.sqrt_nonneg 2]
  -- the final arithmetic
  have hN4nn : (0 : ℝ) ≤ HkNorm α 6 f := hN6nn
  have hfinal : HkNorm α 3 Gsum
      ≤ 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2 := by
    have hA4 : A ≤ A ^ 4 := by
      have h3 : (1 : ℝ) ≤ A ^ 3 := one_le_pow₀ hA1 (n := 3)
      calc A = A * 1 := by ring
        _ ≤ A * A ^ 3 := mul_le_mul_of_nonneg_left h3 hAnn
        _ = A ^ 4 := by ring
    have hM4 : (1 + M) ≤ (1 + M) ^ 4 := by
      have h1 : (1 : ℝ) ≤ 1 + M := by linarith
      have h3 : (1 : ℝ) ≤ (1 + M) ^ 3 := one_le_pow₀ h1 (n := 3)
      calc (1 + M) = (1 + M) * 1 := by ring
        _ ≤ (1 + M) * (1 + M) ^ 3 := mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = (1 + M) ^ 4 := by ring
    have hM2 : M + 2 * HkNorm α 6 f ≤ 3 * ((1 + M) * (1 + HkNorm α 6 f)) := by
      nlinarith [hMnn, hN6nn]
    have hNN : HkNorm α 6 f * (1 + HkNorm α 6 f) ≤ (1 + HkNorm α 6 f) ^ 2 := by
      nlinarith [hN6nn]
    have hKnn : (0 : ℝ) ≤ C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f := by positivity
    have hXnn : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have s1 : 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M)
          + 8 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f)
        = 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f) := by
      ring
    have s2 : 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f)
        ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f))) := by
      calc 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f)
          ≤ 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f)
              * (3 * ((1 + M) * (1 + HkNorm α 6 f))) :=
            mul_le_mul_of_nonneg_left hM2 (by positivity)
        _ = 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A)
              * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f))) := by ring
    have s3 : 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f)))
        ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hNN (by linarith : (0 : ℝ) ≤ 1 + M))
        (by positivity)
    have s4 : 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2)
        ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4)
            * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := by
      have h1 : A * (1 + M) ≤ A ^ 4 * (1 + M) ^ 4 :=
        mul_le_mul hA4 hM4 (by linarith) (by positivity)
      have h0 : (0 : ℝ) ≤ 12 * C4 * α ^ (-(1 / 2 : ℝ)) := by positivity
      calc 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2)
          = 12 * C4 * α ^ (-(1 / 2 : ℝ)) * (A * (1 + M)) * (1 + HkNorm α 6 f) ^ 2 := by ring
        _ ≤ 12 * C4 * α ^ (-(1 / 2 : ℝ)) * (A ^ 4 * (1 + M) ^ 4)
              * (1 + HkNorm α 6 f) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h0) (by positivity)
        _ = 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4)
              * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := by ring
    have s5 : 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4) * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2)
        ≤ 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4
            * (1 + HkNorm α 6 f) ^ 2 := by
      have hc : 12 * C4 ≤ 100 * (C4 + 1) := by linarith
      have h0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) * A ^ 4 * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2 := by
        positivity
      calc 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4) * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2)
          = (12 * C4) * (α ^ (-(1 / 2 : ℝ)) * A ^ 4 * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := by
            ring
        _ ≤ (100 * (C4 + 1))
              * (α ^ (-(1 / 2 : ℝ)) * A ^ 4 * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) :=
            mul_le_mul_of_nonneg_right hc h0
        _ = 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4
              * (1 + HkNorm α 6 f) ^ 2 := by ring
    calc HkNorm α 3 Gsum
        ≤ 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M)
          + 8 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := hsum
      _ = 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f) := s1
      _ ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A)
            * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f))) := s2
      _ ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2) := s3
      _ ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4)
            * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := s4
      _ ≤ 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4
            * (1 + HkNorm α 6 f) ^ 2 := s5
  -- transfer from `Gsum` to `NGgSum`
  have hEqOn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      NGgSum α f Φg z θ = Gsum z θ := by
    intro z θ hz hθ hθ2
    have hsin : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    have hkey : (Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
          / (Real.sin (2 * θ)))
          * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)
        = Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
          * Work.Spaces.pth f z θ := by
      rw [← mul_assoc, div_mul_cancel₀ _ hsin]
    simp only [NGgSum, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N3gg,
      Work.FTS.Nonlin.PhiTg, hR, hU, hV, hP1, hP2, hP3, hG1, hG2, hG3, hGsum,
      Work.Spaces.Dth, Work.Construction.s2_eq]
    rw [hkey]
    ring
  have hmemN : HkMem α 3 (NGgSum α f Φg) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 3)
      (u := Gsum) (v := NGgSum α f Φg) hGsummem
      (fun z hz θ hθ => (hEqOn z θ hz hθ.1 hθ.2).symm)
  have hnormN : HkNorm α 3 (NGgSum α f Φg) = HkNorm α 3 Gsum :=
    hkNorm_congr_openNgg α 3 (fun z θ hz hθ hθ2 => hEqOn z θ hz hθ hθ2)
  have hGsumso : SmoothOpen Gsum := by
    rw [hGsum]
    exact Work.FTS.EllipticEst.smoothOpen_add
      (Work.FTS.EllipticEst.smoothOpen_add hG1so hG2so) hG3so
  have hcont : ContDiffOn ℝ 3 (Function.uncurry (NGgSum α f Φg)) Work.FTS.EllipticEst.Q0 :=
    (hGsumso.forall 3).congr (fun p hp => by
      have hp' := hp
      rw [Work.FTS.EllipticEst.mem_Q0] at hp'
      exact hEqOn p.1 p.2 hp'.1 hp'.2.1 hp'.2.2)
  refine ⟨hcont, hmemN, ?_⟩
  rw [hnormN]
  have hfin := hfinal
  rw [hA] at hfin
  exact hfin

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock =====
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
set_option linter.unusedVariables false

theorem L3RhsNstarBlock : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn) (μ lam M : ℝ),
    Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
    |μ| ≤ 1 / 2 → |lam| ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Nstar μ lam f) ∧
    Work.Spaces.HkMem α 3 (Work.Construction.Nstar μ lam f) ∧
    Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f) ≤ C * (1 + M) := by
  refine ⟨5 * Real.sqrt 2 / 2, ?_, ?_⟩
  · have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    linarith
  · intro α hα f μ lam M hf hM hμ hlam
    have hα0 : 0 < α := hα.1
    -- the regularity of the datum
    have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
    have hmem6 : Work.Spaces.HkMem α 6 f := hf.reg.2
    have hmem4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem6
    have hmem3 : Work.Spaces.HkMem α 3 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm 3 (by norm_num) hmem6
    have hQ0Sm4 : Work.FTS.CoercivityFix.Transfer.Q0Sm 4 f := hsm.forall 4
    -- `D_z f` is in `ℋ³` (the index shift)
    have hmem3Dz : Work.Spaces.HkMem α 3 (Work.Spaces.Dz f) :=
      (Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm α hα0 3 hQ0Sm4 hmem4).2.2
    have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := hsm.Dz
    -- the two summands of `N_*`
    have hsmA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-μ) * f z θ) :=
      Work.FTS.EllipticEst.smoothOpen_const_mul' (-μ) hsm
    have hsmB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ) :=
      Work.FTS.EllipticEst.smoothOpen_const_mul' _ hsmDz
    have hmA : Work.Spaces.HkMem α 3 (fun z θ => (-μ) * f z θ) :=
      Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of (-μ) hmem3
    have hmB : Work.Spaces.HkMem α 3
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ) :=
      Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of _ hmem3Dz
    -- the decomposition `N_* = A + B`
    have hsum : (fun z θ => (-μ) * f z θ
          + (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ)
        = Work.Construction.Nstar μ lam f := by
      funext z θ
      simp only [Work.Construction.Nstar]
      ring
    have hsmN : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Nstar μ lam f) := by
      rw [← hsum]
      exact Work.FTS.EllipticEst.smoothOpen_add hsmA hsmB
    have hmN : Work.Spaces.HkMem α 3 (Work.Construction.Nstar μ lam f) := by
      rw [← hsum]
      exact Work.FTS.EllipticEst.HkMem_add_open hsmA hsmB hmA hmB
    refine ⟨hsmN, hmN, ?_⟩
    -- the norm bound
    have hXn : Work.Spaces.HkNorm α 4 f ≤ M := hM
    have hMnn : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXn
    have hN01 : Work.Spaces.HkNorm α 3 f ≤ Work.Spaces.HkNorm α 4 f := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt
        (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem4)
    have hN0Dz : Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f) ≤ Work.Spaces.HkNorm α 4 f := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt
        (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 3 hQ0Sm4 hmem4)
    have hnormA : Work.Spaces.HkNorm α 3 (fun z θ => (-μ) * f z θ)
        = |μ| * Work.Spaces.HkNorm α 3 f := by
      have heq : (fun z θ => (-μ) * f z θ) = (-μ) • f := by
        funext z θ; simp
      rw [heq, Work.FTS.EllipticEst.HkNorm_smul]
      simp
    have hnormB : Work.Spaces.HkNorm α 3
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ)
        = |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f) := by
      have heq : (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ)
          = (-(μ + lam + μ * lam)) • Work.Spaces.Dz f := by
        funext z θ; simp
      rw [heq, Work.FTS.EllipticEst.HkNorm_smul, abs_neg]
    have hmain : Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f)
        ≤ Real.sqrt 2 * (|μ| * Work.Spaces.HkNorm α 3 f
            + |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f)) := by
      rw [← hsum]
      have h := Work.FTS.EllipticEst.HkNorm_add_le α 3
        (fun n => hsmA.forall n) (fun n => hsmB.forall n) hmA hmB
      rw [hnormA, hnormB] at h
      exact h
    -- the coefficient bounds
    have hcoef : |μ + lam + μ * lam| ≤ 2 := by
      have h1 : |μ| ≤ 1 / 2 := hμ
      have h2 : |lam| ≤ 1 := hlam
      have h3 : |μ * lam| ≤ 1 / 2 := by
        rw [abs_mul]; nlinarith [abs_nonneg μ, abs_nonneg lam]
      calc |μ + lam + μ * lam| ≤ |μ + lam| + |μ * lam| := abs_add_le _ _
        _ ≤ (|μ| + |lam|) + |μ * lam| := by linarith [abs_add_le μ lam]
        _ ≤ 2 := by linarith
    have hfin : Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f)
        ≤ 5 * Real.sqrt 2 / 2 * (1 + M) := by
      have h1 : Real.sqrt 2 * (|μ| * Work.Spaces.HkNorm α 3 f
            + |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f))
          ≤ Real.sqrt 2 * ((1 / 2) * Work.Spaces.HkNorm α 4 f
            + 2 * Work.Spaces.HkNorm α 4 f) := by
        have hA : |μ| * Work.Spaces.HkNorm α 3 f ≤ (1 / 2) * Work.Spaces.HkNorm α 4 f := by
          have h0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 3 f := Work.Spaces.HkNorm_nonneg α 3 f
          nlinarith [hN01, hμ, Work.Spaces.HkNorm_nonneg α 4 f]
        have hB : |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f)
            ≤ 2 * Work.Spaces.HkNorm α 4 f := by
          have h0 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f) :=
            Work.Spaces.HkNorm_nonneg α 3 (Work.Spaces.Dz f)
          nlinarith [hN0Dz, hcoef, Work.Spaces.HkNorm_nonneg α 4 f]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
      have h2 : Real.sqrt 2 * ((1 / 2) * Work.Spaces.HkNorm α 4 f
            + 2 * Work.Spaces.HkNorm α 4 f)
          ≤ Real.sqrt 2 * ((5 / 2) * M) := by
        have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h3 : (1 / 2) * Work.Spaces.HkNorm α 4 f + 2 * Work.Spaces.HkNorm α 4 f
            = (5 / 2) * Work.Spaces.HkNorm α 4 f := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left (by linarith) hs2
      calc Work.Spaces.HkNorm α 3 (Work.Construction.Nstar μ lam f)
          ≤ Real.sqrt 2 * (|μ| * Work.Spaces.HkNorm α 3 f
              + |μ + lam + μ * lam| * Work.Spaces.HkNorm α 3 (Work.Spaces.Dz f)) := hmain
        _ ≤ Real.sqrt 2 * ((1 / 2) * Work.Spaces.HkNorm α 4 f
              + 2 * Work.Spaces.HkNorm α 4 f) := h1
        _ ≤ Real.sqrt 2 * ((5 / 2) * M) := h2
        _ = 5 * Real.sqrt 2 / 2 * M := by ring
        _ ≤ 5 * Real.sqrt 2 / 2 * (1 + M) := by
            have h5 : (0 : ℝ) ≤ 5 * Real.sqrt 2 / 2 := by positivity
            nlinarith [hMnn, Real.sqrt_nonneg 2]
    exact hfin

end Work.FTS.StrongPersist.L3Rhs
end
end
