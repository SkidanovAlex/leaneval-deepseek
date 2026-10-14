import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Final.Small
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.GalFields.RHS.SharpAux.Defs
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.RegPkgGal.GalMinAssembly
import Submission.Work.FTS.RegPkgGal.GalMinConv
import Submission.Work.FTS.RegPkgGal.PartsAssembly
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.AngProfAll
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.Top.Main
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_FinalLeaves.mu6_proved
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_aux
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.FinalV2.Adapter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.Adapter` — PROVED (curric-46 lead install, 2026-10-10)

`exists_blowupAt_of_inputs'`: `∃ α, Inputs' α` gives the blow-up. The firing
(`FireFix.blowupAtTop_of_regPkg'`) runs on `extG G` with `Φ := psiFire Φs E G`, where
`G := tauExt g` is the right-Taylor τ-extension of the strong solution `g` (REVIEW FIX-2); every
conjunct of `Inputs'` is applied at `G` through `sol_dynOK'_tauExt`. Old conjunct (11) is proved
here (`dynOK_extG` + `diffAt2_merProfile`); (12), (13) are no longer inputs.

`theorem_1_of_inputs'` is `Final.Wire.theorem_1_of_inputs` re-pointed at `Inputs'`.

**RegExport REVIEW F1 (2026-10-10).** (7″) is applied at `G = tauExt g₁` with `hdat` from the (4′)
initial-value clause (+ `tauExt_of_nonneg`), and the firing runs on the SANITISED `extG (gS α G)`;
`hsmall` is transported by `extG_gS_of_mem`, `hMer`/`hW` by `merProfile_gS`, `hHid` by
`physOmega_gS` (`FinalV2.Sanitize`). `hPsi`, `ClockData` are untouched.

**StreamBdry REVIEW FIX-A (2026-10-10).** (9″) is applied at `G := gS α g` with `hRegG` and
`hG` by `simp [gS]`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

theorem exists_blowupAt_of_inputs' (h : ∃ α : ℝ, Inputs' α) :
    ∃ α : ℝ≥0, 0 < (α : ℝ) ∧ Nonempty (Work.FTS.Top.BlowupAt α 1) := by
  obtain ⟨α, hα, hα13, hpress, core⟩ := h
  obtain ⟨Ce, Cs, Cg, C₀, K, ρ, E, Φs, _hCe, hCg, hC₀, hK, hscale, _hρ, _hEll, _hEL, _hML,
    _hMLip, _hStar, hEps, hDat, hDyn, hSup, hMu, hReg, hMer, hHid, hPsi⟩ := core
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the datum
  obtain ⟨L₀, _hL₀, hL⟩ := Work.FTS.LocData6.locG6_data (pExp α) hαG hαG1 K hK
  obtain ⟨β, _hβ, _hAdm, hRegQ, _hGal, hL12, hXn4₀, hXn6₀⟩ := hL (max L₀ 1) (le_max_left _ _)
  have hU := hEps K (Work.FTS.LocData6.locG6 (pExp α) (max L₀ 1) β)
      hRegQ (locG6_vanish hαG _ _) (hDat (max L₀ 1) β (le_max_right _ _) hRegQ hL12) hXn4₀ hXn6₀
  obtain ⟨g₁, hSol₁, hinit₁, hOK₁⟩ := hDyn (Work.FTS.LocData6.locG6 (pExp α) (max L₀ 1) β) K hU
  -- REVIEW FIX-2: work with the right-Taylor τ-extension `g := tauExt g₁`
  set g : Fam := tauExt g₁ with hgdef
  obtain ⟨hSol, hOK⟩ := sol_dynOK'_tauExt hSol₁ hOK₁
  have hdat : ∃ L β' : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β' z θ :=
    ⟨max L₀ 1, β, le_max_right _ _, fun z θ => by
      show tauExt g₁ z θ 0 = _
      rw [tauExt_of_nonneg _ le_rfl]
      exact hinit₁ z θ⟩
  have hRegG := hReg g hSol hOK hdat
  rw [hgdef, tauExt_tauExt, ← hgdef] at hRegG
  -- the clock
  obtain ⟨hμ, hc, _hμh⟩ := hMu g hSol hOK
  set m : ℝ → ℝ := maxMu (pExp α) (PsiCan Φs E g) g with hm
  have hcm : Continuous m := continuous_maxExt hc
  have hmb : MuBound m := maxExt_bound hμ
  set C : PhysClock := physClockOf m hcm hmb with hC
  set A : ℝ → ℝ := ampA m with hA
  set B : ℝ → ℝ := ampB m with hB
  have hCmuA : C.mu = m := rfl
  have hClock : ClockData (pExp α) (PsiCan Φs E g) g A B C := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hCmuA, hm, maxMu, max_eq_left hτ]
    · intro τ hτ
      rw [hA]
      rfl
    · intro τ hτ
      rw [hA, hCmuA]
      simpa only [ampA] using Avort_hasDerivAt hcm τ
    · intro τ hτ
      rw [hB, hCmuA]
      have h := hasDerivAt_Bdyn_of_clock m hcm hmb 1 τ
      rw [physClockOf_mu] at h
      simpa only [ampB, one_mul] using h
    · intro τ hτ
      rw [hB]
      simpa only [ampB] using Bdyn_pos m τ
  -- the smallness of the extension
  have hsmall : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |extG g z θ τ| ≤ 3 * α / 200 := by
    intro τ hτ z hz θ hθ
    have h1 := hSup g hOK τ hτ z hz θ hθ
    have hkey : Cg * C₀ * (9 * α) ≤ 3 / 200 := by
      have h1' : (α * (600 * Cg * C₀)) * (1 / 200 : ℝ) ≤ 1 * (1 / 200 : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (by norm_num)
      nlinarith [h1', hα, hCg, hC₀.le]
    have h3 : Cg * (C₀ * (pExp α) ^ 2) ≤ 3 * α / 200 := by
      rw [Work.FTS.Regularity.pExp_eq]
      have h : Cg * (C₀ * (3 * α) ^ 2) = α * (Cg * C₀ * (9 * α)) := by ring
      rw [h]
      calc α * (Cg * C₀ * (9 * α)) ≤ α * (3 / 200) := mul_le_mul_of_nonneg_left hkey hα.le
        _ = 3 * α / 200 := by ring
    exact le_trans h1 h3
  -- the D²-clause, now PROVED for the extension (was conjunct (11))
  have hOKe : DynOK (pExp α) C₀ (extG g) := Work.FTS.Final.ExtG.dynOK_extG hαG hOK.1
  have hW : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2 (fun r z => Work.FTS.Physical.merProfile α A B (extG g) C r z t) r z :=
    fun t ht r z hr hz =>
      Work.FTS.Final.Recon.diffAt2_merProfile (g := extG g) (A := A) (B := B) (C := C)
        hOKe.1.c4 (fun τ hτ => hClock.2.2.2.2 τ hτ) ht hr hz
  -- transport to the sanitised family (RegExport REVIEW F1)
  have hsmallS : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |extG (gS α g) z θ τ| ≤ 3 * α / 200 := by
    intro τ hτ z hz θ hθ
    rw [extG_gS_of_mem α g hθ.1 hθ.2]
    exact hsmall τ hτ z hz θ hθ
  have hMerS := hMer g A B C hSol hOK hClock
  rw [← merProfile_gS α A B g C] at hMerS
  have hGS : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → gS α g z θ τ = g z θ τ :=
    fun z θ τ hz hθ _ => by simp [gS, hz, hθ.1, hθ.2]
  have hHidS := hHid g (gS α g) A B C hSol hOK hClock hRegG hGS
  simp only [← physOmega_gS α A B g C] at hHidS
  have hWS : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2
        (fun r z => Work.FTS.Physical.merProfile α A B (extG (gS α g)) C r z t) r z := by
    rw [merProfile_gS α A B g C]
    exact hW
  -- the firing on `extG (gS α g)` with `Φ := psiFire Φs E g`, then the rescale
  exact ⟨⟨α, hα.le⟩, hα, ⟨Work.FTS.Top.blowupAt_one_of_blowupAt
    (Work.FTS.FireFix.blowupAtTop_of_regPkg' (α := ⟨α, hα.le⟩) (A := A) (B := B)
      (g := extG (gS α g)) (C := C) (Φ := psiFire Φs E g)
      (hRegG) hClock.2.1 hsmallS Work.FTS.BSSwirl.biotSavartSwirl hpress
      hMerS hHidS (hPsi g A B C hSol hOK hClock) hWS)⟩⟩

open FiniteTimeSingularity Gradient Matrix MeasureTheory in
/-- **The challenge statement from the corrected bundle** (`Final.Wire.theorem_1_of_inputs`
re-pointed at `Inputs'`; same conclusion, character for character). -/
theorem theorem_1_of_inputs' (h : ∃ α : ℝ, Inputs' α) :
    ∃ β > 0, ∃ u₀ : Work.FTS.Top.R3 → Work.FTS.Top.R3, div u₀ = 0 ∧ IsOdd u₀ ∧
      IsContDiffHolder ℝ β u₀ ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : Work.FTS.Top.R3, ‖vorticity u₀ x‖ ≤ C / (‖x‖ ^ (β : ℝ) + 1)) ∧
        ∃ p : Work.FTS.Top.R3 → ℝ → ℝ, ∃ u : Work.FTS.Top.R3 → ℝ → Work.FTS.Top.R3,
            (∀ t ∈ Set.Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Set.Ioo 0 1,
                IsContDiffHolderOn ℝ β u.uncurry (Set.univ ×ˢ Set.Icc 0 T)) ∧
                Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => u y s) x‖)
                  (𝓝[<] 1) Filter.atTop := by
  obtain ⟨α, hα, ⟨B⟩⟩ := exists_blowupAt_of_inputs' h
  exact Work.FTS.Top.theorem_1_of_blowupAt hα B

end Work.FTS.FinalV2
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpAux.WlInfTermsAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `Xn` is monotone in the order: `|f|_{ℋ⁴} ≤ |f|_{ℋ⁵}` for honest `f`. -/
theorem Xn_le_Xn5_aux {α : ℝ} {f : Fn} (h5 : Work.Spaces.HkMem α 5 f) :
    Work.FTS.Nonlin.Xn α f ≤ Work.FTS.GalFields.Xn5 α f :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) h5)

/-- **The `𝒲^{4,∞}`-product rule in the shape used by the ten terms**: a coefficient `f` priced by
the `𝒲^{4,∞}`-norm `Cw` times an honest `u` carrying `B·|h|_{ℋ⁵}`, scaled by `a`, is honest in
`ℋ⁴` with `|·|_{ℋ⁴} ≤ |a|·Ci·α^{-1/2}·Cw·B·|h|_{ℋ⁵}`. -/
theorem wl_term_bound {α α₂ Ci : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) {f u h : Fn}
    (hfS : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    (huS : Work.FTS.EllipticEst.SmoothOpen u) (hu : Work.Spaces.HkMem α 4 u)
    {Cw B : ℝ} (hCw : Work.Spaces.WlInf α 4 f ≤ Cw)
    (huX : Work.FTS.Nonlin.Xn α u ≤ B * Work.FTS.GalFields.Xn5 α h) (a : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a * (f z θ * u z θ)) ∧
      Work.Spaces.HkMem α 4 (fun z θ => a * (f z θ * u z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a * (f z θ * u z θ))
        ≤ |a| * (Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B) * Work.FTS.GalFields.Xn5 α h := by
  obtain ⟨hmem, hbd⟩ :=
    Work.FTS.GalFields.RHS.Sharp.Xn_mul_wlInf hN hα hαα₂ hfS hfm huS hu hCw huX
  have hXeq : Work.FTS.Nonlin.Xn α (fun z θ => a * (f z θ * u z θ))
      = |a| * Work.FTS.Nonlin.Xn α (fun z θ => f z θ * u z θ) :=
    Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α a (fun z θ => f z θ * u z θ)
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.NonlinRows.smoothOpen_const_mul a
      (Work.FTS.NonlinRows.smoothOpen_mul hfS huS)
  · exact Work.FTS.LocData.HkMem_const_mul α 4 a hmem
  · rw [hXeq]
    calc |a| * Work.FTS.Nonlin.Xn α (fun z θ => f z θ * u z θ)
        ≤ |a| * (Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B * Work.FTS.GalFields.Xn5 α h) :=
          mul_le_mul_of_nonneg_left hbd (abs_nonneg a)
      _ = |a| * (Ci * α ^ (-(1 / 2 : ℝ)) * Cw * B) * Work.FTS.GalFields.Xn5 α h := by ring

/-- **Multiplication by `sin²θ`**: the angular multiple `sin²θ·u` of an honest `ℋ⁴`-function `u`
is honest, with `|sin²θ·u|_{ℋ⁴} ≤ B·Ci·Bu·|h|_{ℋ⁵}` whenever `|u|_{ℋ⁴} ≤ Bu·|h|_{ℋ⁵}`.

The proof is the rescaling trick of row 24: the angular profile `-sin²θ` (with iteration constants
`B`) is scaled by `c = Ci/B`, so that its `L^∞`-data fits the `Ci`-budget of `N4Norm'.angmul`; the
scaling is undone with `Xn_const_mul`, and `c^{-1}·Ci² = B·Ci`. -/
theorem sinSq_mul_bound {α α₂ Ci B Bu : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) (hBpos : 0 < B)
    (hSI : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => -((Real.sin θ) ^ 2)))
    (hbnd : ∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ) ^ 2))| ≤ B)
    (hdth : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ) ^ 2)) 0 θ|
        ≤ B * Real.sin (2 * θ))
    {u h : Fn} (huS : Work.FTS.EllipticEst.SmoothOpen u) (hu : Work.Spaces.HkMem α 4 u)
    (huX : Work.FTS.Nonlin.Xn α u ≤ Bu * Work.FTS.GalFields.Xn5 α h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * u z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ => Real.sin θ ^ 2 * u z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Real.sin θ ^ 2 * u z θ)
        ≤ (B * Ci * Bu) * Work.FTS.GalFields.Xn5 α h := by
  have hCi : 0 < Ci := hN.pos.1
  have hCine : Ci ≠ 0 := ne_of_gt hCi
  have hBne : B ≠ 0 := ne_of_gt hBpos
  set c : ℝ := Ci / B with hc
  have hcpos : 0 < c := by rw [hc]; exact div_pos hCi hBpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcB : c * B = Ci := by rw [hc]; field_simp
  have hcore := Work.FTS.Nonlinear.Open.Row24Aux.angMulScaledOpen hN hBpos hcB hSI hbnd hdth
    huS hu ⟨hα, hαα₂⟩
  have hkey : (fun z θ => Real.sin θ ^ 2 * u z θ)
      = fun z θ => (1 / (-c)) * (c * (-(Real.sin θ ^ 2)) * u z θ) := by
    funext z θ
    field_simp
  have hXeq : Work.FTS.Nonlin.Xn α (fun z θ => Real.sin θ ^ 2 * u z θ)
      = |1 / (-c)| * Work.FTS.Nonlin.Xn α (fun z θ => c * (-(Real.sin θ ^ 2)) * u z θ) := by
    rw [hkey]
    exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (1 / (-c))
      (fun z θ => c * (-(Real.sin θ ^ 2)) * u z θ)
  refine ⟨?_, ?_, ?_⟩
  · rw [hkey]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (-c))
      (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul c
          (Work.FTS.EllipticEst.smoothOpen_of_smoothInt hSI)) huS)
  · rw [hkey]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / (-c)) hcore.1
  · rw [hXeq]
    have habs : |1 / (-c)| = 1 / c := by
      rw [abs_of_neg (div_neg_of_pos_of_neg one_pos (by linarith : -c < 0))]
      field_simp
    rw [habs]
    calc (1 / c) * Work.FTS.Nonlin.Xn α (fun z θ => c * (-(Real.sin θ ^ 2)) * u z θ)
        ≤ (1 / c) * (Ci * Ci * Work.FTS.Nonlin.Xn α u) :=
          mul_le_mul_of_nonneg_left hcore.2 (by positivity)
      _ ≤ (1 / c) * (Ci * Ci * (Bu * Work.FTS.GalFields.Xn5 α h)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huX (by positivity))
            (by positivity)
      _ = (B * Ci * Bu) * Work.FTS.GalFields.Xn5 α h := by
          have hcinv : (1 : ℝ) / c = B / Ci := by
            rw [hc]
            field_simp
          rw [hcinv]
          field_simp

/-- **The `max`-trick for a constant of unknown sign**: if `A ≤ B·Y` with `Y ≤ Yh` and both
`A, Y, Yh ≥ 0`, then `A ≤ max B 0 · Yh`. -/
theorem scale_le_max {A B Y Yh : ℝ} (hA0 : 0 ≤ A) (hY0 : 0 ≤ Y) (hYh0 : 0 ≤ Yh)
    (hAY : A ≤ B * Y) (hYY : Y ≤ Yh) : A ≤ max B 0 * Yh := by
  have h1 : B * Y ≤ max B 0 * Y := mul_le_mul_of_nonneg_right (le_max_left B 0) hY0
  have h2 : max B 0 * Y ≤ max B 0 * Yh :=
    mul_le_mul_of_nonneg_left hYY (le_max_right B 0)
  exact le_trans (le_trans hAY h1) h2

/-- **The final comparison**: `A ≤ K` turns the `A`-bound of a term into the shape required by the
statement, because `1 ≤ 1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵}`. -/
theorem le_K_mul_Xn5 {α K A : ℝ} {g g' h : Fn} (hK : 0 ≤ K) (hAK : A ≤ K) :
    A * Work.FTS.GalFields.Xn5 α h
      ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h := by
  have hY : 0 ≤ Work.FTS.GalFields.Xn5 α g := Real.sqrt_nonneg _
  have hY' : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Real.sqrt_nonneg _
  have hYh : 0 ≤ Work.FTS.GalFields.Xn5 α h := Real.sqrt_nonneg _
  have hone : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' := by
    linarith
  have hKm : K ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') := by
    simpa using mul_le_mul_of_nonneg_left hone hK
  calc A * Work.FTS.GalFields.Xn5 α h ≤ K * Work.FTS.GalFields.Xn5 α h :=
        mul_le_mul_of_nonneg_right hAK hYh
    _ ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h :=
        mul_le_mul_of_nonneg_right hKm hYh

end Work.FTS.GalFields.RHS.SharpAux
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpMod.N_L12_WlInfAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpMod

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000






end Work.FTS.GalFields.RHS.SharpMod
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Tail.FrBoxAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Generic helpers -/

/-- `HkSq` is the square of `HkNorm`. -/
theorem HkSq_eq_HkNorm_sq (α : ℝ) (k : ℕ) (f : Fn) :
    Work.Spaces.HkSq α k f = Work.Spaces.HkNorm α k f ^ 2 :=
  (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)).symm







end Work.FTS.GalFields.Tail
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.psiP_div_cos_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `psiP/cos θ` chain: definitions

This module fixes the vocabulary of the estimate `psiP_div_cos` (the `U`-slot part
`Φ = psiP α Φ` of a stream function, divided by `cos θ`, is `ℋ⁰` with quantitative bounds).

* `beta α = 3/α - 1` is the exponent of the kernel in the representation
  `psiP α Φ z θ = -(sin(2θ)/α) ∫₀¹ v^{3/α-1} U'(zv,θ) dv`.
* `mom U z = ∫_θ U z θ² sin(2θ)^{-η}` is the angular moment `M₁(z)` of the `U`-slot.
* `mass α U z = ∫_θ HkIntegrand α 0 U z θ` is the level-`0` angular slice mass; the two are
  related by `mass α U z = w(z)² · mom U z` (`mass_eq_w2_mom`), because at level `0` the
  `ℋ⁰`-integrand is `(U z θ · w z / sin(2θ)^{η/2})²`.
* `Gf α U z = w(z)² ∫₀¹ v^β mom U (zv) dv` is the radial density dominating the `ℋ⁰`-slices of
  `Φ/cos θ`.
* `Xf Φ z θ = Φ z θ / cos θ`.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- The exponent `β = 3/α - 1` of the kernel in the `psiP` representation. -/
def beta (α : ℝ) : ℝ := 3 / α - 1

/-- `M₁(z) = ∫_θ U(z,θ)² sin(2θ)^{-η}`: the angular moment of the `U`-slot. -/
def mom (U : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ

/-- `A(z) = ∫_θ HkIntegrand α 0 U z θ`: the level-`0` angular slice mass of `U`. -/
def mass (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 U z θ

/-- The radial density `G(z) = w(z)² ∫₀¹ v^β M₁(zv) dv` dominating the `ℋ⁰`-slices of `Φ/cos θ`. -/
def Gf (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * ∫ v in (0 : ℝ)..1, v ^ (beta α) * mom U (z * v)

/-- The quotient `Φ / cos θ`. -/
def Xf (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Φ z θ / Real.cos θ

/-! ## Elementary properties of `mom` and `mass` -/

theorem mom_nonneg (U : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ mom U z :=
  setIntegral_nonneg measurableSet_Icc fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)

theorem mass_nonneg (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ mass α U z :=
  setIntegral_nonneg measurableSet_Icc fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 U z θ

/-- At level `0` the `ℋ⁰`-integrand is exactly `(U·w/sin(2θ)^{η/2})²`. -/
theorem HkIntegrand_zero_eq' (α : ℝ) (U : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 U z θ
      = (U z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.DzIter]

/-- At level `0` the `ℋ⁰`-integrand is `U²·w²·σ` on the angular interval. -/
theorem HkIntegrand_eq_w2_sig (α : ℝ) (U : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 U z θ
      = (Work.Spaces.w z) ^ 2 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  rw [HkIntegrand_zero_eq', Work.FTS.EllipticEst.AngSecond.sq_mul_W U hθ]
  simp only [Work.FTS.EllipticEst.AngSecond.w2]
  ring

/-- The slice mass is the radial weight times the angular moment. -/
theorem mass_eq_w2_mom (α : ℝ) (U : ℝ → ℝ → ℝ) (z : ℝ) :
    mass α U z = (Work.Spaces.w z) ^ 2 * mom U z := by
  have hEq : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 U z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((U z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) :=
    setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
      (fun θ hθ => HkIntegrand_eq_w2_sig α U hθ)
  rw [mass, mom, hEq, integral_const_mul]


/-- `w(z)² z⁴ = (1+z)⁴` for `z ≠ 0`. -/
theorem w_sq_mul_z4 {z : ℝ} (hz : z ≠ 0) : (Work.Spaces.w z) ^ 2 * z ^ 4 = (1 + z) ^ 4 := by
  have h : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 (pow_ne_zero 2 hz))]
  ring

/-- `1 ≤ w(z)² z⁴` for `z > 0`. -/
theorem one_le_w2_mul_z4 {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 * z ^ 4 := by
  rw [w_sq_mul_z4 (ne_of_gt hz)]
  exact one_le_pow₀ (by linarith)

/-- `mom U z = mass α U z / w(z)²` for `z > 0`. -/
theorem mom_eq_mass_div (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    mom U z = mass α U z / (Work.Spaces.w z) ^ 2 := by
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  rw [mass_eq_w2_mom, eq_div_iff (pow_ne_zero 2 hw)]
  ring

/-- `M₁(z) ≤ z⁴ A(z)` for `z > 0`. -/
theorem mom_le_mass_mul_z4 (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    mom U z ≤ z ^ 4 * mass α U z := by
  have hw : 0 < (Work.Spaces.w z) ^ 2 := by rw [Work.Spaces.w]; positivity
  rw [mom_eq_mass_div α U hz, div_le_iff₀ hw]
  have h1 : 1 ≤ (Work.Spaces.w z) ^ 2 * z ^ 4 := one_le_w2_mul_z4 hz
  have h2 := mul_le_mul_of_nonneg_left h1 (mass_nonneg α U z)
  nlinarith [h2]



/-! ## Integrability and measurability of `mass` and `mom` -/

/-- `A = mass α U` is integrable on `(0,∞)` whenever `U ∈ ℋ⁰`. -/
theorem mass_integrableOn (α : ℝ) (U : ℝ → ℝ → ℝ) (hU : Work.Spaces.HkMem α 0 U) :
    IntegrableOn (mass α U) (Set.Ioi 0) := by
  have h : IntegrableOn (mass α U) Work.Spaces.Iz := hU.2
  have hmeas : MeasureTheory.Measure.restrict volume (Set.Ioi (0 : ℝ))
      = MeasureTheory.Measure.restrict volume (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  rw [Work.Spaces.Iz] at h
  unfold MeasureTheory.IntegrableOn at h ⊢
  rw [hmeas]
  exact h

/-- `∫_{(0,∞)} A = HkSq α 0 U`. -/
theorem mass_Ioi_eq_HkSq (α : ℝ) (U : ℝ → ℝ → ℝ) :
    ∫ z in Set.Ioi (0 : ℝ), mass α U z = Work.Spaces.HkSq α 0 U := by
  rw [Work.Spaces.HkSq, Work.Spaces.Iz]
  exact (MeasureTheory.integral_Ici_eq_integral_Ioi (f := mass α U) (x := (0 : ℝ))).symm

theorem mass_aesm (α : ℝ) (U : ℝ → ℝ → ℝ) (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.AEStronglyMeasurable (mass α U)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (mass_integrableOn α U hU).aestronglyMeasurable

theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
    exact ContinuousOn.div ((continuous_const.add continuous_id).pow 2).continuousOn
      (continuous_id.pow 2).continuousOn
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact h.pow 2


/-! ## The moment bound -/

/-- `∫_θ sin(2θ)^{-η} ≤ 10⁴`. -/
theorem integral_sin_rpow_le :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10 ^ 4 := by
  have hp : (-1 : ℝ) < -(Work.Spaces.eta) := by norm_num [Work.Spaces.eta]
  have hp0 : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hp hp0).2
  refine le_trans h (le_of_eq ?_)
  norm_num [Work.Spaces.eta]

theorem integrableOn_sin_rpow_neg :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hp : (-1 : ℝ) < -(Work.Spaces.eta) := by norm_num [Work.Spaces.eta]
  have hp0 : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
  exact (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hp hp0).1


/-- Substitution `t = zv` in the defining integral of `Gf`'s inner part. -/
theorem mom_subst (α : ℝ) (U : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ v in (0 : ℝ)..1, v ^ (beta α) * mom U (z * v)
      = z ^ (-(beta α + 1)) * ∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t := by
  simpa only [mul_comm] using
    Work.FTS.PhiStar.RadialWAux.integral_zero_one_rpow (mom U) (beta α) hz

end Work.FTS_EllLimOK.ProducerH
end
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.Sup5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_FinalLeaves.Sup5` — the (5′) producer, proved

`sup5'_proved` is the frozen producer `Work.FTS.FinalV2.sup5'` of
`Submission/Work/FTS/FinalV2/Producers.lean` (conjunct (5′) of `Inputs'`), with its statement
copied verbatim: the uniform sup bound

  `|extG g z θ τ| ≤ 10/√(γ(α)-1) · C₀α²`   for `τ ≥ 0`, `z ∈ Iz = [0,∞)`, `θ ∈ Iθ = [0,π/2]`,

for a family `g` satisfying `DynOK' α C₀ Φs E g`.

## Route

`DynOK' = DynOK ∧ LimApprox`.  The three regions of `Iz × Iθ`:

* `z ≤ 0` (i.e. `z = 0`): `extG g 0 θ τ = 0`;
* `z > 0`, `θ ∈ {0, π/2}`: `extG g = g` there and `RegPkgMin.vanish` (a field of `DynOK`) gives
  `g z 0 τ = g z (π/2) τ = 0`;
* `z > 0`, `0 < θ < π/2`: `g` is the limit of the class-C approximating slices `slice (gn n) τ`
  of the `LimApprox` clause, on which the class-C `L^∞`–`ℋ⁴` trade-off
  (`classC_sup_le_proved`, Elgindi's `SecondDerivativesBounded`) gives the bound, with the
  uniform `ℋ⁴`-bound `Xn α (slice (gn n) τ) ≤ C₀α²` making the constant uniform in `n`; the
  limit is then taken with `le_of_tendsto`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_FinalLeaves

set_option autoImplicit false

/-- **(5′) producer**: the uniform sup bound of the extension `extG g` on `Iz × Iθ`, at the
dynamic amplitude bound `C₀α²` of `DynOK'`. -/
theorem sup5'_proved {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤
        10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hCnn : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  intro τ hτ z hz θ hθ
  -- `C₀α² ≥ 0`, from the uniform `ℋ⁴`-bound of `DynOK`
  have hC0 : 0 ≤ C₀ * α ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg α 4 (Work.FTS.Galerkin.slice g τ)) (hOK.1.2 τ hτ)
  rcases le_or_gt z 0 with hz0 | hz0
  · rw [Work.FTS.RegPkgGal.extG_of_nonpos hz0, abs_zero]
    exact mul_nonneg hCnn hC0
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0, Work.FTS.RegPkgGal.extG_of_pos hz0 hτ,
        (hOK.1.1.vanish τ hτ z hz).1, abs_zero]
      exact mul_nonneg hCnn hC0
    · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
      · rw [hθp, Work.FTS.RegPkgGal.extG_of_pos hz0 hτ,
          (hOK.1.1.vanish τ hτ z hz).2, abs_zero]
        exact mul_nonneg hCnn hC0
      · -- the interior: the class-C bound at the approximating slices, then the limit
        have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz0, hθ0, hθp⟩
        obtain ⟨gn, _B, _L, h1, _h2, h3, _h4⟩ := hOK.2 (τ + 1) (by linarith)
        have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
        have hconv : Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ z θ)
            Filter.atTop (𝓝 (Work.FTS.Galerkin.slice g τ z θ)) :=
          h3 τ hτT 0 0 (by norm_num) z θ hzθ
        have hbound : ∀ n : ℕ, |Work.FTS.Galerkin.slice (gn n) τ z θ| ≤
            10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
          intro n
          have hC := classC_sup_le_proved hα hα1 (Work.FTS.Galerkin.slice (gn n) τ)
            (h1 n τ hτT).1 z θ hzθ
          exact le_trans hC (mul_le_mul_of_nonneg_left (h1 n τ hτT).2.1 hCnn)
        have hlim := le_of_tendsto hconv.abs (Filter.Eventually.of_forall hbound)
        rwa [Work.FTS.RegPkgGal.extG_of_pos hz0 hτ]

end Work.FTS_FinalLeaves
end
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.sol_fire_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

open scoped Real Topology

/-! ## Congruence of the differential operators on the open quadrant

The three lemmas below are the `deriv`-locality of `pth`/`Dth`/`pz` at an interior point of the
quadrant, in the form consumed by the `N0`/`N`/`gRHS` congruence chain. -/

/-- `pz` at an interior point of the quadrant only sees the values of the function on the
quadrant. -/
theorem pz_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := by
  simp only [Work.Spaces.pz]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hθ2

/-- `pth` at an interior point of the quadrant only sees the values of the function on the
quadrant. -/
theorem pth_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  simp only [Work.Spaces.pth]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ, hθ2⟩)]
    with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

/-- `Dth` at an interior point of the quadrant only sees the values of the function on the
quadrant. -/
theorem Dth_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  simp only [Work.Spaces.Dth, pth_congr_of_agreeOnQ hz hθ hθ2 h]

/-! ## Congruence of `mubar`, `Nstar`, `gRHS`, `muDyn`, `dynLin`, `dynRHS` -/

/-- `Nstar` is local: it only sees `g` and `Dz g` at the point. -/
theorem Nstar_congr_of_agreeOnQ {μ lam : ℝ} {g g' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ') :
    Work.Construction.Nstar μ lam g z θ = Work.Construction.Nstar μ lam g' z θ := by
  have h1 : g z θ = g' z θ := hg z θ hz hθ hθ2
  have h2 : Work.Spaces.pz g z θ = Work.Spaces.pz g' z θ := pz_congr_of_agreeOnQ hz hθ hθ2 hg
  simp only [Work.Construction.Nstar, Work.Spaces.Dz, h1, h2]

/-- The modulation average `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` only sees its data on the open
quadrant. -/
theorem mubar_congr_of_agreeOnQ {α : ℝ} {F F' Φ Φ' g g' : ℝ → ℝ → ℝ}
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → Φ z' θ' = Φ' z' θ') :
    Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
      = Work.Construction.mubar (Work.Construction.N0 α F' g') (Work.Construction.N α F' Φ') := by
  have h1 : Work.Construction.L12 (Work.Construction.N0 α F g) 0
      = Work.Construction.L12 (Work.Construction.N0 α F' g') 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ hz hθ hθ2 hF hg)
  have h2 : Work.Construction.L12 (Work.Construction.N α F Φ) 0
      = Work.Construction.L12 (Work.Construction.N α F' Φ') 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ hz hθ hθ2 hF hΦ)
  simp only [Work.Construction.mubar, h1, h2]

/-- `gRHS` depends on its three data only through their values on the open quadrant. -/
theorem gRHS_congr_of_agreeOnQ {α μ lam : ℝ} {F F' Φ Φ' g g' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → Φ z' θ' = Φ' z' θ') :
    Work.Construction.gRHS α μ lam F Φ g z θ = Work.Construction.gRHS α μ lam F' Φ' g' z θ := by
  have hmub := mubar_congr_of_agreeOnQ (α := α) hF hg hΦ
  have hN0 := Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ (α := α) hz hθ hθ2 hF hg
  have hN := Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ (α := α) hz hθ hθ2 hF hΦ
  have hNs := Nstar_congr_of_agreeOnQ (μ := μ) (lam := lam) hz hθ hθ2 hg
  simp only [Work.Construction.gRHS, hmub, hN0, hN, hNs]

/-- `muDyn` depends on the two families only through their slices on the open quadrant. -/
theorem muDyn_congr_of_agreeOnQ {α : ℝ} {Φ Φ' g g' : Work.FTS.Galerkin.Fam} {τ : ℝ}
    (hg : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z θ = Work.FTS.Galerkin.slice g' τ z θ)
    (hΦ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice Φ τ z θ = Work.FTS.Galerkin.slice Φ' τ z θ) :
    Work.FTS.Galerkin.muDyn α Φ g τ = Work.FTS.Galerkin.muDyn α Φ' g' τ := by
  have hF : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Ftau α g τ z θ = Work.Construction.Ftau α g' τ z θ := by
    intro z θ hz hθ hθ2
    have h := hg z θ hz hθ hθ2
    simp only [Work.FTS.Galerkin.slice] at h
    simp only [Work.Construction.Ftau]
    rw [h]
  have h1 : Work.Construction.L12
        (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice g τ)) 0
      = Work.Construction.L12
        (Work.Construction.N0 α (Work.Construction.Ftau α g' τ)
          (Work.FTS.Galerkin.slice g' τ)) 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ hz hθ hθ2
          (fun z' θ' hz' hθ' hθ2' => hF z' θ' hz' hθ' hθ2') hg)
  have h2 : Work.Construction.L12
        (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ)) 0
      = Work.Construction.L12
        (Work.Construction.N α (Work.Construction.Ftau α g' τ)
          (Work.FTS.Galerkin.slice Φ' τ)) 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ hz hθ hθ2
          (fun z' θ' hz' hθ' hθ2' => hF z' θ' hz' hθ' hθ2') hΦ)
  have h3 : Work.Construction.L12
        (fun z θ => 3 * Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
      = Work.Construction.L12
        (fun z θ => 3 * Work.Spaces.Dth (Work.FTS.Galerkin.slice g' τ) z θ / (1 + z)) 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 => by
        have hd := Dth_congr_of_agreeOnQ hz hθ hθ2
          (fun z' θ' hz' hθ' hθ2' => hg z' θ' hz' hθ' hθ2')
        simp only [hd])
  simp only [Work.FTS.Galerkin.muDyn, Work.Construction.mufunS, h1, h2, h3]

/-- `dynLin` depends on the family only through its slice on the open quadrant. -/
theorem dynLin_congr_of_agreeOnQ {α : ℝ} {g g' : Work.FTS.Galerkin.Fam} {τ z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z' θ' = Work.FTS.Galerkin.slice g' τ z' θ') :
    Work.FTS.Galerkin.dynLin α g τ z θ = Work.FTS.Galerkin.dynLin α g' τ z θ := by
  simp only [Work.FTS.Galerkin.dynLin,
    Work.FTS_FinalLeaves.SolFire.LGammaT_congr_of_agreeOnQ (α := α) hz hθ hθ2 hg]

/-- `dynRHS` depends on the two families only through their slices on the open quadrant. -/
theorem dynRHS_congr_of_agreeOnQ {α : ℝ} {Φ Φ' g g' : Work.FTS.Galerkin.Fam} {τ z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z' θ' = Work.FTS.Galerkin.slice g' τ z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.Galerkin.slice Φ τ z' θ' = Work.FTS.Galerkin.slice Φ' τ z' θ') :
    Work.FTS.Galerkin.dynRHS α Φ g τ z θ = Work.FTS.Galerkin.dynRHS α Φ' g' τ z θ := by
  have hmu := muDyn_congr_of_agreeOnQ (α := α) (Φ := Φ) (Φ' := Φ') (g := g) (g' := g') hg hΦ
  have hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Ftau α g τ z' θ' = Work.Construction.Ftau α g' τ z' θ' := by
    intro z' θ' hz' hθ' hθ2'
    have h := hg z' θ' hz' hθ' hθ2'
    simp only [Work.FTS.Galerkin.slice] at h
    simp only [Work.Construction.Ftau]
    rw [h]
  simp only [Work.FTS.Galerkin.dynRHS, Work.FTS.Galerkin.lamDyn, hmu]
  exact gRHS_congr_of_agreeOnQ hz hθ hθ2 hF hg hΦ

/-! ## The target -/

theorem sol_fire_proved {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hSol : Work.FTS.FinalV2.Sol α Φs E g) :
    Work.FTS.Galerkin.IsDynGSolWith (Work.FTS.Final.IsBslSolPos α) α
        (Work.FTS.FinalV2.psiFire Φs E g) (Work.FTS.RegPkgGal.extG g) ∧
      ∀ τ : ℝ, 0 ≤ τ →
        Work.FTS.Galerkin.muDyn α (Work.FTS.FinalV2.psiFire Φs E g) (Work.FTS.RegPkgGal.extG g)
            τ
          = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ := by
  -- the two pairs agree on the open quadrant
  have hgOf : ∀ (τ : ℝ), 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z θ
        = Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ z θ :=
    fun τ hτ z θ hz _ _ => by
      simp only [Work.FTS.Galerkin.slice]
      exact (Work.FTS.RegPkgGal.extG_of_pos hz hτ).symm
  have hPhiOf : ∀ (τ : ℝ), ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
        = Work.FTS.Galerkin.slice (Work.FTS.FinalV2.psiFire Φs E g) τ z θ :=
    fun _ z θ _ hθ _ => by
      simp only [Work.FTS.Galerkin.slice]
      exact (Work.FTS.FinalV2.psiFire_of_pos hθ).symm
  refine ⟨⟨fun τ hτ => Work.FTS_FinalLeaves.SolFire.isBslSolPos_psiFire_extG hτ (hSol.1 τ hτ),
    ?_⟩, ?_⟩
  · intro z θ τ hτ hzθ
    have hsol := hSol.2 z θ τ hτ hzθ
    obtain ⟨hz, hθ, hθ2⟩ := hzθ
    have hder : HasDerivWithinAt (fun s => Work.FTS.RegPkgGal.extG g z θ s)
        (Work.FTS.Galerkin.dynLin α g τ z θ
          + Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ z θ)
        (Set.Ici 0) τ :=
      hsol.congr (fun s hs => Work.FTS.RegPkgGal.extG_of_pos hz hs)
        (Work.FTS.RegPkgGal.extG_of_pos hz hτ)
    rw [dynLin_congr_of_agreeOnQ (α := α) hz hθ hθ2 (hgOf τ hτ),
      dynRHS_congr_of_agreeOnQ (α := α) hz hθ hθ2 (hgOf τ hτ) (hPhiOf τ)] at hder
    exact hder
  · intro τ hτ
    exact (muDyn_congr_of_agreeOnQ (α := α) (hgOf τ hτ) (hPhiOf τ)).symm

end Work.FTS_FinalLeaves
end
-- ===== merged: Submission.Work.FTS_RegExport.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## §1 Elementary facts about the weight `ω = z²Γ(θ)/(1+z)²` -/

/-- `Γ(θ) ≥ 0` on `Iθ`. -/
theorem Gamma_nonneg {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.Regularity.Gamma α θ :=
  Work.ConstructionInstance.Gamma_nonneg hθ

/-- `Γ(θ) ≤ 1` on `Iθ`. -/
theorem Gamma_le_one {α : ℝ} (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.Regularity.Gamma α θ ≤ 1 :=
  Work.ConstructionInstance.Gamma_le_one hα hθ



end Work.FTS_RegExport
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RX0.RecutAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS_RegExport.RX0

open Work.FTS.Regularity
open Work.FTS.RegPkgGal (extG extG_of_pos extG_of_nonpos extG_hquad)

set_option autoImplicit false

/-! ## §1 Endpoint continuity of `g̃` from the `θ`-Hölder modulus

`Der.endpoint_cont` obtains the vanishing of the slice `θ ↦ g z θ τ` at `θ = 0` and at
`θ = π/2` from the `a = b = 0` conjunct of `BdryTraces`:  `sin(2θ)^{1-γ}·g² → 0`.
The *same conclusion* follows from the `θ`-Hölder modulus `St1Class.hhθ` of the perturbation
(`|g(z,θ) - g(z,θ')| ≤ Lθ·|θ-θ'|^α`, together with the boundary values `g(z,0) = g(z,π/2) = 0`),
since `|g(z,θ)| ≤ Lθ·|θ|^α → 0`: no boundary trace is needed. -/

/-- `|θ - a|^α → 0` as `θ → a` from either side, for `α > 0`. -/
private lemma tendsto_abs_sub_rpow_zero {α a : ℝ} (hα : 0 < α) {l : Filter ℝ}
    (hl : l ≤ 𝓝 a) : Tendsto (fun θ : ℝ => |θ - a| ^ α) l (𝓝 0) := by
  have hcomp : Tendsto (fun x : ℝ => |x| ^ α) (𝓝 0) (𝓝 0) := by
    have hc := (continuous_abs.continuousAt (x := (0 : ℝ))).rpow_const (Or.inr hα.le)
    simpa [Real.zero_rpow (ne_of_gt hα)] using hc.tendsto
  have hid : Tendsto (fun θ : ℝ => θ - a) l (𝓝 0) := by
    have h1 : Tendsto (fun θ : ℝ => θ - a) (𝓝 a) (𝓝 (a - a)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using (h1.mono_left hl)
  exact hcomp.comp hid

/-- **Endpoint continuity of `g̃` from the `θ`-Hölder modulus** (the replacement of
`Der.endpoint_cont` used by the re-cut assembly).  The hypothesis `hhθ` is
`St1Class.hhθ` verbatim. -/
theorem endpoint_cont_of_holder {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hhθ : ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ,
        |extG g z θ τ - extG g z θ' τ| ≤ Lθ * |θ - θ'| ^ α) :
    (∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Tendsto (fun θ => extG g z θ τ) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (extG g z 0 τ))) ∧
    (∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Tendsto (fun θ => extG g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (extG g z (Real.pi / 2) τ))) := by
  obtain ⟨L, _hL0, hL⟩ := hhθ
  have hpi2 : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  constructor
  · -- `θ → 0⁺`
    intro τ hτ z hz
    rcases le_or_gt z 0 with hz0 | hzpos
    · have he : ∀ θ : ℝ, extG g z θ τ = 0 := fun θ => extG_of_nonpos hz0
      rw [he 0]
      exact Tendsto.congr' (Filter.Eventually.of_forall fun θ => (he θ).symm) tendsto_const_nhds
    · have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hge : ∀ θ : ℝ, extG g z θ τ = g z θ τ := fun θ => extG_of_pos hzpos hτ0
      have he0 : extG g z 0 τ = 0 := by rw [hge 0, (hvan τ hτ z (le_of_lt hzpos)).1]
      rw [he0]
      -- the bound `|g z θ τ| ≤ L·|θ|^α` on a neighbourhood of `0` inside `Ioi 0`
      have hle : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ‖g z θ τ‖ ≤ L * |θ - 0| ^ α := by
        have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
          have h1 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
          have h2 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
            nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hpi2))
          have h3 := inter_mem h1 h2
          rwa [show Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2)
            = Set.Ioo 0 (Real.pi / 2) from rfl] at h3
        filter_upwards [hmem] with θ hθ
        have h1 := hL τ hτ z (le_of_lt hzpos) θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ 0
          ⟨le_refl 0, le_of_lt hpi2⟩
        have heq : |g z θ τ| = |extG g z θ τ - extG g z 0 τ| := by
          rw [hge θ, he0, sub_zero]
        rw [Real.norm_eq_abs, heq]
        exact h1
      have hbound : Tendsto (fun θ : ℝ => L * |θ - 0| ^ α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        have h0 : Tendsto (fun θ : ℝ => |θ - 0| ^ α) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
          tendsto_abs_sub_rpow_zero (a := 0) hα nhdsWithin_le_nhds
        simpa using h0.const_mul L
      have habs : Tendsto (fun θ : ℝ => ‖g z θ τ‖)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
        squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) hle hbound
      have hmain : Tendsto (fun θ : ℝ => g z θ τ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr habs
      exact hmain.congr' (Filter.Eventually.of_forall fun θ => (hge θ).symm)
  · -- `θ → (π/2)⁻`
    intro τ hτ z hz
    rcases le_or_gt z 0 with hz0 | hzpos
    · have he : ∀ θ : ℝ, extG g z θ τ = 0 := fun θ => extG_of_nonpos hz0
      rw [he (Real.pi / 2)]
      exact Tendsto.congr' (Filter.Eventually.of_forall fun θ => (he θ).symm) tendsto_const_nhds
    · have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hge : ∀ θ : ℝ, extG g z θ τ = g z θ τ := fun θ => extG_of_pos hzpos hτ0
      have he0 : extG g z (Real.pi / 2) τ = 0 := by
        rw [hge (Real.pi / 2), (hvan τ hτ z (le_of_lt hzpos)).2]
      rw [he0]
      have hle : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
          ‖g z θ τ‖ ≤ L * |θ - Real.pi / 2| ^ α := by
        have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
            nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
          have h1 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
            self_mem_nhdsWithin
          have h2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
            nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hpi2))
          have h3 := inter_mem h2 h1
          rwa [show Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2)
            = Set.Ioo 0 (Real.pi / 2) from rfl] at h3
        filter_upwards [hmem] with θ hθ
        have h1 := hL τ hτ z (le_of_lt hzpos) θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ (Real.pi / 2)
          ⟨le_of_lt hpi2, le_refl _⟩
        have heq : |g z θ τ| = |extG g z θ τ - extG g z (Real.pi / 2) τ| := by
          rw [hge θ, he0, sub_zero]
        rw [Real.norm_eq_abs, heq]
        exact h1
      have hbound : Tendsto (fun θ : ℝ => L * |θ - Real.pi / 2| ^ α)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
        have h0 : Tendsto (fun θ : ℝ => |θ - Real.pi / 2| ^ α)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) :=
          tendsto_abs_sub_rpow_zero (a := Real.pi / 2) hα nhdsWithin_le_nhds
        simpa using h0.const_mul L
      have habs : Tendsto (fun θ : ℝ => ‖g z θ τ‖)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) :=
        squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) hle hbound
      have hmain : Tendsto (fun θ : ℝ => g z θ τ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr habs
      exact hmain.congr' (Filter.Eventually.of_forall fun θ => (hge θ).symm)

/-! ## §2 The sup bound of `g̃` and `∂_zg̃` from the interior order-`≤ 2` bound

`Der.sup_extG_ext` derives these two bounds from `RegQ (pExp α) 4 (gSlice g τ)` (through the
pointwise trade-off `abs_mixed_le_HkNorm_RegQ`) and the uniform `ℋ⁴` bound.  The interior class
`RegQ` is *not* available in the re-cut bundle, but the two slots that are actually consumed,
`mixed 0 0` and `mixed 1 0`, are bounded by `hIS` outright. -/

/-- **The sup bound of `g̃` and `∂_zg̃` from `hIS`** (the re-cut `Der.sup_extG_ext`).  The
hypothesis `hquad` is `StData.quad`'s second clause for the *extension* slice, verbatim the shape
`GalMinConv` passes. -/
theorem sup_extG_ext_hIS {S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (_hS : 0 < S)
    (hIS : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (gSlice g τ) z θ| ≤ M)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hquad : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (gSlice (extG g) τ) z θ| ≤ Q * z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |extG g z θ τ| ≤ M
        ∧ |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := hIS
  obtain ⟨Q, hQ0, hQext⟩ := hquad
  -- the near-axis clause for the slice of `g` (transported through `pz_gSlice_extG_eq`)
  have hQ : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → z ≤ 2 →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ Q * z := by
    intro τ hτ θ hθ z hz hz2
    rw [← Work.FTS.RegPkgGal.Der.pz_gSlice_extG_eq hτ hz]
    exact hQext τ hτ θ hθ z (le_of_lt hz) hz2
  -- the `z`-slot `mixed 1 0 = D_z = z·∂_z`, at every interior point
  have h10 : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ M / z := by
    intro τ hτ z θ hz hθ hθ'
    have h1 := hM τ hτ 1 0 (by norm_num) z θ hz hθ hθ'
    have h2 : Work.Spaces.mixed 1 0 (gSlice g τ) z θ
        = z * Work.Spaces.pz (gSlice g τ) z θ := rfl
    rw [h2, abs_mul, abs_of_pos hz] at h1
    rw [le_div_iff₀ hz, mul_comm]
    exact h1
  refine ⟨max M (2 * Q), le_trans hM0 (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz hθ
  have hM1 : M ≤ max M (2 * Q) := le_max_left _ _
  have hM2 : 2 * Q ≤ max M (2 * Q) := le_max_right _ _
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  constructor
  · -- the value bound
    by_cases hz0 : z ≤ 0
    · rw [extG_of_nonpos hz0, abs_zero]
      exact le_trans hM0 (le_max_left _ _)
    · simp only [not_le] at hz0
      rw [extG_of_pos hz0 hτ0]
      rcases eq_or_lt_of_le hθ.1 with hθz | hθz
      · rw [← hθz, (hvan τ hτ z (le_of_lt hz0)).1, abs_zero]
        exact le_trans hM0 (le_max_left _ _)
      · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
        · rw [hθp, (hvan τ hτ z (le_of_lt hz0)).2, abs_zero]
          exact le_trans hM0 (le_max_left _ _)
        · exact le_trans (hM τ hτ 0 0 (by norm_num) z θ hz0 hθz hθp) hM1
  · -- the derivative bound
    by_cases hz0 : z = 0
    · rw [hz0, extG_hquad g τ θ, abs_zero]
      exact le_trans hM0 (le_max_left _ _)
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hderiv : Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
          = Work.Spaces.pz (gSlice g τ) z θ := by
        have hev : (fun z' => extG g z' θ τ) =ᶠ[𝓝 z] (fun z' => gSlice g τ z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
          simp [gSlice, extG_of_pos hz' hτ0]
        exact hev.deriv_eq
      rw [hderiv]
      rcases eq_or_lt_of_le hθ.1 with hθz | hθz
      · have hpz0 : Work.Spaces.pz (gSlice g τ) z 0 = 0 := by
          show deriv (fun z' => gSlice g τ z' 0) z = 0
          have hev : (fun z' => gSlice g τ z' 0) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
            filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
            exact (hvan τ hτ z' (le_of_lt hz')).1
          rw [hev.deriv_eq]
          exact deriv_const z 0
        rw [← hθz, hpz0, abs_zero]
        exact le_trans hM0 (le_max_left _ _)
      · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
        · have hpz0 : Work.Spaces.pz (gSlice g τ) z (Real.pi / 2) = 0 := by
            show deriv (fun z' => gSlice g τ z' (Real.pi / 2)) z = 0
            have hev : (fun z' => gSlice g τ z' (Real.pi / 2)) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
              filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
              exact (hvan τ hτ z' (le_of_lt hz')).2
            rw [hev.deriv_eq]
            exact deriv_const z 0
          rw [hθp, hpz0, abs_zero]
          exact le_trans hM0 (le_max_left _ _)
        · by_cases hz2 : z ≤ 2
          · have h1 := hQ τ hτ θ hθ z hzpos hz2
            have h2 : Q * z ≤ 2 * Q := by nlinarith [hQ0, hz, hz2]
            exact le_trans h1 (le_trans h2 hM2)
          · simp only [not_le] at hz2
            have h1 := h10 τ hτ z θ hzpos hθz hθp
            have h2 : M / z ≤ M := by
              have h4 : (1 : ℝ) / z ≤ 1 := by
                rw [div_le_one hzpos]; linarith
              calc M / z = M * (1 / z) := by ring
                _ ≤ M * 1 := mul_le_mul_of_nonneg_left h4 hM0
                _ = M := by ring
            exact le_trans h1 (le_trans h2 hM1)

end Work.FTS_RegExport.RX0
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXB

/-- **RX-B**: the zero mode of `L₁₂` passes to the limit along the class-C approximants of
`Work.FTS.FinalV2.LimApprox` (the `τ ↦ slice g τ` family is the pointwise limit of profiles
which are `C^∞` on the open quadrant and uniformly `ℋ⁴`-bounded, each carrying `L₁₂(·)(0) = 0`
as part of the class data).

The proof is the assembly lemma `Work.FTS_RegExport.RXB.l12_zero_lim_of_bounds` fed with the two
analytic inputs of the directory:

* `sup_bound_all_alpha` — the interior `L^∞`–`ℋ⁴` trade-off `f² ≤ C|f|²_{ℋ⁴}` for every `α > 0`
  (used for the angular dominated convergence of the density);
* `l12dens_weighted_bound` — the weighted bound `|L₁₂dens f s| ≤ C(√s/(1+s)²)|f|_{ℋ⁴}`, which
  turns the uniform `ℋ⁴`-bound of the approximants into an `L¹(ds)` majorant. -/
theorem l12_zero_lim_proved {αG C₀ : ℝ} (hα : 0 < αG) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 :=
  l12_zero_lim_of_bounds hα
    (fun α hα => sup_bound_all_alpha hα)
    (fun α hα => l12dens_weighted_bound hα)
    hA

end Work.FTS_RegExport.RXB
end
