import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.Nonlinear.Open.PiecesHkOpen
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.FinalV2.TauExt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.TauExt` — REVIEW FIX-2 transfer lemma (curric-46 lead install, 2026-10-10)

`Sol`, `DynOK` and `LimApprox` read a family `g` only at fake times `τ ≥ 0` (slices at `τ ≥ 0`,
`HasDerivWithinAt … (Ici 0)`, `ContDiffOn` on `τ > 0`, `deriv` at `τ > 0`), so they transfer from
`g` to its right-Taylor extension `tauExt g`, which agrees with `g` on `τ ≥ 0`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Final

set_option autoImplicit false

variable {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

theorem muDyn_tauExt {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS.Galerkin.muDyn α (PsiCan Φs E (tauExt g)) (tauExt g) τ
      = Work.FTS.Galerkin.muDyn α (PsiCan Φs E g) g τ :=
  Work.FTS.StrongGlobal.muDyn_congr (slice_tauExt g hτ)

theorem gdot_tauExt {τ : ℝ} (hτ : 0 < τ) :
    Work.FTS.Galerkin.gdot (tauExt g) τ = Work.FTS.Galerkin.gdot g τ := by
  funext z θ
  simp only [Work.FTS.Galerkin.gdot]
  exact Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (Ici_mem_nhds hτ) (fun s hs => tauExt_of_nonneg g hs))

theorem regPkgMin_tauExt (h : Work.FTS.StrongGlobal.RegPkgMin α g) :
    Work.FTS.StrongGlobal.RegPkgMin α (tauExt g) where
  c1 := h.c1.congr (fun p hp => tauExt_of_nonneg g (le_of_lt hp.2.2))
  c4 := fun τ hτ => by rw [slice_tauExt g hτ]; exact h.c4 τ hτ
  cont := fun z θ hzθ => (h.cont z θ hzθ).congr (eqOn_tauExt g z θ)
  mem4 := fun τ hτ => by rw [slice_tauExt g hτ]; exact h.mem4 τ hτ
  dbd := fun S hS => by
    obtain ⟨Cd, hCd⟩ := h.dbd S hS
    exact ⟨Cd, fun τ hτ hτS => by rw [gdot_tauExt hτ]; exact hCd τ hτ hτS⟩
  vanish := fun τ hτ z hz => by
    rw [tauExt_of_nonneg g hτ, tauExt_of_nonneg g hτ]; exact h.vanish τ hτ z hz

theorem dynOK_tauExt (h : DynOK α C₀ g) : DynOK α C₀ (tauExt g) :=
  ⟨regPkgMin_tauExt h.1, fun τ hτ => by rw [slice_tauExt g hτ]; exact h.2 τ hτ⟩

theorem limApprox_tauExt (h : LimApprox α C₀ Φs E g) : LimApprox α C₀ Φs E (tauExt g) := by
  intro T hT
  obtain ⟨gn, B, L, h1, h2, h3, h4⟩ := h T hT
  refine ⟨gn, B, L, h1, h2, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · rw [slice_tauExt g hτ.1]; exact h3 τ hτ
  · rw [muDyn_tauExt hτ.1]; exact h4 τ hτ

theorem sol_tauExt (h : Sol α Φs E g) : Sol α Φs E (tauExt g) := by
  refine ⟨fun τ hτ => ?_, fun z θ τ hτ hzθ => ?_⟩
  · rw [Work.FTS.StrongGlobal.Ftau_congr (slice_tauExt g hτ),
      Work.FTS.StrongGlobal.slice_PsiCan_congr (slice_tauExt g hτ)]
    exact h.1 τ hτ
  · have hd := h.2 z θ τ hτ hzθ
    rw [Work.FTS.StrongGlobal.dynLin_congr (slice_tauExt g hτ),
      Work.FTS.StrongGlobal.dynRHS_congr (slice_tauExt g hτ)]
    exact hd.congr (fun s hs => tauExt_of_nonneg g hs) (tauExt_of_nonneg g hτ)

/-- **REVIEW FIX-2, the transfer lemma** (PROVED): the strong solution and its enriched package
pass to the right-Taylor extension. -/
theorem sol_dynOK'_tauExt (hS : Sol α Φs E g) (hOK : DynOK' α C₀ Φs E g) :
    Sol α Φs E (tauExt g) ∧ DynOK' α C₀ Φs E (tauExt g) :=
  ⟨sol_tauExt hS, dynOK_tauExt hOK.1, limApprox_tauExt hOK.2⟩

end Work.FTS.FinalV2
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.abs_mubar_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.Norm



end Work.FTS.GalFields.Norm
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpMod.N0_L12_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.GalFields.RHS.SharpMod.N0_L12_diff`

The **sharp** (linear-in-the-difference) bound for the `L₁₂`-zero-mode of the quadratic term
`N₀ = N₀ α (F_* + g) g` of the modulation problem (Elgindi, Annals **194** (3) 2021,
§Modulation):

  `|L₁₂(N₀ g)(0) − L₁₂(N₀ g')(0)| ≤ K·(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})·|g − g'|_{ℋ⁵}`,

consumed by `Work.FTS.GalFields.RHS.sharp_modulation_diff`.  This is the `N₀` component of the
three `L₁₂`-differences feeding the difference of the two modulation constants
`μ = mufunS …`, `μ̄ = mubar …`.

The proof decomposes `N₀ α (F_*+g) g − N₀ α (F_*+g') g'` on the open quadrant `Qd` into the
**nine pieces** `P1 … P9` of `RHS.sharpN0_defs` (rows 1--7 of `Nonlinear/Open/`:
`N₀ = N0fix + N03g + N04aF + N04bF + N05aF + N05bF + N06F`), each of which telescopes along
`h = g − g'`; the per-piece `ℋ⁴`-bounds are `sharpN0_piecesA`/`sharpN0_piecesB` and their
assembly into `Rsum` is `sharpN0_sums`.  The two `N₀`-blocks are `ℋ⁴`-honest
(`hkMem_N0_of_rows`), so `L₁₂` is additive on the difference (`L12_sub_eq_of_smoothOpen`) and
its zero mode is controlled by `Xn α` of that difference (`N4Norm'.l12zero`); agreement on the
open quadrant suffices for `HkSq`/`Xn` (`HkSq_congr_open`, `HkMem_congr_Q0`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpMod

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.GalFields.RHS.SharpMod
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpMod.transport_L12_diff =====
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

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two elementary shapes used by the transport difference

The datum of the transport zero mode is `F_g(z,θ) = 3·D_θ g(z,θ)/(1+z)`; this file proves the
Lipschitz (difference) estimate for the `L₁₂`-zero-mode of that datum by

1. linearising `L₁₂` in its profile (`Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen`, for
   `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest data);
2. identifying the difference datum with the datum of `h = g - g'` (a *pointwise* identity which
   needs the angular derivatives only off the two angular boundary lines);
3. bounding the resulting `L₁₂(3·D_θ h/(1+z))(0)` by the row estimate `Nonlinear.Open.Rl2`
   applied to `h`, and comparing `ℋ⁴` with `ℋ⁵`.

The regularity/honesty of the datum `F_g` is produced from `g`'s `RegQ α 6` by writing
`3/(1+z) = 3 - 3·z/(1+z)` and using the bounded-radial-factor calculus (`NRow10aux`). -/

/-- `(z,θ) ↦ 3·f(z,θ)/(1+z)` is `C^∞` on the open quadrant whenever `f` is. -/
theorem smoothOpen_three_div_mul {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * f z θ / (1 + z)) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => 3 / (1 + z)) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 3 / (1 + p.1)) Work.FTS.EllipticEst.Q0
    refine contDiffOn_const.div (contDiffOn_const.add contDiffOn_fst) ?_
    intro p hp
    have hp1 : (0 : ℝ) < 1 + p.1 := by
      have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      linarith
    positivity
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (3 / (1 + z)) * f z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul h1 hf
  have hfun : Function.uncurry (fun z θ => 3 * f z θ / (1 + z))
      = Function.uncurry (fun z θ => (3 / (1 + z)) * f z θ) := by
    funext p
    simp only [Function.uncurry]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  simp only [Work.FTS.EllipticEst.SmoothOpen] at h2 ⊢
  rw [hfun]
  exact h2

/-- **Angular additivity of `D_θ` for a pointwise decomposition.**  If `g = g' + h` pointwise
and `g'`, `h` are `C^∞` on the open quadrant, then `D_θ g = D_θ g' + D_θ h` on
`(0,∞) × [0,π/2]`: in the interior this is the product rule `deriv_add`, and on the two
boundary lines `θ = 0`, `θ = π/2` both sides vanish because `sin(2θ) = 0` there. -/
theorem Dth_add_of_pointwise {g g' h : ℝ → ℝ → ℝ}
    (hg'sm : Work.FTS.EllipticEst.SmoothOpen g') (hhsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hgh : ∀ z θ, g z θ = g' z θ + h z θ) :
    ∀ z θ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dth g z θ = Work.Spaces.Dth g' z θ + Work.Spaces.Dth h z θ := by
  intro z θ hz hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    simp only [Work.Spaces.Dth]
    rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · subst h2
      simp only [Work.Spaces.Dth]
      rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      ring
    · have hpth := Work.FTS.GalFields.RHS.pth_add_of_smoothOpen hg'sm hhsm hgh z θ hz h0 h2
      simp only [Work.Spaces.Dth]
      rw [hpth]
      ring

/-- Congruence of the `L₁₂`-density on the angular interval. -/
theorem L12dens_congr_of_Iθ {a b : ℝ → ℝ → ℝ} {s : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, a s θ = b s θ) :
    Work.Construction.L12dens a s = Work.Construction.L12dens b s := by
  rw [Work.Construction.L12dens, Work.Construction.L12dens, Work.FM.L12dens]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [h θ hθ]

/-- Congruence of `L₁₂` from the congruence of its densities on the outer half-line. -/
theorem L12_congr_of_dens {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ s ∈ Set.Ioi z, Work.Construction.L12dens a s = Work.Construction.L12dens b s) :
    Work.Construction.L12 a z = Work.Construction.L12 b z := by
  rw [Work.Construction.L12, Work.Construction.L12, Work.FM.L12]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h



end Work.FTS.GalFields.RHS.SharpMod
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharp_muBlock_summand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

open scoped Real
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The pointwise tools

The `μ`-block of the dynamic right-hand side is `-μ̄·AK α + N_* μ (lamfun μ) g`, and the estimate
below is the pointwise telescoping of that block along the difference `d = g - g'`, using

* the paper's collapse `N_* μ (lamfun μ) g = μ·(D_z g - g)` (valid for `μ ≠ -1`; the two
  hypotheses `|μ| ≤ 1/2` of the statement are what produce `μ ≠ -1`);
* the additivity of `D_z` on the open quadrant for a pointwise decomposition `g = d + g'`.

On the `HkNorm`-side everything is then the subadditivity of `HkNorm` on the open-quadrant class
(`RHS.HkNorm_add_le_open`) together with the two `ℋ⁵`-comparisons `Xn_Dz_le_Xn5` and
`HkNorm_mono_of_mem`. -/

/-- **`D_z` is additive on the open quadrant for a pointwise decomposition `f = f' + k`.** -/
private lemma Dz_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : SmoothOpen f') (hk : SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ + Work.Spaces.Dz k z θ := by
  intro z θ hz hθ0 hθ1
  have h1 := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := f)
    (G := fun z θ => f' z θ + k z θ) (fun z θ _ _ _ => h z θ) 1 z θ hz hθ0 hθ1
  have h2 := Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf' hk 1 z θ hz hθ0 hθ1
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1.trans h2

/-- `Xn` only sees the values on the open quadrant. -/
private lemma Xn_congr_open (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.Nonlin.Xn α f = Work.FTS.Nonlin.Xn α g := by
  rw [show Work.FTS.Nonlin.Xn α f = Work.Spaces.HkNorm α 4 f from rfl,
    show Work.FTS.Nonlin.Xn α g = Work.Spaces.HkNorm α 4 g from rfl,
    Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α 4 h]

/-- `Xn` is homogeneous for the multiplication by a scalar. -/
private lemma Xn_const_mul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => c * f z θ) = |c| * Work.FTS.Nonlin.Xn α f := by
  have h1 : (fun z θ : ℝ => c * f z θ) = c • f := by
    funext z θ; simp [Pi.smul_apply, smul_eq_mul]
  rw [h1]
  exact Work.FTS.EllipticEst.HkNorm_smul c α 4 f

/-- **Subadditivity of `Xn` on the open-quadrant class**, in the difference form. -/
private lemma Xn_sub_le (α : ℝ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ)
      ≤ 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α g) := by
  have hgs : SmoothOpen (fun z θ => -g z θ) := hg.neg
  have hgm : Work.Spaces.HkMem α 4 (fun z θ => -g z θ) := Work.FTS.NonlinRows.HkMem_neg' α 4 hmg
  have h1 := HkNorm_add_le_open α 4 hα hf hgs hmf hgm
  have hneg : Work.Spaces.HkNorm α 4 (fun z θ : ℝ => - g z θ) = Work.Spaces.HkNorm α 4 g := by
    have h2 : (fun z θ : ℝ => - g z θ) = (-1 : ℝ) • g := by
      funext z θ; simp [Pi.smul_apply]
    rw [h2, Work.FTS.EllipticEst.HkNorm_smul]
    norm_num
  rw [hneg] at h1
  rw [Xn_congr_open α (f := fun z θ => f z θ - g z θ) (g := fun z θ => f z θ + - g z θ)
    (fun z θ _ _ _ => by ring)]
  simpa only [Work.FTS.Nonlin.Xn] using h1


end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.SolFire.isBslSolPos_psiFire_extG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Real

namespace Work.FTS_FinalLeaves.SolFire

/-! ## The two pointwise facts about the firing stream function

`psiFire Φs E g` is the odd extension in `θ` of the cut `PsiCan Φs E g`; on the branch
`θ > 0` it *is* the canonical stream function, and at `θ = 0` it vanishes (the cut). -/

/-- `psiFire` agrees with the canonical stream function on the branch `θ > 0`
(restated here so that it can be used without re-importing the `FinalV2` development). -/
theorem slice_psiFire_of_pos {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.FTS.FinalV2.psiFire Φs E g z θ τ = Work.FTS.Nonlin.PsiCan Φs E g z θ τ :=
  Work.FTS.FinalV2.psiFire_of_pos hθ

/-- `psiFire` vanishes on the axis `θ = 0`, for every `z` and every `τ`. -/
theorem slice_psiFire_zero {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} (z τ : ℝ) :
    Work.FTS.FinalV2.psiFire Φs E g z 0 τ = 0 := by
  simp only [Work.FTS.FinalV2.psiFire, Work.FTS.BSIdent.PhiOdd, Work.FTS.FinalV2.psiCut,
    le_refl, ite_true]
  simp

/-- `extG` agrees with `g` at every `z > 0` and `τ ≥ 0`, whence the same for `Ftau`. -/
theorem Ftau_extG_of_pos {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    {z θ : ℝ} (hz : 0 < z) :
    Work.Construction.Ftau α (Work.FTS.RegPkgGal.extG g) τ z θ
      = Work.Construction.Ftau α g τ z θ := by
  simp only [Work.Construction.Ftau, Work.FTS.RegPkgGal.extG_of_pos hz hτ]

theorem isBslSolPos_psiFire_extG {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {τ : ℝ}
    (hτ : 0 ≤ τ)
    (h : Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α g τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) :
    Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α (Work.FTS.RegPkgGal.extG g) τ)
      (Work.FTS.Galerkin.slice (Work.FTS.FinalV2.psiFire Φs E g) τ) := by
  obtain ⟨heq, h0, h1, hdec⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the equation on the open quadrant: `psiFire = PsiCan` there and `extG = g` at `z > 0`
    intro z hz θ hθ hθ2
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩
    rw [Work.FTS.PhiStar.bslOp_congr α
      (Work.FTS.Galerkin.slice (Work.FTS.FinalV2.psiFire Φs E g) τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) hmem
      (fun z' θ' h' => by
        obtain ⟨-, hθ', -⟩ := (Work.FTS.EllipticEst.mem_Q0).mp h'
        exact slice_psiFire_of_pos hθ')]
    rw [heq z hz θ hθ hθ2]
    exact (Ftau_extG_of_pos hτ hz).symm
  · -- the Dirichlet condition at `θ = 0`: the cut kills the value
    intro z _
    exact slice_psiFire_zero z τ
  · -- the Dirichlet condition at `θ = π/2`
    intro z hz
    have hpos : (0 : ℝ) < π / 2 := by positivity
    change Work.FTS.FinalV2.psiFire Φs E g z (π / 2) τ = 0
    rw [slice_psiFire_of_pos hpos]
    exact h1 z hz
  · -- decay in `z` at fixed `θ ∈ Iθ`
    intro θ hθ
    rw [Work.Spaces.Iθ] at hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0]
      have hconst : (fun z : ℝ => Work.FTS.Galerkin.slice
          (Work.FTS.FinalV2.psiFire Φs E g) τ z 0) = fun _ : ℝ => (0 : ℝ) := by
        funext z
        exact slice_psiFire_zero z τ
      rw [hconst]
      exact tendsto_const_nhds
    · have hev : (fun z : ℝ => Work.FTS.Galerkin.slice
            (Work.FTS.FinalV2.psiFire Φs E g) τ z θ)
          =ᶠ[atTop] (fun z : ℝ => Work.FTS.Galerkin.slice
            (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ) := by
        filter_upwards with z
        exact slice_psiFire_of_pos hθ0
      exact Filter.Tendsto.congr' hev.symm (hdec θ ⟨hθ.1, hθ.2⟩)

end Work.FTS_FinalLeaves.SolFire
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.classC_sup_le_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_FinalLeaves.classC_sup_le_proved`

Elgindi's Corollary `SecondDerivativesBounded` in the `(b,a) = (0,0)` case, on the elliptic
class `Work.FTS.ClassC.ClassC`:

  `|f(z,θ)| ≤ 10/√(γ-1) · |f|_{ℋ⁴}`   (`γ = 1 + α/10`, `f ∈ ClassC α`, `(z,θ) ∈ Qd`).

The class `ClassC` constrains `f` only on the **open** quadrant (`SmoothOpen f`, `C^∞` on
`z > 0`, `0 < θ < π/2`), together with the honesty `HkMem α 7 f` and the boundary traces
`BdryTraces α 6 f`; it gives no smoothness across `z = 0`, so the `RegQ`/`SmoothQuad` form
`Work.FTS.RegPkgGal.Der.abs_mixed_le_HkNorm_RegQ` of the corollary does not apply.

The proof below is the two one-dimensional Hardy steps of the corollary, run entirely in the
open class:

* **angular step.**  `f` is `C^∞` on the open quadrant, its `θ`-slices are `C^∞` on `(0,π/2)`,
  and the angular clause of `BdryTraces` makes the slice vanish at `θ → 0⁺`; the weighted
  Cauchy–Schwarz/Hardy inequality on the interval (with the singular weight
  `sin(2σ)^{2-γ}`) gives

    `f(z,θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θf(z,σ))² sin(2σ)^{2-γ} dσ`.

* **radial step.**  On the open quadrant the identity `D_z(D_θf) = sin(2θ)·(z∂_z∂_θf)` puts
  the angular Hardy integrand into the mixed slot `D_zD_θf`; applying the radial Hardy
  inequality (`Work.FTS.H2.hardyZ_open`) to the `z`-slice of `D_θf` — which decays at
  `z → ∞` by the radial clause of `BdryTraces` — turns that slot into the `(1,1)`-slot of the
  `ℋ⁴`-norm, which the Tonelli lemma `Work.FTS.StrongEps.SupPort.slotM_open` bounds by
  `HkSq α 4 f`.

Both Hardy inequalities and the slot Tonelli swap are one-purpose lemmas proved elsewhere in
the workspace (`HardyThetaOpen`, `hardyZ_open`, `slotM_open`,
`integrableOn_pth_mixed_sq_sin`); the assembly below is the argument of the corollary.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_FinalLeaves

/-- **The interior `L^∞`–`ℋ⁴` trade-off on the class `C`** (Elgindi, Corollary
`SecondDerivativesBounded`, `(b,a) = (0,0)` instance): on the open quadrant `Qd = (0,∞)×(0,π/2)`
every `f ∈ ClassC α` with `0 < α ≤ 1` satisfies `|f(z,θ)| ≤ 10/√(γ-1)·|f|_{ℋ⁴}`. -/
theorem classC_sup_le_proved {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f → ∀ z θ,
      (z, θ) ∈ Work.Construction.Qd →
      |f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
  intro f hf z θ hzθ
  -- unpack the point of the open quadrant and the class
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hzθ.2.1, hzθ.2.2⟩
  have hF : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem
  have hbd : Work.FTS.Nonlin.BdryTraces α 4 f := hf.bdry_le_six (by norm_num)
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγne : Work.Spaces.gam α ≠ 0 := by
    have h1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
    linarith
  have hKnn : 0 ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the `(1,1)`-slot of the `ℋ⁴`-norm, and its two integrability consequences
  obtain ⟨hslot_le, hslot_int, hslot_ae⟩ :=
    Work.FTS.StrongEps.SupPort.slotM_open α f hF hmem 1 1 (le_refl 1) (by norm_num)
  -- the radial-slice energy of the `(1,1)`-slot
  set B : ℝ → ℝ := fun σ => ∫ s in Work.Spaces.Iz,
    (Work.Spaces.mixed 1 1 f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 with hBdef
  -- the angular Hardy integrand is integrable at the fixed `z`
  have hint_ang : IntegrableOn (fun σ => (Work.Spaces.pth f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.FTS.StrongEps.SupPort.integrableOn_pth_mixed_sq_sin hα hα1 hF hmem 0 0
      (by norm_num) hz
  -- the slice vanishes at `θ → 0⁺`, from the angular clause of `BdryTraces`
  have hlim0 : Tendsto (fun θ' => f z θ') (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h := Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero (f := f) hα hbd (a := 0) (b := 0)
      (by norm_num) hz
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  -- the angular Hardy inequality at `(z,θ)`
  have hHT :=
    Work.FTS.StrongEps.SupPort.HardyThetaOpen α hα hα1 f z hF hz hlim0 hint_ang θ hθ
  -- the angular Hardy integrand is the `(0,1)`-slot against `sin(2σ)^{-γ}`
  have hI1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.Dth f z σ) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    show (Work.Spaces.pth f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 f z σ hσ]
    ring
  have hDth_int : IntegrableOn (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.Dth f z σ) ^ 2) Work.Spaces.Iθ := by
    refine hint_ang.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    show (Work.Spaces.pth f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 f z σ hσ]
    ring
  -- the radial Hardy inequality on the `D_θ f`-slice, for almost every angle
  have hrad : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
    filter_upwards [hslot_ae, ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with σ hσint hσI
    rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
    · -- the endpoint `σ = 0`, where the singular weight vanishes
      have hs0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hs0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
    · -- the endpoint `σ = π/2`
      have hs0 : Real.sin (2 * σ) = 0 := by
        rw [hσeq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hs0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    · -- an interior angle: the radial Hardy inequality for `s ↦ D_θ f(s,σ)`
      have hσ' : σ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hσpos, hσlt⟩
      refine mul_le_mul_of_nonneg_left ?_
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσI) _)
      have hcd : ContDiffOn ℝ 1 (fun s => Work.Spaces.Dth f s σ) (Set.Ioi 0) :=
        (hF.Dth.curry_z hσ').of_le (by simp [Work.Stability.smoothOrder])
      have hdec : Tendsto (fun s => Work.Spaces.Dth f s σ) atTop (𝓝 0) := by
        have h := Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero (f := f) hbd (a := 1) (b := 0)
          (by norm_num) hσ'
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using h
      have hint2 : IntegrableOn
          (fun s => (s * deriv (fun s => Work.Spaces.Dth f s σ) s) ^ 2
            * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := hσint
      have hzr := Work.FTS.H2.hardyZ_open hcd hdec hint2 z (Set.mem_Ioi.mpr hz)
      rw [hBdef]
      exact hzr
  -- the radial-slice energy is the `θ`-first form of the `(1,1)`-slot
  have hBpt : ∀ σ ∈ Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ
        = ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2 := by
    intro σ hσ
    rw [hBdef]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun s _ => ?_
    show (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ((Work.Spaces.mixed 1 1 f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2
    rw [mul_pow, Work.FTS.H2.HQ.Wt_sq_quad α s σ hσ]
    ring
  have hBeq : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun σ => ∫ s in Work.Spaces.Iz,
        (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2) := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => hBpt σ hσ)
  have hTint : Integrable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      (volume.restrict Work.Spaces.Iθ) := hslot_int.congr hBeq.symm
  -- the angular Hardy integrand is dominated by the radial-slice energy
  have hIntLe : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth f z σ) ^ 2) ≤ ∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ :=
    integral_mono_ae hDth_int hTint hrad
  have hfin : (f z θ) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1))
      * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ) := by
    have h1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        ≤ ∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
      rw [hI1]; exact hIntLe
    exact le_trans hHT (mul_le_mul_of_nonneg_left h1 hKnn)
  -- bound the energy by the `ℋ⁴`-norm (Tonelli for the `(1,1)`-slot, in the `θ`-first order)
  have hTle : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      ≤ Work.Spaces.HkSq α 4 f := by
    rw [show (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
        = ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2
        from integral_congr_ae hBeq]
    exact hslot_le
  -- the constants
  have hfinal : (f z θ) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f :=
    le_trans hfin (mul_le_mul_of_nonneg_left hTle hKnn)
  have hsqrt : Real.sqrt (100 / (Work.Spaces.gam α - 1))
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) := by
    have h2 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h2]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  have hconst : Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f)
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
    rw [Real.sqrt_mul hKnn, hsqrt]
    simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  calc |f z θ| = Real.sqrt ((f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f) :=
        Real.sqrt_le_sqrt hfinal
    _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := hconst

end Work.FTS_FinalLeaves
end
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.merPsi_C3_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C³` regularity of the meridian slice of the reconstruction's stream function

`merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ(ρ(r,z)^α/B(τ), θ(r,z), τ)`, `τ = clockInv C t`,
with `Φ = psiFire Φs E g` the **odd extension in `θ`** of the canonical stream function `PsiCan`.

This is the `C³` companion of `BSIdent.Defs.contDiffAt_merPsi_slice` (which is stated for the `C²`
class and applies the odd extension *inside* `merPsi`).  Here the odd extension is already part of
the profile, so the argument is the same branch analysis plus one extra differentiation order:

* off the degenerate set (`r > 0`, `z ≠ 0`) the angle `θ(r,z) = arctan(z/r)` is nonzero, and the
  sign of `θ` is constant near `(r,z)`;
* on the branch `θ > 0` the profile is `PsiCan` itself (`psiFire_of_pos`);
* on the branch `θ < 0` it is `θ ↦ -PsiCan(·, -θ)` with `-θ > 0` (`psiFire_of_neg`);
* in both cases the polar dictionary `(r,z) ↦ (ρ^α/B(τ), ±θ(r,z))` is `C³` at `(r,z)` (only
  `r > 0` is needed), so the composition with the `C³` hypothesis on `PsiCan` applies.
-/

open Filter Set
open scoped Topology

namespace Work.FTS_FinalLeaves

/-- Unfolding of `Work.FTS.MeridianDyn.merPsi` at a point (definitional). -/
private lemma merPsi_apply' (p : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.Galerkin.Fam)
    (C : Work.FTS.Physical.PhysClock) (r z t : ℝ) :
    Work.FTS.MeridianDyn.merPsi p A B Φ C r z t
      = Work.Cyl.rhoP r z ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹
        * Φ (Work.Cyl.rhoP r z ^ p / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP r z) (Work.FTS.Physical.clockInv C t) := rfl

/-- The **negative-angle branch** of `psiFire`: for `θ < 0` the odd extension reads
`-PsiCan (·, -θ)` (the cut `psiCut` is inactive because `-θ > 0`). -/
private lemma psiFire_of_neg {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {z θ τ : ℝ} (hθ : θ < 0) :
    Work.FTS.FinalV2.psiFire Φs E g z θ τ = - Work.FTS.Nonlin.PsiCan Φs E g z (-θ) τ := by
  simp only [Work.FTS.FinalV2.psiFire, Work.FTS.BSIdent.PhiOdd, Work.FTS.FinalV2.psiCut,
    if_neg (not_le.mpr hθ), if_pos (neg_pos.mpr hθ)]

/-- The polar dictionary is `C³` at every point of the half-plane `r > 0`: the radius
`ρ(r,z) = √(r²+z²)`, the self-similar argument `ρ^p/b` and the angle `θ(r,z) = arctan(z/r)`,
together with the geometric prefactor `ρ²`. -/
private lemma contDiffAt_polar (p b : ℝ) {r z : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2) (r, z) ∧
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ p / b) (r, z) ∧
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2) (r, z) := by
  have hρ : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) := by fun_prop
    have h2 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) ≠ 0 := by
      show r ^ 2 + z ^ 2 ≠ 0
      positivity
    have h3 := (Real.contDiffAt_sqrt (n := 3) h2).comp (r, z) h1
    simpa [Work.Cyl.rhoP, Function.comp_def] using h3
  refine ⟨?_, ?_, ?_⟩
  · simpa using hρ.pow 2
  · have h4 := hρ.rpow_const_of_ne (p := p) (Work.Cyl.rhoP_ne_zero hr z)
    simpa [div_eq_mul_inv] using
      h4.mul (contDiffAt_const (c := b⁻¹) :
        ContDiffAt ℝ 3 (fun _ : ℝ × ℝ => b⁻¹) (r, z))
  · have h1 : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => q.2 / q.1) (r, z) := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa using hr.ne'
    have h3 := Real.contDiff_arctan.contDiffAt.comp (r, z) h1
    simpa [Work.Cyl.thetaP, Function.comp_def] using h3

theorem merPsi_C3_proved {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hC3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ)
        Work.Construction.Qd)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ =>
        Work.FTS.MeridianDyn.merPsi α A B (Work.FTS.FinalV2.psiFire Φs E g) C p.1 p.2 t)
        (r, z) := by
  intro t ht r z hr hz
  -- the clock value and the hypotheses it feeds
  have hτ : 0 ≤ Work.FTS.Physical.clockInv C t :=
    Work.FTS.Physical.clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hBτ : 0 < B (Work.FTS.Physical.clockInv C t) := hB _ hτ
  have hΨ := hC3 _ hτ
  -- the polar dictionary at `(r,z)`
  obtain ⟨hρ2, hρp, hθ⟩ := contDiffAt_polar α (B (Work.FTS.Physical.clockInv C t)) hr
  -- the self-similar argument is positive, the angle is non-zero and `< π/2`
  have hw : 0 < Work.Cyl.rhoP r z ^ α / B (Work.FTS.Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hBτ
  have hθ0 : Work.Cyl.thetaP r z ≠ 0 := by
    simp only [Work.Cyl.thetaP]
    exact fun h => (div_ne_zero hz hr.ne') (Real.arctan_eq_zero_iff.mp h)
  have hθlt : Work.Cyl.thetaP r z < Real.pi / 2 := by
    simpa only [Work.Cyl.thetaP] using Real.arctan_lt_pi_div_two (z / r)
  have hθgt : -(Real.pi / 2) < Work.Cyl.thetaP r z := by
    simpa only [Work.Cyl.thetaP] using Real.neg_pi_div_two_lt_arctan (z / r)
  have hQd : Work.Construction.Qd = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := rfl
  rcases lt_or_gt_of_ne hθ0 with hneg | hpos
  · -- ### branch `θ(r,z) < 0`: the profile is `(w,φ) ↦ -PsiCan (w,-φ)`
    have hbase : ContDiffAt ℝ 3
        (fun p : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g p.1 p.2
          (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ α / B (Work.FTS.Physical.clockInv C t),
          -Work.Cyl.thetaP r z) :=
      hΨ.contDiffAt (by
        rw [hQd]
        exact (isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          ⟨hw, by linarith, by linarith⟩)
    have hcomp : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.FTS.Nonlin.PsiCan Φs E g
          (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
          (-(Work.Cyl.thetaP q.1 q.2)) (Work.FTS.Physical.clockInv C t)) (r, z) := by
      have h := hbase.comp (r, z) (hρp.prodMk hθ.neg)
      simpa [Function.comp_def] using h
    have hfinal : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹ *
          -(Work.FTS.Nonlin.PsiCan Φs E g
            (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
            (-(Work.Cyl.thetaP q.1 q.2)) (Work.FTS.Physical.clockInv C t))) (r, z) :=
      (hρ2.mul (contDiffAt_const (c := (A (Work.FTS.Physical.clockInv C t))⁻¹) :
        ContDiffAt ℝ 3 (fun _ : ℝ × ℝ => (A (Work.FTS.Physical.clockInv C t))⁻¹)
          (r, z))).mul hcomp.neg
    refine hfinal.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | Work.Cyl.thetaP q.1 q.2 < 0} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    filter_upwards [hnb] with q hq
    rw [merPsi_apply', psiFire_of_neg hq]
  · -- ### branch `0 < θ(r,z)`: the profile is `PsiCan` itself
    have hbase : ContDiffAt ℝ 3
        (fun p : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g p.1 p.2
          (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z) :=
      hΨ.contDiffAt (by
        rw [hQd]
        exact (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hw, hpos, hθlt⟩)
    have hcomp : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.FTS.Nonlin.PsiCan Φs E g
          (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP q.1 q.2) (Work.FTS.Physical.clockInv C t)) (r, z) := by
      have h := hbase.comp (r, z) (hρp.prodMk hθ)
      simpa [Function.comp_def] using h
    have hfinal : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹ *
          Work.FTS.Nonlin.PsiCan Φs E g
            (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP q.1 q.2) (Work.FTS.Physical.clockInv C t)) (r, z) :=
      (hρ2.mul (contDiffAt_const (c := (A (Work.FTS.Physical.clockInv C t))⁻¹) :
        ContDiffAt ℝ 3 (fun _ : ℝ × ℝ => (A (Work.FTS.Physical.clockInv C t))⁻¹)
          (r, z))).mul hcomp
    refine hfinal.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | 0 < Work.Cyl.thetaP q.1 q.2} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [hnb] with q hq
    rw [merPsi_apply', Work.FTS.FinalV2.psiFire_of_pos hq]

end Work.FTS_FinalLeaves
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.mu6_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin Work.FTS.FinalV2

namespace Work.FTS_FinalLeaves

theorem mu6_proved {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hML : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hLip : Work.FTS.FinalV2.MuLipC α C₀ Φs E) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    (∀ τ : ℝ, 0 ≤ τ →
        |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
    ContinuousOn (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g) (Set.Ici 0) ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ'|
          ≤ L * |τ - τ'| ^ β := by
  have hLA : Work.FTS.FinalV2.LimApprox α C₀ Φs E g := hOK.2
  obtain ⟨Lμ, hLμ0, hLμ⟩ := hLip
  set F : ℝ → ℝ := fun τ => muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ with hF
  -- `muDyn` only depends on the fake-time slice of the family
  have hslice : ∀ (gg : Fam) (τ : ℝ), muDyn α (Work.FTS.Nonlin.PsiCan Φs E gg) gg τ
      = muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.cst (slice gg τ)))
          (Work.FTS.FinalV2.cst (slice gg τ)) 0 := fun gg τ => rfl
  -- Conjunct 1: the uniform bound `|μ| ≤ 1/2`, obtained by approximation from class-`C` slices.
  have hbdd : ∀ τ : ℝ, 0 ≤ τ → |F τ| ≤ 1 / 2 := by
    intro τ hτ
    obtain ⟨gn, B, L, hgn, hglip, hgj, hgm⟩ := hLA (τ + 1) (by linarith)
    have hb : ∀ n, |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ| ≤ 1 / 2 := by
      intro n
      obtain ⟨hc, hx, -⟩ := hgn n τ ⟨hτ, by linarith⟩
      have hh := (hML (slice (gn n) τ) hc hx).1
      rwa [hslice (gn n) τ]
    have hlim : Tendsto (fun n => |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ|)
        atTop (𝓝 |F τ|) := by
      have hh := (hgm τ ⟨hτ, by linarith⟩).abs
      simpa [hF] using hh
    exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall hb)
  -- Lipschitz on every `[0,S]`: the `τ`-Lipschitz modulus of the approximating class-`C`
  -- families in the `ℋ⁴`-norm, composed with the class-`C` Lipschitz bound `hLip` on `muDyn`.
  have hLipF : ∀ S : ℝ, 0 < S → ∃ K : ℝ, 0 ≤ K ∧
      ∀ τ ∈ Icc (0 : ℝ) S, ∀ τ' ∈ Icc (0 : ℝ) S, |F τ - F τ'| ≤ K * |τ - τ'| := by
    intro S hS
    obtain ⟨gn, B, L, hgn, hglip, hgj, hgm⟩ := hLA (max S 1) (lt_max_of_lt_right one_pos)
    refine ⟨max (Lμ * L) 0, le_max_right _ _, ?_⟩
    intro τ hτ τ' hτ'
    have hτT : τ ∈ Icc (0 : ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 (le_max_left _ _)⟩
    have hτ'T : τ' ∈ Icc (0 : ℝ) (max S 1) := ⟨hτ'.1, le_trans hτ'.2 (le_max_left _ _)⟩
    have hb : ∀ n, |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ
        - muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ'| ≤ Lμ * (L * |τ - τ'|) := by
      intro n
      obtain ⟨hc, hx, -⟩ := hgn n τ hτT
      obtain ⟨hc', hx', -⟩ := hgn n τ' hτ'T
      have h1 := hLμ (slice (gn n) τ) (slice (gn n) τ') hc hc' hx hx'
      rw [← hslice (gn n) τ, ← hslice (gn n) τ'] at h1
      calc |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ
              - muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ'|
          ≤ Lμ * Work.FTS.Nonlin.Xn α (slice (gn n) τ - slice (gn n) τ') := h1
        _ ≤ Lμ * (L * |τ - τ'|) := mul_le_mul_of_nonneg_left (hglip n τ hτT τ' hτ'T) hLμ0
    have hlim : Tendsto (fun n => |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ
        - muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ'|) atTop (𝓝 |F τ - F τ'|) := by
      have hh := ((hgm τ hτT).sub (hgm τ' hτ'T)).abs
      simpa [hF] using hh
    have h2 := le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall hb)
    calc |F τ - F τ'| ≤ Lμ * (L * |τ - τ'|) := h2
      _ = (Lμ * L) * |τ - τ'| := by ring
      _ ≤ max (Lμ * L) 0 * |τ - τ'| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  -- Conjunct 2: continuity on `[0,∞)` from the local Lipschitz bound.
  have hcont : ContinuousOn F (Ici 0) := by
    have hloc : LocallyLipschitzOn (Ici 0) F := by
      intro x hx
      have hx0 : 0 ≤ x := hx
      obtain ⟨K, hK0, hK⟩ := hLipF (x + 1) (by linarith)
      refine ⟨⟨K, hK0⟩, Icc 0 (x + 1), ?_, ?_⟩
      · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Iio (x + 1), Iio_mem_nhds (by linarith), fun y hy => ⟨hy.2, hy.1.le⟩⟩
      · exact LipschitzOnWith.of_dist_le_mul (fun τ hτ τ' hτ' => by
          rw [Real.dist_eq, Real.dist_eq]; exact hK τ hτ τ' hτ')
    exact hloc.continuousOn
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hF] using hbdd
  · simpa only [hF] using hcont
  -- Conjunct 3: `β`-Hölder on `[0,S]` from the Lipschitz bound, `|τ-τ'| ≤ max 1 S^{1-β}|τ-τ'|^β`.
  · intro β hβ0 hβ1 S hS
    obtain ⟨K, hK0, hK⟩ := hLipF S hS
    refine ⟨K * max 1 (S ^ (1 - β)), mul_nonneg hK0 (le_trans zero_le_one (le_max_left _ _)), ?_⟩
    intro τ hτ τ' hτ'
    have hmain : |F τ - F τ'| ≤ K * max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by
      have h1 : |F τ - F τ'| ≤ K * |τ - τ'| := hK τ hτ τ' hτ'
      have hx0 : 0 ≤ |τ - τ'| := abs_nonneg _
      have hxS : |τ - τ'| ≤ S := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
      have h2 : |τ - τ'| ≤ max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by
        rcases hx0.eq_or_lt with h | h
        · rw [← h, Real.zero_rpow (ne_of_gt hβ0), mul_zero]
        · have hxb : 0 ≤ |τ - τ'| ^ β := Real.rpow_nonneg hx0 β
          have hone : |τ - τ'| ^ (1 - β) ≤ max 1 (S ^ (1 - β)) :=
            le_trans (Real.rpow_le_rpow hx0 hxS (by linarith)) (le_max_right _ _)
          calc |τ - τ'| = |τ - τ'| ^ (β + (1 - β)) := by
                rw [show β + (1 - β) = 1 by ring, Real.rpow_one]
            _ = |τ - τ'| ^ β * |τ - τ'| ^ (1 - β) := Real.rpow_add h β (1 - β)
            _ ≤ |τ - τ'| ^ β * max 1 (S ^ (1 - β)) := mul_le_mul_of_nonneg_left hone hxb
            _ = max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by ring
      calc |F τ - F τ'| ≤ K * |τ - τ'| := h1
        _ ≤ K * (max 1 (S ^ (1 - β)) * |τ - τ'| ^ β) := mul_le_mul_of_nonneg_left h2 hK0
        _ = K * max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by ring
    simpa only [hF] using hmain

end Work.FTS_FinalLeaves
end
end
