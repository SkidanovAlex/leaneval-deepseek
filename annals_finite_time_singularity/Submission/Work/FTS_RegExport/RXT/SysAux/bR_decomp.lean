import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.FinalV2.Sanitize
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Support.FstarPartCont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR7.Support

set_option autoImplicit false

/-- `F_*(·,·) = β·(Γ(θ)/c(β))·(2z/(1+z)²)` is `C^n` on the open quadrant `Q0`, for **every**
real exponent `β` (no sign hypothesis: on `Q0` the base `sin θ cos²θ` of the real power is
strictly positive, and division by `c β` is harmless since `c β = 0` only makes `F_*` vanish). -/
theorem contDiffOn_uncurry_Fstar_Q0 (β : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Construction.Fstar β)) Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.contDiffOn_Gam_Q0 β n
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam β p.2 / Work.Spaces.c β)
      Work.FTS.EllipticEst.Q0 := hGam.div_const _
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => β * (Work.Spaces.Gam β p.2 / Work.Spaces.c β))
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_fst_of (Work.FTS_RegExport.RXT.contDiffOn_FM_Fstar n)
  exact (h2.mul h3).congr (fun _ _ => rfl)

/-- The reference profile `F_* = β(Γ/c)·F_{*,rad}` is `C^∞` on the open quadrant, for every
real `β`. -/
theorem smoothOpen_Fstar (β : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar β) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (contDiffOn_uncurry_Fstar_Q0 β)

/-- **Joint continuity of `(∂_zF_*, ∂_θF_*)` on the open quadrant.**  Each component is
`C^∞` there (`smoothOpen_Fstar` + `SmoothOpen.pz` / `SmoothOpen.pth`), hence continuous. -/
theorem FstarPartCont {α : ℝ} :
    ContinuousOn (fun q : ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) :=
    smoothOpen_Fstar (Work.FTS.Regularity.pExp α)
  have h1 : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pz
      (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) q.1 q.2)
      Work.FTS.EllipticEst.Q0 := hso.pz.continuousOn
  have h2 : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.pth
      (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) q.1 q.2)
      Work.FTS.EllipticEst.Q0 := hso.pth.continuousOn
  exact h1.prodMk h2

end Work.FTS_RegExport.RXR7.Support
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.C2Final =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.C2Final` — the assembly of S4 (`coeff_C2`)

`coeff_C2_assembly` takes the three inputs of the pointwise argument — the `C³`-regularity of
the stream-function slice `slice (psiR α Φs E (tauExt g)) τ` on the open quadrant
(`C2Psi.contDiffOn_slice_PhiR_Q0`) and the `C²`/`C³`-regularity of the two radial functions
`𝔽K(F(τ))`, `L₁₂(F(τ))` on `(0,∞)` — and produces the three `C²`-statements for `Vz7`, `Vθ7`,
`cs7`; `coeff_C2` instantiates them (the radial inputs come from the parametric-integral and
primitive lemmas, applied to `Ftau_bounds`).
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (DynOK' LimApprox)
open Work.FTS.RegExportIface.RXT (GR ΦR μR VR bR cR)

set_option autoImplicit false

/-- `c2m` is `C²` on the open interval. -/
theorem contDiffOn_c2m : ContDiffOn ℝ 2 Work.Construction.c2m (Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ 2 (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have h2 : ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).pow 2
  refine (h1.sub h2).congr (fun θ _ => ?_)
  simp only [Work.Construction.c2m]

/-- The stream function slice is `C^n` on `(0,∞)` when it is `C^n` at the fixed angle. -/
theorem contDiffOn_slice_fst {n : ℕ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ n a (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0 :=
  ha.comp contDiffOn_fst (fun p hp => hp.1)

/-- **The pointwise assembly.**  Given the `C³`-stream function and the two radial profiles,
the three coefficients of `(E)` are `C²` on the open quadrant. -/
theorem coeff_C2_assembly {α αG C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hαG : αG ≠ 0)
    (hΦ3 : ContDiffOn ℝ 3 (Function.uncurry (slice (ΦR α Φs E g) τ))
      Work.FTS.EllipticEst.Q0)
    (hFK2 : ContDiffOn ℝ 2 (Work.Construction.FK (Work.Construction.Ftau αG (GR α g) τ))
      (Set.Ioi 0))
    (hL12 : ContDiffOn ℝ 3 (Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ))
      (Set.Ioi 0)) :
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vz7 αG (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ))
      Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vθ7 αG (ΦR α Φs E g) z θ τ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.cs7 αG (μR α Φs E g) (GR α g) (ΦR α Φs E g) z θ τ))
      Work.FTS.EllipticEst.Q0 := by
  have hL2 : ContDiffOn ℝ 2 (Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ))
      (Set.Ioi 0) := hL12.of_le (by norm_num)
  have hc2m := contDiffOn_c2m
  -- the `θ`-weights
  have hsin2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((Real.contDiff_sin.contDiffOn).pow 2).comp contDiffOn_snd (fun p hp => hp.2)
  have hsin2θ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hsin : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  -- Θ and Φ̃
  have hTheta : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta αG (Work.Construction.Ftau αG (GR α g) τ)))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (1 / (4 * αG)) * Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hsin
    have h2 := contDiffOn_slice_fst hL12
    refine (h1.mul h2).congr ?_
    intro p _
    simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  have hPsi : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.PhiTil αG
      (Work.Construction.Ftau αG (GR α g) τ) (slice (ΦR α Φs E g) τ)))
      Work.FTS.EllipticEst.Q0 := hΦ3.sub hTheta
  have hVop := contDiffOn_uncurry_Vop hPsi
  have hUop := contDiffOn_uncurry_Uop (α := αG) hΦ3
  have hRop := contDiffOn_uncurry_Rop (α := αG) hPsi
  refine ⟨?_, ?_, ?_⟩
  · -- Vz7
    have hLmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ) p.1
          * Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_slice_fst hL2).mul (hc2m.comp contDiffOn_snd (fun p hp => hp.2))
    have hV : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        (2 * αG) * Work.Construction.Vop (Work.Construction.PhiTil αG
          (Work.Construction.Ftau αG (GR α g) τ) (slice (ΦR α Φs E g) τ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hVop
    refine (((contDiffOn_const (c := 1 - μR α Φs E g τ)).add hLmul).add hV).congr ?_
    intro p _
    simp only [Function.uncurry, Work.FTS.RegExportIface.Vz7,
      Work.FTS.RegExportIface.phiTil]
  · -- Vθ7 / sin 2θ
    refine (((contDiffOn_const (c := (2 : ℝ))).mul hUop).div hsin2θ
      (fun p hp => ne_of_gt (sin_two_pos_Q0 hp))).congr ?_
    intro p _
    simp only [Pi.div_apply, Function.uncurry, Work.FTS.RegExportIface.Vθ7]
  · -- cs7
    have hLdiv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        Work.Construction.L12 (Work.Construction.Ftau αG (GR α g) τ) p.1 / αG)
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_slice_fst hL2).div contDiffOn_const (fun p hp => hαG)
    have hFKmul : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        Real.sin p.2 ^ 2 * Work.Construction.FK (Work.Construction.Ftau αG (GR α g) τ) p.1)
        Work.FTS.EllipticEst.Q0 :=
      hsin2.mul (hFK2.comp contDiffOn_fst (fun p hp => hp.1))
    have hR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        (2 : ℝ) * Work.Construction.Rop αG (Work.Construction.PhiTil αG
          (Work.Construction.Ftau αG (GR α g) τ) (slice (ΦR α Φs E g) τ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hRop
    refine ((((contDiffOn_const (c := 1 + μR α Φs E g τ)).sub hLdiv).add hFKmul).sub hR).congr ?_
    intro p _
    simp only [Function.uncurry, Work.FTS.RegExportIface.cs7,
      Work.FTS.RegExportIface.phiTil]

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.Ftau_jets_bounded_of_LimApprox =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR)
open Work.FTS.FinalV2 (LimApprox)

set_option autoImplicit false

/-! ## §1 The `g`-part at a fixed horizon `max S 1`

This is `Work.FTS_RegExport.RXT.ftau_DzIter_GR_le` with the horizon `max τ 1` replaced by the
fixed horizon `max S 1` (so that the bound is uniform over `τ ∈ [0,S]`) and with `DynOK'`
replaced by its `LimApprox` half, which is all that `mixed_uniform` uses. -/

lemma ftau_DzIter_GR_le_uniform {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hA : LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) {τ : ℝ} (hτS : τ ∈ Set.Icc (0 : ℝ) S) (j : ℕ) (hj : j ≤ 2) (z θ : ℝ)
    (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter j (slice (GR α g) τ) z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
        * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα1
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.Q0, Set.mem_prod]; exact ⟨hz, h1, h2⟩
  have hEqOn : Set.EqOn (Function.uncurry (slice (GR α g) τ))
      (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    fun p hp => ftau_slice_GR_eq hτS.1 hp.1 hp.2.1.le hp.2.2.le
  have hcongr := Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn j
  have hstep : Work.Spaces.DzIter j (slice (GR α g) τ) z θ
      = Work.Spaces.DzIter j (slice g τ) z θ := hcongr (x := (z, θ)) hmem
  rw [hstep]
  have hT : 0 < max S 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (max S 1) := ⟨hτS.1, le_trans hτS.2 (le_max_left _ _)⟩
  have h := mixed_uniform (α := Work.FTS.Regularity.pExp α) hp0 hp1 hA (max S 1) hT
    τ hτT j 0 (by omega) z θ hmem
  simpa only [Work.Spaces.mixed_zero_right] using h

/-! ## §2 The target -/

/-- Pointwise bounds of the first three `D_z`-jets of the profile `F(τ) = F_* + g(τ)` on the
open quadrant, uniformly in `τ ∈ [0,S]`, from `LimApprox` (which supplies `mixed_uniform` for the
`g`-part) and the `C²`-regularity `hc2` of the slices.

PROOF RECIPE (copy `Work.FTS_RegExport.RXT.Ftau_bounds.Ftau_bounds`, whose `hOK : DynOK'` is used
only through `hOK.1.1.c4` and `hOK.2`):

* put `T := max S 1` (`hT : 0 < T`) so `Icc 0 S ⊆ Icc 0 T`;
* the `F_*` part: `ftau_contDiffOn_Fstar_Q0 (pExp_pos hα) (pExp_le_one hα13)` gives `C²` on `Q0`,
  and `ftau_DzIter_Fstar_le hα hα13 hM j hj` (with `M` from
  `Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7`) bounds `|DzIter j F_*| ≤ 10*M`;
* the `g` part: `Work.FTS_RegExport.RXT.MixedUniform.mixed_uniform hα hα1 hA T hT τ hτT j 0 ...`
  gives `|DzIter j (slice g τ) z θ| ≤ 10/√(γ-1) * (C₀ * (pExp α)^2)` for `j ≤ 2`; transfer it to
  `slice (GR α g) τ` with `ftau_slice_GR_eq hτ` (which needs `0 ≤ τ`, `0 < z`, `0 ≤ θ ≤ π/2`) and
  `Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0`;
* additivity of `DzIter 1`/`DzIter 2` on the sum: `ftau_DzIter_one_add`/`ftau_DzIter_two_add`,
  whose `ContDiffOn ℝ 1`/`ContDiffOn ℝ 2` inputs for the `g`-part come from `hc2 τ hτ` (transferred
  to `GR` with `Work.FTS.H2.DzIter_congr_of_isOpen`/`ContDiffOn.congr`) and for `F_*` from the
  `F_*`-smoothness above;
* conclude with `abs_add_le` and `C := 10*M + |10/√(γ-1) * (C₀ * (pExp α)^2)|`. -/
theorem Ftau_jets_bounded_of_LimApprox {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) (hS : 0 < S)
    (hc2 : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ z θ| ≤ C ∧
      |Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C ∧
      |Work.Spaces.DzIter 2 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  set K : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hK
  refine ⟨10 * M + |K|, ?_, ?_⟩
  · have h10M : 0 ≤ 10 * M := by linarith
    linarith [abs_nonneg K]
  · intro τ hτS z θ hz h1 h2
    have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
    have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
    have hτ : 0 ≤ τ := hτS.1
    have hFc : ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 :=
      ftau_contDiffOn_Fstar_Q0 hp0 hp1
    have hGc : ContDiffOn ℝ 2
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 :=
      (hc2 τ hτS).congr (fun p hp => ftau_slice_GR_eq hτ hp.1 hp.2.1.le hp.2.2.le)
    have hF1 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 := hFc.of_le (by norm_num)
    have hG1 : ContDiffOn ℝ 1
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 := hGc.of_le (by norm_num)
    have sp0 : Work.Spaces.DzIter 0
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ := rfl
    have sp1 : Work.Spaces.DzIter 1
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 1 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ
      exact ftau_DzIter_one_add hF1 hG1 z θ hz h1 h2
    have sp2 : Work.Spaces.DzIter 2
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 2 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ
      exact ftau_DzIter_two_add hFc hGc z θ hz h1 h2
    have hF00 : |Work.Spaces.DzIter 0
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 0 (by norm_num) z θ hz h1 h2
    have hF11 : |Work.Spaces.DzIter 1
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 1 (by norm_num) z θ hz h1 h2
    have hF22 : |Work.Spaces.DzIter 2
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 2 (by norm_num) z θ hz h1 h2
    have hG00 : |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le_uniform hα hα13 hA S hτS 0 (by norm_num) z θ hz h1 h2
    have hG11 : |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le_uniform hα hα13 hA S hτS 1 (by norm_num) z θ hz h1 h2
    have hG22 : |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le_uniform hα hα13 hA S hτS 2 (by norm_num) z θ hz h1 h2
    refine ⟨?_, ?_, ?_⟩
    · calc |Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ z θ|
          = |Work.Spaces.DzIter 0
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ| := rfl
        _ = |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := by rw [sp0]
        _ ≤ |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF00 hG00
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · change |Work.Spaces.DzIter 1
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          ≤ 10 * M + |K|
      calc |Work.Spaces.DzIter 1
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := by rw [sp1]
        _ ≤ |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF11 hG11
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · calc |Work.Spaces.DzIter 2
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := by rw [sp2]
        _ ≤ |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF22 hG22
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.Fstar_Q0_c4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

/-- `F_*(z,θ) = α (Γ(θ)/c) 2z/(1+z)²` is `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)`.

The factors are separate: `Γ(θ) = (sin θ cos²θ)^{α/3}` is `C^n` on the open quadrant for
every `n` (`contDiffOn_Gam_Q0`, via `ContDiffOn.rpow_const_of_ne` — on `Q0` the base
`sin θ cos²θ` is strictly positive), the normalisation `c α` is a nonzero constant
(`c_bounds`, using `0 < α ≤ 1`), and `2z/(1+z)²` is `C^n` on `Ioi 0`
(`contDiffOn_FM_Fstar`).  `ContDiffOn` is closed under constants, products and quotients by a
nowhere-zero function, which is all the statement needs. -/
theorem Fstar_Q0_c4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Fstar α)) Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.contDiffOn_Gam_Q0 α 4
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h1 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 :=
    hGam.div contDiffOn_const (fun _ _ => hc)
  have h2 : ContDiffOn ℝ 4
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_fst_of (Work.FTS_RegExport.RXT.contDiffOn_FM_Fstar 4)
  exact (h2.mul h3).congr (fun _ _ => rfl)

end Work.FTS_RegExport.RXT.Sys.GdotAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.GdotCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.GdotCore` -- local calculus for the `g`-system (S5b, helpers)

Congruence of `D_z`, `D_θ`, `D_z^j`, `D_θ^i` and `mixed` on an open set of the `(z,θ)`-plane,
the `D_θ`-index shift, additivity of `mixed` at order `≤ 2` on the open quadrant, the splitting
of `D_z`/`D_θ` of a function agreeing with a sum `P + G`, the index arithmetic for the six
component pairs `idx`, and the elementary `Finset` estimate lemmas used by
`Work.FTS_RegExport.RXT.Sys.GdotExp.sys_bound`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory


namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7 ω phiTil)
open Work.FTS.RegExportIface.RXT (VR bR cR SigR μR GR ΦR idx)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0


/-! ## Local calculus helpers (congruence and linearity on the open quadrant) -/

theorem Dth_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  simp only [Work.Spaces.Dth]
  rw [Work.Spaces.pth_congr_of_isOpen hV h hz]

theorem Dz_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  simp only [Work.Spaces.Dz]
  rw [Work.Spaces.pz_congr_of_isOpen hV h hz]

theorem DthIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (k : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DthIter k f))
      (Function.uncurry (Work.Spaces.DthIter k f')) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro p hp
      simp only [Function.uncurry, Work.Spaces.DthIter_succ]
      rw [Dth_congr_of_isOpen hV ih hp]

theorem DzIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (k : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter k f))
      (Function.uncurry (Work.Spaces.DzIter k f')) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro p hp
      simp only [Function.uncurry, Work.Spaces.DzIter_succ]
      rw [Dz_congr_of_isOpen hV ih hp]

theorem mixed_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f f' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) (j i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.mixed j i f z θ = Work.Spaces.mixed j i f' z θ := by
  have h1 := DzIter_congr_of_isOpen hV (DthIter_congr_of_isOpen hV h i) j
  exact fun z θ hz => h1 hz

/-- `D_θ^q (D_θ X) = D_θ^{q+1} X`. -/
theorem DthIter_Dth (q : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter q (Work.Spaces.Dth X) = Work.Spaces.DthIter (q + 1) X := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [Work.Spaces.DthIter_succ q (Work.Spaces.Dth X), ih,
        Work.Spaces.DthIter_succ (q + 1) X]

/-- `mixed p q (D_θ X) = mixed p (q+1) X`. -/
theorem mixed_Dth_succ (p q : ℕ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed p q (Work.Spaces.Dth X) = Work.Spaces.mixed p (q + 1) X := by
  simp only [Work.Spaces.mixed]
  rw [DthIter_Dth]

/-- Additivity of `mixed` at a point of the open quadrant, at order `≤ 2`. -/
theorem mixed_add_pt {f₁ f₂ : ℝ → ℝ → ℝ}
    (h₁ : ContDiffOn ℝ 2 (Function.uncurry f₁) Q0)
    (h₂ : ContDiffOn ℝ 2 (Function.uncurry f₂) Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hzθ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed j i (f₁ + f₂) z θ = Work.Spaces.mixed j i f₁ z θ + Work.Spaces.mixed j i f₂ z θ :=
  Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
    Work.FTS.EllipticEst.isOpen_Q0 h₁ h₂ i j (Nat.add_comm j i ▸ hji) (z, θ) hzθ


/-- On the open quadrant, `D_θ` of a function agreeing with `P + G` splits. -/
theorem Dth_split_of_eqOn {X P G : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ 2 (Function.uncurry P) Q0)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) Q0)
    (h : EqOn (Function.uncurry X)
      (Function.uncurry (fun z θ => P z θ + G z θ)) Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Q0 →
      Work.Spaces.Dth X z θ = Work.Spaces.Dth P z θ + Work.Spaces.Dth G z θ := by
  intro z θ hp
  have hdiffP : DifferentiableAt ℝ (fun θ' => P z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hP.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by norm_num))
  have hdiffG : DifferentiableAt ℝ (fun θ' => G z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hG.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by norm_num))
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Q0 :=
    (Continuous.prodMk_right z).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  have hslice : (fun θ' => X z θ') =ᶠ[𝓝 θ] (fun θ' => P z θ' + G z θ') := by
    filter_upwards [hnb] with θ' hθ'
    simpa only [Function.uncurry] using h hθ'
  have h1 : Work.Spaces.pth X z θ = Work.Spaces.pth P z θ + Work.Spaces.pth G z θ := by
    simp only [Work.Spaces.pth]
    rw [hslice.deriv_eq,
      show (fun θ' => P z θ' + G z θ') = (fun θ' => P z θ') + (fun θ' => G z θ') from rfl,
      deriv_add hdiffP hdiffG]
  simp only [Work.Spaces.Dth]
  rw [h1]
  ring

/-! ## Index arithmetic and elementary sum bounds -/

/-- Every pair `(p,q)` of total order `≤ 2` is one of the six `idx`-pairs. -/
theorem idx_exists {p q : ℕ} (h : p + q ≤ 2) :
    ∃ t : Fin 6, (idx t).1 = p ∧ (idx t).2 = q := by
  have hp2 : p ≤ 2 := by omega
  have hq2 : q ≤ 2 := by omega
  interval_cases q
  · interval_cases p
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨3, by decide, by decide⟩
  · interval_cases p
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨4, by decide, by decide⟩
    · omega
  · interval_cases p
    · exact ⟨5, by decide, by decide⟩
    · omega
    · omega

/-- Domination of the order-`≤ 2` jets by the `idx`-sum. -/
theorem mixed_le_sum_idx {G : ℝ → ℝ → ℝ} {z θ : ℝ} {p q : ℕ} (h : p + q ≤ 2) :
    |Work.Spaces.mixed p q G z θ| ≤ ∑ t : Fin 6, |Work.Spaces.mixed (idx t).1 (idx t).2 G z θ| := by
  obtain ⟨t, ht1, ht2⟩ := idx_exists h
  rw [← ht1, ← ht2]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun t : Fin 6 => |Work.Spaces.mixed (idx t).1 (idx t).2 G z θ|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ t)

/-- A binomial coefficient of order `≤ 2` is `≤ 2`. -/
theorem choose_le_two {i a : ℕ} (ha : a ≤ i) (hi : i ≤ 2) : i.choose a ≤ 2 := by
  interval_cases i <;> interval_cases a <;> decide

/-- Peel the `(0,0)`-term off a double `range`-sum. -/
theorem sum_peel (s t : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ u ∈ Finset.range (s + 1), ∑ v ∈ Finset.range (t + 1), F u v) - F 0 0
      = (∑ u ∈ Finset.range s, ∑ v ∈ Finset.range (t + 1), F (u + 1) v)
        + (∑ v ∈ Finset.range t, F 0 (v + 1)) := by
  rw [Finset.sum_range_succ' (fun u => ∑ v ∈ Finset.range (t + 1), F u v) s]
  rw [Finset.sum_range_succ' (fun v => F 0 v) t]
  ring

/-- A double `range`-sum with uniformly bounded terms. -/
theorem abs_double_sum_le (s t : ℕ) (F : ℕ → ℕ → ℝ) (K : ℝ)
    (hF : ∀ u ∈ Finset.range s, ∀ v ∈ Finset.range t, |F u v| ≤ K) :
    |∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, F u v| ≤ ((s * t : ℕ) : ℝ) * K := by
  calc |∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, F u v|
      ≤ ∑ u ∈ Finset.range s, |∑ v ∈ Finset.range t, F u v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, |F u v| :=
        Finset.sum_le_sum (fun u _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ u ∈ Finset.range s, ∑ v ∈ Finset.range t, K :=
        Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => hF u hu v hv))
    _ = ((s * t : ℕ) : ℝ) * K := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- A single `range`-sum with uniformly bounded terms. -/
theorem abs_range_sum_le (t : ℕ) (F : ℕ → ℝ) (K : ℝ)
    (hF : ∀ v ∈ Finset.range t, |F v| ≤ K) :
    |∑ v ∈ Finset.range t, F v| ≤ ((t : ℕ) : ℝ) * K := by
  calc |∑ v ∈ Finset.range t, F v| ≤ ∑ v ∈ Finset.range t, |F v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ Finset.range t, K := Finset.sum_le_sum hF
    _ = ((t : ℕ) : ℝ) * K := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.SigR_eq_reduced =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-! ## The three factorisations of the reference profile `F_*`

With `β = pExp α = 3α`, `Γ(θ) = Gam β θ = (sin θ cos²θ)^α`, `c = c β` and
`F̂ = FM.Fstar = 2z/(1+z)²`, the reference profile is

  `F_* = β·(Γ/c)·F̂ = (β/c)·Γ·F̂`

and its two first-order derivatives factor as

* `D_z F_* = (β/c)·Γ·(z F̂')`,  `z F̂'(z) = 2z(1-z)/(1+z)³`;
* `sin(2θ)·∂_θF_* = (β/c)·Γ·((2β/3)·c2m θ·F̂)`,  `c2m θ = cos 2θ - sin²θ`.

The second is the statement `∂_θΓ = Γ·2α·c2m θ/sin 2θ` (`Work.FTS_RegExport.RXT.hasDerivAt_Gamma`,
which is stated for `Work.FTS.Regularity.Gamma α = Gam (pExp α)`) times the factor `2β/3 = 2α`.
Multiplying by `sin 2θ` clears the angular singularity at the two endpoints of the identity; the
identity itself is used only on the open interval `(0, π/2)` where `sin 2θ ≠ 0`. -/

/-- `F_*(pExp α) = (β/c)·Γ·F̂` with `β = pExp α`. -/
private lemma Fs_coeff (α z θ : ℝ) :
    Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ * Work.FM.Fstar z := by
  simp only [Work.Construction.Fstar]
  ring

/-- `D_z F_* = (β/c)·Γ·(2z(1-z)/(1+z)³)`. -/
private lemma Dz_Fs_coeff {α z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (2 * z * (1 - z) / (1 + z) ^ 3) := by
  have hslice : (fun z' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ)
      = fun z' => (Work.FTS.Regularity.pExp α
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))) * Work.FM.Fstar z' := by
    funext z'; simp only [Work.Construction.Fstar]
  have hd : DifferentiableAt ℝ Work.FM.Fstar z :=
    (Work.FM.hasDerivAt_Fstar z (by linarith)).differentiableAt
  rw [Work.Spaces.Dz, Work.Spaces.pz, hslice, deriv_const_mul _ hd,
    Work.FM.deriv_Fstar z (by linarith)]
  ring

/-- `sin(2θ)·∂_θF_* = (β/c)·Γ·((2β/3)·c2m θ·F̂)`. -/
private lemma sin_pth_Fs_coeff {α z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Real.sin (2 * θ) * Work.Spaces.pth
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2)) := by
  have hGam : HasDerivAt (fun θ' : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ')
      (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) θ := by
    have h := Work.FTS_RegExport.RXT.hasDerivAt_Gamma α θ hθ0 hθ1
    have hfun : (fun θ' : ℝ => Work.FTS.Regularity.Gamma α θ')
        = fun θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' := by
      funext θ'; exact Work.FTS.Regularity.Gamma_eq_Gam α θ'
    rwa [hfun, Work.FTS.Regularity.Gamma_eq_Gam α θ] at h
  have hslice : (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ')
      = fun θ' => (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' := by
    funext θ'; simp only [Work.Construction.Fstar]; ring
  have hpth : Work.Spaces.pth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) := by
    rw [Work.Spaces.pth, hslice, deriv_const_mul _ hGam.differentiableAt, hGam.deriv]
  rw [hpth]
  have hs : Real.sin (2 * θ) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos])
  have h2 : 2 * Work.FTS.Regularity.pExp α / 3 = 2 * α := by
    simp only [Work.FTS.Regularity.pExp]; ring
  rw [h2]
  calc Real.sin (2 * θ) * ((Work.FTS.Regularity.pExp α * Work.FM.Fstar z
          / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))))
      = (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
          / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Real.sin (2 * θ) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))) := by ring
    _ = (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
          / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (2 * α * Work.Construction.c2m θ)) := by
        rw [show Real.sin (2 * θ) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))
            = Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Real.sin (2 * θ) * (2 * α * Work.Construction.c2m θ
                / Real.sin (2 * θ))) by ring,
          mul_div_cancel₀ _ hs]
    _ = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (2 * α * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)) := by
        simp only [Work.FM.Fstar]; ring

/-- **The reduced form of the forcing.**  With `β = pExp α`, `Γ = Gam (pExp α)`, `c = Spaces.c β`,
`F_* = Fstar β = β(Γ/c)·(2z/(1+z)²)`, the forcing
`Σ = VR·D_zF_* + Vθ7·∂_θF_* + cR·F_*` equals `(β/c)·Γ` times the explicit combination
`VR·(z·F̂') + bR·((2β/3)c2m·F̂) + cR·F̂` of the three coefficients, where `zF̂' = 2z(1-z)/(1+z)³`
and `F̂ = 2z/(1+z)²`: this uses `D_zF_* = (β/c)·Γ·zF̂'` and
`∂_θF_* = (β/c)·Γ·(2β/3)c2m·F̂/sin 2θ` together with `Vθ7 = sin 2θ·bR`. -/
theorem SigR_eq_reduced {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} :
    ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.RegExportIface.RXT.SigR α Φs E g σ z θ
        = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * (2 * z * (1 - z) / (1 + z) ^ 3)
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
                * (2 * z / (1 + z) ^ 2))
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * (2 * z / (1 + z) ^ 2)) := by
  intro σ hσ z θ hz hθ0 hθ1
  -- the angular weight is nonzero on the open interval, so `bR = Vθ7/sin 2θ` inverts
  have hs : Real.sin (2 * θ) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos])
  have hU : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
      = Real.sin (2 * θ) * Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ := by
    show Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
      = Real.sin (2 * θ) * (Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ / Real.sin (2 * θ))
    rw [mul_div_cancel₀ _ hs]
  -- the `∂_θF_*`-slot in terms of `bR`
  have hmid : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
      * Work.Spaces.pth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        * ((Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2))) := by
    rw [hU]
    calc (Real.sin (2 * θ) * Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ)
          * Work.Spaces.pth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
          * (Real.sin (2 * θ) * Work.Spaces.pth
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := by ring
      _ = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
          * ((Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
              * (2 * z / (1 + z) ^ 2))) := by
          rw [sin_pth_Fs_coeff hθ0 hθ1]
  rw [Work.FTS.RegExportIface.RXT.SigR, Dz_Fs_coeff hz, Fs_coeff, hmid]
  simp only [Work.FM.Fstar]
  ring

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.bR_decomp`

The `Θ`-decomposition `bR = 2·Uop β Φ̃/sin 2θ + 2·Uop β (Θ β F)/sin 2θ` of the `θ`-coefficient
`bR = Vθ7/sin 2θ = 2·Uop β (slice Φ σ)/sin 2θ`, where `Φ = ΦR α Φs E g` is the *full* stream
function — an arbitrary function of `(z,θ)` as far as the hypotheses go, so that the additivity
`Uop β Φ = Uop β Φ̃ + Uop β (Θ β F)` (equivalently `deriv_sub` on the `z`-slices) is **not**
available as a hypothesis.  It is recovered from `hC2` (the `C²`-ness of the three coefficients)
by the following density argument, whose structural input is
`SysAux/dense_diffAt.exists_differentiableAt_of_slice_identity`:

* the *correction* `Corr := bR - 2·Uop β Φ̃/sin 2θ - 2·Uop β (Θ β F)/sin 2θ` vanishes at every
  `z` at which the `z`-slice of `Φ` is differentiable (`deriv_sub`, twice);
* the set of such `z` has empty complement-interior (because on an interval where the slice is
  nowhere differentiable the definition `sin 2θ·bR = -6Φ - 2β z ∂_zΦ` forces `Φ` to agree with
  the `C²` function `-sin 2θ·bR/6`), so it is dense in `(0,∞)`;
* `Corr` is continuous on `(0,∞)`: the only non-obvious continuity is that of
  `Uop β Φ̃`, which follows from `Uop Ψ = cot θ·(Vop Ψ - Rop β Ψ)` together with the *closed
  forms* `Vz7 = (1-μ) + L₁₂(F)c2m + 2β Vop Φ̃` and `cs7 = (1+μ) - L₁₂(F)/β + sin²θ·𝔽K(F) - 2 Rop β Φ̃`
  of the two `C²` coefficients `VR`, `cR` given by `hC2`.  (This is where the two *extra*
  conjuncts of `hC2` — not just the `bR` one — are used: they are the *only* source of the
  continuity of the perturbed slots `Vop Φ̃`, `Rop β Φ̃`.)  The continuity of the `Θ`-part is
  obtained from `L₁₂(F) ∈ C³(0,∞)`, which is a consequence of `DynOK'` alone
  (`contDiffOn_Ftau_Q0` + `Ftau_bounds` + `contDiffOn_two_integral_Itheta` +
  `C2Radial.contDiffOn_three_L12`).
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two auxiliary lemmas -/

/-- A continuous function on `(0,∞)` whose zero set meets every open subinterval of `(0,∞)`
vanishes identically. -/
private lemma dense_eq_zero_of_continuousOn {f : ℝ → ℝ}
    (hd : ∀ a c : ℝ, 0 < a → a < c → ∃ w ∈ Set.Ioo a c, f w = 0)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z → f z = 0 := by
  intro z hz
  classical
  have hδ0 : ∀ n : ℕ, 0 < min (z / 2) (1 / ((n : ℝ) + 1)) :=
    fun n => lt_min (by linarith) (by positivity)
  have hδle : ∀ n : ℕ, min (z / 2) (1 / ((n : ℝ) + 1)) ≤ z / 2 := fun n => min_le_left _ _
  have hex : ∀ n : ℕ, ∃ w : ℝ,
      w ∈ Set.Ioo (z - min (z / 2) (1 / ((n : ℝ) + 1))) (z + min (z / 2) (1 / ((n : ℝ) + 1)))
        ∧ f w = 0 := by
    intro n
    exact hd _ _ (by have := hδle n; linarith) (by have := hδ0 n; linarith)
  let w : ℕ → ℝ := fun n => Classical.choose (hex n)
  have hw : ∀ n : ℕ, w n ∈ Set.Ioo (z - min (z / 2) (1 / ((n : ℝ) + 1)))
      (z + min (z / 2) (1 / ((n : ℝ) + 1))) ∧ f (w n) = 0 := fun n =>
    Classical.choose_spec (hex n)
  have hδlim : Tendsto (fun n : ℕ => min (z / 2) (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => le_min (by linarith) (by positivity))
      (fun n => min_le_right _ _) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have habs : ∀ n : ℕ, ‖w n - z‖ ≤ min (z / 2) (1 / ((n : ℝ) + 1)) := by
    intro n
    have h1 := (hw n).1
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hlim0 : Tendsto (fun n : ℕ => w n - z) atTop (𝓝 0) :=
    squeeze_zero_norm' (Filter.Eventually.of_forall habs) hδlim
  have hlimw : Tendsto w atTop (𝓝 z) := by
    have h := hlim0.add (tendsto_const_nhds (x := z) : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
    simpa using h
  have hcont : ContinuousAt f z := hf.continuousAt (isOpen_Ioi.mem_nhds hz)
  have htend : Tendsto (fun n : ℕ => f (w n)) atTop (𝓝 (f z)) := hcont.tendsto.comp hlimw
  have hconst : (fun n : ℕ => f (w n)) = fun _ : ℕ => (0 : ℝ) := funext fun n => (hw n).2
  rw [hconst] at htend
  exact (tendsto_nhds_unique
    (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    htend).symm

/-- **The correction vanishes at the differentiability points of the slice**:  at every `z` at
which the `z`-slice of the full stream function `Φ` is differentiable (and where `L₁₂(F)` is
differentiable), all of `Φ̃ = Φ - Θ(F)`, `Θ(F)` are differentiable there too and `deriv_sub` gives
the additivity `Uop β Φ = Uop β Φ̃ + Uop β (Θ β F)` of the split of `bR`. -/
private lemma corr_zero_of_diffAt {α : ℝ} (hα : 0 < α)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {σ θ z : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hzd : DifferentiableAt ℝ
      (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ) z)
    (hLd : DifferentiableAt ℝ (fun z' => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z) :
    Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
          / Real.sin (2 * θ))
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ))
      = 0 := by
  have hs2 : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθπ, Real.pi_pos]))
  have hβne : Work.FTS.Regularity.pExp α ≠ 0 :=
    ne_of_gt (Work.FTS.Regularity.pExp_pos hα)
  have hBd : DifferentiableAt ℝ (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ) z := by
    have h2 : (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ)
        = fun z' => ((1 / (4 * Work.FTS.Regularity.pExp α)) * Real.sin (2 * θ))
            * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z' := by
      funext z'
      simp only [Work.Construction.Theta, Work.Construction.s2]
    rw [h2]
    exact hLd.const_mul _
  have hderiv : deriv (fun z' => Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ z' θ) z
      = deriv (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ) z
        - deriv (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ) z := by
    have hfun : (fun z' => Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ z' θ)
        = (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ)
          - (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ) := by
      funext z'
      simp only [Work.FTS.RegExportIface.phiTil, Work.Construction.PhiTil,
        Work.FTS.Galerkin.slice, Pi.sub_apply]
    rw [hfun, deriv_sub hzd hBd]
  simp only [Work.FTS.RegExportIface.RXT.bR, Work.FTS.RegExportIface.Vθ7,
    Work.Construction.Uop, Work.Spaces.pz, Work.FTS.Galerkin.slice]
  rw [hderiv]
  simp only [Work.FTS.RegExportIface.phiTil, Work.Construction.PhiTil, Work.FTS.Galerkin.slice,
    Work.Construction.Theta, Work.Construction.s2]
  field_simp
  ring

/-! ## The regularity of `L₁₂(F(σ))` and `𝔽K(F(σ))`, from `DynOK'` -/

/-- `L₁₂(F)` is `C³` on `(0,∞)` and `𝔽K(F)` is `C²` on `(0,∞)`, for the full profile
`F = Ftau β (GR α g) σ`, as a consequence of `DynOK'` alone: it suffices that `F` be `C²` on the
open quadrant and bounded, `Ftau_bounds`. -/
theorem L12FK_of_DynOK {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ContinuousOn (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      ContinuousOn (fun z => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) ∧
      ContinuousOn (deriv (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z)) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) := by
  have hF2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) σ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK σ hσ
  obtain ⟨Cb, -, hbnd⟩ :=
    Work.FTS_RegExport.RXT.Ftau_bounds (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hα hα13 hOK σ hσ
  have hKcont : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
    ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
  have hFK2 : ContDiffOn ℝ 2 (fun z => Work.Construction.FK
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K) hKcont hF2 hbnd
  have hL3 : ContDiffOn ℝ 3 (fun z => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2
  have hder : ContinuousOn (deriv (fun z => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z)) (Set.Ioi 0) := by
    have h3 : ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0) := by
      rw [show (2 : WithTop ℕ∞) + 1 = 3 from by norm_num]
      exact hL3
    exact (((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (2 : WithTop ℕ∞))
      isOpen_Ioi).mp h3).2.2).continuousOn
  exact ⟨hL3.continuousOn, hFK2.continuousOn, hder, hL3.differentiableOn (by norm_num)⟩

/-! ## The continuity of the two pieces of the correction -/

/-- The continuity of the perturbed slot `Uop β Φ̃` (from the closed forms of `Vz7`, `cs7` and
`Uop Ψ = cot θ·(Vop Ψ - Rop β Ψ)`) and of the singular slot `2·Uop β (Θ β F)/sin 2θ` (from the
`C³`-regularity of `L₁₂(F)`), at fixed `θ ∈ (0, π/2)`. -/
theorem bR_slotcont_of_DynOK {α C₀ : ℝ} (hα : 0 < α)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hL12con : ContinuousOn (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0))
    (hFKcon : ContinuousOn (fun z => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0))
    (hL12diff : DifferentiableOn ℝ (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z) (Set.Ioi 0))
    (hderivL12con : ContinuousOn (deriv (fun z => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z)) (Set.Ioi 0))
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    ContinuousOn (fun z => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
        z θ) (Set.Ioi 0) ∧
      ContinuousOn (fun z => 2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) (Set.Ioi 0) := by
  have hβne : Work.FTS.Regularity.pExp α ≠ 0 :=
    ne_of_gt (Work.FTS.Regularity.pExp_pos hα)
  have hsinθ : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos]))
  have hcosθ : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    exact ne_of_gt h
  have hs2 : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hVopC : ContinuousOn (fun z => Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ) (Set.Ioi 0) := by
    have hVRc : ContinuousOn (fun z => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ) (Set.Ioi 0) :=
      (((hC2 σ hσ).1).comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
        (fun w hw => ⟨hw, hθ, hθπ⟩)).continuousOn
    have hid : (fun z => Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
        = fun z => (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
            - (1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
            - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) σ) z * Work.Construction.c2m θ)
          / (2 * Work.FTS.Regularity.pExp α) := by
      funext z
      simp only [Work.FTS.RegExportIface.Vz7]
      field_simp
      ring
    rw [hid]
    exact ((hVRc.sub continuousOn_const).sub (hL12con.mul_const _)).div_const _
  have hRopC : ContinuousOn (fun z => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
      z θ) (Set.Ioi 0) := by
    have hcRc : ContinuousOn (fun z => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ) (Set.Ioi 0) :=
      (((hC2 σ hσ).2.2).comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
        (fun w hw => ⟨hw, hθ, hθπ⟩)).continuousOn
    have hid : (fun z => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
        z θ)
        = fun z => ((1 + Work.FTS.RegExportIface.RXT.μR α Φs E g σ)
            - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) σ) z / Work.FTS.Regularity.pExp α
            + (Real.sin θ) ^ 2 * Work.Construction.FK
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) σ) z
            - Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ) / 2 := by
      funext z
      simp only [Work.FTS.RegExportIface.cs7]
      field_simp
      ring
    rw [hid]
    exact (((continuousOn_const.add continuousOn_const).sub
      (hL12con.div_const _)).add (continuousOn_const.mul hFKcon)).sub hcRc |>.div_const _
  have hUopC : ContinuousOn (fun z => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
      z θ) (Set.Ioi 0) := by
    have halg : ∀ z, Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
        = (Real.cos θ / Real.sin θ) * (Work.Construction.Vop (Work.FTS.RegExportIface.phiTil
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
            (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ
          - Work.Construction.Rop (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.phiTil
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g)
            (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ) := by
      intro z
      simp only [Work.Construction.Uop, Work.Construction.Vop, Work.Construction.Rop,
        Work.Spaces.pth, Work.Spaces.pz, Real.tan_eq_sin_div_cos]
      field_simp
      ring
    exact ContinuousOn.congr ((hVopC.sub hRopC).mul_const (Real.cos θ / Real.sin θ)) (fun z _ => by
      rw [halg z]
      simp only [Pi.sub_apply]
      ring_nf)
  refine ⟨hUopC, ?_⟩
  have hcontRHS : ContinuousOn (fun z => -(3 / (2 * Work.FTS.Regularity.pExp α))
      * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z
      - (1 / 2) * (z * deriv (fun z' => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z)) (Set.Ioi 0) :=
    (continuousOn_const.mul hL12con).sub
      (continuousOn_const.mul (continuousOn_id.mul hderivL12con))
  refine ContinuousOn.congr hcontRHS (fun z hz => ?_)
  have hd : DifferentiableAt ℝ (fun z' => Work.Construction.L12
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z') z :=
    (hL12diff z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have h1 : (fun z' => Work.Construction.Theta (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z' θ)
      = fun z' => ((1 / (4 * Work.FTS.Regularity.pExp α)) * Real.sin (2 * θ))
          * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z' := by
    funext z'
    simp only [Work.Construction.Theta, Work.Construction.s2]
  simp only [Work.Construction.Uop, Work.Spaces.pz]
  rw [h1, deriv_const_mul _ hd]
  simp only [Work.Construction.Theta, Work.Construction.s2]
  field_simp
  ring_nf

/-! ## The core: the decomposition from the continuity of the correction -/

/-- **The `Θ`-decomposition of `bR` from the continuity of the correction.**  The hypotheses
beyond `hC2` are exactly what the density argument consumes: `hL12diff` makes `Θ β F`
differentiable, and `hUopC`/`hUC` are the two continuity statements for the pieces of the
correction other than `bR` (provided by `bR_slotcont_of_DynOK`). -/
theorem bR_decomp_of_infra {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) S)
    (hL12diff : ∀ w : ℝ, 0 < w → DifferentiableAt ℝ (fun z' => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) σ) z') w)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hUopC : ContinuousOn (fun z => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ) z θ)
        (Set.Ioi 0))
    (hUC : ContinuousOn (fun z => 2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        = 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
              z θ / Real.sin (2 * θ))
          + 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) := by
  intro z hz
  let Φt : ℝ → ℝ → ℝ := Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ
  let Θt : ℝ → ℝ → ℝ := Work.Construction.Theta (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ)
  let Corr : ℝ → ℝ := fun w => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) Φt w θ / Real.sin (2 * θ))
      - 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) Θt w θ / Real.sin (2 * θ))
  have hbRc2 : ContDiffOn ℝ 2
      (fun w : ℝ => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ) (Set.Ioi 0) :=
    ((hC2 σ hσ.1).2.1).comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
      (fun w hw => ⟨hw, hθ, hθπ⟩)
  have hbRcont : ContinuousOn (fun w : ℝ => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ)
      (Set.Ioi 0) := hbRc2.continuousOn
  have hbd : DifferentiableOn ℝ (fun w : ℝ => Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ)
      (Set.Ioi 0) := hbRc2.differentiableOn (by norm_num)
  have hU1 : ContinuousOn (fun w : ℝ => 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      Φt w θ / Real.sin (2 * θ))) (Set.Ioi 0) := by
    refine ContinuousOn.congr (hUopC.const_mul (2 / Real.sin (2 * θ))) ?_
    intro w _
    ring
  have hU2 : ContinuousOn (fun w : ℝ => 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      Θt w θ / Real.sin (2 * θ))) (Set.Ioi 0) := by
    refine ContinuousOn.congr hUC ?_
    intro w _
    ring
  have hCorrC : ContinuousOn Corr (Set.Ioi 0) := (hbRcont.sub hU1).sub hU2
  have hb : ∀ w : ℝ, 0 < w → Work.FTS.RegExportIface.RXT.bR α Φs E g w θ σ
      = 2 * (-3 * Work.FTS.RegExportIface.RXT.ΦR α Φs E g w θ σ
          - Work.FTS.Regularity.pExp α * w
            * deriv (fun z' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z' θ σ) w)
        / Real.sin (2 * θ) := by
    intro w hw
    simp only [Work.FTS.RegExportIface.RXT.bR, Work.FTS.RegExportIface.Vθ7,
      Work.Construction.Uop, Work.Spaces.pz, Work.FTS.Galerkin.slice]
  have hdens : ∀ a c : ℝ, 0 < a → a < c → ∃ w ∈ Set.Ioo a c, Corr w = 0 := by
    intro a c ha hac
    obtain ⟨w, hw, hdw⟩ := exists_differentiableAt_of_slice_identity
      (β := Work.FTS.Regularity.pExp α) (θ := θ)
      (b := fun z θ' => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ' σ)
      (Φ := fun z θ' => Work.FTS.RegExportIface.RXT.ΦR α Φs E g z θ' σ)
      (Work.FTS.Regularity.pExp_pos hα) hθ hθπ hb hbd ha hac
    exact ⟨w, hw, corr_zero_of_diffAt hα hθ hθπ hdw (hL12diff w (lt_trans ha hw.1))⟩
  have hCorr0 : ∀ w : ℝ, 0 < w → Corr w = 0 :=
    dense_eq_zero_of_continuousOn hdens hCorrC
  have hfin : Corr z = 0 := hCorr0 z hz
  simp only [Corr] at hfin
  linarith

/-- **The `Θ`-decomposition of the `θ`-coefficient.**  The coefficient
`bR = Vθ7/sin 2θ = 2·Uop β (slice Φ σ)/sin 2θ` (with `Φ = ΦR α Φs E g` the *full* stream function,
an arbitrary function of `(z,θ)`) splits as the perturbation part `2·Uop β Φ̃/sin 2θ`
(`Φ̃ = phiTil β (GR α g) (ΦR α Φs E g) σ`) plus the closed-form singular part
`2·Uop β (Θ β F)/sin 2θ` (`F = Ftau β (GR α g) σ`) — i.e. the "additivity of `Uop`" that is *not*
available as a hypothesis, recovered from `hC2` (`bR` is `C²`) by the density argument of
`SysAux/dense_diffAt`. -/
theorem bR_decomp {α C₀ S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0)
    (hw : ∃ C : ℝ, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 → |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
        ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :
    ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        = 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
              z θ / Real.sin (2 * θ))
          + 2 * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) σ)) z θ / Real.sin (2 * θ)) := by
  intro σ hσ z θ hz hθ hθπ
  obtain ⟨hL12con, hFKcon, hderivL12con, hL12diff⟩ := L12FK_of_DynOK hα hα13 hOK hσ.1
  obtain ⟨hUopC, hUC⟩ := bR_slotcont_of_DynOK (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hα hC2 hσ.1
    hL12con hFKcon hL12diff hderivL12con hθ hθπ
  exact bR_decomp_of_infra (C₀ := C₀) (S := S) hα hα13 hS hC2 hσ
    (fun w hw' => (hL12diff w hw').differentiableAt (isOpen_Ioi.mem_nhds hw')) hθ hθπ hUopC hUC z hz

end Work.FTS_RegExport.RXT.SysAux
end
