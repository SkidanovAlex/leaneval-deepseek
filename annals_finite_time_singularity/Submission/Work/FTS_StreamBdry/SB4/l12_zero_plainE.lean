import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.R0vals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 The elementary vanishings of the angular data -/

theorem R0_Gam_at_zero {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  simp [Work.Spaces.Gam, Real.zero_rpow, hα.ne']

theorem R0_Gam_at_pi_div_two {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α (Real.pi / 2) = 0 := by
  simp [Work.Spaces.Gam, Real.zero_rpow, hα.ne']

theorem R0_sin_two_pi_div_two : Real.sin (2 * (Real.pi / 2)) = 0 := by
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

theorem R0_Fstar_at_zero : Work.FM.Fstar 0 = 0 := by
  norm_num [Work.FM.Fstar]

/-! ## §2 The linear part `𝓛_Γ^T` vanishes on the three strata -/

/-- On the stratum `θ = 0`, `𝓛_Γ^T f = 0` whenever the slice `f(·,0)` vanishes:
`Γ(0) = 0` and `sin 0 = 0` kill the `L₁₂`/transport terms, and `𝓛` reduces to
`f z 0 + z ∂_z(f(·,0)) z - 2 f z 0/(1+z) = 0`. -/
theorem R0_LGammaT_at_theta0 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : ∀ z, f z 0 = 0) (z : ℝ) :
    Work.Coercivity.LGammaT α f z 0 = 0 := by
  have hGam : Work.Spaces.Gam α 0 = 0 := R0_Gam_at_zero hα
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.Spaces.Dz, Work.Spaces.Dth, Work.Spaces.pz, Work.Spaces.pth]
  simp [hf, hGam, Real.sin_zero]

/-- On the stratum `θ = π/2`, `𝓛_Γ^T f = 0` whenever the slice `f(·,π/2)` vanishes. -/
theorem R0_LGammaT_at_thetaPi2 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : ∀ z, f z (Real.pi / 2) = 0) (z : ℝ) :
    Work.Coercivity.LGammaT α f z (Real.pi / 2) = 0 := by
  have hGam : Work.Spaces.Gam α (Real.pi / 2) = 0 := R0_Gam_at_pi_div_two hα
  have hs2 : Real.sin (2 * (Real.pi / 2)) = 0 := R0_sin_two_pi_div_two
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.Spaces.Dz, Work.Spaces.Dth, Work.Spaces.pz, Work.Spaces.pth]
  simp [hf, hGam, hs2]

/-- On the stratum `z = 0`, `𝓛_Γ^T f = 0` whenever the slice `f(0,·)` vanishes: every
`z`-factor (`D_z`, the `L₁₂`-correction of `𝓛_Γ`, and the projector `𝕡`) is zero. -/
theorem R0_LGammaT_at_z0 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ θ, f 0 θ = 0) (θ : ℝ) :
    Work.Coercivity.LGammaT α f 0 θ = 0 := by
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.Spaces.Dz, Work.Spaces.Dth, Work.Spaces.pz, Work.Spaces.pth]
  simp [hf]

/-! ## §3 The nonlinear part `gRHS` vanishes on the three strata -/

/-- On the stratum `θ = 0`, `gRHS α μ λ F Φ f = 0` as soon as the slices `F(·,0)`, `f(·,0)`
and `Φ(·,0)` vanish: `s2 0 = Γ(0) = 0` kill the `s2`-terms and the two `F_*`-derivatives
(the latter through `F_* (·,0) ≡ 0`), `f(·,0) ≡ 0` kills `N_*` and the `f`-terms, `F(·,0) ≡ 0`
kills the `F`-factors of `N`, and `Φ̃(·,0) ≡ 0` (from `Φ(·,0) ≡ 0` and `sin(2·0) = 0`) kills
the `Uop`-factor of `N`. -/
theorem R0_gRHS_at_theta0 {α mu lam : ℝ} (hα : 0 < α) {F f Φ : ℝ → ℝ → ℝ}
    (hF : ∀ z, F z 0 = 0) (hf : ∀ z, f z 0 = 0) (hΦ : ∀ z, Φ z 0 = 0) (z : ℝ) :
    Work.Construction.gRHS α mu lam F Φ f z 0 = 0 := by
  have hGam : Work.Spaces.Gam α 0 = 0 := R0_Gam_at_zero hα
  simp only [Work.Construction.gRHS, Work.Construction.N0, Work.Construction.N,
    Work.Construction.Nstar, Work.Construction.AK, Work.Construction.Uop, Work.Construction.Vop,
    Work.Construction.Rop, Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.FK,
    Work.Construction.s2, Work.Construction.c2m, Work.Construction.Fstar,
    Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pth]
  simp [hF, hf, hΦ, hGam, Real.sin_zero]

/-- On the stratum `θ = π/2`: the same as `R0_gRHS_at_theta0`, with `Γ(π/2) = 0`,
`sin(2·(π/2)) = 0` and `cos(π/2) = 0` (which kills `Rop`) in place of their `θ = 0`
counterparts. -/
theorem R0_gRHS_at_thetaPi2 {α mu lam : ℝ} (hα : 0 < α) {F f Φ : ℝ → ℝ → ℝ}
    (hF : ∀ z, F z (Real.pi / 2) = 0) (hf : ∀ z, f z (Real.pi / 2) = 0)
    (hΦ : ∀ z, Φ z (Real.pi / 2) = 0) (z : ℝ) :
    Work.Construction.gRHS α mu lam F Φ f z (Real.pi / 2) = 0 := by
  have hGam : Work.Spaces.Gam α (Real.pi / 2) = 0 := R0_Gam_at_pi_div_two hα
  have hs2 : Real.sin (2 * (Real.pi / 2)) = 0 := R0_sin_two_pi_div_two
  simp only [Work.Construction.gRHS, Work.Construction.N0, Work.Construction.N,
    Work.Construction.Nstar, Work.Construction.AK, Work.Construction.Uop, Work.Construction.Vop,
    Work.Construction.Rop, Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.FK,
    Work.Construction.s2, Work.Construction.c2m, Work.Construction.Fstar,
    Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pth]
  simp [hF, hf, hΦ, hGam, hs2]

/-- On the stratum `z = 0`, `gRHS α μ λ F Φ f = 0` as soon as the slices `F(0,·)` and `f(0,·)`
vanish and `F_*(0,·) ≡ 0` (which holds since `F_* = α(Γ/c)·(2z/(1+z)²)` and `F_*(0) = 0`):
every term carries a factor `z` (through `D_z`), or one of the vanishing slices. -/
theorem R0_gRHS_at_z0 {α mu lam : ℝ} {F f Φ : ℝ → ℝ → ℝ}
    (hF : ∀ θ, F 0 θ = 0) (hf : ∀ θ, f 0 θ = 0)
    (hFst : ∀ θ, Work.Construction.Fstar α 0 θ = 0) (θ : ℝ) :
    Work.Construction.gRHS α mu lam F Φ f 0 θ = 0 := by
  simp only [Work.Construction.gRHS, Work.Construction.N0, Work.Construction.N,
    Work.Construction.Nstar, Work.Construction.AK, Work.Construction.Uop, Work.Construction.Vop,
    Work.Construction.Rop, Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.FK,
    Work.Construction.s2, Work.Construction.c2m,
    Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pth]
  simp [hF, hf, hFst]

/-! ## §4 The assembly -/

theorem R0vals {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    (∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ 0 θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
            (Work.FTS_RegExport.RXR5.SG α g) τ 0 θ = 0) ∧
    (∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ z 0
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
            (Work.FTS_RegExport.RXR5.SG α g) τ z 0 = 0) ∧
    (∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ,
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ z
          (Real.pi / 2)
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
            (Work.FTS_RegExport.RXR5.SG α g) τ z (Real.pi / 2) = 0) := by
  have hα0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hGam0 : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) 0 = 0 := R0_Gam_at_zero hα0
  have hGamπ : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) (Real.pi / 2) = 0 :=
    R0_Gam_at_pi_div_two hα0
  have hs2π : Real.sin (2 * (Real.pi / 2)) = 0 := R0_sin_two_pi_div_two
  have hFs0 : Work.FM.Fstar 0 = 0 := R0_Fstar_at_zero
  have hFst : ∀ θ, Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ = 0 := by
    intro θ
    simp only [Work.Construction.Fstar, hFs0, mul_zero]
  have hFstθ0 : ∀ z, Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z 0 = 0 := by
    intro z
    simp only [Work.Construction.Fstar, hGam0, zero_div, mul_zero, zero_mul]
  have hFstθπ : ∀ z, Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z (Real.pi / 2) = 0 := by
    intro z
    simp only [Work.Construction.Fstar, hGamπ, zero_div, mul_zero, zero_mul]
  -- the vanishing of the sanitiser on the two angular boundaries
  have hSGθ0 : ∀ (τ : ℝ), 0 ≤ τ → ∀ z, Work.FTS_RegExport.RXR5.SG α g z 0 τ = 0 := by
    intro τ hτ z
    by_cases hz : z ≤ 0
    · exact Work.FTS_RegExport.RXR5.SG_apply_of_nonpos hz
    · have hz' : 0 < z := lt_of_not_ge hz
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' le_rfl (by linarith [Real.pi_pos]),
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
      exact (hOK.1.1.vanish τ hτ z hz'.le).1
  have hSGθπ : ∀ (τ : ℝ), 0 ≤ τ → ∀ z, Work.FTS_RegExport.RXR5.SG α g z (Real.pi / 2) τ = 0 := by
    intro τ hτ z
    by_cases hz : z ≤ 0
    · exact Work.FTS_RegExport.RXR5.SG_apply_of_nonpos hz
    · have hz' : 0 < z := lt_of_not_ge hz
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' (by linarith [Real.pi_pos]) le_rfl,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
      exact (hOK.1.1.vanish τ hτ z hz'.le).2
  -- the vanishing of the stream function on the two angular boundaries
  have hPsθ0 : ∀ (τ : ℝ), ∀ z, Work.FTS_RegExport.RXR5.SΨ α Φs E g z 0 τ = 0 := by
    intro τ z
    by_cases hz : z ≤ 0
    · have h := Work.FTS.RegExportIface.psiR_of_nonpos (α := α) (Φs := Φs) (E := E)
        (G := Work.FTS.FinalV2.tauExt g) (z := z) (θ := 0) (τ := τ) hz
      change Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) z 0 τ = 0
      rw [h]
      simp only [Work.Construction.Theta, Work.Construction.s2, Real.sin_zero, mul_zero,
        zero_mul]
    · exact Work.FTS.RegExportIface.psiR_zero (α := α) (Φs := Φs) (E := E)
        (G := Work.FTS.FinalV2.tauExt g) (z := z) (τ := τ) (lt_of_not_ge hz)
  have hPsθπ : ∀ (τ : ℝ), ∀ z, Work.FTS_RegExport.RXR5.SΨ α Φs E g z (Real.pi / 2) τ = 0 := by
    intro τ z
    by_cases hz : z ≤ 0
    · have h := Work.FTS.RegExportIface.psiR_of_nonpos (α := α) (Φs := Φs) (E := E)
        (G := Work.FTS.FinalV2.tauExt g) (z := z) (θ := Real.pi / 2) (τ := τ) hz
      change Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) z (Real.pi / 2) τ
        = 0
      rw [h]
      simp only [Work.Construction.Theta, Work.Construction.s2, hs2π, mul_zero, zero_mul]
    · exact Work.FTS.RegExportIface.psiR_pi_div_two (α := α) (Φs := Φs) (E := E)
        (G := Work.FTS.FinalV2.tauExt g) (z := z) (τ := τ) (lt_of_not_ge hz)
  refine ⟨?_, ?_, ?_⟩
  · -- the stratum `z = 0`
    intro τ hτ θ hθ
    have hf : ∀ θ', Work.FTS_RegExport.RXR5.SG α g 0 θ' τ = 0 :=
      fun θ' => Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl
    have hF : ∀ θ', Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ 0 θ' = 0 := by
      intro θ'
      have h1 : Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ' = 0 := hFst θ'
      simp only [Work.Construction.Ftau]
      rw [h1, hf θ', add_zero]
    have hdl : Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ 0 θ = 0 := by
      have hL := R0_LGammaT_at_z0 (α := Work.FTS.Regularity.pExp α)
        (f := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SG α g) τ) hf θ
      simp only [Work.FTS.Galerkin.dynLin, hL, neg_zero]
    have hdr : Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ 0 θ = 0 := by
      simp only [Work.FTS.Galerkin.dynRHS]
      exact R0_gRHS_at_z0 (α := Work.FTS.Regularity.pExp α)
        (F := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
        (f := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SG α g) τ)
        (Φ := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)
        hF hf hFst θ
    rw [hdl, hdr, add_zero]
  · -- the stratum `θ = 0`
    intro τ hτ z
    have hf : ∀ z', Work.FTS_RegExport.RXR5.SG α g z' 0 τ = 0 := hSGθ0 τ hτ.1
    have hF : ∀ z', Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ z' 0 = 0 := by
      intro z'
      have h1 : Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' 0 = 0 := hFstθ0 z'
      simp only [Work.Construction.Ftau]
      rw [h1, hf z', add_zero]
    have hΦ : ∀ z', Work.FTS_RegExport.RXR5.SΨ α Φs E g z' 0 τ = 0 := fun z' => hPsθ0 τ z'
    have hdl : Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ z 0 = 0 := by
      have hL := R0_LGammaT_at_theta0 (α := Work.FTS.Regularity.pExp α) hα0
        (f := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SG α g) τ) hf z
      simp only [Work.FTS.Galerkin.dynLin, hL, neg_zero]
    have hdr : Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ z 0 = 0 := by
      simp only [Work.FTS.Galerkin.dynRHS]
      exact R0_gRHS_at_theta0 (α := Work.FTS.Regularity.pExp α)
        (F := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
        (f := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SG α g) τ)
        (Φ := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)
        hα0 hF hf hΦ z
    rw [hdl, hdr, add_zero]
  · -- the stratum `θ = π/2`
    intro τ hτ z
    have hf : ∀ z', Work.FTS_RegExport.RXR5.SG α g z' (Real.pi / 2) τ = 0 := hSGθπ τ hτ.1
    have hF : ∀ z', Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ z' (Real.pi / 2) = 0 := by
      intro z'
      have h1 : Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' (Real.pi / 2) = 0 :=
        hFstθπ z'
      simp only [Work.Construction.Ftau]
      rw [h1, hf z', add_zero]
    have hΦ : ∀ z', Work.FTS_RegExport.RXR5.SΨ α Φs E g z' (Real.pi / 2) τ = 0 :=
      fun z' => hPsθπ τ z'
    have hdl : Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ z (Real.pi / 2) = 0 := by
      have hL := R0_LGammaT_at_thetaPi2 (α := Work.FTS.Regularity.pExp α) hα0
        (f := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SG α g) τ) hf z
      simp only [Work.FTS.Galerkin.dynLin, hL, neg_zero]
    have hdr : Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ z
        (Real.pi / 2) = 0 := by
      simp only [Work.FTS.Galerkin.dynRHS]
      exact R0_gRHS_at_thetaPi2 (α := Work.FTS.Regularity.pExp α)
        (F := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
        (f := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SG α g) τ)
        (Φ := Work.FTS.Galerkin.slice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ)
        hα0 hF hf hΦ z
    rw [hdl, hdr, add_zero]

end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.Vz7Split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.Vz7Split` — the sharp decomposition of `Vz7` and the exact smallness
criterion for `VelPkg.vz0`

**Why this file exists.**  The frozen producer `RX-VP` (`velPkg`) concludes, among other fields,
the sign condition `VelPkg.vz0 : 0 ≤ Vz7 αG μ G Φ z θ τ`.  By
`Work.FTS_RegExport.RXDiag.closedFormOpen` this reads, on the open quadrant,

    Vz7 = (1 − μτ) + 2·αG·V(Φ̃),

so the whole difficulty of `vz0` is a *lower* bound on `V(Φ̃)`.  This file isolates that
difficulty in the sharpest form:

* `Vop_add_point` — `V` is additive at a point where the two `θ`-slices are differentiable;
* `two_mul_Vop_Theta` — the exact `Θ`-identity `2 αG·V(Θ αG F) = L₁₂(F)·c2m`;
* `differentiableAt_thetaslice_Theta` — the `θ`-slice of `Θ` is differentiable;
* `vop_slice_eq_star_add_E` — **the sharp split**

      V(Φ) = V(Φ̃_*) + c2m(θ)/(1+z) + V(E u),      Φ = Φs + E u,  Φ̃_* = Φs − Θ(F_*),

  in which the singular `Θ`-parts and the `L₁₂(F_*)·c2m` term cancel *exactly* (using
  `L₁₂(F_*) = 2αG/(1+z)`), so that only the *star* slot `V(Φ̃_*)` and the *elliptic* slot
  `V(E u)` survive — with an extra factor `αG` in the smallness;
* `vz7_nonneg_of_sharp` — the resulting criterion
  `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2  ⟹  Vz7 ≥ 0` when `|V(Φ̃_*)| ≤ Cs·αG` and `|V(E u)| ≤ CE·αG`;
* `vz7_nonneg_of_vop_split` — the same with the split and the closed form discharged.

**What the criterion says (and why the frozen statement cannot be proved as written).**  The
binding term is `2·αG·c2m(θ)/(1+z) ≥ −4·αG/(1+z) ≥ −4·αG`, coming from
`L₁₂(F_*)·c2m(θ) = (2αG/(1+z))·c2m(θ)`.  Since `pExp α = 3α` and the frozen hypothesis is only
`α ≤ 1/3` (i.e. `αG ≤ 1`), even the *best case* `V(Φ̃_*) = V(E u) = 0` fails at `αG ≥ 1/8`:
`1 − μτ − 4·αG/(1+z) < 0`.  And no fixed threshold in `α` can be *proved*, because the available
slot bounds are `|V(Φ̃_*)| ≤ Cs·αG` (from `StarPkgo2.VW`) and
`|V(E u)| ≤ Ce·HkNorm αG 6 u + |L₁₂(u)|/αG`, where `Cs, Ce, C₀` are *free* binders of the
producers, so the required threshold is `αG ≲ min(1/8, 1/(2Cs), 2/(C·C₀), …)`.  This is the
machine-checked form of the diagnosis in `NOTES_FINAL.md` §9/§16.

Everything here is stated for the frozen definitions; nothing outside this file is modified.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## 1. The additivity of `V` at a point -/

/-- `V(A + B) = V(A) + V(B)` at a point where both `θ`-slices are differentiable. -/
theorem Vop_add_point {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Construction.Vop (fun z θ => A z θ + B z θ) z θ
      = Work.Construction.Vop A z θ + Work.Construction.Vop B z θ := by
  have hderiv : deriv (fun θ' => A z θ' + B z θ') θ
      = deriv (fun θ' => A z θ') θ + deriv (fun θ' => B z θ') θ :=
    deriv_add hA hB
  simp only [Work.Construction.Vop, Work.Spaces.pth]
  rw [hderiv]
  ring

/-! ## 2. The closed form of the `Θ` part of `V` -/

/-- `2 αG·V(Θ αG F) = L₁₂(F)·c2m` on the open quadrant — the identity that makes the `Θ` parts
cancel against the `L₁₂(F)·c2m` term of `Vz7`. -/
theorem two_mul_Vop_Theta {αG : ℝ} (hαG : 0 < αG) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hα0 : αG ≠ 0 := ne_of_gt hαG
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (2 * αG)) * Real.cos (2 * θ) * Work.Construction.L12 F z :=
    Work.Construction.pth_Theta_eq hαG z θ
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  rw [Real.sin_sq]
  ring

/-- The `θ`-slice of `Θ αG F` is differentiable everywhere. -/
theorem differentiableAt_thetaslice_Theta {αG : ℝ} {F : ℝ → ℝ → ℝ} (z θ : ℝ) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Theta αG F z θ') θ := by
  have hfun : (fun θ' => Work.Construction.Theta αG F z θ')
      = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
    funext θ'
    simp only [Work.Construction.Theta, Work.Construction.s2]
    ring
  rw [hfun]
  exact (differentiableAt_const _).mul
    ((Real.differentiableAt_sin).comp θ ((differentiableAt_id (x := θ)).const_mul (2 : ℝ)))

/-! ## 3. The sharp split of `V(Φ)` -/


/-! ## 4. The criterion -/

/-- **The criterion.**  If `V(Φ) = A + c2m(θ)/(1+z) + B` at a point of the open quadrant with
`|A| ≤ Cs·αG`, `|B| ≤ CE·αG` and `|μ τ| ≤ 1/2`, then

    Vz7 = (1 − μτ) + 2·αG·V(Φ) ≥ 0

as soon as `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2`.  (No positivity of `Cs, CE` is needed, and the
angular variable enters only through `c2m θ`.) -/
theorem vz7_nonneg_of_sharp {αG Cs CE : ℝ} (hαG : 0 < αG)
    {μ : ℝ → ℝ} {G Φ : Fam} {A B : Fn} {τ z θ : ℝ}
    (hz : 0 < z) (hmu : |μ τ| ≤ 1 / 2)
    (hsplit : Work.Construction.Vop (slice Φ τ) z θ
      = A z θ + Work.Construction.c2m θ / (1 + z) + B z θ)
    (hA : |A z θ| ≤ Cs * αG) (hB : |B z θ| ≤ CE * αG)
    (hclosed : Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
      = (1 - μ τ) + 2 * αG * Work.Construction.Vop (slice Φ τ) z θ)
    (hnum : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ := by
  rw [hclosed, hsplit]
  have hden : (0 : ℝ) < 1 + z := by linarith
  have hc2m : -(2 : ℝ) ≤ Work.Construction.c2m θ := by
    have h := Work.FTS_RegExport.RXVP.abs_c2m_le_two θ
    linarith [neg_abs_le (Work.Construction.c2m θ)]
  have hmu1 : (1 : ℝ) / 2 ≤ 1 - μ τ := by
    have h := (abs_le.mp hmu).2
    linarith
  -- the three lower bounds, scaled by `2 αG > 0`
  have hA' : -(2 * Cs * αG ^ 2) ≤ 2 * αG * A z θ := by
    have h1 : -Cs * αG ≤ A z θ := by
      have h := (abs_le.mp hA).1
      linarith
    nlinarith [hαG, h1]
  have hc2m' : -(4 * αG) ≤ 2 * αG * (Work.Construction.c2m θ / (1 + z)) := by
    have h1 : (0 : ℝ) < 2 * αG / (1 + z) := by positivity
    have h3 : (2 * αG / (1 + z)) * (-2) ≤ (2 * αG / (1 + z)) * Work.Construction.c2m θ :=
      mul_le_mul_of_nonneg_left hc2m h1.le
    have h4 : (2 * αG / (1 + z)) * Work.Construction.c2m θ
        = 2 * αG * (Work.Construction.c2m θ / (1 + z)) := by ring
    have h5 : (2 * αG / (1 + z)) * (-2) = -(4 * αG) + (4 * αG) * z / (1 + z) := by
      field_simp
      ring
    have h6 : 0 ≤ (4 * αG) * z / (1 + z) := by positivity
    linarith [h3, h4, h5, h6]
  have hB' : -(2 * CE * αG ^ 2) ≤ 2 * αG * B z θ := by
    have h1 : -CE * αG ≤ B z θ := by
      have h := (abs_le.mp hB).1
      linarith
    nlinarith [hαG, h1]
  have hsum : 2 * αG * (A z θ + Work.Construction.c2m θ / (1 + z) + B z θ)
      = 2 * αG * A z θ + 2 * αG * (Work.Construction.c2m θ / (1 + z)) + 2 * αG * B z θ := by
    ring
  rw [hsum]
  nlinarith [hA', hc2m', hB', hmu1, hnum]


/-! ## 5. Discharging the star slot from `StarPkgo2.VW` -/

/-- The `VW` field of `StarPkgo2` (`WlInf α 4 (V(Φ̃_*)) ≤ Cs·α`, plus its `WlInfMem`) gives the
pointwise bound `|V(Φ̃_*)(z,θ)| ≤ Cs·α` on the closed quadrant.  This is the *first* of the two
inputs of `vz7_nonneg_of_sharp`, and it is a *field* of the frozen `hStar`. -/
theorem starVop_pointwise_le {α Cs : ℝ} {Φs : Fn}
    (hmem : Work.Spaces.WlInfMem α 4 (Work.Construction.Vop
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)))
    (hbnd : Work.Spaces.WlInf α 4 (Work.Construction.Vop
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ≤ Cs * α) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α := by
  intro z θ hz hθ hθ2
  have h1 : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        z θ|
      ≤ Work.Spaces.WlInf α 4 (Work.Construction.Vop
          (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) := by
    have h := Work.Spaces.WlInf_z_bound α 4 _ hmem 0 (by norm_num) z θ
      (show z ∈ Work.Spaces.Iz from Set.mem_Ici.mpr hz.le)
      (show θ ∈ Work.Spaces.Iθ from Set.mem_Icc.mpr ⟨hθ.le, hθ2.le⟩)
    simpa using h
  exact le_trans h1 hbnd


end Work.FTS_RegExport
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.SliceTr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 The transport identity -/

/-- On the closed angular strip, for `z > 0` and `τ ≥ 0`, the slice `F_* + slice g τ` is the full
profile of the *extended* family `extG G` — the object the package `RegPkg'` describes. -/
theorem Ftau_eq_profFull {a : ℝ} {g G : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ
      = Work.FTS.Regularity.profFull a (Work.FTS.RegPkgGal.extG G) z θ τ := by
  have h1 : Work.FTS.RegPkgGal.extG G z θ τ = g z θ τ := by
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ, hG z θ τ hz hθ hτ]
  simp only [Work.Construction.Ftau, Work.FTS.Regularity.profFull, h1]

/-! ## §2 Elementary facts about `F_*` and `Γ` -/

/-- `|F_*(z)| ≤ 1/2`, with `F_*(z) = 2z/(1+z)²` (attained at `z = 1`). -/
theorem FM_Fstar_abs_le_half {z : ℝ} (hz : 0 ≤ z) : |Work.FM.Fstar z| ≤ 1 / 2 := by
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  have hzabs : |z| = z := abs_of_nonneg hz
  rw [Work.FM.Fstar, abs_div, abs_mul, abs_of_pos hden, abs_of_pos (by norm_num : (0:ℝ) < 2),
    hzabs, div_le_iff₀ hden]
  nlinarith [sq_nonneg (1 - z)]

/-- `Γ(θ) = Gam (pExp a) θ` is nonnegative on the closed strip. -/
theorem Gam_nonneg_of_Iθ {a θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by
  rw [← Work.FTS.Regularity.Gamma_eq_Gam a θ]
  exact Work.ConstructionInstance.Gamma_nonneg hθ

/-- `Γ(θ) = Gam (pExp a) θ` is at most `1` on the closed strip. -/
theorem Gam_le_one_of_Iθ {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ ≤ 1 := by
  rw [← Work.FTS.Regularity.Gamma_eq_Gam a θ]
  exact Work.ConstructionInstance.Gamma_le_one (le_of_lt ha) hθ

/-- **The `Γ`-decay of `F_*`**: `|F_*| ≤ 5 pExp a · Γ(θ)` on the closed strip (the `Γ`-factor
comes from the profile's angular factor `Γ/c`, with `c ≥ 1/10`). -/
theorem Fstar_abs_le_Gamma {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) {z θ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z θ|
      ≤ 5 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp a) hpa
    (Work.FTS.Regularity.pExp_le_one ha13)
  have hc0 : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp a) := by linarith [hc.1]
  have hGam0 : 0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := Gam_nonneg_of_Iθ hθ
  have hFM := FM_Fstar_abs_le_half hz
  have key : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)|
      ≤ 10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by
    rw [abs_of_nonneg (div_nonneg hGam0 (le_of_lt hc0)), div_le_iff₀ hc0]
    nlinarith [hc.1]
  have hkey : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |Work.FM.Fstar z|
      ≤ (10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * (1 / 2) :=
    mul_le_mul key hFM (abs_nonneg _) (by linarith)
  rw [Work.Construction.Fstar, abs_mul, abs_mul, abs_of_pos hpa]
  calc Work.FTS.Regularity.pExp a * |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |Work.FM.Fstar z|
      = Work.FTS.Regularity.pExp a
          * (|Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |Work.FM.Fstar z|) := by ring
    _ ≤ Work.FTS.Regularity.pExp a
          * ((10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * (1 / 2)) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt hpa)
    _ = 5 * Work.FTS.Regularity.pExp a * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by ring
    _ = 5 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
        rw [Work.FTS.Regularity.Gamma_eq_Gam]

/-- **The `Γ`-decay of `D_zF_*`**: `|D_zF_*| ≤ 20 pExp a · Γ(θ)` for `z > 0` on the closed strip. -/
theorem Dz_Fstar_abs_le_Gamma {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ|
      ≤ 20 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp a) hpa
    (Work.FTS.Regularity.pExp_le_one ha13)
  have hc0 : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp a) := by linarith [hc.1]
  have hGam0 : 0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := Gam_nonneg_of_Iθ hθ
  have key : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)|
      ≤ 10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by
    rw [abs_of_nonneg (div_nonneg hGam0 (le_of_lt hc0)), div_le_iff₀ hc0]
    nlinarith [hc.1]
  have hb : |2 * z * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
    have hden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rcases le_total z 1 with hz1 | hz1
    · have hnn : 0 ≤ 2 * z * (1 - z) := by nlinarith
      rw [abs_of_nonneg hnn]
      nlinarith [hz, hz1, sq_nonneg (1 + z), sq_nonneg z,
        pow_pos (by linarith : (0:ℝ) < 1 + z) 3]
    · have hnn : 0 ≤ 2 * z * (z - 1) := by nlinarith
      have heq : 2 * z * (1 - z) = -(2 * z * (z - 1)) := by ring
      rw [heq, abs_neg, abs_of_nonneg hnn]
      nlinarith [hz, hz1, sq_nonneg (1 + z)]
  have hkey : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |2 * z * (1 - z) / (1 + z) ^ 3|
      ≤ (10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * 2 :=
    mul_le_mul key hb (abs_nonneg _) (by linarith)
  have hz1' : (-1 : ℝ) < z := by linarith
  rw [Work.Construction.Dz_Fstar_eq hpa hz1', abs_mul, abs_mul, abs_of_pos hpa]
  calc Work.FTS.Regularity.pExp a * |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |2 * z * (1 - z) / (1 + z) ^ 3|
      = Work.FTS.Regularity.pExp a
          * (|Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |2 * z * (1 - z) / (1 + z) ^ 3|) := by
        ring
    _ ≤ Work.FTS.Regularity.pExp a
          * ((10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * 2) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt hpa)
    _ = 20 * Work.FTS.Regularity.pExp a * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by ring
    _ = 20 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
        rw [Work.FTS.Regularity.Gamma_eq_Gam]



/-- `F_*` vanishes at `θ = 0`. -/
theorem Fstar_apply_zero {a z : ℝ} (ha : a ≠ 0) :
    Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z 0 = 0 := by
  have hne : Work.FTS.Regularity.pExp a / 3 ≠ 0 := by
    rw [Work.FTS.Regularity.pExp]
    exact fun h => ha (by linarith [h])
  have h0 : Work.Spaces.Gam (Work.FTS.Regularity.pExp a) 0 = 0 := by
    have h := Real.zero_rpow hne
    simpa only [Work.Spaces.Gam, Real.sin_zero, Real.cos_zero, mul_one, zero_mul] using h
  simp only [Work.Construction.Fstar, h0, zero_div, zero_mul, mul_zero]

/-- `F_*` vanishes at `θ = π/2`. -/
theorem Fstar_apply_pi_div_two {a z : ℝ} (ha : a ≠ 0) :
    Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z (π / 2) = 0 := by
  have hne : Work.FTS.Regularity.pExp a / 3 ≠ 0 := by
    rw [Work.FTS.Regularity.pExp]
    exact fun h => ha (by linarith [h])
  have h0 : Work.Spaces.Gam (Work.FTS.Regularity.pExp a) (π / 2) = 0 := by
    have h := Real.zero_rpow hne
    simpa only [Work.Spaces.Gam, Real.cos_pi_div_two, Real.sin_pi_div_two, one_mul,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using h
  simp only [Work.Construction.Fstar, h0, zero_div, zero_mul, mul_zero]

/-- `Γ` is continuous (for a positive exponent, also at `0` and `π/2`). -/
theorem continuous_Gamma {a : ℝ} (ha : 0 < a) :
    Continuous (fun θ : ℝ => Work.FTS.Regularity.Gamma a θ) := by
  have hbase : Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) :=
    Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have h := hbase.rpow_const (fun θ => Or.inr (le_of_lt ha))
  simpa only [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma] using h

/-! ## §3 Transport of the `RegPkg'` data to the slice at a fixed `τ ≥ 0` -/

/-- **The `Γ`-decay of the perturbation** `|g| ≤ Cv·Γ(θ)` on the closed strip, transported from
`RegPkg'.hvan` (at the horizon `τ + 1`). -/
theorem slice_abs_le_Gamma {a τ : ℝ} (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma a θ := by
  obtain ⟨Cv, hCv0, hCv⟩ := (hreg (τ + 1) (by linarith)).hvan
  refine ⟨Cv, hCv0, fun z θ hz hθ => ?_⟩
  have hmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have h := hCv τ hmem z θ (le_of_lt hz) hθ
  rwa [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ, hG z θ τ hz hθ hτ] at h

/-- The pointwise `Γ`-bound of the whole profile at a fixed `τ ≥ 0`. -/
theorem ftau_abs_le_Gamma {a τ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) (hτ : 0 ≤ τ)
    {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ|
        ≤ Cg * Work.FTS.Regularity.Gamma a θ := by
  obtain ⟨Cv, hCv0, hCv⟩ := slice_abs_le_Gamma hτ hreg hG
  have hpa : 0 ≤ Work.FTS.Regularity.pExp a := le_of_lt (Work.FTS.Regularity.pExp_pos ha)
  refine ⟨5 * Work.FTS.Regularity.pExp a + Cv, by linarith, fun z θ hz hθ => ?_⟩
  have hstar := Fstar_abs_le_Gamma ha ha13 (le_of_lt hz) hθ
  have hg := hCv z θ hz hθ
  rw [Work.Construction.Ftau]
  calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z θ + g z θ τ|
      ≤ |Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z θ| + |g z θ τ| := abs_add_le _ _
    _ ≤ 5 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ
          + Cv * Work.FTS.Regularity.Gamma a θ := add_le_add hstar hg
    _ = (5 * Work.FTS.Regularity.pExp a + Cv) * Work.FTS.Regularity.Gamma a θ := by ring

/-- The profile `F(τ)` vanishes on the two angular boundary lines (on `z > 0`). -/
theorem ftau_vanish {a τ : ℝ} (ha : a ≠ 0) (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ z : ℝ, 0 < z →
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z 0 = 0 ∧
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z (π / 2) = 0 := by
  intro z hz
  have hmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hv := (hreg (τ + 1) (by linarith)).vanish hmem
  have hIθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by positivity⟩
  have hIθ1 : (π / 2 : ℝ) ∈ Work.Spaces.Iθ := ⟨by positivity, le_rfl⟩
  have hg0 : g z 0 τ = 0 := by
    rw [← hG z 0 τ hz hIθ0 hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
    exact hv.1 z
  have hg1 : g z (π / 2) τ = 0 := by
    rw [← hG z (π / 2) τ hz hIθ1 hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
    exact hv.2 z
  constructor
  · simp only [Work.Construction.Ftau, Fstar_apply_zero ha, hg0, add_zero]
  · simp only [Work.Construction.Ftau, Fstar_apply_pi_div_two ha, hg1, add_zero]

/-- The profile `F(τ)` is supported in `z ≥ L` for some `L > 0`. -/
theorem ftau_supp {a τ : ℝ} (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ : ℝ, L ≤ z → θ ∈ Work.Spaces.Iθ →
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ = 0 := by
  obtain ⟨L, hL0, hL⟩ := (hreg (τ + 1) (by linarith)).supp
  refine ⟨L, hL0, fun z θ hzL hθ => ?_⟩
  have hz : 0 < z := lt_of_lt_of_le hL0 hzL
  rw [Ftau_eq_profFull hτ hG hz hθ]
  exact hL τ ⟨hτ, by linarith⟩ z θ hzL



/-! ## §4 Curry/Fréchet tools for `pz` on an open set -/



end Work.FTS_StreamBdry.Inputs
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.srcOK_Ftau =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-! ## §1 Continuity of `Γ` and of `F_*` on the closed angular strip -/

/-- `Γ(θ) = (sin θ cos²θ)^{α/3}` is continuous on *any* set when `0 < α`.  (The base vanishes at
`θ = 0, π/2`, but the exponent is positive, so `Real.rpow` is continuous there too.) -/
theorem Gam_continuousOn (α : ℝ) (hα : 0 < α) (s : Set ℝ) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) s := by
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) s :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h := hbase.rpow_const (p := α / 3) (fun θ _ => Or.inr (by linarith))
  simpa only [Work.Spaces.Gam] using h

/-- `F_{*,rad}(z) = 2z/(1+z)²` is continuous on `Ioi 0`. -/
theorem FM_Fstar_continuousOn : ContinuousOn (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi 0) := by
  have h2 : ContinuousOn (fun z : ℝ => (2 : ℝ) * z / (1 + z) ^ 2) (Set.Ioi 0) :=
    ((continuousOn_const.mul continuousOn_id).div
      ((continuousOn_const.add continuousOn_id).pow 2)
      (fun z hz => pow_ne_zero 2 (by rw [Set.mem_Ioi] at hz; linarith)))
  simpa only [Work.FM.Fstar] using h2

/-- The closed form `∂_zF_{*,rad} = 2(1-z)/(1+z)³` on `Ioi 0`. -/
theorem deriv_FM_Fstar_closed {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    deriv Work.FM.Fstar z = 2 * (1 - z) / (1 + z) ^ 3 := by
  have hz' : z ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; rw [Set.mem_Ioi] at hz; linarith
  have h := Work.FTS.StrongPersist.H6Pair6Aux.deriv_iter_FM_Fstar_eq 1 hz'
  rw [Function.iterate_one] at h
  rw [h]
  norm_num
  ring

/-- `∂_zF_{*,rad}` is continuous on `Ioi 0`. -/
theorem continuousOn_deriv_FM_Fstar :
    ContinuousOn (fun z : ℝ => deriv Work.FM.Fstar z) (Set.Ioi 0) := by
  refine ContinuousOn.congr ?_ (fun z hz => deriv_FM_Fstar_closed hz)
  have hden : ContinuousOn (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) :=
    ((continuousOn_const.add continuousOn_id).pow 3)
  exact ((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).div hden
    (fun z hz => pow_ne_zero 3 (by rw [Set.mem_Ioi] at hz; linarith)))

/-- `F_{*,rad}` is differentiable at every `z > 0`. -/
theorem FM_Fstar_differentiableAt {z : ℝ} (hz : 0 < z) : DifferentiableAt ℝ Work.FM.Fstar z := by
  have h : DifferentiableAt ℝ (fun z : ℝ => (2 : ℝ) * z / (1 + z) ^ 2) z := by
    refine ((differentiableAt_const (c := (2 : ℝ))).mul differentiableAt_id).div
      (((differentiableAt_const (c := (1 : ℝ))).add differentiableAt_id).pow 2) ?_
    exact pow_ne_zero 2 (by linarith)
  change DifferentiableAt ℝ (fun z : ℝ => (2 : ℝ) * z / (1 + z) ^ 2) z
  exact h

/-- The `z`-derivative of the radial profile `F_*(z,θ) = α(Γ(θ)/c)F_{*,rad}(z)`. -/
theorem pz_Fstar_eq {α : ℝ} {z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.pz (Work.Construction.Fstar α) z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z := by
  have hdiff : DifferentiableAt ℝ Work.FM.Fstar z := FM_Fstar_differentiableAt hz
  rw [Work.Spaces.pz]
  change deriv ((fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
      * Work.FM.Fstar z')) z
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z
  rw [deriv_const_mul _ hdiff]

/-- `(z,θ) ↦ F_*(z,θ)` is continuous on the closed angular strip. -/
theorem continuousOn_Fstar_pair {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.Fstar α p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hGam : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (Gam_continuousOn α hα Set.univ).comp continuousOn_snd (fun p _ => trivial)
  have hFM : ContinuousOn (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    FM_Fstar_continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * Work.FM.Fstar p.1)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_const.mul (hGam.div_const _)).mul hFM
  refine h.congr (fun p _ => ?_)
  simp only [Work.Construction.Fstar]


/-- **The numerical bounds of the radial profile**: on the closed angular strip,
`|F_*| ≤ 40α` and `|z ∂_zF_*| ≤ 40α` for `0 < α ≤ 1`.  (Uses `Γ ≤ 1`, `c ∈ [1/10,10]` and the
order-`≤ 1` jets `|F_{*,rad}| ≤ 2`, `|z ∂_zF_{*,rad}| ≤ 4`.) -/
theorem Fstar_bounds {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar z| ≤ 40 * α ∧
    |z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z)| ≤ 40 * α := by
  obtain ⟨hGam0, _⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, _⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hquot : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
    rw [abs_div, abs_of_nonneg hGam0, abs_of_pos hcpos, div_le_iff₀ hcpos]
    linarith
  have hFM : |Work.FM.Fstar z| ≤ 2 := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.zpow_deriv_FM_Fstar_le 0 (le_of_lt hz)
    simpa using h
  have hzderiv : |z * deriv Work.FM.Fstar z| ≤ 4 := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.zpow_deriv_FM_Fstar_le 1 (le_of_lt hz)
    rw [pow_one, Function.iterate_one] at h
    norm_num at h
    rw [abs_mul]
    exact h
  have hα0 : 0 ≤ α := le_of_lt hα
  constructor
  · rw [abs_mul, abs_mul, abs_of_nonneg hα0]
    calc α * |Work.Spaces.Gam α θ / Work.Spaces.c α| * |Work.FM.Fstar z| ≤ α * 10 * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hquot hα0) hFM (abs_nonneg _) (by positivity)
      _ ≤ 40 * α := by linarith
  · rw [show z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z)
        = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (z * deriv Work.FM.Fstar z)
        from by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg hα0]
    calc α * |Work.Spaces.Gam α θ / Work.Spaces.c α| * |z * deriv Work.FM.Fstar z|
        ≤ α * 10 * 4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hquot hα0) hzderiv (abs_nonneg _) (by positivity)
      _ ≤ 40 * α := by linarith

/-! ## §2 Differentiability of a slice, and the splitting of `∂_z(F_* + ·)` -/

/-- **A slice of the family is differentiable in `z` on `z > 0`.**  This is the `hcont` field of
`RegPkg'` (`C¹` in `(z,τ)` on `Ioi (-1) ×ˢ Ioo (-1) (S+1)`) restricted to the line `τ = const`. -/
theorem RegPkg'_slice_differentiableAt {a S z θ τ : ℝ} {A B : ℝ → ℝ} {G' : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' a S A B G') (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) (hz : 0 < z) : DifferentiableAt ℝ (fun z' => G' z' θ τ) z := by
  have hmem : (z, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) :=
    ⟨by rw [Set.mem_Ioi]; linarith,
      by rw [Set.mem_Ioo]; exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => G' q.1 θ q.2) (z, τ) :=
    ((h.hcont θ hθ).differentiableOn one_ne_zero (z, τ) hmem).differentiableAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  have hline : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
  have hcomp := hdiff.comp z hline
  have hfun : (fun z' : ℝ => G' z' θ τ)
      = ((fun q : ℝ × ℝ => G' q.1 θ q.2) ∘ (fun z' : ℝ => (z', τ))) := rfl
  rw [hfun]
  exact hcomp

/-- **The `z`-derivative of `F_* + G'` splits**: the radial profile contributes
`α(Γ/c)∂_zF_{*,rad}`, the perturbation its own `∂_z`. -/
theorem pz_add_eq {α : ℝ} {G' : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ}
    (hdiff : DifferentiableAt ℝ (fun z' => G' z' θ τ) z) (hz : 0 < z) :
    Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + G' z θ τ) z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z
        + Work.Spaces.pz (fun z θ => G' z θ τ) z θ := by
  have hF : DifferentiableAt ℝ (fun z' : ℝ => Work.Construction.Fstar α z' θ) z := by
    have h : DifferentiableAt ℝ
        (fun z' : ℝ => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z') z :=
      (FM_Fstar_differentiableAt hz).const_mul _
    change DifferentiableAt ℝ
      (fun z' : ℝ => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z') z
    exact h
  have hsplit : deriv (fun z' : ℝ => Work.Construction.Fstar α z' θ + G' z' θ τ) z
      = deriv (fun z' : ℝ => Work.Construction.Fstar α z' θ) z
        + deriv (fun z' : ℝ => G' z' θ τ) z := by
    rw [show (fun z' : ℝ => Work.Construction.Fstar α z' θ + G' z' θ τ)
        = (fun z' : ℝ => Work.Construction.Fstar α z' θ)
          + (fun z' : ℝ => G' z' θ τ) from rfl]
    exact deriv_add hF hdiff
  have hFz : deriv (fun z' : ℝ => Work.Construction.Fstar α z' θ) z
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * deriv Work.FM.Fstar z :=
    pz_Fstar_eq (α := α) (θ := θ) hz
  simp only [Work.Spaces.pz]
  rw [hsplit, hFz]

theorem srcOK_Ftau {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ L Mf : ℝ,
      Work.FTS.StreamBdryIface.SrcOK (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) L Mf := by
  intro τ hτ
  have hαpos : 0 < pExp a := Work.FTS.Regularity.pExp_pos ha
  have hα1 : pExp a ≤ 1 := Work.FTS.Regularity.pExp_le_one ha13
  set S : ℝ := max τ 1 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact lt_of_lt_of_le one_pos (le_max_right τ 1)
  have hτS : τ ∈ Set.Icc 0 S := by rw [hSdef]; exact ⟨hτ, le_max_left τ 1⟩
  have hreg' : Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G) := hreg S hSpos
  obtain ⟨Ng, hJet⟩ := hreg'.hg
  obtain ⟨Npz, hJetpz⟩ := hreg'.hpz
  obtain ⟨L, hLpos, hLsupp⟩ := hreg'.hsupp
  have hNg0 : 0 ≤ Ng := hJet.1
  have hNpz0 : 0 ≤ Npz := hJetpz.1
  set Mf : ℝ := 80 * pExp a + Ng + L * Npz + 1 with hMfdef
  -- the `∂_z`-derivative of the full profile splits into that of `F_*` and that of the perturbation
  have hDz_eq : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.pz (Work.Construction.Ftau (pExp a) g τ) z θ
        = pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
            * deriv Work.FM.Fstar z
          + Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ := by
    intro z θ hz hθ
    have hdiff : DifferentiableAt ℝ (fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) z :=
      RegPkg'_slice_differentiableAt hreg' hθ hτS hz
    have h1 : Work.Spaces.pz (Work.Construction.Ftau (pExp a) g τ) z θ
        = Work.Spaces.pz (fun z θ => Work.Construction.Fstar (pExp a) z θ
            + Work.FTS.RegPkgGal.extG G z θ τ) z θ := by
      simp only [Work.Spaces.pz]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      show Work.Construction.Ftau (pExp a) g τ z' θ
          = Work.Construction.Fstar (pExp a) z' θ + Work.FTS.RegPkgGal.extG G z' θ τ
      simp only [Work.Construction.Ftau]
      rw [Work.FTS.RegPkgGal.extG_of_pos hz' hτ, hG z' θ τ hz' hθ hτ]
    rw [h1, pz_add_eq (α := pExp a) (G' := fun z θ τ => Work.FTS.RegPkgGal.extG G z θ τ)
      (z := z) (θ := θ) (τ := τ) hdiff hz]
  -- `D_zF = 0` beyond the support radius
  have hDz_zero : ∀ z θ : ℝ, L < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Construction.Ftau (pExp a) g τ) z θ = 0 := by
    intro z θ hzL hθ
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    have hev : (fun z' : ℝ => Work.Construction.Ftau (pExp a) g τ z' θ) =ᶠ[nhds z] 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds hzL] with z' hz'
      have hz'0 : 0 < z' := lt_trans hLpos hz'
      have h := hLsupp τ hτS z' θ (le_of_lt hz')
      simp only [Work.FTS.Regularity.profFull_apply] at h
      show Work.Construction.Ftau (pExp a) g τ z' θ = 0
      rw [Work.Construction.Ftau,
        ← hG z' θ τ hz'0 hθ hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz'0 hτ]
      exact h
    rw [Filter.EventuallyEq.deriv_eq hev]
    simp
  refine ⟨L, Mf, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of `F` on the closed angular strip
    have hFstar := continuousOn_Fstar_pair (α := pExp a) hαpos
    have hgs : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.RegPkgGal.extG G p.1 p.2 τ)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (Work.FTS.PressureOn.continuousOn_uncurry_gSlice ha hJet hτS).mono
        (fun p hp => ⟨Set.mem_Ici.mpr (le_of_lt hp.1), hp.2⟩)
    refine ContinuousOn.congr (hFstar.add hgs) ?_
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    show Work.Construction.Fstar (pExp a) z θ + g z θ τ
        = Work.Construction.Fstar (pExp a) z θ + Work.FTS.RegPkgGal.extG G z θ τ
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ, hG z θ τ hz hθ hτ]
  · -- continuity of `D_zF` on the closed angular strip
    have hGam : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Gam (pExp a) p.2)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (Gam_continuousOn (pExp a) hαpos Set.univ).comp continuousOn_snd (fun p _ => trivial)
    have hd : ContinuousOn (fun p : ℝ × ℝ => deriv Work.FM.Fstar p.1)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      continuousOn_deriv_FM_Fstar.comp continuousOn_fst (fun p hp => hp.1)
    have h1 : ContinuousOn (fun p : ℝ × ℝ => pExp a
          * (Work.Spaces.Gam (pExp a) p.2 / Work.Spaces.c (pExp a))
          * deriv Work.FM.Fstar p.1) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (continuousOn_const.mul (hGam.div_const _)).mul hd
    have h2 : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) p.1 p.2)
        (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
      (Work.FTS.PressureOn.continuousOn_uncurry_gSlice ha hJetpz hτS).mono
        (fun p hp => ⟨Set.mem_Ici.mpr (le_of_lt hp.1), hp.2⟩)
    refine ContinuousOn.congr (continuousOn_fst.mul (h1.add h2)) ?_
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    show Work.Spaces.Dz (Work.Construction.Ftau (pExp a) g τ) z θ
        = z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
            * deriv Work.FM.Fstar z
          + Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ)
    rw [Work.Spaces.Dz, hDz_eq z θ hz hθ]
  · -- the pointwise bounds
    intro z θ hz hθ
    have hFst1 : |pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
        * Work.FM.Fstar z| ≤ 40 * pExp a := (Fstar_bounds hαpos hα1 hz hθ).1
    have hFst2 : |z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
        * deriv Work.FM.Fstar z)| ≤ 40 * pExp a := (Fstar_bounds hαpos hα1 hz hθ).2
    have hgz : |g z θ τ| ≤ Ng := by
      rw [← hG z θ τ hz hθ hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
      exact hJet.abs_le (le_of_lt hz) hθ hτS
    have hgpz : |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ| ≤ Npz :=
      hJetpz.abs_le (le_of_lt hz) hθ hτS
    refine ⟨?_, ?_⟩
    · show |Work.Construction.Fstar (pExp a) z θ + g z θ τ| ≤ Mf
      calc |Work.Construction.Fstar (pExp a) z θ + g z θ τ|
          ≤ |Work.Construction.Fstar (pExp a) z θ| + |g z θ τ| := abs_add_le _ _
        _ ≤ 40 * pExp a + Ng := add_le_add hFst1 hgz
        _ ≤ Mf := by rw [hMfdef]; nlinarith [hαpos.le, hLpos.le, hNpz0]
    · by_cases hzL : z ≤ L
      · rw [Work.Spaces.Dz, hDz_eq z θ hz hθ]
        have h2 : |z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ|
            ≤ L * Npz := by
          rw [abs_mul, abs_of_pos hz]
          exact mul_le_mul hzL hgpz (abs_nonneg _) hLpos.le
        rw [show z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
              * deriv Work.FM.Fstar z
            + Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ)
            = z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
                * deriv Work.FM.Fstar z)
              + z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ
            from by ring]
        calc |z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
                * deriv Work.FM.Fstar z)
              + z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ|
            ≤ |z * (pExp a * (Work.Spaces.Gam (pExp a) θ / Work.Spaces.c (pExp a))
                * deriv Work.FM.Fstar z)|
              + |z * Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG G z θ τ) z θ| :=
              abs_add_le _ _
          _ ≤ 40 * pExp a + L * Npz := add_le_add hFst2 h2
          _ ≤ Mf := by rw [hMfdef]; nlinarith [hαpos.le, hNg0]
      · rw [hDz_zero z θ (not_le.mp hzL) hθ, abs_zero]
        rw [hMfdef]; nlinarith [hαpos.le, hNg0, hLpos.le, hNpz0]
  · -- vanishing on the angular boundary
    intro z hz
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by positivity⟩
    have hpi : (Real.pi / 2) ∈ Work.Spaces.Iθ := ⟨by positivity, le_rfl⟩
    obtain ⟨hv0, hv1⟩ := hreg'.hvt τ hτS
    have hg0 : g z 0 τ = 0 := by
      rw [← hG z 0 τ hz h0 hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
      exact hv0 z
    have hgpi : g z (Real.pi / 2) τ = 0 := by
      rw [← hG z (Real.pi / 2) τ hz hpi hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
      exact hv1 z
    refine ⟨?_, ?_⟩
    · show Work.Construction.Fstar (pExp a) z 0 + g z 0 τ = 0
      rw [hg0, add_zero]
      simp only [Work.Construction.Fstar, Work.Spaces.Gam_zero_left (pExp a) (ne_of_gt hαpos),
        zero_div, mul_zero, zero_mul]
    · show Work.Construction.Fstar (pExp a) z (Real.pi / 2) + g z (Real.pi / 2) τ = 0
      rw [hgpi, add_zero]
      simp only [Work.Construction.Fstar, Work.Spaces.Gam_zero_right (pExp a) (ne_of_gt hαpos),
        zero_div, mul_zero, zero_mul]
  · -- compact support
    refine ⟨hLpos, ?_⟩
    intro z θ hLz hθ
    have hz : 0 < z := lt_of_lt_of_le hLpos hLz
    have h := hLsupp τ hτS z θ hLz
    simp only [Work.FTS.Regularity.profFull_apply] at h
    show Work.Construction.Ftau (pExp a) g τ z θ = 0
    rw [Work.Construction.Ftau,
      ← hG z θ τ hz hθ hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
    exact h

end Work.FTS_StreamBdry.Inputs
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.abs_deriv_le_of_lipschitzOn_Ioc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `abs_deriv_le_of_lipschitzOn_Ioc`

If `f : ℝ → ℝ` is `C`-Lipschitz on the half-open interval `Ioc 0 1 = (0,1]`, then
`|deriv f z| ≤ C` at every point `z ∈ (0,1]`.

For `z < 1` this is the usual "Lipschitz on a neighbourhood of `x` bounds the derivative at `x`"
(`norm_deriv_le_of_lipschitzOn`, since `Ioc 0 1` is a neighbourhood of `z`).  The right endpoint
`z = 1` needs care: there `Ioc 0 1` is *not* a neighbourhood of `1`, the Lipschitz bound only
controls `f` to the left of `1`.  But `deriv f 1`, when it exists, is also the limit of the
one-sided slopes `slope f 1 t` for `t → 1⁻`, and those are bounded by `C` because both `t` and `1`
lie in `Ioc 0 1`.  (If `f` is not differentiable at `1` then `deriv f 1 = 0` by convention.)
-/

namespace Work.FTS_StreamBdry.SB4

open Set Filter
open scoped Topology

/-- The left-hand slope of `f` at the right endpoint `1` is bounded by `C` on `(0,1)`,
because both `t` and `1` lie in `Ioc 0 1`. -/
theorem norm_slope_one_le {f : ℝ → ℝ} {C : NNReal}
    (hlip : LipschitzOnWith C f (Set.Ioc 0 1)) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ‖slope f 1 t‖ ≤ (C : ℝ) := by
  have hb : ‖f t - f 1‖ ≤ (C : ℝ) * ‖t - 1‖ :=
    hlip.norm_sub_le ⟨ht.1, le_of_lt ht.2⟩ ⟨zero_lt_one, le_rfl⟩
  have hnorm : ‖slope f 1 t‖ = ‖t - 1‖⁻¹ * ‖f t - f 1‖ := by
    rw [slope_def_module, norm_smul, norm_inv]
  rw [hnorm]
  calc ‖t - 1‖⁻¹ * ‖f t - f 1‖
      ≤ ‖t - 1‖⁻¹ * ((C : ℝ) * ‖t - 1‖) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
    _ = (C : ℝ) * (‖t - 1‖⁻¹ * ‖t - 1‖) := by ring
    _ ≤ (C : ℝ) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ C.coe_nonneg
        have hp : 0 < ‖t - 1‖ := by
          rw [Real.norm_eq_abs]; exact abs_pos.mpr (by linarith [ht.2])
        exact le_of_eq (inv_mul_cancel₀ (ne_of_gt hp))
    _ = (C : ℝ) := mul_one _

/-- At the right endpoint `1`, the derivative of a function which is `C`-Lipschitz on `Ioc 0 1`
is bounded by `C`: the bound comes from the slopes on the left. -/
theorem abs_deriv_one_le {f : ℝ → ℝ} {C : NNReal}
    (hlip : LipschitzOnWith C f (Set.Ioc 0 1)) :
    |deriv f 1| ≤ (C : ℝ) := by
  -- `(0,1)` is eventually in the left-neighbourhood filter of `1`
  have hmem : Set.Ioo 0 1 ∈ 𝓝[Set.Iio 1] (1 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioo 0 2, Ioo_mem_nhds (by norm_num) (by norm_num),
      fun x hx => ⟨hx.1.1, hx.2⟩⟩
  have hev : ∀ᶠ t in 𝓝[Set.Iio 1] (1 : ℝ), ‖slope f 1 t‖ ≤ (C : ℝ) := by
    filter_upwards [hmem] with t ht
    exact norm_slope_one_le hlip ht
  by_cases hd : DifferentiableAt ℝ f 1
  · have hT : Tendsto (slope f 1) (𝓝[Set.Iio 1] (1 : ℝ)) (𝓝 (deriv f 1)) :=
      (hd.hasDerivAt.tendsto_slope).mono_left (nhdsWithin_mono 1 (fun x hx => ne_of_lt hx))
    have h2 : ‖deriv f 1‖ ≤ (C : ℝ) := le_of_tendsto hT.norm hev
    rwa [Real.norm_eq_abs] at h2
  · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
    exact C.coe_nonneg

theorem abs_deriv_le_of_lipschitzOn_Ioc {f : ℝ → ℝ} {C : NNReal}
    (hlip : LipschitzOnWith C f (Set.Ioc 0 1)) :
    ∀ z ∈ Set.Ioc 0 1, |deriv f z| ≤ (C : ℝ) := by
  intro z hz
  rcases lt_or_eq_of_le hz.2 with hzlt | hzeq
  · -- `z < 1`: `Ioc 0 1` is a neighbourhood of `z`
    have hmem : Set.Ioc 0 1 ∈ 𝓝 z :=
      mem_of_superset (Ioo_mem_nhds hz.1 hzlt) fun x hx => ⟨hx.1, le_of_lt hx.2⟩
    have h1 : ‖deriv f z‖ ≤ (C : ℝ) := norm_deriv_le_of_lipschitzOn hmem hlip
    rwa [Real.norm_eq_abs] at h1
  · -- `z = 1`: one-sided slope argument
    subst hzeq
    exact abs_deriv_one_le hlip

end Work.FTS_StreamBdry.SB4
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.l12_zero_plainE`

The zero mode of `L₁₂` passes to the limit along the class-C approximants of
`Work.FTS.FinalV2.LimApprox` — the **plain-`E`** form of
`Work.FTS_RegExport.RXB.l12_zero_lim_proved`, whose assembly
`Work.FTS_RegExport.RXB.l12_zero_lim_of_bounds` is stated for a *linear* `E : Fn →ₗ[ℝ] Fn`.

Nothing in the assembly uses the linearity of `E`: `E` occurs in `LimApprox` only as a plain
function (in the `muDyn`-convergence clause, which the argument never reads) and the proof only
consumes the class-C approximants `gn`, their uniform `ℋ⁴`-bound and their jet convergence.
We therefore repeat the assembly verbatim for `E : Fn → Fn`, fed with the two analytic inputs of
the directory:

* `sup_bound_all_alpha` — the interior `L^∞`–`ℋ⁴` trade-off `f² ≤ C|f|²_{ℋ⁴}` (`SupBnd`);
* `l12dens_weighted_bound` — the weighted density bound `|L₁₂dens f s| ≤ C(√s/(1+s)²)|f|_{ℋ⁴}`
  (`DensBnd`), which turns the uniform `ℋ⁴`-bound of the approximants into an `L¹(ds)` majorant.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_StreamBdry.SB4

set_option autoImplicit false

/-- **`RX-B`, plain-`E` form**: the assembly of
`Work.FTS_RegExport.RXB.l12_zero_lim_of_bounds` with an arbitrary (not necessarily linear) `E`.

Given the two analytic inputs `SupBnd` (interior `L^∞`–`ℋ⁴` bound) and `DensBnd` (weighted bound
on the zero mode) at every `α > 0`, every `τ ≥ 0` has `L₁₂(slice g τ)(0) = 0` for a family `g`
which is the pointwise limit of class-C approximants with a uniform `ℋ⁴`-bound (`LimApprox`). -/
theorem l12_zero_lim_of_bounds_plainE {αG C₀ : ℝ} (hα : 0 < αG)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsupAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ Work.FTS_RegExport.RXB.SupBnd α C)
    (hdenAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ Work.FTS_RegExport.RXB.DensBnd α C)
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 := by
  intro τ hτ
  obtain ⟨Csup, hCsup, hsup⟩ := hsupAll αG hα
  obtain ⟨Cden, hCden, hden⟩ := hdenAll αG hα
  obtain ⟨gn, B, L, hcls, hlip, hjet, hmu⟩ := hA (max τ 1 + 1) (by
    have := le_max_right τ 1
    linarith)
  have hτT : τ ∈ Set.Icc (0:ℝ) (max τ 1 + 1) := by
    refine ⟨hτ, ?_⟩
    have := le_max_left τ 1
    linarith
  -- the class data of the approximants
  have hclass : ∀ n, Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) :=
    fun n => (hcls n τ hτT).1
  have hN : ∀ n, Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
    fun n => (hcls n τ hτT).2.1
  have hΛ : 0 ≤ C₀ * αG ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg αG 4 _) (hN 0)
  have hcls' : ∀ n, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := fun n =>
    ⟨(hclass n).reg,
     Work.FTS.OpenPkg.HkMem_mono_open (hclass n).reg 4 (by norm_num) (hclass n).mem,
     Work.FTS.ClassC.bdryTraces_mono (by norm_num) (hclass n).tr⟩
  have hjet' : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 →
      Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ s θ) atTop
        (𝓝 (Work.FTS.Galerkin.slice g τ s θ)) := by
    intro s θ hs hθ hθ'
    have h := hjet τ hτT 0 0 (by norm_num) s θ ⟨hs, hθ, hθ'⟩
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero,
      Work.Spaces.DzIter_zero] using h
  have hzero : ∀ n, Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0 = 0 :=
    fun n => (hclass n).l12_zero
  -- the `L¹(ds)` majorant
  set M : ℝ → ℝ := fun s => Cden * (Real.sqrt s / (1 + s) ^ 2) * (C₀ * αG ^ 2) with hMdef
  have hMint : MeasureTheory.IntegrableOn M (Set.Ioi 0) := by
    have h : MeasureTheory.IntegrableOn
        (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) (Set.Ioi 0) :=
      Work.FTS_RegExport.RXB.integrableOn_sqrt_div_sq.const_mul (Cden * (C₀ * αG ^ 2))
    have hfun : (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) = M := by
      funext s
      simp only [hMdef]
      ring
    rwa [hfun] at h
  -- the dominated convergence theorem in the radial variable
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable (fun z hz => ?_) measurableSet_Ioi
    exact (Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk
      (hcls' n).1 (hcls' n).2.1 hz).continuousWithinAt
  have hconv : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
        atTop (𝓝 (Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) s)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs =>
      Work.FTS_RegExport.RXB.tendsto_L12dens_of_sup_bound hΛ hCsup hsup hcls' hN hjet' hs)
  have hbdd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), ∀ n,
      ‖Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s‖ ≤ M s := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs n => ?_)
    have h1 : |Work.Construction.L12dens (Work.FTS.Galerkin.slice (gn n) τ) s|
        ≤ Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      hden _ (hcls' n).1 (hcls' n).2.1 (hcls' n).2.2 s hs
    have h2 : Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ M s := by
      rw [hMdef]
      exact mul_le_mul_of_nonneg_left (hN n)
        (by positivity)
    rw [Real.norm_eq_abs]
    exact le_trans h1 h2
  have hlim := Work.FTS.StrongEps.L12_tendsto_of_dominated
    (f := fun n => Work.FTS.Galerkin.slice (gn n) τ) (g := Work.FTS.Galerkin.slice g τ)
    (M := M) (ρ := 0) hmeas hconv hbdd hMint
  have h0 : Tendsto (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
      atTop (𝓝 (0:ℝ)) := by
    have hfun : (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
        = fun _ => (0:ℝ) := funext hzero
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

theorem l12_zero_plainE {αG C₀ : ℝ} (hα : 0 < αG)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 :=
  l12_zero_lim_of_bounds_plainE hα
    (fun α hα => Work.FTS_RegExport.RXB.sup_bound_all_alpha hα)
    (fun α hα => Work.FTS_RegExport.RXB.l12dens_weighted_bound hα)
    hA

end Work.FTS_StreamBdry.SB4
end
end
