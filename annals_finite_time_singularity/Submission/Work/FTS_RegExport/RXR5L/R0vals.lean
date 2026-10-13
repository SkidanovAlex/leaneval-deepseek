/-
# `Work.FTS_RegExport.RXR5L.R0vals` — the three boundary values of the right-hand side

`R0vals` are the three "`R0`" clauses of `Work.FTS.RegPkgGal.R5Parts` (the primitive-level
version of the R5 regularity slot): the right-hand side
`dynLin + dynRHS` of the fake-time equation *vanishes* on the three degenerate boundary strata
of the domain `Iz × Iθ`:

* `z = 0`  (the plane `z = 0`), for every `θ ∈ Iθ`,
* `θ = 0`  (the axis `r = 0`), for every `z`,
* `θ = π/2` (the axis `r = 0` of the meridian half-plane), for every `z`.

They are needed because `Sol` only gives the equation on the *open* quadrant
`Qd = (0,∞) × (0,π/2)`, while the consumers (`Der.R5Slot_of_parts`, `RXR1.rhs_c1`) need the
closed-quadrant boundary values.

## Why they are true

At the three strata the sanitiser `gS` and the stream function `psiR` are *exactly* zero (at
`θ = 0`, `θ = π/2` because of the `RegPkgMin.vanish` clause of `DynOK'` and the definition of
`gS`; at `z = 0` by `gS`'s `z ≤ 0` branch and `psiR`'s `z ≤ 0` branch), and the angular data
`Γ(0) = Γ(π/2) = 0`, `sin(2·0) = sin(2·(π/2)) = 0` kill every remaining term:

* `𝓛_Γ^T(f) z 0 = 0` for every `z` when the slice `f(·,0)` vanishes (`Γ(0) = 0` kills the
  `L₁₂`-terms, `sin 0 = 0` kills the transport term, and `f ≡ 0` on the line kills `𝓛`),
  and the same at `θ = π/2` and at `z = 0` (where the `z`-factors of `D_z`, of the `L₁₂`
  correction of `𝓛_Γ` and of the projector `𝕡` vanish);
* `gRHS = -μ̄·AK + N₀ + N + N_*` vanishes because each term carries one of the vanishing
  factors `Γ(0)`/`Γ(π/2)` (through `AK`, `F_*`, `D_z F_*`), `sin(2θ)` (through the `s2`-terms
  and `D_θ`), `F = F_* + g` (the full profile on the stratum), `D_zF`, or one of the slices of
  `g` themselves.  The single non-obvious one is the `Uop · ∂_θF` term of `N`: at `θ = 0` (and
  `θ = π/2`) it vanishes either through `∂_θF` (when the whole slice `F(·,0)` vanishes) or,
  in the general case, through `𝕌(Φ̃) z 0 = -3Φ̃(z,0) - α z ∂_zΦ̃(z,0) = 0`, `Φ̃(·,0)` being
  identically zero by `psiR_zero` (and `Theta(·,0) = 0`, `sin(2·0) = 0`).

## Layout

§1 elementary vanishings, §2 the `L₁₂`-free statement `LGammaT = 0` on the three strata,
§3 the vanishing of `gRHS` on the three strata, §4 the assembly.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF

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
