import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_EllLimOK.FatouG
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.starUop
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.THL.L.DzDthG_tau_mod
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.factor_bound
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWPLim.Gap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsWPLim

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The jump of the coefficient `μ + λ + μλ` at `μ = -1` -/




/-! ## The missing step is false -/


/-! ## `lamfun` is continuous off `-1`: the two natural repairs of the statement -/




end Work.FTS.StrongEps.EpsWPLim
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.UniqG.smallUniq3G_fts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.UniqG

theorem smallUniq3G_fts : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ →
    ∀ (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (fn : ℕ → Work.FTS.Galerkin.Fn)
      (f : Work.FTS.Galerkin.Fn), Work.FTS_EllLimOK.LimSeq4 α fn f →
    ∀ Ψ Ψ' : Work.FTS.Galerkin.Fn,
      Work.FTS_EllLimOK.IsJetLimit3G α E fn f Ψ →
      Work.FTS_EllLimOK.IsJetLimit3G α E fn f Ψ' →
      ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.mixed j i Ψ z θ = Work.Spaces.mixed j i Ψ' z θ := by
  -- The open quadrant is an open set.
  have hQd : IsOpen Work.Construction.Qd := by
    rw [Work.Construction.Qd]
    exact isOpen_Ioi.prod isOpen_Ioo
  refine ⟨1, one_pos, fun α hα _ E fn f _ Ψ Ψ' hΨ hΨ' j i _ z θ hzθ => ?_⟩
  -- Both limits carry the Fatou package; in particular they solve the same elliptic law.
  have hFΨ : Work.FTS_EllLimOK.FatouPkgG α f Ψ := hΨ.1
  have hFΨ' : Work.FTS_EllLimOK.FatouPkgG α f Ψ' := hΨ'.1
  -- Their difference is in `ℋ⁰` (level `0` memberships + closed-box regularity).
  have hδ : Work.Spaces.HkMem α 0 (Work.FTS_EllLimOK.diff Ψ Ψ') :=
    Work.FTS_EllLimOK.HkMem_zero_diff hFΨ.mem hFΨ'.mem hFΨ.box hFΨ'.box
  -- Hence the uniqueness of the homogeneous elliptic problem gives pointwise equality on `Qd`.
  have heq : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Ψ z θ = Ψ' z θ :=
    Work.FTS_EllLimOK.eqOn_of_same_law hα hFΨ.sol hFΨ'.sol hFΨ.box hFΨ'.box
      hFΨ.mem hFΨ.memCos hFΨ'.mem hFΨ'.memCos hδ
  -- `mixed` is local, so equality on the open quadrant implies equality of the jets there.
  exact Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen hQd
    (fun p hp => heq p.1 p.2 hp) hzθ j i

end Work.FTS_EllLimOK.UniqG
end
-- ===== merged: Submission.Work.FTS_MuLipC.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_MuLipC

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-- **The class-`C` Lipschitz bound of the modulation, at the profile exponent
`pExp α = 3α`** — the frozen producer `Work.FTS.FinalV2.muLipC_pExp` (conjunct (1c) of the
final interface `Inputs'`, `FinalV2/Producers.lean`).

The threshold is `α₂ = min (1/4) (1/(4 + 12·C₀))`, which makes both `pExp α ≤ 1` and
`C₀·(pExp α)² ≤ 1` hold. -/
theorem muLipC_pExp {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn →ₗ[ℝ] Fn},
      Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs →
      (∀ f : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) f →
        Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp α) Ce f (E f)) →
      Work.FTS.FinalV2.MuLipC (Work.FTS.Regularity.pExp α) C₀ Φs E := by
  refine ⟨min (1 / 4) (1 / (4 + 12 * C₀)), lt_min (by norm_num) (by positivity), ?_⟩
  intro α hα Φs E hstar hell
  have hα0 : 0 < α := hα.1
  have hαb : α ≤ 1 / (4 + 12 * C₀) := le_trans hα.2 (min_le_right _ _)
  have hαq : α ≤ 1 / 4 := by
    have := le_trans hα.2 (min_le_left (1 / 4 : ℝ) (1 / (4 + 12 * C₀)))
    linarith
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα0
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := by
    rw [Work.FTS.Regularity.pExp_eq]; linarith
  have hsmall : C₀ * (Work.FTS.Regularity.pExp α) ^ 2 ≤ 1 := by
    have hden : (0 : ℝ) < 4 + 12 * C₀ := by positivity
    have hmul : α * (4 + 12 * C₀) ≤ 1 := by
      rw [le_div_iff₀ hden] at hαb
      linarith
    have hCα : C₀ * α ≤ 1 / 12 := by nlinarith
    have hstep : C₀ * α ^ 2 ≤ (1 / 12) * (1 / 4) := by
      calc C₀ * α ^ 2 = α * (C₀ * α) := by ring
        _ ≤ (1 / 4) * (1 / 12) := mul_le_mul hαq hCα (by positivity) (by norm_num)
        _ = (1 / 12) * (1 / 4) := by ring
    rw [Work.FTS.Regularity.pExp_eq]
    have h3 : C₀ * (3 * α) ^ 2 = 9 * (C₀ * α ^ 2) := by ring
    rw [h3]
    linarith
  have hEadd : ∀ a b : Fn, (⇑E) (a - b) = (⇑E) a - (⇑E) b := fun a b => E.map_sub a b
  have hEsmul : ∀ (c : ℝ) (a : Fn), (⇑E) (c • a) = c • (⇑E) a := fun c a => E.map_smul c a
  exact muLipC_of_diffRows hp0
    (Work.FTS_MuLipC.RowN0.diffRow0 hp0 hp1 hsmall)
    (Work.FTS_MuLipC.RowN.diffRow1 hp0 hp1 hsmall hEadd hEsmul hstar hell)
    (Work.FTS_MuLipC.RowT.diffRow2 hp0 hp1)

end Work.FTS_MuLipC
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.L.DzDthG_bound_zderiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `THL.L.DzDthG_bound_zderiv` — B3 of the O1 plan (`cbc/fts_thlip_o1_plans.md`)

The two families of the O1 restatement,

  `DzG α g z θ τ = D_z g̃(z,θ,τ)`,   `DthG α g z θ τ = D_θ g̃(z,θ,τ)`,
  `g̃ = gS α (tauExt g)`  (`FinalV2.gS`, `FinalV2.tauExt`),

satisfy, uniformly for `τ ∈ [0,S]` and `θ ∈ Iθ`:

* `|DzG| ≤ K` and `|DthG| ≤ K` for all `z ≥ 0`;
* both are continuous at `z = 0`;
* both are differentiable in `z` on `z > 0`, with derivative bounded by `K`.

The constant is `K`, the constant of the `Γ`-weighted system `WSys α S K g`, which bounds the six
slots `(j,i) ∈ {(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)}` by `K·ω`, `ω α z θ = z²Γ(θ)/(1+z)²`.

The content:

* `ω ≤ Γ ≤ 1` and `ω/z ≤ Γ ≤ 1`, so the slots `(1,0)`, `(0,1)` give `|DzG|, |DthG| ≤ K` while
  `(2,0)`, `(1,1)` give `|∂_zDzG|, |∂_zDthG| ≤ K`;
* `ω ≤ z²Γ ≤ z²` gives `|DzG z|, |DthG z| ≤ K z²`, hence continuity at `0`; the angular
  endpoints `θ = 0, π/2` and the half-line `z ≤ 0` are handled by the *exact* vanishing of the
  slices there;
* on the open quadrant `∂_z(D_z g̃) = D_z²g̃/z` and `∂_z(D_θ g̃) = D_zD_θg̃/z`, which is
  `Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z` at `(j,i) = (1,0)` resp. `(0,1)`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.THL.L

set_option autoImplicit false

variable {α : ℝ} {g : Work.FTS.Galerkin.Fam}

/-! ## §1 Agreement of `g̃` with the slices of `g` -/

/-- `gS α (tauExt g)` agrees with the `τ`-slice of `g` on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`. -/
theorem gS_eq_slice {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : 0 ≤ τ) :
    Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ = g z θ τ := by
  simp only [Work.FTS.FinalV2.gS, hz, hθ.1, hθ.2, and_self, ↓reduceIte,
    Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- `DzG α g z θ τ` on the open region, written with the slice of `g`. -/
theorem DzG_eq_mixed {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.THL.DzG α g z θ τ
      = Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ := by
  rw [show Work.FTS_RegExport.THL.DzG α g z θ τ
        = z * deriv (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' θ τ) z
      from rfl,
    show Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ
        = z * deriv (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z from rfl]
  congr 1
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have hz'pos : 0 < z' := hz'
    simp only [Work.FTS.FinalV2.gS, hz'pos, hθ.1, hθ.2, and_self, ↓reduceIte,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ, Work.FTS.Galerkin.slice])

/-- `DthG α g z θ τ` at interior angles, written with the slice of `g`. -/
theorem DthG_eq_mixed {z θ τ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.THL.DthG α g z θ τ
      = Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ := by
  rw [show Work.FTS_RegExport.THL.DthG α g z θ τ
        = Real.sin (2 * θ)
          * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) θ
      from rfl,
    show Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ
        = Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ from rfl]
  congr 1
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    have h1 : 0 ≤ θ' := le_of_lt (show 0 < θ' from hθ'.1)
    have h2 : θ' ≤ π / 2 := le_of_lt (show θ' < π / 2 from hθ'.2)
    simp only [Work.FTS.FinalV2.gS, hz, h1, h2, and_self, ↓reduceIte,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ, Work.FTS.Galerkin.slice])

/-! ## §2 Exact vanishing on the boundary of the region -/

/-- The radial slice of `g̃` vanishes identically at `θ = 0`, for `τ ≥ 0`. -/
theorem gS_slice_eq_zero_left (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    {τ : ℝ} (hτ : 0 ≤ τ) : ∀ z : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z 0 τ = 0 := by
  intro z
  by_cases hz : 0 < z
  · rw [gS_eq_slice hz ⟨le_rfl, by linarith [Real.pi_pos]⟩ hτ]
    exact (hmin.vanish τ hτ z hz.le).1
  · simp only [Work.FTS.FinalV2.gS, if_neg hz]

/-- The radial slice of `g̃` vanishes identically at `θ = π/2`, for `τ ≥ 0`. -/
theorem gS_slice_eq_zero_right (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ z : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z (π / 2) τ = 0 := by
  intro z
  by_cases hz : 0 < z
  · rw [gS_eq_slice hz ⟨by linarith [Real.pi_pos], le_rfl⟩ hτ]
    exact (hmin.vanish τ hτ z hz.le).2
  · simp only [Work.FTS.FinalV2.gS, if_neg hz]

/-- `DzG` vanishes wherever the radial slice of `g̃` does. -/
theorem DzG_eq_zero_of_slice_eq_zero {θ τ : ℝ}
    (h : ∀ z : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ = 0) (z : ℝ) :
    Work.FTS_RegExport.THL.DzG α g z θ τ = 0 := by
  rw [show Work.FTS_RegExport.THL.DzG α g z θ τ
        = z * deriv (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' θ τ) z
      from rfl]
  have hfun : (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' θ τ)
      = fun _ => (0 : ℝ) := funext h
  rw [hfun, deriv_const, mul_zero]

/-- `DzG α g z θ τ = 0` for `z ≤ 0` (the family vanishes on the closed left half-plane). -/
theorem DzG_eq_zero_of_nonpos {θ τ : ℝ} {z : ℝ} (h : z ≤ 0) :
    Work.FTS_RegExport.THL.DzG α g z θ τ = 0 := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [show Work.FTS_RegExport.THL.DzG α g z θ τ
          = z * deriv (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' θ τ) z
        from rfl]
    have hfun : (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' θ τ)
        =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds (show z ∈ Set.Iio (0 : ℝ) from hlt)] with z' hz'
      have hz'le : z' ≤ 0 := le_of_lt hz'
      simp only [Work.FTS.FinalV2.gS, if_neg (not_lt.mpr hz'le)]
    rw [hfun.deriv_eq, deriv_const, mul_zero]
  · subst heq
    rw [show Work.FTS_RegExport.THL.DzG α g 0 θ τ
          = 0 * deriv (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' θ τ) 0
        from rfl, zero_mul]

/-- `DzG α g 0 θ τ = 0`. -/
theorem DzG_at_zero (θ τ : ℝ) : Work.FTS_RegExport.THL.DzG α g 0 θ τ = 0 :=
  DzG_eq_zero_of_nonpos le_rfl

/-- `DthG α g z θ τ = 0` for `z ≤ 0` (the angular slice of `g̃` is identically `0` there). -/
theorem DthG_eq_zero_of_nonpos {θ τ : ℝ} {z : ℝ} (h : z ≤ 0) :
    Work.FTS_RegExport.THL.DthG α g z θ τ = 0 := by
  rw [show Work.FTS_RegExport.THL.DthG α g z θ τ
        = Real.sin (2 * θ)
          * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) θ
      from rfl]
  have hfun : (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ)
      = fun _ => (0 : ℝ) := funext (fun θ' => by
        simp only [Work.FTS.FinalV2.gS, if_neg (not_lt.mpr h)])
  rw [hfun, deriv_const, mul_zero]

/-- `DthG α g z 0 τ = 0` (the angular weight `sin 2θ` vanishes). -/
theorem DthG_at_theta_zero (z τ : ℝ) : Work.FTS_RegExport.THL.DthG α g z 0 τ = 0 := by
  rw [show Work.FTS_RegExport.THL.DthG α g z 0 τ
        = Real.sin (2 * 0)
          * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) 0
      from rfl, show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero, zero_mul]

/-- `DthG α g z (π/2) τ = 0` (the angular weight `sin 2θ` vanishes). -/
theorem DthG_at_theta_pi (z τ : ℝ) : Work.FTS_RegExport.THL.DthG α g z (π / 2) τ = 0 := by
  rw [show Work.FTS_RegExport.THL.DthG α g z (π / 2) τ
        = Real.sin (2 * (π / 2))
          * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) (π / 2)
      from rfl, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-! ## §3 The main statement -/

theorem DzDthG_bound_zderiv {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S) (hK0 : 0 ≤ K)
    (hw : Work.FTS_RegExport.THL.WSys α S K g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → |Work.FTS_RegExport.THL.DzG α g z θ τ| ≤ N ∧
        |Work.FTS_RegExport.THL.DthG α g z θ τ| ≤ N) ∧
      ContinuousAt (fun z' => Work.FTS_RegExport.THL.DzG α g z' θ τ) 0 ∧
      ContinuousAt (fun z' => Work.FTS_RegExport.THL.DthG α g z' θ τ) 0 ∧
      ∀ z ∈ Set.Ioi (0:ℝ),
        (∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.THL.DzG α g z' θ τ) d z ∧ |d| ≤ N) ∧
        (∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.THL.DthG α g z' θ τ) d z ∧ |d| ≤ N) := by
  refine ⟨K, hK0, ?_⟩
  intro τ hτ θ hθ
  have hτ0 : 0 ≤ τ := hτ.1
  have hΓ1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
    Work.ConstructionInstance.Gamma_le_one hα.le hθ
  have hslice0 : ∀ z : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z 0 τ = 0 :=
    gS_slice_eq_zero_left hmin hτ0
  have hsliceπ : ∀ z : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z (π / 2) τ = 0 :=
    gS_slice_eq_zero_right hmin hτ0
  -- the weighted bound `K·ω` for both families, at every `z > 0` and every `θ ∈ Iθ`
  have hωDz : ∀ z : ℝ, 0 < z →
      |Work.FTS_RegExport.THL.DzG α g z θ τ| ≤ K * Work.FTS.RegExportIface.ω α z θ := by
    intro z hzpos
    rcases eq_or_lt_of_le hθ.1 with h0 | hθ0
    · rw [← h0, DzG_eq_zero_of_slice_eq_zero hslice0 z, abs_zero]
      exact mul_nonneg hK0
        (Work.FTS_RegExport.RXT.omega_nonneg_of α z 0 hzpos.le
          ⟨le_rfl, by linarith [Real.pi_pos]⟩)
    · rcases eq_or_lt_of_le hθ.2 with hπ | hθ1
      · rw [hπ, DzG_eq_zero_of_slice_eq_zero hsliceπ z, abs_zero]
        exact mul_nonneg hK0 (Work.FTS_RegExport.RXT.omega_nonneg_of α z (π / 2) hzpos.le
          ⟨by linarith [Real.pi_pos], le_rfl⟩)
      · rw [DzG_eq_mixed hzpos hθ hτ0]
        have h := hw (1 : Fin 6) τ hτ z θ hzpos hθ0 hθ1
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h
        exact h
  have hωDth : ∀ z : ℝ, 0 < z →
      |Work.FTS_RegExport.THL.DthG α g z θ τ| ≤ K * Work.FTS.RegExportIface.ω α z θ := by
    intro z hzpos
    rcases eq_or_lt_of_le hθ.1 with h0 | hθ0
    · rw [← h0, DthG_at_theta_zero z τ, abs_zero]
      exact mul_nonneg hK0
        (Work.FTS_RegExport.RXT.omega_nonneg_of α z 0 hzpos.le
          ⟨le_rfl, by linarith [Real.pi_pos]⟩)
    · rcases eq_or_lt_of_le hθ.2 with hπ | hθ1
      · rw [hπ, DthG_at_theta_pi z τ, abs_zero]
        exact mul_nonneg hK0 (Work.FTS_RegExport.RXT.omega_nonneg_of α z (π / 2) hzpos.le
          ⟨by linarith [Real.pi_pos], le_rfl⟩)
      · rw [DthG_eq_mixed hzpos ⟨hθ0, hθ1⟩ hτ0]
        have h := hw (2 : Fin 6) τ hτ z θ hzpos hθ0 hθ1
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h
        exact h
  -- the quadratic majorants `K z²`, for every real `z`
  have hquadDz : ∀ z : ℝ, ‖Work.FTS_RegExport.THL.DzG α g z θ τ‖ ≤ K * z ^ 2 := by
    intro z
    rcases lt_trichotomy z 0 with h | h | h
    · rw [DzG_eq_zero_of_nonpos h.le, norm_zero]
      exact mul_nonneg hK0 (sq_nonneg z)
    · subst h
      rw [DzG_at_zero θ τ, norm_zero]
      exact mul_nonneg hK0 (sq_nonneg 0)
    · rw [Real.norm_eq_abs]
      have h1 : |Work.FTS_RegExport.THL.DzG α g z θ τ|
          ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
        have hstep := mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.omega_le_zsq_mul_Gamma α z θ h.le hθ) hK0
        exact le_trans (hωDz z h) (by simpa only [mul_assoc] using hstep)
      have h2 : K * z ^ 2 * Work.FTS.Regularity.Gamma α θ ≤ K * z ^ 2 := by
        have hstep := mul_le_mul_of_nonneg_left hΓ1 (mul_nonneg hK0 (sq_nonneg z))
        simpa only [mul_one] using hstep
      exact le_trans h1 h2
  have hquadDth : ∀ z : ℝ, ‖Work.FTS_RegExport.THL.DthG α g z θ τ‖ ≤ K * z ^ 2 := by
    intro z
    by_cases h : 0 < z
    · rw [Real.norm_eq_abs]
      have h1 : |Work.FTS_RegExport.THL.DthG α g z θ τ|
          ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
        have hstep := mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.omega_le_zsq_mul_Gamma α z θ h.le hθ) hK0
        exact le_trans (hωDth z h) (by simpa only [mul_assoc] using hstep)
      have h2 : K * z ^ 2 * Work.FTS.Regularity.Gamma α θ ≤ K * z ^ 2 := by
        have hstep := mul_le_mul_of_nonneg_left hΓ1 (mul_nonneg hK0 (sq_nonneg z))
        simpa only [mul_one] using hstep
      exact le_trans h1 h2
    · rw [DthG_eq_zero_of_nonpos (not_lt.mp h), norm_zero]
      exact mul_nonneg hK0 (sq_nonneg z)
  -- the global bound by `K` on `z ≥ 0`
  have hval : ∀ z : ℝ, 0 ≤ z →
      |Work.FTS_RegExport.THL.DzG α g z θ τ| ≤ K ∧
        |Work.FTS_RegExport.THL.DthG α g z θ τ| ≤ K := by
    intro z hz
    rcases eq_or_lt_of_le hz with h | h
    · subst h
      exact ⟨by rw [DzG_at_zero θ τ, abs_zero]; exact hK0,
        by rw [DthG_eq_zero_of_nonpos le_rfl, abs_zero]; exact hK0⟩
    · have hΓ : K * Work.FTS.Regularity.Gamma α θ ≤ K := by
        simpa using mul_le_mul_of_nonneg_left hΓ1 hK0
      have hωGz := Work.FTS_RegExport.RXT.omega_le_Gamma α z θ h.le hθ
      exact ⟨le_trans (hωDz z h) (le_trans (mul_le_mul_of_nonneg_left hωGz hK0) hΓ),
        le_trans (hωDth z h) (le_trans (mul_le_mul_of_nonneg_left hωGz hK0) hΓ)⟩
  -- continuity at `z = 0`, by squeezing against `K z²`
  have htend : ∀ (F : ℝ → ℝ), (∀ z : ℝ, ‖F z‖ ≤ K * z ^ 2) → F 0 = 0 →
      Filter.Tendsto F (𝓝 0) (𝓝 0) := by
    intro F hF _
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero (fun z => norm_nonneg _) hF ?_
    have hc : ContinuousAt (fun z' : ℝ => K * z' ^ 2) 0 :=
      continuousAt_const.mul (continuousAt_id.pow 2)
    have hz : (fun z' : ℝ => K * z' ^ 2) 0 = 0 := by norm_num
    simpa only [ContinuousAt, hz] using hc
  have hcontDz : ContinuousAt (fun z' => Work.FTS_RegExport.THL.DzG α g z' θ τ) 0 := by
    have h0 : (fun z' => Work.FTS_RegExport.THL.DzG α g z' θ τ) 0 = 0 := DzG_at_zero θ τ
    simpa only [ContinuousAt, h0] using htend _ hquadDz h0
  have hcontDth : ContinuousAt (fun z' => Work.FTS_RegExport.THL.DthG α g z' θ τ) 0 := by
    have h0 : (fun z' => Work.FTS_RegExport.THL.DthG α g z' θ τ) 0 = 0 :=
      DthG_eq_zero_of_nonpos le_rfl
    simpa only [ContinuousAt, h0] using htend _ hquadDth h0
  -- the `z`-derivatives on the open half-line
  have hderivDz : ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.THL.DzG α g z' θ τ) d z ∧ |d| ≤ K := by
    intro z hz
    have hzpos : 0 < z := hz
    rcases eq_or_lt_of_le hθ.1 with h0 | hθ0
    · refine ⟨0, ?_, by rw [abs_zero]; exact hK0⟩
      rw [show (fun z' => Work.FTS_RegExport.THL.DzG α g z' θ τ) = fun _ => (0 : ℝ) from
        funext (fun z' => by rw [← h0]; exact DzG_eq_zero_of_slice_eq_zero hslice0 z')]
      exact hasDerivAt_const z 0
    · rcases eq_or_lt_of_le hθ.2 with hπ | hθ1
      · refine ⟨0, ?_, by rw [abs_zero]; exact hK0⟩
        rw [show (fun z' => Work.FTS_RegExport.THL.DzG α g z' θ τ) = fun _ => (0 : ℝ) from
          funext (fun z' => by rw [hπ]; exact DzG_eq_zero_of_slice_eq_zero hsliceπ z')]
        exact hasDerivAt_const z 0
      · have hmix := hw (3 : Fin 6) τ hτ z θ hzpos hθ0 hθ1
        norm_num [Work.FTS.RegExportIface.RXT.idx] at hmix
        refine ⟨Work.Spaces.mixed 2 0 (Work.FTS.Galerkin.slice g τ) z θ / z, ?_, ?_⟩
        · refine (Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z (f := Work.FTS.Galerkin.slice g τ)
            (hmin.c4 τ hτ0) 1 0 (by norm_num) hzpos hθ0 hθ1).congr_of_eventuallyEq ?_
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
          exact DzG_eq_mixed hz' hθ hτ0
        · have hΓ : K * Work.FTS.Regularity.Gamma α θ ≤ K := by
            simpa using mul_le_mul_of_nonneg_left hΓ1 hK0
          calc |Work.Spaces.mixed 2 0 (Work.FTS.Galerkin.slice g τ) z θ / z|
              = |Work.Spaces.mixed 2 0 (Work.FTS.Galerkin.slice g τ) z θ| / z := by
                rw [abs_div, abs_of_pos hzpos]
            _ ≤ K * Work.FTS.RegExportIface.ω α z θ / z :=
                div_le_div_of_nonneg_right hmix hzpos.le
            _ = K * (Work.FTS.RegExportIface.ω α z θ / z) := by ring
            _ ≤ K * Work.FTS.Regularity.Gamma α θ :=
                mul_le_mul_of_nonneg_left
                  (Work.FTS_RegExport.RXT.omega_div_z_le_Gamma α z θ hzpos.le hθ) hK0
            _ ≤ K := hΓ
  have hderivDth : ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.THL.DthG α g z' θ τ) d z ∧ |d| ≤ K := by
    intro z hz
    have hzpos : 0 < z := hz
    rcases eq_or_lt_of_le hθ.1 with h0 | hθ0
    · refine ⟨0, ?_, by rw [abs_zero]; exact hK0⟩
      rw [show (fun z' => Work.FTS_RegExport.THL.DthG α g z' θ τ) = fun _ => (0 : ℝ) from
        funext (fun z' => by rw [← h0]; exact DthG_at_theta_zero z' τ)]
      exact hasDerivAt_const z 0
    · rcases eq_or_lt_of_le hθ.2 with hπ | hθ1
      · refine ⟨0, ?_, by rw [abs_zero]; exact hK0⟩
        rw [show (fun z' => Work.FTS_RegExport.THL.DthG α g z' θ τ) = fun _ => (0 : ℝ) from
          funext (fun z' => by rw [hπ]; exact DthG_at_theta_pi z' τ)]
        exact hasDerivAt_const z 0
      · have hmix := hw (4 : Fin 6) τ hτ z θ hzpos hθ0 hθ1
        norm_num [Work.FTS.RegExportIface.RXT.idx] at hmix
        refine ⟨Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z θ / z, ?_, ?_⟩
        · refine (Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z (f := Work.FTS.Galerkin.slice g τ)
            (hmin.c4 τ hτ0) 0 1 (by norm_num) hzpos hθ0 hθ1).congr_of_eventuallyEq ?_
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
          exact DthG_eq_mixed hz' ⟨hθ0, hθ1⟩ hτ0
        · have hΓ : K * Work.FTS.Regularity.Gamma α θ ≤ K := by
            simpa using mul_le_mul_of_nonneg_left hΓ1 hK0
          calc |Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z θ / z|
              = |Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z θ| / z := by
                rw [abs_div, abs_of_pos hzpos]
            _ ≤ K * Work.FTS.RegExportIface.ω α z θ / z :=
                div_le_div_of_nonneg_right hmix hzpos.le
            _ = K * (Work.FTS.RegExportIface.ω α z θ / z) := by ring
            _ ≤ K * Work.FTS.Regularity.Gamma α θ :=
                mul_le_mul_of_nonneg_left
                  (Work.FTS_RegExport.RXT.omega_div_z_le_Gamma α z θ hzpos.le hθ) hK0
            _ ≤ K := hΓ
  exact ⟨hval, hcontDz, hcontDth, fun z hz => ⟨hderivDz z hz, hderivDth z hz⟩⟩

end Work.FTS_RegExport.THL.L
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_le =====
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


end Work.FTS_StreamBdry.Inputs
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.near0Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.near0Aux` — auxiliary Lipschitz bounds for `near0`

The fragmentary Lipschitz bounds in the radial variable used by `Work.FTS_StreamBdry.SB4.near0`:

* `near0_lip_star` — the `U`-slot of the star summand `Φ̃_* = PhiTs αG Φs` is Lipschitz on `(0,1]`
  (from `RXT.starUop`, i.e. the `𝒲^{4,∞}`-bound of `StarPkgo2.UszW`);
* `near0_Uprime_thetaFstar`, `near0_lip_theta_fstar` — the explicit value of `U'(Θ(F_*))` and the
  resulting Lipschitz bound with constant `2`;
* `near0_hasDerivAt_Theta`, `near0_diff_pz_of_joint`, `near0_diff_pz_Theta` — radial
  differentiability of `Θ αG F` and of its `z`-derivative;
* `near0_lip_of_dz_bound` — a bound on `D_z` of `U'(Φ)` on `(0,1]` gives a Lipschitz bound for
  `U'(Φ)(·,θ)` (mean value inequality).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB4

set_option maxHeartbeats 800000

/-! ## §1 The star summand `Φ̃_*` -/

/-- **Lipschitz bound for the `U`-slot of the star summand.**  From the `𝒲^{4,∞}`-bound on
`((z+1)/z)·U'(Φ̃_*)` (`StarPkgo2.UszW`, via `RXT.starUop`) the `z`-derivative of `U'(Φ̃_*)`
is bounded by `C₁·(max Cs 1·αG)` on `(0,1]`, hence `U'(Φ̃_*)` is Lipschitz there. -/
lemma near0_lip_star {a Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn}
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
          (Work.FTS.Nonlin.PhiTs (Work.FTS.Regularity.pExp a) Φs) z θ
        - Work.FTS.StreamBdryIface.Uprime (Work.FTS.Regularity.pExp a)
          (Work.FTS.Nonlin.PhiTs (Work.FTS.Regularity.pExp a) Φs) z' θ|
        ≤ C * |z - z'| := by
  set αG := Work.FTS.Regularity.pExp a with hαGdef
  have hαG : 0 < αG := by rw [hαGdef, Work.FTS.Regularity.pExp]; linarith
  have hαG1 : αG ≤ 1 := by rw [hαGdef, Work.FTS.Regularity.pExp]; linarith
  obtain ⟨C1, hC1, hC1b⟩ := Work.FTS_RegExport.RXT.starUop hαG hαG1 hStar
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs αG Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hαG hαG1 hStar.smooth).1
  have hCnn : (0 : ℝ) ≤ C1 * (max Cs 1 * αG) :=
    mul_nonneg hC1 (mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hαG.le)
  refine ⟨C1 * (max Cs 1 * αG), hCnn, ?_⟩
  intro z hz z' hz' θ hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
    · -- the open quadrant
      have hdiff : ∀ w ∈ Set.Icc (min z z') (max z z'),
          DifferentiableAt ℝ (fun w' : ℝ => Work.FTS.StreamBdryIface.Uprime αG
            (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w := by
        intro w hw
        have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
        have h1 : DifferentiableAt ℝ (fun w' : ℝ => Work.FTS.Nonlin.PhiTs αG Φs w' θ) w :=
          (hsm.hasDerivAt_slice ⟨hθ0, hθ2⟩ hw0).differentiableAt
        have h2 : DifferentiableAt ℝ
            (fun w' : ℝ => Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w :=
          ((hsm.pz).hasDerivAt_slice ⟨hθ0, hθ2⟩ hw0).differentiableAt
        have hA : DifferentiableAt ℝ (fun w' : ℝ => αG * w') w :=
          differentiableAt_id.const_mul αG
        have h3 : DifferentiableAt ℝ (fun w' : ℝ => -3 * Work.FTS.Nonlin.PhiTs αG Φs w' θ
            - αG * w' * Work.Spaces.pz (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w :=
          (h1.const_mul (-3)).sub (hA.mul h2)
        simpa only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop] using
          h3.div_const (Work.Construction.s2 θ)
      have hbd : ∀ w ∈ Set.Icc (min z z') (max z z'),
          ‖deriv (fun w' : ℝ => Work.FTS.StreamBdryIface.Uprime αG
            (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w‖ ≤ C1 * (max Cs 1 * αG) := by
        intro w hw
        have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
        have hwle : w ≤ 1 := le_trans hw.2 (max_le hz.2 hz'.2)
        have h := hC1b 1 0 (by norm_num) w θ hw0 hθ0 hθ2
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_zero, Work.Spaces.Dz, Work.Spaces.pz] at h
        rw [abs_mul, abs_of_pos hw0, min_eq_left hwle] at h
        rw [Real.norm_eq_abs]
        have h3 : |deriv (fun w' : ℝ => Work.FTS.StreamBdryIface.Uprime αG
              (Work.FTS.Nonlin.PhiTs αG Φs) w' θ) w| * w ≤ C1 * (max Cs 1 * αG) * w := by
          rwa [mul_comm w] at h
        exact (mul_le_mul_iff_of_pos_right hw0).mp h3
      have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_Icc _ _)
        (left_mem_Icc.mpr (min_le_max)) (right_mem_Icc.mpr (min_le_max))
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmain
      rcases le_total z z' with hle | hle
      · rw [max_eq_right hle, min_eq_left hle] at hmain
        calc |Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ
                - Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z' θ|
            = |Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z' θ
                - Work.FTS.StreamBdryIface.Uprime αG (Work.FTS.Nonlin.PhiTs αG Φs) z θ| :=
              abs_sub_comm _ _
          _ ≤ C1 * (max Cs 1 * αG) * |z' - z| := hmain
          _ = C1 * (max Cs 1 * αG) * |z - z'| := by rw [abs_sub_comm z' z]
      · rw [max_eq_left hle, min_eq_right hle] at hmain
        exact hmain
    · -- θ = π/2
      have h0 : Work.Construction.s2 θ = 0 := by
        rw [Work.Construction.s2_eq, hθ2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
      exact mul_nonneg hCnn (abs_nonneg _)
  · -- θ = 0
    have h0 : Work.Construction.s2 θ = 0 := by
      rw [← hθ0, Work.Construction.s2_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
    simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
    exact mul_nonneg hCnn (abs_nonneg _)

/-! ## §2 The summand `Θ(F_*)` -/

/-- `U'(Θ(F_*))` has the explicit value `-3/(2(1+z)) + αG z/(2(1+z)²)`. -/
lemma near0_Uprime_thetaFstar {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
        = -(3 / 2) * (1 + z)⁻¹ + (αG / 2) * z * ((1 + z)⁻¹) ^ 2 := by
  intro z θ hzθ
  have hz : 0 < z := hzθ.1
  have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.s2_pos_of_Qd hzθ)
  have h1z : (1 + z) ≠ 0 := by positivity
  have hLz : Work.Construction.L12 (Work.Construction.Fstar αG) z = 2 * αG / (1 + z) :=
    Work.Construction.L12_Fstar_eq hαG hαG1 hz.le
  have hev : (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w)
      =ᶠ[𝓝 z] (fun w => 2 * αG / (1 + w)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact Work.Construction.L12_Fstar_eq hαG hαG1 hw.le
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-1 / (1 + z) ^ 2) z := h1.inv (by positivity)
  have h3 : HasDerivAt (fun y : ℝ => 2 * αG * (1 + y)⁻¹)
      (2 * αG * (-1 / (1 + z) ^ 2)) z := h2.const_mul _
  have h4 : (fun y : ℝ => 2 * αG / (1 + y)) = fun y : ℝ => 2 * αG * (1 + y)⁻¹ := by
    funext y; rw [div_eq_mul_inv]
  have h6 : HasDerivAt (fun y : ℝ => 2 * αG / (1 + y)) (-(2 * αG) / (1 + z) ^ 2) z := by
    have h3' := h3
    rw [← h4] at h3'
    have h7 : 2 * αG * (-1 / (1 + z) ^ 2) = -(2 * αG) / (1 + z) ^ 2 := by ring
    rw [h7] at h3'
    exact h3'
  have hL : HasDerivAt (fun w => Work.Construction.L12 (Work.Construction.Fstar αG) w)
      (-(2 * αG) / (1 + z) ^ 2) z :=
    (Filter.EventuallyEq.hasDerivAt_iff hev).2 h6
  have hpz' : deriv (fun w => 1 / (4 * αG) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar αG) w) z
      = 1 / (4 * αG) * Work.Construction.s2 θ * (-(2 * αG) / (1 + z) ^ 2) :=
    (hL.const_mul (1 / (4 * αG) * Work.Construction.s2 θ)).deriv
  simp only [Work.FTS.StreamBdryIface.Uprime, Work.Construction.Uop, Work.Construction.Theta,
    Work.Spaces.pz]
  rw [hpz', hLz]
  field_simp
  ring

/-- **Lipschitz bound for the `U`-slot of `Θ(F_*)`.**  From the explicit value of `U'(Θ(F_*))`
one gets the Lipschitz constant `2` on `(0,1]`. -/
lemma near0_lip_theta_fstar {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1) :
    ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
        - Work.FTS.StreamBdryIface.Uprime αG
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z' θ|
        ≤ 2 * |z - z'| := by
  intro z hz z' hz' θ hθ
  have hz1 : 0 < z := hz.1
  have hz2 : z ≤ 1 := hz.2
  have hz'1 : 0 < z' := hz'.1
  have hz'2 : z' ≤ 1 := hz'.2
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
    · rw [near0_Uprime_thetaFstar hαG hαG1 z θ ⟨hz.1, hθ0, hθ2⟩,
        near0_Uprime_thetaFstar hαG hαG1 z' θ ⟨hz'.1, hθ0, hθ2⟩]
      have hz0 : (1 + z) ≠ 0 := by positivity
      have hz0' : (1 + z') ≠ 0 := by positivity
      have hkey1 : (1 + z)⁻¹ - (1 + z')⁻¹ = (z' - z) * (((1 + z) * (1 + z'))⁻¹) := by
        field_simp
        ring
      have hkey2 : z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2
          = (z - z') * (1 - z * z') * (((1 + z) ^ 2 * (1 + z') ^ 2)⁻¹) := by
        field_simp
        ring
      have hb1 : |((1 + z) * (1 + z'))⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
        nlinarith
      have hb2 : |(1 - z * z')| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith
      have hb3 : |((1 + z) ^ 2 * (1 + z') ^ 2)⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
        have h1 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith
        have h2 : (1 : ℝ) ≤ (1 + z') ^ 2 := by nlinarith
        nlinarith
      have e1 : |(1 + z)⁻¹ - (1 + z')⁻¹| ≤ |z - z'| := by
        rw [hkey1, abs_mul, abs_sub_comm z' z]
        calc |z - z'| * |((1 + z) * (1 + z'))⁻¹| ≤ |z - z'| * 1 :=
              mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
          _ = |z - z'| := mul_one _
      have e2 : |z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2| ≤ |z - z'| := by
        rw [hkey2, abs_mul, abs_mul]
        calc |z - z'| * |1 - z * z'| * |((1 + z) ^ 2 * (1 + z') ^ 2)⁻¹|
            ≤ |z - z'| * 1 * 1 := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hb2 (abs_nonneg _)) hb3
                (abs_nonneg _) ?_
              positivity
          _ = |z - z'| := by ring
      have hsplit : (-(3 / 2) * (1 + z)⁻¹ + (αG / 2) * z * ((1 + z)⁻¹) ^ 2)
            - (-(3 / 2) * (1 + z')⁻¹ + (αG / 2) * z' * ((1 + z')⁻¹) ^ 2)
          = (-(3 / 2)) * ((1 + z)⁻¹ - (1 + z')⁻¹)
            + (αG / 2) * (z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2) := by ring
      rw [hsplit]
      have h32 : |(-(3 / 2) : ℝ)| = 3 / 2 := by norm_num
      have hα2 : |αG / 2| = αG / 2 := abs_of_nonneg (by linarith)
      calc |(-(3 / 2)) * ((1 + z)⁻¹ - (1 + z')⁻¹)
            + (αG / 2) * (z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2)|
          ≤ |(-(3 / 2)) * ((1 + z)⁻¹ - (1 + z')⁻¹)|
            + |(αG / 2) * (z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2)| := abs_add_le _ _
        _ = (3 / 2) * |(1 + z)⁻¹ - (1 + z')⁻¹|
            + (αG / 2) * |z * ((1 + z)⁻¹) ^ 2 - z' * ((1 + z')⁻¹) ^ 2| := by
            rw [abs_mul, abs_mul, h32, hα2]
        _ ≤ (3 / 2) * |z - z'| + (αG / 2) * |z - z'| :=
            add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
              (mul_le_mul_of_nonneg_left e2 (by linarith))
        _ ≤ 2 * |z - z'| := by nlinarith [abs_nonneg (z - z')]
    · have h0 : Work.Construction.s2 θ = 0 := by
        rw [Work.Construction.s2_eq, hθ2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
      positivity
  · have h0 : Work.Construction.s2 θ = 0 := by
      rw [← hθ0, Work.Construction.s2_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
    simp only [Work.FTS.StreamBdryIface.Uprime, h0, div_zero, sub_zero, abs_zero]
    positivity

/-! ## §3 Radial differentiability of the summands -/

/-- `Θ αG F` is differentiable in the radial variable as soon as `L12 F` is. -/
lemma near0_hasDerivAt_Theta {αG : ℝ} {F : ℝ → ℝ → ℝ} {θ z : ℝ}
    (h : DifferentiableAt ℝ (fun w => Work.Construction.L12 F w) z) :
    HasDerivAt (fun w => Work.Construction.Theta αG F w θ)
      (Work.Spaces.pz (Work.Construction.Theta αG F) z θ) z := by
  have hc : DifferentiableAt ℝ (fun w => 1 / (4 * αG) * Work.Construction.s2 θ
      * Work.Construction.L12 F w) z := h.const_mul _
  simpa only [Work.Construction.Theta, Work.Spaces.pz] using hc.hasDerivAt

/-- The radial slice of `∂_z Φ` is differentiable when `Φ` is jointly `C³` on the quadrant. -/
lemma near0_diff_pz_of_joint {Φ : ℝ → ℝ → ℝ} {θ w : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hw : 0 < w)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun w' => Work.Spaces.pz Φ w' θ) w := by
  have hslice : ContDiffOn ℝ 3 (fun w' => Φ w' θ) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθ h3
  have hd : ContDiffOn ℝ 2 (derivWithin (fun w' => Φ w' θ) (Set.Ioi 0)) (Set.Ioi 0) :=
    hslice.derivWithin (uniqueDiffOn_Ioi 0) (by norm_num)
  have hdiff : DifferentiableAt ℝ (derivWithin (fun w' => Φ w' θ) (Set.Ioi 0)) w :=
    (hd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hw)
  have hev : (fun w' => Work.Spaces.pz Φ w' θ) =ᶠ[𝓝 w]
      derivWithin (fun w' => Φ w' θ) (Set.Ioi 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
    simp only [Work.Spaces.pz, derivWithin_of_isOpen isOpen_Ioi hw']
  exact (hev.differentiableAt_iff).mpr hdiff

/-- Radial differentiability of `∂_z (Θ αG F)` from the differentiability of `L12dens F`. -/
lemma near0_diff_pz_Theta {αG : ℝ} {F : ℝ → ℝ → ℝ} {θ z : ℝ} (hz : 0 < z)
    (h : ∀ w : ℝ, 0 < w → HasDerivAt (fun w' => Work.Construction.L12 F w')
        (-(Work.Construction.L12dens F w)) w)
    (hd : ∀ w : ℝ, 0 < w → DifferentiableAt ℝ (fun w' => Work.Construction.L12dens F w') w) :
    DifferentiableAt ℝ (fun w' => Work.Spaces.pz (Work.Construction.Theta αG F) w' θ) z := by
  have hev : (fun w' => Work.Spaces.pz (Work.Construction.Theta αG F) w' θ)
      =ᶠ[𝓝 z] (fun w' => 1 / (4 * αG) * Work.Construction.s2 θ
        * (-(Work.Construction.L12dens F w'))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w' hw'
    rw [Work.Spaces.pz]
    show deriv (fun w'' => 1 / (4 * αG) * Work.Construction.s2 θ
        * Work.Construction.L12 F w'') w'
      = 1 / (4 * αG) * Work.Construction.s2 θ * (-(Work.Construction.L12dens F w'))
    rw [deriv_const_mul _ (h w' hw').differentiableAt, (h w' hw').deriv]
  have h2 : DifferentiableAt ℝ (fun w' => 1 / (4 * αG) * Work.Construction.s2 θ
      * (-(Work.Construction.L12dens F w'))) z := ((hd z hz).neg).const_mul _
  exact (hev.differentiableAt_iff).mpr h2

/-! ## §4 Lipschitz bounds from `D_z`-bounds -/

/-- A bound on the `D_z`-derivative of `U'(Φ)` on `(0,1]` gives a Lipschitz bound for
`U'(Φ)(·,θ)`, provided the slices are differentiable. -/
lemma near0_lip_of_dz_bound {αG C : ℝ} (hC : 0 ≤ C) {Φ : ℝ → ℝ → ℝ}
    (hdiff : ∀ w θ, (w, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w)
    (hbd : ∀ w θ, (w, θ) ∈ Work.Construction.Qd → w ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime αG Φ z θ) w θ| ≤ C * w) :
    ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.StreamBdryIface.Uprime αG Φ z θ
        - Work.FTS.StreamBdryIface.Uprime αG Φ z' θ| ≤ C * |z - z'| := by
  intro z hz z' hz' θ hθ
  have hdiff' : ∀ w ∈ Set.Icc (min z z') (max z z'),
      DifferentiableAt ℝ (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
    exact hdiff w θ ⟨hw0, hθ.1, hθ.2⟩
  have hbd' : ∀ w ∈ Set.Icc (min z z') (max z z'),
      ‖deriv (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w‖ ≤ C := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le (lt_min hz.1 hz'.1) hw.1
    have hwle : w ≤ 1 := le_trans hw.2 (max_le hz.2 hz'.2)
    have h := hbd w θ ⟨hw0, hθ.1, hθ.2⟩ hwle
    rw [Real.norm_eq_abs]
    have hD : Work.Spaces.Dz (fun z θ => Work.FTS.StreamBdryIface.Uprime αG Φ z θ) w θ
        = w * deriv (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w := by
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [hD, abs_mul, abs_of_pos hw0] at h
    have h3 : |deriv (fun w' => Work.FTS.StreamBdryIface.Uprime αG Φ w' θ) w| * w ≤ C * w := by
      rwa [mul_comm w] at h
    exact (mul_le_mul_iff_of_pos_right hw0).mp h3
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff' hbd' (convex_Icc _ _)
    (left_mem_Icc.mpr (min_le_max)) (right_mem_Icc.mpr (min_le_max))
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmain
  rcases le_total z z' with hle | hle
  · rw [max_eq_right hle, min_eq_left hle] at hmain
    calc |Work.FTS.StreamBdryIface.Uprime αG Φ z θ
            - Work.FTS.StreamBdryIface.Uprime αG Φ z' θ|
        = |Work.FTS.StreamBdryIface.Uprime αG Φ z' θ
            - Work.FTS.StreamBdryIface.Uprime αG Φ z θ| := abs_sub_comm _ _
      _ ≤ C * |z' - z| := hmain
      _ = C * |z - z'| := by rw [abs_sub_comm z' z]
  · rw [max_eq_left hle, min_eq_right hle] at hmain
    exact hmain


end Work.FTS_StreamBdry.SB4
end
end
