import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.RXT.st1_angle
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z

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
