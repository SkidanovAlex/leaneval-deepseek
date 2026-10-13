import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.RXT.st1_angle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DzG_theta_mod` (B1 of `fts_thlip_o1_plans.md`)

The z-uniform `θ`-modulus of the second slot `g̃ ↦ z∂_z g̃ = D_z g̃` of the family
`g̃ = gS α (tauExt g)`.

The family `DzG α g z · τ = D_z (g̃(·,·,τ))(z,·)` is `α`-Hölder on `Iθ` with a constant uniform in
`z ≥ 0` and `τ ∈ [0,S]`.  Route (exactly the plan's):

* the value bound `|D_z g̃(z,θ,τ)| = |mixed 1 0 g̃| ≤ K·ω ≤ K·Γ(θ)` uses the `(1,0)`-slot of `hw`
  on the open interval and the two boundary vanishing facts at `θ = 0, π/2` (`hmin.vanish`);
* the derivative bound `|∂_θ(D_z g̃)| = |mixed 1 1 g̃|/sin 2θ ≤ K·Γ(θ)/sin 2θ` uses the `(1,1)`
  slot (`mixed_one_one_eq`), with the `z²/(1+z)²` factor absorbed by `ω ≤ Γ`;
* the engine `RXT.theta_modulus_uniform_fb` turns the two into `L·|Δθ|^α`.

The bridge between `DzG` (built from the *sanitised* family `gS α (tauExt g)`, extended to `z ≤ 0`
by `0`) and the family `GG α g = extG (gS α (tauExt g))` used by `st1_prelim` is
`DzG_eq_mul_pz_GG` below: `DzG α g z x τ = z · ∂_z (GG α g)` for `z > 0`, `τ ≥ 0`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

/-- **The bridge**: on `z > 0` and `τ ≥ 0`, `DzG α g z x τ` is `z` times the `∂_z`-slice of the
extended family `GG α g = extG (gS α (tauExt g))`. -/
theorem DzG_eq_mul_pz_GG {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ z : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (x : ℝ) :
    Work.FTS_RegExport.THL.DzG α g z x τ
      = z * Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXT.GG α g) τ) z x := by
  show z * deriv (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' x τ) z
    = z * deriv (fun z' => Work.FTS_RegExport.RXT.GG α g z' x τ) z
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact (Work.FTS.RegPkgGal.extG_of_pos
    (g := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) hz' hτ).symm

/-- `DzG α g 0 x τ = 0`. -/
theorem DzG_zero_left (α : ℝ) (g : Work.FTS.Galerkin.Fam) (x τ : ℝ) :
    Work.FTS_RegExport.THL.DzG α g 0 x τ = 0 := by
  simp only [Work.FTS_RegExport.THL.DzG, Work.Spaces.Dz, zero_mul]

theorem DzG_theta_mod {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S) (hK0 : 0 ≤ K)
    (hw : Work.FTS_RegExport.THL.WSys α S K g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.THL.DzG α g z θ τ - Work.FTS_RegExport.THL.DzG α g z θ' τ|
          ≤ L * |θ - θ'| ^ α := by
  obtain ⟨L, hL0, hL⟩ := Work.FTS_RegExport.RXT.theta_modulus_uniform_fb (α := α) (C := K) (K := K)
    hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    rw [DzG_zero_left α g θ τ, DzG_zero_left α g θ' τ, sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · refine hL (u := fun x => Work.FTS_RegExport.THL.DzG α g z x τ)
      (u' := fun x => z * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x)
      ?_ ?_ ?_ θ hθ θ' hθ'
    · -- differentiability of the `θ`-slice
      intro x hx
      have hc4 : ContDiffAt ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, x) :=
        ((hmin.c4 τ hτ.1).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (z, x) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) from ⟨hzpos, hx.1, hx.2⟩))).of_le
          (by norm_num)
      have hd : HasDerivAt
          (fun x' => Work.Spaces.pz
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXT.GG α g) τ) z x')
          (Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x) x :=
        (Work.FTS.EllipticEst.TT.step2Ae.hasDerivAt_pz_theta hc4).congr_of_eventuallyEq (by
          filter_upwards [isOpen_Ioo.mem_nhds hx] with x' hx'
          exact Work.FTS_RegExport.RXT.pz_GG_eq α hτ.1 hzpos ⟨hx'.1.le, hx'.2.le⟩)
      exact (hd.const_mul z).congr_of_eventuallyEq (by
        filter_upwards with x'
        exact (DzG_eq_mul_pz_GG hτ.1 hzpos x'))
    · -- the derivative bound `|∂_θ(D_z g̃)| ≤ K·Γ/sin 2θ`
      intro x hx
      have hsin : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
      have h4 := hw (4 : Fin 6) τ hτ z x hzpos hx.1 hx.2
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h4
      have hid : Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x
          = z * (Real.sin (2 * x)
              * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x) :=
        Work.FTS_RegExport.RXT.mixed_one_one_eq _ z x
      have hkey : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
            * Real.sin (2 * x)) * z ≤ K * Work.FTS.Regularity.Gamma α x := by
        have h1 : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)) * z
            = |Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x| := by
          rw [hid]
          simp only [abs_mul, abs_of_pos hzpos, abs_of_pos hsin]
          ring
        rw [h1]
        exact le_trans h4 (mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le ⟨hx.1.le, hx.2.le⟩) hK0)
      have hkey' : (z * |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|)
            * Real.sin (2 * x) ≤ K * Work.FTS.Regularity.Gamma α x := by
        have e : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)) * z
            = (z * |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|)
              * Real.sin (2 * x) := by ring
        rw [← e]; exact hkey
      calc |z * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
          = z * |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x| := by
            rw [abs_mul, abs_of_pos hzpos]
        _ ≤ K * (Work.FTS.Regularity.Gamma α x / Real.sin (2 * x)) := by
            rw [← mul_div_assoc]
            exact (le_div_iff₀ hsin).mpr hkey'
    · -- the value bound `|D_z g̃| ≤ K·Γ`
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
      · subst hx0
        rw [DzG_eq_mul_pz_GG hτ.1 hzpos 0,
          Work.FTS_RegExport.RXT.pz_GG_eq_zero_left α hτ.1 hzpos hv, mul_zero, abs_zero]
        exact mul_nonneg hK0 (Work.ConstructionInstance.Gamma_nonneg hx)
      · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
        · subst hxπ
          rw [DzG_eq_mul_pz_GG hτ.1 hzpos (π / 2),
            Work.FTS_RegExport.RXT.pz_GG_eq_zero_right α hτ.1 hzpos hv, mul_zero, abs_zero]
          exact mul_nonneg hK0 (Work.ConstructionInstance.Gamma_nonneg hx)
        · rw [DzG_eq_mul_pz_GG hτ.1 hzpos x, Work.FTS_RegExport.RXT.pz_GG_eq α hτ.1 hzpos hx]
          have h1 := hw (1 : Fin 6) τ hτ z x hzpos hxpos hxlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
          have h1' : |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
              ≤ K * Work.FTS.RegExportIface.ω α z x := by
            simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
              Work.Spaces.DthIter_zero, Work.Spaces.Dz] using h1
          exact le_trans h1' (mul_le_mul_of_nonneg_left
            (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le hx) hK0)

end Work.FTS_RegExport.THL.L
