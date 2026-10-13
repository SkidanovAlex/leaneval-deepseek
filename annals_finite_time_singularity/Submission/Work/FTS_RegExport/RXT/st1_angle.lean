/-
# `Work.FTS_RegExport.RXT.st1_angle` — the two angular moduli of `St1Class`

The `α`-Hölder moduli of `g̃` and of `∂_z g̃` in the angle `θ`, obtained from the uniform
`θ`-modulus engine `theta_modulus_uniform` applied slicewise:

* for `g̃` the derivative bound is `|∂_θ g̃| ≤ Kω/sin 2θ ≤ KΓ/sin 2θ` (the `(0,1)`-slot);
* for `∂_z g̃` it is `|∂_θ∂_z g̃| = |D_zD_θ g̃|/(z sin 2θ) ≤ Kω/(z sin 2θ) ≤ KΓ/sin 2θ`
  (the `(1,1)`-slot, via `mixed_one_one_eq`),

and in both cases the value bound is `|g̃| ≤ KΓ` resp. `|∂_zg̃| ≤ Kω/z ≤ KΓ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.st1_prelim
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-- The `α`-Hölder modulus of `g̃` in `θ`. -/
theorem st1_hhθ {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |GG α g z θ τ - GG α g z θ' τ| ≤ Lθ * |θ - θ'| ^ α := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  obtain ⟨L, hL0, hL⟩ := theta_modulus_uniform_fb (α := α) (C := K) (K := K) hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    rw [GG_of_nonpos α le_rfl, GG_of_nonpos α le_rfl, sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · exact hL (u := fun x => GG α g z x τ)
      (u' := fun x => Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x)
      (fun x hx =>
        (Work.FTS.RegPkgGal.R4b.hasDerivAt_sliceTh isOpen_Ioi isOpen_Ioo
          ((hmin.c4 τ hτ.1).of_le (by norm_num)) hzpos hx).congr_of_eventuallyEq (by
            filter_upwards [isOpen_Ioo.mem_nhds hx] with x' hx'
            exact GG_of_mem α hτ.1 hzpos ⟨hx'.1.le, hx'.2.le⟩))
      (fun x hx => by
        have hxI : x ∈ Work.Spaces.Iθ := ⟨hx.1.le, hx.2.le⟩
        have hsin : 0 < Real.sin (2 * x) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
        have h2 := hw (2 : Fin 6) τ hτ z x hzpos hx.1 hx.2
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h2
        have hDth : Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z x
            = Real.sin (2 * x) * Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x := rfl
        have hkey : |Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x| * Real.sin (2 * x)
            ≤ K * Work.FTS.Regularity.Gamma α x := by
          calc |Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x| * Real.sin (2 * x)
              = |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z x| := by
                rw [hDth, abs_mul, abs_of_pos hsin]; ring
            _ ≤ K * Work.FTS.RegExportIface.ω α z x := h2
            _ ≤ K * Work.FTS.Regularity.Gamma α x :=
                mul_le_mul_of_nonneg_left (omega_le_Gamma α z x hzpos.le hxI) hK0
        have hfin : |Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x|
            ≤ K * Work.FTS.Regularity.Gamma α x / Real.sin (2 * x) :=
          (le_div_iff₀ hsin).mpr hkey
        simpa only [mul_div_assoc] using hfin)
      (fun x hx => by
        rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
        · subst hx0
          rw [GG_eq_zero_left α hτ.1 hzpos hv, Gamma_zero_left hα, mul_zero, abs_zero]
        · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
          · subst hxπ
            rw [GG_eq_zero_right α hτ.1 hzpos hv, Gamma_zero_right hα, mul_zero, abs_zero]
          · rw [GG_of_mem α hτ.1 hzpos hx]
            have h0 := hw (0 : Fin 6) τ hτ z x hzpos hxpos hxlt
            norm_num [Work.FTS.RegExportIface.RXT.idx] at h0
            calc |Work.FTS.Galerkin.slice g τ z x|
                = |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z x| := rfl
              _ ≤ K * Work.FTS.RegExportIface.ω α z x := h0
              _ ≤ K * Work.FTS.Regularity.Gamma α x :=
                  mul_le_mul_of_nonneg_left (omega_le_Gamma α z x hzpos.le hx) hK0)
      θ hθ θ' hθ'

/-- The `α`-Hölder modulus of `∂_z g̃` in `θ`. -/
theorem st1_hhθp {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Nθ : ℝ, 0 ≤ Nθ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
          - Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ'| ≤ Nθ * |θ - θ'| ^ α := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  obtain ⟨L, hL0, hL⟩ := theta_modulus_uniform_fb (α := α) (C := K) (K := K) hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    have hz0' : ∀ x : ℝ, Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) 0 x = 0 :=
      fun x => by
        show deriv (fun z' => GG α g z' x τ) 0 = 0
        exact deriv_eq_zero_of_eq_zero_of_nonpos (fun y hy => GG_of_nonpos α hy)
    rw [hz0' θ, hz0' θ', sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · exact hL (u := fun x => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z x)
      (u' := fun x => Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x)
      (fun x hx =>
        (Work.FTS.EllipticEst.TT.step2Ae.hasDerivAt_pz_theta
          (((hmin.c4 τ hτ.1).contDiffAt
            ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds (show (z, x) ∈ Set.Ioi (0:ℝ) ×ˢ
              Set.Ioo (0:ℝ) (π / 2) from ⟨hzpos, hx.1, hx.2⟩))).of_le
              (by norm_num))).congr_of_eventuallyEq (by
          filter_upwards [isOpen_Ioo.mem_nhds hx] with x' hx'
          exact pz_GG_eq α hτ.1 hzpos ⟨hx'.1.le, hx'.2.le⟩))
      (fun x hx => by
        have hxI : x ∈ Work.Spaces.Iθ := ⟨hx.1.le, hx.2.le⟩
        have hsin : 0 < Real.sin (2 * x) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
        have h4 := hw (4 : Fin 6) τ hτ z x hzpos hx.1 hx.2
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h4
        have hid : Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x
            = z * (Real.sin (2 * x)
                * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x) :=
          mixed_one_one_eq _ z x
        -- `|∂_θ∂_zg| · sin 2θ ≤ KΓ`, then divide by `sin 2θ`
        have hkey : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)) * z ≤ K * Work.FTS.RegExportIface.ω α z x := by
          have h1 : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
                * Real.sin (2 * x)) * z
              = |Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x| := by
            rw [hid]
            simp only [abs_mul, abs_of_pos hzpos, abs_of_pos hsin]
            ring
          rw [h1]; exact h4
        have h5 : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)
            ≤ K * (Work.FTS.RegExportIface.ω α z x / z) := by
          have h7 : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
                * Real.sin (2 * x)
              ≤ K * Work.FTS.RegExportIface.ω α z x / z := (le_div_iff₀ hzpos).mpr hkey
          rwa [mul_div_assoc] at h7
        have hfin : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x) ≤ K * Work.FTS.Regularity.Gamma α x :=
          le_trans h5 (mul_le_mul_of_nonneg_left
            (omega_div_z_le_Gamma α z x hzpos.le hxI) hK0)
        have hres : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
            ≤ K * Work.FTS.Regularity.Gamma α x / Real.sin (2 * x) :=
          (le_div_iff₀ hsin).mpr hfin
        simpa only [mul_div_assoc] using hres)
      (fun x hx => by
        rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
        · subst hx0
          rw [pz_GG_eq_zero_left α hτ.1 hzpos hv, Gamma_zero_left hα, mul_zero, abs_zero]
        · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
          · subst hxπ
            rw [pz_GG_eq_zero_right α hτ.1 hzpos hv, Gamma_zero_right hα, mul_zero, abs_zero]
          · rw [pz_GG_eq α hτ.1 hzpos hx]
            have h1 := hw (1 : Fin 6) τ hτ z x hzpos hxpos hxlt
            norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
            have hkey : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x| * z
                ≤ K * Work.FTS.RegExportIface.ω α z x := by
              have h2 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x| * z
                  = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z x| := by
                show |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x| * z
                  = |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                rw [abs_mul, abs_of_pos hzpos]; ring
              rw [h2]; exact h1
            have h4 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                ≤ K * (Work.FTS.RegExportIface.ω α z x / z) := by
              have h5 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                  ≤ K * Work.FTS.RegExportIface.ω α z x / z := (le_div_iff₀ hzpos).mpr hkey
              rwa [mul_div_assoc] at h5
            calc |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                ≤ K * (Work.FTS.RegExportIface.ω α z x / z) := h4
              _ ≤ K * Work.FTS.Regularity.Gamma α x :=
                  mul_le_mul_of_nonneg_left (omega_div_z_le_Gamma α z x hzpos.le hx) hK0)
      θ hθ θ' hθ'

end Work.FTS_RegExport.RXT
