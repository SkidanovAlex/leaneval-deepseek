import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXR5L.ProdDefs
import Submission.Work.FTS_RegExport.RXT.weighted_system
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.DthFtau_C1Jet
import Submission.Work.FTS_RegExport.RXT.st1_prelim
import Submission.Work.FTS.Regularity.pzFstarModuli

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
open Work.FTS_RegExport.RXR5

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §1 The `Γ`-weighted bounds of the static profile `F_*`

The pieces of `F_*` are the explicit factorisations
`D_θF_* = DthCoeff α θ · F̂(z)` and `D_zF_* = pzCoeff α θ · zF̂'(z)` (`RXR5.Dth_Fstar_eq`,
`RXR5.Dz_Fstar_eq`), with the angular coefficients bounded by a multiple of `Γ = Gmp α` and the
radial factors by `1/2` (`RXR5.hhat_abs_le`, `Regularity.fmFstar_abs_le_half`).  Together with the
global bound `|F_*| ≤ 20·Γ` (`Regularity.fstar_abs_le_gamma`) this is everything the assembly
needs from the static profile. -/

/-- `|pzCoeff α θ| ≤ 10·Γ(θ)` on `Iθ` (`3α ≤ 1`, `c ≥ 1/10`, `Γ ≥ 0`). -/
theorem pzCoeff_gam_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.Regularity.pzCoeff α θ| ≤ 10 * Gmp α θ := by
  have h3a : 0 < 3 * α := by linarith
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c (3 * α) :=
    (Work.Spaces.c_bounds (3 * α) (by linarith) (by linarith)).1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith
  have hcoef : 3 * α / Work.Spaces.c (3 * α) ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hc]
  have hG : Work.Spaces.Gam (3 * α) θ = Gmp α θ :=
    (rfl : Work.Spaces.Gam (3 * α) θ = Work.Spaces.Gam (pExp α) θ).trans (Gmp_eq_Gam α θ).symm
  have hg0 : 0 ≤ Work.Spaces.Gam (3 * α) θ := by rw [hG]; exact Gmp_nonneg hθ
  rw [Work.FTS.Regularity.pzCoeff, abs_mul, abs_div, abs_of_nonneg h3a.le, abs_of_nonneg hg0,
    abs_of_pos hcpos, hG]
  calc 3 * α * (Gmp α θ / Work.Spaces.c (3 * α))
      = (3 * α / Work.Spaces.c (3 * α)) * Gmp α θ := by ring
    _ ≤ 10 * Gmp α θ := mul_le_mul_of_nonneg_right hcoef (Gmp_nonneg hθ)

/-- `|D_θF_*| ≤ 20·Γ` on the closed quadrant. -/
theorem dth_Fstar_gam_le {α z θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dth (Work.Construction.Fstar (pExp α)) z θ| ≤ 20 * Gmp α θ := by
  have hc := Work.Spaces.c_bounds (pExp α) (Work.FTS.Regularity.pExp_pos hα)
    (Work.FTS.Regularity.pExp_le_one hα13)
  have hcpos : 0 < Work.Spaces.c (pExp α) := by linarith [hc.1]
  have hcoef : (pExp α) ^ 2 / Work.Spaces.c (pExp α) ≤ 10 :=
    Work.FTS_RegExport.RXR5.DthCoeff_coef_le hα hα13
  have hG : Work.Spaces.Gam (pExp α) θ = Gmp α θ := (Gmp_eq_Gam α θ).symm
  have hg0 : 0 ≤ Work.Spaces.Gam (pExp α) θ := by rw [hG]; exact Gmp_nonneg hθ
  have hq : |Work.Spaces.qfun θ * Work.Spaces.Gam (pExp α) θ| ≤ 4 / 3 * Gmp α θ := by
    rw [abs_mul, abs_of_nonneg hg0, hG]
    exact mul_le_mul_of_nonneg_right Work.FTS_RegExport.RXR5.qfun_abs_le (Gmp_nonneg hθ)
  have hDthCoeff : |Work.FTS_RegExport.RXR5.DthCoeff α θ| ≤ 40 / 3 * Gmp α θ := by
    rw [Work.FTS_RegExport.RXR5.DthCoeff_shape, abs_mul,
      abs_of_nonneg (div_nonneg (sq_nonneg _) hcpos.le)]
    calc (pExp α) ^ 2 / Work.Spaces.c (pExp α)
          * |Work.Spaces.qfun θ * Work.Spaces.Gam (pExp α) θ|
        ≤ 10 * (4 / 3 * Gmp α θ) := mul_le_mul hcoef hq (abs_nonneg _) (by norm_num)
      _ = 40 / 3 * Gmp α θ := by ring
  rw [Work.FTS_RegExport.RXR5.Dth_Fstar_eq hα hθ, abs_mul]
  calc |Work.FTS_RegExport.RXR5.DthCoeff α θ| * |Work.FM.Fstar z|
      ≤ (40 / 3 * Gmp α θ) * (1 / 2) :=
        mul_le_mul hDthCoeff (Work.FTS.Regularity.fmFstar_abs_le_half hz) (abs_nonneg _)
          (mul_nonneg (by norm_num) (Gmp_nonneg hθ))
    _ = 20 / 3 * Gmp α θ := by ring
    _ ≤ 20 * Gmp α θ := mul_le_mul_of_nonneg_right (by norm_num) (Gmp_nonneg hθ)

/-- `|D_zF_*| ≤ 5·Γ` on the closed quadrant. -/
theorem dz_Fstar_gam_le {α z θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar (pExp α)) z θ| ≤ 5 * Gmp α θ := by
  rw [Work.FTS_RegExport.RXR5.Dz_Fstar_eq hα hz, abs_mul]
  calc |Work.FTS.Regularity.pzCoeff α θ| * |z * deriv Work.FM.Fstar z|
      ≤ (10 * Gmp α θ) * (1 / 2) :=
        mul_le_mul (pzCoeff_gam_le hα hα13 hθ) (Work.FTS_RegExport.RXR5.hhat_abs_le hz)
          (abs_nonneg _) (mul_nonneg (by norm_num) (Gmp_nonneg hθ))
    _ = 5 * Gmp α θ := by ring

/-- `|F_*| ≤ 20·Γ` on the closed quadrant. -/
theorem fstar_pExp_abs_le_gam {α z θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (pExp α) z θ| ≤ 20 * Gmp α θ :=
  Work.FTS.Regularity.fstar_abs_le_gamma hα hα13 hz hθ

/-- `F_*(z,0) = 0`. -/
theorem fstar_pExp_zero_left {α z : ℝ} (hα : 0 < α) :
    Work.Construction.Fstar (pExp α) z 0 = 0 := by
  rw [Work.Construction.Fstar,
    Work.FTS_RegExport.RXR5.gamP_zero (Work.FTS.Regularity.pExp_pos hα)]
  simp

/-- `F_*(z,π/2) = 0`. -/
theorem fstar_pExp_zero_right {α z : ℝ} (hα : 0 < α) :
    Work.Construction.Fstar (pExp α) z (π / 2) = 0 := by
  rw [Work.Construction.Fstar,
    Work.FTS_RegExport.RXR5.gamP_pi_half (Work.FTS.Regularity.pExp_pos hα)]
  simp

/-! ## §2 The sanitised family `g̃ = gS α (tauExt g) = SG α g` -/

/-- `g̃` agrees with the `τ`-slice of `g` on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`. -/
theorem SG_slice_eq_of_pos {α τ z θ : ℝ} {g : Fam} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : 0 ≤ τ) : SG α g z θ τ = slice g τ z θ := by
  rw [SG_apply_of_pos hz hθ.1 hθ.2, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
  rfl

/-- The radial slice of `g̃` vanishes identically at `θ = 0`, for `τ ≥ 0`. -/
theorem SG_slice_zero_left {α τ : ℝ} {g : Fam}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (hτ : 0 ≤ τ) :
    ∀ z : ℝ, SG α g z 0 τ = 0 := by
  intro z
  by_cases hz : 0 < z
  · rw [SG_apply_of_pos hz le_rfl (by linarith [Real.pi_pos]),
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    exact (hmin.vanish τ hτ z hz.le).1
  · exact SG_apply_of_nonpos (not_lt.mp hz)

/-- The radial slice of `g̃` vanishes identically at `θ = π/2`, for `τ ≥ 0`. -/
theorem SG_slice_zero_right {α τ : ℝ} {g : Fam}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (hτ : 0 ≤ τ) :
    ∀ z : ℝ, SG α g z (π / 2) τ = 0 := by
  intro z
  by_cases hz : 0 < z
  · rw [SG_apply_of_pos hz (by linarith [Real.pi_pos]) le_rfl,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    exact (hmin.vanish τ hτ z hz.le).2
  · exact SG_apply_of_nonpos (not_lt.mp hz)

/-- On the open quadrant, `D_θg̃ = D_z^0D_θ^1 g(τ)`. -/
theorem Dth_SG_eq_mixed {α τ z θ : ℝ} {g : Fam} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (hτ : 0 ≤ τ) :
    Work.Spaces.Dth (fun z θ => SG α g z θ τ) z θ = Work.Spaces.mixed 0 1 (slice g τ) z θ := by
  rw [show Work.Spaces.Dth (fun z θ => SG α g z θ τ) z θ
        = Real.sin (2 * θ) * deriv (fun θ' => SG α g z θ' τ) θ from rfl,
      show Work.Spaces.mixed 0 1 (slice g τ) z θ
        = Real.sin (2 * θ) * deriv (fun θ' => slice g τ z θ') θ from rfl]
  congr 1
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact SG_slice_eq_of_pos hz ⟨hθ'.1.le, hθ'.2.le⟩ hτ)

/-- On the open quadrant, `D_zg̃ = D_z^1D_θ^0 g(τ)`. -/
theorem Dz_SG_eq_mixed {α τ z θ : ℝ} {g : Fam} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : 0 ≤ τ) :
    Work.Spaces.Dz (fun z θ => SG α g z θ τ) z θ = Work.Spaces.mixed 1 0 (slice g τ) z θ := by
  rw [show Work.Spaces.Dz (fun z θ => SG α g z θ τ) z θ
        = z * deriv (fun z' => SG α g z' θ τ) z from rfl,
      show Work.Spaces.mixed 1 0 (slice g τ) z θ
        = z * deriv (fun z' => slice g τ z' θ) z from rfl]
  congr 1
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact SG_slice_eq_of_pos hz' hθ hτ)

/-! ## §3 The split of `D_zF_τ` on the open quadrant -/

/-- `D_z(F_* + g̃) = D_zF_* + D_zg̃` on the open quadrant (differentiability of the two
`z`-slices plus `deriv_add`). -/
theorem Dz_Fp_split {α τ z θ : ℝ} {g : Fam}
    (hc4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0)
    (hτ : 0 ≤ τ) (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.Dz (Fp α g τ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar (pExp α)) z θ
        + Work.Spaces.Dz (fun z θ => SG α g z θ τ) z θ := by
  have hdF : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (pExp α) z' θ) z := by
    have hd : DifferentiableAt ℝ (fun z' => Work.FM.Fstar z') z :=
      (Work.FM.hasDerivAt_Fstar z (by linarith)).differentiableAt
    have hfun : (fun z' => Work.Construction.Fstar (pExp α) z' θ)
        = fun z' => (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
            * Work.FM.Fstar z' := by
      funext z'; simp only [Work.Construction.Fstar]
    rw [hfun]; exact hd.const_mul _
  have hdG : DifferentiableAt ℝ (fun z' => SG α g z' θ τ) z := by
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
      rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ0, hθ1⟩
    have hdiff : DifferentiableAt ℝ (Function.uncurry (slice g τ)) (z, θ) :=
      (hc4.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    have hslice : DifferentiableAt ℝ (fun z' => slice g τ z' θ) z :=
      Work.Spaces.differentiableAt_curry_left hdiff
    refine hslice.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact SG_slice_eq_of_pos hz' ⟨hθ0.le, hθ1.le⟩ hτ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [show (fun z' => Fp α g τ z' θ)
        = (fun z' => Work.Construction.Fstar (pExp α) z' θ + SG α g z' θ τ) from rfl,
      show (fun z' => Work.Construction.Fstar (pExp α) z' θ + SG α g z' θ τ)
        = (fun z' => Work.Construction.Fstar (pExp α) z' θ)
          + (fun z' => SG α g z' θ τ) from rfl,
      deriv_add hdF hdG]
  ring

/-! ## §4 The `Γ`-weighted bounds of the sanitised family -/

/-- `|g̃| ≤ K·Γ` on the closed box `z ≥ 0, θ ∈ Iθ, τ ∈ [0,S]`. -/
theorem SG_gam_le {α S K : ℝ} {g : Fam} (hK0 : 0 ≤ K)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g)
    (h00 : ∀ τ : ℝ, τ ∈ Set.Icc 0 S → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed 0 0 (slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      |SG α g z θ τ| ≤ K * Gmp α θ := by
  intro z θ τ hz hθ hτ
  rcases eq_or_lt_of_le hz with h | h
  · subst h
    rw [SG_apply_of_nonpos le_rfl, abs_zero]
    exact mul_nonneg hK0 (Gmp_nonneg hθ)
  · rw [SG_slice_eq_of_pos h hθ hτ.1]
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      simp only [slice]
      rw [(hmin.vanish τ hτ.1 z h.le).1, abs_zero]
      exact mul_nonneg hK0 (Gmp_nonneg hθ)
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · calc |slice g τ z θ|
            = |Work.Spaces.mixed 0 0 (slice g τ) z θ| := rfl
          _ ≤ K * Work.FTS.RegExportIface.ω α z θ := h00 τ hτ z θ h h0 h1
          _ ≤ K * Gmp α θ :=
              mul_le_mul_of_nonneg_left
                (Work.FTS_RegExport.RXT.omega_le_Gamma α z θ h.le hθ) hK0
      · subst h1
        simp only [slice]
        rw [(hmin.vanish τ hτ.1 z h.le).2, abs_zero]
        exact mul_nonneg hK0 (Gmp_nonneg hθ)

/-- `|D_θg̃| ≤ K·Γ` on the closed box. -/
theorem Dth_SG_gam_le {α S K : ℝ} {g : Fam} (hK0 : 0 ≤ K)
    (h01 : ∀ τ : ℝ, τ ∈ Set.Icc 0 S → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed 0 1 (slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      |Work.Spaces.Dth (fun z θ => SG α g z θ τ) z θ| ≤ K * Gmp α θ := by
  intro z θ τ hz hθ hτ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [show Work.Spaces.Dth (fun z θ => SG α g z θ τ) z 0
          = Real.sin (2 * 0) * Work.Spaces.pth (fun z θ => SG α g z θ τ) z 0 from rfl]
    simp only [mul_zero, Real.sin_zero, zero_mul, abs_zero]
    exact mul_nonneg hK0 (Gmp_nonneg hθ)
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · rcases eq_or_lt_of_le hz with hz0 | hzp
      · subst hz0
        rw [show Work.Spaces.Dth (fun z θ => SG α g z θ τ) 0 θ
              = Real.sin (2 * θ) * deriv (fun θ' => SG α g 0 θ' τ) θ from rfl]
        have hzero : (fun θ' => SG α g 0 θ' τ) = fun _ => (0 : ℝ) :=
          funext (fun θ' => SG_apply_of_nonpos le_rfl)
        rw [hzero, deriv_const, mul_zero, abs_zero]
        exact mul_nonneg hK0 (Gmp_nonneg hθ)
      · rw [Dth_SG_eq_mixed hzp ⟨h0, h1⟩ hτ.1]
        calc |Work.Spaces.mixed 0 1 (slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ :=
              h01 τ hτ z θ hzp h0 h1
          _ ≤ K * Gmp α θ :=
              mul_le_mul_of_nonneg_left
                (Work.FTS_RegExport.RXT.omega_le_Gamma α z θ hzp.le hθ) hK0
    · subst h1
      rw [show Work.Spaces.Dth (fun z θ => SG α g z θ τ) z (π / 2)
            = Real.sin (2 * (π / 2)) * Work.Spaces.pth (fun z θ => SG α g z θ τ) z (π / 2)
            from rfl]
      simp only [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi, zero_mul, abs_zero]
      exact mul_nonneg hK0 (Gmp_nonneg hθ)

/-- `|D_zg̃| ≤ K·Γ` on the closed box. -/
theorem Dz_SG_gam_le {α S K : ℝ} {g : Fam} (hK0 : 0 ≤ K)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g)
    (h10 : ∀ τ : ℝ, τ ∈ Set.Icc 0 S → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed 1 0 (slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      |Work.Spaces.Dz (fun z θ => SG α g z θ τ) z θ| ≤ K * Gmp α θ := by
  intro z θ τ hz hθ hτ
  rcases eq_or_lt_of_le hz with hz0 | hzp
  · subst hz0
    rw [show Work.Spaces.Dz (fun z θ => SG α g z θ τ) 0 θ
          = 0 * Work.Spaces.pz (fun z θ => SG α g z θ τ) 0 θ from rfl]
    simp only [zero_mul, abs_zero]
    exact mul_nonneg hK0 (Gmp_nonneg hθ)
  · rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [show Work.Spaces.Dz (fun z θ => SG α g z θ τ) z 0
            = z * deriv (fun z' => SG α g z' 0 τ) z from rfl]
      have hzero : (fun z' => SG α g z' 0 τ) = fun _ => (0 : ℝ) :=
        funext (fun z' => SG_slice_zero_left hmin hτ.1 z')
      rw [hzero, deriv_const, mul_zero, abs_zero]
      exact mul_nonneg hK0 (Gmp_nonneg hθ)
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · rw [Dz_SG_eq_mixed hzp hθ hτ.1]
        calc |Work.Spaces.mixed 1 0 (slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ :=
              h10 τ hτ z θ hzp h0 h1
          _ ≤ K * Gmp α θ :=
              mul_le_mul_of_nonneg_left
                (Work.FTS_RegExport.RXT.omega_le_Gamma α z θ hzp.le hθ) hK0
      · subst h1
        rw [show Work.Spaces.Dz (fun z θ => SG α g z θ τ) z (π / 2)
              = z * deriv (fun z' => SG α g z' (π / 2) τ) z from rfl]
        have hzero : (fun z' => SG α g z' (π / 2) τ) = fun _ => (0 : ℝ) :=
          funext (fun z' => SG_slice_zero_right hmin hτ.1 z')
        rw [hzero, deriv_const, mul_zero, abs_zero]
        exact mul_nonneg hK0 (Gmp_nonneg hθ)

/-! ## §5 The `z = 0` and `θ ∈ {0, π/2}` slices of `F_τ` -/

/-- `F_τ(0,θ) = 0` for every `θ`. -/
theorem Fp_zero_z {α τ θ : ℝ} {g : Fam} : Fp α g τ 0 θ = 0 := by
  show Work.Construction.Fstar (pExp α) 0 θ + SG α g 0 θ τ = 0
  rw [show Work.Construction.Fstar (pExp α) 0 θ = 0 by
        rw [Work.Construction.Fstar, Work.FTS.Regularity.fmFstar_zero]; ring,
      SG_apply_of_nonpos le_rfl, add_zero]

/-- `D_θF_τ(0,θ) = 0` for every `θ`. -/
theorem FpDth_zero_z {α τ θ : ℝ} {g : Fam} : Work.Spaces.Dth (Fp α g τ) 0 θ = 0 := by
  rw [show Work.Spaces.Dth (Fp α g τ) 0 θ
        = Real.sin (2 * θ) * deriv (fun θ' => Fp α g τ 0 θ') θ from rfl]
  have hzero : (fun θ' => Fp α g τ 0 θ') = fun _ => (0 : ℝ) := funext (fun θ' => Fp_zero_z)
  rw [hzero, deriv_const, mul_zero]

/-- `D_zF_τ(z,0) = 0` for every `z`. -/
theorem FpDz_zero_left {α τ z : ℝ} {g : Fam} (hα : 0 < α)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (hτ : 0 ≤ τ) :
    Work.Spaces.Dz (Fp α g τ) z 0 = 0 := by
  rw [show Work.Spaces.Dz (Fp α g τ) z 0
        = z * deriv (fun z' => Fp α g τ z' 0) z from rfl]
  have hzero : (fun z' => Fp α g τ z' 0) = fun _ => (0 : ℝ) := by
    funext z'
    show Work.Construction.Fstar (pExp α) z' 0 + SG α g z' 0 τ = 0
    rw [fstar_pExp_zero_left hα, SG_slice_zero_left hmin hτ z', add_zero]
  rw [hzero, deriv_const, mul_zero]

/-- `D_zF_τ(z,π/2) = 0` for every `z`. -/
theorem FpDz_zero_right {α τ z : ℝ} {g : Fam} (hα : 0 < α)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (hτ : 0 ≤ τ) :
    Work.Spaces.Dz (Fp α g τ) z (π / 2) = 0 := by
  rw [show Work.Spaces.Dz (Fp α g τ) z (π / 2)
        = z * deriv (fun z' => Fp α g τ z' (π / 2)) z from rfl]
  have hzero : (fun z' => Fp α g τ z' (π / 2)) = fun _ => (0 : ℝ) := by
    funext z'
    show Work.Construction.Fstar (pExp α) z' (π / 2) + SG α g z' (π / 2) τ = 0
    rw [fstar_pExp_zero_right hα, SG_slice_zero_right hmin hτ z', add_zero]
  rw [hzero, deriv_const, mul_zero]

/-! ## §6 The target -/

/-- The three factors `F_τ`, `D_θF_τ`, `D_zF_τ` of the product slots of `EllProd_C1JetFull` are
`Γ`-shaped on the whole box `z ≥ 0, θ ∈ Iθ, τ ∈ [0,S]`: each is bounded by `B·Γ(θ)` with
`Γ = Gmp α = Work.FTS.Regularity.Gamma α = Work.Spaces.Gam (pExp α)`.
Route: `Fp α g τ = Fstar (pExp α) + slice (gS α (tauExt g)) τ` (definitional) and on the open
quadrant with `τ ∈ [0,S]` the second piece is `slice g τ` (`RXR5.SG_apply_of_pos`,
`FinalV2.tauExt_of_nonneg`), so `RXT.weighted_system`'s Γ-weighted slot bounds
(`∀ k : Fin 6, |mixed (idx k).1 (idx k).2 (slice g τ)| ≤ K·ω α z θ`,
`idx = ![(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]`) control `g̃`, `D_θg̃ = mixed 0 1`, `D_zg̃ = mixed 1 0`
by `K·ω ≤ K·Γ` (`RegExportIface.ω α z θ = z²Gamma α θ/(1+z)² ≤ Gamma α θ` for `z ≥ 0`); the
static profile part is explicit (`Fstar (pExp α) z θ = pExp α·(Gamma α θ/c(pExp α))·FM.Fstar z`,
`c` bounded below, `FM.Fstar` and `deriv FM.Fstar` bounded).  At `z = 0` all three vanish
identically in `θ` (the `θ`-slice of `F_τ` at `z = 0` is `0` for all `θ`, so `D_θF_τ(0,θ,τ) = 0`,
and `D_zF_τ(0,θ,τ) = 0·pz = 0`); at `θ ∈ {0,π/2}` all three vanish too (`Gam` vanishes there,
`RegPkgMin.vanish` of `hOK.1.1` kills `g`). -/
theorem factor_gam_bounds {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ z θ τ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.Fp α g τ z θ|
          ≤ B * Work.FTS_RegExport.RXR5L.Gmp α θ) ∧
      (∀ z θ τ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.FpDth α g τ z θ|
          ≤ B * Work.FTS_RegExport.RXR5L.Gmp α θ) ∧
      (∀ z θ τ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.FpDz α g τ z θ|
          ≤ B * Work.FTS_RegExport.RXR5L.Gmp α θ) := by
  have hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g := hOK.1.1
  obtain ⟨K, hK⟩ := Work.FTS_RegExport.RXT.weighted_system (α := α) (Ce := Ce) (C₀ := C₀)
    (Cs := Cs) (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  set K' : ℝ := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right K 0
  have hKb : ∀ (k : Fin 6) (τ : ℝ), τ ∈ Set.Icc 0 S → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < π / 2 → |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2 (slice g τ) z θ|
        ≤ K' * Work.FTS.RegExportIface.ω α z θ := by
    intro k τ hτ z θ hz hθ0 hθ1
    have h1 := hK k τ hτ z θ hz hθ0 hθ1
    have h2 : (0 : ℝ) ≤ Work.FTS.RegExportIface.ω α z θ :=
      Work.FTS_RegExport.RXT.omega_nonneg_of α z θ hz.le ⟨hθ0.le, hθ1.le⟩
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left K 0) h2)
  have h00 : ∀ τ : ℝ, τ ∈ Set.Icc 0 S → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed 0 0 (slice g τ) z θ| ≤ K' * Work.FTS.RegExportIface.ω α z θ := by
    intro τ hτ z θ hz h0 h1
    have h := hKb 0 τ hτ z θ hz h0 h1
    norm_num [Work.FTS.RegExportIface.RXT.idx] at h
    exact h
  have h01 : ∀ τ : ℝ, τ ∈ Set.Icc 0 S → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed 0 1 (slice g τ) z θ| ≤ K' * Work.FTS.RegExportIface.ω α z θ := by
    intro τ hτ z θ hz h0 h1
    have h := hKb 2 τ hτ z θ hz h0 h1
    norm_num [Work.FTS.RegExportIface.RXT.idx] at h
    exact h
  have h10 : ∀ τ : ℝ, τ ∈ Set.Icc 0 S → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed 1 0 (slice g τ) z θ| ≤ K' * Work.FTS.RegExportIface.ω α z θ := by
    intro τ hτ z θ hz h0 h1
    have h := hKb 1 τ hτ z θ hz h0 h1
    norm_num [Work.FTS.RegExportIface.RXT.idx] at h
    exact h
  have hB0 : 0 ≤ 20 + K' := by linarith
  refine ⟨20 + K', hB0, ?_, ?_, ?_⟩
  · -- ## (1) `F_τ`
    intro z θ τ hz hθ hτ
    rw [show Fp α g τ z θ = Work.Construction.Fstar (pExp α) z θ + SG α g z θ τ from rfl]
    refine le_trans (abs_add_le _ _) ?_
    rw [show (20 + K') * Gmp α θ = 20 * Gmp α θ + K' * Gmp α θ by ring]
    exact add_le_add (fstar_pExp_abs_le_gam hα hα13 hz hθ) (SG_gam_le hK'0 hmin h00 z θ τ hz hθ hτ)
  · -- ## (2) `D_θF_τ`
    intro z θ τ hz hθ hτ
    have hsplit := Dth_Ftau_eq_strip (α := α) (S := S) (g := g)
      (fun τ hτ => hmin.c4 τ hτ) hτ hz hθ
    rw [show FpDth α g τ z θ = Work.Spaces.Dth (Fp α g τ) z θ from rfl,
      show Work.Spaces.Dth (Fp α g τ) z θ
        = Work.Spaces.Dth (fun z θ => Work.Construction.Ftau (pExp α) (SG α g) τ z θ) z θ
        from rfl, ← hsplit]
    refine le_trans (abs_add_le _ _) ?_
    rw [show (20 + K') * Gmp α θ = 20 * Gmp α θ + K' * Gmp α θ by ring]
    exact add_le_add (dth_Fstar_gam_le hα hα13 hz hθ) (Dth_SG_gam_le hK'0 h01 z θ τ hz hθ hτ)
  · -- ## (3) `D_zF_τ`
    intro z θ τ hz hθ hτ
    rcases eq_or_lt_of_le hz with hz0 | hzp
    · subst hz0
      rw [show FpDz α g τ 0 θ = Work.Spaces.Dz (Fp α g τ) 0 θ from rfl,
        show Work.Spaces.Dz (Fp α g τ) 0 θ
            = 0 * Work.Spaces.pz (Fp α g τ) 0 θ from rfl]
      simp only [zero_mul, abs_zero]
      exact mul_nonneg hB0 (Gmp_nonneg hθ)
    · rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        rw [show FpDz α g τ z 0 = Work.Spaces.Dz (Fp α g τ) z 0 from rfl,
          FpDz_zero_left hα hmin hτ.1, abs_zero]
        exact mul_nonneg hB0 (Gmp_nonneg hθ)
      · rcases lt_or_eq_of_le hθ.2 with h1 | h1
        · have hsplit := Dz_Fp_split (α := α) (τ := τ) (g := g) (z := z) (θ := θ)
            (hmin.c4 τ hτ.1) hτ.1 hzp h0 h1
          rw [show FpDz α g τ z θ = Work.Spaces.Dz (Fp α g τ) z θ from rfl, hsplit]
          refine le_trans (abs_add_le _ _) ?_
          rw [show (20 + K') * Gmp α θ = 20 * Gmp α θ + K' * Gmp α θ by ring]
          refine add_le_add ?_ (Dz_SG_gam_le hK'0 hmin h10 z θ τ hzp.le hθ hτ)
          exact le_trans (dz_Fstar_gam_le hα hα13 hzp.le hθ)
            (mul_le_mul_of_nonneg_right (by norm_num) (Gmp_nonneg hθ))
        · subst h1
          rw [show FpDz α g τ z (π / 2) = Work.Spaces.Dz (Fp α g τ) z (π / 2) from rfl,
            FpDz_zero_right hα hmin hτ.1, abs_zero]
          exact mul_nonneg hB0 (Gmp_nonneg hθ)

end Work.FTS_RegExport.RXR5L
