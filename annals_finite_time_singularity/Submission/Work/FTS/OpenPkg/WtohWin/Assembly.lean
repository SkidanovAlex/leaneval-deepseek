import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false

/-! ## The algebraic identity `𝒰 = -(ℛ - 𝒱)` at `θ = π/4`

`ℛ(Ψ) = (2 sin θ·Ψ + α sin θ·z∂_zΨ + cos θ·∂_θΨ)/cos θ` and `𝒱 = ∂_θΨ - tan θ·Ψ`, so
`ℛ - 𝒱 = tan θ·(3Ψ + α z ∂_zΨ) = -tan θ·𝒰`; at `θ = π/4`, where `tan = 1`, this is exactly
`𝒰 = -(ℛ - 𝒱)`.  That is the anchor of the bound: both `ℛ` and `𝒱` are bounded by `StarPkg`. -/

/-- `ℛ(Ψ) - 𝒱(Ψ) = tan θ·(3Ψ + α z ∂_zΨ)` wherever `cos θ ≠ 0`. -/
theorem Rop_sub_Vop_eq_tan (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Construction.Rop α Ψ z θ - Work.Construction.Vop Ψ z θ
      = Real.tan θ * (3 * Ψ z θ + α * z * Work.Spaces.pz Ψ z θ) := by
  simp only [Work.Construction.Rop, Work.Construction.Vop, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- At `θ = π/4` the coefficient identity reads `ℛ - 𝒱 = 3Ψ + α z ∂_zΨ`. -/
theorem Rop_sub_Vop_pi_div_four (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.Rop α Ψ z (π / 4) - Work.Construction.Vop Ψ z (π / 4)
      = 3 * Ψ z (π / 4) + α * z * Work.Spaces.pz Ψ z (π / 4) := by
  have hc : Real.cos (π / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  rw [Rop_sub_Vop_eq_tan α Ψ hc, Real.tan_pi_div_four, one_mul]

/-- `𝒰(Ψ) = -(ℛ(Ψ) - 𝒱(Ψ))` at `θ = π/4`. -/
theorem Uop_pi_div_four (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.Uop α Ψ z (π / 4)
      = -(Work.Construction.Rop α Ψ z (π / 4) - Work.Construction.Vop Ψ z (π / 4)) := by
  rw [Rop_sub_Vop_pi_div_four]
  simp only [Work.Construction.Uop]
  ring

/-! ## `SmoothQuad` of `𝒰(Φ̃_*)`

For the mean-value step we need the `θ`-slices of `𝒰(Φ̃_*)` to be `C^∞` on `(0,π/2)`.  The
function `𝒰` is built from the datum and its `z`-derivative, so it preserves
`Work.FTS.LocData.SmoothQuad` (`contDiffOn_pz`); for the datum we use
`Φ̃_* = Φ_s - Θ_*(α)` with `Θ_*(α)(z,θ) = sin(2θ)/(2(1+z))` on `z > -1`, the profile identity
`L₁₂(F_*)(z) = 2α/(1+z)` of `FstarPkg`. -/

/-- The singular part `Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant `z > -1`,
`0 < θ < π/2`, where it is the explicit function `(z,θ) ↦ sin(2θ)/(2(1+z))`. -/
theorem smoothQuad_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Work.Spaces.quadU := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.Spaces.quadU :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Work.Spaces.quadU, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := Set.mem_Ioi.mp hp.1
        linarith
      positivity
    exact hnum.div hden hne
  refine hsmooth.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := Set.mem_Ioi.mp hp.1
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz]
  field_simp
  ring

/-- `Φ̃_* = Φ_s - Θ_*(α)` is `C^∞` on the open quadrant when `Φ_s` is. -/
theorem smoothQuad_PhiTs {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.LocData.SmoothQuad Φs) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
  have hTheta : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) := smoothQuad_Theta_Fstar hα hα1
  show Work.FTS.LocData.SmoothQuad
    (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
  exact Work.FTS.LocData.smoothQuad_sub hs hTheta

/-- `𝒰(Ψ) = -3Ψ - α·D_zΨ`, so it preserves `C^∞`-smoothness on the open quadrant. -/
theorem Uop_eq_neg_three_sub_Dz (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Construction.Uop α f = fun z θ => -3 * f z θ - α * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Construction.Uop, Work.Spaces.Dz]
  ring

/-- `𝒰` preserves `SmoothQuad`. -/
theorem smoothQuad_Uop {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α f) := by
  rw [Uop_eq_neg_three_sub_Dz]
  refine Work.FTS.LocData.smoothQuad_sub ?_ ?_
  · exact Work.FTS.LocData.smoothQuad_const_mul (-3) h
  · have h1 : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz f) := by
      simpa using Work.FTS.LocData.SmoothQuad.DzIter h 1
    exact Work.FTS.LocData.smoothQuad_const_mul α h1



end Work.FTS.Nonlinear.Pieces.Rl1
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-! ## Elementary facts about the weights -/

theorem Pss_hKer_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Work.Spaces.hKer r := by
  rw [Work.Spaces.hKer_apply]
  exact div_nonneg hr (by positivity)

theorem Pss_hKer_le_one {r : ℝ} (hr : 0 ≤ r) : Work.Spaces.hKer r ≤ 1 := by
  rw [Work.Spaces.hKer_apply, div_le_one (by positivity)]
  nlinarith

/-- `K(θ) = 3 sin θ cos²θ` is bounded by `3` on `Iθ`. -/
theorem Pss_K_abs_le {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.K θ| ≤ 3 := by
  rw [Work.Spaces.K, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2)]
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h3 : |(3 : ℝ)| = 3 := by norm_num
  rw [h3]
  have h4 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [h2, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have h5 : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 := by
    have h := mul_le_mul h1 h4 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  nlinarith [h5]

/-- `K(θ) ≥ 0` on `Iθ`. -/
theorem Pss_K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  obtain ⟨h1, h2⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨h1, by linarith [Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h2⟩
  rw [Work.Spaces.K]
  positivity

theorem Pss_K_zero_left : Work.Spaces.K (0 : ℝ) = 0 := by simp [Work.Spaces.K]

theorem Pss_K_zero_right : Work.Spaces.K (Real.pi / 2) = 0 := by
  rw [Work.Spaces.K, Real.cos_pi_div_two]
  ring

theorem Pss_sin_two_zero_left {p : ℝ} (hp : p ≠ 0) : Real.sin (2 * (0 : ℝ)) ^ p = 0 := by
  rw [show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero, Real.zero_rpow hp]

theorem Pss_sin_two_zero_right {p : ℝ} (hp : p ≠ 0) :
    Real.sin (2 * (Real.pi / 2)) ^ p = 0 := by
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, Real.zero_rpow hp]

/-- `|H(z)| ≤ 2 h(z)` on `z ≥ 0` for `H(z) = 2z(1-z)/(1+z)³` and `h(z) = z/(1+z)²`. -/
theorem Pss_HLz_le {r : ℝ} (hr : 0 ≤ r) :
    |Work.FTS.Nonlinear.FstarPkg.Hz r| ≤ 2 * Work.Spaces.hKer r := by
  rw [Work.FTS.Nonlinear.FstarPkg.Hz, Work.Spaces.hKer_apply]
  rcases eq_or_lt_of_le hr with h | h
  · subst h; norm_num
  · have h1 : 0 < (1 + r) ^ 3 := by positivity
    have h2 : 0 < (1 + r) ^ 2 := by positivity
    rw [abs_div, abs_of_pos h1, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hr]
    have habs : |1 - r| ≤ 1 + r := abs_le.mpr ⟨by linarith, by linarith⟩
    have hfac : 0 ≤ 2 * r * (1 + r) ^ 2 := by positivity
    have key : 2 * r * |1 - r| * (1 + r) ^ 2 ≤ 2 * r * (1 + r) ^ 3 := by
      calc 2 * r * |1 - r| * (1 + r) ^ 2
          = (2 * r * (1 + r) ^ 2) * |1 - r| := by ring
        _ ≤ (2 * r * (1 + r) ^ 2) * (1 + r) := mul_le_mul_of_nonneg_left habs hfac
        _ = 2 * r * (1 + r) ^ 3 := by ring
    rw [show (2 * (r / (1 + r) ^ 2)) = 2 * r / (1 + r) ^ 2 from by ring]
    rw [div_le_div_iff₀ h1 h2]
    exact key

/-! ## The pointwise shape of `F_*`, `∂_θF_*` and `D_zF_*` -/

theorem Pss_Fstar_le (α r θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α r θ| ≤ 20 * α * Work.Spaces.hKer r := by
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α :=
    Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hGam : |Work.Spaces.Gam α θ| ≤ 1 := by
    obtain ⟨h1, h2⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg h1]; exact h2
  rw [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored α]
  simp only
  rw [abs_mul, abs_mul, abs_of_nonneg hker0]
  have h2 : |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ| ≤ (20 * α) * 1 :=
    calc |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ|
        ≤ (20 * α) * |Work.Spaces.Gam α θ| :=
          mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      _ ≤ (20 * α) * 1 :=
          mul_le_mul_of_nonneg_left hGam (mul_nonneg (by norm_num) hα.le)
  have h3 : |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ| * Work.Spaces.hKer r
      ≤ (20 * α) * 1 * (1 * Work.Spaces.hKer r) :=
    mul_le_mul h2 (by rw [one_mul]) hker0
      (mul_nonneg (mul_nonneg (by norm_num) hα.le) (by norm_num))
  calc |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ| * Work.Spaces.hKer r
      ≤ (20 * α) * 1 * (1 * Work.Spaces.hKer r) := h3
    _ = 20 * α * Work.Spaces.hKer r := by ring

theorem Pss_pth_Fstar_le (α r θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r) :
    |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ 20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r := by
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α :=
    Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hfun : Work.Spaces.pth (Work.Construction.Fstar α) r θ
      = (2 * α / Work.Spaces.c α * Work.Spaces.hKer r)
          * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ := by
    rw [Work.Spaces.pth]
    have hc : (fun θ' : ℝ => Work.Construction.Fstar α r θ')
        = fun θ' : ℝ =>
            (2 * α / Work.Spaces.c α * Work.Spaces.hKer r) * Work.Spaces.Gam α θ' := by
      funext θ'
      rw [congrFun (congrFun (Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored α) r) θ']
      ring
    rw [hc, Work.Spaces.deriv_const_mul']
  rw [hfun, abs_mul, abs_mul, abs_of_nonneg hker0]
  have h2 : |2 * α / Work.Spaces.c α| * Work.Spaces.hKer r ≤ 20 * α * Work.Spaces.hKer r :=
    mul_le_mul_of_nonneg_right hcoef hker0
  calc |2 * α / Work.Spaces.c α| * Work.Spaces.hKer r
        * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      = (|2 * α / Work.Spaces.c α| * Work.Spaces.hKer r)
          * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| := by ring
    _ ≤ (20 * α * Work.Spaces.hKer r) * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    _ = 20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r := by ring

theorem Pss_Dz_Fstar_le (α r θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar α) r θ| ≤ 40 * α * Work.Spaces.hKer r := by
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hGam : |Work.Spaces.Gam α θ| ≤ 1 := by
    obtain ⟨h1, h2⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg h1]; exact h2
  rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith : (-1 : ℝ) < r)]
  rw [abs_mul, abs_mul]
  have h2 : |Work.Spaces.Gam α θ| * |Work.FTS.Nonlinear.FstarPkg.Hz r|
      ≤ 2 * (2 * Work.Spaces.hKer r) :=
    mul_le_mul (le_trans hGam (by norm_num)) (Pss_HLz_le hr) (abs_nonneg _) (by norm_num)
  calc |α / Work.Spaces.c α| * (|Work.Spaces.Gam α θ| * |Work.FTS.Nonlinear.FstarPkg.Hz r|)
      ≤ (10 * α) * (2 * (2 * Work.Spaces.hKer r)) :=
        mul_le_mul hcoef h2 (by positivity) (by positivity)
    _ = 40 * α * Work.Spaces.hKer r := by ring

/-! ## The angular derivative of `Γ` -/

/-- On the open interval, `Γ' = α q Γ / sin(2θ)`. -/
theorem Pss_Gam_deriv_eq {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h := Work.Spaces.dthU_Gam α θ hα hθ
  rw [Work.Spaces.dthU] at h
  exact (eq_div_iff hsin2.ne').mpr (by rw [mul_comm]; exact h)

/-- `|q(θ)| = |cos 2θ - 1/3| ≤ 4/3`. -/
theorem Pss_qfun_abs_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun, abs_le]
  constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]

/-- On the open interval, `|Γ'| ≤ (4α/3)·Γ/sin(2θ)`. -/
theorem Pss_Gam_deriv_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (4 * α / 3) * (Work.Spaces.Gam α θ / Real.sin (2 * θ)) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hq := Pss_qfun_abs_le θ
  have hd := Pss_Gam_deriv_eq hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα ⟨hθ.1.le, hθ.2.le⟩).1
  rw [hd, abs_div, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hsin2, abs_of_nonneg hG0]
  have h3 : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
      ≤ (4 * α / 3) * Work.Spaces.Gam α θ := by
    nlinarith [hq, hG0, hα, mul_nonneg hα.le hG0]
  calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Real.sin (2 * θ)
      ≤ ((4 * α / 3) * Work.Spaces.Gam α θ) / Real.sin (2 * θ) :=
        div_le_div_of_nonneg_right h3 hsin2.le
    _ = (4 * α / 3) * (Work.Spaces.Gam α θ / Real.sin (2 * θ)) := by ring

/-- `K(θ)·|Γ'(θ)| ≤ 2α` on the closed angular interval. -/
theorem Pss_K_deriv_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · subst h0
    rw [Pss_K_zero_left, zero_mul]
    linarith [hα]
  rcases lt_or_eq_of_le hθ1 with h1 | h1
  · have hsin2 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hcosθ : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], h1⟩
    have hq := Pss_qfun_abs_le θ
    have hd := Pss_Gam_deriv_eq hα ⟨h0, h1⟩
    have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
      (Work.Spaces.Gam_bounds α θ hα ⟨hθ0, hθ1⟩).1
    have hG1 : Work.Spaces.Gam α θ ≤ 1 :=
      (Work.Spaces.Gam_bounds α θ hα ⟨hθ0, hθ1⟩).2
    rw [hd, abs_div, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hsin2, abs_of_nonneg hG0]
    have hratio : Work.Spaces.K θ * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
          / Real.sin (2 * θ))
        = (3 * Real.cos θ / 2) * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ) := by
      have hsne : Real.sin θ ≠ 0 := ne_of_gt hsinθ
      have hcne : Real.cos θ ≠ 0 := ne_of_gt hcosθ
      rw [Work.Spaces.K, Real.sin_two_mul]
      rw [show (3 * Real.sin θ * Real.cos θ ^ 2)
            * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
              / (2 * Real.sin θ * Real.cos θ))
          = (3 * Real.sin θ * Real.cos θ ^ 2 / (2 * Real.sin θ * Real.cos θ))
            * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ) from by ring]
      rw [show 3 * Real.sin θ * Real.cos θ ^ 2 / (2 * Real.sin θ * Real.cos θ)
          = 3 * Real.cos θ / 2 from by field_simp]
    rw [hratio]
    have h1' : α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
        ≤ α * (4 / 3) * Work.Spaces.Gam α θ := by
      nlinarith [hq, hG0, hα, mul_nonneg hα.le hG0]
    have h2' : (3 * Real.cos θ / 2) * (α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ)
        ≤ (3 * Real.cos θ / 2) * (α * (4 / 3) * Work.Spaces.Gam α θ) :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    have h4 : (3 * Real.cos θ / 2) * (α * (4 / 3) * Work.Spaces.Gam α θ)
        ≤ (3 * Real.cos θ / 2) * (α * (4 / 3) * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG1 (by positivity)) (by positivity)
    have h5 : (3 * Real.cos θ / 2) * (α * (4 / 3) * 1) ≤ 2 * α := by
      nlinarith [Real.cos_le_one θ, hα, hcosθ.le]
    linarith [h2', h4, h5]
  · subst h1
    rw [Pss_K_zero_right, zero_mul]
    linarith [hα]

/-- On the open interval, `3 cos³θ·|Γ'| ≤ 4α·sin(2θ)^{α/5-1}`. -/
theorem Pss_K_Gam_deriv_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 4 * α * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by
  have hsin2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hGderiv := Pss_Gam_deriv_le hα hθ
  have hG := Work.FTS.Nonlinear.FstarPkg.Gam_le_sin_two_rpow hα ⟨hθ.1.le, hθ.2.le⟩
  have hsplit : (Real.sin (2 * θ)) ^ (α / 5)
      = (Real.sin (2 * θ)) ^ (α / 5 - 1) * Real.sin (2 * θ) := by
    have h := Real.rpow_add hsin2 (α / 5 - 1) 1
    rw [Real.rpow_one] at h
    rw [show α / 5 - 1 + 1 = α / 5 by ring] at h
    exact h
  have hGam_le : Work.Spaces.Gam α θ / Real.sin (2 * θ)
      ≤ (Real.sin (2 * θ)) ^ (α / 5 - 1) := by
    rw [div_le_iff₀ hsin2]
    calc Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := hG
      _ = (Real.sin (2 * θ)) ^ (α / 5 - 1) * Real.sin (2 * θ) := hsplit
  have hcos3 : Real.cos θ ^ 3 ≤ 1 := pow_le_one₀ hcos.le (Real.cos_le_one θ)
  calc 3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 3 * 1 * ((4 * α / 3) * (Work.Spaces.Gam α θ / Real.sin (2 * θ))) := by
        have h31 : 3 * Real.cos θ ^ 3 ≤ 3 * 1 := by nlinarith [hcos3]
        exact mul_le_mul h31 hGderiv (abs_nonneg _) (by positivity)
    _ ≤ 3 * 1 * ((4 * α / 3) * (Real.sin (2 * θ)) ^ (α / 5 - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hGam_le (by positivity)
    _ = 4 * α * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by ring

/-! ## The relation `V = R + tan θ · U` -/

theorem Pss_tan_Uop {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Real.tan θ * Work.Construction.Uop α Ψ z θ
      = Work.Construction.Vop Ψ z θ - Work.Construction.Rop α Ψ z θ := by
  simp only [Work.Construction.Uop, Work.Construction.Vop, Work.Construction.Rop]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## The measure-theoretic reduction -/

/-- Reduction step: a pointwise bound of the shape `|K θ · N r θ| ≤ C·h(r)·A(θ)` gives the
required weighted estimate with constant `C·M·2`, where `M` bounds `∫⁻ A`. -/
theorem PssReduce {N : ℝ → ℝ → ℝ} {C M : ℝ} {A : ℝ → ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hAnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A θ)
    (hA : ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (A θ) ≤ ENNReal.ofReal M)
    (hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.K θ * N r θ| ≤ C * Work.Spaces.hKer r * A θ) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|)) ≤ ENNReal.ofReal (C * M * 2) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (C * Work.Spaces.hKer r * M) := by
    intro r hr
    have hker0 : 0 ≤ Work.Spaces.hKer r := by
      rw [Work.Spaces.hKer_apply]; exact div_nonneg (le_of_lt hr) (by positivity)
    have hCk : 0 ≤ C * Work.Spaces.hKer r := mul_nonneg hC hker0
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (C * Work.Spaces.hKer r) * ENNReal.ofReal (A θ) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hpt r hr, MeasureTheory.ae_restrict_mem hIθm] with θ h1 h2
          calc ENNReal.ofReal |Work.Spaces.K θ * N r θ|
              ≤ ENNReal.ofReal (C * Work.Spaces.hKer r * A θ) :=
                ENNReal.ofReal_le_ofReal h1
            _ = ENNReal.ofReal (C * Work.Spaces.hKer r) * ENNReal.ofReal (A θ) :=
                ENNReal.ofReal_mul hCk
      _ = ENNReal.ofReal (C * Work.Spaces.hKer r)
            * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (A θ) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C * Work.Spaces.hKer r) * ENNReal.ofReal M :=
          mul_le_mul_right hA (ENNReal.ofReal (C * Work.Spaces.hKer r))
      _ = ENNReal.ofReal (C * Work.Spaces.hKer r * M) :=
          (ENNReal.ofReal_mul hCk).symm
  have houter : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * ENNReal.ofReal (C * Work.Spaces.hKer r * M) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_right (hinner r hr) (ENNReal.ofReal r⁻¹)
  have hcongr : (fun r : ℝ => ENNReal.ofReal r⁻¹
        * ENNReal.ofReal (C * Work.Spaces.hKer r * M))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun r : ℝ => ENNReal.ofReal (C * M) * ENNReal.ofReal (1 / (1 + r) ^ 2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hker0 : 0 ≤ Work.Spaces.hKer r := by
      rw [Work.Spaces.hKer_apply]; exact div_nonneg hr0.le (by positivity)
    have hCk : 0 ≤ C * Work.Spaces.hKer r := mul_nonneg hC hker0
    have hCM : 0 ≤ C * M := mul_nonneg hC hM
    have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
    have hkey : r⁻¹ * Work.Spaces.hKer r = 1 / (1 + r) ^ 2 := by
      rw [Work.Spaces.hKer_apply]
      field_simp
    calc ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * Work.Spaces.hKer r * M)
        = ENNReal.ofReal (r⁻¹ * (C * Work.Spaces.hKer r * M)) :=
            (ENNReal.ofReal_mul hinv).symm
      _ = ENNReal.ofReal (C * M * (r⁻¹ * Work.Spaces.hKer r)) := by
            rw [show r⁻¹ * (C * Work.Spaces.hKer r * M)
                = C * M * (r⁻¹ * Work.Spaces.hKer r) by ring]
      _ = ENNReal.ofReal (C * M * (1 / (1 + r) ^ 2)) := by rw [hkey]
      _ = ENNReal.ofReal (C * M) * ENNReal.ofReal (1 / (1 + r) ^ 2) :=
            ENNReal.ofReal_mul hCM
  rw [MeasureTheory.lintegral_congr_ae hcongr] at houter
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at houter
  refine le_trans houter ?_
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => 1 / (1 + r) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.Coercivity.rb_integrableOn_inv_one_add_sq_Iz.mono_set Set.Ioi_subset_Ici_self
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun r : ℝ => 1 / (1 + r) ^ 2) :=
    Filter.Eventually.of_forall fun r => by positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [← ENNReal.ofReal_mul (mul_nonneg hC hM)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hI : (∫ r in Set.Ioi (0 : ℝ), 1 / (1 + r) ^ 2) ≤ 2 := by
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact Work.Coercivity.rb_integral_Iz_inv_one_add_sq_le
  calc C * M * (∫ r in Set.Ioi (0 : ℝ), 1 / (1 + r) ^ 2) ≤ C * M * 2 :=
        mul_le_mul_of_nonneg_left hI (mul_nonneg hC hM)
    _ = C * M * 2 := rfl

/-! ## The angular integral for the `N₂` slot -/

theorem PssAngInt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Real.sin (2 * θ)) ^ (α / 5 - 1)))
      ≤ ENNReal.ofReal (500 / α) := by
  obtain ⟨hint, hle⟩ := Work.Spaces.sin_two_rpow (α / 5 - 1) (by linarith) (by linarith)
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (α / 5 - 1)) :=
    (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
      measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun θ hθ =>
        Real.rpow_nonneg (Work.FTS.Nonlinear.FstarPkg.sin_two_nonneg_of_mem_Iθ hθ) _)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_trans hle ?_
  rw [show α / 5 - 1 + 1 = α / 5 by ring]
  have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
  have heq : 100 / (α / 5) = 500 / α := by
    have hα5 : α / 5 ≠ 0 := div_ne_zero hαne (by norm_num)
    field_simp
    ring
  rw [heq]

/-! ## The five pointwise bounds -/

theorem Pss_N1ss_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs r θ|
        ≤ 120 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hR := (Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs).1 r hr θ hθ
  have hF := Pss_Fstar_le α r θ hα hα1 hr0 hθ
  have hK3 := Pss_K_abs_le hθ
  show |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Construction.Fstar α r θ)| ≤ 120 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Construction.Fstar α r θ)|
      = |Work.Spaces.K θ| * (2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Construction.Fstar α r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hLHS]
  have h2 : 2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
      ≤ 2 * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hR (by norm_num)
  calc |Work.Spaces.K θ| * (2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Construction.Fstar α r θ|
      ≤ 3 * (2 * (max Cs 0 * α)) * (20 * α * Work.Spaces.hKer r) := by
        refine mul_le_mul (mul_le_mul hK3 h2 (by positivity) (by norm_num)) hF
          (abs_nonneg _) (by positivity)
    _ = 120 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r := by ring

theorem Pss_N2ss_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2ss α Φs r θ|
        ≤ 320 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
            * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by
  intro r hr θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hne : α / 5 - 1 ≠ 0 := by linarith
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · subst h0
    rw [Pss_K_zero_left, Pss_sin_two_zero_left hne]
    simp
  rcases lt_or_eq_of_le hθ1 with h1 | h1
  · have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hcosθ : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], h1⟩
    have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two h0 h1
    have hKpos := Pss_K_nonneg ⟨hθ0, hθ1⟩
    obtain ⟨hRpt, hVpt, _⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
    have hR := hRpt r hr θ ⟨hθ0, hθ1⟩
    have hV := hVpt r hr0 θ ⟨hθ0, hθ1⟩
    have hUop : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 2 * max Cs 0 * α / Real.tan θ := by
      have hid := Pss_tan_Uop (α := α) (Ψ := Work.FTS.Nonlin.PhiTs α Φs) (z := r) (θ := θ)
        (ne_of_gt hcosθ)
      have h1' : Real.tan θ * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
          ≤ 2 * max Cs 0 * α := by
        calc Real.tan θ * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            = |Real.tan θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
              rw [abs_mul, abs_of_pos htan]
          _ = |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
                - Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by rw [hid]
          _ ≤ |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
                + |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
              rw [sub_eq_add_neg]
              simpa [abs_neg] using abs_add_le
                (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
                (-(Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ))
          _ ≤ 2 * max Cs 0 * α := by linarith
      exact (le_div_iff₀ htan).mpr (by rw [mul_comm]; exact h1')
    have hpth := Pss_pth_Fstar_le α r θ hα hα1 hr0
    have hG := Pss_K_Gam_deriv_le hα hα1 ⟨h0, h1⟩
    have hKsplit : Work.Spaces.K θ / Real.tan θ = 3 * Real.cos θ ^ 3 := by
      have hsne : Real.sin θ ≠ 0 := ne_of_gt hsinθ
      have hcne : Real.cos θ ≠ 0 := ne_of_gt hcosθ
      rw [Work.Spaces.K, Real.tan_eq_sin_div_cos]
      field_simp
    show |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
        ≤ 320 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
            * (Real.sin (2 * θ)) ^ (α / 5 - 1)
    have hLHS : |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
          * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
        = Work.Spaces.K θ * (2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
          * |Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hKpos]
      ring
    rw [hLHS]
    have hmul : Work.Spaces.K θ
          * (2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
          * |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
        ≤ Work.Spaces.K θ * (2 * (2 * max Cs 0 * α / Real.tan θ))
          * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r) := by
      have h1 : 2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
          ≤ 2 * (2 * max Cs 0 * α / Real.tan θ) :=
        mul_le_mul_of_nonneg_left hUop (by norm_num)
      refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hKpos) hpth (abs_nonneg _) (by positivity)
    refine le_trans hmul ?_
    rw [show Work.Spaces.K θ * (2 * (2 * max Cs 0 * α / Real.tan θ))
          * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r)
        = 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
          * (3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
        from by rw [← hKsplit]; ring]
    have hcoef : 0 ≤ 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_max_right Cs 0)) (sq_nonneg α))
        (Pss_hKer_nonneg hr0)
    calc 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
          * (3 * Real.cos θ ^ 3 * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
        ≤ 80 * max Cs 0 * α ^ 2 * Work.Spaces.hKer r
            * (4 * α * (Real.sin (2 * θ)) ^ (α / 5 - 1)) :=
          mul_le_mul_of_nonneg_left hG hcoef
      _ = 320 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
            * (Real.sin (2 * θ)) ^ (α / 5 - 1) := by ring
  · subst h1
    rw [Pss_K_zero_right, Pss_sin_two_zero_right hne]
    simp

theorem Pss_N3ss_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N3ss α Φs r θ|
        ≤ 240 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hV := (Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs).2.1 r hr0 θ hθ
  have hDz := Pss_Dz_Fstar_le α r θ hα hα1 hr0 hθ
  have hK3 := Pss_K_abs_le hθ
  show |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      ≤ 240 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      = |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Spaces.Dz (Work.Construction.Fstar α) r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hα.le]
    ring
  rw [hLHS]
  have h2 : 2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
      ≤ 2 * α * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hV (by positivity)
  calc |Work.Spaces.K θ| * (2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|)
        * |Work.Spaces.Dz (Work.Construction.Fstar α) r θ|
      ≤ 3 * (2 * α * (max Cs 0 * α)) * (40 * α * Work.Spaces.hKer r) := by
        refine mul_le_mul (mul_le_mul hK3 h2 (by positivity) (by norm_num)) hDz
          (abs_nonneg _) (by positivity)
    _ = 240 * max Cs 0 * α ^ 3 * Work.Spaces.hKer r := by ring

theorem Pss_N4ss_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4ss α r θ| ≤ 40 * α ^ 2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr0
  have hker1 : Work.Spaces.hKer r ≤ 1 := Pss_hKer_le_one hr0
  have hKgm := Pss_K_deriv_le hα hθ
  have hpth := Pss_pth_Fstar_le α r θ hα hα1 hr0
  have hFK := Work.FTS.Nonlinear.FstarPkg.FK_Fstar (z := r) hα hα1
  have hK0 := Pss_K_nonneg hθ
  have hFKval : |Work.Construction.FK (Work.Construction.Fstar α) r|
      = α * (2 * Work.Spaces.hKer r) := by
    rw [hFK, abs_of_nonneg (mul_nonneg hα.le (by positivity)), Work.Spaces.hKer_apply]
    ring
  show |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
      * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Spaces.pth (Work.Construction.Fstar α) r θ)| ≤ 40 * α ^ 2 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      = Work.Spaces.K θ * ((1 / 2) * |Work.Construction.s2 θ|)
        * |Work.Construction.FK (Work.Construction.Fstar α) r|
        * |Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg hK0]
    ring
  rw [hLHS, hFKval]
  have hs21 : |Work.Construction.s2 θ| ≤ 1 := by
    show |Real.sin (2 * θ)| ≤ 1
    exact abs_le.mpr ⟨Real.neg_one_le_sin (2 * θ), Real.sin_le_one (2 * θ)⟩
  have hstep : Work.Spaces.K θ * ((1 / 2) * |Work.Construction.s2 θ|)
        * (α * (2 * Work.Spaces.hKer r))
        * |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ Work.Spaces.K θ * ((1 / 2) * 1) * (α * (2 * Work.Spaces.hKer r))
        * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r) := by
    have h2 : (1 / 2) * |Work.Construction.s2 θ| ≤ (1 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hs21 (by norm_num)
    have h3 : Work.Spaces.K θ * ((1 / 2) * |Work.Construction.s2 θ|)
          * (α * (2 * Work.Spaces.hKer r))
        ≤ Work.Spaces.K θ * ((1 / 2) * 1) * (α * (2 * Work.Spaces.hKer r)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK0) (by positivity)
    exact mul_le_mul h3 hpth (abs_nonneg _) (by positivity)
  refine le_trans hstep ?_
  rw [show Work.Spaces.K θ * ((1 / 2) * 1) * (α * (2 * Work.Spaces.hKer r))
        * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * Work.Spaces.hKer r)
      = 20 * α ^ 2 * Work.Spaces.hKer r * Work.Spaces.hKer r
        * (Work.Spaces.K θ * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
      from by ring]
  have hker2 : Work.Spaces.hKer r * Work.Spaces.hKer r ≤ Work.Spaces.hKer r := by
    have h := mul_le_mul_of_nonneg_left hker1 hker0
    simpa using h
  calc 20 * α ^ 2 * Work.Spaces.hKer r * Work.Spaces.hKer r
        * (Work.Spaces.K θ * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|)
      ≤ 20 * α ^ 2 * Work.Spaces.hKer r * Work.Spaces.hKer r * (2 * α) :=
        mul_le_mul_of_nonneg_left hKgm (by positivity)
    _ = 40 * α ^ 3 * (Work.Spaces.hKer r * Work.Spaces.hKer r) := by ring
    _ ≤ 40 * α ^ 3 * Work.Spaces.hKer r :=
        mul_le_mul_of_nonneg_left hker2 (by positivity)
    _ ≤ 40 * α ^ 2 * Work.Spaces.hKer r :=
        mul_le_mul_of_nonneg_right (by nlinarith [hα, hα1]) hker0

theorem Pss_N5ss_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * Work.FTS.Nonlin.N5ss α r θ| ≤ 120 * α ^ 2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have hker0 : 0 ≤ Work.Spaces.hKer r := Pss_hKer_nonneg hr0
  have hker1 : Work.Spaces.hKer r ≤ 1 := Pss_hKer_le_one hr0
  have hF := Pss_Fstar_le α r θ hα hα1 hr0 hθ
  have hK3 := Pss_K_abs_le hθ
  have hFK := Work.FTS.Nonlinear.FstarPkg.FK_Fstar (z := r) hα hα1
  have hsin1 : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (Real.sin_le_one θ)
  show |Work.Spaces.K θ * (-(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Construction.Fstar α r θ)| ≤ 120 * α ^ 2 * Work.Spaces.hKer r
  have hLHS : |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Construction.Fstar α r θ)|
      = |Work.Spaces.K θ| * ((Real.sin θ) ^ 2
          * |Work.Construction.FK (Work.Construction.Fstar α) r|)
        * |Work.Construction.Fstar α r θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (sq_nonneg (Real.sin θ))]
    ring
  rw [hLHS]
  have hFKval : |Work.Construction.FK (Work.Construction.Fstar α) r|
      = α * (2 * Work.Spaces.hKer r) := by
    rw [hFK, abs_of_nonneg (mul_nonneg hα.le (by positivity)), Work.Spaces.hKer_apply]
    ring
  rw [hFKval]
  have h2 : (Real.sin θ) ^ 2 * (α * (2 * Work.Spaces.hKer r))
      ≤ 1 * (α * (2 * Work.Spaces.hKer r)) :=
    mul_le_mul_of_nonneg_right hsin1 (by positivity)
  calc |Work.Spaces.K θ| * ((Real.sin θ) ^ 2 * (α * (2 * Work.Spaces.hKer r)))
        * |Work.Construction.Fstar α r θ|
      ≤ 3 * (1 * (α * (2 * Work.Spaces.hKer r))) * (20 * α * Work.Spaces.hKer r) :=
        mul_le_mul (mul_le_mul hK3 h2 (by positivity) (by norm_num)) hF
          (abs_nonneg _) (by positivity)
    _ = 120 * α ^ 2 * (Work.Spaces.hKer r * Work.Spaces.hKer r) := by ring
    _ ≤ 120 * α ^ 2 * (Work.Spaces.hKer r * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hker1 hker0) (by positivity)
    _ = 120 * α ^ 2 * Work.Spaces.hKer r := by ring

theorem Pss {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2ss α Φs r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3ss α Φs r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4ss α r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5ss α r θ|))
        ≤ ENNReal.ofReal (K * α ^ 2) := by
  refine ⟨400000 * max Cs 0 + 1000, ?_, ?_⟩
  · have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
    linarith
  · intro α g Φs Φg hα hα1 hαα2 hN4 hGal hStar hEll
    have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
    have hπ := Real.pi_lt_four
    have hunit : ∀ θ : ℝ, (fun _ : ℝ => (1 : ℝ)) θ = 1 := fun θ => rfl
    have hA1 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) θ)) ≤ ENNReal.ofReal (Real.pi / 2) := by
      have h1 : (fun θ : ℝ => ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) θ))
          = fun _ : ℝ => (1 : ENNReal) := by funext x; simp
      rw [h1, MeasureTheory.lintegral_const, one_mul,
        MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      unfold Work.Spaces.Iθ
      rw [Real.volume_Icc]
      simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hred := PssReduce (N := Work.FTS.Nonlin.N1ss α Φs)
          (C := 120 * max Cs 0 * α ^ 2) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (by nlinarith [hm, sq_nonneg α])
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N1ss_pt hα hα1 hStar r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (120 : ℝ) * Real.pi * max Cs 0 ≤ 400000 * max Cs 0 + 1000 := by
        nlinarith [hπ, hm]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]
    · have hred := PssReduce (N := Work.FTS.Nonlin.N2ss α Φs)
          (C := 320 * max Cs 0 * α ^ 3) (M := 500 / α)
          (A := fun θ : ℝ => (Real.sin (2 * θ)) ^ (α / 5 - 1))
          (mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3))
          (div_nonneg (by norm_num) hα.le)
          (fun θ hθ => Real.rpow_nonneg
            (Work.FTS.Nonlinear.FstarPkg.sin_two_nonneg_of_mem_Iθ hθ) _)
          (PssAngInt hα hα1)
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            exact Pss_N2ss_pt hα hα1 hStar r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have hval : 320 * max Cs 0 * α ^ 3 * (500 / α) * 2 = 320000 * max Cs 0 * α ^ 2 := by
        have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
        field_simp
        ring
      rw [hval]
      have h1 : (320000 : ℝ) * max Cs 0 ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hm]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
    · have hred := PssReduce (N := Work.FTS.Nonlin.N3ss α Φs)
          (C := 240 * max Cs 0 * α ^ 3) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3))
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N3ss_pt hα hα1 hStar r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (240 : ℝ) * Real.pi * max Cs 0 * α ≤ 400000 * max Cs 0 + 1000 := by
        have hA : 240 * Real.pi * max Cs 0 * α ≤ 960 * max Cs 0 * α := by
          have hp : Real.pi * (max Cs 0 * α) ≤ 4 * (max Cs 0 * α) :=
            mul_le_mul_of_nonneg_right hπ.le (mul_nonneg hm hα.le)
          nlinarith [hp]
        have hB : (960 : ℝ) * max Cs 0 * α ≤ 960 * max Cs 0 := by
          have hb : (960 * max Cs 0) * α ≤ (960 * max Cs 0) * 1 :=
            mul_le_mul_of_nonneg_left hα1 (mul_nonneg (by norm_num) hm)
          linarith [hb]
        have hC : (960 : ℝ) * max Cs 0 ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hm]
        linarith [hA, hB, hC]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]
    · have hred := PssReduce (N := Work.FTS.Nonlin.N4ss α)
          (C := 40 * α ^ 2) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (by positivity)
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N4ss_pt hα hα1 r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (40 : ℝ) * Real.pi ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hπ, hm]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]
    · have hred := PssReduce (N := Work.FTS.Nonlin.N5ss α)
          (C := 120 * α ^ 2) (M := Real.pi / 2) (A := fun _ : ℝ => (1 : ℝ))
          (by positivity)
          (by positivity) (fun θ _ => by norm_num) hA1
          (fun r hr => by
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
            simpa only [mul_one, hunit θ] using Pss_N5ss_pt hα hα1 r hr θ hθ)
      refine le_trans hred (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (120 : ℝ) * Real.pi ≤ 400000 * max Cs 0 + 1000 := by nlinarith [hπ, hm]
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg α)
      nlinarith [h2]

end Work.FTS.Nonlinear.Pieces.rl1Pieces
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKradialL1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-! ## Measurability of the angular moment -/

/-- The angular moment `FK g z = ∫_θ K(θ) g(z,θ) dθ` is a.e. strongly measurable in `z` on
`(0,∞)` as soon as `g` is continuous on the open quadrant: the uncurried integrand
`(z,θ) ↦ g z θ·K θ` is then a.e. strongly measurable for the product of the restrictions
(`Work.Spaces.aesm_of_continuousOn_Qd`), and `AEStronglyMeasurable.integral_prod_right'`
integrates it in `θ`. -/
theorem FK_aesm_of_cont {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry g)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable (fun z => Work.Construction.FK g z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hK : Continuous fun θ : ℝ => Work.Spaces.K θ := by
    unfold Work.Spaces.K
    fun_prop
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2 * Work.Spaces.K p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hcont.mul ((hK.comp continuous_snd).continuousOn))
  have h := hjoint.integral_prod_right'
  have hrestrict : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
  rw [hrestrict]
  simpa [Work.Construction.FK] using h

/-! ## The integrable majorant `√Φ · z²/(1+z)⁴` -/

/-- The majorant `z ↦ √(Φ z)·z²/(1+z)⁴` of `z ↦ |ρ z|/(1+z)²` is integrable on `(0,∞)` for a
radial function of class `ℋ⁴`: `√Φ ∈ L²` because `Φ` is integrable (`HkMem`), and
`z²/(1+z)⁴ ∈ L²`. -/
theorem radialL1_majorant_integrable {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) :
    Integrable (fun z => Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hΦi : IntegrableOn (Phi α 4 ρ) (Set.Ioi (0 : ℝ)) := Phi_integrable_Ioi hmem
  have hΦnn : ∀ z, 0 ≤ Phi α 4 ρ z := Phi_nonneg α 4 ρ
  have hAesm : AEStronglyMeasurable (fun z => Real.sqrt (Phi α 4 ρ z))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hΦi.aestronglyMeasurable
  have hAint : Integrable (fun z => Real.sqrt (Phi α 4 ρ z) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hΦi.congr (Filter.Eventually.of_forall fun z => (Real.sq_sqrt (hΦnn z)).symm)
  have hAmem : MemLp (fun z => Real.sqrt (Phi α 4 ρ z)) 2
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq hAesm).mpr hAint
  have hBmem : MemLp (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) 2
      (volume.restrict (Set.Ioi (0 : ℝ))) := BqSqIntegral.1
  exact memLp_one_iff_integrable.mp (hAmem.mul hBmem)

/-- The pointwise domination `|ρ z|/(1+z)² ≤ √(Φ z)·z²/(1+z)⁴` for `z > 0`, the
`L¹`-functional being split as `(|ρ z|·w z)·(z²/(1+z)⁴)` with `w z = (1+z)²/z²`. -/
theorem radialL1_pointwise {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) {z : ℝ} (hz : 0 < z) :
    |ρ z| / (1 + z) ^ 2 ≤ Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4) := by
  have hΦnn : 0 ≤ Phi α 4 ρ z := Phi_nonneg α 4 ρ z
  have hw0 : 0 ≤ Work.Spaces.w z := by unfold Work.Spaces.w; positivity
  have hsq : (|ρ z| * Work.Spaces.w z) ^ 2 ≤ Phi α 4 ρ z := by
    rw [mul_pow, sq_abs]
    exact radial_slot_le_Phi hmem hz
  have hle : |ρ z| * Work.Spaces.w z ≤ Real.sqrt (Phi α 4 ρ z) :=
    (Real.le_sqrt (mul_nonneg (abs_nonneg _) hw0) hΦnn).mpr hsq
  have hB0 : 0 ≤ z ^ 2 / (1 + z) ^ 4 := by positivity
  have hstep := mul_le_mul_of_nonneg_right hle hB0
  have hid : |ρ z| / (1 + z) ^ 2 = |ρ z| * Work.Spaces.w z * (z ^ 2 / (1 + z) ^ 4) := by
    unfold Work.Spaces.w
    field_simp
  rw [hid]
  exact hstep

/-- **Integrability of the weighted radial `L¹`-functional** of a radial `ℋ⁴`-function which is
a.e. strongly measurable: domination by the integrable majorant `√Φ·z²/(1+z)⁴`. -/
theorem radialL1_integrableOn {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z))
    (hρ : AEStronglyMeasurable (fun z => |ρ z| / (1 + z) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    IntegrableOn (fun z => |ρ z| / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  refine Integrable.mono' (radialL1_majorant_integrable hmem) hρ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (by positivity))]
  exact radialL1_pointwise hmem hz

/-! ## The target -/

theorem FKradialL1 {α₂ Ci : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g : Work.FTS.Galerkin.Fn}, 0 < α → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      MeasureTheory.IntegrableOn (fun z => |Work.Construction.FK g z| / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ z in Set.Ioi (0 : ℝ), |Work.Construction.FK g z| / (1 + z) ^ 2)
        ≤ 2 * Ci * Work.FTS.Nonlin.Xn α g := by
  intro α g hα hαα₂ hgal
  -- `GalClass α g` is an `ℋ⁶`-class, hence an `ℋ⁴`-class, with vanishing zero mode of `L₁₂`.
  have hreg : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  obtain ⟨hmem, hbnd⟩ := hN.fkH α ⟨hα, hαα₂⟩ g hreg hgal.l12
  -- `g` is `C^∞` on the open quadrant, so `FK g` is a.e. strongly measurable.
  have hcont : ContinuousOn (Function.uncurry g)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hgal.reg.1.continuousOn.mono (by
      intro p hp
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2⟩)
  have haesm : AEStronglyMeasurable (fun z => Work.Construction.FK g z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := FK_aesm_of_cont hcont
  have haesm2 : AEStronglyMeasurable
      (fun z => |Work.Construction.FK g z| / (1 + z) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    haesm.norm.mul (by fun_prop)
  refine ⟨radialL1_integrableOn hmem haesm2, ?_⟩
  have h1 : (∫ z in Set.Ioi (0 : ℝ), |Work.Construction.FK g z| / (1 + z) ^ 2)
      ≤ 2 * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) :=
    fk_radialL1_le hmem
  have h2 : 2 * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
      ≤ 2 * Ci * Work.FTS.Nonlin.Xn α g := by linarith [hbnd]
  exact le_trans h1 h2

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The classes -/

/-- `SmoothQuad` (genuine `C^∞` on `z > -1`, `0 < θ < π/2`) implies `SmoothOpen` (the same on the
smaller open quadrant `(0,∞) × (0,π/2)`). -/
theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.EllipticEst.SmoothOpen f := by
  refine hf.mono ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp1]), hp2⟩

/-- **`RegQ` refines `HQo`**: the interior class of the frozen vocabulary only adds the boundary
traces to the open-quadrant class of `VocabO`. -/
theorem HQo_of_RegQ {α : ℝ} {k : ℕ} {f : Fn} (h : RegQ α k f) : HQo α k f :=
  ⟨smoothOpen_of_smoothQuad h.1, h.2.1⟩

/-- The `ℋ^k`-integrand is monotone in the order. -/
theorem HkIntegrand_mono_le (α : ℝ) {l k : ℕ} (hkl : l ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  induction k, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (Work.Spaces.HkIntegrand_mono α n f z θ)

/-- **`HkMem` is monotone in the order, in the open-quadrant class**: the `ℋ^k`-integrand is
dominated by the `ℋ^l`-integrand for `k ≤ l`, and the honesty of the larger one is exactly the
integrability certificate the smaller one needs. -/
theorem HkMem_mono_open {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ l : ℕ, l ≤ k → Work.Spaces.HkMem α k f → Work.Spaces.HkMem α l f :=
  fun l hlk h =>
    Work.FTS.LocData.HkMem_of_majorant α l (hf.continuousOn_HkIntegrand α l)
      h.1 h.2 (fun z _ θ _ => HkIntegrand_mono_le α hlk f z θ)

/-- `HQo` is monotone in the order. -/
theorem HQo.mono {α : ℝ} {k l : ℕ} {f : Fn} (h : HQo α k f) (hkl : l ≤ k) : HQo α l f :=
  ⟨h.1, HkMem_mono_open h.1 l hkl h.2⟩

/-- `HkMem` descends from `ℋ^5` to `ℋ^4` for functions smooth on the open quadrant. -/
theorem HkMem_four_of_five {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : Work.Spaces.HkMem α 5 f) : Work.Spaces.HkMem α 4 f :=
  HkMem_mono_open hf 4 (by norm_num) h

/-! ## The `GalClass` side conditions -/


theorem galClass_HkMem4 {α : ℝ} {g : Fn} (h : GalClass α g) : Work.Spaces.HkMem α 4 g :=
  HkMem_mono_open (HQo_of_RegQ h.reg).1 4 (by norm_num) h.reg.2.1






/-! ## The flat angular norm `CoefTh` -/


/-- `supAbsO` is nonnegative. -/
theorem supAbsO_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.H2.supAbsO g := by
  rw [Work.FTS.H2.supAbsO]
  by_cases h : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|}
  · exact le_trans (abs_nonneg _) (le_csSup h ⟨1, one_pos, 1, one_pos,
      by linarith [Real.pi_gt_three], rfl⟩)
  · rw [csSup_of_not_bddAbove h, Real.sSup_empty]




/-! ## The `D`-sup norms `WDp`/`WDMem` -/


/-- `WDp l f` is nonnegative. -/
theorem WDp_nonneg (l : ℕ) (f : Fn) : 0 ≤ WDp l f := by
  classical
  rw [WDp]
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with hbj
  · exact supAbsO_nonneg _
  · exact le_rfl


/-- A `WDp`-bound is a `WDMem`-bound, on the honest class (the direction the interfaces use). -/
theorem WDMem_of_WDp_le {l : ℕ} {f : Fn} {C : ℝ} (hf : WDMem l f) (h : WDp l f ≤ C) :
    ∀ b j : ℕ, b + j ≤ l → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j f z θ| ≤ C := by
  classical
  intro b j hbj z θ hz hθ0 hθ1
  obtain ⟨K, hK⟩ := hf b j hbj
  have hbdd : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2
      ∧ y = |Work.Spaces.mixed b j f z θ|} :=
    ⟨K, by rintro y ⟨z', hz', θ', hθ', hθ'', rfl⟩; exact hK z' θ' hz' hθ' hθ''⟩
  have h1 : |Work.Spaces.mixed b j f z θ| ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) :=
    le_csSup hbdd ⟨z, hz, θ, hθ0, hθ1, rfl⟩
  have h2 : Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) ≤ WDp l f := by
    have hb' : b ∈ Finset.range (l + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
    have hj' : j ∈ Finset.range (l + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
    have hnn : ∀ a c : ℕ, 0 ≤ (if a + c ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed a c f) else 0) := fun a c => by
      split_ifs with h
      · exact supAbsO_nonneg _
      · exact le_rfl
    have hinner : (if b + j ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0)
        ≤ ∑ j' ∈ Finset.range (l + 1),
            (if b + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0) :=
      Finset.single_le_sum (f := fun j' => if b + j' ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0) (fun j' _ => hnn b j') hj'
    have houter : (∑ j' ∈ Finset.range (l + 1),
          (if b + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0))
        ≤ ∑ b' ∈ Finset.range (l + 1), ∑ j' ∈ Finset.range (l + 1),
            (if b' + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b' j' f) else 0) :=
      Finset.single_le_sum (f := fun b' => ∑ j' ∈ Finset.range (l + 1),
          (if b' + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b' j' f) else 0))
        (fun b' _ => Finset.sum_nonneg fun j' _ => hnn b' j') hb'
    have h := le_trans hinner houter
    rw [ite_eq_left hbj] at h
    simpa only [WDp] using h
  linarith

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WtohWin.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WtohWin

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The pointwise form of `W^{4,∞} ⟹ ℋ⁴` in the open-quadrant class.**  Given the two
pointwise bounds `hA`, `hB` on the plain `z`-derivatives of `f`, the `ℋ⁴`-norm of `f` is
bounded by `10¹⁰ W`.  No finiteness of `f` beyond `SmoothOpen f` is used. -/
theorem wtoHQ_pointwise_open {α : ℝ} {f : ℝ → ℝ → ℝ} {W : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hW : 0 ≤ W)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hA : ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ| ≤ 200000 * W)
    (hB : ∀ i l : ℕ, 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    Work.FTS.Nonlin.Xn α f ≤ 10 ^ 10 * W := by
  -- the pointwise bound of the `ℋ⁴`-integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 f z θ
        ≤ W ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
    fun z hz θ hθ => hkIntegrand_le_open (α := α) (f := f) hα hα1 hsm hW hA hB z hz θ hθ
  -- the angular integral
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
    intro z hz
    have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by rw [Work.Spaces.eta]; norm_num)
        (by rw [Work.Spaces.eta]; norm_num)).1
    have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.Spaces.integrableOn_angular_weight' hα hα1
    have hmaj : Integrable (fun θ : ℝ => W ^ 2 * (1 / (1 + z) ^ 2)
        * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hS1.const_mul (2 * 10 ^ 15)).add (hS2.const_mul (10 ^ 16))).const_mul _
    have hIoo : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      exact Measure.restrict_congr_set haeeq.symm
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 4 f z θ
          ≤ W ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
      rw [hIoo]
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt z hz θ hθ)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, W ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hmaj hae
      _ = W ^ 2 * (1 / (1 + z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
          refine mul_le_mul_of_nonneg_left
            (Work.Elliptic.WtoH_Angular hα hα1 (by norm_num) (by norm_num)) ?_
          exact mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _))
  -- the radial integral
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ)
      ≤ (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 := by
    set K : ℝ := 2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700 with hK
    have hI : IntegrableOn (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K) Work.Spaces.Iz := by
      refine (Work.Elliptic.WtoH_IntZ.1.mul_const (W ^ 2 * K)).congr ?_
      filter_upwards with z
      ring
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ z in Work.Spaces.Iz, W ^ 2 * (1 / (1 + z) ^ 2) * K :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
      _ = (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) * (W ^ 2 * K) := by
          rw [show (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K)
              = fun z : ℝ => (1 / (1 + z) ^ 2) * (W ^ 2 * K) from by funext z; ring]
          rw [MeasureTheory.integral_mul_const]
      _ ≤ 2 * (W ^ 2 * K) :=
          mul_le_mul_of_nonneg_right Work.Elliptic.WtoH_IntZ.2
            (mul_nonneg (sq_nonneg _) (by rw [hK]; norm_num))
      _ = K * 2 * W ^ 2 := by rw [hK]; ring
  have hSq : Work.Spaces.HkSq α 4 f ≤ 10 ^ 20 * W ^ 2 := by
    rw [Work.Spaces.HkSq]
    have hK2 : (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 ≤ 10 ^ 20 * W ^ 2 := by
      nlinarith [sq_nonneg W]
    linarith [houter]
  have hmain : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ 10 ^ 10 * W := by
    calc Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ Real.sqrt (10 ^ 20 * W ^ 2) :=
          Real.sqrt_le_sqrt hSq
      _ = 10 ^ 10 * W := by
          rw [show (10 : ℝ) ^ 20 * W ^ 2 = (10 ^ 10 * W) ^ 2 by ring]
          exact Real.sqrt_sq (mul_nonneg (by norm_num) hW)
  simpa only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm] using hmain

end Work.FTS.OpenPkg.WtohWin
end
end
