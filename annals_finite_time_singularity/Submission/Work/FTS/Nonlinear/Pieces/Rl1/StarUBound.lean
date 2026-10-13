import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.splits_of_ctx
import Submission.Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one

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

/-- The `θ`-slice of a `SmoothQuad` function is `C^n` on `(0,π/2)` for every finite `n`
(composing the genuine smooth order with the coercion `ℕ → ℕ∞ω`). -/
theorem contDiffOn_thSlice_Uop {α z : ℝ} {Ψ : ℝ → ℝ → ℝ} (hz : -1 < z)
    (hΨ : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ)) (n : ℕ) :
    ContDiffOn ℝ n (fun θ' => Work.Construction.Uop α Ψ z θ') (Set.Ioo 0 (π / 2)) :=
  (Work.FTS.LocData.SmoothQuad.curry_θ hΨ (show z ∈ Set.Ioi (-1 : ℝ) from hz)).of_le
    (by simp [Work.Stability.smoothOrder])

/-- `𝒰(Φ̃_*) = Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)` is bounded pointwise by
`C·max Cs 0·α` on `z > 0`, `θ ∈ Iθ`, with a universal constant `C`.  (`StarPkg` bounds only
`∂_θ𝒰(Φ̃_*)`, `ℛ(Φ̃_*)`, `𝒱(Φ̃_*)`, never `𝒰(Φ̃_*)` itself, and only for `z > 0`.)

Route: (i) the identity `Uop α Ψ z θ = -(Rop α Ψ z θ - Vop α Ψ z θ)·(cos θ/sin θ)` (valid since
`Rop - Vop = tan θ·(3Ψ + α z ∂_zΨ) = -tan θ·Uop`), at `θ = π/4` reads
`Uop α Ψ z (π/4) = -(Rop α Ψ z (π/4) - Vop α Ψ z (π/4))` (as `tan (π/4) = 1`), so
`rl1Tools.starPt`'s bounds `|ℛ| ≤ max Cs 0·α`, `|𝒱| ≤ max Cs 0·α` give
`|Uop α Ψ z (π/4)| ≤ 2·max Cs 0·α`;
(ii) for interior `θ ∈ (0,π/2)`, `abs_sub_le_mul_abs_sub_of_deriv_bound`
(`Work.FTS.EllipticEst.SgamBound`) applied to `θ' ↦ Uop α (PhiTs α Φs) z θ'` — which is `C^∞`
on `(0,π/2)` because `PhiTil α (Fstar α) Φs` agrees on a neighbourhood of `z > 0` with
`Φs - sin(2θ)/(2(1+z))`, a `SmoothQuad` function, so `Uop` of it is `SmoothQuad` and one uses
`SmoothQuad.curry_θ` — with the derivative bound `|∂_θ𝒰| ≤ max Cs 0·α` of `starPt` gives
`|Uop … z θ - Uop … z (π/4)| ≤ max Cs 0·α·(π/2)`;
(iii) the endpoints `θ = 0, π/2` are immediate from `StarPkg.vanishU : VanishTheta (Uop …)`.
Hence `C = 4` works. -/
theorem StarUBound : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ C * max Cs 0 * α := by
  refine ⟨4, by norm_num, ?_⟩
  intro α Cs Φs hs hα hα1 z hz θ hθ
  -- unfold `PhiTs` once and for all: `Φ̃_* = Φ_s - Θ_*(α)`
  change |Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
    ≤ 4 * max Cs 0 * α
  let Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
  -- the three pointwise bounds of `StarPkg`, restricted to `𝒰(Φ̃_*)`
  obtain ⟨hR, hV, hdU⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hR' : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Rop α Ψ z θ| ≤ max Cs 0 * α := hR
  have hV' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Vop Ψ z θ| ≤ max Cs 0 * α := hV
  have hdU' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ| ≤ max Cs 0 * α := hdU
  have hvU : Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ) := hs.vanishU
  have hMnn : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hMα : 0 ≤ max Cs 0 * α := mul_nonneg hMnn hα.le
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hpi4Iθ : (π / 4) ∈ Work.Spaces.Iθ :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hpi4Ioo : (π / 4) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  -- ### (i) the anchor at `θ = π/4`
  have hanchor : |Work.Construction.Uop α Ψ z (π / 4)| ≤ 2 * (max Cs 0 * α) := by
    rw [Uop_pi_div_four α Ψ z, abs_neg]
    have h1 := hR' z hz (π / 4) hpi4Iθ
    have h2 := hV' z hzI (π / 4) hpi4Iθ
    have htri : |Work.Construction.Rop α Ψ z (π / 4) - Work.Construction.Vop Ψ z (π / 4)|
        ≤ |Work.Construction.Rop α Ψ z (π / 4)| + |Work.Construction.Vop Ψ z (π / 4)| := by
      have h := abs_add_le (Work.Construction.Rop α Ψ z (π / 4))
        (-(Work.Construction.Vop Ψ z (π / 4)))
      rw [abs_neg] at h
      simpa only [sub_eq_add_neg] using h
    linarith
  -- ### the two boundary values
  rcases eq_or_ne θ 0 with hθ0 | hθ0
  · subst hθ0
    rw [hvU.1 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  rcases eq_or_ne θ (π / 2) with hθ2 | hθ2
  · subst hθ2
    rw [hvU.2 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  -- ### (ii) the interior mean-value step
  have hθint : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ2⟩
  have hsq : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) := by
    show Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
    exact smoothQuad_Uop (smoothQuad_PhiTs hα hα1 hs.smooth)
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n (fun θ' => Work.Construction.Uop α Ψ z θ')
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    fun n => contDiffOn_thSlice_Uop (by linarith) hsq n
  have hK : ∀ ξ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (fun θ' => Work.Construction.Uop α Ψ z θ') ξ| ≤ max Cs 0 * α := by
    intro ξ hξ
    have hξI : ξ ∈ Work.Spaces.Iθ := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
    have h := hdU' z hzI ξ hξI
    simpa only [Work.Spaces.pth] using h
  have hmvt := Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
    (u := fun θ' => Work.Construction.Uop α Ψ z θ') hslice hθint hpi4Ioo hK
  have hdist : |θ - π / 4| ≤ π / 4 := by
    rw [abs_le]
    exact ⟨by linarith [hθint.1], by linarith [hθint.2]⟩
  have hb1 : |Work.Construction.Uop α Ψ z θ - Work.Construction.Uop α Ψ z (π / 4)|
      ≤ (max Cs 0 * α) * (π / 4) :=
    le_trans hmvt (mul_le_mul_of_nonneg_left hdist hMα)
  have htri : |Work.Construction.Uop α Ψ z θ|
      ≤ |Work.Construction.Uop α Ψ z θ - Work.Construction.Uop α Ψ z (π / 4)|
        + |Work.Construction.Uop α Ψ z (π / 4)| := by
    have h := abs_add_le (Work.Construction.Uop α Ψ z θ - Work.Construction.Uop α Ψ z (π / 4))
      (Work.Construction.Uop α Ψ z (π / 4))
    rwa [sub_add_cancel] at h
  have hpi : (π / 4 : ℝ) ≤ 2 := by linarith [Real.pi_lt_four]
  have hstep : (max Cs 0 * α) * (π / 4) ≤ (max Cs 0 * α) * 2 :=
    mul_le_mul_of_nonneg_left hpi hMα
  linarith [hb1, hanchor, htri, hstep]

end Work.FTS.Nonlinear.Pieces.Rl1
