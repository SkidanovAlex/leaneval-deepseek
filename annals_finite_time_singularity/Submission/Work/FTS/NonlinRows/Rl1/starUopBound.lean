import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.EllipticEst.Uop_bound_reg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

open scoped Real Topology
open Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-
Port of `Work.FTS.Nonlinear.Pieces.Rl1.StarUBound` (already proved, constant `4`) from the
frozen `StarPkg` to the open-quadrant `StarPkgo`.  The only genuinely new ingredient is the
θ-slice smoothness of `θ ↦ Uop α (PhiTs α Φs) z θ` on `(0, π/2)` from `SmoothOpen Φs`
(the frozen proof uses `smoothQuad_PhiTs`/`smoothQuad_Uop`/`contDiffOn_thSlice_Uop`, which need
`SmoothQuad`); the rest is verbatim: the anchor `Uop_pi_div_four` at `π/4` plus
`star_Rop_le`/`star_Vop_le` (in `Rl1/tools.lean`) give `|Uop z (π/4)| ≤ 2 max Cs 0 α`, and the
interior mean-value lemma `Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound`
with the derivative bound `|pth (Uop …)| ≤ max Cs 0 α` (from `hs.dU` via
`Work.FTS.OpenPkg.WDMem_of_WDp_le`) gives `|Uop z θ - Uop z (π/4)| ≤ (π/4) max Cs 0 α`.
The endpoints `θ = 0, π/2` follow from `hs.vanishU`.  `C = 4` works.
-/

/-! ## The new ingredient: `θ`-slice smoothness in the open-quadrant class

`SmoothOpen Φ_*` (from `StarPkgo.smooth`) makes `Φ̃_* = PhiTs α Φs` and then `U(Φ̃_*)` `C^∞`
on the open quadrant (`smoothOpen_PhiTs`, `smoothOpen_Uop`), so the angular slice at any
`z > 0` is `C^n` on `(0, π/2)` for every finite `n` (`SmoothOpen.curry_θ`).  This replaces the
frozen `contDiffOn_thSlice_Uop`, which went through `SmoothQuad`. -/
theorem contDiffOn_thSlice_Uop_open {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    ∀ z : ℝ, 0 < z → ∀ n : ℕ, ContDiffOn ℝ n
      (fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro z hz n
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs
  have hU : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.EllipticEst.smoothOpen_Uop hPhi
  exact (hU.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])

theorem starUopBound : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.VocabO.StarPkgo α Cs Φs →
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ C * max Cs 0 * α := by
  refine ⟨4, by norm_num, ?_⟩
  intro α Cs Φs hα hα1 hs z hz θ hθ
  have hMnn : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hMα : 0 ≤ max Cs 0 * α := mul_nonneg hMnn hα.le
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hpi4Ioo : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hpi4Iθ : (Real.pi / 4) ∈ Work.Spaces.Iθ :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  -- the three pointwise bounds of `StarPkgo`, on the open angular interval
  have hR : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z ξ| ≤ max Cs 0 * α :=
    fun ξ hξ => star_Rop_le hα hs z hz ξ hξ
  have hV : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z ξ| ≤ max Cs 0 * α :=
    fun ξ hξ => star_Vop_le hα hs z hz ξ hξ
  have hdU : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z ξ|
        ≤ max Cs 0 * α := by
    intro ξ hξ
    have h1 := Work.FTS.OpenPkg.WDMem_of_WDp_le hs.dU.1 hs.dU.2 0 0 (by norm_num)
      z ξ hz hξ.1 hξ.2
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hvU : Work.Spaces.VanishTheta
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := hs.vanishU
  -- ### (i) the anchor at `θ = π/4`
  have hanchor : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
      ≤ 2 * (max Cs 0 * α) := by
    rw [Work.FTS.Nonlinear.Pieces.Rl1.Uop_pi_div_four α (Work.FTS.Nonlin.PhiTs α Φs) z,
      abs_neg]
    have h1 := hR (Real.pi / 4) hpi4Ioo
    have h2 := hV (Real.pi / 4) hpi4Ioo
    have htri : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)
        - Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
        ≤ |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
          + |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)| := by
      have h := abs_add_le
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4))
        (-(Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)))
      rw [abs_neg] at h
      simpa only [sub_eq_add_neg] using h
    linarith
  -- ### the two boundary values
  rcases eq_or_ne θ 0 with hθ0 | hθ0
  · subst hθ0
    rw [hvU.1 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  rcases eq_or_ne θ (Real.pi / 2) with hθ2 | hθ2
  · subst hθ2
    rw [hvU.2 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  -- ### (ii) the interior mean-value step
  have hθint : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ2⟩
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n
      (fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_thSlice_Uop_open hα hα1 hs z hz
  have hK : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ') ξ|
        ≤ max Cs 0 * α := by
    intro ξ hξ
    have h := hdU ξ hξ
    simpa only [Work.Spaces.pth] using h
  have hmvt := Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
    (u := fun θ' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
    hslice hθint hpi4Ioo hK
  have hdist : |θ - Real.pi / 4| ≤ Real.pi / 4 := by
    rw [abs_le]
    exact ⟨by linarith [hθint.1], by linarith [hθint.2]⟩
  have hb1 : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      - Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
      ≤ (max Cs 0 * α) * (Real.pi / 4) :=
    le_trans hmvt (mul_le_mul_of_nonneg_left hdist hMα)
  have htri : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
      ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          - Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)|
        + |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4)| := by
    have h := abs_add_le
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        - Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4))
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 4))
    rwa [sub_add_cancel] at h
  have hpi : (Real.pi / 4 : ℝ) ≤ 2 := by linarith [Real.pi_lt_four]
  have hstep : (max Cs 0 * α) * (Real.pi / 4) ≤ (max Cs 0 * α) * 2 :=
    mul_le_mul_of_nonneg_left hpi hMα
  linarith [hb1, hanchor, htri, hstep]

end Work.FTS.NonlinRows.Rl1
