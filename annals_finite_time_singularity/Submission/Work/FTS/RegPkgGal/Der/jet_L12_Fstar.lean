import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_L12_Fstar`

The `L₁₂`-image of the **explicit** profile `F_* = Work.Construction.Fstar (pExp α)`, as a
`Jet` in the joint variables `(z,θ,τ)`: the function

  `(z,θ,τ) ↦ L₁₂(F_*)(z)`

is a *radial* function, so it is trivially constant in `θ` and `τ`; the content of the lemma is
the explicit evaluation

  `L₁₂(F_*)(z) = 2·pExp α/(1+z)`   (`Work.Construction.L12_Fstar_eq`, at `α' = pExp α`)

together with the two elementary facts about `z ↦ 2·pExp α/(1+z)` on `z ≥ 0`: it is bounded by
`2·pExp α` and `2·pExp α`-Lipschitz.  Those give the `Jet` with constant
`max (2 pExp α) (4 pExp α)` (the `4` comes from the large-distance regime, where the sup bound
replaces the Lipschitz estimate).

This is the leaf `Der.jet_L12_Fstar` of the `R5Slot` tree (NOTES_RegPkgGal §14), consumed by
`Der.jet_N0`.
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

theorem jet_L12_Fstar {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S) :
    ∃ N : ℝ, Work.FTS.Regularity.Jet α S N
      (fun z θ τ => Work.Coercivity.L12f (fun z θ => Work.Construction.Fstar
        (Work.FTS.Regularity.pExp α) z θ) z) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp0 : (0 : ℝ) ≤ Work.FTS.Regularity.pExp α := hp.le
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hα1 : α ≤ 1 := by linarith
  -- the explicit value of the operator on the profile
  have hval : ∀ z : ℝ, 0 ≤ z → Work.Coercivity.L12f
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
        = 2 * (Work.FTS.Regularity.pExp α) / (1 + z) := by
    intro z hz
    rw [show Work.Coercivity.L12f
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        = Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) from rfl,
      Work.Construction.L12_Fstar_eq hp hp1 hz]
  -- it is `2 · pExp α`-Lipschitz on `[0,∞)`
  have hglip : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |Work.Coercivity.L12f (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
        - Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z'|
        ≤ 2 * Work.FTS.Regularity.pExp α * |z - z'| := by
    intro z z' hz hz'
    rw [hval z hz, hval z' hz']
    have hden : (0 : ℝ) < (1 + z) * (1 + z') := by positivity
    rw [show 2 * Work.FTS.Regularity.pExp α / (1 + z) - 2 * Work.FTS.Regularity.pExp α / (1 + z')
        = 2 * Work.FTS.Regularity.pExp α * (z' - z) / ((1 + z) * (1 + z')) by
      field_simp
      ring]
    rw [abs_div, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hp0),
      abs_of_pos hden, abs_sub_comm]
    rw [div_le_iff₀ hden]
    have hd1 : (1 : ℝ) ≤ (1 + z) * (1 + z') := by nlinarith
    have hA : (0 : ℝ) ≤ 2 * Work.FTS.Regularity.pExp α * |z - z'| :=
      mul_nonneg (mul_nonneg (by norm_num) hp0) (abs_nonneg _)
    calc 2 * Work.FTS.Regularity.pExp α * |z - z'|
          = 2 * Work.FTS.Regularity.pExp α * |z - z'| * 1 := by ring
      _ ≤ 2 * Work.FTS.Regularity.pExp α * |z - z'| * ((1 + z) * (1 + z')) :=
          mul_le_mul_of_nonneg_left hd1 hA
  -- and bounded by `2 · pExp α`
  have hgbdd : ∀ z : ℝ, 0 ≤ z →
      |Work.Coercivity.L12f (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z|
        ≤ 2 * Work.FTS.Regularity.pExp α := by
    intro z hz
    rw [hval z hz,
      abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hp0) (by linarith))]
    exact div_le_self (mul_nonneg (by norm_num) hp0) (by linarith)
  refine ⟨max (2 * Work.FTS.Regularity.pExp α) (2 * (2 * Work.FTS.Regularity.pExp α)),
    le_trans (mul_nonneg (by norm_num) hp0) (le_max_left _ _), ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    change |Work.Coercivity.L12f
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z|
      ≤ max (2 * Work.FTS.Regularity.pExp α) (2 * (2 * Work.FTS.Regularity.pExp α))
    exact le_trans (hgbdd z hz) (le_max_left _ _)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hh := Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded
      (f := fun z => Work.Coercivity.L12f
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z)
      hα hα1 (mul_nonneg (by norm_num) hp0) (mul_nonneg (by norm_num) hp0)
      hglip hgbdd z z' hz hz'
    have hzth : |z - z'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]) hα.le
    change |Work.Coercivity.L12f
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
        - Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z'|
      ≤ max (2 * Work.FTS.Regularity.pExp α) (2 * (2 * Work.FTS.Regularity.pExp α))
        * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
    exact le_trans hh (mul_le_mul_of_nonneg_left hzth
      (le_trans (mul_nonneg (by norm_num) hp0) (le_max_left _ _)))

end Work.FTS.RegPkgGal.Der
