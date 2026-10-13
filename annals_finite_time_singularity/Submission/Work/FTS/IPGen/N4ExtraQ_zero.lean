import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IPGen/N4ExtraQ_zero.lean` — the identically vanishing pairing inhabits `N4ExtraQ`

The contract `Work.FTS.IPGen.N4ExtraQ IP α₂ Ct` is a structure of *inequalities and
identities* about a pairing `IP : ℝ → Fn → Fn → ℝ`, all of whose hypotheses (`HQo`, `RegQ`,
`T2Clause`, `T3Clause`, …) are properties of the arguments only.  Hence the zero pairing
`IP ≡ 0` inhabits it for any positive `Ct`, `α₂`: every identity becomes `0 = 0` (or a
definitional redex), and every inequality becomes `0 ≤` a product of nonnegative factors.

The lemmas below supply the nonnegativity of the latter: `ℋ⁴`-norm, the flat angular norm
`CoefTh`, the `D`-sup norm `WDp`, the `𝒲^{l,∞}`-norm, and the real power `α ^ (-(1/2))` for
`α > 0`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Nonnegativity of the norms appearing in the contract -/

/-- The closed-quadrant supremum `Work.Spaces.supAbs` is nonnegative: the defining set
contains `|g 0 0|`, and `supAbs` is Lean's junk value `0` for unbounded functions. -/
theorem supAbs_nonneg_zero (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.supAbs g := by
  rw [Work.Spaces.supAbs]
  by_cases h : BddAbove {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ, y = |g z θ|}
  · exact le_trans (abs_nonneg _) (le_csSup h ⟨0, Set.mem_Ici.mpr le_rfl, 0,
      ⟨le_rfl, by linarith [Real.pi_pos]⟩, rfl⟩)
  · rw [csSup_of_not_bddAbove h, Real.sSup_empty]

/-- The `𝒲^{l,∞}`-norm is nonnegative (unconditionally: `supAbs` is the junk value `0`
for unbounded functions). -/
theorem WlInf_nonneg_zero (α : ℝ) (l : ℕ) (f : Fn) : 0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  refine add_nonneg (Finset.sum_nonneg fun k _ => supAbs_nonneg_zero _) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact supAbs_nonneg_zero _
  · exact le_rfl

/-- The `ℋ⁴`-norm `Xn α f = HkNorm α 4 f` is nonnegative. -/
theorem Xn_nonneg_zero (α : ℝ) (f : Fn) : 0 ≤ Work.FTS.Nonlin.Xn α f :=
  Work.Spaces.HkNorm_nonneg α 4 f

/-- `α ^ (-(1/2)) ≥ 0` for `α > 0`. -/
theorem rpow_neg_half_nonneg_zero {α : ℝ} (hα : 0 < α) : 0 ≤ α ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_nonneg hα.le _

/-! ## The zero pairing inhabits the contract -/

theorem N4ExtraQ_zero :
    Work.FTS.IPGen.N4ExtraQ
      (fun (_ : ℝ) (_ : Work.FTS.Galerkin.Fn) (_ : Work.FTS.Galerkin.Fn) => (0 : ℝ)) 1 1 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `cs`
    intro α hα f g hf hg
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_one (Xn_nonneg_zero α f)) (Xn_nonneg_zero α g)
  · -- `add`
    intro α hα f₁ f₂ g hf₁ hf₂ hg
    simp
  · -- `smul`
    intro α hα c f g hf hg
    simp
  · -- `neg`
    intro α hα f g hf hg
    simp
  · -- `congr`
    intro α hα f f' g hf hf' hg h
    simp
  · -- `dz`
    intro α hα g hg
    simp only [abs_zero]
    exact mul_nonneg zero_le_one (sq_nonneg (Work.FTS.Nonlin.Xn α g))
  · -- `t1`
    intro α hα f g hf hg
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (rpow_neg_half_nonneg_zero hα.1))
      (Xn_nonneg_zero α f)) (sq_nonneg (Work.FTS.Nonlin.Xn α g))
  · -- `t2`
    intro α hα f g hf hf4 hfcoef hg hg5 hdec
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (rpow_neg_half_nonneg_zero hα.1))
      (add_nonneg (Xn_nonneg_zero α f) (Work.FTS.OpenPkg.CoefTh_nonneg 1 f))) (sq_nonneg (Work.FTS.Nonlin.Xn α g))
  · -- `t3`
    intro α hα f g hf hf4 hfcoef hg hg5 hdec
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (rpow_neg_half_nonneg_zero hα.1))
      (add_nonneg (WlInf_nonneg_zero α 4 f) (Work.FTS.OpenPkg.CoefTh_nonneg 3 f))) (sq_nonneg (Work.FTS.Nonlin.Xn α g))
  · -- `t4`
    intro α hα f g hf hg
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (rpow_neg_half_nonneg_zero hα.1))
      (Work.FTS.OpenPkg.WDp_nonneg 4 f)) (sq_nonneg (Work.FTS.Nonlin.Xn α g))
  · -- `st`
    intro α hα f g hf hm hg
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (rpow_neg_half_nonneg_zero hα.1))
      (Work.FTS.OpenPkg.WDp_nonneg 4 (Work.Spaces.pth f))) (sq_nonneg (Work.FTS.Nonlin.Xn α g))

end Work.FTS.IPGen
