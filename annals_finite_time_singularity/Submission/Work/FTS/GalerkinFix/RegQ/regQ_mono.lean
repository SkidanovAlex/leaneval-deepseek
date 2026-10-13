import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.GalerkinFix.Defs
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RegQ` is monotone in the order `k`

`Work.FTS.Nonlin.RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f`.

* `SmoothQuad f` does not mention `k` at all.
* `HkMem α k f` is monotone: the `ℋ^{k+1}`-integrand dominates the `ℋ^k`-integrand, so the
  integrability certificates for the bigger integrand give those for the smaller one
  (`Work.GalerkinFix.RegQ.HkMem_mono_Q`, iterated here).
* `BdryTraces α k f` is a *conjunction over pairs* `a + b ≤ k`, hence weakening `k` weakens the
  condition.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalerkinFix.RegQ

set_option autoImplicit false

/-- Iterated form of `HkMem_mono_Q`: `HkMem` descends in the order, inside the class
`SmoothQuad`. -/
private theorem HkMem_desc {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (k : ℕ) : ∀ k' : ℕ, k' ≤ k → Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k' f := by
  induction k with
  | zero =>
    intro k' hk h
    obtain rfl : k' = 0 := Nat.le_zero.mp hk
    exact h
  | succ k ih =>
    intro k' hk h
    rcases Nat.eq_or_lt_of_le hk with hEq | hLt
    · subst hEq
      exact h
    · exact ih k' (Nat.lt_succ_iff.mp hLt) (Work.GalerkinFix.RegQ.HkMem_mono_Q hf h)

/-- **The `RegQ`-class is monotone in the order**: `RegQ α k f → RegQ α k' f` for `k' ≤ k`. -/
theorem regQ_mono {α : ℝ} {k k' : ℕ} {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.Nonlin.RegQ α k f) (hk : k' ≤ k) : Work.FTS.Nonlin.RegQ α k' f := by
  obtain ⟨hs, hm, hb⟩ := hf
  exact ⟨hs, HkMem_desc hs k k' hk hm, fun a b hab => hb a b (le_trans hab hk)⟩

end Work.FTS.GalerkinFix.RegQ
