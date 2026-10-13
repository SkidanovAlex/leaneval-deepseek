/-
# `HkAdm` is monotone in the order `k`

`Work.Coercivity.HkAdm α k f` is the admissible class of the `ℋ^k`-coercivity layer:
`f` is smooth on a neighbourhood of the closed quadrant, every mixed derivative
`D_z^b D_θ^a f` with `a + b ≤ k` lies in `ℋ^k`, and its `L₁₂`-zero-mode vanishes.

The class is *decreasing* in `k`: if `f` is admissible at order `l`, then it is
admissible at every lower order `k ≤ l`.  Indeed

* the smoothness clause `SmoothNbhd f` does not mention `k` at all;
* the zero-mode clause `L₁₂(D_z^b D_θ^a f)(0) = 0` does not mention `k` either, so
  the hypothesis `a + b ≤ k ≤ l` immediately hands it down;
* the only clause that refers to the order is the membership
  `HkMem α k (D_z^b D_θ^a f)`, and there `HkMem` descends: `HkMem α l g` implies
  `HkMem α k g` for `k ≤ l` by iterating the one-step monotonicity
  `Work.Coercivity.HkMem_mono` (`HkMem α (k+1) g → HkMem α k g`), which is precisely
  the statement that the `H^{k+1}`-integrand pointwise dominates the `H^k`-integrand.

The one-step `HkMem_mono` requires the smoothness of the function it is applied to, so
the iterated descent is proved for a `SmoothNbhd` function `g`; in the application
`g = D_z^b D_θ^a f` is smooth by `SmoothNbhd.DzIter`/`SmoothNbhd.DthIter`.

This is the elementary order-monotonicity that lets every statement proved for
`HkAdm α l` be used at any smaller order `k ≤ l`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-- **`HkMem` descends in the order.**  For a function `g` smooth on a neighbourhood of
the closed quadrant, membership `HkMem α l g` at order `l` implies membership
`HkMem α k g` at every lower order `k ≤ l`.

This is the iteration of the one-step monotonicity `Work.Coercivity.HkMem_mono`
(`HkMem α (m+1) g → HkMem α m g`), which is available because `g` is smooth. -/
theorem HkMem_descend (α : ℝ) {g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd g) :
    ∀ {k l : ℕ}, k ≤ l → Work.Spaces.HkMem α l g → Work.Spaces.HkMem α k g := by
  intro k l
  induction l with
  | zero =>
      intro hkl h
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkl
      subst hk
      exact h
  | succ m ih =>
      intro hkl h
      rcases eq_or_lt_of_le hkl with h_eq | h_lt
      · subst h_eq
        exact h
      · exact ih (Nat.lt_succ_iff.mp h_lt) (Work.Coercivity.HkMem_mono α m hsm h)

/-- **`HkAdm` is monotone in the order.**  A function admissible at order `l` is
admissible at every lower order `k ≤ l`. -/
theorem HkAdm_mono (α : ℝ) {k l : ℕ} (hkl : k ≤ l) {f : ℝ → ℝ → ℝ}
    (h : Work.Coercivity.HkAdm α l f) : Work.Coercivity.HkAdm α k f := by
  obtain ⟨hsm, hmem, hL12⟩ := h
  refine ⟨hsm, ?_, ?_⟩
  · -- membership of every lower mixed derivative, handed down from order `l`
    intro a b hab
    have hsmab : Work.Spaces.SmoothNbhd (Work.Spaces.mixed b a f) :=
      Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm a) b
    exact HkMem_descend α hsmab hkl (hmem a b (le_trans hab hkl))
  · -- the `L₁₂`-zero-mode clause does not mention `k`
    intro a b hab
    exact hL12 a b (le_trans hab hkl)

end Work.FTS.CoercivityStep.Norm
