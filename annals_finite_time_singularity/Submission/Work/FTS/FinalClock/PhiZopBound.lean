/-
# The boundedness of the `Zop`-iterates of `z ↦ 3/(1+z)` up to order four

`Zop u = z ↦ z·u'(z)` (`Work.Spaces.Zop`) is the one-dimensional radial derivation `D_z`.
This file proves that the first five `Zop`-iterates of `Phi(z) = 3/(1+z)` are bounded by `100`
on `[0,∞)`.

The function `z ↦ 1/(1+z)` is the constant `1` minus the profile `z/(1+z)` whose iterated
radial derivatives were already bounded by `1` in
`Submission/Work/FTS/NonlinRows/NRow10aux/phiSelfFacts.lean` (`phiSelf_DzdIter_bound`).  Since
`Zop` is a derivation killing the constants, its iterates of `1 - z/(1+z)` are minus the
iterates of `z/(1+z)` (from order `1` on), and the iterates of `3/(1+z) = 3·(1 - z/(1+z))` are
`-3` times those of `z/(1+z)`; this gives the bound `3 ≤ 100`.

The three elementary facts used are unconditional: `deriv` of a negation and of a constant
minus a function behave as expected (`deriv_neg`, `deriv_const_sub`), and `Zop`-iterates
respect equality of functions on an open set
(`Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn`).
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.NonlinRows.NRow10aux.phiSelfFacts
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Set Filter

namespace Work.FTS.FinalClock

/-! ## `Zop` on a negated or shifted function -/

/-- `Zop` commutes with pointwise negation: this is `deriv_const_sub` with the constant `0`,
since `-h z = 0 - h z`. -/
lemma Zop_neg_fun (h : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => - h z) = fun z => - Work.Spaces.Zop h z := by
  have h' : (fun z : ℝ => - h z) = fun z => (0 : ℝ) - h z := by
    funext z
    ring
  rw [h']
  funext z
  simp only [Work.Spaces.Zop]
  rw [deriv_const_sub]
  ring

/-- `Zop` of a constant minus a function is minus `Zop` of the function. -/
lemma Zop_const_sub_fun (c : ℝ) (h : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => c - h z) = fun z => - Work.Spaces.Zop h z := by
  funext z
  simp only [Work.Spaces.Zop]
  rw [deriv_const_sub]
  ring

/-- The same at the level of the iterates, for order `≥ 1` (the order `0` iterate is the
function itself, for which the identity fails). -/
lemma Zop_iter_const_sub_fun (c : ℝ) (h : ℝ → ℝ) (b : ℕ) (hb : 1 ≤ b) :
    Work.Spaces.Zop^[b] (fun z => c - h z) = fun z => - Work.Spaces.Zop^[b] h z := by
  induction b with
  | zero => exact absurd hb (by omega)
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0]
        simpa using Zop_const_sub_fun c h
      · have ihk : Work.Spaces.Zop^[k] (fun z => c - h z)
            = fun z => - Work.Spaces.Zop^[k] h z := ih hkpos
        calc Work.Spaces.Zop^[k + 1] (fun z => c - h z)
            = Work.Spaces.Zop (Work.Spaces.Zop^[k] (fun z => c - h z)) :=
                Function.iterate_succ_apply' _ k _
          _ = Work.Spaces.Zop (fun z => - Work.Spaces.Zop^[k] h z) := by rw [ihk]
          _ = fun z => - Work.Spaces.Zop (Work.Spaces.Zop^[k] h) z := Zop_neg_fun _
          _ = fun z => - Work.Spaces.Zop^[k + 1] h z := by
                rw [Function.iterate_succ_apply' Work.Spaces.Zop k h]

/-! ## The relation between the iterates of `3/(1+z)` and of `z/(1+z)` -/

/-- For order `b ≥ 1` and `z > -1` (where `1/(1+z) = 1 - z/(1+z)`), the `b`-th `Zop`-iterate
of `3/(1+z)` is `-3` times the `b`-th iterate of `z/(1+z)`. -/
lemma Zop_iter_three_div_eq (b : ℕ) (hb : 1 ≤ b) {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
      = -3 * Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z := by
  have hconst : (fun z : ℝ => 3 / (1 + z)) = fun z => 3 * (1 / (1 + z)) := by
    funext z
    rw [div_eq_mul_inv, one_div]
  have hcongr : Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z
      = Work.Spaces.Zop^[b] (fun z : ℝ => 1 - z / (1 + z)) z :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi
      (fun w hw => by
        have hw1 : (1 : ℝ) + w ≠ 0 := by
          have := Set.mem_Ioi.mp hw
          linarith
        field_simp
        ring)
      hz
  have hstep := Zop_iter_const_sub_fun (1 : ℝ) (fun z : ℝ => z / (1 + z)) b hb
  have hcm : Work.Spaces.Zop^[b] (fun z : ℝ => 3 * (1 / (1 + z))) z
      = 3 * Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z := by
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
  calc Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
      = Work.Spaces.Zop^[b] (fun z : ℝ => 3 * (1 / (1 + z))) z := by rw [hconst]
    _ = 3 * Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z := hcm
    _ = 3 * Work.Spaces.Zop^[b] (fun z : ℝ => 1 - z / (1 + z)) z := by rw [hcongr]
    _ = 3 * (- Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z) := by rw [hstep]
    _ = -3 * Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z := by ring

/-! ## The bound -/

theorem PhiZopBound : ∀ (b : ℕ) (hb : b ≤ 4) (z : ℝ), 0 ≤ z →
    |Work.Spaces.Zop^[b] (fun z => 3 / (1 + z)) z| ≤ 100 := by
  intro b hb z hz
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    have h1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : 3 / (1 + z) ≤ 3 := by
      rw [div_le_iff₀ h1]
      linarith
    have h3 : 0 ≤ 3 / (1 + z) := by positivity
    rw [Function.iterate_zero_apply, abs_of_nonneg h3]
    linarith
  · rw [Zop_iter_three_div_eq b hbpos (by linarith)]
    have hbnd : |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z| ≤ 1 := by
      rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b
        (fun z : ℝ => z / (1 + z))]
      exact Work.FTS.NonlinRows.NRow10aux.phiSelf_DzdIter_bound b hb z hz
    rw [abs_mul, show |(-3 : ℝ)| = 3 by norm_num]
    nlinarith [abs_nonneg (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z)) z)]

end Work.FTS.FinalClock
