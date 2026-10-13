/-
# `Work.FTS.StrongPersist.L3Rhs.window_le_slot` — the unit window is dominated by the slot

On the unit window `[1,2] ⊂ [0,∞) = Iz` the radial weight `w(z) = (1+z)²/z²` is `≥ 1`
(indeed `≥ 9/4`, its minimum being attained at `z = 2`), so the weighted square
`(v z · w z)²` dominates the plain square `(v z)²` there.  Hence

  `∫_{1..2} v² ≤ ∫_{[1,2]} (v·w)² ≤ ∫_{[0,∞)} (v·w)²`,

the last step being monotonicity of the set integral in the domain (only the
integrability of the larger integrand on `Iz` is needed).

The two monotonicity steps use

* `MeasureTheory.integral_mono_of_nonneg` (function domination on a fixed set; it
  needs integrability of the *larger* function only, which matters because `v` is an
  arbitrary function and `v²` need not be a.e. measurable),
* `MeasureTheory.setIntegral_mono_set` (domain inclusion, again with integrability of
  the larger integrand only).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open MeasureTheory Set

theorem window_le_slot {v : ℝ → ℝ}
    (hv : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz) :
    ∫ x in (1 : ℝ)..2, (v x) ^ 2
      ≤ ∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2 := by
  -- On `(1,2)` the weight is at least `1`.
  have hw1 : ∀ x ∈ Set.Ioc (1 : ℝ) 2, 1 ≤ Work.Spaces.w x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx.1.le
    rw [Work.Spaces.w, one_le_div (pow_pos hx0 2)]
    nlinarith [hx0]
  -- Hence `(v x)² ≤ (v x · w x)²` pointwise there.
  have hpt : ∀ x ∈ Set.Ioc (1 : ℝ) 2, (v x) ^ 2 ≤ (v x * Work.Spaces.w x) ^ 2 := by
    intro x hx
    have hwx : 1 ≤ Work.Spaces.w x := hw1 x hx
    have hw0 : 0 ≤ Work.Spaces.w x := le_trans zero_le_one hwx
    have hle : |v x| ≤ |v x| * Work.Spaces.w x := by
      calc |v x| = |v x| * 1 := (mul_one _).symm
        _ ≤ |v x| * Work.Spaces.w x := by gcongr
    have hsq : (v x) ^ 2 = |v x| ^ 2 := (sq_abs _).symm
    have hsq2 : (v x * Work.Spaces.w x) ^ 2 = (|v x| * Work.Spaces.w x) ^ 2 := by
      rw [← sq_abs (v x * Work.Spaces.w x), abs_mul, abs_of_nonneg hw0]
    rw [hsq, hsq2]
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  have hsub : Set.Ioc (1 : ℝ) 2 ⊆ Work.Spaces.Iz := by
    intro x hx
    exact le_trans zero_le_one hx.1.le
  have hinteg : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2)
      (Set.Ioc (1 : ℝ) 2) :=
    hv.mono_set hsub
  -- Function domination on the fixed set `(1,2)`.
  have hmono : ∫ x in Set.Ioc (1 : ℝ) 2, (v x) ^ 2
      ≤ ∫ x in Set.Ioc (1 : ℝ) 2, (v x * Work.Spaces.w x) ^ 2 :=
    integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hinteg
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => hpt x hx))
  -- Domain inclusion `(1,2) ⊆ [0,∞)`.
  have hsub2 : ∫ x in Set.Ioc (1 : ℝ) 2, (v x * Work.Spaces.w x) ^ 2
      ≤ ∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2 :=
    setIntegral_mono_set hv (ae_of_all _ fun x => sq_nonneg _) hsub.eventuallySubset
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  exact le_trans hmono hsub2

end Work.FTS.StrongPersist.L3Rhs
