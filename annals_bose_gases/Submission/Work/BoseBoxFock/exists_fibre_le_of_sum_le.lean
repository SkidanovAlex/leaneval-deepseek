import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem exists_fibre_le_of_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (q ν : ι → ℝ)
    {c : ℝ} (hν : ∀ j ∈ s, 0 ≤ ν j) (hq : ∀ j ∈ s, ν j = 0 → q j = 0) (hc : 0 < s.sum ν)
    (h : s.sum q ≤ c * s.sum ν) : ∃ j ∈ s, 0 < ν j ∧ q j ≤ c * ν j := by
  -- `hcon'` is the negation of the conclusion, in "strict" form: every fibre with
  -- positive mass fails the inequality in the strongest way.
  by_contra hcon
  have hcon' : ∀ j ∈ s, 0 < ν j → c * ν j < q j := by
    intro j hj hjpos
    exact not_le.mp (fun hle => hcon ⟨j, hj, hjpos, hle⟩)
  -- Each summand of `∑ c * ν` is dominated by the corresponding summand of `∑ q`;
  -- this uses `hq` to handle the zero-mass fibres.
  have hle : ∀ j ∈ s, c * ν j ≤ q j := by
    intro j hj
    by_cases h0 : ν j = 0
    · rw [h0, hq j hj h0]; simp
    · exact le_of_lt (hcon' j hj (lt_of_le_of_ne (hν j hj) (Ne.symm h0)))
  -- `hc` forces some fibre to have strictly positive mass.
  have hsumpos : ∃ j ∈ s, 0 < ν j := by
    by_contra hc'
    have hnn : ∀ j ∈ s, ν j ≤ 0 := fun j hj => not_lt.mp (fun hpos => hc' ⟨j, hj, hpos⟩)
    have : s.sum ν ≤ 0 := Finset.sum_nonpos hnn
    linarith
  obtain ⟨j, hj, hjpos⟩ := hsumpos
  -- The previous two facts give the strict inequality `∑ c * ν < ∑ q`.
  have hlt : s.sum (fun j => c * ν j) < s.sum q :=
    Finset.sum_lt_sum hle ⟨j, hj, hcon' j hj hjpos⟩
  have hmul : c * s.sum ν = s.sum (fun j => c * ν j) := Finset.mul_sum s ν c
  linarith

end Work.BoseBoxFock
