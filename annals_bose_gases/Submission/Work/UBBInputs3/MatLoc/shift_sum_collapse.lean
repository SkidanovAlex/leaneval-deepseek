import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.UBBInputs3.MatLoc.gamma_sum_shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

theorem shift_sum_collapse (f : ℤ → ℝ) (p m i : ℕ) (hi : i < m)
    (hsupp : ∀ s : ℤ, (p : ℤ) < |s| → f s = 0) :
    ∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
        (f (s + (i : ℤ) + 1) - f (s + (i : ℤ))) ^ 2
      = ∑ t ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1), (f (t + 1) - f t) ^ 2 := by
  -- The summand is `g u = (f (u+1) - f u)^2`, supported on `Icc (-p-1) p`.
  set g : ℤ → ℝ := fun u => (f (u + 1) - f u) ^ 2 with hg
  have hg_apply : ∀ u : ℤ, g u = (f (u + 1) - f u) ^ 2 := by
    intro u; rw [hg]
  -- g vanishes outside `Icc (-(p:ℤ)-1) (p:ℤ)`.
  have hg_zero : ∀ u : ℤ, u ∉ Finset.Icc (-(p : ℤ) - 1) (p : ℤ) → g u = 0 := by
    intro u hu
    have hu' : u < -(p : ℤ) - 1 ∨ (p : ℤ) < u := by
      rw [Finset.mem_Icc, not_and_or] at hu
      rcases hu with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    rw [hg_apply]
    have h1 : (p : ℤ) < |u| := by
      rcases hu' with h | h
      · exact lt_abs.mpr (Or.inr (by omega))
      · exact lt_abs.mpr (Or.inl h)
    have h2 : (p : ℤ) < |u + 1| := by
      rcases hu' with h | h
      · exact lt_abs.mpr (Or.inr (by omega))
      · exact lt_abs.mpr (Or.inl (by omega))
    rw [hsupp u h1, hsupp (u + 1) h2]; ring
  -- The two index sets of interest.
  set A : Finset ℤ := Finset.Icc (-(p : ℤ) - (m : ℤ) + (i : ℤ))
      ((p : ℤ) + (m : ℤ) + (i : ℤ)) with hA
  set S : Finset ℤ := Finset.Icc (-(p : ℤ) - 1) (p : ℤ) with hS
  have hSA : S ⊆ A := by
    intro x hx
    rw [hS] at hx; rw [hA]
    simp only [Finset.mem_Icc] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    have him : (i : ℤ) ≤ (m : ℤ) - 1 := by omega
    constructor <;> omega
  have hSB : S ⊆ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1) := by
    intro x hx
    rw [hS] at hx
    simp only [Finset.mem_Icc] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    constructor <;> omega
  have hsumA : (∑ u ∈ A, g u) = ∑ u ∈ S, g u :=
    (Finset.sum_subset hSA (fun u _ hu => hg_zero u hu)).symm
  have hsumB : (∑ u ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1), g u) = ∑ u ∈ S, g u :=
    (Finset.sum_subset hSB (fun u _ hu => hg_zero u hu)).symm
  -- Reindex the left-hand sum.
  have hL : (∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
        (f (s + (i : ℤ) + 1) - f (s + (i : ℤ))) ^ 2) = ∑ u ∈ A, g u := by
    have e1 : (∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
          (f (s + (i : ℤ) + 1) - f (s + (i : ℤ))) ^ 2)
        = ∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)), g (s + (i : ℤ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hg_apply]
    rw [e1, sum_Icc_addConst g (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)) (i : ℤ), hA]
  -- Rewrite the right-hand summand.
  have hR : (∑ t ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1), (f (t + 1) - f t) ^ 2)
        = ∑ u ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1), g u := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hg_apply]
  rw [hL, hR, hsumA, hsumB]

end Work.UBBInputs3.MatLoc
