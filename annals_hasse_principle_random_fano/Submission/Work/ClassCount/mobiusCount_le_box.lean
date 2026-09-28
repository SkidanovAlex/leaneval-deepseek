import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.Q44Geom.ncard_ball_le

namespace Work.ClassCount

open Finset

/-- A subset of integer vectors all of whose elements have Euclidean norm `≤ R` has at most
`(2 ⌈R⌉₊ + 1) ^ (card ι)` elements.  This is the box-counting refinement of
`Work.Q44Geom.ncard_ball_le` to arbitrary subsets. -/
lemma ncard_le_box {ι : Type*} [Fintype ι] (s : Set (ι → ℤ)) (R : ℝ)
    (h : ∀ v ∈ s, Work.HP.eNorm v ≤ R) :
    (s.ncard : ℝ) ≤ (2 * (⌈R⌉₊ : ℝ) + 1) ^ Fintype.card ι := by
  classical
  set m : ℕ := ⌈R⌉₊ with hm
  have hsub : s ⊆ ↑(Fintype.piFinset (fun _ : ι => Finset.Icc (-(m:ℤ)) (m:ℤ))) := by
    intro v hv
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := Work.Q44Geom.abs_coord_le_eNorm_aux v i
    have h2 : |((v i : ℤ) : ℝ)| ≤ (m : ℝ) := by
      refine le_trans (le_trans h1 (h v hv)) ?_
      rw [hm]; exact Nat.le_ceil R
    have h4 := abs_le.mp h2
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩
  have hfinite : (Fintype.piFinset (fun _ : ι => Finset.Icc (-(m:ℤ)) (m:ℤ)) : Set (ι → ℤ)).Finite :=
    (Fintype.piFinset _).finite_toSet
  have hle := Set.ncard_le_ncard hsub hfinite
  have hcardIcc : (Finset.Icc (-(m:ℤ)) (m:ℤ)).card = 2 * m + 1 := by
    rw [Int.card_Icc]
    have hc : (m:ℤ) + 1 - (-(m:ℤ)) = ((2*m+1 : ℕ) : ℤ) := by push_cast; ring
    rw [hc, Int.toNat_natCast]
  have hcard : (Fintype.piFinset (fun _ : ι => Finset.Icc (-(m:ℤ)) (m:ℤ))).card
      = (2 * m + 1) ^ Fintype.card ι := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcardIcc]
  have hleR : (s.ncard : ℝ)
      ≤ ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(m:ℤ)) (m:ℤ))).card : ℝ) := by
    exact_mod_cast hle
  calc (s.ncard : ℝ)
      ≤ ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(m:ℤ)) (m:ℤ))).card : ℝ) := hleR
    _ = (2 * (m:ℝ) + 1) ^ Fintype.card ι := by rw [hcard]; push_cast; ring
    _ = (2 * (⌈R⌉₊ : ℝ) + 1) ^ Fintype.card ι := by rw [hm]

/-- The `k`-th Möbius summand `mobiusCount` is bounded by the size of the box of integer points
of side `2 ⌈R/k⌉₊ + 1`, since every vector counted has Euclidean norm at most `R/k`. -/
theorem mobiusCount_le_box (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (b : Fin (n + 1) → ℤ)
    (W k : ℕ) (α R : ℝ) :
    ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
      ≤ (2 * (⌈R / (k : ℝ)⌉₊ : ℝ) + 1) ^ (n + 1) := by
  rw [Work.HP.mobiusCount]
  apply le_trans (ncard_le_box _ (R / (k : ℝ)) (fun v hv => hv.2.2.1))
  simp

end Work.ClassCount
