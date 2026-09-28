import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.PairsAux

namespace Work.Q44Geom

open Finset

/-- Every coordinate of an integer vector is bounded in absolute value by its Euclidean norm. -/
lemma abs_coord_le_eNorm_aux {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |((v i : ℤ) : ℝ)| ≤ Work.HP.eNorm v := by
  have h1 : (((v i : ℤ) : ℝ)) ^ 2 ≤ ∑ j, (((v j : ℤ) : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (((v j : ℤ) : ℝ))) (Finset.mem_univ i)
  calc |((v i : ℤ) : ℝ)| = Real.sqrt ((((v i : ℤ) : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (((v j : ℤ) : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Work.HP.eNorm v := rfl

/-- The number of integer vectors of Euclidean norm `≤ R` is at most the size of the box
of integer points of side `2 * ⌈R⌉₊ + 1` in each coordinate. -/
theorem ncard_ball_le {ι : Type*} [Fintype ι] (R : ℝ) :
    (({A : ι → ℤ | Work.HP.eNorm A ≤ R} : Set (ι → ℤ)).ncard : ℝ)
      ≤ (2 * (⌈R⌉₊ : ℝ) + 1) ^ Fintype.card ι := by
  classical
  set n : ℕ := ⌈R⌉₊ with hn
  have hsub : ({A : ι → ℤ | Work.HP.eNorm A ≤ R} : Set (ι → ℤ))
      ⊆ ↑(Fintype.piFinset (fun _ : ι => Finset.Icc (-(n:ℤ)) (n:ℤ))) := by
    intro v hv
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := abs_coord_le_eNorm_aux v i
    have h2 : |((v i : ℤ) : ℝ)| ≤ (n : ℝ) := by
      refine le_trans (le_trans h1 hv) ?_
      rw [hn]; exact Nat.le_ceil R
    have h4 := abs_le.mp h2
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩
  have hfinite : (Fintype.piFinset (fun _ : ι => Finset.Icc (-(n:ℤ)) (n:ℤ)) : Set (ι → ℤ)).Finite :=
    (Fintype.piFinset _).finite_toSet
  have hle := Set.ncard_le_ncard hsub hfinite
  have hcardIcc : (Finset.Icc (-(n:ℤ)) (n:ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    have h : (n:ℤ) + 1 - (-(n:ℤ)) = ((2*n+1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  have hcard : (Fintype.piFinset (fun _ : ι => Finset.Icc (-(n:ℤ)) (n:ℤ))).card
      = (2 * n + 1) ^ Fintype.card ι := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcardIcc]
  have hleR : (({A : ι → ℤ | Work.HP.eNorm A ≤ R} : Set (ι → ℤ)).ncard : ℝ)
      ≤ ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(n:ℤ)) (n:ℤ))).card : ℝ) := by
    exact_mod_cast hle
  have hfin_card : ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(n:ℤ)) (n:ℤ))).card : ℝ)
      = (2 * (n : ℝ) + 1) ^ Fintype.card ι := by
    rw [hcard]; push_cast; ring
  calc (({A : ι → ℤ | Work.HP.eNorm A ≤ R} : Set (ι → ℤ)).ncard : ℝ)
      ≤ ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(n:ℤ)) (n:ℤ))).card : ℝ) := hleR
    _ = (2 * (n : ℝ) + 1) ^ Fintype.card ι := hfin_card
    _ = (2 * (⌈R⌉₊ : ℝ) + 1) ^ Fintype.card ι := by rw [hn]

end Work.Q44Geom
