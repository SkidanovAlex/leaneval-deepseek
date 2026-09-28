import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.DNC

/-- The absolute value of a single coordinate of an integer vector is at most its
Euclidean norm. -/
private lemma natAbs_coord_le_eNorm {ι : Type*} [Fintype ι] (a : ι → ℤ) (i : ι) :
    ((a i).natAbs : ℝ) ≤ Work.HP.eNorm a := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [Work.HP.eNorm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun j => ((a j : ℝ)) ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

theorem gcd_natAbs_le_floor {ι : Type*} [Fintype ι] (a : ι → ℤ) (ha : a ≠ 0) (A : ℝ)
    (hA : 0 ≤ A) (h : Work.HP.eNorm a ≤ A) :
    (Finset.univ.gcd a).natAbs ≤ ⌊A⌋₊ := by
  rw [Nat.le_floor_iff hA]
  -- `a ≠ 0` supplies a nonzero coordinate, against which we may bound the gcd.
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hdvd : Finset.univ.gcd a ∣ a i := Finset.gcd_dvd (Finset.mem_univ i)
  have hnat : (Finset.univ.gcd a).natAbs ≤ (a i).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hi) (Int.natAbs_dvd_natAbs.mpr hdvd)
  calc ((Finset.univ.gcd a).natAbs : ℝ) ≤ ((a i).natAbs : ℝ) := by exact_mod_cast hnat
    _ ≤ Work.HP.eNorm a := natAbs_coord_le_eNorm a i
    _ ≤ A := h

end Work.HP.DNC
