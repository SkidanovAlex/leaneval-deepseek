import Mathlib
import Submission.Work.QuadraticLocalGlobal.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

theorem exists_squarefree_rep (a : ℚˣ) : ∃ (A : ℤ) (hA : A ≠ 0) (s : ℚˣ), Squarefree A.natAbs ∧ Work.HilbertSymbol.intUnit A hA * s ^ 2 = a ∧ A.natAbs ≤ Work.HilbertSymbol.numDenNat a := by
  have hNpos : 0 < numDenNat a := by
    rw [numDenNat]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr a.ne_zero))
      (Rat.den_pos (a : ℚ))
  obtain ⟨u, hu⟩ := exists_intRep_mul_sq a
  have hN : intRep a ≠ 0 := intRep_ne_zero a
  have hNabs : (intRep a).natAbs = numDenNat a := natAbs_intRep a
  obtain ⟨c₀, b₀, hbc₀, hcsq₀⟩ :=
    Nat.sq_mul_squarefree_of_pos' (n := (intRep a).natAbs) (by rw [hNabs]; exact hNpos)
  set c : ℕ := c₀ + 1 with hcdef
  set b : ℕ := b₀ + 1 with hbdef
  have hbc : b ^ 2 * c = (intRep a).natAbs := by rw [hbdef, hcdef]; exact hbc₀
  have hcsq : Squarefree c := by rw [hcdef]; exact hcsq₀
  have hbpos : 0 < b := by rw [hbdef]; exact Nat.succ_pos _
  have hcpos : 0 < c := by rw [hcdef]; exact Nat.succ_pos _
  set A : ℤ := Int.sign (intRep a) * (c : ℤ) with hAdef
  have hAbs : A.natAbs = c := by
    rw [hAdef, Int.natAbs_mul, Int.natAbs_sign, if_neg hN, Int.natAbs_natCast, one_mul]
  have hA : A ≠ 0 := by
    rw [← Int.natAbs_pos, hAbs]
    exact hcpos
  have hNA : intRep a = A * (b : ℤ) ^ 2 := by
    rw [← Int.sign_mul_natAbs (intRep a), ← hbc, hAdef, hbdef]
    push_cast
    ring
  have hu' : ((intRep a : ℤ) : ℚ) * (u : ℚ) ^ 2 = (a : ℚ) := by
    have h := congrArg (fun x : ℚˣ => (x : ℚ)) hu
    simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h
  have hNcast : ((intRep a : ℤ) : ℚ) = (A : ℚ) * (b : ℚ) ^ 2 := by
    rw [hNA]
    push_cast
    ring
  refine ⟨A, hA, intUnit (b : ℤ) (by exact_mod_cast ne_of_gt hbpos) * u, ?_, ?_, ?_⟩
  · rw [hAbs]; exact hcsq
  · apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, intUnit_coe]
    push_cast
    rw [mul_pow, ← mul_assoc, ← hNcast, hu']
  · rw [hAbs, ← hNabs, ← hbc]
    exact Nat.le_mul_of_pos_left c (pow_pos hbpos 2)

end Work.QuadraticLocalGlobal
