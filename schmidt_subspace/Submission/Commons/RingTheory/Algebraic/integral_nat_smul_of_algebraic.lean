import Mathlib.RingTheory.Algebraic.Denominator
import Mathlib.RingTheory.Localization.Integral

namespace Commons.RingTheory.Algebraic

/-- Auxiliary: on a ring `K` there is at most one `ℤ`-algebra structure, so being integral over
`ℤ` does not depend on which structure is used. -/
private lemma isIntegral_int_algebra_eq {K : Type*} [Ring K] (x : K) (A B : Algebra ℤ K) :
    @IsIntegral ℤ K _ _ A x = @IsIntegral ℤ K _ _ B x :=
  congrArg (fun C : Algebra ℤ K => @IsIntegral ℤ K _ _ C x) (Subsingleton.elim A B)

/-- Auxiliary version with the canonical `ℤ`-algebra structure on `K`: an element of a `ℚ`-algebra
which is algebraic over `ℚ` becomes integral over `ℤ` after multiplication by a positive natural
number. -/
private lemma exists_nat_smul_isIntegral_of_isAlgebraic {K : Type*} [Field K] [Algebra ℚ K]
    {x : K} (h : IsAlgebraic ℚ x) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x) := by
  have hZ : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr h
  refine ⟨Algebra.natDenominator x,
    Nat.pos_of_ne_zero (IsAlgebraic.natDenominator_ne_zero hZ), ?_⟩
  simpa only [nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul x

/-- Clearing denominators: an element of a `ℚ`-algebra which is algebraic over `ℚ` becomes
integral over `ℤ` after multiplication by a positive natural number. -/
lemma integral_nat_smul_of_algebraic {K : Type*} [Field K] [Algebra ℚ K] [Algebra ℤ K]
    [IsScalarTower ℤ ℚ K] {x : K} (h : IsAlgebraic ℚ x) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x) := by
  obtain ⟨n, hn, hint⟩ := exists_nat_smul_isIntegral_of_isAlgebraic h
  exact ⟨n, hn, (isIntegral_int_algebra_eq ((n : K) * x) _ (Ring.toIntAlgebra K)).mpr hint⟩

end Commons.RingTheory.Algebraic