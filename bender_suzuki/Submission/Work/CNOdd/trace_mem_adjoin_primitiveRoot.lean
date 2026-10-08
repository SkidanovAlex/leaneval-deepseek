import Mathlib
import Submission.Work.Clifford.charpoly_roots_pow_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CNOdd

/-- If `T` is an endomorphism of a finite-dimensional complex vector space with `T ^ n = 1`
and `ζ` is a primitive `n`-th root of unity, then `trace T` lies in `ℚ(ζ) = ℚ[ζ]`.

Indeed `T` satisfies `T ^ n = 1`, so every root of the characteristic polynomial of `T` is an
`n`-th root of unity (`charpoly_roots_pow_eq_one`), hence a power of `ζ`.  Over `ℂ` the
characteristic polynomial splits, and the trace is the sum of its roots
(`Module.End.trace_eq_sum_roots_charpoly_of_splits`); a sum of powers of `ζ` lies in the
subalgebra `ℚ[ζ]`. -/
theorem trace_mem_adjoin_primitiveRoot {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) {n : ℕ} (hn : 0 < n) (hT : T ^ n = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    LinearMap.trace ℂ V T ∈ Algebra.adjoin ℚ ({ζ} : Set ℂ) := by
  have hnz : NeZero n := ⟨hn.ne'⟩
  have ht : LinearMap.trace ℂ V T = T.charpoly.roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits T.charpoly)
  rw [ht]
  apply Subalgebra.multiset_sum_mem
  intro a ha
  have ha_pow : a ^ n = 1 := Work.Clifford.charpoly_roots_pow_eq_one T n hT ha
  obtain ⟨i, -, hia⟩ := @IsPrimitiveRoot.eq_pow_of_pow_eq_one ℂ _ _ n hnz ζ a hζ ha_pow
  rw [← hia]
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) i

end Work.CNOdd
