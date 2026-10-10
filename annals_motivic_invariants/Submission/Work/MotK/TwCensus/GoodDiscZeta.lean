import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwCensus

/-- In a field `K` of characteristic `≠ 5` there is a primitive fifth root of unity in the
algebraic closure: the cyclotomic polynomial `Φ₅ = X⁴ + X³ + X² + X + 1` is separable in
characteristic `≠ 5`, so it has a root in the algebraically closed field `AlgebraicClosure K`,
and such a root is exactly a primitive `5`-th root.

The hypothesis `ringChar K ≠ 5` is used only through `(5 : AlgebraicClosure K) ≠ 0`, which is
needed to make `cyclotomic 5` separable / to apply `Polynomial.isRoot_cyclotomic_iff`. -/
theorem GoodDiscZeta (K : Type) [Field K] (hK : ringChar K ≠ 5) :
    ∃ ζ : AlgebraicClosure K, IsPrimitiveRoot ζ 5 := by
  -- `ringChar K ≠ 5` implies `(5 : AlgebraicClosure K) ≠ 0`.
  have h5ne : NeZero (5 : AlgebraicClosure K) := ⟨by
    intro h
    -- apply the (injective) structure map `K → AlgebraicClosure K` to reduce to `K`
    have h5K : (5 : K) = 0 := by
      have key : (algebraMap K (AlgebraicClosure K)) (5 : K) = 0 := by
        change (algebraMap K (AlgebraicClosure K)) ((5 : ℕ) : K) = 0
        rw [map_natCast]
        exact h
      exact (FaithfulSMul.algebraMap_eq_zero_iff K (AlgebraicClosure K)).mp key
    have hdvd : ringChar K ∣ 5 := (ringChar.spec (R := K) 5).1 h5K
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5
    · exact CharP.ringChar_ne_one h1
    · exact hK h5⟩
  -- `Φ₅` has positive degree, so it has a root in the algebraically closed `AlgebraicClosure K`
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 5 (AlgebraicClosure K))
    (Polynomial.degree_cyclotomic_pos 5 (AlgebraicClosure K) (by norm_num)).ne'
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

end Work.MotK.TwCensus
