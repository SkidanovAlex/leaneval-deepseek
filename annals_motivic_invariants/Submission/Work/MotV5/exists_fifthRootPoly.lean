import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- In characteristic `5` and over an algebraically closed field, the Frobenius map
`a ↦ a ^ 5` of `M` is bijective (it is injective because `M` is a field of characteristic `5` and
surjective because every element has a `5`-th root in an algebraically closed field), so the
"fifth root" map `φ := (frobeniusEquiv M 5).symm : M →+* M` is a ring homomorphism satisfying
`φ a ^ 5 = a`. -/
theorem exists_fifthRootPoly {M : Type*} [Field M] [IsAlgClosed M] [CharP M 5]
    (A : Polynomial M) :
    ∃ A₀ : Polynomial M, A₀.natDegree = A.natDegree ∧
      (∀ x : RatFunc M, (Polynomial.aeval x A₀) ^ 5 = Polynomial.aeval (x ^ 5) A) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : ExpChar M 5 := inferInstance
  have : PerfectRing M 5 :=
    PerfectRing.ofSurjective M 5 fun y => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 5)
      exact ⟨z, by rw [frobenius_def, hz]⟩
  -- the (inverse) Frobenius ring homomorphism `φ`, with `φ a ^ 5 = a`
  let φ : M →+* M := (frobeniusEquiv M 5).symm
  have hcomp : φ.comp (frobenius M 5) = RingHom.id M :=
    frobeniusEquiv_symm_comp_frobenius M 5
  refine ⟨A.map φ, ?_, ?_⟩
  · exact Polynomial.natDegree_map_eq_of_injective (f := φ)
      (fun _ _ h => (frobeniusEquiv M 5).symm.injective h) A
  · -- the polynomial identity `(A.map φ) ^ 5 = expand M 5 A`
    have hpoly : (A.map φ) ^ 5 = Polynomial.expand M 5 A := by
      have h1 : Polynomial.map (frobenius M 5) (Polynomial.expand M 5 A) = A ^ 5 :=
        Polynomial.map_frobenius_expand 5 A
      have h2 := congrArg (Polynomial.map φ) h1
      rw [Polynomial.map_map, Polynomial.map_pow, hcomp, Polynomial.map_id] at h2
      exact h2.symm
    intro x
    rw [show (Polynomial.aeval x (A.map φ)) ^ 5
          = Polynomial.aeval x ((A.map φ) ^ 5) by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval₂_pow],
      hpoly, Polynomial.expand_aeval]

end Work.MotV5
