import Mathlib
import Submission.Work.MotA.quotient_vertical

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotA

/-- **`A1` companion.**  For a prime `g ∈ 𝕜[t]`, the element `g(x₀)` of the polynomial ring
`𝕜[x₀,…,xₙ]` (the image of `g` under the substitution `t ↦ x₀`) is prime again.

This is the element-level statement of `Work.MotA.quotient_vertical`: the quotient
`𝕜[x₀,…,xₙ] ⧸ (g(x₀))` is the polynomial ring over the field `𝕜[t] ⧸ (g)` (via
`quotient_vertical`), hence a domain, so `(g(x₀))` is a prime ideal; since `g(x₀) ≠ 0` this is
equivalent to `g(x₀)` being a prime element. -/
theorem prime_aeval_X0 (𝕜 : Type) [Field 𝕜] (n : ℕ) (g : Polynomial 𝕜) (hg : Prime g) :
    Prime (Polynomial.aeval (MvPolynomial.X 0) g : MvPolynomial (Fin (n + 1)) 𝕜) := by
  classical
  set P : MvPolynomial (Fin (n + 1)) 𝕜 :=
    (Polynomial.aeval (MvPolynomial.X 0) g : MvPolynomial (Fin (n + 1)) 𝕜) with hP
  -- The quotient `𝕜[x₀,…,xₙ] ⧸ (g(x₀))` is a polynomial ring over the domain `𝕜[t] ⧸ (g)`.
  obtain ⟨e⟩ := quotient_vertical 𝕜 n g hg
  haveI hgp : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hg.ne_zero).mpr hg
  haveI : IsDomain (Polynomial 𝕜 ⧸ Ideal.span {g}) := inferInstance
  haveI : IsDomain (MvPolynomial (Fin n) (Polynomial 𝕜 ⧸ Ideal.span {g})) := inferInstance
  -- The composite `R → R ⧸ (g(x₀)) → 𝕜[y₁,…,yₙ] ⧸ (g)` is a ring homomorphism into a domain
  -- whose kernel is exactly `(g(x₀))`; hence `(g(x₀))` is a prime ideal.
  have hker : RingHom.ker ((e : (MvPolynomial (Fin (n + 1)) 𝕜 ⧸ Ideal.span {P}) →+*
        MvPolynomial (Fin n) (Polynomial 𝕜 ⧸ Ideal.span {g})).comp
      (Ideal.Quotient.mk (Ideal.span {P}))) = Ideal.span {P} := by
    rw [RingHom.ker_comp_of_injective _ (AlgEquiv.injective e), Ideal.mk_ker]
  have hprime : (Ideal.span {P}).IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime _
  -- `g(x₀) ≠ 0`: this is the injectivity of the substitution `t ↦ x₀`, obtained by writing the
  -- substitution as `𝕜[t] ≃ 𝕜[x₀] ↪ 𝕜[x₀,…,xₙ]`.
  have hne : P ≠ 0 := by
    have hsymm : ((MvPolynomial.uniqueAlgEquiv 𝕜 (Fin 1)).symm g : MvPolynomial (Fin 1) 𝕜) ≠ 0 := by
      simpa using (MvPolynomial.uniqueAlgEquiv 𝕜 (Fin 1)).symm.injective.ne hg.ne_zero
    have hPeq : P = MvPolynomial.renameEquiv 𝕜 (finCongr (Nat.add_comm 1 n))
        (MvPolynomial.rename (Fin.castAdd n)
          ((MvPolynomial.uniqueAlgEquiv 𝕜 (Fin 1)).symm g : MvPolynomial (Fin 1) 𝕜)) := by
      rw [hP, ← renameEquiv_finCongr_aeval_X0 𝕜 n g, ← rename_castAdd_uniqueAlgEquiv_symm 𝕜 n g]
    rw [hPeq]
    exact fun h => hsymm (MvPolynomial.rename_injective (Fin.castAdd n) (Fin.castAdd_injective 1 n)
        ((MvPolynomial.renameEquiv 𝕜 (finCongr (Nat.add_comm 1 n))).injective h))
  exact (Ideal.span_singleton_prime hne).mp hprime

end Work.MotA
