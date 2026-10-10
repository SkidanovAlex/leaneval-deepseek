import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.CensusBridge

/-- **The residue field at the kernel of a surjective presentation.**

If `θ : K[x₀,…,xₙ₋₁] →ₐ[K] R` is a surjective `K`-algebra homomorphism onto a domain `R`, then the
residue field of the point `ker θ ∈ 𝔸ⁿ_K` (i.e. `Work.MotV.resF K ⟨ker θ, ·⟩`) is the fraction field
of `R`.

This is the first isomorphism theorem (`Ideal.quotientKerAlgEquivOfSurjective`) transported to
fraction fields (`IsFractionRing.algEquivOfAlgEquiv`). -/
theorem resF_ker_algEquiv {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {n : ℕ} (θ : MvPolynomial (Fin n) K →ₐ[K] R) (hsurj : Function.Surjective θ) :
    Nonempty (Work.MotV.resF K ⟨RingHom.ker θ, RingHom.ker_isPrime θ⟩ ≃ₐ[K] FractionRing R) :=
  ⟨IsFractionRing.algEquivOfAlgEquiv (Ideal.quotientKerAlgEquivOfSurjective hsurj)⟩

/-- **(E) The census-by-presentation bridge.**

Let `θ : K[x₀,x₁,x₂] →ₐ[K] R` be a surjective `K`-algebra homomorphism onto a domain `R` whose
fraction field is `RatFunc F` (via `e`), and suppose `θ` has kernel exactly the principal ideal
`(G)`.  Then `(G)` is a height-one prime of `K[x₀,x₁,x₂]`, and the residue field of the
corresponding point of `𝔸³_K` is `RatFunc F`.

(Note: the hypothesis is `Ideal.height`, the ring-theoretic height, not `Order.coheight` on the
bare `PrimeSpectrum`, whose order is inclusion of ideals; on the *scheme* `Work.MotA.polySpec K 3`
the two agree by `AlgebraicGeometry.idealHeight_eq_coheight`.)

This is the "elementary half" of the census of the Crauder–Katz link: it turns an explicit
parametrisation of a ruled divisor (whose image generates the relation ideal `(G)`) into the
`zP_res` / `F_all` conditions of `Work.MotV.LinkCert`. -/
theorem resF_span_eq_ratFunc {K R F : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    [Field F] [Algebra K F] (θ : MvPolynomial (Fin 3) K →ₐ[K] R) (G : MvPolynomial (Fin 3) K)
    (hG : G ≠ 0) (hker : RingHom.ker θ = Ideal.span {G}) (hsurj : Function.Surjective θ)
    (e : FractionRing R ≃ₐ[K] RatFunc F) :
    ∃ h : (Ideal.span {G} : Ideal (MvPolynomial (Fin 3) K)).IsPrime,
      Ideal.height (Ideal.span {G}) = 1 ∧
        Nonempty (Work.MotV.resF K ⟨Ideal.span {G}, h⟩ ≃ₐ[K] RatFunc F) := by
  -- `(G) = ker θ` is the kernel of a map into the domain `R`, hence prime.
  have hprime : (Ideal.span {G} : Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    hker ▸ RingHom.ker_isPrime θ
  -- Krull's principal ideal theorem (`height (span {x}) = 1` for a non-unit nonzerodivisor),
  -- in the form `Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors`.
  have hheight : Ideal.height (Ideal.span {G}) = 1 := by
    refine Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors ?_ ?_
    · rw [mem_nonZeroDivisors_iff]
      exact ⟨fun y hy => (mul_eq_zero.mp hy).elim (fun h => absurd h hG) id,
             fun y hy => (mul_eq_zero.mp hy).elim id (fun h => absurd h hG)⟩
    · intro hunit
      -- if `G` were a unit then `(G) = ⊤` would not be prime
      exact Ideal.IsPrime.ne_top hprime (Ideal.span_singleton_eq_top.mpr hunit)
  refine ⟨hprime, hheight, ?_⟩
  -- Identify the residue field at `(G) = ker θ` and transport the fraction field of `R`.
  show Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.span {G}) ≃ₐ[K] RatFunc F)
  rw [show (Ideal.span {G} : Ideal (MvPolynomial (Fin 3) K)) = RingHom.ker θ from hker.symm]
  exact ⟨(IsFractionRing.algEquivOfAlgEquiv
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)).trans e⟩

end Work.MotK.CensusBridge
