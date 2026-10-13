import Mathlib

open Polynomial

namespace Work.DSM5b

/-- If `x : S` is not integral over `R`, then some prime ideal `P` of `S` has the property that the
image of `x` in `S ⧸ P` is not integral over `R`.

The idea: the set `N = {f(x) : f ∈ R[X] monic}` is a multiplicative subset of `S` (the monic
polynomials are closed under multiplication), and `0 ∉ N` exactly because `x` is not integral.
Hence there is a prime ideal `P` of `S` disjoint from `N` (maximal ideal disjoint from a
multiplicative set), and for such a `P` the image of `x` is not integral. -/
theorem exists_isPrime_quotient_not_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (x : S) (hx : ¬ IsIntegral R x) :
    ∃ P : Ideal S, P.IsPrime ∧ ¬ IsIntegral R (Ideal.Quotient.mk P x) := by
  classical
  -- `N` is the multiplicative subset of `S` consisting of the `f(x)` with `f` monic.
  let N : Submonoid S :=
    { carrier := {y | ∃ p : R[X], p.Monic ∧ Polynomial.aeval x p = y}
      one_mem' := ⟨1, Polynomial.monic_one, by simp⟩
      mul_mem' := by
        rintro a b ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, hp.mul hq, by rw [map_mul]⟩ }
  -- Non-integrality of `x` says exactly that `0 ∉ N`.
  have h0N : (0 : S) ∉ N := by
    rintro ⟨p, hp, hp0⟩
    rw [Polynomial.aeval_def] at hp0
    exact hx ⟨p, hp, hp0⟩
  have hdisj : Disjoint ((⊥ : Ideal S) : Set S) (N : Set S) := by
    rw [Set.disjoint_left]
    intro a ha
    rw [SetLike.mem_coe, Ideal.mem_bot] at ha
    rw [ha]
    exact h0N
  -- A prime ideal disjoint from `N`.
  obtain ⟨P, hPprime, -, hPdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal S) N hdisj
  refine ⟨P, hPprime, ?_⟩
  -- If the image of `x` were integral, `f(x) ∈ P` for some monic `f`, contradicting disjointness.
  intro hint
  obtain ⟨p, hp, hp0⟩ := hint
  have h1 : Ideal.Quotient.mk P (Polynomial.aeval x p) = 0 := by
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R P) x p
    simp only [Ideal.Quotient.mkₐ_eq_mk] at h
    rw [Polynomial.aeval_def, hp0] at h
    exact h.symm
  have h2 : Polynomial.aeval x p ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp h1
  have h3 : Polynomial.aeval x p ∈ N := ⟨p, hp, rfl⟩
  exact (Set.disjoint_left.mp hPdisj h2) h3

end Work.DSM5b
