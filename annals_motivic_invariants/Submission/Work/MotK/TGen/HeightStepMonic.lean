import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotK.TGen

/-- **Height step for a prime of a polynomial ring.**

Let `A` be a Noetherian ring and `P ⊆ A[X]` a prime ideal.  If `P` contains a polynomial `f` with
some coefficient `f.coeff n` not lying in the contraction `p = P ∩ A`, then `P` is strictly larger
than `p·A[X]`, and the height of `P` is at least `ht p + 1`.

The proof uses Mathlib's Krull height theorem for polynomial rings in the form
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`:
`ht P = ht p + ht (P̄)`, where `P̄` is the image of `P` in `A[X]/(p·A[X]) = (A/p)[X]`.
The hypothesis on the coefficient shows that `f ∉ p·A[X]`, i.e. `P̄ ≠ 0`; since `A/p` is a domain,
`P̄` is a nonzero prime of the polynomial ring `(A/p)[X]`, whence `ht P̄ ≥ 1`. -/
theorem HeightStepMonic {A : Type} [CommRing A] [IsNoetherianRing A]
    (P : Ideal (Polynomial A)) [P.IsPrime] (f : Polynomial A) {n : ℕ}
    (hf : f ∈ P) (hn : f.coeff n ∉ P.comap Polynomial.C) :
    (P.comap Polynomial.C).height + 1 ≤ P.height := by
  -- the contraction `p = P ∩ A` is prime and `P` lies over it
  haveI : (P.comap Polynomial.C).IsPrime := inferInstance
  haveI hLO : P.LiesOver (P.comap Polynomial.C) :=
    ⟨by rw [Ideal.under_def, Polynomial.algebraMap_eq]⟩
  -- Krull's height theorem for the polynomial ring
  have hkey :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.comap Polynomial.C) P
  -- the quotient `A[X]/(p·A[X])` is a domain
  haveI hdom : IsDomain (Polynomial A ⧸ Ideal.map Polynomial.C (P.comap Polynomial.C)) :=
    Ideal.isDomain_map_C_quotient inferInstance
  -- `f ∉ p·A[X]`, so its class in the quotient is nonzero
  have hmkf : (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C))) f ≠ 0 := by
    intro h
    exact hn (Ideal.mem_map_C_iff.mp (Ideal.Quotient.eq_zero_iff_mem.mp h) n)
  -- hence the image of `P` is a nonzero prime ideal of the quotient
  haveI : (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C)))).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (I := Ideal.map Polynomial.C (P.comap Polynomial.C))
      (p := P) (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have hP'ne : (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C)))) ≠ ⊥ := by
    intro h
    refine hmkf ?_
    have : (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C))) f
        ∈ P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C))) :=
      Ideal.mem_map_of_mem _ hf
    rwa [h] at this
  -- a nonzero prime ideal of a domain has height at least one
  have h1 : (1 : ℕ∞) ≤
      (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C)))).height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime
      (show (⊥ : Ideal (Polynomial A ⧸ Ideal.map Polynomial.C (P.comap Polynomial.C)))
          < (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C)))) from
        bot_lt_iff_ne_bot.mpr hP'ne)
    simpa [Ideal.height_bot] using h
  calc (P.comap Polynomial.C).height + 1
      ≤ (P.comap Polynomial.C).height +
          (P.map (Ideal.Quotient.mk (Ideal.map Polynomial.C (P.comap Polynomial.C)))).height :=
        add_le_add le_rfl h1
    _ = P.height := hkey.symm

end Work.MotK.TGen
