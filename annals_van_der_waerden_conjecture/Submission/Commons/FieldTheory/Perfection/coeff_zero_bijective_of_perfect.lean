import Mathlib.RingTheory.Perfection

/-!
# The coefficient at `0` of the perfection of a perfect ring is bijective

If `R` is a perfect ring of prime characteristic `p` (in the sense of Serre, i.e. its Frobenius
endomorphism is bijective), then every element of `R` extends uniquely to a compatible sequence of
`p`-th roots — i.e. to an element of `Perfection R p`. Hence the canonical map
`Perfection.coeff R p 0 : Perfection R p →+* R` sending a compatible sequence to its zeroth
coordinate is bijective.

* Injectivity: two compatible sequences agreeing at position `0` agree everywhere, by induction
  using injectivity of the `p`-th power map on `R`.
* Surjectivity: given `x : R`, repeatedly choose `p`-th roots using surjectivity of Frobenius
  (provided by Mathlib's `Perfection.coeff_surjective`).
-/

namespace Commons.FieldTheory.Perfection

theorem coeff_zero_bijective_of_perfect (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommSemiring R] [CharP R p] [PerfectRing R p] :
    Function.Bijective (Perfection.coeff R p 0) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity: recover all coefficients from the zeroth one.
    intro f g hfg
    apply Perfection.ext
    intro n
    induction n with
    | zero => simpa using hfg
    | succ n ih =>
      -- `(coeff (n+1) f) ^ p = coeff n f` and likewise for `g`; use injectivity of `x ↦ x ^ p`.
      apply (PerfectRing.bijective_frobenius (R := R) (p := p)).1
      calc
        (Perfection.coeff R p (n + 1)) f ^ p = (Perfection.coeff R p n) f :=
          Perfection.coeff_pow_p' f n
        _ = (Perfection.coeff R p n) g := ih
        _ = (Perfection.coeff R p (n + 1)) g ^ p := (Perfection.coeff_pow_p' g n).symm
  · -- Surjectivity: Frobenius is surjective on a perfect ring.
    exact Perfection.coeff_surjective (surjective_frobenius R p) 0

end Commons.FieldTheory.Perfection