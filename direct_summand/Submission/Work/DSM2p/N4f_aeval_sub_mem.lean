import Mathlib

namespace Work.DSM2p

/-- Divided-difference membership: for `a, b` in a subring `U` of `L` whose elements
contain the image of the base ring `C`, the difference `aeval a g - aeval b g` is a
multiple of `a - b` by an element of `U`. -/
theorem N4f_aeval_sub_mem {C L : Type*} [CommRing C] [CommRing L] [Algebra C L]
    (U : Subring L) (hU : ∀ c : C, algebraMap C L c ∈ U)
    {a b : L} (ha : a ∈ U) (hb : b ∈ U) (g : Polynomial C) :
    ∃ s ∈ U, Polynomial.aeval a g - Polynomial.aeval b g = (a - b) * s := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨sp, hsp, hpeq⟩ := hp
      obtain ⟨sq, hsq, hqeq⟩ := hq
      refine ⟨sp + sq, U.add_mem hsp hsq, ?_⟩
      have h1 : Polynomial.aeval a (p + q) - Polynomial.aeval b (p + q)
          = (Polynomial.aeval a p - Polynomial.aeval b p)
            + (Polynomial.aeval a q - Polynomial.aeval b q) := by
        rw [map_add, map_add]; ring
      rw [h1, hpeq, hqeq, mul_add]
  | monomial n c =>
      refine ⟨algebraMap C L c * ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i),
        U.mul_mem (hU c)
          (Subring.sum_mem U
            (fun i _ => U.mul_mem (U.pow_mem ha i) (U.pow_mem hb (n - 1 - i)))), ?_⟩
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← mul_sub,
        ← (Commute.all a b).mul_geom_sum₂ n]
      ring

end Work.DSM2p
