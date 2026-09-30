import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BW

open Polynomial

/-- **Conclusion of the argument.** Let `P ∈ ℤ[X]` be monic irreducible of degree `> 1` and let
`α` be one of its complex roots.  If for some `k ≥ 1` the product `∏_z (z^k - 1)` over the roots
`z` of `P` vanishes, then `α^k = 1`.

Indeed `z^k = 1` for some root `z`, so `minpoly ℚ z` divides `X^k - 1`; since `P` is monic
irreducible over `ℤ` (hence over `ℚ`, by Gauss) and both `α` and `z` are roots of `P`, they have
the same minimal polynomial, so `X^k - 1` also annihilates `α`. -/
theorem pow_eq_one_of_prod_roots_vanishes (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree) {α : ℂ}
    (hα : (P.map (Int.castRingHom ℂ)).IsRoot α) {k : ℕ} (hk : 1 ≤ k)
    (h0 : ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k - 1)).prod = 0) :
    α ^ k = 1 := by
  -- `P` viewed over `ℚ`, and the bridge between being a complex root of the `ℂ`-image of `P`
  -- and being annihilated by the image of `P` in `ℚ[X]`.
  have key : ∀ x : ℂ,
      (P.map (Int.castRingHom ℂ)).IsRoot x ↔ Polynomial.aeval x (P.map (Int.castRingHom ℚ)) = 0 := by
    intro x
    have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    have heq : (P.map (Int.castRingHom ℂ)).eval x
        = Polynomial.aeval x (P.map (Int.castRingHom ℚ)) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      congr 1
      rw [← hcomp, Polynomial.map_map]
    rw [Polynomial.IsRoot.def, heq]
  -- The vanishing product has a zero factor: some complex root `z` of `P` satisfies `z^k = 1`.
  obtain ⟨z, hzmem, hz0⟩ :
      ∃ z ∈ (P.map (Int.castRingHom ℂ)).roots, z ^ k - 1 = 0 := by
    have hmem : (0 : ℂ) ∈ (P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k - 1) :=
      Multiset.prod_eq_zero_iff.mp h0
    obtain ⟨z, hz, hzz⟩ := Multiset.mem_map.mp hmem
    exact ⟨z, hz, hzz⟩
  have hzk : z ^ k = 1 := sub_eq_zero.mp hz0
  have hmap_ne : P.map (Int.castRingHom ℂ) ≠ 0 := (hP.map (Int.castRingHom ℂ)).ne_zero
  have hzroot : (P.map (Int.castRingHom ℂ)).IsRoot z := (Polynomial.mem_roots hmap_ne).mp hzmem
  have hzₐ : Polynomial.aeval z (P.map (Int.castRingHom ℚ)) = 0 := (key z).mp hzroot
  -- Gauss's lemma: `P` stays irreducible after extending scalars from `ℤ` to `ℚ`.
  have hcompZ : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := RingHom.ext_int _ _
  have hirrQ : Irreducible (P.map (Int.castRingHom ℚ)) := by
    rw [← hcompZ]
    exact (hP.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirr
  have hmonicQ : (P.map (Int.castRingHom ℚ)).Monic := hP.map _
  -- `z` and `α` have the same minimal polynomial over `ℚ`, namely the image of `P`.
  have hmin : minpoly ℚ z = P.map (Int.castRingHom ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirrQ hzₐ hmonicQ).symm
  -- Hence `X^k - 1` is a multiple of that minimal polynomial.
  have hdvd : P.map (Int.castRingHom ℚ) ∣ (Polynomial.X ^ k - 1 : Polynomial ℚ) := by
    rw [← hmin]
    exact minpoly.dvd ℚ z (by rw [map_sub, map_pow, aeval_X, aeval_one, hzk, sub_self])
  obtain ⟨S, hS⟩ := hdvd
  -- And `α`, also a root of `P`, is thereby annihilated by `X^k - 1`.
  have hαₐ : Polynomial.aeval α (P.map (Int.castRingHom ℚ)) = 0 := (key α).mp hα
  have hzX : Polynomial.aeval α (Polynomial.X ^ k - 1 : Polynomial ℚ) = 0 := by
    rw [hS, map_mul, hαₐ, zero_mul]
  rw [map_sub, map_pow, aeval_X, aeval_one] at hzX
  exact sub_eq_zero.mp hzX

end Work.BW
