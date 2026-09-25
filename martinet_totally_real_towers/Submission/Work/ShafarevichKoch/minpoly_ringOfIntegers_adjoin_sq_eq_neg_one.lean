import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.int_coords_and_norm
import Submission.Work.ClassFieldTower.WitnessField

/-!
# `minpoly` over `𝓞 Kc` of a square root of `-1` in `𝓞 Kc⟮z⟯`

Let `M` be the maximal unramified pro-`2` extension of `Kc = ℚ(√-30030)`, let `z ∈ M.K` satisfy
`z * z = -1` (so that `z ∉ Kc`, because `-1` is not a square in `Kc`), and put
`L = Kc⟮z⟯ = IntermediateField.adjoin Kc {z}`.  If `x ∈ 𝓞 L` satisfies `x * x = -1`, then the
minimal polynomial of `x` over the *ring* `𝓞 Kc` is `X ^ 2 + 1`.

The argument has three steps, none of which uses arithmetic:

* `x` is integral over `𝓞 Kc` (it is an element of the integral closure `𝓞 L = integralClosure ℤ L`
  of `ℤ`, and `ℤ → 𝓞 Kc`);
* the *field* minimal polynomial of the image of `x` in `L` is `X ^ 2 + 1`: this is
  `minpoly.eq_of_irreducible_of_monic` applied to the irreducible polynomial `X ^ 2 + 1`, whose
  irreducibility over `Kc` follows from the hypothesis that `-1` is not a square in `Kc`;
* `minpoly.isIntegrallyClosed_eq_field_fractions` identifies `minpoly Kc` of the image in `L`
  with the image under `𝓞 Kc → Kc` of `minpoly (𝓞 Kc) x`; since that map is injective the two
  polynomials coincide.

The hypothesis `hz` is used only to see that `L` is finite dimensional over `Kc` (equivalently
that `z` is integral over `Kc`), which is what makes `𝓞 L` the fraction ring of `L` and `L` a
number field.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Work.ClassFieldTower
open Polynomial

noncomputable section

namespace Work.ShafarevichKoch

/-- **`minpoly` over `𝓞 Kc` of an element of `𝓞 (Kc⟮z⟯)` squaring to `-1`.**

For `z ∈ M.K` with `z * z = -1` and `-1` not a square in `Kc`, any `x ∈ 𝓞 (Kc⟮z⟯)` with
`x * x = -1` has minimal polynomial `X ^ 2 + 1` over the ring `𝓞 Kc` of integers of `Kc`. -/
theorem minpoly_ringOfIntegers_adjoin_sq_eq_neg_one
    {M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2}
    {z : M.K} (hz : z * z = algebraMap Work.ClassFieldTower.Kc M.K (-1 : Work.ClassFieldTower.Kc))
    (hne : ¬ ∃ w : Work.ClassFieldTower.Kc, w * w = -1)
    (x : NumberField.RingOfIntegers
      ↥(IntermediateField.adjoin Work.ClassFieldTower.Kc ({z} : Set M.K)))
    (hx : (x : ↥(IntermediateField.adjoin Work.ClassFieldTower.Kc ({z} : Set M.K)))
        * (x : ↥(IntermediateField.adjoin Work.ClassFieldTower.Kc ({z} : Set M.K))) = -1) :
    minpoly (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) x = Polynomial.X ^ 2 + 1 := by
  let L : IntermediateField Work.ClassFieldTower.Kc M.K :=
    IntermediateField.adjoin Work.ClassFieldTower.Kc ({z} : Set M.K)
  -- `z` is integral over `Kc`, so `Kc⟮z⟯` is finite dimensional over `Kc` and hence a number
  -- field; this is the only place where `hz` is used.
  have hint : IsIntegral Work.ClassFieldTower.Kc z :=
    IsIntegral.of_pow (n := 2) (by norm_num)
      (by rw [pow_two, hz]; exact isIntegral_algebraMap)
  haveI hfd : FiniteDimensional Work.ClassFieldTower.Kc ↥L :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField ↥L := NumberField.of_module_finite Work.ClassFieldTower.Kc ↥L
  -- (1) `x` is integral over `𝓞 Kc`.
  have hintx : IsIntegral (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) x :=
    Algebra.IsIntegral.isIntegral x
  -- the image of `x` in `L` also squares to `-1`.
  have hy : ((algebraMap (NumberField.RingOfIntegers ↥L) ↥L) x)
      * ((algebraMap (NumberField.RingOfIntegers ↥L) ↥L) x) = -1 := hx
  -- (2) `X ^ 2 + 1` is irreducible over `Kc` because `-1` is not a square in `Kc`.
  have hirr : Irreducible (Polynomial.X ^ 2 + 1 : Polynomial Work.ClassFieldTower.Kc) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [show (Polynomial.X ^ 2 + 1 : Polynomial Work.ClassFieldTower.Kc).natDegree = 2 by
        compute_degree!]
      decide
    · intro w hw
      rw [Polynomial.IsRoot.def] at hw
      have h1 : w ^ 2 + 1 = 0 := by simpa using hw
      refine hne ⟨w, ?_⟩
      rw [pow_two] at h1
      linear_combination h1
  have hroot : aeval ((algebraMap (NumberField.RingOfIntegers ↥L) ↥L) x)
      (Polynomial.X ^ 2 + 1 : Polynomial Work.ClassFieldTower.Kc) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    simp only [Polynomial.eval₂_one]
    rw [pow_two, hy]
    ring
  have hmonic : (Polynomial.X ^ 2 + 1 : Polynomial Work.ClassFieldTower.Kc).Monic := by
    simpa using monic_X_pow_add_C (n := 2) (a := (1 : Work.ClassFieldTower.Kc)) (by norm_num)
  -- so the field minimal polynomial of the image of `x` in `L` is `X ^ 2 + 1`.
  have hfield : minpoly Work.ClassFieldTower.Kc ((algebraMap (NumberField.RingOfIntegers ↥L) ↥L) x)
      = Polynomial.X ^ 2 + 1 :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  -- (3) transport `minpoly` along `𝓞 Kc → Kc` (an injective map of rings).
  have hfr := minpoly.isIntegrallyClosed_eq_field_fractions
    (R := NumberField.RingOfIntegers Work.ClassFieldTower.Kc)
    (S := NumberField.RingOfIntegers ↥L) Work.ClassFieldTower.Kc ↥L hintx
  have hmap : (minpoly (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) x).map
      (algebraMap (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) Work.ClassFieldTower.Kc)
      = Polynomial.X ^ 2 + 1 := by
    rw [← hfr, hfield]
  have hmap2 : ((Polynomial.X ^ 2 + 1
      : Polynomial (NumberField.RingOfIntegers Work.ClassFieldTower.Kc))).map
      (algebraMap (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) Work.ClassFieldTower.Kc)
      = Polynomial.X ^ 2 + 1 := by
    simp
  exact Polynomial.map_injective
    (algebraMap (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) Work.ClassFieldTower.Kc)
    (NumberField.RingOfIntegers.coe_injective) (by rw [hmap, hmap2])

end Work.ShafarevichKoch
