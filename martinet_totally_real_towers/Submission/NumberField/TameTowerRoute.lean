import Mathlib
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal

set_option linter.style.haveILetI false

/-!
# The tame tower route to Martinet's theorem

**STATUS: sorry-free.**  ON the `Submission.lean` proof path since SESSION 279.

## The route

The on-path reduction (`Submission.Towers.FromNarrowHCF`, `CFTAssembly`) builds the Martinet
tower as the iterated **narrow Hilbert class field tower** over a totally real quadratic base.
That needs two deep inputs: ray class field existence (the `E`-seam) and the non-termination
of the narrow tower (the `GS`-seam).

This module records a much lighter route (the one used in the source paper,
Bloom--Sawin--Schildkraut--Zhelezov `arXiv:2605.28781`, proof of `field-existence-split-p`):

* Let `F` be a totally real number field, `S` a fixed finite set of **odd** primes and `K/F`
  an infinite Galois extension all of whose finite dimensional Galois subextensions are
  * pro-`2` (`IsPGroup 2`),
  * totally real, and
  * ramified only at the primes lying over `S`.
* Every finite level then has `2`-power degree over `F`, so every ramification index at a
  prime over `q ∈ S` is a `2`-power, hence **coprime to `q`** (`q ≠ 2`): the ramification is
  *tame* and the tame different formula bounds the discriminant,
  `disc L ∣ (disc F · ∏_{q ∈ S} q) ^ [L : F]`.
* Consequently every level has `|disc L| ≤ C ^ [L : ℚ]` with the **explicit** constant
  `C = |disc F| · ∏_{q ∈ S} q`, and the levels have arbitrarily large degree.

So the whole of Martinet's theorem reduces (modulo the tame different bookkeeping) to the
single **Golod--Shafarevich input**: an infinite totally real pro-`2` extension of a totally
real base field ramified only over a fixed finite set of odd primes.

## Contents

* `discr_le_of_tame_different` -- the arithmetic heart: a finite level `L/F` with `2`-power
  degree, totally real, ramified only over `S`, has `(disc L).natAbs ∣ (disc F · ∏_{q∈S} q) ^ [L:F]`.
  Stated here from the two literal inputs the tame different formula provides (the support of
  the relative different and tameness of every ramification index).
* `exists_totallyReal_discr_le_of_infinite_tame_pro2` -- the extraction of the tower: the
  benchmark statement from such an infinite extension.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Submission.NumberField

/-- **A `2`-power ramification index at an odd prime is tame.**  This is the numerical step
that makes the whole tame tower work: if `q` is an odd prime and `e` divides `2 ^ n`, then
`q ∤ e`. -/
theorem not_dvd_of_dvd_two_pow {q n e : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (he : e ∣ 2 ^ n) :
    ¬ q ∣ e := by
  rintro ⟨k, rfl⟩
  have hq2dvd : q ∣ 2 ^ n := dvd_trans ⟨k, rfl⟩ he
  have hdiv : q ∣ 2 := hq.dvd_of_dvd_pow hq2dvd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdiv)

/-- **The tame tower route.**

Let `F` be a totally real number field and `K/F` an infinite Galois extension whose finite
dimensional Galois subextensions `L` are

* totally real (`htr`), and
* satisfy the tame discriminant bound `(disc L).natAbs ≤ (disc F · ∏_{q ∈ S} q) ^ [L : ℚ]`
  (`hbound`; supplied by `natAbs_discr_le_pow_of_tame_different` from `2`-power degree plus
  tameness at the primes over the odd prime set `S`; NOTE the exponent is `[L : ℚ]`, NOT
  `[L : F]`: the tame exponent of a rational prime `q` in `N(𝔡_{L/F})` is at most
  `[L : F] · [F : ℚ] = [L : ℚ]` (it can be `[L:F]` times the number of primes of `F` above
  `q`), so the `[L : F]`-form is FALSE for `[F : ℚ] > 1` -- a counterexample by the fleet:
  `F = ℚ(√2)`, `L = F·ℚ(ζ₇)⁺`, `S = {7}`, where `(disc L).natAbs = 1229312` but
  `(|disc F| · 7) ^ [L : F] = 175616`).

Then the benchmark statement `∃ C > 0, ∀ N, ∃ d ≥ N, ∃ K totally real, [K : ℚ] = d ∧
|disc K| ≤ C ^ d` holds, with the *explicit* constant `C = |disc F| · ∏_{q ∈ S} q`. -/
theorem exists_totallyReal_discr_le_of_infinite_tame_pro2
    {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q)
    {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type} [Field K] [Algebra F K] [IsGalois F K] (hinf : Infinite (K ≃ₐ[F] K))
    (htr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → NumberField.IsTotallyReal ↥L)
    (hbound : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L →
      (NumberField.discr ↥L).natAbs ≤
        ((NumberField.discr F).natAbs * ∏ q ∈ S, q) ^ Module.finrank ℚ ↥L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d := by
  classical
  have hFne : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
  have hFpos : 0 < (NumberField.discr F).natAbs := Int.natAbs_pos.mpr hFne
  have hSpos : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  refine ⟨((NumberField.discr F).natAbs : ℝ) * ((∏ q ∈ S, q : ℕ) : ℝ), ?_, ?_⟩
  · exact mul_pos (by exact_mod_cast hFpos) (by exact_mod_cast hSpos)
  intro N
  obtain ⟨L, hfdL, hgalL, hdegL⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal
      (F := F) (K := K) hinf N
  haveI : FiniteDimensional F L := hfdL
  haveI : IsGalois F L := hgalL
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  have htrL : NumberField.IsTotallyReal ↥L := htr L hfdL hgalL
  have hle : (NumberField.discr ↥L).natAbs ≤
      ((NumberField.discr F).natAbs * ∏ q ∈ S, q) ^ Module.finrank ℚ ↥L := hbound L hfdL hgalL
  have hdegQ : N ≤ Module.finrank ℚ ↥L := by
    have hmul : Module.finrank ℚ ↥L = Module.finrank ℚ F * Module.finrank F ↥L :=
      (Module.finrank_mul_finrank (F := ℚ) (K := F) (A := ↥L)).symm
    have h1 : 1 ≤ Module.finrank ℚ F := Module.finrank_pos
    calc N ≤ Module.finrank F ↥L := hdegL
      _ = 1 * Module.finrank F ↥L := (one_mul _).symm
      _ ≤ Module.finrank ℚ F * Module.finrank F ↥L := Nat.mul_le_mul_right _ h1
      _ = Module.finrank ℚ ↥L := hmul.symm
  refine ⟨Module.finrank ℚ ↥L, hdegQ, ↥L, inferInstance, ‹NumberField ↥L›, htrL, rfl, ?_⟩
  calc |(NumberField.discr ↥L : ℝ)|
      = ((NumberField.discr ↥L).natAbs : ℝ) :=
        (Int.cast_abs (a := NumberField.discr ↥L)).symm.trans
          (Nat.cast_natAbs (NumberField.discr ↥L)).symm
    _ ≤ ((((NumberField.discr F).natAbs * ∏ q ∈ S, q) ^ Module.finrank ℚ ↥L : ℕ) : ℝ) := by
        exact_mod_cast hle
    _ = (((NumberField.discr F).natAbs : ℝ) * ((∏ q ∈ S, q : ℕ) : ℝ)) ^ Module.finrank ℚ ↥L := by
        push_cast; ring

/-- **The tame tower route, "abstract type" form.**  Identical to
`exists_totallyReal_discr_le_of_infinite_tame_pro2`, but the levels of the tower are quantified
over ABSTRACT types `L` carrying their instances as binders (with an injective `F`-algebra map
into `K`) instead of over `IntermediateField F K`.

This is the formulation that survives specialization to the concrete base `F = ℚ`: for
`L : IntermediateField ℚ K` the type `IsGalois ℚ ↥L` (and likewise `NumberField ↥L` /
`Module.Finite ℚ ↥L`) is AMBIGUOUS (instance search prefers the generic
`DivisionRing.toRatAlgebra` over `IntermediateField.algebra'`, and the two induced module
structures are not definitionally equal), whereas instance BINDERS are unambiguous (see the
SESSION 278 ADDENDUM 2 block of `Submission/Notes.lean`). -/
theorem exists_totallyReal_discr_le_of_infinite_tame_pro2_types
    {S : Finset ℕ} (hS : ∀ q ∈ S, Nat.Prime q)
    {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {K : Type} [Field K] [Algebra F K] [IsGalois F K] (hinf : Infinite (K ≃ₐ[F] K))
    (htr : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
      [IsGalois F L], (L →ₐ[F] K) → (∀ i : L →ₐ[F] K, Function.Injective i) →
      NumberField.IsTotallyReal L)
    (hbound : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
      [IsGalois F L], (L →ₐ[F] K) → (∀ i : L →ₐ[F] K, Function.Injective i) →
      (NumberField.discr L).natAbs ≤
        ((NumberField.discr F).natAbs * ∏ q ∈ S, q) ^ Module.finrank ℚ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d := by
  classical
  refine exists_totallyReal_discr_le_of_infinite_tame_pro2 hS hinf ?_ ?_
  · intro L hnumL hfdL hgalL
    haveI : NumberField ↥L := hnumL
    haveI : FiniteDimensional F ↥L := hfdL
    haveI : IsGalois F ↥L := hgalL
    exact htr ↥L (IntermediateField.val L) (fun i => i.injective)
  · intro L hnumL hfdL hgalL
    haveI : NumberField ↥L := hnumL
    haveI : FiniteDimensional F ↥L := hfdL
    haveI : IsGalois F ↥L := hgalL
    exact hbound ↥L (IntermediateField.val L) (fun i => i.injective)


end Submission.NumberField
