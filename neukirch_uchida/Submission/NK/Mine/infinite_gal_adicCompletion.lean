import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion

/-!
# The absolute Galois group of a `𝔭`-adic completion is infinite

Let `K` be a number field, `𝔭` a finite prime of `𝔭`, `F = 𝔭.adicCompletion K` the completion
and `L` a separable closure of `F`.  This file proves that `Gal(L/F)` is infinite.

Two ingredients:

* (linear algebra) if `L/F` is a separable closure whose Galois group is finite, then `L/F`
  is finite-dimensional: by Artin's theorem (`FixedPoints.rank_le_card`) the rank of `L` over
  the fixed field of `Gal(L/F)` is at most `Nat.card Gal(L/F)`, and the fixed field of the full
  Galois group is `F` itself (`InfiniteGalois.mem_bot_iff_fixed`).
* (arithmetic) `L/F` is *not* finite-dimensional: `F` is a discretely valued field with
  uniformizer `π`, and for every odd `n` the polynomial `X ^ n - π` has no root of the form
  `b ^ p` with `p` prime dividing `n` (a valuation argument: `v π = exp (-1)` is not a `p`-th
  power in the value group `ℤ`), so Kummer theory (`X_pow_sub_C_irreducible_of_odd`) makes it
  irreducible, and `L` contains a root `α` of it, giving an intermediate field `F⟮α⟯` of degree
  `n` over `F`.
-/

namespace NK.Mine

open scoped Classical WithZero NumberField
open IsDedekindDomain.HeightOneSpectrum

noncomputable section

/-! ## Part 1: a finite Galois group forces finite dimension -/

/-- Membership in the subfield of fixed points of a monoid action. -/
lemma mem_fixedPoints_subfield {M F : Type*} [Monoid M] [Field F] [MulSemiringAction M F]
    (x : F) : x ∈ FixedPoints.subfield M F ↔ ∀ m : M, m • x = x :=
  MulAction.mem_fixedPoints

/-- **A finite Galois group forces finite dimension.**  If `L` is a separable closure of `F`
and `Gal(L/F)` is finite, then `L` is a finite-dimensional `F`-vector space.

Indeed `F` is the fixed field of `Gal(L/F)` (`InfiniteGalois.mem_bot_iff_fixed`), and by
Artin's theorem the rank of `L` over the fixed field of a finite group of automorphisms is at
most the order of the group (`FixedPoints.rank_le_card`). -/
theorem finiteDimensional_of_finite_gal_isSepClosure {F L : Type*} [Field F] [Field L]
    [Algebra F L] [IsSepClosure F L] (h : Finite Gal(L/F)) : FiniteDimensional F L := by
  haveI : Fintype Gal(L/F) := Fintype.ofFinite _
  have hsub : (⊥ : IntermediateField F L).toSubfield = FixedPoints.subfield Gal(L/F) L := by
    ext x
    rw [show x ∈ FixedPoints.subfield Gal(L/F) L ↔ ∀ f : Gal(L/F), f x = x from
      mem_fixedPoints_subfield x]
    exact (InfiniteGalois.mem_bot_iff_fixed (k := F) x)
  have hle : Module.rank F L ≤ (Fintype.card Gal(L/F) : Cardinal) := by
    rw [← IntermediateField.rank_bot' (F := F) (E := L)]
    have hkey : Module.rank (↥(⊥ : IntermediateField F L)) L
        = Module.rank (↥(FixedPoints.subfield Gal(L/F) L)) L := by
      rw [show Module.rank (↥(⊥ : IntermediateField F L)) L =
          Module.rank (↥((⊥ : IntermediateField F L).toSubfield)) L from rfl, hsub]
    rw [hkey]
    exact FixedPoints.rank_le_card _ _
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  exact lt_of_le_of_lt hle Cardinal.natCast_lt_aleph0

/-! ## Part 2: the arithmetic — extensions of unbounded degree -/

/-- The uniformizer of the `𝔭`-adic completion of `K`, an element of the completed valuation
ring whose value is `exp (-1)`. -/
def adicUniformizer {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    𝔭.adicCompletionIntegers K :=
  Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K) (K := K) 𝔭

lemma adicUniformizer_val {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Valued.v ((adicUniformizer 𝔭 : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
      WithZero.exp (-1 : ℤ) :=
  Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) 𝔭

/-- **The uniformizer is not a `p`-th power** for any prime `p`: the valuation of `π` is
`exp (-1)` in a value group `ℤ`, while `v (b ^ p) = (v b) ^ p = exp (-(p * k))` can never equal
`exp (-1)`. -/
lemma uniformizer_ne_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) (hp : p.Prime) (b : 𝔭.adicCompletion K) :
    b ^ p ≠ ((adicUniformizer 𝔭 : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) := by
  intro h
  have hπ := adicUniformizer_val 𝔭
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have h1 : (0 : Zstar0) = WithZero.exp (-1 : ℤ) := by
      rw [← hπ, ← h, zero_pow hp.ne_zero, Valuation.map_zero]
    exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) h1.symm
  · have hvne : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
    have key : WithZero.exp (p • WithZero.log (Valued.v b)) = WithZero.exp (-1 : ℤ) := by
      rw [WithZero.exp_nsmul, WithZero.exp_log hvne, ← Valuation.map_pow, h]
      exact hπ
    have hkey : (p : ℤ) * WithZero.log (Valued.v b) = -1 := by
      simpa [nsmul_eq_mul] using WithZero.exp_injective key
    have hnat : p * (WithZero.log (Valued.v b)).natAbs = 1 := by
      have habs := congrArg Int.natAbs hkey
      simpa [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_one, Int.natAbs_natCast] using habs
    exact hp.not_dvd_one ⟨(WithZero.log (Valued.v b)).natAbs, hnat.symm⟩

/-- **`X ^ n - π` is irreducible for odd `n`**, by Kummer theory
(`X_pow_sub_C_irreducible_of_odd`), since `π` is not a `p`-th power for any prime `p`. -/
lemma irreducible_X_pow_sub_uniformizer {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {n : ℕ} (hn : Odd n) :
    Irreducible (Polynomial.X ^ n - Polynomial.C
      ((adicUniformizer 𝔭 : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) :=
  X_pow_sub_C_irreducible_of_odd hn fun p hp _ b => uniformizer_ne_pow 𝔭 p hp b

/-- **There are intermediate fields of every odd degree.**  For every odd `n` there is a
subfield `E` of the separable closure `L` of `F = 𝔭.adicCompletion K` with `[E : F] = n`: take
`E = F⟮α⟯` for a root `α ∈ L` of the irreducible polynomial `X ^ n - π`. -/
lemma exists_intermediateField_finrank_eq_odd {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : Type*) [Field L] [Algebra (𝔭.adicCompletion K) L]
    [IsSepClosure (𝔭.adicCompletion K) L]
    (n : ℕ) (hn : Odd n) :
    ∃ E : IntermediateField (𝔭.adicCompletion K) L,
      Module.finrank (𝔭.adicCompletion K) E = n := by
  haveI : IsSepClosed L := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  haveI : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  haveI : PerfectField (𝔭.adicCompletion K) := inferInstance
  set π : 𝔭.adicCompletion K :=
    ((adicUniformizer 𝔭 : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) with hπdef
  have hpos : 0 < n := hn.pos
  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C π) := by
    rw [hπdef]
    exact irreducible_X_pow_sub_uniformizer 𝔭 hn
  have hmonic : (Polynomial.X ^ n - Polynomial.C π).Monic :=
    Polynomial.monic_X_pow_sub_C π hpos.ne'
  have hsep : (Polynomial.X ^ n - Polynomial.C π).Separable :=
    PerfectField.separable_of_irreducible hirr
  have hdeg : (Polynomial.X ^ n - Polynomial.C π).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C hpos π]
    exact_mod_cast hpos.ne'
  obtain ⟨α, hα⟩ := IsSepClosed.exists_aeval_eq_zero L
    (Polynomial.X ^ n - Polynomial.C π) hdeg hsep
  have hint : IsIntegral (𝔭.adicCompletion K) α := ⟨_, hmonic, hα⟩
  have hmin : minpoly (𝔭.adicCompletion K) α = Polynomial.X ^ n - Polynomial.C π :=
    (minpoly.eq_of_irreducible_of_monic hirr hα hmonic).symm
  exact ⟨IntermediateField.adjoin (𝔭.adicCompletion K) {α},
    by rw [IntermediateField.adjoin.finrank hint, hmin, Polynomial.natDegree_X_pow_sub_C]⟩

/-- **The separable closure of a `𝔭`-adic completion is infinite-dimensional.** -/
lemma not_finiteDimensional_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : Type*) [Field L] [Algebra (𝔭.adicCompletion K) L]
    [IsSepClosure (𝔭.adicCompletion K) L] :
    ¬ FiniteDimensional (𝔭.adicCompletion K) L := by
  intro hfin
  haveI := hfin
  obtain ⟨E, hE⟩ := exists_intermediateField_finrank_eq_odd 𝔭 L
    (2 * Module.finrank (𝔭.adicCompletion K) L + 1) ⟨_, by ring⟩
  have hle : Module.finrank (𝔭.adicCompletion K) ↥E ≤
      Module.finrank (𝔭.adicCompletion K) ↥(⊤ : IntermediateField (𝔭.adicCompletion K) L) :=
    IntermediateField.finrank_le_of_le_right le_top
  rw [IntermediateField.finrank_top'] at hle
  omega

/-! ## The target -/

theorem infinite_gal_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : Type*) [Field L] [Algebra (𝔭.adicCompletion K) L]
    [IsSepClosure (𝔭.adicCompletion K) L] :
    Infinite (Gal(L/𝔭.adicCompletion K)) := by
  classical
  by_contra h
  have hfin : Finite (Gal(L/𝔭.adicCompletion K)) := by
    by_contra hc
    exact h ⟨hc⟩
  exact not_finiteDimensional_adicCompletion 𝔭 L
    (finiteDimensional_of_finite_gal_isSepClosure hfin)

end

end NK.Mine
