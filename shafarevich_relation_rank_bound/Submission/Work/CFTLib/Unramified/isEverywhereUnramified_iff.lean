import Mathlib
import Submission.Work.CFTLib.ShafDeps

/-!
# `IsEverywhereUnramified` versus `CFTLib.IsUnramified`

The challenge's predicate `LeanEval.NumberTheory.IsEverywhereUnramified F K` (`ChallengeDeps.lean`)
says that

* every nonzero prime `𝔭` of `𝓞 F` has ramification index `1` in `𝓞 K` (i.e. every prime `𝔓` of
  `𝓞 K` lying over a nonzero prime `𝔭` of `𝓞 F` is unramified over `𝓞 F`), and
* every real place of `F` stays real in `K`.

The library predicate `CFTLib.IsUnramified F K` (`Submission/CFTLib/Interfaces.lean`) says that the
relative different `𝔡_{K/F}` is the unit ideal and that `K/F` is unramified at the infinite places.

For a finite extension of number fields the two predicates coincide:

* the relative different is trivial iff every prime of `𝓞 K` is unramified over `𝓞 F`
  (`Ideal.dvd_differentIdeal_iff` + `Ideal.ramificationIdx_eq_one_iff`, in both directions);
* an infinite place of `K` is unramified over `F` iff it is real or complex over a complex place
  (`NumberField.InfinitePlace.isUnramified_iff`), which for the condition "real places stay real"
  is exactly the statement that every place of `K` above a real place of `F` is real.

## Main results

* `Work.CFTLib.Unramified.differentIdeal_eq_top_iff_forall_mem_primesOver`
* `Work.CFTLib.Unramified.isUnramifiedAtInfinitePlaces_iff`
* `Work.CFTLib.Unramified.isEverywhereUnramified_iff`
-/

open NumberField

namespace Work.CFTLib.Unramified

/-- **The finite part.** For a finite extension of number fields, the relative different is trivial
if and only if every prime `𝔓` of `𝓞 K` lying over a nonzero prime `𝔭` of `𝓞 F` has ramification
index `1` over `𝓞 F`.

This is the form of unramifiedness used by `LeanEval.NumberTheory.IsEverywhereUnramified`.  Note
that it is *not* necessary to test primes `𝔓` of `𝓞 K` lying over the zero ideal: such a `𝔓` would
have to be `⊥` itself (`Ideal.IsIntegral.eq_bot_of_under_eq_bot`), and `⊥` never divides a nonzero
different ideal. -/
theorem differentIdeal_eq_top_iff_forall_mem_primesOver
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] :
    differentIdeal (𝓞 F) (𝓞 K) = ⊤ ↔
      ∀ (𝔭 : Ideal (𝓞 F)) (𝔓 : Ideal (𝓞 K)), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
        𝔓 ∈ 𝔭.primesOver (𝓞 K) → 𝔓.ramificationIdx (𝓞 F) = 1 := by
  letI : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) :=
    FractionRing.liftAlgebra (R := 𝓞 F) (FractionRing (𝓞 K))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := inferInstance
  constructor
  · intro h 𝔭 𝔓 _h𝔭 _h𝔭ne h𝔓
    have h𝔓prime : 𝔓.IsPrime := h𝔓.1
    haveI := h𝔓prime
    have hnd : ¬ 𝔓 ∣ differentIdeal (𝓞 F) (𝓞 K) := by
      rw [h, Ideal.dvd_iff_le, top_le_iff]
      exact h𝔓prime.ne_top
    exact (Ideal.ramificationIdx_eq_one_iff (R := 𝓞 F) (q := 𝔓)).mpr
      (not_dvd_differentIdeal_iff.mp hnd)
  · intro h
    rw [← not_ne_iff]
    intro hne
    obtain ⟨M, hMmax, hMle⟩ := Ideal.ne_top_iff_exists_maximal.mp hne
    have hMprime : M.IsPrime := hMmax.isPrime
    have hdvd : M ∣ differentIdeal (𝓞 F) (𝓞 K) := Ideal.dvd_iff_le.mpr hMle
    -- a prime dividing the different is nonzero (the different is nonzero) ...
    have hMne : M ≠ ⊥ := by
      intro hbot
      rw [hbot, ← Ideal.zero_eq_bot] at hdvd
      exact differentIdeal_ne_bot (zero_dvd_iff.mp hdvd)
    -- ... hence its contraction to `𝓞 F` is nonzero, by integrality
    have hunder : M.under (𝓞 F) ≠ ⊥ := Ideal.IsIntegral.under_ne_bot _ hMne
    haveI : (M.under (𝓞 F)).IsPrime := inferInstance
    have hram : M.ramificationIdx (𝓞 F) = 1 :=
      h _ M inferInstance hunder ⟨hMprime, Ideal.over_under M⟩
    exact (dvd_differentIdeal_iff.mp hdvd)
      ((Ideal.ramificationIdx_eq_one_iff (R := 𝓞 F) (q := M)).mp hram)

/-- **The infinite part.** For a finite extension of number fields, `K/F` is unramified at the
infinite places if and only if every infinite place of `K` above a real place of `F` is real. -/
theorem isUnramifiedAtInfinitePlaces_iff
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] :
    IsUnramifiedAtInfinitePlaces F K ↔
      ∀ w : InfinitePlace F, w.IsReal →
        ∀ w' : InfinitePlace K, w'.comap (algebraMap F K) = w → w'.IsReal := by
  constructor
  · intro h w hw w' hw'
    -- a place of `K` is unramified over `F` iff it is real, or complex over a complex place
    rcases InfinitePlace.isUnramified_iff.mp (h.isUnramified w') with hreal | hcplx
    · exact hreal
    · rw [hw'] at hcplx
      exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr hcplx)
  · intro h
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isUnramified_iff]
    by_cases hw : (w.comap (algebraMap F K)).IsReal
    · exact Or.inl (h _ hw w rfl)
    · exact Or.inr (InfinitePlace.not_isReal_iff_isComplex.mp hw)

/-- **The challenge's `IsEverywhereUnramified` is the library's `CFTLib.IsUnramified`.**

`LeanEval.NumberTheory.IsEverywhereUnramified F K` (the trusted definition of the problem
statement, `ChallengeDeps.lean`) says that every nonzero prime of `𝓞 F` has ramification index `1`
in `𝓞 K` and that every real place of `F` stays real in `K`.
`CFTLib.IsUnramified F K` (`Submission/CFTLib/Interfaces.lean`, the predicate used by the
class-field-theory hypotheses `RelShafBound` and `UnramifiedAbelianDegreeLe`) says
`differentIdeal (𝓞 F) (𝓞 K) = ⊤ ∧ IsUnramifiedAtInfinitePlaces F K`.

For a finite extension of number fields the two predicates coincide. -/
theorem isEverywhereUnramified_iff
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] :
    LeanEval.NumberTheory.IsEverywhereUnramified F K ↔ CFTLib.IsUnramified F K :=
  (differentIdeal_eq_top_iff_forall_mem_primesOver F K).symm.and
    (isUnramifiedAtInfinitePlaces_iff F K).symm

end Work.CFTLib.Unramified
