import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.NumberField.MaximalProPOutsideS

/-!
# The maximal unramified pro-`p` extension `F_∅` exists

This file proves `Work.ClassFieldTower.exists_maximalUnramifiedProP`: for every number field `F`
and every prime `p` there is a field `F_∅` with the three defining properties of the maximal
unramified pro-`p` extension of `F` (see `Work.ClassFieldTower.MaximalUnramifiedProP`):

* **universality** -- every finite Galois extension `M/F` with pro-`p` Galois group and trivial
  relative different `𝓓(M/F) = (1)` embeds into `F_∅` as an `F`-algebra;
* **pro-`p`** -- every finite dimensional Galois subextension `L/F` of `F_∅` has pro-`p` Galois
  group;
* **unramified** -- every finite dimensional Galois subextension `L/F` of `F_∅` has trivial
  relative different, `𝓓(L/F) = (1)`.

No class field theory is used.  The extension is the compositum, inside the algebraic closure of
`F`, of *all* finite Galois pro-`p` subextensions with trivial relative different; this is the
`S = ∅` case of

* `Submission.NumberField.exists_maximal_proP_field_unramifiedOutside` (the sup-construction: the
  universal property holds because every admissible `M` embeds into the algebraic closure and
  *is* one of the summands; pro-`p`-ness is
  `Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup`), together with the
  observation that "the relative different is supported on `∅`" is exactly "the relative
  different is the unit ideal":

* `differentIdeal_eq_top_of_forall_prime_ne_bot_not_dvd` below (a maximal ideal containing the
  different would be a nonzero prime divisor of it).

The `S = ∅` specialisation is what distinguishes the *unramified* pro-`p` extension from the
tame/`S`-ramified one.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **From "no nonzero prime divides the different" to "the different is the unit ideal".**

If `Q ∤ 𝓓(K/E)` for every prime ideal `Q ≠ ⊥` of `𝓞 K`, then `𝓓(K/E) = ⊤`.  (The hypothesis is
only needed for *nonzero* primes: `⊥` is prime in the domain `𝓞 K`, and `⊥ ∣ I` merely says
`I = ⊥`.)

Proof: if `𝓓(K/E) ≠ ⊤`, some maximal ideal `M` contains it; `M` is prime, and `𝓞 K` is not a
field (it is a number ring), so `M ≠ ⊥`; divisibility `M ∣ 𝓓(K/E)` contradicts the hypothesis
at `M`. -/
private theorem differentIdeal_eq_top_of_forall_prime_ne_bot_not_dvd
    {E K : Type*} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (h : ∀ Q : Ideal (𝓞 K), Q.IsPrime → Q ≠ ⊥ → ¬ Q ∣ differentIdeal (𝓞 E) (𝓞 K)) :
    differentIdeal (𝓞 E) (𝓞 K) = ⊤ := by
  by_contra hne
  obtain ⟨M, hMmax, hDleM⟩ := Ideal.exists_le_maximal (differentIdeal (𝓞 E) (𝓞 K)) hne
  refine h M hMmax.isPrime ?_ (Ideal.dvd_iff_le.mpr hDleM)
  exact Ring.ne_bot_of_isMaximal_of_not_isField hMmax (NumberField.RingOfIntegers.not_isField K)

/-- **The maximal unramified pro-`p` extension of a number field exists.**

See the module docstring: it is the compositum, in `AlgebraicClosure F`, of all finite Galois
pro-`p` subextensions whose relative different is trivial, i.e. the `S = ∅` case of
`Submission.NumberField.exists_maximal_proP_field_unramifiedOutside`. -/
theorem exists_maximalUnramifiedProP (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] : Nonempty (MaximalUnramifiedProP.{0} F p) := by
  classical
  obtain ⟨K, hFldK, hAlgK, hGalK, huniv, hsub⟩ :=
    Submission.NumberField.exists_maximal_proP_field_unramifiedOutside F p (∅ : Finset ℕ)
  letI : Field K := hFldK
  letI : Algebra F K := hAlgK
  letI : IsGalois F K := hGalK
  refine ⟨{ K := K, universal := ?_, proP := ?_, unramified := ?_ }⟩
  · -- universality: `𝓓(M/F) = ⊤` is the `S = ∅` support condition
    intro M _ _ _ _ hpg hdiff
    refine huniv M hpg ?_
    intro P hP hPne hPdvd
    rw [hdiff] at hPdvd
    exact absurd (le_antisymm le_top (Ideal.dvd_iff_le.mp hPdvd)) hP.ne_top
  · -- pro-`p`: read off from the sup-construction
    intro L hfdL hgalL
    haveI : FiniteDimensional F ↥L := hfdL
    haveI : IsGalois F ↥L := hgalL
    haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
    exact (hsub L hfdL hgalL).1
  · -- unramified: the `S = ∅` support condition says no nonzero prime divides the different
    intro L hnumL hfdL hgalL
    haveI : NumberField ↥L := hnumL
    haveI : FiniteDimensional F ↥L := hfdL
    haveI : IsGalois F ↥L := hgalL
    refine differentIdeal_eq_top_of_forall_prime_ne_bot_not_dvd (E := F) (K := ↥L) ?_
    intro P hP hPne hPdvd
    obtain ⟨q, hq, -⟩ := (hsub L hfdL hgalL).2 P hP hPne hPdvd
    exact absurd hq (Finset.notMem_empty q)

end Work.ClassFieldTower
