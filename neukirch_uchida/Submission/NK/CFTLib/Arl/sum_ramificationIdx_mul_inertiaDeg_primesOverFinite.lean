import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.Commons.NumberTheory.NumberField.finite_primesOver

/-!
# The fundamental identity `∑ e(𝔮|𝔭) f(𝔮|𝔭) = [L : K]` over `primesOverFinite`

For a finite extension `L / K` of number fields and a non-zero prime `𝔭` of `𝓞 K`, the sum of
`e(𝔮|𝔭) · f(𝔮|𝔭)` over the primes `𝔮` of `𝓞 L` above `𝔭` equals the degree `[L : K]`.

This is `Ideal.sum_ramification_inertia_eq_finrank` for the extension `𝓞 L / 𝓞 K`, transported
from `Module.finrank (𝓞 K) (𝓞 L)` to `Module.finrank K L` by `IsFractionRing.finrank_eq`, and
reindexed from the subtype `𝔭.asIdeal.primesOver (𝓞 L)` onto the `Finset`
`NK.GlobalCFT.Place.primesOverFinite 𝔭`.
-/

set_option linter.style.haveILetI false

namespace NK.CFTLib.Arl

open scoped NumberField
open IsDedekindDomain

theorem sum_ramificationIdx_mul_inertiaDeg_primesOverFinite {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    ∑ 𝔮 ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭,
      𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)
        * 𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = Module.finrank K L := by
  classical
  letI : Fintype ↥(𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)) :=
    (Commons.NumberTheory.NumberField.finite_primesOver 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot).fintype
  -- The canonical bijection between the subtype of primes of `𝓞 L` over `𝔭` and the finset
  -- `primesOverFinite 𝔭`.
  let g : ↥(𝔭.asIdeal.primesOver (𝓞 L)) → HeightOneSpectrum (𝓞 L) :=
    fun q => ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot q.2⟩
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : (g a).asIdeal = (g b).asIdeal := congrArg HeightOneSpectrum.asIdeal hab
    exact Subtype.ext h1
  have hset : NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) 𝔭
      = Finset.univ.image g := by
    ext q
    rw [NK.GlobalCFT.Place.mem_primesOverFinite, Finset.mem_image]
    constructor
    · intro hq
      exact ⟨⟨q.asIdeal, q.isPrime, hq⟩, Finset.mem_univ _, HeightOneSpectrum.ext rfl⟩
    · rintro ⟨q', -, rfl⟩
      exact q'.2.2
  rw [hset, Finset.sum_image (Set.injOn_of_injective hinj)]
  -- Now the sum runs over the subtype; apply the Dedekind domain identity.
  have h := Ideal.sum_ramification_inertia_eq_finrank (R := NumberField.RingOfIntegers K)
    𝔭.asIdeal (NumberField.RingOfIntegers L)
  rw [← IsFractionRing.finrank_eq (NumberField.RingOfIntegers K) K
    (NumberField.RingOfIntegers L) L] at h
  exact h

end NK.CFTLib.Arl
