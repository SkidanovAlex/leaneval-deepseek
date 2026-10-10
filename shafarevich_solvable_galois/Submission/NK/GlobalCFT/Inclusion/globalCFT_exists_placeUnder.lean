import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain

namespace NK.GlobalCFT.Inclusion

/-- Every place `w` of a finite extension `L / K` of number fields lies over some place `v` of `K`:
at an archimedean place `v` is the restriction of the corresponding embedding, and at a
nonarchimedean place `v` is the prime of `𝓞 K` contracted from the prime of `𝓞 L`. -/
theorem globalCFT_exists_placeUnder {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (w : Place L) :
    ∃ v : Place K, Place.LiesOver w v := by
  classical
  rcases w with w | q
  · -- archimedean case: restrict the embedding defining `w` to `K`
    refine ⟨Place.ofInfinite
      (NumberField.InfinitePlace.mk (w.embedding.comp (algebraMap K L))), ?_⟩
    refine Place.liesOver_ofInfinite ?_
    refine ⟨?eq⟩
    apply AbsoluteValue.ext
    intro x
    change (w.val.comp (algebraMap K L).injective) x =
      NumberField.place (w.embedding.comp (algebraMap K L)) x
    rw [NumberField.place_apply]
    change w.val (algebraMap K L x) = ‖w.embedding (algebraMap K L x)‖
    exact (NumberField.InfinitePlace.norm_embedding_eq w (algebraMap K L x)).symm
  · -- nonarchimedean case: contract the prime of `𝓞 L` to a prime of `𝓞 K`
    refine ⟨Place.ofFinite ⟨q.asIdeal.under (𝓞 K), inferInstance, ?_⟩, ?_⟩
    · exact Ideal.under_ne_bot (𝓞 K) q.ne_bot
    · refine Place.liesOver_ofFinite ?_
      exact Ideal.over_under (A := 𝓞 K) q.asIdeal

end NK.GlobalCFT.Inclusion
