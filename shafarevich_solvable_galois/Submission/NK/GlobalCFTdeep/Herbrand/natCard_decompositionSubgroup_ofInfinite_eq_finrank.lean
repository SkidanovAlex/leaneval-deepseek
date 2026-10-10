import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

open scoped NumberField.LiesOver

/-- **The order of the decomposition group at an archimedean place is the local degree.**

For a finite Galois extension `L / K` of number fields, an infinite place `w` of `L` lying over
an infinite place `v` of `K`, the decomposition subgroup of `w` in `Gal(L/K)` (the stabiliser of
`w` in the action of `Gal(L/K)` on the places of `L`) has order equal to the degree
`[L_w : K_v]` of the corresponding local extension:

  `#D_w = [L_w : K_v]`.

Both sides are `1` unless `w` is a complex place lying over a real place `v` (the ramified
archimedean case), in which case both are `2`.  The point of the statement is that the *global*
stabiliser of the place and the *local* degree agree; the local Galois group is computed in
`NK.GlobalCFT.Inclusion.natCard_infStab_of_isUnramified`,
`NK.GlobalCFT.Inclusion.natCard_infStab_of_not_isUnramified` and
`NK.GlobalCFT.Inclusion.finrank_completionMap`. -/
theorem natCard_decompositionSubgroup_ofInfinite_eq_finrank {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [hw : w.LiesOver v] :
    Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w))
      = Module.finrank v.Completion w.Completion := by
  classical
  -- The decomposition subgroup of `Place.ofInfinite w` is, by definition, the subtype of
  -- `Gal(L/K)` fixing the archimedean place `w`; `Nat.card` of a subgroup is `Nat.card` of that
  -- subtype (`rfl`), so it suffices to compute the latter.
  have hcard : Nat.card {δ : L ≃ₐ[K] L //
      δ • NK.GlobalCFT.Place.ofInfinite w = NK.GlobalCFT.Place.ofInfinite w}
      = Module.finrank v.Completion w.Completion := by
    by_cases hu : NumberField.InfinitePlace.IsUnramified K w
    · -- Unramified: the stabiliser is trivial and the local extension is trivial.
      rw [NK.GlobalCFT.Inclusion.natCard_infStab_of_isUnramified (K := K) (L := L) hu]
      have hsurj := NK.GlobalCFT.Inclusion.surjective_completionMap_of_isUnramified
        (K := K) (L := L) (v := v) (w := w) hu
      have hinj : Function.Injective (algebraMap v.Completion w.Completion) :=
        (algebraMap v.Completion w.Completion).injective
      exact (Module.finrank_of_bijective_algebraMap ⟨hinj, hsurj⟩).symm
    · -- Ramified: the stabiliser has order `2` and the local degree is `2`.
      rw [NK.GlobalCFT.Inclusion.natCard_infStab_of_not_isUnramified (K := K) (L := L) hu,
        NK.GlobalCFT.Inclusion.finrank_completionMap (K := K) (L := L)
          (NK.GlobalCFT.Inclusion.isReal_of_not_isUnramified (K := K) (L := L)
            (v := v) (w := w) hu)
          (NK.GlobalCFT.Inclusion.isComplex_of_not_isUnramified (K := K) (L := L)
            (v := v) (w := w) hu)]
  exact hcard

end NK.GlobalCFTdeep.Herbrand
