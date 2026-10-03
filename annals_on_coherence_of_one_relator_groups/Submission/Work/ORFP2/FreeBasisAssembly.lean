/-
# The augmentation ideal of a free group algebra is free

Assembled from the two halves: `augIdeal_freeGroup_injective` (the classical fact that there are
no `k[F]`-linear relations among the elements `x - 1`, `x` a free generator) and
`augIdeal_freeGroup_surjective` (they generate the augmentation ideal).
-/
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.augIdeal_freeGroup_injective
import Submission.Work.ORFP2.augIdeal_freeGroup_surjective

set_option autoImplicit false

namespace Work.ORFP2

open MonoidAlgebra

/-- **The augmentation ideal of a free group algebra is free on `{x - 1}`.** -/
theorem freeGroupAugIdealBasis_assembled (k : Type*) [CommRing k] : FreeGroupAugIdealBasis k := by
  intro α _
  let Φ : (α →₀ MonoidAlgebra k (FreeGroup α)) →ₗ[MonoidAlgebra k (FreeGroup α)]
      MonoidAlgebra k (FreeGroup α) :=
    Finsupp.linearCombination (MonoidAlgebra k (FreeGroup α))
      (fun a => MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)
  have hinj : Function.Injective Φ := augIdeal_freeGroup_injective k α
  have hrange : LinearMap.range Φ = augIdeal k (FreeGroup α) :=
    augIdeal_freeGroup_surjective k α
  refine ⟨LinearEquiv.ofBijective (Φ.codRestrict (augIdeal k (FreeGroup α)) fun x => ?_)
    ⟨?_, ?_⟩, ?_⟩
  · rw [← hrange]
    exact LinearMap.mem_range_self Φ x
  · intro x y hxy
    exact hinj (Subtype.ext_iff.mp hxy)
  · rintro ⟨y, hy⟩
    have hy' : y ∈ LinearMap.range Φ := by rw [hrange]; exact hy
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, Subtype.ext hx⟩
  · intro c
    show Φ c = c.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1))
    rw [Finsupp.linearCombination_apply]
    exact Finsupp.sum_congr fun a _ => smul_eq_mul _ _

end Work.ORFP2
