import Mathlib
import Submission.Work.ANALYTIC.towerFEAsetup

namespace Work.ANALYTIC

/-- **Naturality of the inverse of `Work.ATOM.homFreeEquiv`.**

`Work.ATOM.homFreeEquiv S M : (ℤ[S] ⟶ M) ≃ M(S)` classifies a morphism out of the free light
condensed abelian group `ℤ[S]` by its underlying section over `S`.  This is `homFreeEquiv`'s
naturality (`Work.ATOM.homFreeEquiv_naturality`, which says that
`homFreeEquiv T M (zmap f ≫ g) = M.map f (homFreeEquiv S M g)`) read through the inverses: the
inverse of the classification intertwines `zmap f : ℤ[T] ⟶ ℤ[S]` with the restriction map
`M.obj.map f.op : M(S) ⟶ M(T)`.

Both sides are morphisms `ℤ[T] ⟶ M`, so it suffices to apply the (injective) classification
`homFreeEquiv T M` to them, where the claim is the naturality of `homFreeEquiv` followed by the
two cancellation identities `homFreeEquiv _ M ((homFreeEquiv _ M).symm -) = -`. -/
theorem zmapSymm : Work.ANALYTIC.ZmapSymm := by
  intro M T S f a
  apply (Work.ATOM.homFreeEquiv T M).injective
  rw [Work.ATOM.homFreeEquiv_naturality f, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Work.ANALYTIC
