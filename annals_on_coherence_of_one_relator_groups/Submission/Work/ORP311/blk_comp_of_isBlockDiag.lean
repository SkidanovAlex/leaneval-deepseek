import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.starProjection_comp_of_mapsTo

namespace Work.ORP311

theorem blk_comp_of_isBlockDiag {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (n : ℕ) (j : ℤ) (S : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) (hS : Work.ORP311.IsBlockDiag N t n S) (hS' : Work.ORP311.IsBlockDiag N t n (ContinuousLinearMap.adjoint S)) : Work.ORP311.P311.blk n N t j ∘L S = S ∘L Work.ORP311.P311.blk n N t j :=
  -- `blk n N t j` is the orthogonal projection onto `K = ell2Sub n (coset N t j)`, and both `S`
  -- and `S*` preserve `K`; hence `S` commutes with the projection onto `K`.
  starProjection_comp_of_mapsTo (ell2Sub (G := G) n (coset N t j))
    (ell2Sub (G := G) n (coset N t j)) S (hS j) (hS' j)

end Work.ORP311
