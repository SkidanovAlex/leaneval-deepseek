import Mathlib

namespace Work.TopologyGroup

/-- A continuous surjective homomorphism from a compact topological group onto a Hausdorff topological group is an open map.  Route: `q` factors as `G → G ⧸ ker q → Q`; the first map is open (`QuotientGroup.isOpenMap_coe`), and the second is a continuous bijection from a compact space onto a Hausdorff space, hence a homeomorphism, hence open. -/
theorem isOpenMap_of_compact_surjective {G Q : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [T2Space Q] (q : G →* Q) (hq : Continuous q)
    (hsurj : Function.Surjective q) : IsOpenMap q := by
  -- Factor `q` as the quotient map onto `G ⧸ ker q` followed by the induced bijection.
  let e : G ⧸ q.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective q hsurj
  -- The induced bijection is continuous: `mk` is a quotient map and `e ∘ mk = q`.
  have he : Continuous (e : G ⧸ q.ker → Q) :=
    (QuotientGroup.isQuotientMap_mk q.ker).continuous_iff.mpr (by
      convert hq using 1
      ext g
      rfl)
  -- Hence, being a continuous bijection between a compact and a Hausdorff space, it is a
  -- homeomorphism, and in particular an open map.
  have hopen : IsOpenMap (e : G ⧸ q.ker → Q) :=
    (Continuous.homeoOfEquivCompactToT2 he).isOpenMap
  -- The quotient map `G → G ⧸ ker q` is open, so the composite `q` is open.
  have hcoe : IsOpenMap (QuotientGroup.mk : G → G ⧸ q.ker) := QuotientGroup.isOpenMap_coe
  have hcomp : IsOpenMap ((e : G ⧸ q.ker → Q) ∘ (QuotientGroup.mk : G → G ⧸ q.ker)) :=
    hopen.comp hcoe
  convert hcomp using 1
  ext g
  rfl

end Work.TopologyGroup
