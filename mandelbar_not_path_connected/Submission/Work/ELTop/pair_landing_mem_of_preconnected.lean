import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- **Separation lemma (R-b).**  A preconnected set `S` contained in the filled Julia set `K c`
which meets the far side of a co-landing pair `P` and also contains a point outside the closure
of that side must contain the landing point `P.y` of the pair.

Indeed, if `P.y ∉ S` then `S` misses the pair curve `pairCurve P` — the only point of the pair
curve inside `K c` is the landing point, the rays being disjoint from `K c`.  A preconnected set
inside the complement of the pair curve lies in a single connected component of that complement;
since `S` meets the side `pairSide P`, it lies in that side, contradicting that the given point
`x'` lies outside its closure. -/
theorem pair_landing_mem_of_preconnected {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (S : Set ℂ) (hS : S ⊆ Work.EL.K c) (hconn : IsPreconnected S)
    {x x' : ℂ} (hx : x ∈ S ∩ Work.EL.pairSide P) (hx' : x' ∈ S)
    (hx'2 : x' ∉ closure (Work.EL.pairSide P)) : P.y ∈ S := by
  by_contra hy
  have hxS : x ∈ S := hx.1
  have hxside : x ∈ Work.EL.pairSide P := hx.2
  -- `S` misses the pair curve: it is contained in `K c`, and the pair curve meets `K c` only at `P.y`.
  have hSsub : S ⊆ (Work.EL.pairCurve P)ᶜ := by
    intro z hzS
    simp only [Set.mem_compl_iff]
    intro hzc
    have hzK : z ∈ Work.EL.K c := hS hzS
    rcases (Work.EL.mem_pairCurve_iff P z).mp hzc with h | h | h
    · exact (Work.EL.paramRay_subset_compl hN P.a) h hzK
    · exact hy (h ▸ hzS)
    · exact (Work.EL.paramRay_subset_compl hN P.b) h hzK
  -- a preconnected subset of the complement lies in a single component
  have hcomp : S ⊆ connectedComponentIn ((Work.EL.pairCurve P)ᶜ) x :=
    hconn.subset_connectedComponentIn hxS hSsub
  -- the component containing `x` is the far side
  have heq : Work.EL.pairSide P = connectedComponentIn ((Work.EL.pairCurve P)ᶜ) x :=
    connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) hxside
  have hx'side : x' ∈ Work.EL.pairSide P := heq ▸ hcomp hx'
  exact hx'2 (subset_closure hx'side)

end Work.ELTop
