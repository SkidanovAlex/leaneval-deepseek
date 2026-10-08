import Mathlib
import Submission.Work.BMAX.D17Defs

namespace Work.BMAX

open Subgroup

/-- The `p`-residual of `K ⊓ H` computed inside `K ⊓ H` and pushed into the ambient group `G`
agrees with `O^p(K ⊓ H)` computed directly in `G`.

Both sides are the closure of the same set: the image of a `p'`-element of `K ⊓ H` is a
`p'`-element of `K ⊓ H`, and conversely every `p'`-element of `K ⊓ H` is the image of itself. -/
theorem map_pResidual_subgroupOf_eq {G : Type} [Group G] (p : ℕ) (K H : Subgroup G) :
    (Work.BMAX.pResidual p ↥(K.subgroupOf H)).map (H.subtype.comp (K.subgroupOf H).subtype)
      = Work.BMAX.pResidualIn p (K ⊓ H) := by
  have hset : (H.subtype.comp (K.subgroupOf H).subtype) '' {x : ↥(K.subgroupOf H) | ¬ p ∣ orderOf x}
      = {y : G | y ∈ K ⊓ H ∧ ¬ p ∣ orderOf y} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Subgroup.mem_subgroupOf.mp x.2
      · exact x.1.2
      · have hord : orderOf ((H.subtype.comp (K.subgroupOf H).subtype) x) = orderOf x := by
          rw [MonoidHom.comp_apply]
          exact (Subgroup.orderOf_coe ((K.subgroupOf H).subtype x)).trans (Subgroup.orderOf_coe x)
        rw [hord]; exact hx
    · rintro ⟨hy, hyord⟩
      rw [Subgroup.mem_inf] at hy
      let x : ↥(K.subgroupOf H) := ⟨⟨y, hy.2⟩, Subgroup.mem_subgroupOf.mpr hy.1⟩
      have hxH : (x : ↥H) = ⟨y, hy.2⟩ := rfl
      refine ⟨x, ?_, ?_⟩
      · change ¬ p ∣ orderOf x
        have h1 : orderOf x = orderOf (⟨y, hy.2⟩ : ↥H) := by
          rw [← Subgroup.orderOf_coe (H := K.subgroupOf H) x, hxH]
        have h2 : orderOf (⟨y, hy.2⟩ : ↥H) = orderOf y := by
          rw [← Subgroup.orderOf_coe (H := H) (⟨y, hy.2⟩ : ↥H)]
        rw [h1, h2]; exact hyord
      · rfl
  rw [Work.BMAX.pResidual, Work.BMAX.pResidualIn, MonoidHom.map_closure, hset]

end Work.BMAX
