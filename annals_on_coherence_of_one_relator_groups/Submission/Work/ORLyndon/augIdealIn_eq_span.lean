import Mathlib
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.augIdeal_eq_span

/-!
# `I^G_{K[H]}` is spanned by `{h - 1 : h ∈ H}`

`I^G_{K[H]}` is defined as the ideal of `K[G]` spanned by the image of the augmentation ideal
`I_{K[H]}` of `K[H]` under the ring map `K[H] → K[G]` induced by `H ≤ G`.  Since `I_{K[H]}` is
spanned by the elements `of K H h - 1` (`h : H`), and that ring map sends `of K H h - 1` to
`of K G h - 1`, the ideal `I^G_{K[H]}` is spanned by the elements `of K G h - 1`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

theorem augIdealIn_eq_span {K : Type*} [CommRing K] {G : Type*} [Group G] (H : Subgroup G) :
    Work.ORLyndon.augIdealIn K H =
      Ideal.span (Set.range (fun h : H => (MonoidAlgebra.of K G) (h : G) - 1)) := by
  -- the ring map `K[H] → K[G]` sends `of K H h` to `of K G h`
  have hf_of : ∀ h : H,
      MonoidAlgebra.mapDomainRingHom K H.subtype ((MonoidAlgebra.of K H) h)
        = (MonoidAlgebra.of K G) (h : G) := by
    intro h
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    exact congrArg (fun g : G => MonoidAlgebra.single g (1 : K)) (Subgroup.subtype_apply h)
  -- hence it sends the generator `h - 1` to `of K G h - 1`
  have hf_sub : ∀ h : H,
      MonoidAlgebra.mapDomainRingHom K H.subtype ((MonoidAlgebra.of K H) h - 1)
        = (MonoidAlgebra.of K G) (h : G) - 1 := by
    intro h
    rw [map_sub, map_one, hf_of h]
  -- so the image of the generating set is the generating set of the right hand side
  have hset : MonoidAlgebra.mapDomainRingHom K H.subtype ''
        (Set.range (fun h : H => (MonoidAlgebra.of K H) h - 1))
      = Set.range (fun h : H => (MonoidAlgebra.of K G) (h : G) - 1) := by
    ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨y, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, (hf_sub h).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨_, ⟨h, rfl⟩, hf_sub h⟩
  rw [augIdealIn, ← Ideal.map_span, Ideal.span_eq, augIdeal_eq_span, Ideal.map_span, hset]

end Work.ORLyndon
