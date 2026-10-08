import Mathlib

namespace Work.L2F.Torus

/-- For a surjective homomorphism `f : G →* H` whose kernel lies in a subgroup `M ≤ G`, the
normalizer of the image of `M` is the image of the normalizer of `M`. -/
theorem normalizer_map_eq_of_le_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (M : Subgroup G) (h : MonoidHom.ker f ≤ M) :
    Subgroup.normalizer (M.map f : Set H) = (Subgroup.normalizer (M : Set G)).map f := by
  -- Pass to the preimage: the preimage of the normalizer of `f(M)` is the normalizer of `M`.
  have hcomap : Subgroup.comap f (Subgroup.normalizer (M.map f : Set H))
      = Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective (M.map f) hf, Subgroup.comap_map_eq_self h]
  -- Since `f` is surjective, `normalizer (f(M))` is the image of its own preimage.
  rw [← Subgroup.map_comap_eq_self_of_surjective hf (Subgroup.normalizer (M.map f : Set H)),
    hcomap]

end Work.L2F.Torus
