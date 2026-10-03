import Mathlib
import Submission.Work.ORDunwoody.FP2

namespace Work.ORAssembly.FP2

open scoped MonoidAlgebra

/-- The algebra equivalence `MonoidAlgebra.domCongr k k e` induced by a multiplicative
equivalence `e : G ≃* H` sends the generator `of k G g` of `k[G]` to `of k H (e g)`. -/
lemma domCongr_of {k : Type*} [CommRing k] {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    (MonoidAlgebra.domCongr k k e).toRingEquiv.toRingHom (MonoidAlgebra.of k G g)
      = MonoidAlgebra.of k H (e g) := by
  simp [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single]

/-- The image of the set of augmentation-ideal generators `of k G g - 1` under the ring
homomorphism induced by `e : G ≃* H` is the corresponding set of generators in `k[H]`. -/
lemma domCongr_image_augmentationGenerators {k : Type*} [CommRing k] {G H : Type*} [Group G]
    [Group H] (e : G ≃* H) :
    (MonoidAlgebra.domCongr k k e).toRingEquiv.toRingHom ''
        (Set.range fun g : G => MonoidAlgebra.of k G g - 1)
      = Set.range fun h : H => MonoidAlgebra.of k H h - 1 := by
  ext x
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, by rw [map_sub, map_one, domCongr_of]⟩
  · rintro ⟨h, rfl⟩
    refine ⟨MonoidAlgebra.of k G (e.symm h) - 1, ⟨e.symm h, rfl⟩, ?_⟩
    rw [map_sub, map_one, domCongr_of, MulEquiv.apply_symm_apply]

theorem map_augmentationIdeal_domCongr {k : Type*} [CommRing k] {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) :
    (Work.ORDunwoody.augmentationIdeal k G).map
      (MonoidAlgebra.domCongr k k e).toRingEquiv.toRingHom = Work.ORDunwoody.augmentationIdeal k H := by
  unfold Work.ORDunwoody.augmentationIdeal
  rw [Ideal.map_span, domCongr_image_augmentationGenerators]

end Work.ORAssembly.FP2
