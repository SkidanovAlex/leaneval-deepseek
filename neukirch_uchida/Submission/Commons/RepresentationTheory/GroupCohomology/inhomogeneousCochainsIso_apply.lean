import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Limits

/-- For a `k`-linear representation `σ` of a monoid `G`, the intertwining map `σ.freeLift f`
evaluated at the basis element `single i (single 1 1)` is `f i`. -/
lemma freeLift_apply_single_one {G : Type} [Monoid G] {k : Type} [CommSemiring k]
    {V : Type} [AddCommMonoid V] [Module k V] (σ : Representation k G V) (α : Type)
    (f : α → V) (i : α) :
    σ.freeLift f (Finsupp.single i (MonoidAlgebra.single (1 : G) (1 : k))) = f i := by
  rw [← Representation.freeLiftLEquiv_apply σ α (σ.freeLift f) i,
    ← Representation.freeLiftLEquiv_symm_apply σ α f,
    LinearEquiv.apply_symm_apply]

/-- The inverse of `Rep.freeLiftLEquiv` is `Rep.freeLift`. -/
lemma freeLiftLEquiv_symm_eq_freeLift {k : Type} [CommRing k] {G : Type} [Monoid G]
    {A : Rep k G} (α : Type) (f : α → A.V) :
    (Rep.freeLiftLEquiv k G α A).symm f = Rep.freeLift k G A f := rfl

theorem inhomogeneousCochainsIso_apply {G : Type} [Group G] (A : Rep ℤ G) (i : ℕ)
    (z : (Fin i → G) → A.V) (x : Fin i → G) :
    (((groupCohomology.inhomogeneousCochainsIso A).hom.f i).hom z).hom
      (Finsupp.single x (MonoidAlgebra.single (1:G) (1:ℤ))) = z x := by
  change (((Rep.freeLiftLEquiv ℤ G (Fin i → G) A).symm z).hom
      (Finsupp.single x (MonoidAlgebra.single (1:G) (1:ℤ))) = z x)
  rw [freeLiftLEquiv_symm_eq_freeLift]
  simp only [Rep.freeLift, Rep.hom_ofHom, freeLift_apply_single_one]

end Commons.RepresentationTheory.GroupCohomology