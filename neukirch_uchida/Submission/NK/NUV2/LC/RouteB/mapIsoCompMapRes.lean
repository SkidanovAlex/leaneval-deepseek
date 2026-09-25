import Mathlib

namespace NK.NUV2.LC.RouteB

open CategoryTheory

universe u

/-- **The `mapIso`/restriction square.**  Let `e : G ≃* H` be a group isomorphism, `e' : B.V ≃ₗ[k] A.V`
an equivariant isomorphism of coefficient modules over `A : Rep k H` and `B : Rep k G`, and let
`f : G₀ →* G`, `g : H₀ →* H`, `e₀ : G₀ ≃* H₀` be compatible (`g (e₀ x) = e (f x)`).  Then the
square formed by `groupCohomology.mapIso e e' he n`, the restriction maps `groupCohomology.map g 𝟙 n`
and `groupCohomology.map f 𝟙 n`, and `groupCohomology.mapIso e₀ e'' he'' n` commutes, provided the
coefficient isomorphisms `e'` and `e''` agree as functions. -/
theorem mapIsoCompMapRes {k : Type u} [CommRing k]
    {G H G₀ H₀ : Type u} [Group G] [Group H] [Group G₀] [Group H₀]
    {A : Rep.{u, u, u} k H} {B : Rep.{u, u, u} k G} (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V)
    (he : ∀ g : G, e' ∘ₗ B.ρ g = A.ρ (e g) ∘ₗ e')
    (f : G₀ →* G) (g : H₀ →* H) (e₀ : G₀ ≃* H₀)
    (he₀ : ∀ x : G₀, g (e₀ x) = e (f x))
    (e'' : (Rep.res f B).V ≃ₗ[k] (Rep.res g A).V)
    (he'' : ∀ x : G₀, e'' ∘ₗ (Rep.res f B).ρ x = (Rep.res g A).ρ (e₀ x) ∘ₗ e'')
    (heq : ∀ x : (Rep.res f B).V, e'' x = e' x) (n : ℕ) :
    (groupCohomology.mapIso e e' he n).hom ≫
        groupCohomology.map g (𝟙 (Rep.res g A)) n =
      groupCohomology.map f (𝟙 (Rep.res f B)) n ≫
        (groupCohomology.mapIso e₀ e'' he'' n).hom := by
  -- The two group homomorphisms `H₀ →* G` defining the two sides agree.
  have hfg : (e.symm : H →* G).comp g = f.comp e₀.symm := by
    ext x
    obtain ⟨y, rfl⟩ := e₀.surjective x
    simp [MonoidHom.comp_apply, he₀ y]
  -- Unfold the two `mapIso`s into `map` along the inverse isomorphisms.
  simp only [groupCohomology.mapIso_hom]
  -- Combine each pair of `map`s into a single `map` via `map_comp`.
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  simp only [Category.comp_id]
  -- Both sides are now `map` along the *same* group homomorphism.
  refine groupCohomology.map_congr hfg ?_ n
  ext x
  simp only [Rep.hom_comp, Rep.hom_ofHom]
  exact (heq x).symm

end NK.NUV2.LC.RouteB
