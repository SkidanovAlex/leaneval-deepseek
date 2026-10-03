import Mathlib

namespace Work.ORFlatness

universe u

/-- Splitting a short exact sequence of right `R`-modules `0 → A → Q → P → 0` whose
right-hand term `P` is projective: the injection `f : A → Q` admits a linear retraction
`r : Q → A` with `r ∘ f = id`.

Proof: by projectivity of `P`, the surjection `p : Q ↠ P` has a linear section
`s : P → Q` (`Module.projective_lifting_property` applied to `p` and `id_P`); the map
`x ↦ x - s (p x)` lands in `p.ker = f.range`; since `f` is injective, this factors as
`f ∘ r` for the retraction `r = (LinearEquiv.ofInjective f hf).symm ∘ (x ↦ ⟨x - s (p x)⟩)`.
On `f a` the section term vanishes (as `p (f a) = 0`), so `r (f a) = a`. -/
theorem exists_retraction_of_projective_cokernel {R : Type u} [Ring R] {A Q P : Type u}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [AddCommGroup P] [Module Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (f : A →ₗ[Rᵐᵒᵖ] Q) (p : Q →ₗ[Rᵐᵒᵖ] P)
    (hf : Function.Injective f) (hp : Function.Surjective p) (hfp : f.range = p.ker) :
    ∃ r : Q →ₗ[Rᵐᵒᵖ] A, r.comp f = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) hp
  let e : A ≃ₗ[Rᵐᵒᵖ] f.range := LinearEquiv.ofInjective f hf
  have hs' : ∀ y, p (s y) = y := fun y => by
    have := LinearMap.congr_fun hs y
    simpa using this
  have hψ : ∀ x : Q, ((LinearMap.id : Q →ₗ[Rᵐᵒᵖ] Q) - s.comp p) x ∈ f.range := by
    intro x
    rw [hfp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.map_sub, hs']
    simp
  let ψ : Q →ₗ[Rᵐᵒᵖ] f.range :=
    LinearMap.codRestrict f.range ((LinearMap.id : Q →ₗ[Rᵐᵒᵖ] Q) - s.comp p) hψ
  refine ⟨e.symm.comp ψ, ?_⟩
  ext a
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h1 : p (f a) = 0 :=
    (LinearMap.mem_ker).mp (by rw [← hfp]; exact LinearMap.mem_range_self f a)
  have h2 : ψ (f a) = ⟨f a, LinearMap.mem_range_self f a⟩ := by
    apply Subtype.ext
    simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, h1, map_zero, sub_zero]
  rw [h2]
  apply hf
  exact LinearEquiv.ofInjective_symm_apply (h := hf) f
    (⟨f a, LinearMap.mem_range_self f a⟩ : f.range)

end Work.ORFlatness
