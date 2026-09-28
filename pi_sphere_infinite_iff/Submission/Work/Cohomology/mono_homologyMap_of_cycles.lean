import Mathlib

namespace Work.Cohomology

open CategoryTheory

/-- **Injectivity of the map on homology induced by a chain map, from a lifting
condition on cycles.**

Let `φ : C ⟶ D` be a morphism of chain complexes of `ℤ`-modules and `n : ℕ`. Suppose
that every `n`-cycle `z` of `C` whose image `φ z` is a boundary in `D` is itself a
boundary in `C`:

`∀ z, ∂ z = 0 → ∀ a, φ z = ∂ a → ∃ w, ∂ w = z`.

Then `homologyMap φ n : Hₙ(C) → Hₙ(D)` is injective, i.e. a monomorphism in
`ModuleCat ℤ`.

We use Mathlib's refinement criterion for the monomorphy of `homologyMap`,
`HomologicalComplex.mono_homologyMap_iff_up_to_refinements`, which asks that for
every `x₂ : A ⟶ Cₙ` which is a cycle and every `y₁ : A ⟶ Dₙ₊₁` with
`x₂ ≫ φ.f n = y₁ ≫ ∂`, one can lift `x₂` to `x₁ : A' ⟶ Cₙ₊₁` along `∂` after
precomposing with an epimorphism `π : A' ⟶ A`.  The lift need not exist on `A`
itself (`∂ : Cₙ₊₁ → Cₙ` need not be split), so we take `A' := A →₀ ℤ`, the free
`ℤ`-module on `A`, with `π := Finsupp.linearCombination ℤ id`, and lift the
generators `a` individually using the hypothesis, which gives the required linear
map `A' ⟶ Cₙ₊₁`. -/
theorem mono_homologyMap_of_cycles {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (n : ℕ)
    (h : ∀ (z : C.X n), (C.d n (n - 1)) z = 0 →
          ∀ (a : D.X (n + 1)), (φ.f n) z = (D.d (n + 1) n) a →
          ∃ w : C.X (n + 1), (C.d (n + 1) n) w = z) :
    CategoryTheory.Mono (HomologicalComplex.homologyMap φ n) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements (K := C) (L := D) (φ := φ)
        (n + 1) n (n - 1) (by
          exact ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (n + 1) n from by simp))
        (by
          cases n with
          | zero =>
              rw [ComplexShape.next_eq_self' _ 0 (fun k hk => by
                simp [ComplexShape.down_Rel] at hk)]
          | succ m =>
              rw [ComplexShape.next_eq' _
                (show (ComplexShape.down ℕ).Rel (m + 1) m from by simp)]
              simp)]
  intro A x₂ hx₂ y₁ hy
  -- `x₂` is a cycle
  have hcyc : ∀ a : A, (C.d n (n - 1)) (x₂ a) = 0 := by
    intro a
    have h1 := ModuleCat.comp_apply x₂ (C.d n (n - 1)) a
    rw [hx₂] at h1
    simpa using h1.symm
  -- the boundary condition relating `x₂` and `y₁`
  have hbnd : ∀ a : A, (φ.f n) (x₂ a) = (D.d (n + 1) n) (y₁ a) := by
    intro a
    have h1 := ModuleCat.comp_apply x₂ (φ.f n) a
    have h2 := ModuleCat.comp_apply y₁ (D.d (n + 1) n) a
    rw [hy] at h1
    rw [h2] at h1
    exact h1.symm
  -- choose a lift in `C` of each element of the image of `x₂`
  let w : A → C.X (n + 1) := fun a => Classical.choose (h (x₂ a) (hcyc a) (y₁ a) (hbnd a))
  have hw : ∀ a : A, (C.d (n + 1) n) (w a) = x₂ a := fun a =>
    Classical.choose_spec (h (x₂ a) (hcyc a) (y₁ a) (hbnd a))
  -- refine along the free module `A →₀ ℤ` on `A`
  refine ⟨ModuleCat.of ℤ (A →₀ ℤ), ModuleCat.ofHom (Finsupp.linearCombination ℤ (id : A → A)), ?_,
      ModuleCat.ofHom (Finsupp.linearCombination ℤ w), ?_⟩
  · -- `π` is an epimorphism (it is surjective)
    rw [ModuleCat.epi_iff_surjective]
    simpa using Finsupp.linearCombination_id_surjective (R := ℤ) A
  · -- `π ≫ x₂ = x₁ ≫ ∂`
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro l
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [Finsupp.apply_linearCombination_id, Finsupp.apply_linearCombination]
    have hfun : (⇑(ModuleCat.Hom.hom (C.d (n + 1) n)) ∘ w) = ⇑(ModuleCat.Hom.hom x₂) :=
      funext (fun a => hw a)
    rw [hfun]

end Work.Cohomology
