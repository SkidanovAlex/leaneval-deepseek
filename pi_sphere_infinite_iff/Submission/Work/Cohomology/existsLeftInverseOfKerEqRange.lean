import Mathlib

namespace Work.Cohomology

/-- Given a short exact sequence `0 → A → N → P → 0` of `R`-modules with `P` projective,
the injection `f : A →ₗ N` admits a left inverse (the sequence splits). -/
theorem existsLeftInverseOfKerEqRange {R : Type*} [Ring R] {A N P : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : A →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hker : LinearMap.ker g = LinearMap.range f)
    [Module.Projective R P] :
    ∃ r : N →ₗ[R] A, r.comp f = LinearMap.id := by
  -- Since `P` is projective, the surjection `g` splits.
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.2 hg)
  have hgs : ∀ p, g (s p) = p := fun p => by
    have := LinearMap.congr_fun hs p
    simpa [LinearMap.comp_apply] using this
  -- The endomorphism `σ = id - s ∘ g` retracts `N` onto `range f = ker g`.
  let σ : N →ₗ[R] N := LinearMap.id - s.comp g
  have hσ_apply : ∀ n, σ n = n - s (g n) := fun n => rfl
  have hσ_mem : ∀ n, σ n ∈ LinearMap.range f := by
    intro n
    have : g (σ n) = 0 := by
      rw [hσ_apply n, map_sub, hgs (g n), sub_self]
    rw [← hker]
    exact LinearMap.mem_ker.2 this
  have hσ_id : ∀ a, σ (f a) = f a := by
    intro a
    have hfa : f a ∈ LinearMap.ker g := by
      rw [hker]; exact LinearMap.mem_range_self f a
    have hgfa : g (f a) = 0 := LinearMap.mem_ker.1 hfa
    rw [hσ_apply (f a), hgfa, map_zero, sub_zero]
  let e : A ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  let r₀ : N →ₗ[R] LinearMap.range f := σ.codRestrict (LinearMap.range f) hσ_mem
  refine ⟨(e.symm : LinearMap.range f →ₗ[R] A).comp r₀, ?_⟩
  apply LinearMap.ext
  intro a
  have hr₀ : r₀ (f a) = e a := by
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply, hσ_id a]
    rfl
  show e.symm (r₀ (f a)) = a
  rw [hr₀]
  exact LinearEquiv.symm_apply_apply e a

end Work.Cohomology
