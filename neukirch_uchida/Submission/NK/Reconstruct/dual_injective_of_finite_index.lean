import Mathlib

namespace NK.Reconstruct

/-- A finite submodule of a torsion-free module over an infinite ring is trivial: if `y ≠ 0`
belonged to it, then `a ↦ a • y` would be an injection from the infinite ring `R` into `N`. -/
lemma submodule_eq_bot_of_finite {R M : Type*} [Ring R] [IsCancelMulZero R] [AddCommGroup M]
    [Module R M] [Module.IsTorsionFree R M] [Infinite R] (N : Submodule R M) (hN : Finite N) :
    N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  by_contra hne
  have hinj : Function.Injective (fun a : R => (⟨a • y, N.smul_mem a hy⟩ : N)) := by
    intro a b hab
    have h1 : a • y = b • y := Subtype.ext_iff.mp hab
    have h2 : (a - b) • y = 0 := by rw [sub_smul, h1, sub_self]
    rcases (smul_eq_zero.mp h2) with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hne
  exact (Finite.not_infinite hN) (Infinite.of_injective _ hinj)

/-- If `f : B → A` has finite-index image, then the dual of `A` (over `ℤ_[ℓ]`) injects into the
dual of `B`: a `ℤ_[ℓ]`-linear form on `A` that vanishes on the image of `f` is zero.

Indeed `φ` factors through the finite quotient `A ⧸ range f`; the image of the resulting map is a
finite submodule of `ℤ_[ℓ]`, which is torsion-free over the infinite ring `ℤ_[ℓ]`, so that image
is trivial. -/
theorem dual_injective_of_finite_index {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [Module (PadicInt ℓ) A] [AddCommGroup B] [Module (PadicInt ℓ) B]
    (f : B →ₗ[PadicInt ℓ] A) (hfin : Finite (A ⧸ LinearMap.range f))
    (φ : A →ₗ[PadicInt ℓ] PadicInt ℓ) (hφ : φ.comp f = 0) : φ = 0 := by
  -- `φ` kills the image of `f`, so it factors through the finite quotient `A ⧸ range f`.
  have hle : LinearMap.range f ≤ LinearMap.ker φ := LinearMap.range_le_ker_iff.mpr hφ
  let ψ : A ⧸ LinearMap.range f →ₗ[PadicInt ℓ] PadicInt ℓ := (LinearMap.range f).liftQ φ hle
  have hψ : ψ.comp (LinearMap.range f).mkQ = φ := Submodule.liftQ_mkQ (LinearMap.range f) φ hle
  -- Its image is a finite submodule of `ℤ_[ℓ]`, hence trivial.
  have hfr : Finite ↥ψ.range :=
    @Finite.of_surjective (A ⧸ LinearMap.range f) ↥ψ.range hfin
      (fun x => (⟨ψ x, LinearMap.mem_range_self ψ x⟩ : ψ.range))
      (fun y => by
        obtain ⟨x, hx⟩ := (LinearMap.mem_range).mp y.2
        exact ⟨x, Subtype.ext hx⟩)
  have hbot : ψ.range = ⊥ := submodule_eq_bot_of_finite ψ.range hfr
  have hψ0 : ψ = 0 := LinearMap.range_eq_bot.mp hbot
  rw [← hψ, hψ0, LinearMap.zero_comp]

end NK.Reconstruct
