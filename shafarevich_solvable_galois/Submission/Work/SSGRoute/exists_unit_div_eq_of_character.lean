import Mathlib
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A group homomorphism `Gal(M/U) → Uˣ` is a coboundary (Hilbert 90, Noether's form)

Let `M/U` be a finite-dimensional field extension (no separability, normality or Galois
hypothesis is needed) and let `d : (M ≃ₐ[U] M) →* Uˣ` be a homomorphism from the group of
`U`-algebra automorphisms of `M` into the units of the base field `U`.  Viewing `d` as taking
values in `Mˣ` via `U ↪ M`, it is a multiplicative `1`-cocycle, because the automorphisms fix `U`
and `U` is commutative.  The theorem below produces `β : Mˣ` with

`χ β / β = d χ`  for all `χ : M ≃ₐ[U] M`,

i.e. `d` is a coboundary: `H¹(Gal(M/U), Mˣ) = 1` in the concrete Noether form, for the
`U`-valued characters.

The proof is the classical one, and uses only Dedekind's linear independence of characters
(Mathlib's `linearIndependent_monoidHom`): the linear combination
`∑_χ d χ · χ` of the distinct field automorphisms `χ` has all coefficients nonzero, hence is not
the zero function, so there is `x` with `Y := ∑_χ d χ · χ x ≠ 0`. The cocycle identity gives
`d τ · τ Y = Y` for all `τ`, and then `β = Y⁻¹` is the required element.
-/

namespace Work.SSGRoute

theorem exists_unit_div_eq_of_character
    {U M : Type*} [Field U] [Field M] [Algebra U M] [FiniteDimensional U M]
    (d : (M ≃ₐ[U] M) →* Uˣ) :
    ∃ β : Mˣ, ∀ χ : M ≃ₐ[U] M,
      χ (β : M) / (β : M) = algebraMap U M (((d χ : Uˣ) : U)) := by
  classical
  -- `D χ` is `d χ`, regarded as an element of `M`.
  set D : (M ≃ₐ[U] M) → M := fun χ => algebraMap U M (((d χ : Uˣ) : U)) with hD
  have hD1 : D 1 = 1 := by simp [hD]
  have hDmul : ∀ χ ψ : M ≃ₐ[U] M, D (χ * ψ) = D χ * D ψ := by
    intro χ ψ
    simp only [hD, Units.val_mul, map_mul]
  -- The automorphisms fix `U`, hence fix each `D χ`.
  have hDfix : ∀ (τ χ : M ≃ₐ[U] M), τ (D χ) = D χ := by
    intro τ χ
    simp only [hD]
    exact τ.commutes _
  have hDne : ∀ χ : M ≃ₐ[U] M, D χ ≠ 0 := by
    intro χ
    simp only [hD]
    exact fun h => (d χ).ne_zero ((algebraMap U M).injective (by rw [h, map_zero]))
  -- Dedekind: the characters `χ : M → M` are linearly independent over `M`.
  have hli : LinearIndependent M (fun χ : M ≃ₐ[U] M => (χ : M → M)) :=
    LinearIndependent.comp (ι' := M ≃ₐ[U] M) (linearIndependent_monoidHom M M)
      (fun χ => (χ : M →* M))
      (fun a b hab => by ext x; exact DFunLike.ext_iff.1 hab x)
  -- Hence the linear combination `∑_χ D χ · χ` is not the zero function.
  have hex : ∃ x : M, (∑ χ : M ≃ₐ[U] M, D χ * χ x) ≠ 0 := by
    by_contra h
    push Not at h
    have hcomb : (∑ χ : M ≃ₐ[U] M, D χ • (fun x : M => (χ : M → M) x)) = 0 := by
      funext x
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact h x
    have h0 := Fintype.linearIndependent_iff.mp hli (fun χ => D χ) hcomb 1
    rw [hD1] at h0
    exact one_ne_zero h0
  obtain ⟨x, hx⟩ := hex
  set Y : M := ∑ χ : M ≃ₐ[U] M, D χ * χ x with hY
  -- The key identity: `d τ · τ Y = Y` for every `τ`.
  have hkey : ∀ τ : M ≃ₐ[U] M, D τ * τ Y = Y := by
    intro τ
    have hterm : ∀ χ : M ≃ₐ[U] M, D τ * τ (D χ * χ x) = D (τ * χ) * (τ * χ) x := by
      intro χ
      rw [map_mul, hDfix τ χ, ← mul_assoc, hDmul τ χ]
      rfl
    calc D τ * τ Y = D τ * τ (∑ χ : M ≃ₐ[U] M, D χ * χ x) := by rw [hY]
      _ = D τ * ∑ χ : M ≃ₐ[U] M, τ (D χ * χ x) := by rw [map_sum]
      _ = ∑ χ : M ≃ₐ[U] M, D τ * τ (D χ * χ x) := by rw [Finset.mul_sum]
      _ = ∑ χ : M ≃ₐ[U] M, D (τ * χ) * (τ * χ) x :=
          Finset.sum_congr rfl (fun χ _ => hterm χ)
      _ = ∑ ψ : M ≃ₐ[U] M, D ψ * ψ x :=
          Fintype.sum_bijective (fun χ => τ * χ) (Group.mulLeft_bijective τ) _ _
            (fun χ => rfl)
      _ = Y := by rw [hY]
  -- With `β = Y⁻¹` we get `χ β / β = (χ Y / Y)⁻¹ = d χ`.
  refine ⟨(Units.mk0 Y hx)⁻¹, fun χ => ?_⟩
  have hval : (((Units.mk0 Y hx)⁻¹ : Mˣ) : M) = Y⁻¹ := by simp
  rw [hval]
  change χ Y⁻¹ / Y⁻¹ = D χ
  rw [map_inv₀, div_eq_iff (inv_ne_zero hx)]
  conv_rhs => rw [← hkey χ]
  rw [mul_inv_rev, ← mul_assoc, mul_comm (D χ) ((χ Y)⁻¹), mul_assoc,
    mul_inv_cancel₀ (hDne χ), mul_one]

end Work.SSGRoute
