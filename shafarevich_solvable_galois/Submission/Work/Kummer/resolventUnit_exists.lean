/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer resolvent / Noether's form of Hilbert's Theorem 90

For a finite Galois extension `L/K`, every character `χ : Gal(L/K) →* μ_n(K)` is the Kummer
character of some element `β ∈ Lˣ`: there is `β` with `σ β / β = χ(σ)` for all `σ`, and then
automatically `β ^ n ∈ K` (indeed `β ^ n` is fixed by `Gal(L/K)`).

The essential input is Noether's generalization of Hilbert's Theorem 90 for the multiplicative
group `Lˣ`: since `χ` takes values in `K` (which is fixed by `Gal(L/K)`), it is a crossed
homomorphism, hence a coboundary.  The proof below is the classical Lagrange resolvent: for a
homomorphism `d : Gal(L/K) →* Kˣ` the combination
`R = ∑_σ d(σ)⁻¹ · σ(x)` is an eigenvector for `d(τ)`, and it is nonzero for a suitable `x` by
Dedekind's linear independence of the automorphisms.
-/
import Mathlib
import Submission.Work.Kummer.Pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

open IntermediateField

section Resolvent

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- **Noether's form of Hilbert's Theorem 90 (resolvent).**  For a finite Galois extension
`L/K` and a homomorphism `d : Gal(L/K) →* Kˣ` there is `β : Lˣ` with
`kummerRatio σ β = d(σ)` for every `σ : Gal(L/K)`. -/
theorem kummerResolvent_exists (d : Gal(L/K) →* Kˣ) :
    ∃ β : Lˣ, ∀ σ : Gal(L/K), kummerRatio σ β = Units.map (algebraMap K L) (d σ) := by
  classical
  -- Dedekind's linear independence of the `K`-automorphisms of `L`.
  have hli : LinearIndependent L (fun f : Gal(L/K) => (f : L → L)) :=
    LinearIndependent.comp (ι' := Gal(L/K)) (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  -- Work with the inverse character, so that the resolvent has eigenvalue `d(τ)`.
  set e : Gal(L/K) →* Kˣ := d⁻¹ with he
  set c : Gal(L/K) → L := fun σ => algebraMap K L ((e σ : Kˣ) : K) with hc
  have hc_mul : ∀ σ τ, c (σ * τ) = c σ * c τ := by
    intro σ τ; simp only [hc, map_mul e, Units.val_mul, map_mul]
  have hc_one : c 1 = 1 := by simp only [hc, map_one e, Units.val_one, map_one]
  have hc_inv : ∀ σ, c σ⁻¹ = (c σ)⁻¹ := by
    intro σ; simp only [hc, map_inv e, Units.val_inv_eq_inv_val, map_inv₀]
  have hc_fix : ∀ (τ σ : Gal(L/K)), (τ : L ≃ₐ[K] L) (c σ) = c σ :=
    fun τ σ => AlgEquiv.commutes τ _
  -- The linear combination `∑ σ, c σ • σ` is not the zero operator.
  have hsum_ne : (∑ σ : Gal(L/K), c σ • (σ : L → L)) ≠ 0 := by
    intro h0
    have h1 := (Fintype.linearIndependent_iff.mp hli) c h0 1
    rw [hc_one] at h1
    exact one_ne_zero h1
  obtain ⟨x, hx⟩ : ∃ x : L, (∑ σ : Gal(L/K), c σ * (σ : L ≃ₐ[K] L) x) ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum_ne (funext fun y => by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h y)
  set R : L := ∑ σ : Gal(L/K), c σ * (σ : L ≃ₐ[K] L) x with hRdef
  have hR0 : R ≠ 0 := by rw [hRdef]; exact hx
  -- `R` is an eigenvector with eigenvalue `c(τ)⁻¹ = e(τ)`.
  have hτ : ∀ τ : Gal(L/K), (τ : L ≃ₐ[K] L) R = (c τ)⁻¹ * R := by
    intro τ
    have hstep : (τ : L ≃ₐ[K] L) R
        = ∑ σ : Gal(L/K), c (τ⁻¹ * σ) * (σ : L ≃ₐ[K] L) x := by
      rw [hRdef, map_sum]
      refine Fintype.sum_bijective (fun σ : Gal(L/K) => τ * σ) (Group.mulLeft_bijective τ)
        (fun σ : Gal(L/K) => (τ : L ≃ₐ[K] L) (c σ * (σ : L ≃ₐ[K] L) x))
        (fun σ : Gal(L/K) => c (τ⁻¹ * σ) * (σ : L ≃ₐ[K] L) x) ?_
      intro σ
      rw [map_mul, hc_fix, AlgEquiv.mul_apply]
      congr 1
      rw [show τ⁻¹ * (τ * σ) = σ by group]
    rw [hstep]
    have hc2 : ∀ σ : Gal(L/K), c (τ⁻¹ * σ) = (c τ)⁻¹ * c σ := by
      intro σ
      rw [← hc_inv τ, ← hc_mul τ⁻¹ σ]
    have h1 : (∑ σ : Gal(L/K), c (τ⁻¹ * σ) * (σ : L ≃ₐ[K] L) x)
        = ∑ σ : Gal(L/K), (c τ)⁻¹ * (c σ * (σ : L ≃ₐ[K] L) x) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hc2 σ, mul_assoc]
    rw [h1, ← Finset.mul_sum, ← hRdef]
  refine ⟨Units.mk0 R hR0, fun τ => ?_⟩
  apply Units.ext
  rw [kummerRatio_coe, Units.val_mk0, Units.coe_map, hτ τ, mul_div_cancel_right₀ _ hR0]
  simp only [hc, he, MonoidHom.inv_apply]
  rw [← map_inv₀, ← Units.val_inv_eq_inv_val, inv_inv]
  rfl

end Resolvent

/-- **Existence of the Kummer resolvent.**  For a finite Galois extension `L/K` and any character
`χ : Gal(L/K) →* μ_n(K)`, there is a unit `β ∈ Lˣ` with `σ β / β = χ(σ)` for all `σ`, and with
`β ^ n ∈ K`. -/
theorem resolventUnit_exists {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] [FiniteDimensional K L] [IsGalois K L]
    (χ : Gal(L/K) →* rootsOfUnity n K) :
    ∃ β : Lˣ, (∀ σ : Gal(L/K),
        kummerRatio σ β = Units.map (algebraMap K L) ((χ σ : rootsOfUnity n K) : Kˣ)) ∧
      ∃ a : Kˣ, β ^ n = Units.map (algebraMap K L) a := by
  classical
  let d : Gal(L/K) →* Kˣ := (rootsOfUnity n K).subtype.comp χ
  obtain ⟨β, hβ⟩ := kummerResolvent_exists (K := K) (L := L) d
  -- `d(σ) ^ n = 1`, since `χ` takes values in the `n`-th roots of unity.
  have hdpow : ∀ σ : Gal(L/K), (d σ) ^ n = 1 := by
    intro σ
    have h : (((χ σ : rootsOfUnity n K) : Kˣ)) ^ n = 1 :=
      (mem_rootsOfUnity n _).mp (χ σ).2
    simpa [d] using h
  -- Hence `σ β = d(σ) · β`.
  have hsigma : ∀ σ : Gal(L/K),
      (σ : L ≃ₐ[K] L) (β : L) = algebraMap K L ((d σ : Kˣ) : K) * (β : L) := by
    intro σ
    have h2 := congrArg (fun u : Lˣ => (u : L)) (hβ σ)
    rw [kummerRatio_coe, Units.coe_map] at h2
    rw [div_eq_iff_mul_eq (Units.ne_zero β)] at h2
    exact h2.symm
  -- So `β ^ n` is fixed by `Gal(L/K)`.
  have hfixpow : ∀ τ : Gal(L/K),
      (τ : L ≃ₐ[K] L) (((β : Lˣ) : L) ^ n) = ((β : Lˣ) : L) ^ n := by
    intro τ
    rw [map_pow, hsigma τ, mul_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hdpow τ,
      Units.val_one, map_one, one_mul]
  -- Since `L/K` is Galois, the fixed field is `K`.
  obtain ⟨a, ha⟩ := Set.mem_range.mp
    ((IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) ((β : L) ^ n)).mpr hfixpow)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero n (Units.ne_zero β) ha.symm
  refine ⟨β, ?_, Units.mk0 a ha0, ?_⟩
  · simpa [d] using hβ
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
    exact ha.symm

end Work.Kummer
