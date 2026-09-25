import Mathlib
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions

namespace NK.HeckeL.Product

open Polynomial

/-- For a primitive `k`-th root of unity `ζ` in `ℂ` and any `x : ℂ`,
`∏_{i<k} (1 - ζ^i * x) = 1 - x^k`.

This is the classical identity `∏_{ζ^k = 1} (1 - ζ x) = 1 - x^k` written with an
explicit primitive root: it follows from `∏_{i<k} (X - ζ^i) = X^k - 1`
(`X_pow_sub_C_eq_prod`) by evaluating at `X = 0` and at `X = x` (for the primitive
root `ζ⁻¹`) and splitting off the factor `-ζ^i` in each term. -/
private lemma prod_range_one_sub_pow_mul {ζ : ℂ} {k : ℕ} (hζ : IsPrimitiveRoot ζ k)
    (hk : 0 < k) (x : ℂ) :
    ∏ i ∈ Finset.range k, (1 - ζ ^ i * x) = 1 - x ^ k := by
  -- Evaluate `∏_{i<k} (X - ζ⁻¹^i) = X^k - 1` at `X = x`.
  have h1 : ∏ i ∈ Finset.range k, (x - (ζ⁻¹) ^ i) = x ^ k - 1 := by
    have h := congrArg (Polynomial.eval x)
      (X_pow_sub_C_eq_prod hζ.inv hk (one_pow k : (1 : ℂ) ^ k = 1))
    rw [Polynomial.eval_prod] at h
    simpa using h.symm
  -- Evaluate `∏_{i<k} (X - ζ^i) = X^k - 1` at `X = 0`, giving `∏_{i<k} (-ζ^i) = -1`.
  have hneg : ∏ i ∈ Finset.range k, -(ζ ^ i) = -1 := by
    have h := congrArg (Polynomial.eval (0 : ℂ))
      (X_pow_sub_C_eq_prod hζ hk (one_pow k : (1 : ℂ) ^ k = 1))
    rw [Polynomial.eval_prod] at h
    simpa [zero_pow hk.ne'] using h.symm
  have hz0 : ζ ≠ 0 := hζ.ne_zero hk.ne'
  -- `1 - ζ^i x = (-ζ^i) * (x - (ζ⁻¹)^i)`.
  have key : ∀ i : ℕ, 1 - ζ ^ i * x = -(ζ ^ i) * (x - (ζ⁻¹) ^ i) := by
    intro i
    have hz : ζ ^ i * (ζ⁻¹) ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hz0, one_pow]
    calc 1 - ζ ^ i * x = -(ζ ^ i * x) + ζ ^ i * (ζ⁻¹) ^ i := by rw [hz]; ring
      _ = -(ζ ^ i) * (x - (ζ⁻¹) ^ i) := by ring
  rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib, hneg, h1]
  ring

theorem prod_zpowers_monoidHom_one_sub_mul {G : Type*} [CommGroup G] [Fintype G] (σ : G) (x : ℂ) :
    ∏ ψ : Subgroup.zpowers σ →* ℂˣ, (1 - ((ψ ⟨σ, Subgroup.mem_zpowers σ⟩ : ℂˣ) : ℂ) * x)
      = 1 - x ^ orderOf σ := by
  classical
  -- `H := Subgroup.zpowers σ` is cyclic of order `orderOf σ`, so its group of complex
  -- characters is (via evaluation at `σ`) the group of `orderOf σ`-th roots of unity.
  have hk : 0 < Nat.card (Subgroup.zpowers σ) := by
    rw [Nat.card_zpowers σ]; exact orderOf_pos σ
  have : NeZero (Nat.card (Subgroup.zpowers σ)) := ⟨hk.ne'⟩
  have : Fintype (rootsOfUnity (Nat.card (Subgroup.zpowers σ)) ℂ) := Fintype.ofFinite _
  have hgen : ∀ y : Subgroup.zpowers σ,
      y ∈ Subgroup.zpowers (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) := by
    intro y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
    have hy : (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) ^ m = y := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hm
    rw [← hy]
    exact Subgroup.zpow_mem_zpowers _ m
  let e₁ : (Subgroup.zpowers σ →* ℂˣ) ≃* rootsOfUnity (Nat.card (Subgroup.zpowers σ)) ℂˣ :=
    IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator hgen ℂˣ
  let e : (Subgroup.zpowers σ →* ℂˣ) ≃* rootsOfUnity (Nat.card (Subgroup.zpowers σ)) ℂ :=
    e₁.trans (rootsOfUnityUnitsMulEquiv ℂ (Nat.card (Subgroup.zpowers σ)))
  have he : ∀ ψ : Subgroup.zpowers σ →* ℂˣ,
      ((e ψ : ℂˣ) : ℂ) = ((ψ ⟨σ, Subgroup.mem_zpowers σ⟩ : ℂˣ) : ℂ) := by
    intro ψ; congr 1
  -- A primitive `Nat.card H`-th root of unity, and its unit incarnation.
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card (Subgroup.zpowers σ)))
  have hω : IsPrimitiveRoot ω (Nat.card (Subgroup.zpowers σ)) :=
    Complex.isPrimitiveRoot_exp _ hk.ne'
  let u : ℂˣ := (hω.toRootsOfUnity : ℂˣ)
  have hue : (u : ℂ) = ω := rootsOfUnity.coe_mkOfPowEq hω.pow_eq_one
  have hu : IsPrimitiveRoot u (Nat.card (Subgroup.zpowers σ)) :=
    IsPrimitiveRoot.coe_units_iff.mp (by rw [hue]; exact hω)
  -- Reindex the product over the character group as a product over the roots of unity.
  have hstep1 : ∏ ψ : Subgroup.zpowers σ →* ℂˣ,
        (1 - ((ψ ⟨σ, Subgroup.mem_zpowers σ⟩ : ℂˣ) : ℂ) * x)
      = ∏ ζ : rootsOfUnity (Nat.card (Subgroup.zpowers σ)) ℂ, (1 - ((ζ : ℂˣ) : ℂ) * x) := by
    refine Fintype.prod_bijective (fun ψ => e ψ) e.bijective _ _ (fun ψ => ?_)
    rw [he ψ]
  -- Reindex the product over the roots of unity as a product over `range`.
  have hrange : ∏ ζ : rootsOfUnity (Nat.card (Subgroup.zpowers σ)) ℂ,
        (1 - ((ζ : ℂˣ) : ℂ) * x)
      = ∏ i ∈ Finset.range (Nat.card (Subgroup.zpowers σ)), (1 - (u : ℂ) ^ i * x) := by
    refine (Finset.prod_bij
      (fun i _ => (⟨u ^ i, Subgroup.pow_mem _ hu.mem_rootsOfUnity i⟩ : rootsOfUnity _ ℂ))
      ?_ ?_ ?_ ?_).symm
    · intro i _; exact Finset.mem_univ _
    · intro i hi j hj hij
      exact hu.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (Subtype.ext_iff.mp hij)
    · intro b _
      obtain ⟨i, hi, hiu⟩ := hu.eq_pow_of_mem_rootsOfUnity b.2
      exact ⟨i, Finset.mem_range.mpr hi, Subtype.ext hiu⟩
    · intro i _; simp
  rw [hstep1, hrange]
  rw [show (∏ i ∈ Finset.range (Nat.card (Subgroup.zpowers σ)), (1 - (u : ℂ) ^ i * x))
      = ∏ i ∈ Finset.range (Nat.card (Subgroup.zpowers σ)), (1 - ω ^ i * x) by
    refine Finset.prod_congr rfl (fun i _ => by rw [hue])]
  rw [prod_range_one_sub_pow_mul hω hk x, Nat.card_zpowers σ]

end NK.HeckeL.Product
