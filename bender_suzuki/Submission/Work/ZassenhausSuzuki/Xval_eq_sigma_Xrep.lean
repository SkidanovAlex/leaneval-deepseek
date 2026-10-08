import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.frel_spread
import Submission.Work.ZassenhausSuzuki.frel_generic_value_eps
import Submission.Work.ZassenhausSuzuki.frel_center

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Xval θ ν ξ = σ (Xrep θ ν)`: the generic value of HB III XI 11.13 (b)

In the Suzuki-group coordinatisation `A(K,θ)` (`K` of characteristic two, `θ² = x ↦ x²` a Ts
endomorphism) the generic `D`-orbit representative is
`Xrep θ ν = (1+ν, θν·(1+ν))` and the value that the book's map `f` takes at it is
`Xval θ ν ξ = (ν⁻²ξ⁻¹ + ν⁻¹, θ(ν⁻¹)·(ν⁻²ξ⁻¹ + ν⁻¹))`, where `ξ` is the auxiliary unit with
`ξ·θξ = 1 + ν⁻¹·θ(ν⁻¹)` (the existence/uniqueness of `ξ` is `θ² =` Frobenius + `Fix θ = {0,1}`).

This file proves that the two agree: `Xval` is *exactly* the Suzuki involution `σ` evaluated at
`Xrep θ ν`.  The mathematical content is the identity

`θ ν · ν² · ξ · (1+ν) = (1 + ν ξ) · (1 + ν² θ ν)`   (`XvalKey` below),

whose proof uses the two companion forms of the hypothesis on `ξ`:
`νθν·(ξθξ) = νθν + 1` (the hypothesis itself) and its image under `θ`,
`ν²θν·(ξ²θξ) = ν²θν + 1`.  Writing `N(Xrep θ ν) = (1+ν)²(1+θν) + (1+ν)·θν(1+ν) + ν²(1+θν)`
and using `(1+ν)² = 1+ν²` in characteristic two gives `N(Xrep θ ν) = 1 + ν²θν`, and the key
identity then states precisely that `(1+νξ)/(ν²ξ)` — the common value of the two coordinates —
equals `θν(1+ν)/N` and `θ(ν⁻¹)·θν(1+ν)/N`.
-/

set_option autoImplicit false

namespace Work.ZassenhausSuzuki

/-- Companion form of the hypothesis on `ξ`, obtained by applying `θ`.

From `ξ·θξ = 1 + ν⁻¹θ(ν⁻¹)`, using `θ(ν⁻¹) = (θν)⁻¹` and `θ² = (·)²` on both `ν` and `ξ`:
`ξ²·θξ = 1 + (ν²θν)⁻¹`. -/
private lemma sq_mul_theta_of_unit {K : Type*} [Field K] (θ : K ≃+* K) {ν ξ : K}
    (h2 : ∀ x : K, θ (θ x) = x ^ 2)
    (hx : ξ * θ ξ = 1 + ν⁻¹ * θ (ν⁻¹)) :
    ξ ^ 2 * θ ξ = 1 + (ν ^ 2 * θ ν)⁻¹ := by
  have hx1 : ξ * θ ξ = 1 + ν⁻¹ * (θ ν)⁻¹ := by simpa [map_inv₀] using hx
  have h := congrArg θ hx1
  simp only [map_mul, map_add, map_one, map_inv₀] at h
  rw [h2 ξ, h2 ν] at h
  rw [mul_comm (θ ξ) (ξ ^ 2)] at h
  rw [h, mul_inv_rev]

/-- **The norm of the generic representative** (BG Definition 5.5).

`N(Xrep θ ν) = (1+ν)²(1+θν) + (1+ν)·θν(1+ν) + ν²(1+θν) = 1 + ν²θν`, where the middle
simplifications `(1+ν)² = 1+ν²` and `θν + θν = 0` use characteristic two. -/
private lemma N_Xrep {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) {ν : K}
    (h2 : θ (θ ν) = ν ^ 2) : SzA.N θ (Xrep θ ν) = 1 + ν ^ 2 * θ ν := by
  rw [Xrep, SzA.N_mk]
  rw [map_mul, h2, map_add, map_one]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod]
  ring

/-- **The key identity of HB III XI 11.13 (b).**

For `ν ≠ 0`, `θ²ν = ν²` and `ξ·θξ = 1 + ν⁻¹θ(ν⁻¹)`:
`θν·ν²·ξ·(1+ν) = (1+νξ)·(1+ν²θν)`.

Writing `S := ν²θνξ + 1 + ν²θν + νξ` for the sum of the two sides, the two companion forms
`νθν·ξθξ = νθν+1` and `ν²θν·ξ²θξ = ν²θν+1` of the hypothesis give
`S = νξ(νθν + νθνξθξ + 1) = νξ(νθν + (νθν+1) + 1) = 0`. -/
private lemma XvalKey {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) {ν ξ : K}
    (hν : ν ≠ 0) (hθν : θ ν ≠ 0) (h2 : ∀ x : K, θ (θ x) = x ^ 2)
    (hx : ξ * θ ξ = 1 + ν⁻¹ * θ (ν⁻¹)) :
    θ ν * ν ^ 2 * ξ * (1 + ν) = (1 + ν * ξ) * (1 + ν ^ 2 * θ ν) := by
  have hx1 : ξ * θ ξ = 1 + ν⁻¹ * (θ ν)⁻¹ := by simpa [map_inv₀] using hx
  have hxθ : ξ ^ 2 * θ ξ = 1 + (ν ^ 2 * θ ν)⁻¹ := sq_mul_theta_of_unit θ h2 hx
  -- the two companion forms of the hypothesis
  have hA : ν * θ ν * (ξ * θ ξ) = ν * θ ν + 1 := by
    rw [hx1]; field_simp
  have hB : ν ^ 2 * θ ν * (ξ ^ 2 * θ ξ) = ν ^ 2 * θ ν + 1 := by
    rw [hxθ]; field_simp
  -- the sum of the two sides of the claim vanishes
  have hS : ν ^ 2 * θ ν * ξ + 1 + ν ^ 2 * θ ν + ν * ξ = 0 := by
    have hB' : ν ^ 2 * θ ν + 1 = ν ^ 2 * θ ν * (ξ ^ 2 * θ ξ) := hB.symm
    calc ν ^ 2 * θ ν * ξ + 1 + ν ^ 2 * θ ν + ν * ξ
        = ν * ξ * (ν * θ ν) + (ν ^ 2 * θ ν + 1) + ν * ξ := by ring
      _ = ν * ξ * (ν * θ ν) + ν ^ 2 * θ ν * (ξ ^ 2 * θ ξ) + ν * ξ := by rw [hB']
      _ = ν * ξ * (ν * θ ν + ν * θ ν * (ξ * θ ξ) + 1) := by ring
      _ = ν * ξ * (ν * θ ν + (ν * θ ν + 1) + 1) := by rw [hA]
      _ = 0 := by ring_nf; simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod]; ring
  have hsum : θ ν * ν ^ 2 * ξ * (1 + ν) + (1 + ν * ξ) * (1 + ν ^ 2 * θ ν) = 0 := by
    rw [← hS]; ring_nf; simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod]; ring
  rwa [CharTwo.add_eq_zero] at hsum

/-- **HB III XI 11.13 (b), coordinate form.**

The value `Xval θ ν ξ` that the book's map `f` takes at the generic orbit representative
`Xrep θ ν = (1+ν, θν(1+ν))` is exactly the Suzuki involution `σ` applied to `Xrep θ ν`.
Both coordinates of `σ (Xrep θ ν) = (b/N, a/N)` equal the common value `(1+νξ)/(ν²ξ)` of the two
coordinates of `Xval θ ν ξ`; this is `XvalKey`, together with `N = 1 + ν²θν` and `N ≠ 0`. -/
theorem Xval_eq_sigma_Xrep {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K)
    (hθ : Work.ZassenhausSuzuki.IsTitsTheta θ) (nu xi : Kˣ) (hnu : (nu : K) ≠ 1)
    (hxi : (xi : K) * θ (xi : K) = 1 + ((nu : K))⁻¹ * θ (((nu : K))⁻¹)) :
    Work.ZassenhausSuzuki.Xval θ (nu : K) (xi : K)
      = Work.ZassenhausSuzuki.SzA.sigma θ (Work.ZassenhausSuzuki.Xrep θ (nu : K)) := by
  set ν : K := (nu : K) with hνnu
  set ξ : K := (xi : K) with hξxi
  have hν : ν ≠ 0 := by simp [hνnu]
  have hξ : ξ ≠ 0 := by simp [hξxi]
  have h2 : ∀ x : K, θ (θ x) = x ^ 2 := hθ.2
  have hθν : θ ν ≠ 0 := fun h => hν (θ.injective (by rw [h, map_zero]))
  have hθξ : θ ξ ≠ 0 := fun h => hξ (θ.injective (by rw [h, map_zero]))
  have hν1 : 1 + ν ≠ 0 := by
    intro h
    apply hnu
    have h1 : ν = 1 := by
      have h2' : ν = -1 := by linear_combination h
      rw [h2', CharTwo.neg_eq]
    simpa [hνnu] using h1
  have hx : ξ * θ ξ = 1 + ν⁻¹ * θ (ν⁻¹) := by
    simpa [hνnu, hξxi] using hxi
  have hkey : θ ν * ν ^ 2 * ξ * (1 + ν) = (1 + ν * ξ) * (1 + ν ^ 2 * θ ν) :=
    XvalKey θ hν hθν h2 hx
  have hN : SzA.N θ (Xrep θ ν) = 1 + ν ^ 2 * θ ν := N_Xrep θ (h2 ν)
  -- `1 + ν²θν = ν²θν·ξ²θξ`, hence non-zero
  have hB : ν ^ 2 * θ ν * (ξ ^ 2 * θ ξ) = ν ^ 2 * θ ν + 1 := by
    rw [sq_mul_theta_of_unit θ h2 hx]; field_simp
  have hN0 : 1 + ν ^ 2 * θ ν ≠ 0 := by
    rw [add_comm 1 (ν ^ 2 * θ ν), ← hB]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hν) hθν)
      (mul_ne_zero (pow_ne_zero 2 hξ) hθξ)
  have hD : ν ^ 2 * ξ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hν) hξ
  -- the key identity, commuted
  have hK : (1 + ν * ξ) * (1 + ν ^ 2 * θ ν) = θ ν * (1 + ν) * (ν ^ 2 * ξ) := by
    rw [← hkey]; ring
  have hA : ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹ = (1 + ν * ξ) / (ν ^ 2 * ξ) := by
    field_simp
  have hB2 : θ ν * (1 + ν) / (1 + ν ^ 2 * θ ν) = (1 + ν * ξ) / (ν ^ 2 * ξ) := by
    rw [div_eq_div_iff hN0 hD]
    rw [hK]
  have hC : (θ ν)⁻¹ * ((1 + ν * ξ) / (ν ^ 2 * ξ)) = (1 + ν) / (1 + ν ^ 2 * θ ν) := by
    rw [← mul_div_assoc, div_eq_div_iff hD hN0]
    calc (θ ν)⁻¹ * (1 + ν * ξ) * (1 + ν ^ 2 * θ ν)
        = (θ ν)⁻¹ * ((1 + ν * ξ) * (1 + ν ^ 2 * θ ν)) := by ring
      _ = (θ ν)⁻¹ * (θ ν * (1 + ν) * (ν ^ 2 * ξ)) := by rw [hK]
      _ = (1 + ν) * (ν ^ 2 * ξ) := by field_simp
  apply SzA.ext
  · simpa only [Xval_a, SzA.sigma_a, Xrep_b, hN] using hA.trans hB2.symm
  · have h1 : θ (ν⁻¹) * (ν⁻¹ ^ 2 * ξ⁻¹ + ν⁻¹)
        = (θ ν)⁻¹ * ((1 + ν * ξ) / (ν ^ 2 * ξ)) := by
      rw [map_inv₀, hA]
    simpa only [Xval_b, SzA.sigma_b, Xrep_a, hN] using h1.trans hC

end Work.ZassenhausSuzuki
