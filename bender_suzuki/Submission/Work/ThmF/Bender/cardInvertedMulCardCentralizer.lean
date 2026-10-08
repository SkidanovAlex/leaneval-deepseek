import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Appendix I (1)(b) at `d = 2`: `|J(X,t)| · |C_X(t)| = |X|`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix I (1)(b) (p. 200), in the case `d = 2`:
if `t` is an involution normalising a subgroup `X` of odd order, and

`J(X,t) = invertedBy X t = {x ∈ X | t x t⁻¹ = x⁻¹}`,

then `|X| = |J(X,t)| · |C_X(t)|`.  Equivalently the multiplication map

`(c, k) ↦ c * k : (X ⊓ C_G(t)) × J(X,t) → X`

is a bijection.  Injectivity uses that `X` has odd order (so squaring is injective on `X`);
surjectivity is proved by exhibiting the factorisation explicitly: for `x ∈ X` one takes the
unique square root `k ∈ X` of `(t x t⁻¹)⁻¹ x`, checks that `t k t⁻¹ = k⁻¹`, and sets
`c = x k⁻¹`.

This is the "three-point" counting input of the Bender–Suzuki argument.
-/

namespace Work.ThmF.Bender

open Submission.Blueprint

/-- **Injectivity of the multiplication map `(c,k) ↦ c k`.**  If `cᵢ ∈ C_G(t)` and `kᵢ ∈ J(X,t)`
with `c₁ k₁ = c₂ k₂`, then `c₁ = c₂` and `k₁ = k₂` — provided `X` has odd order, so that
squaring is injective on `X`.

Writing `u = c₂⁻¹ c₁ = k₂ k₁⁻¹`, the element `u` is both centralised by `t` (it is a product of
elements of `C_G(t)`) and inverted by `t` (it is a product of two elements of `J(X,t)`); hence
`k₂ k₁⁻¹ = k₂⁻¹ k₁`, so `k₁² = k₂²` and `k₁ = k₂`, whence `c₁ = c₂`. -/
theorem mul_invertedBy_centralizer_injective {G : Type*} [Group G] [Finite G] {t : G}
    {X : Subgroup G} (hodd : Odd (Nat.card X)) :
    ∀ c₁ c₂ k₁ k₂ : G, c₁ ∈ Subgroup.centralizer ({t} : Set G) → c₁ ∈ X →
      k₁ ∈ invertedBy X t → c₂ ∈ Subgroup.centralizer ({t} : Set G) → c₂ ∈ X →
      k₂ ∈ invertedBy X t → c₁ * k₁ = c₂ * k₂ → c₁ = c₂ ∧ k₁ = k₂ := by
  have hsqinj : Function.Injective (fun x : ↥X => x ^ 2) :=
    (Nat.Coprime.pow_left_bijective (Nat.coprime_two_right.mpr hodd)).1
  intro c₁ c₂ k₁ k₂ hc₁C hc₁X hk₁ hc₂C hc₂X hk₂ heq
  have hk₁t : t * k₁ * t⁻¹ = k₁⁻¹ := hk₁.2
  have hk₂t : t * k₂ * t⁻¹ = k₂⁻¹ := hk₂.2
  -- `c₂⁻¹ * c₁ = k₂ * k₁⁻¹`
  have hu : c₂⁻¹ * c₁ = k₂ * k₁⁻¹ := by
    have h : c₂⁻¹ * c₁ * k₁ = k₂ := by
      calc c₂⁻¹ * c₁ * k₁ = c₂⁻¹ * (c₁ * k₁) := by group
        _ = c₂⁻¹ * (c₂ * k₂) := by rw [heq]
        _ = k₂ := by group
    calc c₂⁻¹ * c₁ = (c₂⁻¹ * c₁ * k₁) * k₁⁻¹ := by group
      _ = k₂ * k₁⁻¹ := by rw [h]
  -- it lies in `C_G(t)`
  have huC : c₂⁻¹ * c₁ ∈ Subgroup.centralizer ({t} : Set G) :=
    (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hc₂C) hc₁C
  have hucomm : t * (c₂⁻¹ * c₁) * t⁻¹ = c₂⁻¹ * c₁ := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp huC
    rw [← h]; group
  -- while conjugation by `t` inverts it
  have huconj : t * (c₂⁻¹ * c₁) * t⁻¹ = k₂⁻¹ * k₁ := by
    rw [hu]
    rw [show t * (k₂ * k₁⁻¹) * t⁻¹ = (t * k₂ * t⁻¹) * (t * k₁⁻¹ * t⁻¹) from by group,
        hk₂t, show t * k₁⁻¹ * t⁻¹ = k₁ from by
          rw [show t * k₁⁻¹ * t⁻¹ = (t * k₁ * t⁻¹)⁻¹ from by group, hk₁t, inv_inv]]
  have h4 : k₂ * k₁⁻¹ = k₂⁻¹ * k₁ := hu.symm.trans (hucomm.symm.trans huconj)
  -- hence `k₁² = k₂²`
  have hsq : k₁ * k₁ = k₂ * k₂ := by
    have key : k₂ * (k₂ * k₁⁻¹) * k₁ = k₂ * (k₂⁻¹ * k₁) * k₁ := by rw [h4]
    rw [show k₂ * (k₂ * k₁⁻¹) * k₁ = k₂ * k₂ from by group,
        show k₂ * (k₂⁻¹ * k₁) * k₁ = k₁ * k₁ from by group] at key
    exact key.symm
  have hsub : (⟨k₁, hk₁.1⟩ : ↥X) ^ 2 = (⟨k₂, hk₂.1⟩ : ↥X) ^ 2 := by
    apply Subtype.ext; simpa [pow_two] using hsq
  have hkeq : k₁ = k₂ := by
    have := congrArg (fun z : ↥X => (z : G)) (hsqinj hsub)
    simpa using this
  refine ⟨?_, hkeq⟩
  have hceq : c₂⁻¹ * c₁ = 1 := by rw [hu, hkeq, mul_inv_cancel]
  calc c₁ = c₂ * (c₂⁻¹ * c₁) := by group
    _ = c₂ * 1 := by rw [hceq]
    _ = c₂ := mul_one c₂

open Submission.Blueprint in theorem cardInvertedMulCardCentralizer {G : Type*} [Group G] [Finite G] {X : Subgroup G} (hodd : Odd (Nat.card X)) {t : G} (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : orderOf t = 2) : (invertedBy X t).ncard * Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card X := by
  classical
  -- `t` normalises `X`.
  have htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.mp ht x).mp hx
  -- `|X|` is odd, so squaring is a bijection of `X`.
  have hsqbij : Function.Bijective (fun x : ↥X => x ^ 2) :=
    Nat.Coprime.pow_left_bijective (Nat.coprime_two_right.mpr hodd)
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  set K : Set G := invertedBy X t with hKdef
  -- The multiplication map `(X ⊓ C_G(t)) × J(X,t) → X`.
  let φ : ↥C × ↥K → ↥X := fun p => ⟨(p.1 : G) * (p.2 : G), X.mul_mem p.1.2.1 p.2.2.1⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨c₁, k₁⟩ ⟨c₂, k₂⟩ heq
    have hval : (c₁ : G) * (k₁ : G) = (c₂ : G) * (k₂ : G) := by
      simpa [φ] using congrArg (fun z : ↥X => (z : G)) heq
    obtain ⟨hc, hk⟩ := mul_invertedBy_centralizer_injective hodd (c₁:G) (c₂:G) (k₁:G) (k₂:G)
      c₁.2.2 c₁.2.1 k₁.2 c₂.2.2 c₂.2.1 k₂.2 hval
    exact Prod.ext (Subtype.ext hc) (Subtype.ext hk)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hxX⟩
    have htx : t * x * t⁻¹ ∈ X := htX x hxX
    have hyX : (t * x * t⁻¹)⁻¹ * x ∈ X := X.mul_mem (X.inv_mem htx) hxX
    -- the unique `k ∈ X` with `k² = (t x t⁻¹)⁻¹ x`
    obtain ⟨k, hk2⟩ := hsqbij.2 (⟨(t * x * t⁻¹)⁻¹ * x, hyX⟩ : ↥X)
    have hkX : (k : G) ∈ X := k.2
    have hk2G : (k : G) * (k : G) = (t * x * t⁻¹)⁻¹ * x := by
      have h := congrArg (fun z : ↥X => (z : G)) hk2
      simpa [pow_two] using h
    have ht2m : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rw [ht2] at h; simpa [pow_two] using h
    -- `t ((t x t⁻¹)⁻¹ x) t⁻¹ = ((t x t⁻¹)⁻¹ x)⁻¹`
    have hty : t * ((t * x * t⁻¹)⁻¹ * x) * t⁻¹ = ((t * x * t⁻¹)⁻¹ * x)⁻¹ := by
      have h1 : t * (t * x * t⁻¹)⁻¹ * t⁻¹ = x⁻¹ := by
        rw [show (t * x * t⁻¹)⁻¹ = t * x⁻¹ * t⁻¹ from by group]
        rw [show t * (t * x⁻¹ * t⁻¹) * t⁻¹ = (t * t) * x⁻¹ * (t⁻¹ * t⁻¹) from by group,
            ht2m, one_mul, ← mul_inv_rev, ht2m, inv_one, mul_one]
      have hyinv : ((t * x * t⁻¹)⁻¹ * x)⁻¹ = x⁻¹ * (t * x * t⁻¹) := by
        rw [mul_inv_rev, inv_inv]
      rw [hyinv]
      rw [show t * ((t * x * t⁻¹)⁻¹ * x) * t⁻¹
            = (t * (t * x * t⁻¹)⁻¹ * t⁻¹) * (t * x * t⁻¹) from by group, h1]
    -- `k ∈ J(X,t)`: `(t k t⁻¹)² = t k² t⁻¹ = y⁻¹ = (k⁻¹)²` and squaring is injective on `X`.
    have hkc : t * (k : G) * t⁻¹ = (k : G)⁻¹ := by
      have hsq : (t * (k : G) * t⁻¹) * (t * (k : G) * t⁻¹) = (k:G)⁻¹ * (k:G)⁻¹ := by
        have e1 : (t * (k:G) * t⁻¹) * (t * (k:G) * t⁻¹) = t * ((k:G) * (k:G)) * t⁻¹ := by
          group
        rw [e1, hk2G, hty, ← hk2G, mul_inv_rev]
      have heq : (⟨t * (k:G) * t⁻¹, htX (k:G) hkX⟩ : ↥X) ^ 2
          = (⟨(k:G)⁻¹, X.inv_mem hkX⟩ : ↥X) ^ 2 := by
        apply Subtype.ext
        simpa [pow_two] using hsq
      have h2 := congrArg (fun z : ↥X => (z : G)) (hsqbij.1 heq)
      simpa using h2
    -- and `c = x k⁻¹ ∈ X ⊓ C_G(t)`
    have hc_conj : t * (x * (k:G)⁻¹) * t⁻¹ = x * (k:G)⁻¹ := by
      have e1 : t * (x * (k:G)⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * (k:G)⁻¹ * t⁻¹) := by group
      have e2 : t * (k:G)⁻¹ * t⁻¹ = (k:G) := by
        rw [show t * (k:G)⁻¹ * t⁻¹ = (t * (k:G) * t⁻¹)⁻¹ from by group, hkc, inv_inv]
      rw [e1, e2]
      refine mul_right_cancel (b := (k:G)) ?_
      rw [show (t * x * t⁻¹) * (k:G) * (k:G) = (t * x * t⁻¹) * ((k:G) * (k:G)) from by group,
          hk2G]
      rw [show (t * x * t⁻¹) * ((t * x * t⁻¹)⁻¹ * x) = x from by group]
      rw [show x * (k:G)⁻¹ * (k:G) = x from by group]
    have hcxC : x * (k:G)⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' : t * (x * (k:G)⁻¹) = (x * (k:G)⁻¹) * t := by
        calc t * (x * (k:G)⁻¹) = t * (x * (k:G)⁻¹) * t⁻¹ * t := by group
          _ = (x * (k:G)⁻¹) * t := by rw [hc_conj]
      exact h'.symm
    refine ⟨(⟨x * (k:G)⁻¹, ⟨X.mul_mem hxX (X.inv_mem hkX), hcxC⟩⟩, ⟨(k:G), hkX, hkc⟩), ?_⟩
    apply Subtype.ext
    show (x * (k:G)⁻¹) * (k:G) = x
    group
  -- A bijection `(X ⊓ C_G(t)) × J(X,t) ≃ X` gives the cardinality identity.
  have hcard : Nat.card (↥C × ↥K) = Nat.card ↥X :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
  rw [Nat.card_prod, Nat.card_coe_set_eq] at hcard
  rw [← hcard, mul_comm]

end Work.ThmF.Bender
