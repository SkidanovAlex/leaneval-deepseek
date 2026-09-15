import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi

namespace Commons.Combinatorics.Additive.AP

open Finset

/-- The `ZMod p`-linear map `y ↦ (m ↦ ∑ i, c m i * y i)` associated with a family of
linear forms `c`. -/
noncomputable def sumLinearMap {p : ℕ} {n r : ℕ} (c : Fin r → Fin n → ZMod p) :
    (Fin n → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p) :=
  LinearMap.pi (fun m =>
    ∑ i : Fin n, c m i •
      (LinearMap.proj (R := ZMod p) i : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p))

lemma sumLinearMap_apply {p : ℕ} {n r : ℕ} (c : Fin r → Fin n → ZMod p)
    (y : Fin n → ZMod p) (m : Fin r) :
    sumLinearMap c y m = ∑ i, c m i * y i := by
  simp [sumLinearMap, LinearMap.pi_apply, Finset.sum_apply, smul_eq_mul]

theorem sum_of_linear_forms {p : ℕ} [Fact p.Prime] {n r : ℕ} (hr : r ≤ n)
    (c : Fin r → Fin n → ZMod p)
    (hsurj : Function.Surjective (fun y : Fin n → ZMod p => fun m : Fin r => ∑ i, c m i * y i))
    (g : (Fin r → ZMod p) → ℝ) :
    (∑ y : Fin n → ZMod p, g (fun m => ∑ i, c m i * y i))
      = (p : ℝ) ^ (n - r) * ∑ z : Fin r → ZMod p, g z := by
  classical
  set φ : (Fin n → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p) := sumLinearMap c with hφ
  have hφ_apply : ∀ y m, φ y m = ∑ i, c m i * y i := by
    intro y m; rw [hφ]; exact sumLinearMap_apply c y m
  have hφfun : (fun y : Fin n → ZMod p => fun m : Fin r => ∑ i, c m i * y i) = φ := by
    funext y m; exact (hφ_apply y m).symm
  have hsurj' : Function.Surjective φ := hφfun ▸ hsurj
  -- a (set-theoretic) section of `φ`
  let ψ : (Fin r → ZMod p) → (Fin n → ZMod p) := Function.surjInv hsurj'
  have hψ : ∀ z, φ (ψ z) = z := Function.surjInv_eq hsurj'
  -- the kernel
  let K : Submodule (ZMod p) (Fin n → ZMod p) := φ.ker
  -- the bijection `K × codomain ≃ domain`, `(k, z) ↦ k + ψ z`
  let F : K × (Fin r → ZMod p) → (Fin n → ZMod p) :=
    fun x => (x.1 : Fin n → ZMod p) + ψ x.2
  have hFφ : ∀ x, φ (F x) = x.2 := by
    rintro ⟨k, z⟩
    have hk : φ (k : Fin n → ZMod p) = 0 := (LinearMap.mem_ker).1 k.2
    show φ ((k : Fin n → ZMod p) + ψ z) = z
    rw [map_add, hk, zero_add, hψ z]
  have hF_inj : Function.Injective F := by
    intro x y hxy
    have h2 : x.2 = y.2 := by rw [← hFφ x, hxy, hFφ y]
    obtain ⟨k1, z1⟩ := x
    obtain ⟨k2, z2⟩ := y
    simp only at h2
    subst h2
    simp only [F] at hxy
    have h1 : k1 = k2 := by
      have := add_right_cancel hxy
      exact Subtype.ext (by simpa using this)
    subst h1
    rfl
  have hF_surj : Function.Surjective F := by
    intro y
    refine ⟨(⟨y - ψ (φ y), (LinearMap.mem_ker).2 ?_⟩, φ y), ?_⟩
    · rw [map_sub, hψ (φ y), sub_self]
    · simp only [F]
      exact sub_add_cancel y (ψ (φ y))
  let E : K × (Fin r → ZMod p) ≃ (Fin n → ZMod p) := Equiv.ofBijective F ⟨hF_inj, hF_surj⟩
  have hE : ∀ x, E x = F x := fun _ => rfl
  -- the cardinality of the kernel
  have hcard : Fintype.card K = p ^ (n - r) := by
    have hprod : Fintype.card K * Fintype.card (Fin r → ZMod p)
        = Fintype.card (Fin n → ZMod p) := by
      have h := Fintype.card_congr E
      rwa [Fintype.card_prod] at h
    have hcod : Fintype.card (Fin r → ZMod p) = p ^ r := by
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    have hdom : Fintype.card (Fin n → ZMod p) = p ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [hcod, hdom] at hprod
    have hpr : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
    refine Nat.mul_right_cancel hpr ?_
    rw [← pow_add, Nat.sub_add_cancel hr]
    exact hprod
  -- the reindexing
  have key : (∑ y : Fin n → ZMod p, g (φ y))
      = Fintype.card K • (∑ z : Fin r → ZMod p, g z) := by
    have h1 : (∑ y : Fin n → ZMod p, g (φ y))
        = ∑ x : K × (Fin r → ZMod p), g x.2 :=
      (Fintype.sum_equiv E (fun x : K × (Fin r → ZMod p) => g x.2)
        (fun y : Fin n → ZMod p => g (φ y)) (fun x => by rw [hE x, hFφ x])).symm
    rw [h1, Fintype.sum_prod_type]
    have hconst : ∀ x : K, (∑ y : Fin r → ZMod p, g (x, y).2) = ∑ z : Fin r → ZMod p, g z :=
      fun x => Finset.sum_congr rfl (fun y _ => rfl)
    rw [Finset.sum_congr rfl (fun x _ => hconst x), Finset.sum_const, Finset.card_univ]
  calc (∑ y : Fin n → ZMod p, g (fun m => ∑ i, c m i * y i))
      = ∑ y : Fin n → ZMod p, g (φ y) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [show (fun m : Fin r => ∑ i, c m i * y i) = φ y from
          funext (fun m => (hφ_apply y m).symm)]
    _ = Fintype.card K • (∑ z : Fin r → ZMod p, g z) := key
    _ = (p : ℝ) ^ (n - r) * ∑ z : Fin r → ZMod p, g z := by
        rw [nsmul_eq_mul, hcard, Nat.cast_pow]

end Commons.Combinatorics.Additive.AP