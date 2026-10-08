import Mathlib
import Submission.Work.Frobenius.Complement.exists_fixed_of_isFpf_module

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A fixed point of `x` on a fixed-point-free elementary abelian `2`-group

Let `N` be a finite elementary abelian `2`-group with a group `A` of automorphisms, and let
`y, x ∈ A` have odd prime orders `q, p` with `x * y * x⁻¹ = y ^ s` and `s % q ≠ 1`.
If `y` acts fixed-point-freely on `N`, then `x` has a nontrivial fixed point.

The proof views `N` as an `𝔽₂`-vector space (`Additive N`), turns the `A`-action into an
`𝔽₂`-linear representation and invokes
`Work.Frobenius.Complement.exists_fixed_of_isFpf_module`.
-/

set_option linter.style.haveILetI false

namespace Work.PSU3.StageA

open scoped IsMulCommutative
open Additive

theorem exists_fixed_of_fpf_elementaryAbelian {A : Type*} [Group A] {N : Type*} [Group N]
    [Finite N] [Nontrivial N] [MulDistribMulAction A N] {p q s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : (p : ZMod 2) ≠ 0) (hq2 : (q : ZMod 2) ≠ 0) (hs : s % q ≠ 1)
    (hNexp : ∀ n : N, n * n = 1) (hNcomm : ∀ a b : N, a * b = b * a)
    {y x : A} (hy : orderOf y = q) (hx : orderOf x = p) (hrel : x * y * x⁻¹ = y ^ s)
    (hfpf : ∀ n : N, y • n = n → n = 1) :
    ∃ n : N, n ≠ 1 ∧ x • n = n := by
  classical
  -- `N` is commutative of exponent `2`, hence `Additive N` is an `𝔽₂`-vector space.
  haveI : IsMulCommutative N := ⟨⟨hNcomm⟩⟩
  have h2zero : ∀ v : Additive N, 2 • v = 0 := by
    intro v
    obtain ⟨n, rfl⟩ : ∃ n : N, Additive.ofMul n = v := ⟨Additive.toMul v, rfl⟩
    calc 2 • (Additive.ofMul n) = Additive.ofMul n + Additive.ofMul n := two_nsmul _
      _ = Additive.ofMul (n * n) := ofMul_mul n n
      _ = 0 := by rw [hNexp n]; rfl
  letI : Module (ZMod 2) (Additive N) := AddCommGroup.zmodModule (n := 2) h2zero
  haveI : Module.Finite (ZMod 2) (Additive N) := Module.Finite.of_finite
  -- The action of `A` as `𝔽₂`-linear maps.
  let g : A → Additive N →+ Additive N := fun a =>
    { toFun := fun v => Additive.ofMul (a • v.toMul)
      map_zero' := by apply Additive.ext; simp
      map_add' := fun u v => by
        apply Additive.ext
        simp only [toMul_add, toMul_ofMul, smul_mul'] }
  let ρ : A →* (Additive N →ₗ[ZMod 2] Additive N) :=
    { toFun := fun a => (g a).toZModLinearMap 2
      map_one' := by
        apply LinearMap.ext; intro v; apply Additive.ext; simp [g]
      map_mul' := by
        intro a b; apply LinearMap.ext; intro v; apply Additive.ext
        simp [g, mul_smul] }
  let T : Additive N →ₗ[ZMod 2] Additive N := ρ y
  let X : Additive N →ₗ[ZMod 2] Additive N := ρ x
  have hyq : y ^ q = 1 := by have h := pow_orderOf_eq_one y; rwa [hy] at h
  have hxp : x ^ p = 1 := by have h := pow_orderOf_eq_one x; rwa [hx] at h
  have hTq : T ^ q = 1 := by rw [show T = ρ y from rfl, ← map_pow, hyq, map_one]
  have hXp : X ^ p = 1 := by rw [show X = ρ x from rfl, ← map_pow, hxp, map_one]
  -- `T` is fixed-point-free, transported from `y` acting fixed-point-freely on `N`.
  have hT1 : ∀ v, T v = v → v = 0 := by
    intro v hv
    have hv' : g y v = v := hv
    have h2 : y • v.toMul = v.toMul := by
      have := congrArg Additive.toMul hv'
      simpa [g] using this
    have h3 : v.toMul = 1 := hfpf v.toMul h2
    rw [← ofMul_toMul v, h3, ofMul_one]
  -- The conjugation relation, transported to the linear maps.
  have hxy : x * y = y ^ s * x := by
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y ^ s * x := by rw [hrel]
  have hTrel : X * T = T ^ s * X := by
    have h3 : ρ (x * y) = ρ (y ^ s * x) := by rw [hxy]
    simp only [map_mul, map_pow] at h3
    simpa [X, T] using h3
  have hrel' : ∀ v, X (T v) = (T ^ s) (X v) := by
    intro v
    have : (X * T) v = (T ^ s * X) v := by rw [hTrel]
    simpa [Module.End.mul_apply] using this
  -- Apply the `p`-`q` lemma for fixed-point-free modules.
  obtain ⟨w, hw_ne, hw_fix⟩ :=
    Work.Frobenius.Complement.exists_fixed_of_isFpf_module (F := ZMod 2) (W := Additive N)
      hp hq hp2 hq2 hs hTq hT1 hXp hrel'
  refine ⟨w.toMul, ?_, ?_⟩
  · intro h
    exact hw_ne (by rw [← ofMul_toMul w, h, ofMul_one])
  · have h' : g x w = w := hw_fix
    have := congrArg Additive.toMul h'
    simpa [g] using this

end Work.PSU3.StageA
