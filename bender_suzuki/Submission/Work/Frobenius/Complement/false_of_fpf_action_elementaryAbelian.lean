import Mathlib
import Submission.Work.Coprime.Basic
import Submission.Work.Frobenius.Complement.fpf_module_pq_contradiction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped IsMulCommutative Pointwise
open Additive

namespace Work.Frobenius.Complement

theorem false_of_fpf_action_elementaryAbelian {A N : Type*} [Group A] [Group N] [Finite N] [Nontrivial N]
    [MulDistribMulAction A N] {r p q : ℕ} (hr : r.Prime) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpr : (p : ZMod r) ≠ 0) (hqr : (q : ZMod r) ≠ 0)
    (W : Subgroup N) (hWne : W ≠ ⊥) (hWinv : ∀ a : A, ∀ x : N, x ∈ W ↔ a • x ∈ W)
    (hWcomm : IsMulCommutative ↥W) (hWexp : ∀ w : ↥W, w ^ r = 1)
    (hfpf : ∀ a : A, a ≠ 1 → ∀ n : N, a • n = n → n = 1)
    {s : ℕ} {y x : A} (hy : orderOf y = q) (hx : orderOf x = p) (hs : s % q ≠ 1)
    (hrel : x * y * x⁻¹ = y ^ s) : False := by
  classical
  haveI : IsMulCommutative ↥W := hWcomm
  haveI : Nontrivial ↥W := W.nontrivial_iff_ne_bot.mpr hWne
  -- `W` is `A`-invariant
  have hpt : ∀ a : A, a • W = W := fun a => by
    refine Subgroup.ext fun z => ?_
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact (hWinv a⁻¹ z).symm
  haveI : FT.IsInvariant A W := ⟨hpt⟩
  -- vector space structure over `ZMod r`
  haveI : Fact r.Prime := ⟨hr⟩
  have hr0 : ∀ v : Additive ↥W, r • v = 0 := fun v => by
    rw [← ofMul_toMul v, ← ofMul_pow, hWexp, ofMul_one]
  haveI : Module (ZMod r) (Additive ↥W) := AddCommGroup.zmodModule hr0
  haveI : Module.Finite (ZMod r) (Additive ↥W) := Module.Finite.of_finite
  haveI : Nontrivial (Additive ↥W) := inferInstance
  -- the additive automorphism induced by the action
  let g : A → (Additive ↥W →+ Additive ↥W) := fun a =>
    { toFun := fun v => Additive.ofMul (a • v.toMul)
      map_zero' := by apply Additive.ext; simp
      map_add' := fun u v => by
        apply Additive.ext
        simp [toMul_add, smul_mul', ofMul_mul] }
  -- the linear representation
  let ρ : A →* (Additive ↥W →ₗ[ZMod r] Additive ↥W) :=
    { toFun := fun a => (g a).toZModLinearMap r
      map_one' := by
        apply LinearMap.ext
        intro v
        apply Additive.ext
        simp [g]
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro v
        apply Additive.ext
        simp [g, mul_smul] }
  let T : Additive ↥W →ₗ[ZMod r] Additive ↥W := ρ y
  let X : Additive ↥W →ₗ[ZMod r] Additive ↥W := ρ x
  have hy_ne : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact hq.ne_one hy.symm
  have hx_ne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hTq : T ^ q = 1 := by
    have hyq : y ^ q = 1 := by
      have h := pow_orderOf_eq_one y
      rwa [hy] at h
    rw [← map_pow, hyq, map_one]
  have hXp : X ^ p = 1 := by
    have hxp : x ^ p = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    rw [← map_pow, hxp, map_one]
  have hT1 : ∀ v, T v = v → v = 0 := by
    intro v hv
    have hv' : g y v = v := hv
    have h2 : y • v.toMul = v.toMul := by
      have := congrArg Additive.toMul hv'
      simpa [g] using this
    have h2N : y • ((v.toMul : ↥W) : N) = ((v.toMul : ↥W) : N) := by
      have := congrArg Subtype.val h2
      rwa [FT.coe_subgroup_smul] at this
    have h3N : ((v.toMul : ↥W) : N) = 1 := hfpf y hy_ne ((v.toMul : ↥W) : N) h2N
    have h3 : v.toMul = 1 := Subtype.ext h3N
    rw [← ofMul_toMul v, h3, ofMul_one]
  have hX1 : ∀ v, X v = v → v = 0 := by
    intro v hv
    have hv' : g x v = v := hv
    have h2 : x • v.toMul = v.toMul := by
      have := congrArg Additive.toMul hv'
      simpa [g] using this
    have h2N : x • ((v.toMul : ↥W) : N) = ((v.toMul : ↥W) : N) := by
      have := congrArg Subtype.val h2
      rwa [FT.coe_subgroup_smul] at this
    have h3N : ((v.toMul : ↥W) : N) = 1 := hfpf x hx_ne ((v.toMul : ↥W) : N) h2N
    have h3 : v.toMul = 1 := Subtype.ext h3N
    rw [← ofMul_toMul v, h3, ofMul_one]
  have hTrel : X * T = T ^ s * X := by
    have hxy : x * y = y ^ s * x := by
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y ^ s * x := by rw [hrel]
    have h3 : ρ (x * y) = ρ (y ^ s * x) := by rw [hxy]
    simp only [map_mul, map_pow] at h3
    simpa [X, T] using h3
  have hrel' : ∀ v, X (T v) = (T ^ s) (X v) := by
    intro v
    have : (X * T) v = (T ^ s * X) v := by rw [hTrel]
    simpa [Module.End.mul_apply] using this
  exact fpf_module_pq_contradiction hp hq hpq hpr hqr hs hTq hT1 hXp hX1 hrel'

end Work.Frobenius.Complement
