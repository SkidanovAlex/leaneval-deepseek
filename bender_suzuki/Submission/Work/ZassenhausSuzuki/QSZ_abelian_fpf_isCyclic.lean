import Mathlib
import Submission.Work.Coprime.Basic
import Submission.Work.Frobenius.Complement.abelian_fpf_representation_isCyclic
import Submission.Work.Frobenius.Complement.exists_invariant_elementaryAbelian_of_solvable_action
import Submission.Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An abelian fixed-point-free group of automorphisms is cyclic

Let `A` be a finite abelian group acting on a nontrivial finite group `N` in such a way that every
element `a ≠ 1` has `1` as its only fixed point.  Then `A` is cyclic.

This is Burnside's theorem on abelian fixed-point-free automorphism groups (a Frobenius complement
that is abelian is cyclic).

## Proof

* The action is *coprime*: no prime `p` divides both `|A|` and `|N|`.  Otherwise an element
  `a₀ ∈ A` of order `p` spans a `p`-group `⟨a₀⟩` acting on `N`; a group of order `p` acting on a
  finite set whose cardinality is divisible by `p` has a non-trivial fixed point (orbit counting),
  contradicting fixed-point-freeness of `a₀`.
* An abelian group is solvable, so this coprime action leaves invariant a nontrivial elementary
  abelian subgroup `W ≤ N` (`exists_invariant_elementaryAbelian_of_solvable_action`).
* `W` is a nontrivial finite-dimensional module over `𝔽_r` on which `A` acts fixed-point-freely,
  and `abelian_fpf_representation_isCyclic` says such an `A` is cyclic.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped IsMulCommutative Pointwise
open Additive

namespace Work.ZassenhausSuzuki

/-- A finite commutative group acting fixed-point-freely on a nontrivial finite commutative group
of exponent a prime `r` is cyclic.

`W` becomes a nontrivial finite-dimensional vector space over `𝔽_r` carrying a fixed-point-free
representation of `A`, and `abelian_fpf_representation_isCyclic` applies. -/
private theorem isCyclic_of_fpf_action_on_elementaryAbelian {r : ℕ} (hr : r.Prime)
    {A W : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group W] [Finite W] [IsMulCommutative W] [Nontrivial W]
    [MulDistribMulAction A W] (hexp : ∀ w : W, w ^ r = 1)
    (hfp : ∀ a : A, a ≠ 1 → ∀ w : W, a • w = w → w = 1) : IsCyclic A := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr0 : ∀ x : Additive W, r • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]
  haveI : Module (ZMod r) (Additive W) := AddCommGroup.zmodModule hr0
  haveI : Module.Finite (ZMod r) (Additive W) := Module.Finite.of_finite
  haveI : Nontrivial (Additive W) := inferInstance
  let f : A → (Additive W →+ Additive W) := fun a =>
    { toFun := fun x => Additive.ofMul (a • x.toMul)
      map_zero' := by apply Additive.ext; simp
      map_add' := fun x y => by
        apply Additive.ext
        simp [toMul_add, smul_mul', ofMul_mul] }
  let ρ : Representation (ZMod r) A (Additive W) :=
    { toFun := fun a => (f a).toZModLinearMap r
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Additive.ext
        simp [f]
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro x
        apply Additive.ext
        simp [f, mul_smul] }
  have hff : ∀ a : A, a ≠ 1 → ∀ w : Additive W, ρ a w = w → w = 0 := fun a ha w hw => by
    have h1 : f a w = w := hw
    have h2 : a • w.toMul = w.toMul := by
      have := congrArg Additive.toMul h1
      simpa [f] using this
    have h3 := hfp a ha w.toMul h2
    apply Additive.ext
    simp [h3]
  exact Work.Frobenius.Complement.abelian_fpf_representation_isCyclic ρ inferInstance hff

theorem QSZ_abelian_fpf_isCyclic {A N : Type} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [Nontrivial N] (ρ : A →* MulAut N)
    (hfpf : ∀ a : A, a ≠ 1 → ∀ n : N, ρ a n = n → n = 1) : IsCyclic A := by
  classical
  -- turn `ρ` into a multiplicative action of `A` on `N`
  let f : A → N → N := fun a n => ρ a n
  have hf1 : ∀ n : N, f 1 n = n := fun n => by
    show ρ 1 n = n
    rw [map_one]
    rfl
  have hf2 : ∀ a b : A, ∀ n : N, f (a * b) n = f a (f b n) := fun a b n => by
    show ρ (a * b) n = ρ a (ρ b n)
    rw [map_mul]
    rfl
  have hf3 : ∀ a : A, f a 1 = 1 := fun a => by
    show ρ a 1 = 1
    rw [map_one]
  have hf4 : ∀ a : A, ∀ m n : N, f a (m * n) = f a m * f a n := fun a m n => by
    show ρ a (m * n) = ρ a m * ρ a n
    rw [map_mul]
  letI : MulDistribMulAction A N :=
    { smul := f, one_smul := hf1, mul_smul := hf2, smul_one := hf3, smul_mul := hf4 }
  have hf_eq : ∀ (a : A) (n : N), a • n = f a n := fun a n => rfl
  have hfpf' : ∀ a : A, a ≠ 1 → ∀ n : N, a • n = n → n = 1 := fun a ha n hn => by
    rw [hf_eq a n] at hn
    exact hfpf a ha n hn
  -- The action is coprime: no prime divides both `|A|` and `|N|`.
  have hcop : (Nat.card A).Coprime (Nat.card N) := by
    by_contra h
    rw [Nat.Prime.not_coprime_iff_dvd] at h
    obtain ⟨p, hp, hpA, hpN⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨a0, ha0⟩ := exists_prime_orderOf_dvd_card' p hpA
    have ha0ne : a0 ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ha0
      exact hp.ne_one ha0.symm
    let H : Subgroup A := Subgroup.zpowers a0
    have hHcard : Nat.card H = p := by rw [Nat.card_zpowers, ha0]
    haveI hHp : IsPGroup p ↥H := IsPGroup.of_card (by rw [hHcard, pow_one])
    have h1fix : (1 : N) ∈ MulAction.fixedPoints ↥H N := by
      rw [MulAction.mem_fixedPoints]
      intro h
      exact smul_one h
    obtain ⟨b, hbfix, hbne⟩ :=
      IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (p := p) hHp N hpN h1fix
    have hbfix_a0 : a0 • b = b := by
      have h := (MulAction.mem_fixedPoints.mp hbfix) (⟨a0, Subgroup.mem_zpowers a0⟩ : ↥H)
      simpa using h
    exact hbne (hfpf' a0 ha0ne b hbfix_a0).symm
  -- An abelian group is solvable, so the coprime action fixes a nontrivial elementary abelian
  -- subgroup of `N`.
  have hsol : Group.IsSolvable A :=
    Group.isSolvable_of_comm
      (fun a b => isMulCommutative_iff.mp (inferInstance : IsMulCommutative A) a b)
  obtain ⟨r, hr, W, hWne, hWinv, hWcomm, hWexp⟩ :=
    Work.Frobenius.Complement.exists_invariant_elementaryAbelian_of_solvable_action
      (A := A) (N := N) hsol hcop
  haveI hWinvI : FT.IsInvariant A W := ⟨fun a => Subgroup.ext fun x => by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact (hWinv a⁻¹ x).symm⟩
  haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hWne
  haveI : IsMulCommutative ↥W := hWcomm
  refine isCyclic_of_fpf_action_on_elementaryAbelian hr hWexp (fun a ha w hw => ?_)
  have h2 : a • (w : N) = (w : N) := by
    have h3 := congrArg Subtype.val hw
    rwa [FT.coe_subgroup_smul] at h3
  exact Subtype.ext (hfpf' a ha (w : N) h2)

end Work.ZassenhausSuzuki
