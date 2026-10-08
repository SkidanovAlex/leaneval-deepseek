import Mathlib
import Submission.Work.Coprime.Basic
import Submission.Work.Frobenius.Complement.abelian_fpf_representation_isCyclic
import Submission.Work.Frobenius.Complement.exists_invariant_elementaryAbelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A finite abelian `p`-group acting fixed-point-freely is cyclic

Let `A` be a finite abelian `p`-group acting on a nontrivial finite group `N` in such a way
that every `a ≠ 1` has only the identity as fixed point.  Then `A` is cyclic.

This is the statement that an abelian Frobenius complement is cyclic, in the form needed for
the Feit--Thompson development.

The proof reduces the fixed-point-free action on `N` to a fixed-point-free linear action of `A`
on a nonzero vector space: by the coprime action argument there is a nontrivial `A`-invariant
elementary abelian `q`-subgroup `H ≤ N` for some prime `q`, and `H` carries the structure of an
`𝔽_q[A]`-module.  The linear statement — a finite commutative group acting fixed-point-freely
and linearly on a nontrivial finite dimensional vector space is cyclic — is proved in
`Work.Frobenius.Complement.abelian_fpf_representation_isCyclic`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.Frobenius.Complement

open scoped IsMulCommutative Pointwise

/-- A finite commutative group that acts fixed-point-freely on a nontrivial finite commutative
group of exponent a prime `q` is cyclic. -/
private theorem isCyclic_of_fpf_action_on_elementaryAbelian {q : ℕ} (hq : q.Prime)
    {A H : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group H] [Finite H] [IsMulCommutative H] [Nontrivial H]
    [MulDistribMulAction A H] (hexp : ∀ h : H, h ^ q = 1)
    (hfp : ∀ a : A, a ≠ 1 → ∀ h : H, a • h = h → h = 1) : IsCyclic A := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : ∀ x : Additive H, q • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]
  haveI : Module (ZMod q) (Additive H) := AddCommGroup.zmodModule hq0
  haveI : Module.Finite (ZMod q) (Additive H) := Module.Finite.of_finite
  haveI : Nontrivial (Additive H) := inferInstance
  let g : A → (Additive H →+ Additive H) := fun a =>
    { toFun := fun x => Additive.ofMul (a • x.toMul)
      map_zero' := by apply Additive.ext; simp
      map_add' := fun x y => by
        apply Additive.ext
        simp [toMul_add, smul_mul', ofMul_mul] }
  let ρ : Representation (ZMod q) A (Additive H) :=
    { toFun := fun a => (g a).toZModLinearMap q
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Additive.ext
        simp [g]
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro x
        apply Additive.ext
        simp [g, mul_smul] }
  have hff : ∀ a : A, a ≠ 1 → ∀ w : Additive H, ρ a w = w → w = 0 := fun a ha w hw => by
    have h1 : g a w = w := hw
    have h2 : a • w.toMul = w.toMul := by
      have := congrArg Additive.toMul h1
      simpa [g] using this
    have h3 := hfp a ha w.toMul h2
    apply Additive.ext
    simp [h3]
  exact abelian_fpf_representation_isCyclic ρ inferInstance hff

/-- The main reduction: if a function `f : A → N → N` makes `N` a fixed-point-free
`A`-group, with `A` a finite commutative `p`-group and `N` a nontrivial finite group, then
`A` is cyclic. -/
private theorem isCyclic_of_fpf_action {p : ℕ} (hp : p.Prime)
    {A N : Type*} [Group A] [Finite A] (hAp : IsPGroup p A) [IsMulCommutative A]
    [Group N] [Finite N] [Nontrivial N]
    (f : A → N → N) (hf1 : ∀ n : N, f 1 n = n) (hf2 : ∀ a b : A, ∀ n : N, f (a * b) n = f a (f b n))
    (hf3 : ∀ a : A, f a 1 = 1) (hf4 : ∀ a : A, ∀ m n : N, f a (m * n) = f a m * f a n)
    (hfp : ∀ a : A, a ≠ 1 → ∀ n : N, f a n = n → n = 1) : IsCyclic A := by
  classical
  letI hid : MulDistribMulAction A N :=
  { smul := f, one_smul := hf1, mul_smul := hf2, smul_one := hf3, smul_mul := hf4 }
  have hf_eq : ∀ (a : A) (n : N), a • n = f a n := fun a n => rfl
  have hfpsmul : ∀ a : A, a ≠ 1 → ∀ n : N, a • n = n → n = 1 := fun a ha n hn => by
    rw [hf_eq a n] at hn
    exact hfp a ha n hn
  by_cases hsub : Subsingleton A
  · refine ⟨1, fun a => ⟨0, ?_⟩⟩
    show (1 : A) ^ (0 : ℤ) = a
    rw [zpow_zero]
    exact (Subsingleton.elim a 1).symm
  · haveI hntA : Nontrivial A := not_subsingleton_iff_nontrivial.mp hsub
    have hpN : ¬ p ∣ Nat.card N := by
      intro hdiv
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a0, ha0⟩ := exists_ne (1 : A)
      have h1fix : (1 : N) ∈ MulAction.fixedPoints A N := by
        rw [MulAction.mem_fixedPoints]
        intro a
        rw [hf_eq a 1]
        exact hf3 a
      obtain ⟨b, hbfix, hbne⟩ :=
        hAp.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdiv h1fix
      have hb1 : b = 1 := hfpsmul a0 ha0 b ((MulAction.mem_fixedPoints.mp hbfix) a0)
      exact hbne hb1.symm
    obtain ⟨q, hq, H, hHne, hHinv, hHcomm, hHexp⟩ :=
      exists_invariant_elementaryAbelian hp hAp hpN
    haveI : Nontrivial ↥H := H.nontrivial_iff_ne_bot.mpr hHne
    haveI : IsMulCommutative ↥H := hHcomm
    have hpt : ∀ a : A, a • H = H := fun a => by
      refine Subgroup.ext fun x => ?_
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hf_eq]
      exact hHinv a⁻¹ x
    haveI : FT.IsInvariant A H := ⟨hpt⟩
    have hfp' : ∀ a : A, a ≠ 1 → ∀ h : ↥H, a • h = h → h = 1 := fun a ha h hh => by
      apply Subtype.ext
      have key : a • (h : N) = (h : N) := by
        have h2 := congrArg Subtype.val hh
        rwa [FT.coe_subgroup_smul] at h2
      simpa using hfpsmul a ha (h : N) key
    exact isCyclic_of_fpf_action_on_elementaryAbelian hq hHexp hfp'

theorem isPGroup_abelian_fpf_isCyclic {p : ℕ} (hp : p.Prime) {A : Type*} [Group A] [Finite A]
    (hAp : IsPGroup p A) [IsMulCommutative A] {N : Type*} [Group N] [Finite N] [Nontrivial N]
    (ρ : A →* MulAut N) (hfp : ∀ a : A, a ≠ 1 → ∀ n : N, ρ a n = n → n = 1) :
    IsCyclic A := by
  classical
  refine isCyclic_of_fpf_action hp hAp (fun a n => ρ a n) ?_ ?_ ?_ ?_ ?_
  · intro n
    show ρ 1 n = n
    rw [map_one]
    rfl
  · intro a b n
    show ρ (a * b) n = ρ a (ρ b n)
    rw [map_mul]
    rfl
  · intro a
    show ρ a 1 = 1
    rw [map_one]
  · intro a m n
    show ρ a (m * n) = ρ a m * ρ a n
    rw [map_mul]
  · intro a ha n hn
    exact hfp a ha n hn

end Work.Frobenius.Complement
