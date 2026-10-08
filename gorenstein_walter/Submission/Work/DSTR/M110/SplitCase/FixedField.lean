/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The fixed field of an automorphism of `GF(p^k)` of prime order `r`

`card_fixed_of_orderOf_eq`: if `γ` is a ring automorphism of `GaloisField p k` with
`orderOf γ = r` (`r` prime), then the fixed field of `γ` has `p ^ (k / r)` elements.

Proof: `γ` fixes the prime field `ZMod p`, so it is a `ZMod p`-algebra automorphism `γA`.
The subgroup `⟨γA⟩` has order `r`, so by `IntermediateField.finrank_fixedField_eq_card` the
fixed field has `ZMod p`-codimension `r` in `GF(p^k)`: `k = m * r` with `m` the `ZMod p`-dimension
of the fixed field.  A finite field of dimension `m` over `ZMod p` has `p ^ m = p ^ (k / r)`
elements.
-/
import Mathlib

namespace Work.DSTR.M110.SplitCase

open IntermediateField

/-- The fixed field of a ring automorphism of `GF(p^k)` of prime order `r` has `p ^ (k / r)`
elements. -/
theorem card_fixed_of_orderOf_eq (p k r : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hr : r.Prime)
    (γ : GaloisField p k ≃+* GaloisField p k) (hγ : orderOf γ = r) :
    Nat.card {a : GaloisField p k // γ a = a} = p ^ (k / r) := by
  haveI : CharP (GaloisField p k) p := inferInstance
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI : Fact r.Prime := ⟨hr⟩
  -- `γ` fixes the prime field
  have hf : ∀ x : ZMod p, γ (algebraMap (ZMod p) (GaloisField p k) x) =
      algebraMap (ZMod p) (GaloisField p k) x := by
    intro x
    have hx : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
    rw [show algebraMap (ZMod p) (GaloisField p k) x =
        ((x.val : ℕ) : GaloisField p k) from by
      conv_lhs => rw [← hx]
      exact map_natCast (algebraMap (ZMod p) (GaloisField p k)) x.val]
    exact map_natCast γ x.val
  let γA : GaloisField p k ≃ₐ[ZMod p] GaloisField p k :=
    AlgEquiv.ofRingEquiv (f := γ) hf
  have hcoe : ∀ x : GaloisField p k, γA x = γ x := fun x => rfl
  -- iteration of a `RingEquiv` power
  have hiter : ∀ (e : GaloisField p k ≃+* GaloisField p k) (x : GaloisField p k) (n : ℕ),
      (e ^ n) x = (⇑e)^[n] x := by
    intro e x n
    induction n with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ']
        show e ((e ^ m) x) = (⇑e)^[m + 1] x
        rw [ih, Function.iterate_succ_apply']
  -- order of `γA`
  have hpowA : γA ^ r = 1 := by
    apply AlgEquiv.ext
    intro x
    rw [AlgEquiv.coe_pow]
    have hfun : (⇑γA : GaloisField p k → GaloisField p k) = ⇑γ := funext hcoe
    rw [hfun, ← hiter γ x r, ← hγ, pow_orderOf_eq_one γ]
    rfl
  have hneA : γA ≠ 1 := by
    intro h
    have h1 : γ = 1 := by
      ext x
      have hxx := congrFun (congrArg DFunLike.coe h) x
      rw [← hcoe x]
      exact hxx
    rw [h1, orderOf_one] at hγ
    have := hr.one_lt
    omega
  have horderA : orderOf γA = r := orderOf_eq_prime hpowA hneA
  let H : Subgroup (GaloisField p k ≃ₐ[ZMod p] GaloisField p k) := Subgroup.zpowers γA
  haveI : FiniteDimensional (ZMod p) (GaloisField p k) := Module.Finite.of_finite
  -- the fixed field has `ZMod p`-codimension `r`
  have hcodim : Module.finrank (↥(fixedField H)) (GaloisField p k) = r := by
    rw [finrank_fixedField_eq_card H]
    show Nat.card ↥(Subgroup.zpowers γA) = r
    rw [Nat.card_zpowers, horderA]
  -- `finrank (ZMod p) (GaloisField p k) = k`
  have hZp : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hFk : Module.finrank (ZMod p) (GaloisField p k) = k := by
    haveI : NeZero (Nat.card (ZMod p)) := ⟨Nat.card_pos.ne'⟩
    have h1 : Nat.card (GaloisField p k)
        = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (GaloisField p k) :=
      Module.natCard_eq_pow_finrank
    rw [GaloisField.card p k hk, hZp] at h1
    exact (Nat.pow_right_injective (by have := (Fact.out : p.Prime).one_lt; omega) h1).symm
  -- tower: `k = m * r`
  have htower : k = Module.finrank (ZMod p) (↥(fixedField H)) * r := by
    calc k = Module.finrank (ZMod p) (GaloisField p k) := hFk.symm
      _ = Module.finrank (ZMod p) (↥(fixedField H)) * r := by
            rw [← Module.finrank_mul_finrank (ZMod p) (↥(fixedField H)) (GaloisField p k), hcodim]
  have hkr : k / r = Module.finrank (ZMod p) (↥(fixedField H)) :=
    (Nat.eq_div_of_mul_eq_right hr.ne_zero (Nat.mul_comm r _ ▸ htower.symm)).symm
  haveI : Finite ↥(fixedField H) := inferInstance
  have hcardfix : Nat.card (↥(fixedField H)) = p ^ (k / r) := by
    have h2 : Nat.card (↥(fixedField H))
        = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (↥(fixedField H)) :=
      Module.natCard_eq_pow_finrank
    rw [h2, hkr, hZp]
  rw [← hcardfix]
  apply Nat.card_congr
  refine
    { toFun := fun a => ⟨a.1, ?_⟩
      invFun := fun a => ⟨a.1, ?_⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  · rw [mem_fixedField_iff]
    intro f hf'
    have hγmem : γA ∈ Subgroup.zpowers γA := Subgroup.mem_zpowers γA
    have hγa : γA a.1 = a.1 := by rw [hcoe a.1]; exact a.2
    let S : Subgroup (GaloisField p k ≃ₐ[ZMod p] GaloisField p k) :=
      { carrier := {g | g a.1 = a.1}
        mul_mem' := by
          intro g h hg hh
          show (g * h) a.1 = a.1
          rw [AlgEquiv.mul_apply, hh, hg]
        one_mem' := AlgEquiv.one_apply a.1
        inv_mem' := by
          intro g hg
          have h1 : (g⁻¹ : GaloisField p k ≃ₐ[ZMod p] GaloisField p k) = g.symm := rfl
          rw [h1]
          have h2 : g.symm (g a.1) = g.symm a.1 := congrArg g.symm hg
          rw [AlgEquiv.symm_apply_apply] at h2
          exact h2.symm }
    exact (Subgroup.zpowers_le (g := γA) (H := S)).mpr hγa hf'
  · have hfix' : γA a.1 = a.1 := (mem_fixedField_iff H a.1).mp a.2 γA (Subgroup.mem_zpowers γA)
    rw [← hcoe a.1]
    exact hfix'

/-- Key step of the two preceding results, exposed for reuse. -/
private theorem setup_finrank (p k r : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hr : r.Prime)
    (γ : GaloisField p k ≃+* GaloisField p k) (hγ : orderOf γ = r) :
    ∃ m : ℕ, k = m * r := by
  haveI : CharP (GaloisField p k) p := inferInstance
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI : Fact r.Prime := ⟨hr⟩
  have hf : ∀ x : ZMod p, γ (algebraMap (ZMod p) (GaloisField p k) x) =
      algebraMap (ZMod p) (GaloisField p k) x := by
    intro x
    have hx : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
    rw [show algebraMap (ZMod p) (GaloisField p k) x =
        ((x.val : ℕ) : GaloisField p k) from by
      conv_lhs => rw [← hx]
      exact map_natCast (algebraMap (ZMod p) (GaloisField p k)) x.val]
    exact map_natCast γ x.val
  let γA : GaloisField p k ≃ₐ[ZMod p] GaloisField p k :=
    AlgEquiv.ofRingEquiv (f := γ) hf
  have hcoe : ∀ x : GaloisField p k, γA x = γ x := fun x => rfl
  have hiter : ∀ (e : GaloisField p k ≃+* GaloisField p k) (x : GaloisField p k) (n : ℕ),
      (e ^ n) x = (⇑e)^[n] x := by
    intro e x n
    induction n with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ']
        show e ((e ^ m) x) = (⇑e)^[m + 1] x
        rw [ih, Function.iterate_succ_apply']
  have hpowA : γA ^ r = 1 := by
    apply AlgEquiv.ext
    intro x
    rw [AlgEquiv.coe_pow]
    have hfun : (⇑γA : GaloisField p k → GaloisField p k) = ⇑γ := funext hcoe
    rw [hfun, ← hiter γ x r, ← hγ, pow_orderOf_eq_one γ]
    rfl
  have hneA : γA ≠ 1 := by
    intro h
    have h1 : γ = 1 := by
      ext x
      have hxx := congrFun (congrArg DFunLike.coe h) x
      rw [← hcoe x]
      exact hxx
    rw [h1, orderOf_one] at hγ
    have := hr.one_lt
    omega
  have horderA : orderOf γA = r := orderOf_eq_prime hpowA hneA
  let H : Subgroup (GaloisField p k ≃ₐ[ZMod p] GaloisField p k) := Subgroup.zpowers γA
  haveI : FiniteDimensional (ZMod p) (GaloisField p k) := Module.Finite.of_finite
  have hcodim : Module.finrank (↥(fixedField H)) (GaloisField p k) = r := by
    rw [finrank_fixedField_eq_card H]
    show Nat.card ↥(Subgroup.zpowers γA) = r
    rw [Nat.card_zpowers, horderA]
  have hZp : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hFk : Module.finrank (ZMod p) (GaloisField p k) = k := by
    haveI : NeZero (Nat.card (ZMod p)) := ⟨Nat.card_pos.ne'⟩
    have h1 : Nat.card (GaloisField p k)
        = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (GaloisField p k) :=
      Module.natCard_eq_pow_finrank
    rw [GaloisField.card p k hk, hZp] at h1
    exact (Nat.pow_right_injective (by have := (Fact.out : p.Prime).one_lt; omega) h1).symm
  refine ⟨Module.finrank (ZMod p) (↥(fixedField H)), ?_⟩
  calc k = Module.finrank (ZMod p) (GaloisField p k) := hFk.symm
    _ = Module.finrank (ZMod p) (↥(fixedField H)) * r := by
          rw [← Module.finrank_mul_finrank (ZMod p) (↥(fixedField H)) (GaloisField p k), hcodim]

/-- If a ring automorphism of `GF(p^k)` has prime order `r`, then `r ∣ k`. -/
theorem dvd_of_orderOf_eq (p k r : ℕ) [Fact p.Prime] (hk : k ≠ 0) (hr : r.Prime)
    (γ : GaloisField p k ≃+* GaloisField p k) (hγ : orderOf γ = r) : r ∣ k := by
  obtain ⟨m, hm⟩ := setup_finrank p k r hk hr γ hγ
  exact ⟨m, by rw [hm, mul_comm]⟩

end Work.DSTR.M110.SplitCase
