import Mathlib
import Submission.NK.NUV2.RouteC.delta_qmodz

/-!
# The `ℚ/ℤ`-valued invariant attached to a generator of `H²` (Route C, RouteD plan)

For a finite group `G` (the local Galois group `Gal(E/F)` of a finite abelian level) the group
`H²(G, Eˣ)` is cyclic of order `[E : F]` (local class field theory).  This file provides, in the
vocabulary of `NK.NUV2.RouteC.qmodZ = ℚ/ℤ`:

* `zmodToQmodZ n : ZMod n →+ ℚ/ℤ`, `k ↦ k/n` (the level map);
* `generatorEquiv u hu : ZMod n ≃+ A` for an element `u` of additive order `Nat.card A`, and the
  invariant `invariantOf u hu : A →+ ℚ/ℤ` with `invariantOf u hu u = 1/Nat.card A`;

these are the ingredients of the character formula `χ(θ a) = inv_u(a ∪ δχ)`, and of the
compatibility of the invariants under inflation (`invariantOf_comp_eq_of_inf`).
-/

open scoped Classical

namespace NK.NUV2.RouteC

noncomputable section

/-! ## The level map `ZMod n → ℚ/ℤ` -/

/-- The additive homomorphism `ℤ →+ ℚ/ℤ`, `k ↦ k/n` (the value `k/0 = 0` keeps it additive at
`n = 0`). -/
noncomputable def zmodIntHom (n : ℕ) : ℤ →+ qmodZ where
  toFun k := ratToQmodZ ((k : ℚ) / (n : ℚ))
  map_zero' := by simp
  map_add' a b := by
    show ratToQmodZ ((((a + b : ℤ) : ℚ)) / (n : ℚ))
      = ratToQmodZ ((a : ℚ) / (n : ℚ)) + ratToQmodZ ((b : ℚ) / (n : ℚ))
    rw [← map_add, Int.cast_add, add_div]

theorem zmodIntHom_apply (n : ℕ) (k : ℤ) :
    zmodIntHom n k = ratToQmodZ ((k : ℚ) / (n : ℚ)) := rfl

/-- `q = 0` in `ℚ/ℤ` exactly when `q` is an integer. -/
theorem ratToQmodZ_eq_zero_iff (q : ℚ) :
    ratToQmodZ q = 0 ↔ ∃ t : ℤ, (t : ℚ) = q := by
  have h : ratToQmodZ q = (q : qmodZ) := rfl
  rw [h, QuotientAddGroup.eq_zero_iff q, ← AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa using ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp⟩

/-- **The kernel of `k ↦ k/n`** (for `n ≠ 0`): exactly the multiples of `n`. -/
theorem zmodIntHom_eq_zero_iff {n : ℕ} (hn : n ≠ 0) (k : ℤ) :
    zmodIntHom n k = 0 ↔ (n : ℤ) ∣ k := by
  rw [zmodIntHom_apply, ratToQmodZ_eq_zero_iff]
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  constructor
  · rintro ⟨t, ht⟩
    have h2 : (k : ℚ) = (t : ℚ) * (n : ℚ) := by
      rw [ht, div_mul_cancel₀ _ hnq]
    exact ⟨t, by rw [mul_comm]; exact_mod_cast h2⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    push_cast
    rw [mul_div_cancel_left₀ (t : ℚ) hnq]

/-- **The level map `ZMod n →+ ℚ/ℤ`, `k ↦ k/n`.** -/
noncomputable def zmodToQmodZ (n : ℕ) : ZMod n →+ qmodZ :=
  ZMod.lift n ⟨zmodIntHom n, by
    by_cases hn : n = 0
    · subst hn
      simp [zmodIntHom]
    · have hq : ((((n : ℤ)) : ℚ) / (n : ℚ)) = (1 : ℚ) := by
        rw [Int.cast_natCast, div_self (Nat.cast_ne_zero.mpr hn)]
      rw [zmodIntHom_apply, hq]
      exact (ratToQmodZ_eq_zero_iff 1).mpr ⟨1, by norm_num⟩⟩

theorem zmodToQmodZ_intCast (n : ℕ) (k : ℤ) :
    zmodToQmodZ n (k : ZMod n) = ratToQmodZ ((k : ℚ) / (n : ℚ)) := by
  unfold zmodToQmodZ
  rw [ZMod.lift_coe]
  rfl

/-- On `1`, the level map is the class of `1/n`. -/
theorem zmodToQmodZ_one (n : ℕ) :
    zmodToQmodZ n (1 : ZMod n) = ratToQmodZ ((1 : ℚ) / (n : ℚ)) := by
  rw [show (1 : ZMod n) = (((1 : ℤ)) : ZMod n) by norm_num, zmodToQmodZ_intCast]
  norm_num

/-- **The level map is injective** (for `n ≠ 0`). -/
theorem zmodToQmodZ_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective (zmodToQmodZ n) := by
  haveI : NeZero n := ⟨hn⟩
  intro a b hab
  have hsub : zmodToQmodZ n (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hcast : zmodToQmodZ n ((((a - b).val : ℤ)) : ZMod n) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hsub
  have hcast2 : zmodIntHom n ((a - b).val : ℤ) = 0 := by
    have h := hcast
    unfold zmodToQmodZ at h
    rw [ZMod.lift_coe] at h
    exact h
  have hdvd : (n : ℤ) ∣ ((a - b).val : ℤ) := (zmodIntHom_eq_zero_iff hn _).mp hcast2
  have hnat : n ∣ (a - b).val := Int.natCast_dvd_natCast.mp hdvd
  have hzero : (a - b).val = 0 := Nat.eq_zero_of_dvd_of_lt hnat (ZMod.val_lt _)
  have : a - b = 0 := by
    rw [← ZMod.natCast_zmod_val (a - b), hzero]
    simp
  exact sub_eq_zero.mp this

/-! ## The generator equivalence and the invariant -/

section Generator

variable {A : Type} [AddCommGroup A] [Finite A]

/-- An element of additive order `Nat.card A` generates `A`. -/
theorem zmultiples_eq_top_of_addOrderOf_eq_card (u : A)
    (hu : addOrderOf u = Nat.card A) : AddSubgroup.zmultiples u = ⊤ := by
  refine AddSubgroup.eq_of_le_of_card_ge (H := AddSubgroup.zmultiples u) (K := ⊤) le_top ?_
  have htop : Nat.card ↥(⊤ : AddSubgroup A) = Nat.card A :=
    Nat.card_congr (Equiv.Set.univ A)
  rw [htop, Nat.card_zmultiples, hu]

variable (u : A) (hu : addOrderOf u = Nat.card A)

/-- **A generator `u` of additive order `Nat.card A` gives an isomorphism `ZMod (Nat.card A) ≃+ A`**
(which sends `1` to `u`). -/
noncomputable def generatorEquiv : ZMod (Nat.card A) ≃+ A :=
  zmodAddEquivOfGenerator (fun x => by
    rw [zmultiples_eq_top_of_addOrderOf_eq_card u hu]; trivial) rfl

theorem generatorEquiv_apply_intCast (i : ℤ) : generatorEquiv u hu (i : ZMod (Nat.card A)) = i • u :=
  zmodAddEquivOfGenerator_apply_intCast _ _ i

theorem generatorEquiv_apply_one : generatorEquiv u hu 1 = u :=
  zmodAddEquivOfGenerator_apply_one _ _

theorem generatorEquiv_symm_apply_generator : (generatorEquiv u hu).symm u = 1 :=
  zmodAddEquivOfGenerator_symm_apply_generator _ _

theorem generatorEquiv_symm_apply_zsmul (i : ℤ) :
    (generatorEquiv u hu).symm (i • u) = (i : ZMod (Nat.card A)) :=
  zmodAddEquivOfGenerator_symm_apply_zsmul _ _ i

omit hu in
theorem card_ne_zero : Nat.card A ≠ 0 :=
  (Nat.card_pos (α := A)).ne'

end Generator

section Invariant

variable {A : Type} [AddCommGroup A] [Finite A]

/-- **The `ℚ/ℤ`-valued invariant attached to a generator `u`** of the finite abelian group `A`: the
composite `A ≃+ ZMod (Nat.card A) →+ ℚ/ℤ` of the inverse of the generator isomorphism with the level
map `k ↦ k/Nat.card A`.  It sends `u` to `1/Nat.card A`. -/
noncomputable def invariantOf (u : A) (hu : addOrderOf u = Nat.card A) : A →+ qmodZ :=
  (zmodToQmodZ (Nat.card A)).comp (generatorEquiv u hu).symm.toAddMonoidHom

variable (u : A) (hu : addOrderOf u = Nat.card A)

theorem invariantOf_apply (x : A) :
    invariantOf u hu x = zmodToQmodZ (Nat.card A) ((generatorEquiv u hu).symm x) := rfl

@[simp]
theorem invariantOf_zero (hu' : addOrderOf u = Nat.card A) : invariantOf u hu' 0 = 0 := map_zero _

/-- The invariant of the generator itself is `1/Nat.card A`. -/
theorem invariantOf_generator :
    invariantOf u hu u = ratToQmodZ ((1 : ℚ) / (Nat.card A : ℚ)) := by
  rw [invariantOf_apply, generatorEquiv_symm_apply_generator, zmodToQmodZ_one]

/-- The invariant of a multiple of the generator is the class of `k/Nat.card A`. -/
theorem invariantOf_zsmul (k : ℤ) :
    invariantOf u hu (k • u) = ratToQmodZ ((k : ℚ) / (Nat.card A : ℚ)) := by
  rw [invariantOf_apply, generatorEquiv_symm_apply_zsmul, zmodToQmodZ_intCast]

/-- **The invariant is injective.** -/
theorem invariantOf_injective : Function.Injective (invariantOf u hu) :=
  (zmodToQmodZ_injective (card_ne_zero (A := A))).comp (generatorEquiv u hu).symm.injective

theorem invariantOf_eq_zero_iff (x : A) : invariantOf u hu x = 0 ↔ x = 0 :=
  ⟨fun h => invariantOf_injective u hu (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

theorem invariantOf_eq_iff (x y : A) : invariantOf u hu x = invariantOf u hu y ↔ x = y :=
  ⟨fun h => invariantOf_injective u hu h, fun h => by rw [h]⟩

end Invariant

/-! ## Compatibility of the invariant with a map on generators

This is the algebraic content of the *compatibility* of the level maps of the reciprocity law: if
`Inf u_L = ([E:L]) • u_E` for generators `u_L` of `H²(Gal(L/F), Lˣ)` and `u_E` of `H²(Gal(E/F),Eˣ)`
(the relation read off from `range Inf = {x | [L:F] • x = 0}`), then the corresponding invariants
are linked by `Inf`: `inv_{u_L} = inv_{u_E} ∘ Inf`. -/

theorem invariantOf_comp_eq_of_inf {A : Type} [AddCommGroup A] [Finite A]
    {B : Type} [AddCommGroup B] [Finite B]
    (u : A) (hu : addOrderOf u = Nat.card A) (v : B) (hv : addOrderOf v = Nat.card B)
    (hdvd : Nat.card A ∣ Nat.card B) (f : A →+ B)
    (hfu : f u = ((Nat.card B / Nat.card A : ℕ) : ℤ) • v) :
    invariantOf u hu = (invariantOf v hv).comp f := by
  have hA : Nat.card A ≠ 0 := card_ne_zero
  have hB : Nat.card B ≠ 0 := card_ne_zero
  have hgen : AddSubgroup.zmultiples u = ⊤ := zmultiples_eq_top_of_addOrderOf_eq_card u hu
  refine AddMonoidHom.ext fun x => ?_
  have hx : x ∈ AddSubgroup.zmultiples u := by rw [hgen]; trivial
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [← hk, invariantOf_zsmul, AddMonoidHom.comp_apply, map_zsmul, hfu, ← mul_zsmul,
    invariantOf_zsmul]
  congr 1
  have hA' : (Nat.card A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hA
  have hB' : (Nat.card B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hA']
  field_simp

end

end NK.NUV2.RouteC
