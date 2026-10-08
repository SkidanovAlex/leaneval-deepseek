import Mathlib
import Submission.Work.ThmF.Tools.External
import Submission.Work.ThmF.Prove.cyclic_orders_prime
import Submission.Work.ThmF.Prove.fixedField_card_finrank

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.fieldStep8` — the field arithmetic of Ch. V §3 step (8)

The Bender–Suzuki development (Peterfalvi, Ch. V §3 step (8)) needs the following arithmetic
fact.  Let `F` be a finite field of characteristic `f ∈ {3, 5}` and let `A` be a finite group of
**odd** order, `|A| > 1`, acting faithfully on `F` by ring automorphisms, in such a way that
every `w ≠ 1` in `A` fixes exactly `2 ^ b + 1` elements of `F`.  Then `|A|` is prime and
`|F| ∈ {3 ^ |A|, 5 ^ |A|, 9 ^ |A|}`.

The proof has three ingredients.

* Every ring automorphism of `F` fixes the prime field `𝔽_f`, hence is an `𝔽_f`-algebra
  automorphism; this gives an injective monoid hom `A →* Gal(F/𝔽_f)` (`toGalHom` below).
* For `σ ∈ Gal(F/𝔽_f)`, if `d := [F^{⟨σ⟩} : 𝔽_f]` is the degree of the fixed field, then
  `|Fix σ| = f ^ d` and `d * orderOf σ = [F : 𝔽_f]` (Artin's theorem; this is the delegated
  lemma `fixedField_card_finrank`).
* Combining with the hypothesis and Huppert–Blackburn IX (2.7) (`ArithmeticNineTwoSeven`,
  the input `hA`) gives, for every `w ≠ 1`, `orderOf (act w) = [F : 𝔽_f]` or `f = 3` and
  `2 * orderOf (act w) = [F : 𝔽_f]`; the elementary group-theoretic lemma
  `cyclic_orders_prime` (delegated) then yields `|A|` prime and `[F : 𝔽_f] ∈ {|A|, 2|A|}`,
  which gives the claimed values of `|F|`.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove

open Classical

/-! ## Ring automorphisms of a finite field are automorphisms of the prime field -/

section Setup

variable {f : ℕ} [Fact f.Prime] {F : Type} [Field F] [Fintype F] [CharP F f] [Algebra (ZMod f) F]

/-- Every ring automorphism of a field of characteristic `f` fixes the prime field `𝔽_f = ZMod f`,
so it is an `𝔽_f`-algebra automorphism. -/
noncomputable def toGal (σ : F ≃+* F) : F ≃ₐ[ZMod f] F where
  toRingEquiv := σ
  commutes' := fun a => by
    haveI : NeZero f := ⟨(Fact.out : f.Prime).ne_zero⟩
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
    simp

omit [Fintype F] [CharP F f] in
theorem toGal_injective : Function.Injective (toGal (f := f) (F := F)) := by
  intro σ τ h
  ext x
  exact congrArg (fun e : F ≃ₐ[ZMod f] F => e x) h

/-- The canonical monoid hom from the ring automorphism group of `F` to `Gal(F/𝔽_f)`.  It is
injective, the underlying function being unchanged. -/
noncomputable def toGalHom : (F ≃+* F) →* (F ≃ₐ[ZMod f] F) where
  toFun := toGal (f := f) (F := F)
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    rfl

end Setup

section Main

/-- **Ch. V §3 step (8), field arithmetic.**  A finite group `A` of odd order `> 1` acting
faithfully on a finite field `F` of characteristic `3` or `5` by ring automorphisms, with every
`w ≠ 1` fixing exactly `2 ^ b + 1` elements, has prime order, and `|F|` is `3 ^ |A|`, `5 ^ |A|`
or `9 ^ |A|`. -/
theorem fieldStep8 (hA : Work.ThmF.ArithmeticNineTwoSeven) (f : ℕ) [Fact f.Prime]
    (hf : f = 3 ∨ f = 5) {F : Type} [Field F] [Fintype F] [CharP F f]
    {A : Type} [Group A] [Finite A] (hodd : Odd (Nat.card A)) (hA1 : 1 < Nat.card A)
    (act : A →* (F ≃+* F)) (hinj : Function.Injective act)
    (h2 : ∀ w : A, w ≠ 1 → ∃ b : ℕ, Nat.card (Function.fixedPoints (act w)) = 2 ^ b + 1) :
    (Nat.card A).Prime ∧
      (Nat.card F = 3 ^ Nat.card A ∨ Nat.card F = 5 ^ Nat.card A ∨ Nat.card F = 9 ^ Nat.card A) := by
  classical
  haveI : NeZero f := ⟨(Fact.out : f.Prime).ne_zero⟩
  -- view `F` as an algebra over its prime field `𝔽_f`
  letI : Algebra (ZMod f) F := ZMod.algebra F f
  -- the induced faithful action on `Gal(F/𝔽_f)`
  let Φ : A →* (F ≃ₐ[ZMod f] F) := (toGalHom (f := f) (F := F)).comp act
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    exact hinj (toGal_injective hab)
  -- cardinality of `F` in terms of the `𝔽_f`-dimension
  have hFcard : Nat.card F = f ^ Module.finrank (ZMod f) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod f) (V := F), Nat.card_zmod]
  -- the Galois group of a finite field is (finite) of order the degree
  have hGcard : Nat.card (F ≃ₐ[ZMod f] F) = Module.finrank (ZMod f) F :=
    IsGalois.card_aut_eq_finrank (ZMod f) F
  have hodd_f : Odd f := by rcases hf with h | h <;> rw [h] <;> norm_num
  have h2f : 2 ≤ f := by rcases hf with h | h <;> rw [h] <;> norm_num
  -- the dichotomy for a single automorphism
  have key : ∀ (σ : F ≃ₐ[ZMod f] F), (∃ b : ℕ, Nat.card (Function.fixedPoints σ) = 2 ^ b + 1) →
      orderOf σ = Module.finrank (ZMod f) F ∨
        (f = 3 ∧ 2 * orderOf σ = Module.finrank (ZMod f) F) := by
    intro σ ⟨b, hb⟩
    set d : ℕ := Module.finrank (ZMod f) (IntermediateField.fixedField (Subgroup.zpowers σ)) with hd
    obtain ⟨hfix, hdmul⟩ := fixedField_card_finrank (p := f) (F := F) σ
    -- the fixed field has `f ^ d` elements, and `hA` forces `d ∈ {1, 2}`
    have hbd : f ^ d = 2 ^ b + 1 := by
      rw [← hfix]
      exact hb
    have hdpos : 0 < d := by
      by_contra hcon
      have h0 : d = 0 := Nat.eq_zero_of_not_pos hcon
      rw [h0, pow_zero] at hbd
      have hb0 : 2 ^ b = 0 := by omega
      exact (Nat.two_pow_pos b).ne' hb0
    have hdisj : d = 1 ∨ f ^ d = 9 := hA f d b hodd_f h2f hdpos hbd
    rcases hdisj with h1 | h9
    · left
      rw [← hdmul, ← hd, h1, one_mul]
    · right
      have hf3 : f = 3 := by
        rcases hf with h3 | h5
        · exact h3
        · exfalso
          rw [h5] at h9
          have hdvd : 5 ∣ 9 := by
            rw [← h9]
            exact dvd_pow_self 5 (Nat.pos_iff_ne_zero.mp hdpos)
          norm_num at hdvd
      have hd2 : d = 2 := by
        rw [hf3] at h9
        have h9' : 3 ^ d = 3 ^ 2 := by norm_num at h9 ⊢; exact h9
        exact Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) h9'
      exact ⟨hf3, by rw [← hdmul, ← hd, hd2]⟩
  -- the dichotomy for every non-identity element of `A`
  have key' : ∀ a : A, a ≠ 1 →
      orderOf (Φ a) = Nat.card (F ≃ₐ[ZMod f] F) ∨
        2 * orderOf (Φ a) = Nat.card (F ≃ₐ[ZMod f] F) := by
    intro a ha
    obtain ⟨b, hb⟩ := h2 a ha
    rcases key (Φ a) ⟨b, hb⟩ with h | ⟨-, h⟩
    · left
      rwa [hGcard]
    · right
      rwa [hGcard]
  obtain ⟨hprime, hcases⟩ := cyclic_orders_prime Φ hΦinj hA1 hodd key'
  have hcases' : Module.finrank (ZMod f) F = Nat.card A ∨
      Module.finrank (ZMod f) F = 2 * Nat.card A := by
    rcases hcases with h | h
    · left
      rwa [← hGcard]
    · right
      rwa [← hGcard]
  refine ⟨hprime, ?_⟩
  rcases hcases' with hn | hn
  · -- `[F : 𝔽_f] = |A|`
    rw [hFcard, hn]
    rcases hf with h3 | h5
    · exact Or.inl (by rw [h3])
    · exact Or.inr (Or.inl (by rw [h5]))
  · -- `[F : 𝔽_f] = 2|A|`; then the quadratic case forces `f = 3` and gives `9 ^ |A|`
    have hf3 : f = 3 := by
      haveI : Fact (Nat.card A).Prime := ⟨hprime⟩
      haveI : Fintype A := Fintype.ofFinite A
      have hdvd : Nat.card A ∣ Fintype.card A := by rw [Nat.card_eq_fintype_card]
      obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (Nat.card A) hdvd
      have ha1 : a ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at ha
        omega
      obtain ⟨b, hb⟩ := h2 a ha1
      rcases key (Φ a) ⟨b, hb⟩ with h | ⟨hf3, -⟩
      · exfalso
        have ho : orderOf (Φ a) = orderOf a := orderOf_injective Φ hΦinj a
        rw [ho, ha] at h
        omega
      · exact hf3
    rw [hFcard, hn, hf3]
    right
    right
    rw [pow_mul]
    norm_num

end Main

end Work.ThmF.Prove
