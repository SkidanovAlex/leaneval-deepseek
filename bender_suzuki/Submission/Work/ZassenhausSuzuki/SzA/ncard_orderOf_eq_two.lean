import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of involutions of Higman's group `A(K,θ)`

For a finite field `K` of characteristic two and any ring automorphism `θ` of `K`, the
involutions of Higman's group `A(K,θ) = SzA K θ` are exactly the non-trivial elements of the
central root subgroup `{(0,b)}`, so there are `|K| - 1` of them:

`#{x ∈ A(K,θ) | x² = 1, x ≠ 1} = |K| - 1`.

Indeed, in characteristic two `x * x = ⟨0, x.a·θ x.a⟩` (`SzA.sq_eq`), and since `K` is a field
and `θ` is injective this equals `1` exactly when `x.a = 0`; such an element is `1` precisely
when its second coordinate vanishes.  The count is then the elementary fact that a finite type
with one point removed has cardinality one less.

This is the count used in `Work.ZassenhausSuzuki.card_twoPoint` to prove `|D| = q - 1` in the
Suzuki rank-one configuration (`REFS/zassenhaus_groups.md` §5, Suzuki 1962, Lemma 6).
-/

namespace Work.ZassenhausSuzuki.SzA

/-- **The involutions of `A(K,θ)` in coordinates.**  In characteristic two an element `x` of
Higman's group `A(K,θ)` has order two if and only if its first coordinate vanishes and its
second coordinate is non-zero.

`x ^ 2 = ⟨0, x.a * θ x.a⟩` (`SzA.sq_eq`); the product `x.a * θ x.a` vanishes exactly when
`x.a = 0`, because `K` is a field and `θ` is injective, and conversely `⟨0, b⟩ ^ 2 = 1` while
`⟨0, b⟩ ≠ 1` for `b ≠ 0`. -/
theorem orderOf_eq_two_iff_coord {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)
    (x : SzA K θ) : orderOf x = 2 ↔ x.a = 0 ∧ x.b ≠ 0 := by
  have hsqeq : x ^ 2 = (⟨0, x.a * θ x.a⟩ : SzA K θ) := by
    rw [pow_two]; exact sq_eq θ x
  have hsq : x ^ 2 = 1 ↔ x.a = 0 := by
    rw [hsqeq]
    constructor
    · intro h
      have hb : x.a * θ x.a = 0 := by
        have h' := congrArg SzA.b h
        simpa using h'
      rcases mul_eq_zero.mp hb with h'' | h''
      · exact h''
      · exact (RingEquiv.map_eq_zero_iff θ).mp h''
    · intro h
      ext <;> simp [h]
  rw [orderOf_eq_prime_iff]
  constructor
  · rintro ⟨h2, hne⟩
    have ha := hsq.mp h2
    refine ⟨ha, ?_⟩
    intro hb
    exact hne (by ext <;> simp [ha, hb])
  · rintro ⟨ha, hb⟩
    exact ⟨hsq.mpr ha, by intro h1; exact hb (by simp [h1])⟩

/-- For a set in a finite type, `Set.ncard` is the `Nat.card` of the corresponding subtype. -/
theorem ncard_eq_natCard_of_finite {α : Type*} [Finite α] (s : Set α) :
    s.ncard = Nat.card ↥s := by
  haveI : Fintype ↥s := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Nat.card_eq_fintype_card]

/-- Removing one point from a finite type decreases its cardinality by one. -/
theorem natCard_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h := Fintype.card_subtype_compl (fun x : α => x = a)
  have h1 : Fintype.card {x : α // x = a} = 1 := Fintype.card_subtype_eq a
  rw [h1] at h
  exact h

theorem ncard_orderOf_eq_two {K : Type*} [Field K] [CharP K 2] [Finite K]
    (θ : K ≃+* K) :
    ({x : Work.ZassenhausSuzuki.SzA K θ | orderOf x = 2} : Set (Work.ZassenhausSuzuki.SzA K θ)).ncard
      = Nat.card K - 1 := by
  classical
  set S : Set (SzA K θ) := {x | orderOf x = 2} with hS
  have hbridge : S.ncard = Nat.card ↥S := ncard_eq_natCard_of_finite S
  rw [hbridge]
  -- The involutions `⟨0,b⟩`, `b ≠ 0`, are in bijection with the non-zero elements of `K`.
  have he : Nat.card ↥S = Nat.card {b : K // b ≠ 0} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨x.1.b, ((orderOf_eq_two_iff_coord θ x.1).mp x.2).2⟩
        invFun := fun b => ⟨⟨0, b.1⟩, (orderOf_eq_two_iff_coord θ ⟨0, b.1⟩).mpr ⟨rfl, b.2⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      apply Subtype.ext
      have ha := ((orderOf_eq_two_iff_coord θ x.1).mp x.2).1
      ext <;> simp [ha]
    · intro b
      apply Subtype.ext
      rfl
  rw [he]
  exact natCard_subtype_ne 0

end Work.ZassenhausSuzuki.SzA
