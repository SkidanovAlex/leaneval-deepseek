/-
Copyright (c) 2025. All rights reserved.

# The transgression `H²(ℤ/n, A) → A/nA` is surjective on the nose

For `G = Multiplicative (ZMod n)` and an additive commutative group `A` with the trivial action,
the "carry" `2`-cocycle

`c(g, h) = (((repr g) + (repr h)) / n) • b`

(where `repr` is the canonical representative `ZMod.val ∈ {0, …, n-1}`) is a `2`-cocycle, because
the number of carries in a sum of three residues is computed in two ways (`carry_split`).  Its
transgression is

`τ c = ∑_{x : ZMod n} c(x, s) = ∑_{m ∈ range n} ((m + 1) / n) • b = b`

since the only term with a nonzero carry is `m = n - 1`.  Hence `τ : Z²(ℤ/n, A) → A` is
surjective: the element `b` is realized exactly (not merely modulo `nA`), which is the form of
the statement used by the Kummer-theoretic realization step.

The proof of the cocycle identity is carried out in `A` (the type synonym `TrivMod G A` is
definitionally `A`), using the additive equivalence `trivEquiv n A : TrivMod G A ≃+ A` to move
between the two copies of the same group.
-/
import Mathlib
import Submission.Work.GroupCohomology.CyclicTriv
import Submission.Work.GroupCohomology.CarryArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.GroupCohomology

open Multiplicative

universe v

/-- Arithmetic form of the cocycle identity for the carry cocycle: both sides count the total
number of carries in `a + c + d`, splitting the sum at `a + c` on the left and at `c + d` on the
right. -/
theorem carry_arith (n a c d : ℕ) (hn : 0 < n) :
    ((a + c) % n + d) / n + (a + c) / n = (c + d) / n + (a + (c + d) % n) / n := by
  have h1 := carry_split n (a + c) d hn
  have h2 := carry_split n (c + d) a hn
  rw [Nat.add_comm (((a + c) % n + d) / n) ((a + c) / n), h1, Nat.add_comm a ((c + d) % n),
    h2, show a + c + d = c + d + a from by omega]

/-- The identity equivalence `TrivMod G A ≃+ A`, with `G = Multiplicative (ZMod n)` fixed so that
the group is never left implicit. -/
noncomputable def trivEquiv (n : ℕ) (A : Type v) [AddCommGroup A] :
    TrivMod (Multiplicative (ZMod n)) A ≃+ A :=
  TrivMod.addEquiv

/-- The underlying `A`-valued "carry" `2`-cochain: `(g, h) ↦ carry(g, h) • b`, where the carry is
the quotient `(val g + val h) / n` of the canonical representatives. -/
noncomputable def carryFun (n : ℕ) [NeZero n] (A : Type v) [AddCommGroup A] (b : A) :
    Multiplicative (ZMod n) × Multiplicative (ZMod n) → A :=
  fun p => ((p.1.toAdd.val + p.2.toAdd.val) / n) • b

@[simp] theorem carryFun_apply (n : ℕ) [NeZero n] (A : Type v) [AddCommGroup A] (b : A)
    (g h : Multiplicative (ZMod n)) :
    carryFun n A b (g, h) = ((g.toAdd.val + h.toAdd.val) / n) • b := rfl

/-- The carry `2`-cocycle, as a `TrivMod G A`-valued cochain. -/
noncomputable def carryCocycle (n : ℕ) [NeZero n] (A : Type v) [AddCommGroup A] (b : A) :
    Multiplicative (ZMod n) × Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A :=
  fun p => (trivEquiv n A).symm (carryFun n A b p)

@[simp] theorem carryCocycle_apply (n : ℕ) [NeZero n] (A : Type v) [AddCommGroup A] (b : A)
    (g h : Multiplicative (ZMod n)) :
    carryCocycle n A b (g, h) = (trivEquiv n A).symm (carryFun n A b (g, h)) := rfl

/-- The carry cochain is a `2`-cocycle: both sides of the cocycle identity are
`(carry(g + h, k) + carry(g, h)) • b = (carry(h, k) + carry(g, h + k)) • b`, and the two natural
numbers agree because they both count the carries in `val g + val h + val k`. -/
theorem carryCocycle_mem (n : ℕ) [NeZero n] (A : Type v) [AddCommGroup A] (b : A) :
    carryCocycle n A b ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) := by
  rw [mem_Z2_iff]
  intro g h k
  change carryFun n A b (g * h, k) + carryFun n A b (g, h)
      = carryFun n A b (h, k) + carryFun n A b (g, h * k)
  have hcoef : ((g * h).toAdd.val + k.toAdd.val) / n + (g.toAdd.val + h.toAdd.val) / n
      = (h.toAdd.val + k.toAdd.val) / n + (g.toAdd.val + (h * k).toAdd.val) / n := by
    have hgh : (g * h).toAdd = g.toAdd + h.toAdd := rfl
    have hhk : (h * k).toAdd = h.toAdd + k.toAdd := rfl
    rw [hgh, hhk, ZMod.val_add, ZMod.val_add]
    exact carry_arith n g.toAdd.val h.toAdd.val k.toAdd.val (Nat.pos_of_neZero n)
  simp only [carryFun_apply]
  rw [← add_nsmul, ← add_nsmul, hcoef]

/-- The transgression of the carry cocycle is `b`: the only generator-slice value of the cocycle
that does not vanish is the one at `x = -1`, where the carry is `1`. -/
theorem trivT_carryCocycle (n : ℕ) [NeZero n] (hn : 1 < n) (A : Type v) [AddCommGroup A]
    (b : A) :
    trivT n A (carryCocycle n A b
      : Multiplicative (ZMod n) × Multiplicative (ZMod n) →
        TrivMod (Multiplicative (ZMod n)) A) = b := by
  have key : trivEquiv n A (trivT n A (carryCocycle n A b)) = b := by
    rw [trivT_eq_sum_range, map_sum]
    have hterm : ∀ m ∈ Finset.range n,
        trivEquiv n A (genSlice n A (carryCocycle n A b) (m : ZMod n))
          = (((m + 1) / n) • b : A) := by
      intro m hm
      have hm' : m < n := Finset.mem_range.mp hm
      have hofadd : (Multiplicative.ofAdd (m : ZMod n)).toAdd.val = (m : ZMod n).val := rfl
      have hcyc : (cycGen n).toAdd.val = 1 := by
        rw [show (cycGen n).toAdd = (1 : ZMod n) from rfl]
        haveI : Fact (1 < n) := ⟨hn⟩
        exact ZMod.val_one n
      have hmv : ((m : ZMod n)).val = m := ZMod.val_cast_of_lt hm'
      simp only [genSlice_apply, carryCocycle_apply, carryFun_apply, AddEquiv.apply_symm_apply]
      rw [hofadd, hmv, hcyc]
    have hsum : (∑ m ∈ Finset.range n,
          trivEquiv n A (genSlice n A (carryCocycle n A b) (m : ZMod n)))
        = ∑ m ∈ Finset.range n, (((m + 1) / n) • b : A) :=
      Finset.sum_congr rfl hterm
    rw [hsum, Finset.sum_eq_single (n - 1)]
    · rw [Nat.sub_add_cancel (show 1 ≤ n by omega), Nat.div_self (show 0 < n by omega), one_nsmul]
    · intro x hx hne
      rw [Nat.div_eq_of_lt (by simp only [Finset.mem_range] at hx; omega), zero_nsmul]
    · intro hmem
      exact absurd (by simp only [Finset.mem_range]; omega) hmem
  exact (trivEquiv n A).injective key

/-- **Surjectivity of the transgression on cocycles.**  For the cyclic group `ℤ/n` (`n > 1`) and
any additive commutative group `A` with trivial action, every `b : A` is the transgression
`τ c = ∑_{x : ZMod n} c (x, s)` of some `2`-cocycle `c`. -/
theorem exists_cocycle_of_transgression {n : ℕ} [NeZero n] (hn : 1 < n) {A : Type*} [AddCommGroup A]
    (b : A) :
    ∃ c : Work.GroupCohomology.Z2 (Multiplicative (ZMod n))
        (Work.GroupCohomology.TrivMod (Multiplicative (ZMod n)) A),
      Work.GroupCohomology.trivT n A
        (c : Multiplicative (ZMod n) × Multiplicative (ZMod n) →
          Work.GroupCohomology.TrivMod (Multiplicative (ZMod n)) A) = b := by
  exact ⟨⟨carryCocycle n A b, carryCocycle_mem n A b⟩, trivT_carryCocycle n hn A b⟩

end Work.GroupCohomology
