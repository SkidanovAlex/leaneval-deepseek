import Mathlib
import Submission.Work.GroupCohomology.Cyclic
import Submission.Work.GroupCohomology.Basic
import Submission.Work.GroupCohomology.CyclicTriv
import Submission.Work.GroupCohomology.H2_induction_on
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
import Submission.Work.GroupCohomology.CarryArith
import Submission.Work.GroupCohomology.exists_cocycle_of_transgression
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H²(ℤ/n, A) ≅ A/nA` for trivial coefficients

For any `n ≥ 1` and any additive commutative group `A`, the second cohomology of the cyclic group
`ℤ/n = Multiplicative (ZMod n)` with trivial coefficients `A` (`TrivMod`) is `A/nA`:

`H²(ℤ/n, A) ≅ A / nA`.

The isomorphism is the transgression `trivH2Map`, `[c] ↦ [∑_{x : ZMod n} c (x, s)]`, where
`s = cycGen n = ofAdd 1` generates `ℤ/n` (`CyclicTriv.lean`).

The two halves of the proof:

* *Injectivity* (`mem_B2_of_transgression_mem`): a cocycle whose transgression lies in `nA` is a
  coboundary.  After subtracting the coboundary `d¹ (const b)` — whose transgression is `n • b` —
  one reduces to the case `trivT c = 0` (`mem_B2_of_transgression_eq_zero`), where the coboundary
  `u (ofAdd y) = Φ 0 - ∑_{m < y.val} Φ m` is exhibited explicitly (`Φ = genSlice c`); the key
  identities are the cocycle recursion `cocycle_apply_eq_sum` and the uniqueness
  `eq_of_genSlice_eq`.
* *Surjectivity*: the "carry" cocycle of the cyclic extension has any prescribed transgression
  (`Work.GroupCohomology.exists_cocycle_of_transgression`).
-/

universe v

namespace Work.GroupCohomology

open Multiplicative

variable (n : ℕ) [NeZero n]

/-- The `2`-cochains of `ℤ/n = Multiplicative (ZMod n)` with trivial coefficients in `A`. -/
abbrev CycCochain (A : Type v) [AddCommGroup A] : Type v :=
  Multiplicative (ZMod n) × Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A

/-- **The cocycle recursion.**  A `2`-cocycle of `ℤ/n` with trivial coefficients is determined by
its generator slice `Φ x = c (x, s)`: for every `k : ℕ`,

`c (x, s^k) = ∑_{m < k} (Φ (x + m) - Φ m) + Φ 0`.

(Here `s^k` is written additively as `ofAdd (k : ZMod n)`.) -/
theorem cocycle_apply_eq_sum (A : Type v) [AddCommGroup A] {c : CycCochain n A}
    (hc : c ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A))
    (x : ZMod n) (k : ℕ) :
    c (ofAdd x, ofAdd (k : ZMod n)) =
      (∑ m ∈ Finset.range k,
          (genSlice n A c (x + (m : ZMod n)) - genSlice n A c (m : ZMod n)))
        + genSlice n A c 0 := by
  induction k with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, zero_add, genSlice_apply, Nat.cast_zero]
      have hz : (ofAdd (0 : ZMod n) : Multiplicative (ZMod n)) = 1 := rfl
      rw [hz, Z2.map_one_snd (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) hc
          (ofAdd x),
        Z2.map_one_fst (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) hc
          (cycGen n), TrivMod.smul_def]
  | succ k ih =>
      have hrec : c (ofAdd x, ofAdd (k : ZMod n) * ofAdd (1 : ZMod n)) =
          c (ofAdd x * ofAdd (k : ZMod n), ofAdd (1 : ZMod n)) + c (ofAdd x, ofAdd (k : ZMod n))
            - c (ofAdd (k : ZMod n), ofAdd (1 : ZMod n)) := by
        have h := hc (ofAdd x) (ofAdd (k : ZMod n)) (ofAdd (1 : ZMod n))
        simp only [TrivMod.smul_def] at h
        rw [← h.symm]
        abel
      rw [show ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 by push_cast; ring, ofAdd_add]
      rw [hrec, ih, Finset.sum_range_succ]
      simp only [genSlice_apply, ofAdd_add, cycGen_def]
      abel

/-- **Uniqueness.**  A `2`-cocycle of `ℤ/n` with trivial coefficients is determined by its
generator slice. -/
theorem eq_of_genSlice_eq (A : Type v) [AddCommGroup A] {c c' : CycCochain n A}
    (hc : c ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A))
    (hc' : c' ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A))
    (h : ∀ x : ZMod n, genSlice n A c x = genSlice n A c' x) : c = c' := by
  have key : ∀ x y : ZMod n, c (ofAdd x, ofAdd y) = c' (ofAdd x, ofAdd y) := by
    intro x y
    rw [← ZMod.natCast_zmod_val y, cocycle_apply_eq_sum n A hc x y.val,
      cocycle_apply_eq_sum n A hc' x y.val]
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [h (x + (m : ZMod n)), h (m : ZMod n)]
    · rw [h 0]
  funext p
  obtain ⟨g, hh⟩ := p
  show c (ofAdd g.toAdd, ofAdd hh.toAdd) = c' (ofAdd g.toAdd, ofAdd hh.toAdd)
  exact key g.toAdd hh.toAdd

/-- **Injectivity, vanishing transgression.**  A `2`-cocycle of `ℤ/n` with trivial coefficients
whose transgression vanishes is a coboundary. -/
theorem mem_B2_of_transgression_eq_zero (A : Type v) [AddCommGroup A] (c : CycCochain n A)
    (hc : c ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A))
    (h : trivT n A c = 0) :
    c ∈ B2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) := by
  obtain ⟨u, hu⟩ : ∃ u : Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A,
      ∀ y : ZMod n, u (ofAdd y) = genSlice n A c 0
        - (∑ m ∈ Finset.range y.val, genSlice n A c (m : ZMod n)) :=
    ⟨fun g => genSlice n A c 0
        - (∑ m ∈ Finset.range g.toAdd.val, genSlice n A c (m : ZMod n)), fun y => by simp⟩
  refine (mem_B2_iff _ _ c).mpr ⟨u, ?_⟩
  refine eq_of_genSlice_eq n A (d1_mem_Z2 _ _ u) hc ?_
  intro x
  rw [genSlice_apply, genSlice_apply, d1_apply, TrivMod.smul_def, cycGen_def]
  rw [show (ofAdd x * ofAdd (1 : ZMod n) : Multiplicative (ZMod n)) = ofAdd (x + 1) from rfl]
  rw [hu 1, hu (x + 1), hu x]
  rcases eq_or_ne n 1 with hn | hn
  · -- degenerate case `n = 1`
    subst hn
    have hx0 : x = 0 := Subsingleton.elim x 0
    have hx1 : (x + 1 : ZMod 1) = x := Subsingleton.elim _ _
    have hv1 : (1 : ZMod 1).val = 0 := by rw [ZMod.val_one_eq_one_mod]
    rw [hx1, hx0, hv1]
    simp only [ZMod.val_zero, Finset.range_zero, Finset.sum_empty, sub_zero, add_zero,
      genSlice_apply, cycGen_def]
    abel
  · have hn1 : 1 < n := by have := NeZero.pos n; omega
    have hm1 : (1 : ZMod n).val = 1 := ZMod.val_one'' hn
    rw [hm1, Finset.sum_range_one, Nat.cast_zero]
    by_cases hcase : x.val + 1 < n
    · -- no carry: `(x + 1).val = x.val + 1`
      have hw : (x + 1).val = x.val + 1 := by
        rw [ZMod.val_add, hm1, Nat.mod_eq_of_lt hcase]
      rw [hw, Finset.sum_range_succ, ZMod.natCast_zmod_val x]
      simp only [genSlice_apply, cycGen_def]
      abel
    · -- carry: `x.val = n - 1` and `(x + 1).val = 0`
      have hx : x.val = n - 1 := by have := ZMod.val_lt x; omega
      have hw : (x + 1).val = 0 := by
        rw [ZMod.val_add, hm1, show x.val + 1 = n by omega, Nat.mod_self]
      have hxn : (((n - 1 : ℕ)) : ZMod n) = x := by rw [← hx, ZMod.natCast_zmod_val]
      rw [hw, Finset.range_zero, Finset.sum_empty, sub_zero, hx]
      have hsum : (∑ m ∈ Finset.range (n - 1), genSlice n A c (m : ZMod n))
          + genSlice n A c x = 0 := by
        rw [← hxn, ← Finset.sum_range_succ, show n - 1 + 1 = n by omega,
          ← trivT_eq_sum_range]
        exact h
      have hsum' : (∑ m ∈ Finset.range (n - 1), genSlice n A c (m : ZMod n))
          = - genSlice n A c x := eq_neg_of_add_eq_zero_left hsum
      rw [hsum']
      simp only [genSlice_apply, cycGen_def]
      abel

/-- **Injectivity of the transgression.**  A `2`-cocycle of `ℤ/n` with trivial coefficients whose
transgression lies in `nA` is a coboundary. -/
theorem mem_B2_of_transgression_mem (A : Type v) [AddCommGroup A] (c : CycCochain n A)
    (hc : c ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A))
    (h : trivT n A c ∈ nsmulRange n (TrivMod (Multiplicative (ZMod n)) A)) :
    c ∈ B2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) := by
  obtain ⟨b, hb⟩ := mem_nsmulRange.mp h
  have hd1f : d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)
      (fun _ => b) ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) :=
    d1_mem_Z2 _ _ _
  have hmem : c - d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)
        (fun _ => b) ∈ Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) :=
    (Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)).sub_mem hc hd1f
  have hzero : trivT n A (c - d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)
      (fun _ => b)) = 0 := by
    rw [map_sub, trivT_d1, ← hb]
    simp
  have hB2 : c - d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) (fun _ => b) ∈
      B2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) :=
    mem_B2_of_transgression_eq_zero n A _ hmem hzero
  have hd1B2 : d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) (fun _ => b) ∈
      B2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) :=
    (mem_B2_iff _ _ _).mpr ⟨fun _ => b, rfl⟩
  have : c = (c - d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) (fun _ => b))
      + d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) (fun _ => b) := by
    abel
  rw [this]
  exact (B2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)).add_mem hB2 hd1B2

/-- **`H²(ℤ/n, A) ≅ A/nA`** for the trivial action, by the transgression `[c] ↦ [∑_x c (x, s)]`. -/
theorem H2_cyclic_trivial (n : ℕ) [NeZero n] (A : Type*) [AddCommGroup A] :
    Nonempty (Work.GroupCohomology.H2 (Multiplicative (ZMod n))
        (Work.GroupCohomology.TrivMod (Multiplicative (ZMod n)) A) ≃+
      (Work.GroupCohomology.TrivMod (Multiplicative (ZMod n)) A ⧸
        Work.GroupCohomology.nsmulRange n
          (Work.GroupCohomology.TrivMod (Multiplicative (ZMod n)) A))) := by
  refine ⟨AddEquiv.ofBijective (trivH2Map n A) ⟨?_, ?_⟩⟩
  · -- injectivity: the transgression is injective because its kernel is `nA`
    intro x y hxy
    have hzero : ∀ z : H2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A),
        trivH2Map n A z = 0 → z = 0 := by
      intro z hz
      refine H2_induction_on z (C := fun w => trivH2Map n A w = 0 → w = 0) ?_ hz
      intro c hc
      rw [trivH2Map_H2π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hc
      rw [H2pi_eq_zero_iff]
      exact mem_B2_of_transgression_mem n A (c : Multiplicative (ZMod n) ×
        Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A) c.2 hc
    have h1 : trivH2Map n A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h2 : x - y = 0 := hzero (x - y) h1
    rwa [sub_eq_zero] at h2
  · -- surjectivity: every element of `A/nA` is the transgression of a cocycle
    intro y
    rcases eq_or_ne n 1 with hn | hn
    · subst hn
      refine ⟨0, ?_⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
        (nsmulRange 1 (TrivMod (Multiplicative (ZMod 1)) A)) y
      rw [map_zero]
      symm
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      have htop : nsmulRange 1 (TrivMod (Multiplicative (ZMod 1)) A) = ⊤ := by
        ext a
        simp [mem_nsmulRange]
      rw [htop]
      exact trivial
    · have hn1 : 1 < n := by have := NeZero.pos n; omega
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective
        (nsmulRange n (TrivMod (Multiplicative (ZMod n)) A)) y
      obtain ⟨c, hc⟩ := exists_cocycle_of_transgression (n := n) (A := A) hn1 b
      refine ⟨H2π (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) c, ?_⟩
      rw [trivH2Map_H2π, hc]

end Work.GroupCohomology
