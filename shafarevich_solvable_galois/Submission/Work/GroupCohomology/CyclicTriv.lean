/-
Copyright (c) 2025. All rights reserved.

# The transgression for cyclic groups with trivial coefficients

For `G = Multiplicative (ZMod n)` and coefficients `A` with the trivial action (`TrivMod G A`),
we set up the transgression

`trivT : C²(G, A) →+ A`,   `trivT c = ∑_{x : ZMod n} c (ofAdd x, s)`,

where `s = cycGen n = ofAdd 1` is the standard generator of `G`.

The two structural facts proved here are

* `trivT_d1 : trivT (d¹ f) = n • f s` (so `trivT` kills `B²` modulo `n • A`), whence the induced
  map `trivH2Map : H²(ℤ/n, A) →+ A/nA` (`trivH2Map`), the map that is proved to be an
  isomorphism in `Submission/Work/GroupCohomology/H2_cyclic_trivial.lean`;
* `trivT_eq_sum_range` and `sum_univ_zmod_eq_sum_range`, reindexing `∑_{x : ZMod n}` as a sum over
  `Finset.range n` (this is what makes the cocycle recursion of the companion file usable).

* `genSlice c x = c (x, s)`: the "generator slice" of a `2`-cochain; a `2`-cocycle with trivial
  coefficients is determined by its generator slice (`Work.GroupCohomology.eq_of_genSlice_eq`).
-/
import Mathlib
import Submission.Work.GroupCohomology.Basic
import Submission.Work.GroupCohomology.Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe v

namespace Work.GroupCohomology

open Multiplicative

variable (n : ℕ) [NeZero n]

/-- The standard generator `s = ofAdd 1` of the cyclic group `Multiplicative (ZMod n)`. -/
def cycGen : Multiplicative (ZMod n) := ofAdd (1 : ZMod n)

@[simp] theorem cycGen_def : cycGen n = ofAdd (1 : ZMod n) := rfl

/-- The generator slice `Φ c x = c (x, s)` of a `2`-cochain `c`. -/
def genSlice (A : Type v) [AddCommGroup A]
    (c : Multiplicative (ZMod n) × Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A) :
    ZMod n → TrivMod (Multiplicative (ZMod n)) A :=
  fun x => c (ofAdd x, cycGen n)

@[simp] theorem genSlice_apply (A : Type v) [AddCommGroup A]
    (c : Multiplicative (ZMod n) × Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A)
    (x : ZMod n) : genSlice n A c x = c (ofAdd x, cycGen n) := rfl

/-- The transgression `C²(G, A) →+ A`, `c ↦ ∑_{x : ZMod n} c (x, s)`. -/
noncomputable def trivT (A : Type v) [AddCommGroup A] :
    (Multiplicative (ZMod n) × Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A) →+
      TrivMod (Multiplicative (ZMod n)) A where
  toFun c := ∑ x : ZMod n, c (ofAdd x, cycGen n)
  map_zero' := by simp
  map_add' c c' := by simp [Finset.sum_add_distrib]

@[simp] theorem trivT_apply (A : Type v) [AddCommGroup A]
    (c : Multiplicative (ZMod n) × Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A) :
    trivT n A c = ∑ x : ZMod n, c (ofAdd x, cycGen n) := rfl

/-- Reindexing a sum over `ZMod n` as a sum over `Finset.range n` (via `ZMod.val`). -/
theorem sum_univ_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ZMod n → M) :
    (∑ x : ZMod n, F x) = ∑ m ∈ Finset.range n, F (m : ZMod n) := by
  refine Finset.sum_bij (fun (x : ZMod n) (_ : x ∈ Finset.univ) => x.val) ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.mpr x.val_lt
  · intro x _ y _ hxy; exact ZMod.val_injective n hxy
  · intro b hb
    refine ⟨(b : ZMod n), Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
  · intro x _
    rw [ZMod.natCast_zmod_val]

theorem trivT_eq_sum_range (A : Type v) [AddCommGroup A]
    (c : Multiplicative (ZMod n) × Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A) :
    trivT n A c = ∑ m ∈ Finset.range n, genSlice n A c (m : ZMod n) :=
  sum_univ_zmod_eq_sum_range n (genSlice n A c)

/-- The transgression of a coboundary: `τ (d¹ f) = n • f s`. -/
theorem trivT_d1 (A : Type v) [AddCommGroup A]
    (f : Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A) :
    trivT n A (d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) f) =
      n • f (cycGen n) := by
  have h1 : trivT n A (d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) f) =
      ∑ x : ZMod n, (f (cycGen n) - f (ofAdd x * cycGen n) + f (ofAdd x)) := by
    rw [trivT_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [d1_apply, TrivMod.smul_def]
  rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hshift : (∑ x : ZMod n, f (ofAdd x * cycGen n)) = ∑ x : ZMod n, f (ofAdd x) := by
    have := Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
      (fun y : ZMod n => f (ofAdd y))
    simpa [cycGen, ofAdd_add] using this
  rw [hshift]
  have hconst : (∑ _x : ZMod n, f (cycGen n)) = n • f (cycGen n) := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [hconst]
  abel

theorem trivT_d1_mem (A : Type v) [AddCommGroup A]
    (f : Multiplicative (ZMod n) → TrivMod (Multiplicative (ZMod n)) A) :
    trivT n A (d1 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) f) ∈
      nsmulRange n (TrivMod (Multiplicative (ZMod n)) A) :=
  ⟨f (cycGen n), (trivT_d1 n A f).symm⟩

/-- The map induced by the transgression on cohomology, `H²(ℤ/n, A) →+ A/nA`, `[c] ↦ [τ c]`. -/
noncomputable def trivH2Map (A : Type v) [AddCommGroup A] :
    H2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) →+
      (TrivMod (Multiplicative (ZMod n)) A ⧸
        nsmulRange n (TrivMod (Multiplicative (ZMod n)) A)) :=
  QuotientAddGroup.lift
    ((B2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)).comap
      (Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)).subtype)
    ((QuotientAddGroup.mk' (nsmulRange n (TrivMod (Multiplicative (ZMod n)) A))).comp
      ((trivT n A).comp
        (Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)).subtype))
    (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      have hx' : ((x : Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)) :
          Multiplicative (ZMod n) × Multiplicative (ZMod n) →
            TrivMod (Multiplicative (ZMod n)) A) ∈
          B2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) :=
        AddSubgroup.mem_comap.mp hx
      obtain ⟨f, hf⟩ := (mem_B2_iff (Multiplicative (ZMod n))
        (TrivMod (Multiplicative (ZMod n)) A)
        ((x : Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)) :
          Multiplicative (ZMod n) × Multiplicative (ZMod n) →
            TrivMod (Multiplicative (ZMod n)) A)).mp hx'
      have h2 : ((Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)).subtype x) =
          (↑x : Multiplicative (ZMod n) × Multiplicative (ZMod n) →
            TrivMod (Multiplicative (ZMod n)) A) := rfl
      rw [h2, ← hf]
      exact trivT_d1_mem n A f)

theorem trivH2Map_H2π (A : Type v) [AddCommGroup A]
    (c : Z2 (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A)) :
    trivH2Map n A (H2π (Multiplicative (ZMod n)) (TrivMod (Multiplicative (ZMod n)) A) c) =
      QuotientAddGroup.mk' (nsmulRange n (TrivMod (Multiplicative (ZMod n)) A)) (trivT n A c) := by
  rw [trivH2Map, H2π, QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk']
  rfl

end Work.GroupCohomology
