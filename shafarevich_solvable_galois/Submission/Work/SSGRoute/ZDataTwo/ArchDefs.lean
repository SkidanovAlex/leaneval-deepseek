import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.InvAux
import Submission.Work.SSGRoute.ZDataTwo.ArchKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the archimedean count `arch_sum_eq_badRealSum`

This file collects the definitions and elementary lemmas shared by the archimedean side of the
`p = 2` reciprocity: the sign predicate `IsNegAt` at an infinite place of a number field (used for
the count of the real places at which an element is negative), and the dictionary between the
Kummer character of `a ∈ kˣ` at an involution `c` of `Gal(Ω/k)` and the norm set of `c` (i.e. the
positivity of `a` in the real closed fixed field `Ω^c`).

The main theorem these serve is `Work.SSGRoute.ZDataTwo.arch_sum_eq_badRealSum`: the sum of the
archimedean local invariants `χ_α(c) χ_β(c)` over a transversal `C'` of the conjugacy classes of
the involutions of `G_k` is the number of real places of `k` at which `β` is not a local norm from
`k(√α)`.
-/

set_option linter.unusedSectionVars false

namespace Work.SSGRoute.ZDataTwo

open NumberField

/-! ## The sign of a unit at an infinite place -/

variable {k : Type} [Field k] [NumberField k]

/-- **`a : kˣ` is negative at the infinite place `w`**: `w` is real and the image of `a` under the
real embedding attached to `w` is `< 0`.  (The conjunct `w.IsReal` is part of the definition so that
the predicate is `False` at a complex place, even for elements of `k` which happen to have a real
image under the complex embedding.) -/
def IsNegAt (w : NumberField.InfinitePlace k) (a : kˣ) : Prop :=
  ∃ hw : w.IsReal, NumberField.InfinitePlace.embedding_of_isReal hw (a : k) < 0

lemma IsNegAt.isReal {w : NumberField.InfinitePlace k} {a : kˣ} (h : IsNegAt w a) : w.IsReal :=
  h.1

/-- The real embedding attached to a real infinite place does not depend on the proof of
realness. -/
lemma embedding_of_isReal_eq {w : NumberField.InfinitePlace k} (hw hw' : w.IsReal) :
    NumberField.InfinitePlace.embedding_of_isReal hw
      = NumberField.InfinitePlace.embedding_of_isReal hw' := by
  ext x
  apply Complex.ofReal_injective
  rw [NumberField.InfinitePlace.embedding_of_isReal_apply]

lemma isNegAt_iff {w : NumberField.InfinitePlace k} (hw : w.IsReal) (a : kˣ) :
    IsNegAt w a ↔ NumberField.InfinitePlace.embedding_of_isReal hw (a : k) < 0 := by
  constructor
  · intro h
    rw [← embedding_of_isReal_eq h.1 hw]
    exact h.2
  · intro h
    exact ⟨hw, h⟩

/-- At a real place, `a` is *not* negative exactly when it is positive. -/
lemma not_isNegAt_iff {w : NumberField.InfinitePlace k} (hw : w.IsReal) (a : kˣ) :
    ¬ IsNegAt w a ↔ 0 < NumberField.InfinitePlace.embedding_of_isReal hw (a : k) := by
  rw [isNegAt_iff hw]
  have hne : NumberField.InfinitePlace.embedding_of_isReal hw (a : k) ≠ 0 := fun h =>
    a.ne_zero ((NumberField.InfinitePlace.embedding_of_isReal hw).injective (by rw [h, map_zero]))
  rw [not_lt]
  exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hne), fun h => le_of_lt h⟩

lemma isNegAt_neg_one {w : NumberField.InfinitePlace k} (hw : w.IsReal) :
    IsNegAt w (-1 : kˣ) := by
  refine ⟨hw, ?_⟩
  rw [show ((-1 : kˣ) : k) = -((1 : kˣ) : k) by simp, map_neg, show ((1 : kˣ) : k) = 1 by simp,
    map_one]
  norm_num

lemma isNegAt_neg_one_iff {w : NumberField.InfinitePlace k} :
    IsNegAt w (-1 : kˣ) ↔ w.IsReal :=
  ⟨IsNegAt.isReal, isNegAt_neg_one⟩

/-! ## Some easy facts about `ZMod 2` -/

lemma zmodTwo_mul_eq_one {x y : ZMod 2} (h : x * y = 1) : x = 1 ∧ y = 1 := by
  revert h
  revert x y
  decide

lemma zmodTwo_eq_zero_or_eq_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

lemma zmodTwo_eq_one_of_ne_zero' {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (zmodTwo_eq_zero_or_eq_one x).resolve_left h

lemma zmodTwo_eq_one_iff_ne_zero (x : ZMod 2) : x = 1 ↔ x ≠ 0 := by
  refine ⟨fun h => by rw [h]; decide, fun h => zmodTwo_eq_one_of_ne_zero' h⟩

lemma zmodTwo_eq_zero_iff_ne_one (x : ZMod 2) : x = 0 ↔ x ≠ 1 := by
  constructor
  · intro h h1; rw [h] at h1; exact zero_ne_one h1
  · intro h
    rcases zmodTwo_eq_zero_or_eq_one x with h0 | h1
    · exact h0
    · exact absurd h1 h

/-! ## The Kummer character of a unit at an element of `Gal(Ω/k)` -/

variable {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- The Kummer character of `1 ∈ Ω ≃ₐ[k] Ω` vanishes. -/
lemma kummerChar_one (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (a : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a (1 : Ω ≃ₐ[k] Ω) = 0 := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω (a : k))
    (by norm_num : (0 : ℕ) < 2)
  refine (Work.SSGRoute.kummerChar_eq_zero_iff_exists_sqrt_fixed (K := k) (Ω := Ω) ζ hζ a
    (1 : Ω ≃ₐ[k] Ω)).mpr ⟨y, rfl, ?_⟩
  rw [pow_two] at hy ⊢
  exact hy

/-- The Kummer character of `a` is invariant under conjugation in `Gal(Ω/k)`. -/
lemma kummerChar_conj (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (a : kˣ)
    (c σ : Ω ≃ₐ[k] Ω) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a (σ * c * σ⁻¹) =
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c := by
  have h2 : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a σ +
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a σ⁻¹ = 0 := by
    rw [← Work.SSGRoute.kummerChar_mul_apply (K := k) (Ω := Ω) ζ hζ a σ σ⁻¹,
      mul_inv_cancel, kummerChar_one]
  calc Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a (σ * c * σ⁻¹)
      = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a (σ * (c * σ⁻¹)) := by
        rw [mul_assoc]
    _ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a σ +
          Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a (c * σ⁻¹) :=
        Work.SSGRoute.kummerChar_mul_apply (K := k) (Ω := Ω) ζ hζ a σ (c * σ⁻¹)
    _ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a σ +
          (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c +
            Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a σ⁻¹) := by
        rw [Work.SSGRoute.kummerChar_mul_apply (K := k) (Ω := Ω) ζ hζ a c σ⁻¹]
    _ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c := by
        rw [add_comm (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c)
          (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a σ⁻¹),
          ← add_assoc, h2, zero_add]

/-- **The dictionary between the Kummer character and the norm set.**  For an involution `c` of
`Gal(Ω/k)`, the Kummer character of `a ∈ kˣ` at `c` vanishes exactly when `a` lies in the norm set
of `c` — equivalently, when `a` is a square in the real closed fixed field `Ω^c`, i.e. when `a` is
positive for the ordering of `Ω^c`. -/
theorem kummerChar_eq_zero_iff_mem_normSet (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (a : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
      algebraMap k Ω (a : k) ∈ Work.SSGRoute.TwoTorsion.normSet c.toRingEquiv := by
  constructor
  · intro h
    obtain ⟨y, hy, hy2⟩ :=
      (Work.SSGRoute.kummerChar_eq_zero_iff_exists_sqrt_fixed (K := k) (Ω := Ω) ζ hζ a c).mp h
    have hy0 : y ≠ 0 := by
      intro h0
      have h' : algebraMap k Ω (a : k) = 0 := by rw [← hy2, h0, zero_pow (by norm_num : 2 ≠ 0)]
      exact a.ne_zero ((algebraMap k Ω).injective (by simpa using h'))
    refine ⟨y, hy0, ?_⟩
    show algebraMap k Ω (a : k) = y * c.toRingEquiv y
    rw [show (c : Ω → Ω) = c.toRingEquiv from rfl] at hy
    rw [← hy2, hy, pow_two]
  · intro h
    have hc' : c.toRingEquiv * c.toRingEquiv = 1 := by
      rw [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl]
      have h2 : (c * c : Ω ≃ₐ[k] Ω) = 1 := by rw [← pow_two, hc]
      exact_mod_cast congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω ≃+* Ω)) h2
    obtain ⟨m, hm, hm0, hm2⟩ := Work.SSGRoute.TwoTorsion.exists_fixed_sq_of_mem_normSet hc' h
    refine (Work.SSGRoute.kummerChar_eq_zero_iff_exists_sqrt_fixed (K := k) (Ω := Ω)
      ζ hζ a c).mpr ⟨m, ?_, ?_⟩
    · show (c : Ω → Ω) m = m
      rw [show (c : Ω → Ω) = c.toRingEquiv from rfl]
      exact hm
    · rw [hm2, pow_two]

/-- The complement form of `kummerChar_eq_zero_iff_mem_normSet`. -/
theorem kummerChar_eq_one_iff_not_mem_normSet (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (a : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 1 ↔
      algebraMap k Ω (a : k) ∉ Work.SSGRoute.TwoTorsion.normSet c.toRingEquiv := by
  constructor
  · intro h hmem
    rw [(kummerChar_eq_zero_iff_mem_normSet ζ hζ c hc a).mpr hmem] at h
    exact zero_ne_one h
  · intro h
    exact zmodTwo_eq_one_of_ne_zero'
      (fun h0 => h ((kummerChar_eq_zero_iff_mem_normSet ζ hζ c hc a).mp h0))

end Work.SSGRoute.ZDataTwo
