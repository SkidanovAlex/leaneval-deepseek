/-
**The involutions of `SU(3,2^n)`.**

The unipotent radical `U ≤ SU(3,2^n)` is a special `2`-group of order `q^3` (`q = 2^n`): an
element `u(b,c)` squares to `u(0, b^(q+1))`, so `u(b,c)^2 = 1` iff `b = 0`.  The elements
`u(0,c)` of `U` are exactly those with `c^q = c`; hence

  `#{x ∈ U : x² = 1} = q`, i.e. `U` has `q - 1` involutions,

by the commons lemma `Commons.FieldTheory.Finite.fixed_card_pow_two` counting the fixed field of
the Frobenius.  As in the Suzuki case, every involution of the Borel subgroup `B = U ⋊ T` lies
in `U` (the quotient `B/U ≅ T` has odd order), so
`#{involutions of B} = q - 1`, and the Bender counting theorem gives

  `#{involutions of SU(3,q)} = [SU(3,q) : B] · (q - 1) = (q³ + 1)(q - 1)`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.SuzukiCondition
import Submission.Work.Models.Port.PSU3.Sylow
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_of_sq_eq_one_of_odd_index
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul
import Submission.Work.Models.Port.Commons.GroupTheory.OrderOfElement.card_orderOf_eq_two_eq_card_sq_eq_one_sub_one
import Submission.Work.Models.Port.Commons.FieldTheory.Finite.fixed_card_pow_two
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.normalizer_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.PSU3

/-! ## Elements of order `≤ 2` in the unipotent radical -/

lemma suUg_mul_self (n : ℕ) (b c : F n) :
    suUg n b c * suUg n b c = suUg n 0 (b ^ (2 ^ n + 1)) := by
  rw [suUg_mul, CharTwo.add_self_eq_zero b, CharTwo.add_self_eq_zero c, zero_add,
    ← pow_succ' b (2 ^ n)]

/-- `u(b,c)² = 1` iff `b = 0`: the involutions of the unipotent radical are the elements
`u(0,c)`. -/
lemma suUg_sq_eq_one_iff (n : ℕ) (b c : F n) : (suUg n b c) ^ 2 = 1 ↔ b = 0 := by
  rw [pow_two, suUg_mul_self]
  constructor
  · intro h
    have h1 : ((0 : F n), b ^ (2 ^ n + 1)) = ((0 : F n), (0 : F n)) :=
      suUg_injective n (h.trans (suUg_zero n).symm)
    have h0 : b ^ (2 ^ n + 1) = 0 := (Prod.ext_iff.mp h1).2
    by_contra hb
    exact pow_ne_zero _ hb h0
  · rintro rfl
    rw [zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), suUg_zero]

lemma suUg_zero_mem (n : ℕ) (c : F n) (hc : c ^ (2 ^ n) = c) : suUg n 0 c ∈ suU n := by
  refine ⟨0, c, ?_, rfl⟩
  rw [zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), hc, CharTwo.add_self_eq_zero c]

lemma suUg_zero_sq_psu (n : ℕ) (c : F n) (hc : c ^ (2 ^ n) = c) :
    (⟨suUg n 0 c, suUg_zero_mem n c hc⟩ : ↥(suU n)) ^ 2 = 1 := by
  refine Subtype.ext ?_
  show ((suUg n 0 c) ^ 2 : GL (Fin 3) (F n)) = 1
  rw [pow_two, suUg_mul_self, zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), suUg_zero]

/-- The elements of the unipotent radical squaring to `1` are exactly the `u(0,c)` with
`c` fixed by the Frobenius `x ↦ x^q`; there are `q = 2^n` of them. -/
lemma card_sq_eq_one_suU (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {x : ↥(suU n) // x ^ 2 = 1} = 2 ^ n := by
  have hmain : Nat.card {x : ↥(suU n) // x ^ 2 = 1} =
      Nat.card {c : F n // c ^ (2 ^ n) = c} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : {c : F n // c ^ (2 ^ n) = c} =>
        (⟨⟨suUg n 0 c.1, suUg_zero_mem n c.1 c.2⟩, suUg_zero_sq_psu n c.1 c.2⟩ :
          {x : ↥(suU n) // x ^ 2 = 1}))
      ⟨?_, ?_⟩).symm
    · intro c₁ c₂ h
      have h2 : (⟨suUg n 0 c₁.1, suUg_zero_mem n c₁.1 c₁.2⟩ : ↥(suU n)) =
          ⟨suUg n 0 c₂.1, suUg_zero_mem n c₂.1 c₂.2⟩ := Subtype.ext_iff.mp h
      have h3 : (suUg n 0 c₁.1 : GL (Fin 3) (F n)) = suUg n 0 c₂.1 := by
        simpa using congrArg Subtype.val h2
      have h4 : ((0, c₁.1) : F n × F n) = (0, c₂.1) :=
        suUg_injective n (show (fun p : F n × F n => suUg n p.1 p.2) (0, c₁.1) =
          (fun p : F n × F n => suUg n p.1 p.2) (0, c₂.1) from h3)
      exact Subtype.ext (Prod.ext_iff.mp h4).2
    · rintro ⟨y, hy⟩
      obtain ⟨b, c, hc, hybc⟩ := y.2
      have h1 : (suUg n b c) ^ 2 = 1 := by
        have h2 : (y : GL (Fin 3) (F n)) ^ 2 = 1 := by
          have h3 := Subtype.ext_iff.mp hy
          simpa using h3
        rwa [hybc] at h2
      have hb : b = 0 := (suUg_sq_eq_one_iff n b c).mp h1
      have hc' : c ^ (2 ^ n) = c := by
        have h4 : c + c ^ (2 ^ n) = 0 := by
          have h5 := hc
          rwa [hb, zero_pow (show 2 ^ n + 1 ≠ 0 by positivity)] at h5
        have h5 : c = -c ^ (2 ^ n) := eq_neg_of_add_eq_zero_left h4
        rw [CharTwo.neg_eq] at h5
        exact h5.symm
      refine ⟨⟨c, hc'⟩, Subtype.ext (Subtype.ext ?_)⟩
      show (suUg n 0 c : GL (Fin 3) (F n)) = (y : GL (Fin 3) (F n))
      rw [hybc, hb]
  rw [hmain]
  exact Commons.FieldTheory.Finite.fixed_card_pow_two n (by omega)

/-- The unipotent radical has `q - 1` involutions. -/
lemma card_orderOf_eq_two_suU (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {t : ↥(suU n) // orderOf t = 2} = 2 ^ n - 1 := by
  rw [Commons.GroupTheory.OrderOfElement.card_orderOf_eq_two_eq_card_sq_eq_one_sub_one
      (G := ↥(suU n)),
    card_sq_eq_one_suU n hn]

lemma card_orderOf_eq_two_suUS (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {t : ↥(suUS n) // orderOf t = 2} = 2 ^ n - 1 := by
  have e := Subgroup.subgroupOfEquivOfLe (suU_le_SU3 n)
  have h : Nat.card {t : ↥(suUS n) // orderOf t = 2} =
      Nat.card {t : ↥(suU n) // orderOf t = 2} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => ?_))
    have h1 : orderOf (e.toEquiv x) = orderOf x :=
      orderOf_injective (e : ↥(suUS n) →* ↥(suU n)) e.injective x
    constructor
    · intro hx
      rw [h1, hx]
    · intro hx
      rw [← h1, hx]
  rw [h, card_orderOf_eq_two_suU n hn]

/-! ## Involutions of the Borel subgroup -/

lemma card_suUS (n : ℕ) (hn : 1 ≤ n) : Nat.card ↥(suUS n) = 2 ^ (3 * n) := by
  rw [suUS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suU_le_SU3 n)).toEquiv, card_suU n hn]

lemma card_suBS (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(suBS n) = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) := by
  rw [suBS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suB_le_SU3 n)).toEquiv,
    card_suB n hn]

lemma suUS_le_normalizer_suUS_self (n : ℕ) (hn : 1 ≤ n) :
    suBS n ≤ Subgroup.normalizer (suUS n : Set (↥(SU3 n))) :=
  (normalizer_suUS n hn).ge

lemma suUS_subgroupOf_normal (n : ℕ) (hn : 1 ≤ n) :
    ((suUS n).subgroupOf (suBS n)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (suUS_le_suBS n)).mpr
    (suUS_le_normalizer_suUS_self n hn)

/-- The index of `U` in the Borel subgroup is `q² - 1`. -/
lemma suUS_subgroupOf_index (n : ℕ) (hn : 1 ≤ n) :
    ((suUS n).subgroupOf (suBS n)).index = 2 ^ (2 * n) - 1 := by
  have hcard : Nat.card ↥((suUS n).subgroupOf (suBS n)) = 2 ^ (3 * n) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suUS_le_suBS n)).toEquiv, suUS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (suU_le_SU3 n)).toEquiv, card_suU n hn]
  have hprod := Subgroup.index_mul_card ((suUS n).subgroupOf (suBS n))
  rw [hcard, card_suBS n hn] at hprod
  exact Nat.mul_right_cancel (pow_pos (by norm_num : (0 : ℕ) < 2) _)
    (by rw [hprod, mul_comm])

/-- An element of the Borel subgroup of `SU(3,2^n)` with `x² = 1` already lies in the
unipotent radical: `B/U ≅ T` has odd order. -/
lemma mem_suUS_of_sq_eq_one (n : ℕ) (hn : 1 ≤ n) {x : ↥(SU3 n)} (hxB : x ∈ suBS n)
    (hx : x * x = 1) : x ∈ suUS n := by
  haveI := suUS_subgroupOf_normal n hn
  have hx' : (⟨x, hxB⟩ : ↥(suBS n)) * (⟨x, hxB⟩ : ↥(suBS n)) = 1 := Subtype.ext hx
  exact Commons.GroupTheory.Subgroup.mem_of_sq_eq_one_of_odd_index
    ((suUS n).subgroupOf (suBS n))
    (by rw [suUS_subgroupOf_index n hn]
        exact odd_two_pow_sub_one (2 * n) (by omega)) hx'

lemma mem_suUS_of_orderOf_coe_eq_two (n : ℕ) (hn : 1 ≤ n) {x : ↥(SU3 n)}
    (hxB : x ∈ suBS n) (hx : orderOf (⟨x, hxB⟩ : ↥(suBS n)) = 2) : x ∈ suUS n := by
  have h2 : orderOf x = 2 := (Subgroup.orderOf_coe (⟨x, hxB⟩ : ↥(suBS n))).trans hx
  have h3 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  rw [h2] at h3
  refine mem_suUS_of_sq_eq_one n hn hxB ?_
  rw [← pow_two]
  exact h3

/-- The number of involutions of the Borel subgroup of `SU(3,2^n)` is `q - 1`. -/
lemma card_orderOf_eq_two_suBS (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {t : ↥(suBS n) // orderOf t = 2} = 2 ^ n - 1 := by
  have hkey : Nat.card {t : ↥(suBS n) // orderOf t = 2} =
      Nat.card {t : ↥(suUS n) // orderOf t = 2} := by
    refine le_antisymm ?_ ?_
    · let f : {t : ↥(suBS n) // orderOf t = 2} → {t : ↥(suUS n) // orderOf t = 2} :=
        fun t => ⟨⟨t.1.1, mem_suUS_of_orderOf_coe_eq_two n hn t.1.2 t.2⟩,
          ((Subgroup.orderOf_coe (⟨t.1.1, mem_suUS_of_orderOf_coe_eq_two n hn t.1.2 t.2⟩ :
              ↥(suUS n))).symm.trans ((Subgroup.orderOf_coe t.1).trans t.2))⟩
      refine Nat.card_le_card_of_injective f ?_
      intro a b hab
      have h1 : a.1.1 = b.1.1 := by
        have h2 : ((f a).1 : ↥(SU3 n)) = ((f b).1 : ↥(SU3 n)) :=
          congrArg (fun z : {t : ↥(suUS n) // orderOf t = 2} => (z.1 : ↥(SU3 n))) hab
        simpa [f] using h2
      exact Subtype.ext (Subtype.ext h1)
    · let g : {t : ↥(suUS n) // orderOf t = 2} → {t : ↥(suBS n) // orderOf t = 2} :=
        fun u => ⟨⟨u.1.1, suUS_le_suBS n u.1.2⟩,
          ((Subgroup.orderOf_coe (⟨u.1.1, suUS_le_suBS n u.1.2⟩ :
              ↥(suBS n))).symm.trans ((Subgroup.orderOf_coe u.1).trans u.2))⟩
      refine Nat.card_le_card_of_injective g ?_
      intro a b hab
      have h1 : a.1.1 = b.1.1 := by
        have h2 : ((g a).1 : ↥(SU3 n)) = ((g b).1 : ↥(SU3 n)) :=
          congrArg (fun z : {t : ↥(suBS n) // orderOf t = 2} => (z.1 : ↥(SU3 n))) hab
        simpa [g] using h2
      exact Subtype.ext (Subtype.ext h1)
  rw [hkey, card_orderOf_eq_two_suUS n hn]

/-- **The number of involutions of `SU(3,2^n)` is `(q³ + 1)(q - 1)`** with `q = 2^n`. -/
theorem card_involutions_SU3 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {t : ↥(SU3 n) // orderOf t = 2} = (2 ^ (3 * n) + 1) * (2 ^ n - 1) := by
  obtain ⟨hM, hEven, hOdd⟩ := suB_stronglyEmbedded n hn
  rw [Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul (suBS n) hM hEven hOdd,
    suBS_index_eq_one_add n hn, card_orderOf_eq_two_suBS n hn, card_suUS n hn, Nat.add_comm]

end Submission.PSU3
