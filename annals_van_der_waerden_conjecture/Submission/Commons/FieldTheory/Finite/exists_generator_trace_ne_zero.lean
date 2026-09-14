import Mathlib
import Submission.Commons.FieldTheory.Finite.count_generators_trace_zero_le
import Submission.Commons.FieldTheory.Finite.count_generators_trace_zero_le_char
import Submission.Commons.NumberTheory.totient_or_divisorCount_le

namespace Commons.FieldTheory.Finite

open Module

/-- The number of generators of `Fˣ` (elements of maximal order) is the totient of
`card F - 1`. -/
theorem card_generators_eq_totient {F : Type*} [Field F] [Fintype F] :
    Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1} = Nat.totient (Fintype.card F - 1) := by
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hcardF : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hcardU : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hset : Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1}
      = Nat.card {x : Fˣ // orderOf x = Nat.card Fˣ} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by rw [hcardU, hcardF])
  rw [hset]
  have hd : Nat.card Fˣ ∣ Fintype.card Fˣ := by rw [Nat.card_eq_fintype_card]
  have htot : (Finset.univ.filter (fun x : Fˣ => orderOf x = Nat.card Fˣ)).card
      = Nat.totient (Nat.card Fˣ) := by
    simpa using IsCyclic.card_orderOf_eq_totient (α := Fˣ) hd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Fˣ => orderOf x = Nat.card Fˣ)).card
    = Nat.totient (Fintype.card F - 1)
  rw [htot, hcardU, hcardF]

/-- The trace of a finite field extension of the prime field is not the zero form. -/
theorem trace_ne_zero_finite_field {F : Type*} [Field F] [Fintype F] (p : ℕ)
    [Fact (Nat.Prime p)] [Algebra (ZMod p) F] [CharP F p] :
    Algebra.trace (ZMod p) F ≠ 0 := by
  haveI : Module.Finite (ZMod p) F :=
    Module.Finite.of_fg_top ⟨Finset.univ, by rw [Finset.coe_univ, Submodule.span_univ]⟩
  haveI : PerfectField (ZMod p) := PerfectField.ofFinite
  haveI : Algebra.IsSeparable (ZMod p) F := inferInstance
  exact Algebra.trace_ne_zero (K := ZMod p) (L := F)

/-- If the bad set is strictly smaller than the number of generators, some generator has
nonzero trace. -/
theorem exists_generator_trace_ne_zero_of_bad_lt {F : Type*} [Field F] [Fintype F]
    (p : ℕ) [Fact (Nat.Prime p)] [Algebra (ZMod p) F] [CharP F p]
    (hbad : Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1 ∧
        Algebra.trace (ZMod p) F (x : F) = 0} < Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1}) :
    ∃ x : Fˣ, orderOf x = Fintype.card F - 1 ∧ Algebra.trace (ZMod p) F (x : F) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1}
      ≤ Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1 ∧
          Algebra.trace (ZMod p) F (x : F) = 0} := by
    apply Nat.card_le_card_of_injective
      (f := fun x : {x : Fˣ // orderOf x = Fintype.card F - 1} =>
        (⟨x.1, x.2, hcon x.1 x.2⟩ :
          {x : Fˣ // orderOf x = Fintype.card F - 1 ∧ Algebra.trace (ZMod p) F (x : F) = 0}))
    intro a b hab
    have : (a.1 : Fˣ) = (b.1 : Fˣ) := by
      simpa using congrArg (fun w : {x : Fˣ // orderOf x = Fintype.card F - 1 ∧
          Algebra.trace (ZMod p) F (x : F) = 0} => (w.1 : Fˣ)) hab
    exact Subtype.ext this
  omega

/-- Counting branch: if the number of generators exceeds the size of the trace-zero
hyperplane, we are done. -/
theorem exists_generator_trace_ne_zero_of_count {F : Type*} [Field F] [Fintype F]
    (p : ℕ) [Fact (Nat.Prime p)] [Algebra (ZMod p) F] [CharP F p]
    (hT : Algebra.trace (ZMod p) F ≠ 0)
    (hcount : p ^ (Module.finrank (ZMod p) F - 1) - 1 < Nat.totient (Fintype.card F - 1)) :
    ∃ x : Fˣ, orderOf x = Fintype.card F - 1 ∧ Algebra.trace (ZMod p) F (x : F) ≠ 0 := by
  have hbad := count_generators_trace_zero_le p hT
  apply exists_generator_trace_ne_zero_of_bad_lt p
  rw [card_generators_eq_totient]
  exact lt_of_le_of_lt hbad hcount

/-- Character-sum branch: if the divisor-count bound beats the totient, we are done. -/
theorem exists_generator_trace_ne_zero_of_char {F : Type*} [Field F] [Fintype F]
    (p : ℕ) [Fact (Nat.Prime p)] [Algebra (ZMod p) F] [CharP F p]
    (hchar : (Nat.divisors (Fintype.card F - 1)).card * (Nat.sqrt (Fintype.card F) + 1)
        < Nat.totient (Fintype.card F - 1)) :
    ∃ x : Fˣ, orderOf x = Fintype.card F - 1 ∧ Algebra.trace (ZMod p) F (x : F) ≠ 0 := by
  have hbad := count_generators_trace_zero_le_char (F := F) p
  apply exists_generator_trace_ne_zero_of_bad_lt p
  rw [card_generators_eq_totient]
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hX : (Nat.divisors (Fintype.card F - 1)).card * (Nat.sqrt (Fintype.card F) + 1)
      < Nat.totient (Fintype.card F - 1) := hchar
  have hlt : (Nat.totient (Fintype.card F - 1)
      + (p - 1) * (Nat.divisors (Fintype.card F - 1)).card
          * (Nat.sqrt (Fintype.card F) + 1)) / p
      < Nat.totient (Fintype.card F - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < p), Nat.mul_assoc]
    have h1 : (p - 1) * ((Nat.divisors (Fintype.card F - 1)).card * (Nat.sqrt (Fintype.card F) + 1))
        < (p - 1) * Nat.totient (Fintype.card F - 1) :=
      Nat.mul_lt_mul_of_pos_left hX (by omega)
    have h2 : Nat.totient (Fintype.card F - 1)
          + (p - 1) * ((Nat.divisors (Fintype.card F - 1)).card * (Nat.sqrt (Fintype.card F) + 1))
        < Nat.totient (Fintype.card F - 1)
          + (p - 1) * Nat.totient (Fintype.card F - 1) := Nat.add_lt_add_left h1 _
    have key : Nat.totient (Fintype.card F - 1)
          + (p - 1) * Nat.totient (Fintype.card F - 1)
        = Nat.totient (Fintype.card F - 1) * p := by
      conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ p by omega), Nat.mul_succ]
      rw [Nat.mul_comm (Nat.totient (Fintype.card F - 1)) (p - 1), Nat.add_comm]
    rwa [key] at h2
  exact lt_of_le_of_lt hbad hlt

theorem exists_generator_trace_ne_zero {F : Type*} [Field F] [Fintype F]
    (p : ℕ) [Fact (Nat.Prime p)] [Algebra (ZMod p) F] [CharP F p] :
    ∃ x : Fˣ, orderOf x = Fintype.card F - 1 ∧ Algebra.trace (ZMod p) F (x : F) ≠ 0 := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hT : Algebra.trace (ZMod p) F ≠ 0 := trace_ne_zero_finite_field p
  have hcard : Fintype.card F = p ^ Module.finrank (ZMod p) F := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := F), ZMod.card]
  have hkpos : 1 ≤ Module.finrank (ZMod p) F := by
    by_contra h
    push Not at h
    have h0 : Module.finrank (ZMod p) F = 0 := by omega
    rw [h0, pow_zero] at hcard
    have : Fintype.card F = 1 := hcard
    exact absurd (Fintype.card_le_one_iff.mp (le_of_eq this) 0 1) zero_ne_one
  rcases eq_or_lt_of_le hkpos with hk1 | hk2
  · -- degree 1: `p ^ 0 - 1 = 0 < φ (card F - 1)`
    apply exists_generator_trace_ne_zero_of_count p hT
    rw [hcard, ← hk1]
    simp only [pow_one, Nat.sub_self, pow_zero]
    have : 0 < Nat.totient (p - 1) := Nat.totient_pos.mpr (by omega)
    omega
  · -- degree ≥ 2
    rcases Commons.NumberTheory.totient_or_divisorCount_le (Fact.out : Nat.Prime p) hk2 with hcount | hchar
    · apply exists_generator_trace_ne_zero_of_count p hT
      rwa [hcard]
    · apply exists_generator_trace_ne_zero_of_char p
      rwa [hcard]

end Commons.FieldTheory.Finite
