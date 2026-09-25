import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.one_le_rootDiscr

/-! Helpers for the tower-to-family reduction, developed locally. -/

namespace TotallyRealBounded

/-- The `ℚ`-degree of the `n`-th field of a tower with steps of degree at least
2 is at least `2 ^ n`. -/
lemma finrank_ge_two_pow {F : ℕ → Type} [∀ n : ℕ, Field (F n)] [∀ n : ℕ, NumberField (F n)]
    (alg : ∀ n : ℕ, Algebra (F n) (F (n + 1)))
    (hdeg : ∀ n : ℕ, 2 ≤ Module.finrank (F n) (F (n + 1))) :
    ∀ n : ℕ, 2 ^ n ≤ Module.finrank ℚ (F n) := by
  intro n
  induction n with
  | zero =>
      have hpos : 0 < Module.finrank ℚ (F 0) := Module.finrank_pos (R := ℚ) (M := F 0)
      omega
  | succ n ih =>
      have hmul : Module.finrank ℚ (F (n + 1)) =
          Module.finrank ℚ (F n) * Module.finrank (F n) (F (n + 1)) := by
        exact (Module.finrank_mul_finrank (F := ℚ) (K := F n) (A := F (n + 1))).symm
      have hdeg' : 2 ≤ Module.finrank (F n) (F (n + 1)) := hdeg n
      have hm : 2 ^ n * 2 ≤ Module.finrank ℚ (F n) * Module.finrank (F n) (F (n + 1)) :=
        Nat.mul_le_mul ih hdeg'
      rw [pow_succ, hmul]
      exact hm

/-- Every natural `N` is at most `2 ^ N`. -/
lemma nat_le_two_pow (N : ℕ) : N ≤ 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h1 : 1 ≤ 2 ^ N := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) N)
      calc
        N + 1 ≤ 2 ^ N + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ N + 2 ^ N := Nat.add_le_add_left h1 (2 ^ N)
        _ = 2 * 2 ^ N := by rw [two_mul]
        _ = 2 ^ (N + 1) := by
          rw [pow_succ, mul_comm]

/-- Along a tower whose root discriminant is constant at every step, the root
discriminant of the `N`-th field equals that of the base `F 0`. -/
lemma rootDiscr_eq_of_tower {F : ℕ → Type} [∀ n : ℕ, Field (F n)] [∀ n : ℕ, NumberField (F n)]
    (hrd : ∀ n : ℕ, NumberField.rootDiscr (F (n + 1)) = NumberField.rootDiscr (F n)) (N : ℕ) :
    NumberField.rootDiscr (F N) = NumberField.rootDiscr (F 0) := by
  induction N with
  | zero => rfl
  | succ n ih => rw [hrd n, ih]

end TotallyRealBounded

namespace Commons.NumberTheory.NumberField

/-- An infinite tower of totally real number fields with constant root
discriminant along every step and steps of degree at least 2 yields a
constant `C > 0` (take `C = rootDiscr (F 0)`) such that for every `N` there
is a totally real number field of degree `≥ N` whose root discriminant is
`≤ C`.  This is the general "unbounded degree + bounded root discriminant"
content of Martinet's asymptotically-good totally real towers, extracted from
the tower data; the remaining class-field-theoretic task is only to construct
such an `F`.

A complete worked proof is in the local module
`Submission.TowerToFamily.lean` (namespace `Submission.Towers`:
`finrank_ge_two_pow`, `nat_le_two_pow`, `rootDiscr_eq_of_tower`,
`rootDiscrFamily_of_tower`); reuse its argument.  It uses
`Commons.NumberTheory.NumberField.one_le_rootDiscr` and the standard degree
identity `Module.finrank_mul_finrank`.  The degree lower bound `2 ^ n ≤
Module.finrank ℚ (F n)` is by induction with `Nat.mul_le_mul`; `N ≤ 2 ^ N`
follows from `Nat.lt_two_pow_self`. -/
theorem totallyReal_rootDiscr_bounded_of_tower {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsTotallyReal (F n)]
    (alg : ∀ n : ℕ, Algebra (F n) (F (n + 1)))
    (hrd : ∀ n : ℕ, NumberField.rootDiscr (F (n + 1)) = NumberField.rootDiscr (F n))
    (hdeg : ∀ n : ℕ, 2 ≤ Module.finrank (F n) (F (n + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : NumberField.IsTotallyReal K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C := by
  refine ⟨NumberField.rootDiscr (F 0), ?_, ?_⟩
  · have hone : 1 ≤ NumberField.rootDiscr (F 0) :=
      Commons.NumberTheory.NumberField.one_le_rootDiscr (F 0)
    linarith
  · intro N
    refine ⟨F N, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · have hpow := TotallyRealBounded.finrank_ge_two_pow (F := F) alg hdeg N
      exact le_trans (TotallyRealBounded.nat_le_two_pow N) hpow
    · rw [TotallyRealBounded.rootDiscr_eq_of_tower (F := F) hrd N]

end Commons.NumberTheory.NumberField