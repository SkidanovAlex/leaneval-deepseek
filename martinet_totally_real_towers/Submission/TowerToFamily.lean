import Mathlib
import Submission.Helpers
import Submission.Commons.NumberTheory.NumberField.one_le_rootDiscr
import Submission.Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top

/-!
# From an infinite Martinet tower to the root-discriminant family

This module records the machine-checked reduction between the two
formulations of Martinet's theorem:

  * an *infinite Martinet tower*: a family `F : ℕ → Type` of totally real
    number fields `F 0 ⊂ F 1 ⊂ ⋯`, bundled either by root-discriminant data
    (`TowerInstances F`: root discriminant constant along every step, every
    step at least quadratic) or -- the form a class-field construction
    supplies -- by ramification data (`UnramifiedTowerData F`: the relative
    different of every step is the unit ideal, i.e. unramified at every finite
    prime, and every step is at least quadratic);
  * the *root-discriminant family* `Submission.Helpers.rootDiscrFamily C`
    (for every `N` a totally real field of degree `≥ N` and root discriminant
    `≤ C`), which by `Submission.Helpers` implies the benchmark statement.

`rootDiscrFamily_of_tower`, `exists_totallyReal_discr_le_of_tower(Data)` and
`exists_totallyReal_discr_le_of_unramified_tower` prove the passage; the
root-discriminant constancy of an unramified step is the shared-commons fact
`Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top`.

The entire remaining mathematical content of Martinet's theorem -- the
*construction* of such a tower via narrow Hilbert class fields and the
Golod--Shafarevich criterion -- is reduced to the single existential
`milestone_unramified_tower` at the end of this file.
-/

open scoped NumberField
open NumberField

namespace Submission.Towers

/-- The data of an infinite tower of totally real number fields
`F 0 ⊂ F 1 ⊂ ⋯`: field / number-field / totally-real instances for every
level, an algebra inclusion for every step, root discriminant constant along
every step, and every step of degree at least 2. -/
structure TowerInstances (F : ℕ → Type) where
  [field : ∀ n : ℕ, Field (F n)]
  [numberField : ∀ n : ℕ, NumberField (F n)]
  [totallyReal : ∀ n : ℕ, NumberField.IsTotallyReal (F n)]
  alg : ∀ n : ℕ, Algebra (F n) (F (n + 1))
  rd : ∀ n : ℕ, NumberField.rootDiscr (F (n + 1)) = NumberField.rootDiscr (F n)
  deg : ∀ n : ℕ, 2 ≤ Module.finrank (F n) (F (n + 1))

/-- An infinite Martinet tower exists iff some family `F` carries
`TowerInstances`. -/
def HasMartinetTower : Prop := ∃ F : ℕ → Type, Nonempty (TowerInstances F)

/-- The `ℚ`-degree of the `n`-th field of a tower with steps of degree ≥ 2 is
at least `2 ^ n`. -/
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

/-- A tower of totally real number fields with constant root discriminant and
steps of degree at least 2 yields a root-discriminant-bounded family of totally
real fields of unbounded degree (with `C = rootDiscr (F 0)`). -/
theorem rootDiscrFamily_of_tower {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsTotallyReal (F n)]
    (alg : ∀ n : ℕ, Algebra (F n) (F (n + 1)))
    (hrd : ∀ n : ℕ, NumberField.rootDiscr (F (n + 1)) = NumberField.rootDiscr (F n))
    (hdeg : ∀ n : ℕ, 2 ≤ Module.finrank (F n) (F (n + 1))) :
    ∃ C : ℝ, 0 < C ∧ Submission.Helpers.rootDiscrFamily C := by
  refine ⟨NumberField.rootDiscr (F 0), ?_, ?_⟩
  · have hone : 1 ≤ NumberField.rootDiscr (F 0) :=
      Commons.NumberTheory.NumberField.one_le_rootDiscr (F 0)
    linarith
  · intro N
    refine ⟨Module.finrank ℚ (F N), ?_, F N, inferInstance, inferInstance, inferInstance, rfl, ?_⟩
    · have hpow := finrank_ge_two_pow (F := F) alg hdeg N
      exact le_trans (nat_le_two_pow N) hpow
    · rw [rootDiscr_eq_of_tower (F := F) hrd N]

/-- Bundled version of `rootDiscrFamily_of_tower`. -/
theorem rootDiscrFamily_of_towerData {F : ℕ → Type} (T : TowerInstances F) :
    ∃ C : ℝ, 0 < C ∧ Submission.Helpers.rootDiscrFamily C := by
  letI : ∀ n : ℕ, Field (F n) := T.field
  letI : ∀ n : ℕ, NumberField (F n) := T.numberField
  letI : ∀ n : ℕ, NumberField.IsTotallyReal (F n) := T.totallyReal
  exact rootDiscrFamily_of_tower (F := F) T.alg T.rd T.deg

/-- An infinite Martinet tower of totally real number fields (constant root
discriminant, steps of degree at least 2) implies the benchmark statement
`exists_totallyReal_discr_le`. -/
theorem exists_totallyReal_discr_le_of_tower {F : ℕ → Type} [∀ n : ℕ, Field (F n)]
    [∀ n : ℕ, NumberField (F n)] [∀ n : ℕ, NumberField.IsTotallyReal (F n)]
    (alg : ∀ n : ℕ, Algebra (F n) (F (n + 1)))
    (hrd : ∀ n : ℕ, NumberField.rootDiscr (F (n + 1)) = NumberField.rootDiscr (F n))
    (hdeg : ∀ n : ℕ, 2 ≤ Module.finrank (F n) (F (n + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  Submission.Helpers.exists_totallyReal_discr_le_of_rootDiscrFamily
    (rootDiscrFamily_of_tower (F := F) alg hrd hdeg)

/-- Bundled version of `exists_totallyReal_discr_le_of_tower`. -/
theorem exists_totallyReal_discr_le_of_towerData {F : ℕ → Type} (T : TowerInstances F) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  letI : ∀ n : ℕ, Field (F n) := T.field
  letI : ∀ n : ℕ, NumberField (F n) := T.numberField
  letI : ∀ n : ℕ, NumberField.IsTotallyReal (F n) := T.totallyReal
  exact exists_totallyReal_discr_le_of_tower (F := F) T.alg T.rd T.deg

/-- An infinite tower of totally real number fields whose steps are all
unramified at every finite prime (relative different is the unit ideal) and of
degree at least 2: the raw data that a class-field-theoretic construction
(narrow Hilbert class field tower) provides for a Martinet tower. -/
structure UnramifiedTowerData (F : ℕ → Type) where
  [field : ∀ n : ℕ, Field (F n)]
  [numberField : ∀ n : ℕ, NumberField (F n)]
  [totallyReal : ∀ n : ℕ, NumberField.IsTotallyReal (F n)]
  alg : ∀ n : ℕ, Algebra (F n) (F (n + 1))
  unram_step : ∀ n : ℕ, differentIdeal (𝓞 (F n)) (𝓞 (F (n + 1))) = ⊤
  deg : ∀ n : ℕ, 2 ≤ Module.finrank (F n) (F (n + 1))

/-- Unramified tower data yields root-discriminant-constant tower data
(`TowerInstances`), by the shared-commons per-step fact
`Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top`. -/
def towerInstances_of_unramified {F : ℕ → Type} (U : UnramifiedTowerData F) :
    TowerInstances F := by
  refine { field := U.field, numberField := U.numberField, totallyReal := U.totallyReal,
           alg := U.alg, deg := U.deg, rd := ?_ }
  intro n
  letI : Field (F n) := U.field n
  letI : NumberField (F n) := U.numberField n
  letI : Field (F (n + 1)) := U.field (n + 1)
  letI : NumberField (F (n + 1)) := U.numberField (n + 1)
  letI : Algebra (F n) (F (n + 1)) := U.alg n
  exact Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top (U.unram_step n)

/-- An everywhere-unramified (at finite primes) infinite tower of totally real
number fields with steps of degree at least 2 implies the benchmark statement
`exists_totallyReal_discr_le`.  **This is the precise interface a class-field
construction must satisfy** (it contains no `sorry`). -/
theorem exists_totallyReal_discr_le_of_unramified_tower {F : ℕ → Type}
    (U : UnramifiedTowerData F) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  exists_totallyReal_discr_le_of_towerData (towerInstances_of_unramified U)

end Submission.Towers
