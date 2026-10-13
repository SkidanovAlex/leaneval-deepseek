/-
  WilC5 / S4ExpF — bridge facts between the `LEc` symbols and the field operations.

  In the `S4ExpF` development one works with a field `K` carrying an `LEc`-structure, a
  `rexpL`-structure and real constants, together with the hypotheses

      `hadd : addE x y = x + y`,  `hmul : mulE x y = x * y`,
      `hone : oneE = 1`,          `hleneg : leE x y ↔ x ≤ y`

  (which say that the *given* `LEc`- and `rexpL`-structures agree with the field data) and the
  model hypothesis `hTE : K ⊨ TE`.  The ring symbols `zeroE`, `negE` (hence `subE`) of `LEc` are
  *not* among those hypotheses, so this module puts them in the same normal form by transferring
  the corresponding `TE`-sentences from `ℝ` (`Work.WilC5.transfer`, `ReductEmb.lean`).

  The main outputs are `zeroE_eq_zero`, `negE_eq_neg`, `subE_eq_sub`, `leE_zero_iff` (the
  `LEc`-order `leE zeroE x ∧ ¬ leE x zeroE` is the field order) and `absLeOne_iff_abs` (the ring
  formula `|x| ≤ 1` is the field condition `|x| ≤ 1`).
-/
import Mathlib
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.expE_add_of_model

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open Classical

namespace Work.WilC5.S4ExpF

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

section Bridge

variable {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    [rexpL.Structure K] [(constantsOn ℝ).Structure K]

/-- **`exp 0 = 1` in a model of `TE`** (transferred from `ℝ`). -/
theorem expE_zeroE_of_model (hM : K ⊨ TE) : expE (zeroE : K) = oneE := by
  have h := transfer hM dmExpZeroForm (fun xs => expZeroForm_real xs)
  exact (dmExpZeroForm_realize (emptyVar : Empty → K) (default : Fin 0 → K)).mp (h default)

/-- **`0` is the additive identity in a model of `TE`** (transferred from `ℝ`). -/
theorem addE_zeroE_of_model (hM : K ⊨ TE) (x : K) : addE (zeroE : K) x = x := by
  have h := transfer hM (φ := (Term.bdEqual (eAdd eZero (v1 0)) (v1 0)))
    (fun xs : Fin 1 → ℝ => by
      rw [BoundedFormula.realize_bdEqual]
      simp only [v1, Term.realize_var, Sum.elim_inr, realize_eAdd, realize_eZero, addE_real,
        zeroE_real, zero_add]) ![x]
  rw [BoundedFormula.realize_bdEqual] at h
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eAdd, realize_eZero] at h
  exact h

/-- **`x + (-x) = 0` in a model of `TE`** (transferred from `ℝ`). -/
theorem addE_negE_of_model (hM : K ⊨ TE) (x : K) : addE x (negE x) = zeroE := by
  have h := transfer hM (φ := (Term.bdEqual (eAdd (v1 0) (eNeg (v1 0))) eZero))
    (fun xs : Fin 1 → ℝ => by
      rw [BoundedFormula.realize_bdEqual]
      simp only [v1, Term.realize_var, Sum.elim_inr, realize_eAdd, realize_eNeg, realize_eZero,
        addE_real, negE_real, zeroE_real, add_neg_cancel]) ![x]
  rw [BoundedFormula.realize_bdEqual] at h
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eAdd, realize_eNeg, realize_eZero] at h
  exact h

/-- The `LEc`-zero of `K` is the field zero. -/
theorem zeroE_eq_zero (hTE : K ⊨ TE) (hadd : ∀ x y : K, addE x y = x + y) :
    (zeroE : K) = 0 := by
  have h := addE_zeroE_of_model hTE (0 : K)
  rw [hadd] at h
  simpa using h

/-- The `LEc`-negation of `K` is the field negation. -/
theorem negE_eq_neg (hTE : K ⊨ TE) (hadd : ∀ x y : K, addE x y = x + y) (x : K) :
    negE x = -x := by
  have h := addE_negE_of_model hTE x
  rw [hadd, zeroE_eq_zero hTE hadd] at h
  exact eq_neg_of_add_eq_zero_right h

/-- The `LEc`-subtraction of `K` is the field subtraction. -/
theorem subE_eq_sub (hTE : K ⊨ TE) (hadd : ∀ x y : K, addE x y = x + y) (x y : K) :
    subE x y = x - y := by
  rw [subE, hadd, negE_eq_neg hTE hadd]
  ring

/-- The `LEc`-order `leE zeroE · ∧ ¬ leE · zeroE` is the field strict order `0 < ·`. -/
theorem leE_zero_iff (hTE : K ⊨ TE) (hadd : ∀ x y : K, addE x y = x + y)
    (hleneg : ∀ x y : K, leE x y ↔ x ≤ y) (x : K) :
    (leE zeroE x ∧ ¬ leE x zeroE) ↔ 0 < x := by
  have h0 := zeroE_eq_zero hTE hadd
  rw [hleneg zeroE x, hleneg x zeroE, h0]
  constructor
  · rintro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 (fun he => h2 (le_of_eq he.symm))
  · intro h
    exact ⟨le_of_lt h, not_le.mpr h⟩

/-- The ring formula `|x| ≤ 1` (`absLeOne`) is the field condition `|x| ≤ 1`. -/
theorem absLeOne_iff_abs (hTE : K ⊨ TE) (hadd : ∀ x y : K, addE x y = x + y)
    (hone : (oneE : K) = 1) (hleneg : ∀ x y : K, leE x y ↔ x ≤ y) (x : K) :
    absLeOne x ↔ |x| ≤ 1 := by
  have hn : ∀ y : K, negE y = -y := negE_eq_neg hTE hadd
  have hs : ∀ y z : K, subE y z = y - z := subE_eq_sub hTE hadd
  have hinv1 : (x ≤ oneE) ↔ (x ≤ 1) := by rw [hone]
  have hinv2 : (negE oneE ≤ x) ↔ (-1 ≤ x) := by rw [hn oneE, hone]
  have h1 : isSquare (subE oneE x) ↔ x ≤ oneE := by rw [← hleneg x oneE, leE]
  have h2 : isSquare (addE oneE x) ↔ negE oneE ≤ x := by
    have hkey : subE x (negE oneE) = addE oneE x := by
      rw [hs, hn, hadd]; ring
    rw [← hkey, ← hleneg (negE oneE) x, leE]
  rw [absLeOne, h1, h2, hinv1, hinv2, abs_le]
  constructor
  · rintro ⟨hA, hB⟩; exact ⟨hB, hA⟩
  · rintro ⟨hA, hB⟩; exact ⟨hB, hA⟩

end Bridge

end Work.WilC5.S4ExpF
