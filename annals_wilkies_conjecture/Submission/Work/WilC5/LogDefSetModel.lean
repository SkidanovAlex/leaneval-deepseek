/-
  WilC5 — `logDefSet` is the graph of a total function in every model of `TE`.

  `logDefSet x y` says "`y = log x`" using only the `LEc` vocabulary:

      `(0 < x ∧ exp y = x) ∨ (¬ 0 < x ∧ exp y = 1)`,

  where `0 < x` is the definable order `leE zeroE x ∧ ¬ leE x zeroE` (`leE x y := ∃z, z*z = y - x`).
  This module proves that in every model `M` of `TE = Th(ℝ_exp)` and for every `x : M` there is
  *exactly one* `y` with `logDefSet x y`.

  The three facts used are all `LEc`-sentences true in `ℝ`, hence in every model of `TE`:

  * `exp 0 = 1`             (so the second clause has the witness `y = 0` when `0 < x` fails),
  * injectivity of `exp`    (so each clause has *at most* one solution),
  * surjectivity of `exp` onto the positive elements (`0 < x → ∃ y, exp y = x`).

  The transfer from `ℝ` to an arbitrary model of `TE` is `Work.WilC5.transfer`
  (`Submission/Work/WilC5/ReductEmb.lean`), which packages the elementarity argument: `TE` is the
  complete theory of the standard structure, so any sentence true in `ℝ` holds in `M`.
-/
import Mathlib
import Submission.Work.WilC5.ExpLog

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The three `LEc`-sentences and their realization -/

section Formulas

variable {M : Type} [LEc.Structure M]

/-- `exp 0 = 1`, as a formula with no free and no bound variables. -/
def dmExpZeroForm : LEc.BoundedFormula Empty 0 :=
  Term.bdEqual (eExp (eZero : LEc.Term (Empty ⊕ Fin 0))) (eOne : LEc.Term (Empty ⊕ Fin 0))

theorem dmExpZeroForm_realize (v : Empty → M) (xs : Fin 0 → M) :
    dmExpZeroForm.Realize v xs ↔ expE (zeroE : M) = oneE := by
  rw [dmExpZeroForm, BoundedFormula.realize_bdEqual]
  simp

/-- Injectivity of `exp`, as a formula with two bound variables `x₀`, `x₁`. -/
def expInjForm : LEc.BoundedFormula Empty 2 :=
  (Term.bdEqual (eExp (v2 0)) (eExp (v2 1))).imp (Term.bdEqual (v2 0) (v2 1))

theorem expInjForm_realize (v : Empty → M) (xs : Fin 2 → M) :
    expInjForm.Realize v xs ↔ (expE (xs 0) = expE (xs 1) → xs 0 = xs 1) := by
  rw [expInjForm, BoundedFormula.realize_imp, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_bdEqual]
  simp [v2, Term.realize_var]

/-- The *definable* positivity predicate `0 < x`, as a formula with one bound variable. -/
def dmPosForm : LEc.BoundedFormula Empty 1 :=
  leForm (eZero : LEc.Term (Empty ⊕ Fin 1)) (v1 0) ⊓
    (leForm (v1 0) (eZero : LEc.Term (Empty ⊕ Fin 1))).not

theorem dmPosForm_realize (v : Empty → M) (xs : Fin 1 → M) :
    dmPosForm.Realize v xs ↔ leE zeroE (xs 0) ∧ ¬ leE (xs 0) zeroE := by
  rw [dmPosForm, BoundedFormula.realize_inf, BoundedFormula.realize_not, leForm_realize,
    leForm_realize]
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eZero, leE]

/-- `0 < x → ∃ y, exp y = x`, as a formula with one bound variable. -/
def expSurjForm : LEc.BoundedFormula Empty 1 :=
  dmPosForm.imp (Term.bdEqual (eExp (v2 1)) (v2 0)).ex

/-- Evaluation of `Fin.snoc` at the last index of `Fin 2` (the witness of `∃'`). -/
theorem snoc_fin2_one {N : Type} (xs : Fin 1 → N) (a : N) :
    (Fin.snoc xs a : Fin 2 → N) 1 = a := by
  have h := Fin.snoc_last (α := fun _ => N) a xs
  simpa using h

/-- Evaluation of `Fin.snoc` at the first index of `Fin 2`. -/
theorem snoc_fin2_zero {N : Type} (xs : Fin 1 → N) (a : N) :
    (Fin.snoc xs a : Fin 2 → N) 0 = xs 0 := by
  simp

theorem expSurjForm_realize (v : Empty → M) (xs : Fin 1 → M) :
    expSurjForm.Realize v xs ↔
      (leE zeroE (xs 0) ∧ ¬ leE (xs 0) zeroE → ∃ a : M, expE a = xs 0) := by
  rw [expSurjForm, BoundedFormula.realize_imp, dmPosForm_realize, BoundedFormula.realize_ex]
  constructor
  · intro h hh
    obtain ⟨a, ha⟩ := h hh
    exact ⟨a, by simpa only [BoundedFormula.realize_bdEqual, realize_eExp, v2, Term.realize_var,
      Sum.elim_inr, snoc_fin2_one, snoc_fin2_zero] using ha⟩
  · intro h hh
    obtain ⟨a, ha⟩ := h hh
    exact ⟨a, by simpa only [BoundedFormula.realize_bdEqual, realize_eExp, v2, Term.realize_var,
      Sum.elim_inr, snoc_fin2_one, snoc_fin2_zero] using ha⟩

end Formulas

/-! ## 2. The three sentences hold in `ℝ` -/

section Real

theorem expZeroForm_real (xs : Fin 0 → ℝ) :
    dmExpZeroForm.Realize (emptyVar : Empty → ℝ) xs := by
  rw [dmExpZeroForm_realize, expE_real, zeroE_real, oneE_real]
  exact Real.exp_zero

theorem expInjForm_real (xs : Fin 2 → ℝ) :
    expInjForm.Realize (emptyVar : Empty → ℝ) xs := by
  rw [expInjForm_realize]
  intro h
  exact Real.exp_injective h

theorem expSurjForm_real (xs : Fin 1 → ℝ) :
    expSurjForm.Realize (emptyVar : Empty → ℝ) xs := by
  rw [expSurjForm_realize]
  rintro ⟨h1, h2⟩
  have hpos : 0 < xs 0 := by
    simp only [leE, subE_real, zeroE_real, isSquare_real] at h1 h2
    linarith
  exact ⟨Real.log (xs 0), by rw [expE_real, Real.exp_log hpos]⟩

end Real

/-! ## 3. The main theorem -/

theorem LogDefSetModel {M : Type} [WilkiesDesign.CG.LEc.Structure M]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE) (x : M) :
    ∃! y : M, Work.WilC5.logDefSet x y := by
  -- the three facts, transferred from `ℝ`
  have h0 : expE (zeroE : M) = oneE := by
    have h := transfer hM dmExpZeroForm (fun xs => expZeroForm_real xs)
    exact (dmExpZeroForm_realize (emptyVar : Empty → M) (emptyBnd : Fin 0 → M)).mp (h emptyBnd)
  have hinj : ∀ a b : M, expE a = expE b → a = b := by
    intro a b hab
    have h := transfer hM expInjForm (fun xs => expInjForm_real xs)
    have hh := h ![a, b]
    rw [expInjForm_realize] at hh
    exact hh (by simpa using hab)
    -- `simpa` removes the `Fin.cons` scaffolding of `![a, b]`
  have hsurj : ∀ a : M, leE zeroE a ∧ ¬ leE a zeroE → ∃ b : M, expE b = a := by
    intro a ha
    have h := transfer hM expSurjForm (fun xs => expSurjForm_real xs)
    have hh := h ![a]
    rw [expSurjForm_realize] at hh
    exact hh (by simpa using ha)
  by_cases hx : leE zeroE x ∧ ¬ leE x zeroE
  · -- `0 < x`: the unique solution is the (transferred) logarithm of `x`
    obtain ⟨y, hy⟩ := hsurj x hx
    refine ⟨y, Or.inl ⟨hx, hy⟩, ?_⟩
    intro y' hy'
    rcases hy' with ⟨⟨h1, h2⟩, he⟩ | ⟨hne, he⟩
    · exact hinj y' y (by rw [he, hy])
    · exact absurd hx hne
  · -- `¬ 0 < x`: the unique solution is `0`
    refine ⟨zeroE, Or.inr ⟨hx, h0⟩, ?_⟩
    intro y' hy'
    rcases hy' with ⟨⟨h1, h2⟩, he⟩ | ⟨hne, he⟩
    · exact absurd ⟨h1, h2⟩ hx
    · exact hinj y' zeroE (by rw [he, h0])

end Work.WilC5
