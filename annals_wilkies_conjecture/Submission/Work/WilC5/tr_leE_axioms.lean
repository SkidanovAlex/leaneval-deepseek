/-
  WilC5 — the definable order `leEL` of a model of `T_r` is a linear order.

  `LRc` has no relation symbols, so "the order" of a model `M` of `TR = Th(ℝ_rexp)` is the
  *definable* order

      `leEL x y  :=  ∃ z, z * z = y - x`      (`LRcOps.lean`),

  i.e. `y - x` is a square.  The point of this module is that, exactly as for the full
  exponential (`ReductEmb.lean`, where the same four axioms are transferred to models of `TE`),
  the four order axioms for `leEL` are *first-order sentences of `LRc` without parameters* which
  hold in `ℝ`; hence they hold in every model of `TR` by elementarity.

  This is the "ME0" input of the C5 specification (`Spec.lean`): the amalgamation arguments of
  vdDMM Lemmas 4.2–4.4 need `leEL` to be a linear order at each of the models involved.

  Concretely we build, for every model `M ⊨ TR`,

  * the four `LRc`-sentences `reflForm`, `antiForm`, `transForm`, `totForm` (universal closures
    of the corresponding ring formulas),
  * their realizations in `M` as the four requested statements about `leEL`,
  * and the transfer lemma `transfer_LRc`.

  The only place where the standard structure `ℝ` is used is `leEL_real` (the statement that
  on `ℝ` the definable order is the usual one), proved in `WilC5/leEL_real.lean`.
-/
import Mathlib
import Submission.Work.WilC5.LRcReduct
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.leEL_real

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. `LRc`-terms for the ring operations -/

/-- Addition as an `LRc`-term. -/
def tAddL {α : Type} (t₁ t₂ : LRc.Term α) : LRc.Term α :=
  Term.func (ringSymL Ring.addFunc) ![t₁, t₂]

/-- Multiplication as an `LRc`-term. -/
def tMulL {α : Type} (t₁ t₂ : LRc.Term α) : LRc.Term α :=
  Term.func (ringSymL Ring.mulFunc) ![t₁, t₂]

/-- Negation as an `LRc`-term. -/
def tNegL {α : Type} (t : LRc.Term α) : LRc.Term α :=
  Term.func (ringSymL Ring.negFunc) ![t]

/-- Subtraction as an `LRc`-term. -/
def tSubL {α : Type} (t₁ t₂ : LRc.Term α) : LRc.Term α := tAddL t₁ (tNegL t₂)

/-! ## 2. Realization of the `LRc`-term constructors -/

section RealizeTerms

variable {M : Type} [LRc.Structure M]

@[simp] theorem realize_tAddL {α : Type} (v : α → M) (t₁ t₂ : LRc.Term α) :
    Term.realize v (tAddL t₁ t₂) = addEL (Term.realize v t₁) (Term.realize v t₂) := by
  rw [tAddL, Term.realize_func, addEL]
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem realize_tMulL {α : Type} (v : α → M) (t₁ t₂ : LRc.Term α) :
    Term.realize v (tMulL t₁ t₂) = mulEL (Term.realize v t₁) (Term.realize v t₂) := by
  rw [tMulL, Term.realize_func, mulEL]
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem realize_tNegL {α : Type} (v : α → M) (t : LRc.Term α) :
    Term.realize v (tNegL t) = negEL (Term.realize v t) := by
  rw [tNegL, Term.realize_func, negEL]
  congr 1
  ext i
  fin_cases i
  rfl

@[simp] theorem realize_tSubL {α : Type} (v : α → M) (t₁ t₂ : LRc.Term α) :
    Term.realize v (tSubL t₁ t₂) = subEL (Term.realize v t₁) (Term.realize v t₂) := by
  rw [tSubL, subEL, realize_tAddL, realize_tNegL]

end RealizeTerms

/-! ## 3. The formula `∃z, z*z = t` — the `LRc` version

The witness `z` is the *last* bound variable of the formula (so that `ex` removes it); `t` is
pushed into the larger variable type by relabelling the bound variables along `Fin.castSucc`.
This is the `LRc` mirror of `Translate.lean`'s `witTerm`/`pushTerm` for `LEc`. -/

section QuantifierFree

/-- The witness `z`, as a term in the context with one more bound variable. -/
def witTermL {β : Type} {l : ℕ} : LRc.Term (β ⊕ Fin (l + 1)) := Term.var (Sum.inr (Fin.last l))

/-- Push a term into a context with one more bound variable at the end. -/
def pushTermL {β : Type} {l : ℕ} (t : LRc.Term (β ⊕ Fin l)) : LRc.Term (β ⊕ Fin (l + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

variable {M : Type} [LRc.Structure M]

@[simp] theorem realize_witTermL {β : Type} {l : ℕ} (w : β → M) (xs : Fin (l + 1) → M) :
    Term.realize (Sum.elim w xs) (witTermL (β := β) (l := l)) = xs (Fin.last l) := by
  rw [witTermL, Term.realize_var]
  rfl

@[simp] theorem realize_pushTermL {β : Type} {l : ℕ} (t : LRc.Term (β ⊕ Fin l))
    (w : β → M) (xs : Fin (l + 1) → M) :
    Term.realize (Sum.elim w xs) (pushTermL t) =
      Term.realize (Sum.elim w (xs ∘ Fin.castSucc)) t := by
  rw [pushTermL, Term.realize_relabel]
  congr 1
  ext i
  rcases i with i | i <;> rfl

/-- **The ring formula `∃z, z*z = t`**, as an `LRc`-formula. -/
def sqFormL {β : Type} {l : ℕ} (t : LRc.Term (β ⊕ Fin l)) : LRc.BoundedFormula β l :=
  (Term.bdEqual (tMulL (witTermL (β := β) (l := l)) (witTermL (β := β) (l := l)))
    (pushTermL t)).ex

theorem sqFormL_realize {β : Type} {l : ℕ} (t : LRc.Term (β ⊕ Fin l)) (v : β → M)
    (xs : Fin l → M) :
    (sqFormL t).Realize v xs ↔ ∃ z : M, mulEL z z = Term.realize (Sum.elim v xs) t := by
  rw [sqFormL, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using ha⟩

/-- **The ring formula `t₁ ≤ t₂`, i.e. `∃z, z*z = t₂ - t₁`**, as an `LRc`-formula. -/
def leFormL {β : Type} {l : ℕ} (t₁ t₂ : LRc.Term (β ⊕ Fin l)) : LRc.BoundedFormula β l :=
  sqFormL (tSubL t₂ t₁)

theorem leFormL_realize {β : Type} {l : ℕ} (t₁ t₂ : LRc.Term (β ⊕ Fin l)) (v : β → M)
    (xs : Fin l → M) :
    (leFormL t₁ t₂).Realize v xs ↔
      leEL (Term.realize (Sum.elim v xs) t₁) (Term.realize (Sum.elim v xs) t₂) := by
  rw [leFormL, sqFormL_realize, realize_tSubL]
  rfl

end QuantifierFree

/-! ## 4. The four sentences and their realizations -/

section Sentences

/-- The variable of a one-variable formula. -/
def vL1 (i : Fin 1) : LRc.Term (Empty ⊕ Fin 1) := Term.var (Sum.inr i)

/-- The two variables of a two-variable formula. -/
def vL2 (i : Fin 2) : LRc.Term (Empty ⊕ Fin 2) := Term.var (Sum.inr i)

/-- The three variables of a three-variable formula. -/
def vL3 (i : Fin 3) : LRc.Term (Empty ⊕ Fin 3) := Term.var (Sum.inr i)

/-- Reflexivity: `∀x, x ≤ x`. -/
def reflForm : LRc.BoundedFormula Empty 1 := leFormL (vL1 0) (vL1 0)

/-- Antisymmetry: `∀x y, x ≤ y → y ≤ x → x = y`. -/
def antiForm : LRc.BoundedFormula Empty 2 :=
  (leFormL (vL2 0) (vL2 1)).imp
    ((leFormL (vL2 1) (vL2 0)).imp (Term.bdEqual (vL2 0) (vL2 1)))

/-- Transitivity: `∀x y z, x ≤ y → y ≤ z → x ≤ z`. -/
def transForm : LRc.BoundedFormula Empty 3 :=
  (leFormL (vL3 0) (vL3 1)).imp
    ((leFormL (vL3 1) (vL3 2)).imp (leFormL (vL3 0) (vL3 2)))

/-- Totality: `∀x y, x ≤ y ∨ y ≤ x`. -/
def totForm : LRc.BoundedFormula Empty 2 :=
  leFormL (vL2 0) (vL2 1) ⊔ leFormL (vL2 1) (vL2 0)

variable {M : Type} [LRc.Structure M]

theorem reflForm_realize (xs : Fin 1 → M) :
    reflForm.Realize emptyVar xs ↔ leEL (xs 0) (xs 0) := by
  rw [reflForm, leFormL_realize]
  simp [vL1]

theorem antiForm_realize (xs : Fin 2 → M) :
    antiForm.Realize emptyVar xs ↔ (leEL (xs 0) (xs 1) → leEL (xs 1) (xs 0) → xs 0 = xs 1) := by
  rw [antiForm, BoundedFormula.realize_imp, BoundedFormula.realize_imp,
    BoundedFormula.realize_bdEqual, leFormL_realize, leFormL_realize]
  simp [vL2]

theorem transForm_realize (xs : Fin 3 → M) :
    transForm.Realize emptyVar xs ↔
      (leEL (xs 0) (xs 1) → leEL (xs 1) (xs 2) → leEL (xs 0) (xs 2)) := by
  rw [transForm, BoundedFormula.realize_imp, BoundedFormula.realize_imp,
    leFormL_realize, leFormL_realize, leFormL_realize]
  simp [vL3]

theorem totForm_realize (xs : Fin 2 → M) :
    totForm.Realize emptyVar xs ↔ (leEL (xs 0) (xs 1) ∨ leEL (xs 1) (xs 0)) := by
  rw [totForm, BoundedFormula.realize_sup, leFormL_realize, leFormL_realize]
  simp [vL2]

end Sentences

/-! ## 5. Transfer from `ℝ` to an arbitrary model of `TR` -/

/-- The realization of the universal closure of a bounded formula is the realization for all
tuples (the `LRc` mirror of `ReductEmb.sentence_realize_alls`). -/
theorem sentence_realize_alls_LRc {M : Type} [LRc.Structure M] (n : ℕ)
    (φ : LRc.BoundedFormula Empty n) :
    (@Sentence.Realize LRc M _ (φ.alls : LRc.Sentence)) ↔
      ∀ xs : Fin n → M, φ.Realize emptyVar xs := by
  rw [sentence_realize_bounded (inferInstance : LRc.Structure M) (φ.alls : LRc.Sentence)]
  exact BoundedFormula.realize_alls

/-- **Elementarity transfer.**  A bounded `LRc`-formula with no free variables all of whose
realizations in `ℝ` hold, has all realizations in any model of `TR`. -/
theorem transfer_LRc {M : Type} [LRc.Structure M] (hM : M ⊨ TR) {n : ℕ}
    (φ : LRc.BoundedFormula Empty n) (h : ∀ xs : Fin n → ℝ, φ.Realize emptyVar xs) :
    ∀ xs : Fin n → M, φ.Realize emptyVar xs := by
  have hR : (@Sentence.Realize LRc ℝ _ (φ.alls : LRc.Sentence)) :=
    (sentence_realize_alls_LRc (M := ℝ) n φ).mpr h
  have hmem : (φ.alls : LRc.Sentence) ∈ TR := mem_completeTheory.mpr hR
  have hM' : (@Sentence.Realize LRc M _ (φ.alls : LRc.Sentence)) :=
    (Theory.model_iff TR).mp hM (φ.alls) hmem
  exact (sentence_realize_alls_LRc (M := M) n φ).mp hM'

/-! ## 6. The four order axioms on `ℝ` -/

/-- The four order axioms on `ℝ`, derived from `leEL_real` (`WilC5/leEL_real.lean`). -/
theorem leEL_refl_real (x : ℝ) : leEL x x := (leEL_real x x).mpr le_rfl

theorem leEL_antisymm_real (x y : ℝ) (h₁ : leEL x y) (h₂ : leEL y x) : x = y :=
  le_antisymm ((leEL_real x y).mp h₁) ((leEL_real y x).mp h₂)

theorem leEL_trans_real (x y z : ℝ) (h₁ : leEL x y) (h₂ : leEL y z) : leEL x z :=
  (leEL_real x z).mpr (le_trans ((leEL_real x y).mp h₁) ((leEL_real y z).mp h₂))

theorem leEL_total_real (x y : ℝ) : leEL x y ∨ leEL y x :=
  (le_total x y).imp (fun h => (leEL_real x y).mpr h) (fun h => (leEL_real y x).mpr h)

/-! ## 7. The main theorem -/

/-- **The definable order of a model of `TR` is a linear order.** -/
theorem tr_leE_axioms (M : Type) [FirstOrder.Language.Structure WilkiesDesign.CG.LRc M]
    (h : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR) :
    (∀ x : M, Work.WilC5.leEL x x) ∧
    (∀ x y : M, Work.WilC5.leEL x y → Work.WilC5.leEL y x → x = y) ∧
    (∀ x y z : M, Work.WilC5.leEL x y → Work.WilC5.leEL y z → Work.WilC5.leEL x z) ∧
    (∀ x y : M, Work.WilC5.leEL x y ∨ Work.WilC5.leEL y x) := by
  have hrefl : ∀ xs : Fin 1 → M, reflForm.Realize emptyVar xs :=
    transfer_LRc h reflForm (by
      intro xs
      rw [reflForm_realize]
      exact leEL_refl_real (xs 0))
  have hanti : ∀ xs : Fin 2 → M, antiForm.Realize emptyVar xs :=
    transfer_LRc h antiForm (by
      intro xs
      rw [antiForm_realize]
      exact fun h₁ h₂ => leEL_antisymm_real (xs 0) (xs 1) h₁ h₂)
  have htrans : ∀ xs : Fin 3 → M, transForm.Realize emptyVar xs :=
    transfer_LRc h transForm (by
      intro xs
      rw [transForm_realize]
      exact fun h₁ h₂ => leEL_trans_real (xs 0) (xs 1) (xs 2) h₁ h₂)
  have htot : ∀ xs : Fin 2 → M, totForm.Realize emptyVar xs :=
    transfer_LRc h totForm (by
      intro xs
      rw [totForm_realize]
      exact leEL_total_real (xs 0) (xs 1))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have h1 := hrefl ![x]
    rwa [reflForm_realize] at h1
  · intro x y hxy hyx
    have h1 := hanti ![x, y]
    rw [antiForm_realize] at h1
    exact h1 hxy hyx
  · intro x y z hxy hyz
    have h1 := htrans ![x, y, z]
    rw [transForm_realize] at h1
    exact h1 hxy hyz
  · intro x y
    have h1 := htot ![x, y]
    rwa [totForm_realize] at h1

end Work.WilC5
