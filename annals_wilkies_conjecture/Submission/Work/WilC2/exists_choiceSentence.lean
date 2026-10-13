/-
  Area C2 (WilC2): the *choice statement* as a single first-order sentence.

  The semantic content produced elsewhere in this area (`ChoiceCond`, `selectForm_exists`,
  `definable_choice_fibre`) is a statement about the realisations of a pair of parametric formulas
  `φ ψ : ParamFormula n`:

    "for every parameter tuple `v`, if the fibre of `φ` over `v` is nonempty, then there is a
     *unique* point of the fibre of `φ` in which `ψ` holds".

  The point of this module is that this condition is *elementary*: it is expressed by a single
  `LRc`-sentence `choiceSent φ ψ`, and this holds in **every** `LRc`-structure, not merely in the
  models of `TR` or in ordered fields.  Indeed the condition is

    `∀ v, (∃ y, φ(v,y)) → ∃! y, (ψ(v,y) ∧ φ(v,y))`,

  which is a first-order sentence of the language; the content of the file is the (careful)
  syntactic transcription, together with the semantic computation `realize_choiceSent`.

  Variable layout.  The sentence is `Formula.iAlls (Fin n) Ψ`, where `Ψ` lives in the context
  `CV n = (Empty ⊕ Fin n) ⊕ Fin 1` (parameters, then the point `y`).  Inside `Ψ` the two
  quantifiers of the implication are added on the right and stripped by `Formula.iExs (Fin 1)`:
  the antecedent quantifies a fresh point variable (`cFill φ`), the consequent its own point
  variable (`cPair φ ψ`), and the uniqueness clause further quantifies `y'` on the right of
  `CV2 n = CV n ⊕ Fin 1` (`cUniq φ ψ`).  The relabellings `cParam`, `c2Param`, `cY`, `c2Y`,
  `c2Y'` name the individual variables of the two contexts.

  The auxiliary declarations are confined to the namespace `ChoiceSentAux`: the only declaration
  of the file visible to the rest of the project is `exists_choiceSentence`.
-/
import Mathlib
import Submission.Work.WilC2.ChoiceDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

namespace ChoiceSentAux

/-! ## 1. The variable contexts and the sentence -/

/-- The variable context of the body of the sentence: the parameters, then the point `y`. -/
abbrev CV (n : ℕ) := (Empty ⊕ Fin n) ⊕ Fin 1

/-- The variable context of the body of the uniqueness clause: the parameters, `y`, then `y'`. -/
abbrev CV2 (n : ℕ) := CV n ⊕ Fin 1

/-- The parameter variable of `CV n`. -/
def cParam {n : ℕ} (i : Fin n) : CV n := Sum.inl (Sum.inr i)

/-- The point variable `y` of `CV n`. -/
def cY {n : ℕ} : CV n := Sum.inr 0

/-- The parameter variable of `CV2 n`. -/
def c2Param {n : ℕ} (i : Fin n) : CV2 n := Sum.inl (Sum.inl (Sum.inr i))

/-- The variable `y` of `CV2 n`. -/
def c2Y {n : ℕ} : CV2 n := Sum.inl (Sum.inr 0)

/-- The variable `y'` of `CV2 n`. -/
def c2Y' {n : ℕ} : CV2 n := Sum.inr 0

/-- `y' = y`, as a formula of the context `CV2 n`. -/
def eqF {n : ℕ} : LRc.Formula (CV2 n) := Term.equal (Term.var c2Y') (Term.var c2Y)

/-- `φ` with its variables renamed: the parameters become `cParam`, the point becomes `cY`. -/
def cFill {n : ℕ} (φ : ParamFormula n) : LRc.Formula (CV n) :=
  φ.relabel (Sum.elim cParam (fun _ => cY))

/-- `ψ ∧ φ` with its variables renamed: the parameters become `cParam`, the point becomes `cY`. -/
def cPair {n : ℕ} (φ ψ : ParamFormula n) : LRc.Formula (CV n) :=
  (ψ ⊓ φ).relabel (Sum.elim cParam (fun _ => cY))

/-- The body of the uniqueness clause: for `y'` in the fibre, `y' = y`. -/
def cUniq {n : ℕ} (φ ψ : ParamFormula n) : LRc.Formula (CV2 n) :=
  ((ψ ⊓ φ).relabel (Sum.elim c2Param (fun _ => c2Y'))) ⟹ eqF

/-- **The choice sentence** of the pair `(φ, ψ)`:
"for every parameter tuple `v`, if the `φ`-fibre over `v` is nonempty then there is a unique point
of that fibre in which `ψ` holds". -/
def choiceSent {n : ℕ} (φ ψ : ParamFormula n) : LRc.Sentence :=
  Formula.iAlls (Fin n)
    (Formula.iExs (Fin 1) (cFill φ) ⟹
      Formula.iExs (Fin 1) (cPair φ ψ ⊓ Formula.iAlls (Fin 1) (cUniq φ ψ)))

/-! ## 2. Renaming the variables of `iAlls` -/

/-- `Formula.iAlls` with the assignment written as a plain `Sum.elim` (the library statement
produces the `η`-expanded form `fun a => Sum.elim v i a`, which does not match the `Sum.elim`
shapes used below). -/
theorem realize_iAlls_fin {M : Type} {α : Type*} [LRc.Structure M] {n : ℕ}
    (Ψ : LRc.Formula (α ⊕ Fin n)) (v : α → M) :
    (Formula.iAlls (Fin n) Ψ).Realize v ↔ ∀ i : Fin n → M, Ψ.Realize (Sum.elim v i) :=
  Formula.realize_iAlls

/-! ## 3. Evaluating the composite assignments -/

theorem comp_cFill {M : Type} {n : ℕ} (v : Fin n → M) (i : Fin 1 → M) :
    (Sum.elim (Sum.elim (default : Empty → M) v) i) ∘
        (Sum.elim cParam (fun _ : Fin 1 => cY (n := n))) =
      Sum.elim v (fun _ => i 0) := by
  funext b
  rcases b with j | k <;> simp [cParam, cY]

theorem comp_cUniq {M : Type} {n : ℕ} (v : Fin n → M) (i i' : Fin 1 → M) :
    (Sum.elim (Sum.elim (Sum.elim (default : Empty → M) v) i) i') ∘
        (Sum.elim c2Param (fun _ : Fin 1 => c2Y' (n := n))) =
      Sum.elim v (fun _ => i' 0) := by
  funext b
  rcases b with j | k <;> simp [c2Param, c2Y']

/-! ## 4. Semantics of the three ingredients -/

theorem cFill_realize {M : Type} [LRc.Structure M] {n : ℕ} (φ : ParamFormula n)
    (v : Fin n → M) (i : Fin 1 → M) :
    (cFill φ).Realize (Sum.elim (Sum.elim (default : Empty → M) v) i) ↔
      φ.Realize (Sum.elim v (fun _ => i 0)) := by
  rw [cFill, Formula.realize_relabel, comp_cFill]

theorem cPair_realize {M : Type} [LRc.Structure M] {n : ℕ} (φ ψ : ParamFormula n)
    (v : Fin n → M) (i : Fin 1 → M) :
    (cPair φ ψ).Realize (Sum.elim (Sum.elim (default : Empty → M) v) i) ↔
      (ψ ⊓ φ).Realize (Sum.elim v (fun _ => i 0)) := by
  rw [cPair, Formula.realize_relabel, comp_cFill]

theorem eqF_realize {M : Type} [LRc.Structure M] {n : ℕ} (v : Fin n → M) (i i' : Fin 1 → M) :
    (eqF (n := n)).Realize (Sum.elim (Sum.elim (Sum.elim (default : Empty → M) v) i) i') ↔
      i' 0 = i 0 := by
  rw [eqF, Formula.realize_equal, Term.realize_var, Term.realize_var]
  simp [c2Y, c2Y', Sum.elim_inl, Sum.elim_inr]

theorem cUniq_realize {M : Type} [LRc.Structure M] {n : ℕ} (φ ψ : ParamFormula n)
    (v : Fin n → M) (i i' : Fin 1 → M) :
    (cUniq φ ψ).Realize (Sum.elim (Sum.elim (Sum.elim (default : Empty → M) v) i) i') ↔
      ((ψ ⊓ φ).Realize (Sum.elim v (fun _ => i' 0)) → i' 0 = i 0) := by
  rw [cUniq, Formula.realize_imp, Formula.realize_relabel, comp_cUniq, eqF_realize]

/-! ## 5. `Fin 1 → M` binders versus `M` binders -/

theorem iExs_fin_one_iff {M : Type} (f : (Fin 1 → M) → Prop) :
    (∃ i : Fin 1 → M, f i) ↔ ∃ y : M, f (fun _ => y) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i 0, ?_⟩
    have h : (fun _ : Fin 1 => i 0) = i := by funext k; rw [Fin.eq_zero k]
    rwa [h]
  · rintro ⟨y, hy⟩; exact ⟨fun _ => y, hy⟩

theorem iAlls_fin_one_iff {M : Type} (f : (Fin 1 → M) → Prop) :
    (∀ i : Fin 1 → M, f i) ↔ ∀ y : M, f (fun _ => y) := by
  constructor
  · intro h y; exact h (fun _ => y)
  · intro h i
    have h1 := h (i 0)
    have h' : (fun _ : Fin 1 => i 0) = i := by funext k; rw [Fin.eq_zero k]
    rwa [h'] at h1

/-! ## 6. The semantic characterisation -/

/-- **The realisation theorem.**  In every `LRc`-structure, the sentence `choiceSent φ ψ` says
exactly that every nonempty `φ`-fibre contains a unique point in which `ψ` holds. -/
theorem realize_choiceSent {M : Type} [LRc.Structure M] {n : ℕ} (φ ψ : ParamFormula n) :
    (M ⊨ choiceSent φ ψ) ↔
      ∀ v : Fin n → M, (∃ y : M, φ.Realize (Sum.elim v (fun _ => y))) →
        ∃ y : M, (ψ.Realize (Sum.elim v (fun _ => y)) ∧
            φ.Realize (Sum.elim v (fun _ => y))) ∧
          ∀ y' : M, (ψ.Realize (Sum.elim v (fun _ => y')) ∧
            φ.Realize (Sum.elim v (fun _ => y'))) → y' = y := by
  rw [choiceSent, Sentence.Realize, realize_iAlls_fin]
  refine forall_congr' (fun v => ?_)
  simp only [Formula.realize_imp, Formula.realize_iExs, Formula.realize_inf, realize_iAlls_fin,
    cFill_realize, cPair_realize, cUniq_realize]
  simp only [iExs_fin_one_iff, iAlls_fin_one_iff]

end ChoiceSentAux

theorem exists_choiceSentence {n : ℕ} (φ ψ : Work.WilC2.ParamFormula n) :
    ∃ σ : WilkiesDesign.CG.LRc.Sentence, ∀ {M : Type} [WilkiesDesign.CG.LRc.Structure M],
      (M ⊨ σ) ↔ ∀ v : Fin n → M, (∃ y : M, φ.Realize (Sum.elim v (fun _ => y))) →
        ∃ y : M, (ψ.Realize (Sum.elim v (fun _ => y)) ∧
            φ.Realize (Sum.elim v (fun _ => y))) ∧
          ∀ y' : M, (ψ.Realize (Sum.elim v (fun _ => y')) ∧
            φ.Realize (Sum.elim v (fun _ => y'))) → y' = y := by
  refine ⟨ChoiceSentAux.choiceSent φ ψ, ?_⟩
  intro M inst
  exact ChoiceSentAux.realize_choiceSent φ ψ

end Work.WilC2
