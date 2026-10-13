/-
  WilC5 — an `LEc`-embedding between models of `TE` is an `LRc`-embedding of the `rexp`-reducts.

  This is the "mechanical" half `ME1` of the C5 specification (`Spec.lean`): every embedding of
  models of `TE = Th(ℝ_exp)` restricts to an embedding of the `rexp`-reducts.  Since `TE` is a
  complete theory of ordered exponential fields, the definable order

      `leE x y  :=  ∃ z, z * z = y - x`

  of a model of `TE` is a linear order, and the predicate `absLeOne x` (the ring formula
  `|x| ≤ 1`, i.e. `1 - x` and `1 + x` are both squares) is invariant under the embedding.  Hence
  the definable restricted exponential `rexpFromExp x = if absLeOne x then exp x else 0` is
  preserved, and the `LEc`-embedding is automatically an `LRc`-embedding of the reducts.

  The linearity and antisymmetry of `leE` in an arbitrary model of `TE` are transferred from `ℝ`
  by elementarity: the corresponding sentences hold in `ℝ`, hence belong to `TE`, hence hold in
  every model of `TE`.  The syntactic machinery for this (`BoundedFormula`, `completeTheory`) is
  used below.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC5.RealFacts
import Submission.Work.WilC5.Reduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The formulas `∃z, z*z = t` and `t₁ ≤ t₂`, and the sentences used for transfer -/

section Formulas

variable {M : Type} [LEc.Structure M]

/-- `sqForm t` is the ring formula `∃ z, z * z = t`. -/
def sqForm {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l)) : LEc.BoundedFormula β l :=
  (Term.bdEqual (eMul (witTerm (l := l)) (witTerm (l := l))) (pushTerm t)).ex

theorem sqForm_realize {β : Type} {l : ℕ} (t : LEc.Term (β ⊕ Fin l)) (v : β → M) (xs : Fin l → M) :
    (sqForm t).Realize v xs ↔ ∃ z : M, mulE z z = Term.realize (Sum.elim v xs) t := by
  rw [sqForm, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by simpa using ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by simpa using ha⟩

/-- `leForm t₁ t₂` is the ring formula `t₁ ≤ t₂`, i.e. `∃ z, z * z = t₂ - t₁`. -/
def leForm {β : Type} {l : ℕ} (t₁ t₂ : LEc.Term (β ⊕ Fin l)) : LEc.BoundedFormula β l :=
  sqForm (eSub t₂ t₁)

theorem leForm_realize {β : Type} {l : ℕ} (t₁ t₂ : LEc.Term (β ⊕ Fin l)) (v : β → M)
    (xs : Fin l → M) :
    (leForm t₁ t₂).Realize v xs ↔
      isSquare (subE (Term.realize (Sum.elim v xs) t₂) (Term.realize (Sum.elim v xs) t₁)) := by
  rw [leForm, sqForm_realize, realize_eSub]; rfl

/-- The `j`-th variable of a formula with two bound variables. -/
def v2 (i : Fin 2) : LEc.Term (Empty ⊕ Fin 2) := Term.var (Sum.inr i)

/-- The `j`-th variable of a formula with one bound variable. -/
def v1 (i : Fin 1) : LEc.Term (Empty ⊕ Fin 1) := Term.var (Sum.inr i)

/-- Totality of the definable order: `x ≤ y` or `y ≤ x`. -/
def totFormula : LEc.BoundedFormula Empty 2 := leForm (v2 0) (v2 1) ⊔ leForm (v2 1) (v2 0)

/-- Antisymmetry of the definable order: `x ≤ y → y ≤ x → x = y`. -/
def antiFormula : LEc.BoundedFormula Empty 2 :=
  (leForm (v2 0) (v2 1)).imp ((leForm (v2 1) (v2 0)).imp (Term.bdEqual (v2 0) (v2 1)))

/-- Commutativity of addition. -/
def commFormula : LEc.BoundedFormula Empty 2 :=
  Term.bdEqual (eAdd (v2 0) (v2 1)) (eAdd (v2 1) (v2 0))

/-- Involutivity of negation. -/
def nnFormula : LEc.BoundedFormula Empty 1 :=
  Term.bdEqual (eNeg (eNeg (v1 0))) (v1 0)

theorem totFormula_realize (xs : Fin 2 → M) :
    totFormula.Realize (emptyVar : Empty → M) xs ↔
      isSquare (subE (xs 1) (xs 0)) ∨ isSquare (subE (xs 0) (xs 1)) := by
  rw [totFormula, BoundedFormula.realize_sup, leForm_realize, leForm_realize]
  simp only [v2, Term.realize_var, Sum.elim_inr]

theorem antiFormula_realize (xs : Fin 2 → M) :
    antiFormula.Realize (emptyVar : Empty → M) xs ↔
      (isSquare (subE (xs 1) (xs 0)) → isSquare (subE (xs 0) (xs 1)) → xs 0 = xs 1) := by
  rw [antiFormula, BoundedFormula.realize_imp, BoundedFormula.realize_imp,
    BoundedFormula.realize_bdEqual, leForm_realize, leForm_realize]
  simp only [v2, Term.realize_var, Sum.elim_inr]

theorem commFormula_realize (xs : Fin 2 → M) :
    commFormula.Realize (emptyVar : Empty → M) xs ↔ addE (xs 0) (xs 1) = addE (xs 1) (xs 0) := by
  rw [commFormula, BoundedFormula.realize_bdEqual]
  simp only [v2, Term.realize_var, Sum.elim_inr, realize_eAdd]

theorem nnFormula_realize (xs : Fin 1 → M) :
    nnFormula.Realize (emptyVar : Empty → M) xs ↔ negE (negE (xs 0)) = xs 0 := by
  rw [nnFormula, BoundedFormula.realize_bdEqual]
  simp only [v1, Term.realize_var, Sum.elim_inr, realize_eNeg]

end Formulas

/-! ## 2. The sentences hold in `ℝ` -/

section Real

theorem tot_real : ∀ xs : Fin 2 → ℝ, totFormula.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [totFormula_realize]
  rw [subE_real, subE_real, isSquare_real, isSquare_real]
  rcases le_total (xs 0) (xs 1) with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem anti_real : ∀ xs : Fin 2 → ℝ, antiFormula.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [antiFormula_realize]
  rw [subE_real, subE_real, isSquare_real, isSquare_real]
  intro h1 h2
  linarith

theorem comm_real : ∀ xs : Fin 2 → ℝ, commFormula.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [commFormula_realize]
  rw [addE_real, addE_real]
  ring

theorem nn_real : ∀ xs : Fin 1 → ℝ, nnFormula.Realize (emptyVar : Empty → ℝ) xs := by
  intro xs
  rw [nnFormula_realize]
  rw [negE_real, negE_real, neg_neg]

end Real

/-! ## 3. Transfer from `ℝ` to any model of `TE` -/

section Transfer

/-- Universal closure: `Sentence.Realize` of the `∀`-closure of a formula is the realization
for all tuples. -/
theorem sentence_realize_alls (M : Type) [LEc.Structure M] (n : ℕ)
    (φ : LEc.BoundedFormula Empty n) :
    (@Sentence.Realize LEc M _ (φ.alls : LEc.Sentence)) ↔
      ∀ xs : Fin n → M, φ.Realize (emptyVar : Empty → M) xs := by
  rw [sentence_realize_bounded]
  exact BoundedFormula.realize_alls

/-- **Transfer of universally quantified formulas** from `ℝ` to any model of `TE`. -/
theorem transfer {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {n : ℕ}
    (φ : LEc.BoundedFormula Empty n)
    (h : ∀ xs : Fin n → ℝ, φ.Realize (emptyVar : Empty → ℝ) xs) :
    ∀ xs : Fin n → M, φ.Realize (emptyVar : Empty → M) xs := by
  have hσR : @Sentence.Realize LEc ℝ _ (φ.alls : LEc.Sentence) :=
    (sentence_realize_alls ℝ n φ).mpr h
  have hmem : (φ.alls : LEc.Sentence) ∈ TE := mem_completeTheory.mpr hσR
  have hM' : @Sentence.Realize LEc M _ (φ.alls : LEc.Sentence) :=
    ((Theory.model_iff TE).mp hM) (φ.alls) hmem
  exact (sentence_realize_alls M n φ).mp hM'

end Transfer

/-! ## 4. The definable order in a model of `TE` -/

section ModelFacts

variable {M : Type} [LEc.Structure M]

/-- The definable order of a model of `TE` is total. -/
theorem le_total_of_model (hM : M ⊨ TE) (x y : M) :
    isSquare (subE y x) ∨ isSquare (subE x y) := by
  have h := transfer hM totFormula tot_real ![x, y]
  rw [totFormula_realize] at h
  simpa using h

/-- The definable order of a model of `TE` is antisymmetric. -/
theorem le_antisymm_of_model (hM : M ⊨ TE) (x y : M)
    (h1 : isSquare (subE y x)) (h2 : isSquare (subE x y)) : x = y := by
  have h := transfer hM antiFormula anti_real ![x, y]
  rw [antiFormula_realize] at h
  exact h (by simpa using h1) (by simpa using h2)

/-- Addition in a model of `TE` is commutative. -/
theorem addE_comm_of_model (hM : M ⊨ TE) (x y : M) : addE x y = addE y x := by
  have h := transfer hM commFormula comm_real ![x, y]
  rw [commFormula_realize] at h
  simpa using h

/-- Negation in a model of `TE` is involutive. -/
theorem negE_negE_of_model (hM : M ⊨ TE) (x : M) : negE (negE x) = x := by
  have h := transfer hM nnFormula nn_real ![x]
  rw [nnFormula_realize] at h
  simpa using h

end ModelFacts

/-! ## 5. An `LEc`-embedding preserves the definable order, `|x| ≤ 1` and `rexpFromExp` -/

section Map

variable {M N : Type} [LEc.Structure M] [LEc.Structure N]

theorem map_mulE (f : M ↪[LEc] N) (x y : M) : f (mulE x y) = mulE (f x) (f y) := by
  rw [mulE, mulE, f.map_fun]
  congr 1
  ext i; fin_cases i <;> rfl

theorem map_addE (f : M ↪[LEc] N) (x y : M) : f (addE x y) = addE (f x) (f y) := by
  rw [addE, addE, f.map_fun]
  congr 1
  ext i; fin_cases i <;> rfl

theorem map_negE (f : M ↪[LEc] N) (x : M) : f (negE x) = negE (f x) := by
  rw [negE, negE, f.map_fun]
  congr 1
  ext i; fin_cases i; rfl

theorem map_oneE (f : M ↪[LEc] N) : f (oneE : M) = (oneE : N) := by
  rw [oneE, oneE, f.map_fun]
  congr 1
  ext i; exact Fin.elim0 i

theorem map_zeroE (f : M ↪[LEc] N) : f (zeroE : M) = (zeroE : N) := by
  rw [zeroE, zeroE, f.map_fun]
  congr 1
  ext i; exact Fin.elim0 i

theorem map_expE (f : M ↪[LEc] N) (x : M) : f (expE x) = expE (f x) := by
  rw [expE, expE, f.map_fun]
  congr 1
  ext i; fin_cases i; rfl

theorem map_subE (f : M ↪[LEc] N) (x y : M) : f (subE x y) = subE (f x) (f y) := by
  rw [subE, subE, map_addE, map_negE]

/-- A homomorphism maps squares to squares. -/
theorem isSquare_map (f : M ↪[LEc] N) {y : M} (h : isSquare y) : isSquare (f y) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨f z, by rw [← map_mulE f z z, hz]⟩

/-- The definable order is preserved (forward) by an `LEc`-embedding. -/
theorem leE_map (f : M ↪[LEc] N) {x y : M} (h : leE x y) : leE (f x) (f y) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨f z, by rw [← map_mulE f z z, ← map_subE f y x, hz]⟩

/-- The definable order is reflected by an `LEc`-embedding between models of `TE`: this uses
totality of the order at the source and antisymmetry of the order at the target. -/
theorem leE_reflect (f : M ↪[LEc] N)
    (htot : ∀ x y : M, leE x y ∨ leE y x)
    (hanti : ∀ x y : N, leE x y → leE y x → x = y)
    {x y : M} (h : leE (f x) (f y)) : leE x y := by
  rcases htot x y with hxy | hyx
  · exact hxy
  · have h1 : leE (f y) (f x) := leE_map f hyx
    have h2 : f x = f y := hanti _ _ h h1
    have h3 : x = y := f.injective h2
    subst h3
    exact hyx

/-- `|x| ≤ 1` is `-1 ≤ x ≤ 1`, in terms of the definable order. -/
theorem absLeOne_iff (hcomm : ∀ x y : M, addE x y = addE y x)
    (hnn : ∀ x : M, negE (negE x) = x) (x : M) :
    absLeOne x ↔ isSquare (subE x (negE oneE)) ∧ isSquare (subE oneE x) := by
  have key : subE x (negE oneE) = addE oneE x := by rw [subE, hnn oneE, hcomm x oneE]
  rw [absLeOne, key]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `|x| ≤ 1` is preserved by an `LEc`-embedding between models of `TE`. -/
theorem absLeOne_map (f : M ↪[LEc] N) (hM : M ⊨ TE) (hN : N ⊨ TE) {x : M}
    (h : absLeOne x) : absLeOne (f x) := by
  have hk := (absLeOne_iff (addE_comm_of_model hM) (negE_negE_of_model hM) x).mp h
  have h1 : isSquare (f (subE x (negE oneE))) := isSquare_map f hk.1
  rw [map_subE, map_negE, map_oneE] at h1
  have h2 : isSquare (f (subE oneE x)) := isSquare_map f hk.2
  rw [map_subE, map_oneE] at h2
  exact (absLeOne_iff (addE_comm_of_model hN) (negE_negE_of_model hN) (f x)).mpr ⟨h1, h2⟩

/-- `|x| ≤ 1` is reflected by an `LEc`-embedding between models of `TE`. -/
theorem absLeOne_comap (f : M ↪[LEc] N) (hM : M ⊨ TE) (hN : N ⊨ TE) {x : M}
    (h : absLeOne (f x)) : absLeOne x := by
  have hk := (absLeOne_iff (addE_comm_of_model hN) (negE_negE_of_model hN) (f x)).mp h
  have h1 : leE (negE oneE) (f x) := hk.1
  have h2 : leE (f x) oneE := hk.2
  have h1' : leE (f (negE oneE)) (f x) := by rw [map_negE, map_oneE]; exact h1
  have h2' : leE (f x) (f oneE) := by rw [map_oneE]; exact h2
  refine (absLeOne_iff (addE_comm_of_model hM) (negE_negE_of_model hM) x).mpr ⟨?_, ?_⟩
  · exact leE_reflect f (le_total_of_model hM) (le_antisymm_of_model hN) h1'
  · exact leE_reflect f (le_total_of_model hM) (le_antisymm_of_model hN) h2'

/-- The definable restricted exponential is preserved by an `LEc`-embedding of models of `TE`. -/
theorem rexpFromExp_map (f : M ↪[LEc] N) (hM : M ⊨ TE) (hN : N ⊨ TE) (x : M) :
    f (rexpFromExp x) = rexpFromExp (f x) := by
  by_cases h : absLeOne x
  · rw [rexpFromExp_of_absLeOne h, rexpFromExp_of_absLeOne (absLeOne_map f hM hN h), map_expE]
  · rw [rexpFromExp_of_not_absLeOne h]
    have h' : ¬ absLeOne (f x) := fun hh => h (absLeOne_comap f hM hN hh)
    rw [rexpFromExp_of_not_absLeOne h', map_zeroE]

end Map

/-! ## 6. The main theorem -/

theorem ReductEmb {M N : Type} [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    (hM : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE)
    (hN : FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TE)
    (f : FirstOrder.Language.Embedding WilkiesDesign.CG.LEc M N) :
    ∃ fR : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc M N
        (Work.WilC5.reductStruct M) (Work.WilC5.reductStruct N),
      (fR : M → N) = (f : M → N) := by
  letI : LRc.Structure M := reductStruct M
  letI : LRc.Structure N := reductStruct N
  refine ⟨{ toEmbedding := f.toEmbedding, map_fun' := ?_, map_rel' := ?_ }, rfl⟩
  · intro n g x
    rcases g with (g | r) | c
    · exact f.map_fun (ringSym g) x
    · rcases r with ⟨⟩
      show f (rexpFromExp (x 0)) = rexpFromExp ((f ∘ x) 0)
      exact rexpFromExp_map f hM hN (x 0)
    · exact f.map_fun (Sum.inr c) x
  · intro n r x
    exact nomatch r

end Work.WilC5
