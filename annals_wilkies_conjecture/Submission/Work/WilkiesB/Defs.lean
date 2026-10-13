import Submission.Work.Wilkies.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Area B (syntax) — basic vocabulary

* `expEval v P` evaluates an exp-polynomial `P(z, e^z)`; the variable `Sum.inl i` is `v i` and
  the variable `Sum.inr i` is `Real.exp (v i)`.
* `ExpExistI X` is the frozen `WilkiesDesign.ExpExist` for an arbitrary index type of the ambient
  variables and an arbitrary *finite type* of existential witnesses: `X` is the projection of the
  zero set of a single exp-polynomial.
* `sumFinSnocEquiv` and the `Sum`-shuffling lemmas are the index bookkeeping used by the closure
  lemmas and by the formula induction.

Everything else in `Submission/Work/WilkiesB` imports this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

noncomputable section

open FirstOrder FirstOrder.Language
open MvPolynomial

namespace Work.WilkiesB

/-- The language of rings together with one exponential. -/
abbrev Lexp : Language := WilkiesConjecture.expRing

/-! ## Evaluation of exp-polynomials -/

/-- Evaluate an exp-polynomial `P(z, e^z)` at `z := v`.  The variable type `ι ⊕ ι` splits into
the "plain" copy (`Sum.inl`) and the "exponentiated" copy (`Sum.inr`). -/
def expEval {ι : Type*} (v : ι → ℝ) (P : MvPolynomial (ι ⊕ ι) ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim v (fun i => Real.exp (v i))) P

/-- The frozen `WilkiesDesign.expPolyEval` is `expEval` with the arguments in the other order. -/
theorem expPolyEval_eq_expEval {N : ℕ} (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) (v : Fin N → ℝ) :
    WilkiesDesign.expPolyEval P v = expEval v P := rfl

@[simp] theorem expEval_zero {ι : Type*} (v : ι → ℝ) :
    expEval v (0 : MvPolynomial (ι ⊕ ι) ℝ) = 0 := by
  simp only [expEval, map_zero]

@[simp] theorem expEval_one {ι : Type*} (v : ι → ℝ) :
    expEval v (1 : MvPolynomial (ι ⊕ ι) ℝ) = 1 := by
  simp only [expEval, map_one]

@[simp] theorem expEval_add {ι : Type*} (v : ι → ℝ) (P Q : MvPolynomial (ι ⊕ ι) ℝ) :
    expEval v (P + Q) = expEval v P + expEval v Q := by
  simp only [expEval, map_add]

@[simp] theorem expEval_mul {ι : Type*} (v : ι → ℝ) (P Q : MvPolynomial (ι ⊕ ι) ℝ) :
    expEval v (P * Q) = expEval v P * expEval v Q := by
  simp only [expEval, map_mul]

@[simp] theorem expEval_sub {ι : Type*} (v : ι → ℝ) (P Q : MvPolynomial (ι ⊕ ι) ℝ) :
    expEval v (P - Q) = expEval v P - expEval v Q := by
  simp only [expEval, map_sub]

@[simp] theorem expEval_neg {ι : Type*} (v : ι → ℝ) (P : MvPolynomial (ι ⊕ ι) ℝ) :
    expEval v (-P) = -expEval v P := by
  simp only [expEval, map_neg]

@[simp] theorem expEval_pow {ι : Type*} (v : ι → ℝ) (P : MvPolynomial (ι ⊕ ι) ℝ) (k : ℕ) :
    expEval v (P ^ k) = expEval v P ^ k := by
  simp only [expEval, map_pow]

@[simp] theorem expEval_C {ι : Type*} (v : ι → ℝ) (r : ℝ) :
    expEval v (MvPolynomial.C r) = r := by
  simp only [expEval, MvPolynomial.eval_C]

@[simp] theorem expEval_X_inl {ι : Type*} (v : ι → ℝ) (i : ι) :
    expEval v (MvPolynomial.X (Sum.inl i)) = v i := by
  simp only [expEval, MvPolynomial.eval_X, Sum.elim_inl]

@[simp] theorem expEval_X_inr {ι : Type*} (v : ι → ℝ) (i : ι) :
    expEval v (MvPolynomial.X (Sum.inr i)) = Real.exp (v i) := by
  simp only [expEval, MvPolynomial.eval_X, Sum.elim_inr]

/-! ## Renaming the index type -/

/-- The map on exp-polynomial variable types induced by a map of index types. -/
def polyMap {ι ι' : Type*} (f : ι → ι') : (ι ⊕ ι) → (ι' ⊕ ι') := Sum.map f f

theorem polyMap_apply_inl {ι ι' : Type*} (f : ι → ι') (i : ι) :
    polyMap f (Sum.inl i) = Sum.inl (f i) := rfl

theorem polyMap_apply_inr {ι ι' : Type*} (f : ι → ι') (i : ι) :
    polyMap f (Sum.inr i) = Sum.inr (f i) := rfl

/-- `Sum.elim` is natural in the first variable of `Sum.map f id`. -/
theorem sumElim_comp_map {κ ν μ : Type*} (f : κ → ν) (y : μ → ℝ) (z : ν → ℝ) :
    Sum.elim z y ∘ Sum.map f id = Sum.elim (z ∘ f) y := by
  funext q
  rcases q with i | i <;> rfl

/-- `Sum.elim` is natural in the second variable of `Sum.map id f`. -/
theorem sumElim_comp_map_id {κ μ ν : Type*} (z : κ → ℝ) (y : ν → ℝ) (f : μ → ν) :
    Sum.elim z y ∘ Sum.map id f = Sum.elim z (y ∘ f) := by
  funext q
  rcases q with i | i <;> rfl

theorem sumElim_comp_inl {κ μ : Type*} (z : κ → ℝ) (y : μ → ℝ) :
    Sum.elim z y ∘ (Sum.inl : κ → κ ⊕ μ) = z := by
  funext a
  rfl

theorem sumElim_comp_inr {κ μ : Type*} (z : κ → ℝ) (y : μ → ℝ) :
    Sum.elim z y ∘ (Sum.inr : μ → κ ⊕ μ) = y := by
  funext a
  rfl

theorem sumElim_comp_self {κ μ : Type*} (w : κ ⊕ μ → ℝ) :
    Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := by
  funext q
  rcases q with i | i <;> rfl

theorem sumElim_comp_polyMap {κ ν : Type*} (u : ν → ℝ) (f : κ → ν) :
    (Sum.elim u (fun i => Real.exp (u i))) ∘ polyMap f =
      Sum.elim (u ∘ f) (fun i => Real.exp ((u ∘ f) i)) := by
  funext q
  rcases q with i | i <;> rfl

/-- **The master lemma.** Renaming the index type of an exp-polynomial along `f : κ → λ`
composes evaluation with `f`. -/
theorem expEval_rename {κ ν : Type*} (f : κ → ν) (u : ν → ℝ) (P : MvPolynomial (κ ⊕ κ) ℝ) :
    expEval u (MvPolynomial.rename (polyMap f) P) = expEval (u ∘ f) P := by
  simp only [expEval, MvPolynomial.eval_rename, sumElim_comp_polyMap]

/-! ## Existential definability -/

/-- The zero set of the exp-polynomial `P` in the ambient variables indexed by `κ`, with
existential witnesses indexed by `μ`. -/
def ExpZero {κ : Type*} (μ : Type) (P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ) : Set (κ → ℝ) :=
  {x | ∃ y : μ → ℝ, expEval (Sum.elim x y) P = 0}

/-- Existential definability in `ℝ_exp` for an arbitrary index type of the ambient variables:
`X` is the projection of the zero set of a single exp-polynomial along finitely many witnesses. -/
def ExpExistI {κ : Type*} (X : Set (κ → ℝ)) : Prop :=
  ∃ (μ : Type) (_ : Fintype μ), ∃ P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ, X = ExpZero μ P

theorem ExpExistI.of_eq {κ : Type*} {X Y : Set (κ → ℝ)} (h : X = Y) (hX : ExpExistI X) :
    ExpExistI Y := h ▸ hX

/-! ## An index-shuffling equivalence -/

/-- `ι ⊕ Fin (m+1) ≃ (ι ⊕ Fin m) ⊕ Fin 1`: the last coordinate of `Fin (m+1)` becomes the
`Fin 1` block. -/
def sumFinSnocEquiv (ι : Type*) (m : ℕ) : ι ⊕ Fin (m + 1) ≃ (ι ⊕ Fin m) ⊕ Fin 1 :=
  (Equiv.sumCongr (Equiv.refl ι) (finSumFinEquiv (m := m) (n := 1)).symm).trans
    (Equiv.sumAssoc ι (Fin m) (Fin 1)).symm

@[simp] theorem sumFinSnocEquiv_inl (ι : Type*) (m : ℕ) (i : ι) :
    sumFinSnocEquiv ι m (Sum.inl i) = Sum.inl (Sum.inl i) := by
  simp [sumFinSnocEquiv]

@[simp] theorem sumFinSnocEquiv_inr_castSucc (ι : Type*) (m : ℕ) (j : Fin m) :
    sumFinSnocEquiv ι m (Sum.inr j.castSucc) = Sum.inl (Sum.inr j) := by
  simp [sumFinSnocEquiv]

@[simp] theorem sumFinSnocEquiv_inr_last (ι : Type*) (m : ℕ) :
    sumFinSnocEquiv ι m (Sum.inr (Fin.last m)) = Sum.inr 0 := by
  simp [sumFinSnocEquiv]

/-- Evaluation in `Fin (n+m)` at `Fin.append x y` is evaluation in `Fin n ⊕ Fin m` at
`Sum.elim x y`, after the canonical reindexing. -/
theorem sumElim_comp_symm {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (Sum.elim x y) ∘ ⇑(finSumFinEquiv (m := n) (n := m)).symm = Fin.append x y := by
  funext i
  obtain ⟨q, rfl⟩ := (finSumFinEquiv (m := n) (n := m)).surjective i
  rcases q with j | j <;> simp [Fin.append_left, Fin.append_right]

theorem append_comp_finSumFinEquiv {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Fin.append x y ∘ ⇑(finSumFinEquiv (m := n) (n := m)) = Sum.elim x y :=
  Fin.append_comp_sumElim

/-- Mixing the `Fin (n+m)` context with a reindexing of the witness type. -/
theorem append_comp_finSum_map {n m : ℕ} {μ : Type*} (e : μ ≃ Fin m)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (Fin.append x y) ∘ (fun q => ⇑(finSumFinEquiv (m := n) (n := m)) (Sum.map id (⇑e) q))
      = Sum.elim x (y ∘ ⇑e) := by
  have h1 : (fun q => ⇑(finSumFinEquiv (m := n) (n := m)) (Sum.map id (⇑e) q))
      = ⇑(finSumFinEquiv (m := n) (n := m)) ∘ Sum.map id (⇑e) := rfl
  rw [h1, ← Function.comp_assoc, append_comp_finSumFinEquiv, sumElim_comp_map_id]

/-! ## Comparison with the frozen `ExpExist` -/

/-- `ExpExistI` (general finite witness type) agrees with the frozen `WilkiesDesign.ExpExist`
(witnesses `Fin m`, ambient `Fin n`). -/
theorem expExist_iff_expExistI {n : ℕ} (X : Set (Fin n → ℝ)) :
    WilkiesDesign.ExpExist X ↔ ExpExistI X := by
  constructor
  · rintro ⟨m, P, hP⟩
    refine ⟨Fin m, inferInstance,
      MvPolynomial.rename (polyMap ⇑(finSumFinEquiv (m := n) (n := m)).symm) P, ?_⟩
    rw [hP]
    ext x
    simp only [ExpZero, Set.mem_ofPred_eq, expEval_rename, sumElim_comp_symm,
      expPolyEval_eq_expEval]
  · rintro ⟨μ, hμ, P, hP⟩
    letI := hμ
    let e : μ ≃ Fin (Fintype.card μ) := Fintype.equivFin μ
    refine ⟨Fintype.card μ,
      MvPolynomial.rename
        (polyMap (fun q => ⇑(finSumFinEquiv (m := n) (n := Fintype.card μ))
          (Sum.map id (⇑e) q))) P, ?_⟩
    rw [hP]
    ext x
    simp only [ExpZero, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ ⇑e.symm, ?_⟩
      rw [expPolyEval_eq_expEval, expEval_rename, append_comp_finSum_map]
      have hcomp : (y ∘ ⇑e.symm) ∘ ⇑e = y := by funext q; simp
      rw [hcomp, hy]
    · rintro ⟨y, hy⟩
      refine ⟨y ∘ ⇑e, ?_⟩
      rw [expPolyEval_eq_expEval, expEval_rename] at hy
      rw [append_comp_finSum_map] at hy
      exact hy

end Work.WilkiesB
