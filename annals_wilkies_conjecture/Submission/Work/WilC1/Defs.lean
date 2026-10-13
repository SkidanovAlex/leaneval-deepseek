/-
  WilC1 — area C1 of the Wilkie / van den Dries–Macintyre–Marker development.

  Vocabulary: `rexpEval` (evaluation of a polynomial in `z` and `rexp z` over an arbitrary
  index type) and `REx`, existential definability in `ℝ_rexp` with a witness block of an
  arbitrary finite type — the flexible form of the frozen `WilkiesDesign.RExpExist` that the
  closure lemmas are proved in.

  Conventions of `REx X` (`X : Set (ι → ℝ)`):
  * witnesses are indexed by a finite type `γ`, so that block-combining needs no `Fin` arithmetic;
  * the polynomial lives in `MvPolynomial ((ι ⊕ γ) ⊕ (ι ⊕ γ)) ℝ`, variables `Sum.inl q` meaning
    "the `q`-th coordinate" and `Sum.inr q` meaning "`rexp` of the `q`-th coordinate".
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-! ## 1. `rexp`-evaluation of polynomials -/

/-- Evaluate the polynomial `P` in the coordinates `v` and the `rexp` of the coordinates. -/
def rexpEval {ι : Type*} (v : ι → ℝ) (P : MvPolynomial (ι ⊕ ι) ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim v (fun i => rexp (v i))) P

variable {ι : Type*} {ι' : Type*}

@[simp] theorem rexpEval_zero (v : ι → ℝ) : rexpEval v (0 : MvPolynomial (ι ⊕ ι) ℝ) = 0 := by
  simp only [rexpEval]
  exact map_zero _

@[simp] theorem rexpEval_one (v : ι → ℝ) : rexpEval v (1 : MvPolynomial (ι ⊕ ι) ℝ) = 1 := by
  simp only [rexpEval]
  exact map_one _

@[simp] theorem rexpEval_add (v : ι → ℝ) (P Q : MvPolynomial (ι ⊕ ι) ℝ) :
    rexpEval v (P + Q) = rexpEval v P + rexpEval v Q := by
  simp only [rexpEval]
  exact map_add _ P Q

@[simp] theorem rexpEval_mul (v : ι → ℝ) (P Q : MvPolynomial (ι ⊕ ι) ℝ) :
    rexpEval v (P * Q) = rexpEval v P * rexpEval v Q := by
  simp only [rexpEval]
  exact map_mul _ P Q

@[simp] theorem rexpEval_sub (v : ι → ℝ) (P Q : MvPolynomial (ι ⊕ ι) ℝ) :
    rexpEval v (P - Q) = rexpEval v P - rexpEval v Q := by
  simp only [rexpEval]
  exact map_sub _ P Q

@[simp] theorem rexpEval_neg (v : ι → ℝ) (P : MvPolynomial (ι ⊕ ι) ℝ) :
    rexpEval v (-P) = -rexpEval v P := by
  simp only [rexpEval]
  exact map_neg _ P

@[simp] theorem rexpEval_pow (v : ι → ℝ) (P : MvPolynomial (ι ⊕ ι) ℝ) (k : ℕ) :
    rexpEval v (P ^ k) = rexpEval v P ^ k := by
  simp only [rexpEval]
  exact map_pow _ P k

@[simp] theorem rexpEval_natCast (v : ι → ℝ) (k : ℕ) :
    rexpEval v ((k : MvPolynomial (ι ⊕ ι) ℝ)) = k := by
  simp only [rexpEval]
  exact map_natCast _ k

theorem rexpEval_sum {κ : Type*} (v : ι → ℝ) (s : Finset κ) (f : κ → MvPolynomial (ι ⊕ ι) ℝ) :
    rexpEval v (∑ i ∈ s, f i) = ∑ i ∈ s, rexpEval v (f i) := by
  simp only [rexpEval]
  exact map_sum _ _ _

theorem rexpEval_sum_univ {κ : Type*} [Fintype κ] (v : ι → ℝ)
    (f : κ → MvPolynomial (ι ⊕ ι) ℝ) :
    rexpEval v (∑ i, f i) = ∑ i, rexpEval v (f i) := by
  simp only [rexpEval]
  exact map_sum _ _ _

@[simp] theorem rexpEval_C (v : ι → ℝ) (r : ℝ) : rexpEval v (MvPolynomial.C r) = r := by
  simp [rexpEval]

@[simp] theorem rexpEval_X_inl (v : ι → ℝ) (i : ι) :
    rexpEval v (MvPolynomial.X (Sum.inl i)) = v i := by
  simp only [rexpEval, MvPolynomial.eval_X, Sum.elim_inl]

@[simp] theorem rexpEval_X_inr (v : ι → ℝ) (i : ι) :
    rexpEval v (MvPolynomial.X (Sum.inr i)) = rexp (v i) := by
  simp only [rexpEval, MvPolynomial.eval_X, Sum.elim_inr]

/-- The map on the variable types of `MvPolynomial (ι ⊕ ι) ℝ` induced by `f : ι → ι'`. -/
def polyMap (f : ι → ι') : (ι ⊕ ι) → (ι' ⊕ ι') := Sum.map f f

theorem polyMap_inl (f : ι → ι') (i : ι) : polyMap f (Sum.inl i) = Sum.inl (f i) := rfl
theorem polyMap_inr (f : ι → ι') (i : ι) : polyMap f (Sum.inr i) = Sum.inr (f i) := rfl

theorem sumElim_comp_polyMap (v : ι' → ℝ) (f : ι → ι') :
    (Sum.elim v (fun i => rexp (v i))) ∘ polyMap f =
      Sum.elim (v ∘ f) (fun i => rexp ((v ∘ f) i)) := by
  funext q
  rcases q with i | i <;> rfl

/-- Renaming the index type of an exp-polynomial does not change its evaluation. -/
theorem rexpEval_rename (v : ι' → ℝ) (f : ι → ι') (P : MvPolynomial (ι ⊕ ι) ℝ) :
    rexpEval v (MvPolynomial.rename (polyMap f) P) = rexpEval (v ∘ f) P := by
  simp only [rexpEval, MvPolynomial.eval_rename, sumElim_comp_polyMap]

/-! ## 2. `REx`: existential definability with an arbitrary finite witness type -/

/-- `REx X` for `X : Set (ι → ℝ)`: `X` is the projection of the zero set of one polynomial in the
coordinates and their `rexp`s, with a block of witnesses indexed by a finite type `γ`. -/
def REx (ι : Type*) (X : Set (ι → ℝ)) : Prop :=
  ∃ (γ : Type) (_ : Fintype γ) (P : MvPolynomial ((ι ⊕ γ) ⊕ (ι ⊕ γ)) ℝ),
    X = {x | ∃ y : γ → ℝ, rexpEval (Sum.elim x y) P = 0}

theorem REx.congr {X Y : Set (ι → ℝ)} (h : X = Y) : REx ι X → REx ι Y := h ▸ id

/-- The zero set of a polynomial is `REx` (no witnesses). -/
theorem REx.zeroSet (P : MvPolynomial (ι ⊕ ι) ℝ) : REx ι {x : ι → ℝ | rexpEval x P = 0} := by
  refine ⟨PEmpty, inferInstance,
    MvPolynomial.rename (polyMap (Sum.inl : ι → ι ⊕ PEmpty)) P, ?_⟩
  ext x
  constructor
  · intro h
    exact ⟨fun e => e.elim, by simpa [rexpEval_rename, Sum.elim_comp_inl] using h⟩
  · rintro ⟨y, hy⟩
    simpa [rexpEval_rename, Sum.elim_comp_inl] using hy

/-- The whole space is `REx`. -/
theorem REx.univ : REx ι (Set.univ : Set (ι → ℝ)) := by
  refine ⟨PEmpty, inferInstance, (0 : MvPolynomial ((ι ⊕ PEmpty) ⊕ (ι ⊕ PEmpty)) ℝ), ?_⟩
  ext x
  simp

/-- The empty set is `REx`. -/
theorem REx.empty : REx ι (∅ : Set (ι → ℝ)) := by
  refine ⟨PEmpty, inferInstance,
    MvPolynomial.rename (polyMap (Sum.inl : ι → ι ⊕ PEmpty)) (1 : MvPolynomial (ι ⊕ ι) ℝ), ?_⟩
  ext x
  constructor
  · intro h
    exact absurd h (by simp)
  · rintro ⟨y, hy⟩
    rw [rexpEval_rename, Sum.elim_comp_inl, rexpEval_one] at hy
    exact one_ne_zero hy

/-! ## 3. Term constructors of `LRc` and their realization -/

/-- The variable term. -/
def tVar {τ : Type*} (i : τ) : LRc.Term τ := Term.var i

/-- A constant-symbol term (every real is a constant symbol of `LRc`). -/
def tConst {τ : Type*} (r : ℝ) : LRc.Term τ :=
  Term.func (L := LRc) (α := τ) (l := 0) (Sum.inr r) (fun i => i.elim0)

/-- The ring constant `0`. -/
def tZero {τ : Type*} : LRc.Term τ :=
  Term.func (L := LRc) (α := τ) (l := 0) (Sum.inl (Sum.inl Ring.zeroFunc)) (fun i => i.elim0)

/-- The ring constant `1`. -/
def tOne {τ : Type*} : LRc.Term τ :=
  Term.func (L := LRc) (α := τ) (l := 0) (Sum.inl (Sum.inl Ring.oneFunc)) (fun i => i.elim0)

/-- Sum of two terms. -/
def tAdd {τ : Type*} (a b : LRc.Term τ) : LRc.Term τ :=
  Term.func (L := LRc) (α := τ) (l := 2) (Sum.inl (Sum.inl Ring.addFunc)) ![a, b]

/-- Product of two terms. -/
def tMul {τ : Type*} (a b : LRc.Term τ) : LRc.Term τ :=
  Term.func (L := LRc) (α := τ) (l := 2) (Sum.inl (Sum.inl Ring.mulFunc)) ![a, b]

/-- Negation of a term. -/
def tNeg {τ : Type*} (a : LRc.Term τ) : LRc.Term τ :=
  Term.func (L := LRc) (α := τ) (l := 1) (Sum.inl (Sum.inl Ring.negFunc)) ![a]

/-- The restricted exponential of a term. -/
def tRexp {τ : Type*} (a : LRc.Term τ) : LRc.Term τ :=
  Term.func (L := LRc) (α := τ) (l := 1) (Sum.inl (Sum.inr rexpFunc.rexp)) ![a]

@[simp] theorem realize_tVar {τ : Type*} (v : τ → ℝ) (i : τ) :
    Term.realize v (tVar i) = v i := rfl

@[simp] theorem realize_tConst {τ : Type*} (v : τ → ℝ) (r : ℝ) :
    Term.realize v (tConst (τ := τ) r) = r := by
  rw [tConst]; rfl

@[simp] theorem realize_tZero {τ : Type*} (v : τ → ℝ) :
    Term.realize v (tZero (τ := τ)) = 0 := by
  rw [tZero]; rfl

@[simp] theorem realize_tOne {τ : Type*} (v : τ → ℝ) :
    Term.realize v (tOne (τ := τ)) = 1 := by
  rw [tOne]; rfl

@[simp] theorem realize_tAdd {τ : Type*} (v : τ → ℝ) (a b : LRc.Term τ) :
    Term.realize v (tAdd a b) = Term.realize v a + Term.realize v b := by
  rw [tAdd]; rfl

@[simp] theorem realize_tMul {τ : Type*} (v : τ → ℝ) (a b : LRc.Term τ) :
    Term.realize v (tMul a b) = Term.realize v a * Term.realize v b := by
  rw [tMul]; rfl

@[simp] theorem realize_tNeg {τ : Type*} (v : τ → ℝ) (a : LRc.Term τ) :
    Term.realize v (tNeg a) = - Term.realize v a := by
  rw [tNeg]; rfl

@[simp] theorem realize_tRexp {τ : Type*} (v : τ → ℝ) (a : LRc.Term τ) :
    Term.realize v (tRexp a) = rexp (Term.realize v a) := by
  rw [tRexp]; rfl

/-- `LRc` has no relation symbols. -/
theorem isEmpty_rel (k : ℕ) : IsEmpty (LRc.Relations k) :=
  ⟨fun x => nomatch (Eq.mp (show LRc.Relations k = ((Empty ⊕ Empty) ⊕ Empty : Type) from rfl) x)⟩

/-! ## 4. Graphs of terms, realization sets of formulas -/

/-- The graph of the term function of `t`, inside `ℝ^{ι ⊕ Fin 1}` (last coordinate = value). -/
def GraphSet {ι : Type*} (t : LRc.Term ι) : Set ((ι ⊕ Fin 1) → ℝ) :=
  {x | x (Sum.inr 0) = Term.realize (x ∘ Sum.inl) t}

/-- The realization set of `φ : LRc.BoundedFormula α k` on the index type `α ⊕ Fin k`. -/
def Sof {α : Type*} {k : ℕ} (φ : LRc.BoundedFormula α k) : Set ((α ⊕ Fin k) → ℝ) :=
  {w | φ.Realize (w ∘ Sum.inl) (w ∘ Sum.inr)}

end Work.WilC1
