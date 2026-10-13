/-
  Area C0 (Wilkie's conjecture for Pfaffian structures): the syntax of `ℝ_rexp`.

  The frozen hole `WilkiesDesign.CG.C0_rexp_syntax` says: every subset of `ℝⁿ` definable in the
  language `LRc` of ordered rings with the *restricted* exponential and a constant for every real
  is `RExpExist` (a projection of a zero set of a single rexp-polynomial), assuming Gabrielov's
  theorem of the complement for `ℝ_rexp` (the hypothesis `hR`).

  This file builds the vocabulary:
  * `rexpEval v P` evaluates a "rexp-polynomial" `P` at `v` (the variable `Sum.inl i` is `v i`
    and the variable `Sum.inr i` is `rexp (v i)`);
  * `RExZero μ P` is the projection of the zero set of `P` along `μ` existential witnesses;
  * `RExpExistI X` is the general form of the frozen `RExpExist` for an arbitrary index type of
    the ambient variables;
  * the closure operations used by the syntax induction: pullback along a map of index types,
    finite intersections and unions, and existential projection over a block of witnesses.
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace Work.WilC0

open WilkiesDesign (rexp)

/-! ## 1. rexp-polynomials and their evaluation -/

/-- Evaluate the rexp-polynomial `P` at `v`: the variable `Sum.inl i` is `v i` and the variable
`Sum.inr i` is `rexp (v i)`. -/
def rexpEval {κ : Type} (v : κ → ℝ) (P : MvPolynomial (κ ⊕ κ) ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim v (fun i => rexp (v i))) P

@[simp] theorem rexpEval_zero {κ : Type} (v : κ → ℝ) :
    rexpEval v (0 : MvPolynomial (κ ⊕ κ) ℝ) = 0 := by
  simp only [rexpEval, map_zero]

@[simp] theorem rexpEval_one {κ : Type} (v : κ → ℝ) :
    rexpEval v (1 : MvPolynomial (κ ⊕ κ) ℝ) = 1 := by
  simp only [rexpEval, map_one]

@[simp] theorem rexpEval_add {κ : Type} (v : κ → ℝ) (P Q : MvPolynomial (κ ⊕ κ) ℝ) :
    rexpEval v (P + Q) = rexpEval v P + rexpEval v Q := by
  simp only [rexpEval, map_add]

@[simp] theorem rexpEval_mul {κ : Type} (v : κ → ℝ) (P Q : MvPolynomial (κ ⊕ κ) ℝ) :
    rexpEval v (P * Q) = rexpEval v P * rexpEval v Q := by
  simp only [rexpEval, map_mul]

@[simp] theorem rexpEval_sub {κ : Type} (v : κ → ℝ) (P Q : MvPolynomial (κ ⊕ κ) ℝ) :
    rexpEval v (P - Q) = rexpEval v P - rexpEval v Q := by
  simp only [rexpEval, map_sub]

@[simp] theorem rexpEval_neg {κ : Type} (v : κ → ℝ) (P : MvPolynomial (κ ⊕ κ) ℝ) :
    rexpEval v (-P) = -rexpEval v P := by
  simp only [rexpEval, map_neg]

@[simp] theorem rexpEval_pow {κ : Type} (v : κ → ℝ) (P : MvPolynomial (κ ⊕ κ) ℝ) (k : ℕ) :
    rexpEval v (P ^ k) = rexpEval v P ^ k := by
  simp only [rexpEval, map_pow]

@[simp] theorem rexpEval_C {κ : Type} (v : κ → ℝ) (a : ℝ) :
    rexpEval v (MvPolynomial.C a) = a := by
  simp only [rexpEval, MvPolynomial.eval_C]

@[simp] theorem rexpEval_X_inl {κ : Type} (v : κ → ℝ) (i : κ) :
    rexpEval v (MvPolynomial.X (Sum.inl i)) = v i := by
  simp only [rexpEval, MvPolynomial.eval_X, Sum.elim_inl]

@[simp] theorem rexpEval_X_inr {κ : Type} (v : κ → ℝ) (i : κ) :
    rexpEval v (MvPolynomial.X (Sum.inr i)) = rexp (v i) := by
  simp only [rexpEval, MvPolynomial.eval_X, Sum.elim_inr]

/-! ## 2. Renaming the index type -/

section Rename

variable {κ η : Type}

/-- `Sum.elim` is natural in the second variable of `Sum.map f id`. -/
theorem sumElim_comp_map {μ : Type} (f : κ → η) (y : μ → ℝ) (z : η → ℝ) :
    Sum.elim z y ∘ Sum.map f id = Sum.elim (z ∘ f) y := by
  funext q
  rcases q with i | i <;> rfl

theorem sumElim_comp_inl {μ : Type} (z : κ → ℝ) (y : μ → ℝ) :
    Sum.elim z y ∘ (Sum.inl : κ → κ ⊕ μ) = z := by
  funext a
  rfl

theorem sumElim_comp_inr {μ : Type} (z : κ → ℝ) (y : μ → ℝ) :
    Sum.elim z y ∘ (Sum.inr : μ → κ ⊕ μ) = y := by
  funext a
  rfl

theorem sumElim_comp_map_id_inl {μ ν : Type} (z : κ → ℝ) (y : μ ⊕ ν → ℝ) :
    Sum.elim z y ∘ Sum.map id (Sum.inl : μ → μ ⊕ ν) = Sum.elim z (y ∘ Sum.inl) := by
  funext q
  rcases q with i | i <;> rfl

theorem sumElim_comp_map_id_inr {μ ν : Type} (z : κ → ℝ) (y : μ ⊕ ν → ℝ) :
    Sum.elim z y ∘ Sum.map id (Sum.inr : ν → μ ⊕ ν) = Sum.elim z (y ∘ Sum.inr) := by
  funext q
  rcases q with i | i <;> rfl

/-- Reindexing the *witness* block of a tuple: `Sum.elim z y ∘ Sum.map id g = Sum.elim z (y ∘ g)`. -/
theorem sumElim_comp_map_id {μ ν : Type} (z : κ → ℝ) (y : ν → ℝ) (g : μ → ν) :
    Sum.elim z y ∘ Sum.map id g = Sum.elim z (y ∘ g) := by
  funext q
  rcases q with i | i <;> rfl

theorem sumElim_comp_self {μ ν : Type} (w : μ ⊕ ν → ℝ) :
    Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := by
  funext q
  rcases q with i | i <;> rfl

/-- **The master lemma.** Renaming the index type of a rexp-polynomial along `f : κ → η`
composes evaluation with `f`. -/
theorem rexpEval_rename (f : κ → η) (u : η → ℝ) (P : MvPolynomial (κ ⊕ κ) ℝ) :
    rexpEval u (MvPolynomial.rename (Sum.map f f) P) = rexpEval (u ∘ f) P := by
  unfold rexpEval
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun g => MvPolynomial.eval g P) ?_
  funext q
  rcases q with i | i <;> rfl

/-- The master lemma, specialised to embedding a witness block into a larger witness block
(the `Sum.inl` half of the new block). -/
theorem rexpEval_rename_inl {κ μ ν : Type} (z : κ → ℝ) (y : μ ⊕ ν → ℝ)
    (P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ) :
    rexpEval (Sum.elim z y)
        (MvPolynomial.rename (Sum.map (Sum.map id (Sum.inl : μ → μ ⊕ ν))
          (Sum.map id (Sum.inl : μ → μ ⊕ ν))) P)
      = rexpEval (Sum.elim z (y ∘ Sum.inl)) P := by
  rw [rexpEval_rename (Sum.map id (Sum.inl : μ → μ ⊕ ν)) (Sum.elim z y) P,
    sumElim_comp_map_id_inl]

/-- The master lemma, specialised to the `Sum.inr` half of a larger witness block. -/
theorem rexpEval_rename_inr {κ μ ν : Type} (z : κ → ℝ) (y : μ ⊕ ν → ℝ)
    (P : MvPolynomial ((κ ⊕ ν) ⊕ (κ ⊕ ν)) ℝ) :
    rexpEval (Sum.elim z y)
        (MvPolynomial.rename (Sum.map (Sum.map id (Sum.inr : ν → μ ⊕ ν))
          (Sum.map id (Sum.inr : ν → μ ⊕ ν))) P)
      = rexpEval (Sum.elim z (y ∘ Sum.inr)) P := by
  rw [rexpEval_rename (Sum.map id (Sum.inr : ν → μ ⊕ ν)) (Sum.elim z y) P,
    sumElim_comp_map_id_inr]

/-- The associativity map `(κ ⊕ μ) ⊕ ν → κ ⊕ (μ ⊕ ν)`, i.e. the reindexing used when a block of
existential witnesses is split into the witnesses of two nested existential quantifiers. -/
def sumAssocMap (κ μ ν : Type) : (κ ⊕ μ) ⊕ ν → κ ⊕ (μ ⊕ ν) :=
  Sum.elim (Sum.map id (Sum.inl : μ → μ ⊕ ν)) (fun k => Sum.inr (Sum.inr k))

theorem sumElim_comp_sumAssocMap {κ μ ν : Type} (z : κ → ℝ) (w : μ ⊕ ν → ℝ) :
    (Sum.elim z w) ∘ sumAssocMap κ μ ν
      = Sum.elim (Sum.elim z (w ∘ Sum.inl)) (w ∘ Sum.inr) := by
  funext q
  rcases q with q | k
  · rcases q with a | j <;> rfl
  · rfl

theorem sumElim_assoc_inv {κ μ ν : Type} (z : κ → ℝ) (u : μ → ℝ) (y : ν → ℝ) :
    Sum.elim (Sum.elim z (Sum.elim u y ∘ Sum.inl)) (Sum.elim u y ∘ Sum.inr)
      = Sum.elim (Sum.elim z u) y := by
  funext q
  rcases q with q | k
  · rcases q with a | j <;> rfl
  · rfl

/-- The master lemma, specialised to the associativity reindexing (used for existential
projection over a block of witnesses). -/
theorem rexpEval_rename_sumAssoc {κ μ ν : Type} (z : κ → ℝ) (w : μ ⊕ ν → ℝ)
    (P : MvPolynomial (((κ ⊕ μ) ⊕ ν) ⊕ ((κ ⊕ μ) ⊕ ν)) ℝ) :
    rexpEval (Sum.elim z w)
        (MvPolynomial.rename (Sum.map (sumAssocMap κ μ ν) (sumAssocMap κ μ ν)) P)
      = rexpEval (Sum.elim (Sum.elim z (w ∘ Sum.inl)) (w ∘ Sum.inr)) P := by
  rw [rexpEval_rename (sumAssocMap κ μ ν) (Sum.elim z w) P, sumElim_comp_sumAssocMap]

end Rename

/-! ## 3. Existential definability -/

/-- The zero set of the rexp-polynomial `P`, in the ambient variables indexed by `κ`, with `μ`
existential witnesses. -/
def RExZero {κ : Type} (μ : Type) (P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ) : Set (κ → ℝ) :=
  {x | ∃ y : μ → ℝ, rexpEval (Sum.elim x y) P = 0}

/-- Existential definability in `ℝ_rexp`, for an arbitrary index type of the ambient variables:
`X` is the projection of the zero set of one rexp-polynomial along finitely many witnesses. -/
def RExpExistI {κ : Type} (X : Set (κ → ℝ)) : Prop :=
  ∃ (μ : Type) (_ : Fintype μ), ∃ P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ, X = RExZero μ P

/-- A "hypersurface" set: the zero set of a rexp-polynomial in the ambient variables only. -/
def RExPoly {κ : Type} (P : MvPolynomial (κ ⊕ κ) ℝ) : Set (κ → ℝ) := {z | rexpEval z P = 0}

@[simp] theorem mem_RExZero {κ μ : Type} (P : MvPolynomial ((κ ⊕ μ) ⊕ (κ ⊕ μ)) ℝ)
    (z : κ → ℝ) : z ∈ RExZero μ P ↔ ∃ y : μ → ℝ, rexpEval (Sum.elim z y) P = 0 := Iff.rfl

@[simp] theorem mem_RExPoly {κ : Type} (P : MvPolynomial (κ ⊕ κ) ℝ) (z : κ → ℝ) :
    z ∈ RExPoly P ↔ rexpEval z P = 0 := Iff.rfl

theorem RExpExistI.of_eq {κ : Type} {X Y : Set (κ → ℝ)} (h : X = Y) (hX : RExpExistI X) :
    RExpExistI Y := h ▸ hX

/-- Every hypersurface is existentially definable (with no witnesses). -/
theorem RExpExistI.rexPoly {κ : Type} (P : MvPolynomial (κ ⊕ κ) ℝ) :
    RExpExistI (RExPoly P) := by
  refine ⟨Fin 0, inferInstance,
    MvPolynomial.rename (Sum.map (Sum.inl : κ → κ ⊕ Fin 0) (Sum.inl : κ → κ ⊕ Fin 0)) P, ?_⟩
  ext z
  constructor
  · intro h
    exact ⟨Fin.elim0, by
      rw [rexpEval_rename (Sum.inl : κ → κ ⊕ Fin 0) (Sum.elim z Fin.elim0) P,
        sumElim_comp_inl]
      exact h⟩
  · rintro ⟨y, hy⟩
    rw [rexpEval_rename (Sum.inl : κ → κ ⊕ Fin 0) (Sum.elim z y) P, sumElim_comp_inl] at hy
    exact hy

/-! ## 4. Pullback along a map of index types -/

theorem RExpExistI.pullback {κ η : Type} (f : κ → η) {X : Set (κ → ℝ)} (hX : RExpExistI X) :
    RExpExistI {z : η → ℝ | z ∘ f ∈ X} := by
  obtain ⟨μ, hμ, P, rfl⟩ := hX
  refine ⟨μ, hμ, MvPolynomial.rename (Sum.map (Sum.map f id) (Sum.map f id)) P, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by
      rw [rexpEval_rename (Sum.map f id) (Sum.elim z y) P, sumElim_comp_map]
      exact hy⟩
  · rintro ⟨y, hy⟩
    rw [rexpEval_rename (Sum.map f id) (Sum.elim z y) P, sumElim_comp_map] at hy
    exact ⟨y, hy⟩

/-! ## 5. Boolean operations -/

theorem RExpExistI.univ {κ : Type} : RExpExistI (Set.univ : Set (κ → ℝ)) := by
  refine ⟨Fin 0, inferInstance, 0, ?_⟩
  ext z
  constructor
  · intro _
    exact ⟨Fin.elim0, by simp⟩
  · intro _
    trivial

theorem RExpExistI.empty {κ : Type} : RExpExistI (∅ : Set (κ → ℝ)) := by
  refine ⟨Fin 1, inferInstance,
    MvPolynomial.X (Sum.inr (Sum.inr (0 : Fin 1))) ^ 2 + 1, ?_⟩
  ext z
  constructor
  · intro h
    exact absurd h (Set.notMem_empty z)
  · rintro ⟨y, hy⟩
    have h : rexpEval (Sum.elim z y) (MvPolynomial.X (Sum.inr (Sum.inr (0 : Fin 1))) ^ 2 + 1)
        = rexp (y 0) ^ 2 + 1 := by simp
    rw [h] at hy
    nlinarith [sq_nonneg (rexp (y 0))]

theorem RExpExistI.inter {κ : Type} {X Y : Set (κ → ℝ)} (hX : RExpExistI X)
    (hY : RExpExistI Y) : RExpExistI (X ∩ Y) := by
  obtain ⟨μ, hμ, P, rfl⟩ := hX
  obtain ⟨ν, hν, Q, rfl⟩ := hY
  letI := hμ
  letI := hν
  refine ⟨μ ⊕ ν, inferInstance,
    MvPolynomial.rename (Sum.map (Sum.map id (Sum.inl : μ → μ ⊕ ν))
        (Sum.map id (Sum.inl : μ → μ ⊕ ν))) P ^ 2 +
    MvPolynomial.rename (Sum.map (Sum.map id (Sum.inr : ν → μ ⊕ ν))
        (Sum.map id (Sum.inr : ν → μ ⊕ ν))) Q ^ 2, ?_⟩
  ext z
  simp only [mem_RExZero, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨Sum.elim u v, ?_⟩
    rw [rexpEval_add, rexpEval_pow, rexpEval_pow, rexpEval_rename_inl, rexpEval_rename_inr,
      sumElim_comp_inl, sumElim_comp_inr, hu, hv]
    ring
  · rintro ⟨y, hy⟩
    rw [rexpEval_add, rexpEval_pow, rexpEval_pow, rexpEval_rename_inl, rexpEval_rename_inr] at hy
    have h1 : rexpEval (Sum.elim z (y ∘ Sum.inl)) P = 0 := by
      have h2 : rexpEval (Sum.elim z (y ∘ Sum.inl)) P ^ 2 = 0 := by
        linarith [sq_nonneg (rexpEval (Sum.elim z (y ∘ Sum.inl)) P),
          sq_nonneg (rexpEval (Sum.elim z (y ∘ Sum.inr)) Q), hy]
      exact sq_eq_zero_iff.mp h2
    have h3 : rexpEval (Sum.elim z (y ∘ Sum.inr)) Q = 0 := by
      have h2 : rexpEval (Sum.elim z (y ∘ Sum.inr)) Q ^ 2 = 0 := by
        linarith [sq_nonneg (rexpEval (Sum.elim z (y ∘ Sum.inl)) P),
          sq_nonneg (rexpEval (Sum.elim z (y ∘ Sum.inr)) Q), hy]
      exact sq_eq_zero_iff.mp h2
    exact ⟨⟨y ∘ Sum.inl, h1⟩, ⟨y ∘ Sum.inr, h3⟩⟩

theorem RExpExistI.union {κ : Type} {X Y : Set (κ → ℝ)} (hX : RExpExistI X)
    (hY : RExpExistI Y) : RExpExistI (X ∪ Y) := by
  obtain ⟨μ, hμ, P, rfl⟩ := hX
  obtain ⟨ν, hν, Q, rfl⟩ := hY
  letI := hμ
  letI := hν
  refine ⟨μ ⊕ ν, inferInstance,
    MvPolynomial.rename (Sum.map (Sum.map id (Sum.inl : μ → μ ⊕ ν))
        (Sum.map id (Sum.inl : μ → μ ⊕ ν))) P *
    MvPolynomial.rename (Sum.map (Sum.map id (Sum.inr : ν → μ ⊕ ν))
        (Sum.map id (Sum.inr : ν → μ ⊕ ν))) Q, ?_⟩
  ext z
  simp only [mem_RExZero, Set.mem_union]
  constructor
  · rintro (⟨u, hu⟩ | ⟨v, hv⟩)
    · refine ⟨Sum.elim u (0 : ν → ℝ), ?_⟩
      rw [rexpEval_mul, rexpEval_rename_inl, rexpEval_rename_inr, sumElim_comp_inl,
        sumElim_comp_inr, hu]
      ring
    · refine ⟨Sum.elim (0 : μ → ℝ) v, ?_⟩
      rw [rexpEval_mul, rexpEval_rename_inl, rexpEval_rename_inr, sumElim_comp_inl,
        sumElim_comp_inr, hv]
      ring
  · rintro ⟨y, hy⟩
    rw [rexpEval_mul, rexpEval_rename_inl, rexpEval_rename_inr] at hy
    rcases mul_eq_zero.mp hy with h | h
    · exact Or.inl ⟨y ∘ Sum.inl, h⟩
    · exact Or.inr ⟨y ∘ Sum.inr, h⟩

/-- Finite intersections. -/
theorem RExpExistI.iInter_fin {κ : Type} : ∀ (r : ℕ) (X : Fin r → Set (κ → ℝ)),
    (∀ i, RExpExistI (X i)) → RExpExistI (⋂ i, X i)
  | 0, X, _ => by
    rw [show (⋂ i : Fin 0, X i) = Set.univ from by
      ext z
      simp]
    exact RExpExistI.univ
  | r + 1, X, h => by
    have hsplit : (⋂ i : Fin (r + 1), X i) =
        (⋂ i : Fin r, X (Fin.castSucc i)) ∩ X (Fin.last r) := by
      ext z
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro hz
        exact ⟨fun i => hz _, hz _⟩
      · rintro ⟨h1, h2⟩ i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact h1 j
        · exact h2
    rw [hsplit]
    exact (RExpExistI.iInter_fin r (fun i => X (Fin.castSucc i)) (fun i => h _)).inter (h _)

/-- Finite unions. -/
theorem RExpExistI.iUnion_fin {κ : Type} : ∀ (r : ℕ) (X : Fin r → Set (κ → ℝ)),
    (∀ i, RExpExistI (X i)) → RExpExistI (⋃ i, X i)
  | 0, X, _ => by
    rw [show (⋃ i : Fin 0, X i) = (∅ : Set (κ → ℝ)) from by
      ext z
      simp]
    exact RExpExistI.empty
  | r + 1, X, h => by
    have hsplit : (⋃ i : Fin (r + 1), X i) =
        (⋃ i : Fin r, X (Fin.castSucc i)) ∪ X (Fin.last r) := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Or.inl ⟨j, hi⟩
        · exact Or.inr hi
      · rintro (⟨j, hj⟩ | hlast)
        · exact ⟨Fin.castSucc j, hj⟩
        · exact ⟨Fin.last r, hlast⟩
    rw [hsplit]
    exact (RExpExistI.iUnion_fin r (fun i => X (Fin.castSucc i)) (fun i => h _)).union (h _)

/-! ## 6. Existential projection over a block of witnesses -/

/-- Projecting a block `μ` of coordinates away is existential quantification over them. -/
theorem RExpExistI.existsBlock {κ : Type} {μ : Type} [Fintype μ] {X : Set ((κ ⊕ μ) → ℝ)}
    (hX : RExpExistI X) :
    RExpExistI {z : κ → ℝ | ∃ u : μ → ℝ, Sum.elim z u ∈ X} := by
  obtain ⟨ν, hν, P, rfl⟩ := hX
  letI := hν
  refine ⟨μ ⊕ ν, inferInstance,
    MvPolynomial.rename (Sum.map (sumAssocMap κ μ ν) (sumAssocMap κ μ ν)) P, ?_⟩
  ext z
  simp only [mem_RExZero]
  constructor
  · rintro ⟨u, y, hy⟩
    exact ⟨Sum.elim u y, by
      rw [rexpEval_rename_sumAssoc, sumElim_assoc_inv]
      exact hy⟩
  · rintro ⟨w, hw⟩
    exact ⟨w ∘ Sum.inl, w ∘ Sum.inr, by
      rw [rexpEval_rename_sumAssoc] at hw
      exact hw⟩

/-- Existential quantification over a single real variable. -/
theorem RExpExistI.projLast {κ : Type} {X : Set ((κ ⊕ Fin 1) → ℝ)} (hX : RExpExistI X) :
    RExpExistI {z : κ → ℝ | ∃ a : ℝ, Sum.elim z (fun _ : Fin 1 => a) ∈ X} := by
  refine (hX.existsBlock (μ := Fin 1)).of_eq ?_
  ext z
  constructor
  · rintro ⟨u, hu⟩
    have hu' : u = fun _ : Fin 1 => u 0 := funext fun i => by simp [Subsingleton.elim i 0]
    exact ⟨u 0, by rw [hu'] at hu; exact hu⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, ha⟩

end Work.WilC0
