/-
  WilC4 : `exists_altChain_formula`: `AltChain N {t | φ(p, t)}` is an `LRc`-formula in `p`.

  `AltChain N S` (`Work.WilC4.UnifDefs`) says that `S` contains `N + 1` points separated by `N`
  points *outside* `S`; in a linear order this means that `S` has at least `N + 1` order-convex
  components.  This file shows that the family

      p ↦ AltChain N {t : M | φ.Realize (Sum.elim p (fun _ => t))}

  is itself definable by a single `LRc`-formula with `n` free variables: `∃ x y, …` where the
  points `x j` are required to satisfy `φ`, the separating points `y j` to satisfy `¬φ`, and the
  betweenness conditions are written in the language of rings, which `LRc` contains.

  Since `L_ring` has no relation symbol for `<`, the strict order has to be expressed through the
  field operations; on any model of the hypotheses of the statement (an ordered field in which
  every nonnegative element is a square) the ring formula
  `∃ z w, u + z * z = v ∧ w * z = 1` says exactly `u < v`.  That is `acLtF` below.

  Nothing here is model theory: it is the syntax of `AltChain` in `LRc`, together with the
  (elementary) semantic verification of the formula that is produced.
-/
import Mathlib
import Submission.Work.WilC4.UnifDefs
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.Convert

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Strict order in the language of rings

  `L_ring` has no order symbol, so `<` is written with the field operations.  In any model in
  which every nonnegative element is a square, `u < v` is equivalent to "`v - u` is a nonzero
  square", i.e. to `∃ z w, u + z * z = v ∧ w * z = 1` (`w` witnesses `z ≠ 0`).  The
  quantifier-free part is written with the two bound variables `z`, `w`; a single `exs`
  quantifies both. -/

/-- The `ring`-formula `∃ z w, v 0 + z * z = v 1 ∧ w * z = 1`, which expresses `v 0 < v 1` in
every ordered field in which nonnegative elements are squares. -/
def acLtF : Language.ring.Formula (Fin 2) :=
  ((Term.bdEqual
      (Term.var (Sum.inl (0 : Fin 2)) +
        Term.var (Sum.inr (0 : Fin 2)) * Term.var (Sum.inr (0 : Fin 2)))
      (Term.var (Sum.inl (1 : Fin 2)))) ⊓
    (Term.bdEqual
      (Term.var (Sum.inr (1 : Fin 2)) * Term.var (Sum.inr (0 : Fin 2)))
      (1 : Language.ring.Term (Fin 2 ⊕ Fin 2)))).exs

/-- **The semantics of `acLtF`.** -/
theorem acLtF_realize {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (a b : M) :
    acLtF.Realize ![a, b] ↔ a < b := by
  simp only [acLtF, BoundedFormula.realize_exs, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul, Ring.realize_one,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨xs, h1, h2⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
    have hz : xs 0 ≠ 0 := by
      intro h
      rw [h, mul_zero] at h2
      exact zero_ne_one h2
    have hpos : 0 < xs 0 * xs 0 := mul_self_pos.mpr hz
    linarith
  · intro h
    have hpos : 0 < b - a := by linarith
    obtain ⟨z, hz⟩ := hsq (b - a) hpos.le
    have hzne : z ≠ 0 := by
      intro h'
      rw [h', mul_zero] at hz
      linarith
    refine ⟨Fin.cases z (fun _ : Fin 1 => z⁻¹), ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.cases_zero]
      linarith
    · simp only [Fin.cases_zero]
      exact inv_mul_cancel₀ hzne

/-! ## 2. Relocating ring formulas to `LRc`

  `LRc = (L_ring ⊕ L_rexp)[[ℝ]]`, so ring formulas can be transported to `LRc` along the
  canonical language map.  The definitions below duplicate what `WilC2.Basic` does for two
  reasons: the arguments are universe-polymorphic (`M : Type*`, as in the target statement,
  whereas `WilC2`'s versions are stated for `M : Type`), and the `IsExpansionOn` instance is
  provided for `M : Type*` as well. -/

/-- The inclusion of the language of rings in `LRc = (ring ⊕ rexp)[[ℝ]]`. -/
def altRingToLRc : Language.ring →ᴸ LRc :=
  (LHom.sumInl : LR →ᴸ LRc).comp (LHom.sumInl : Language.ring →ᴸ LR)

instance instAltRingToLRcIsExpansionOn (M : Type*) [Language.ring.Structure M]
    [rexpL.Structure M] [(constantsOn ℝ).Structure M] : altRingToLRc.IsExpansionOn M :=
  ⟨fun {n} f x => by cases f <;> rfl, fun {n} R _ => isEmptyElim R⟩

/-- The `LRc`-formula obtained from the `ring`-formula `F` by renaming its free variables along
`f`. -/
def altLift {k : ℕ} {α : Type*} (f : Fin k → α) (F : Language.ring.Formula (Fin k)) :
    LRc.Formula α :=
  Formula.relabel f (altRingToLRc.onFormula F)

theorem altLift_realize {k : ℕ} {α : Type*} (f : Fin k → α)
    (F : Language.ring.Formula (Fin k)) {M : Type*} [Language.ring.Structure M]
    [LRc.Structure M] [altRingToLRc.IsExpansionOn M] (v : α → M) :
    (altLift f F).Realize v ↔ F.Realize (v ∘ f) := by
  rw [altLift, Formula.realize_relabel, LHom.realize_onFormula]

/-! ## 3. The variables and the body of the `AltChain` formula

  The body has one variable per parameter (`Fin n`), one per point `x j` (`Fin (N + 1)`) and one
  per separating point `y j` (`Fin N`); in the sum type `ACVar n N = Fin n ⊕ (Fin (N+1) ⊕ Fin N)`
  the first summand holds the parameters, so that existentially quantifying the second summand
  (`Formula.iExs`) leaves an `LRc`-formula in the parameters alone. -/

/-- The variables of the `AltChain` body: `n` parameters, `N + 1` points `x`, `N` separating
points `y`. -/
abbrev ACVar (n N : ℕ) := Fin n ⊕ (Fin (N + 1) ⊕ Fin N)

/-- The parameter variable `i`. -/
def acParam {n N : ℕ} (i : Fin n) : ACVar n N := Sum.inl i

/-- The point variable `x j`. -/
def acPt {n N : ℕ} (j : Fin (N + 1)) : ACVar n N := Sum.inr (Sum.inl j)

/-- The separating point variable `y j`. -/
def acSep {n N : ℕ} (j : Fin N) : ACVar n N := Sum.inr (Sum.inr j)

/-- `φ` with its parameters the parameters and its point variable the variable `x`. -/
def acEval {n N : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin 1)) (x : ACVar n N) :
    LRc.Formula (ACVar n N) :=
  φ.relabel (Sum.elim acParam (fun _ : Fin 1 => x))

/-- The variable renaming used by `acEval`. -/
theorem acEval_comp {M : Type*} {n N : ℕ} (p : Fin n → M) (i : (Fin (N + 1) ⊕ Fin N) → M)
    (x : ACVar n N) :
    Sum.elim p i ∘ (Sum.elim acParam (fun _ : Fin 1 => x)) =
      Sum.elim p (fun _ : Fin 1 => Sum.elim p i x) := by
  funext b
  rcases b with b | b <;> rfl

theorem acEval_realize {M : Type*} [LRc.Structure M] {n N : ℕ}
    (φ : LRc.Formula (Fin n ⊕ Fin 1)) (x : ACVar n N) (p : Fin n → M)
    (i : (Fin (N + 1) ⊕ Fin N) → M) :
    (acEval φ x).Realize (Sum.elim p i) ↔ φ.Realize (Sum.elim p (fun _ => Sum.elim p i x)) := by
  rw [acEval, Formula.realize_relabel, acEval_comp]

/-- The `LRc`-formula `v a < v b`. -/
def acLt {n N : ℕ} (a b : ACVar n N) : LRc.Formula (ACVar n N) := altLift ![a, b] acLtF

theorem acLt_realize {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [LRc.Structure M] [altRingToLRc.IsExpansionOn M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) {n N : ℕ} (a b : ACVar n N)
    (v : ACVar n N → M) : (acLt a b).Realize v ↔ v a < v b := by
  have h : v ∘ ![a, b] = ![v a, v b] := by
    funext k
    fin_cases k <;> simp
  rw [acLt, altLift_realize, h, acLtF_realize hsq (v a) (v b)]

/-- **The body of the `AltChain` formula.**  It is the conjunction of

  * `φ` at every point variable `x j`,
  * `¬φ` at every separating point variable `y j`, together with `x j < y j < x (j+1)`. -/
def acBody {n : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin 1)) (N : ℕ) : LRc.Formula (ACVar n N) :=
  (Formula.iInf (fun j : Fin (N + 1) => acEval (N := N) φ (acPt j))) ⊓
    (Formula.iInf (fun j : Fin N =>
      (∼(acEval φ (acSep j))) ⊓ ((acLt (acPt (Fin.castSucc j)) (acSep j)) ⊓
        (acLt (acSep j) (acPt (Fin.succ j))))))

/-- **The syntax of `AltChain`.**  Quantifying the `x` and `y` variables of `acBody` leaves an
`LRc`-formula in the parameters. -/
def acFormula {n : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin 1)) (N : ℕ) : LRc.Formula (Fin n) :=
  (acBody φ N).iExs (Fin (N + 1) ⊕ Fin N)

/-- **The semantics of the body.** -/
theorem acBody_realize {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [LRc.Structure M] [altRingToLRc.IsExpansionOn M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    {n : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin 1)) (N : ℕ) (p : Fin n → M)
    (i : (Fin (N + 1) ⊕ Fin N) → M) :
    (acBody φ N).Realize (Sum.elim p i) ↔
      (∀ j : Fin (N + 1), φ.Realize (Sum.elim p (fun _ => i (Sum.inl j)))) ∧
      (∀ j : Fin N, ¬φ.Realize (Sum.elim p (fun _ => i (Sum.inr j))) ∧
        i (Sum.inl (Fin.castSucc j)) < i (Sum.inr j) ∧
        i (Sum.inr j) < i (Sum.inl (Fin.succ j))) := by
  simp only [acBody, Formula.realize_inf, Formula.realize_iInf, Formula.realize_not,
    acEval_realize, acLt_realize hsq, Sum.elim_inr, acPt, acSep]

/-! ## 4. The main theorem -/

theorem exists_altChain_formula {n : ℕ} (φ : WilkiesDesign.CG.LRc.Formula (Fin n ⊕ Fin 1)) (N : ℕ) :
    ∃ F : WilkiesDesign.CG.LRc.Formula (Fin n),
      ∀ (M : Type*) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
        [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
        (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (p : Fin n → M),
        (F.Realize p ↔ AltChain N {t : M | φ.Realize (Sum.elim p (fun _ => t))}) := by
  refine ⟨acFormula φ N, ?_⟩
  intro M _ _ _ _ _ _ hsq p
  rw [acFormula, Formula.realize_iExs]
  constructor
  · rintro ⟨i, hi⟩
    rw [acBody_realize hsq φ N p i] at hi
    exact ⟨fun j => i (Sum.inl j), fun j => i (Sum.inr j), fun j => hi.1 j, fun j => hi.2 j⟩
  · rintro ⟨x, y, hx, hy⟩
    refine ⟨Sum.elim x y, ?_⟩
    rw [acBody_realize hsq φ N p (Sum.elim x y)]
    exact ⟨fun j => hx j, fun j => hy j⟩

end Work.WilC4
