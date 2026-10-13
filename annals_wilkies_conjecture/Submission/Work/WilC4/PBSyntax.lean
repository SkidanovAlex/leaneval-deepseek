/-
  WilC4/transferOfPB : the transfer of the polynomial-boundedness input `PolyBoundedRExp`
  from `ℝ` to every model of `TR`.

  The mathematical content is that `PolyBoundedRExp` is a *first-order schema*: for each
  `LRc`-formula `φ` describing a family of graphs `x ↦ y` (parameters `c`), the asymptotics hold
  with one finite set of exponents for the whole family.  That statement is not a single
  sentence, because `Qs` is a *finite set of rationals*; but for a fixed family the exponents are
  finitely many *rational numbers*, hence constants of the language `LRc` (which has a name for
  every real), and the corresponding statement *is* a sentence.  Completeness of
  `TR = LRc.completeTheory ℝ` then transfers it.

  The sentence `pbSent` built below is, for a formula `φ : LRc.Formula (Fin n ⊕ Fin (k+2))`
  (the `Fin n` block being the constants of the definable set, the `Fin (k+2)` block the
  coordinates `x, y, c` of the family) and a finite list `qs : Fin N → ℚ` of exponents:

      ∀ a c, (∀ x y y', φ(x,y) → φ(x,y') → y = y') →
        ∃ i : Fin N, ∃ α,
             (α = 0 ∧ ∀ ε > 0 ∃ R > 0 ∀ x y, R ≤ x → φ(x,y) → y = 0)
          ∨  (α ≠ 0 ∧ ∀ ε > 0 ∃ R > 0 ∀ x y, R ≤ x → φ(x,y) →
                ∃ t w, t^{den} x^{m} = x^{p} ∧ w*w = t ∧ |y - α t| ≤ ε t)

  where `p, den, m` are the numerator/denominator of `qs i` (so that `t = x^{q_i}`).  The
  comparisons `0 ≤ u` and `u ≤ v` are expressed *inside the language of rings*, as "`u` is a
  square" and "`v - u` is a square" (`posAtom`, `leF`); in a model of `TR` this definable order
  agrees with the order of the field, which is what makes the sentence mean the same thing in
  `ℝ` and in every model of `TR`.
-/
import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.Square
import Submission.Work.WilC2.definable_fin_params

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize leF leF_realize leF_realize_le ringToLRc)

/-! ## 1. Atomic ring formulas, and their realisation -/

/-- `t ^ n` as a term of the language of rings. -/
def tpow {α : Type*} (t : ring.Term α) : ℕ → ring.Term α
  | 0 => 1
  | (n + 1) => tpow t n * t

/-- The atom `x = y`. -/
def eqAtom : ring.Formula (Fin 2) := Term.equal (Term.var 0) (Term.var 1)

/-- The atom `x = 0`. -/
def zeroAtom : ring.Formula (Fin 1) := Term.equal (Term.var 0) (0 : ring.Term (Fin 1))

/-- The atom `x ≠ 0`. -/
def neZeroAtom : ring.Formula (Fin 1) := (zeroAtom).not

/-- The atom `∃ w, w * w = x`, i.e. `0 ≤ x` in a model of `TR`. -/
def posAtom : ring.Formula (Fin 1) :=
  (Term.bdEqual (Term.var (Sum.inr 0 : Fin 1 ⊕ Fin 1) * Term.var (Sum.inr 0 : Fin 1 ⊕ Fin 1))
    (Term.var (Sum.inl 0))).ex

/-- The atom `0 < x`. -/
def posStrictAtom : ring.Formula (Fin 1) := posAtom ⊓ neZeroAtom

/-- The atom `w * w = x`. -/
def sqAtom : ring.Formula (Fin 2) := Term.equal (Term.var 1 * Term.var 1) (Term.var 0)

/-- The atom `t ^ n * x ^ m = x ^ p`. -/
def rpowAtom (n m p : ℕ) : ring.Formula (Fin 2) :=
  Term.equal (tpow (Term.var 1) n * tpow (Term.var 0) m) (tpow (Term.var 0) p)

/-- The atom `|y - a * t| ≤ e * t`, expanded as the two square inequalities. -/
def absLeAtom : ring.Formula (Fin 4) :=
  (Term.bdEqual (Term.var (Sum.inr 0) * Term.var (Sum.inr 0))
    ((Term.var (Sum.inl 3) * Term.var (Sum.inl 2)) +
      -(Term.var (Sum.inl 0) + -(Term.var (Sum.inl 1) * Term.var (Sum.inl 2))))).ex ⊓
  (Term.bdEqual (Term.var (Sum.inr 0) * Term.var (Sum.inr 0))
    ((Term.var (Sum.inl 3) * Term.var (Sum.inl 2)) +
      -(-(Term.var (Sum.inl 0) + -(Term.var (Sum.inl 1) * Term.var (Sum.inl 2)))))).ex

theorem tpow_realize {R : Type*} [Monoid R] [Add R] [Neg R] [Zero R] [Ring.CompatibleRing R]
    {α : Type*} (v : α → R) (t : ring.Term α) (n : ℕ) :
    Term.realize v (tpow t n) = (Term.realize v t) ^ n := by
  induction n with
  | zero => simp [tpow]
  | succ n ih => simp [tpow, ih, pow_succ]

theorem le_of_posAtom {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {u : R}
    (h : ∃ z : R, z * z = u) : 0 ≤ u := by
  obtain ⟨z, hz⟩ := h
  rw [← hz]
  exact mul_self_nonneg z

theorem exists_sq_iff_nonneg {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hsq : ∀ x : R, 0 ≤ x → ∃ z : R, x = z * z) (u : R) :
    (∃ z : R, z * z = u) ↔ 0 ≤ u :=
  ⟨le_of_posAtom, fun h => (hsq u h).imp fun _ hz => hz.symm⟩

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
  [rexpL.Structure M] [(constantsOn ℝ).Structure M]

theorem eqAtom_lift {Ctx : Type} (f : Fin 2 → Ctx) (rw : Ctx → M) :
    (liftR f eqAtom).Realize rw ↔ rw (f 0) = rw (f 1) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1)] := by funext i; fin_cases i <;> rfl
  rw [h]
  simp [eqAtom]

theorem zeroAtom_lift {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M) :
    (liftR f zeroAtom).Realize rw ↔ rw (f 0) = 0 := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0)] := by funext i; fin_cases i <;> rfl
  rw [h]
  simp [zeroAtom]

theorem neZeroAtom_lift {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M) :
    (liftR f neZeroAtom).Realize rw ↔ rw (f 0) ≠ 0 := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0)] := by funext i; fin_cases i <;> rfl
  rw [h]
  simp [neZeroAtom, zeroAtom]

theorem posAtom_lift {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M) :
    (liftR f posAtom).Realize rw ↔ ∃ z : M, z * z = rw (f 0) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0)] := by funext i; fin_cases i <;> rfl
  rw [h]
  rw [posAtom, Formula.Realize, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_mul, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_fin_one]

theorem posStrictAtom_lift {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR f posStrictAtom).Realize rw ↔ 0 < rw (f 0) := by
  rw [show liftR f posStrictAtom = (liftR f posAtom) ⊓ (liftR f neZeroAtom) from rfl,
    Formula.realize_inf, posAtom_lift, neZeroAtom_lift, exists_sq_iff_nonneg hsq]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2.symm, fun h => ⟨h.le, ne_of_gt h⟩⟩

theorem leF_lift {Ctx : Type} (f : Fin 2 → Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR f leF).Realize rw ↔ rw (f 0) ≤ rw (f 1) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1)] := by funext i; fin_cases i <;> rfl
  rw [h]
  exact leF_realize_le hsq _ _

theorem sqAtom_lift {Ctx : Type} (f : Fin 2 → Ctx) (rw : Ctx → M) :
    (liftR f sqAtom).Realize rw ↔ rw (f 1) * rw (f 1) = rw (f 0) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1)] := by funext i; fin_cases i <;> rfl
  rw [h]
  simp [sqAtom]

theorem rpowAtom_lift (n m p : ℕ) {Ctx : Type} (f : Fin 2 → Ctx) (rw : Ctx → M) :
    (liftR f (rpowAtom n m p)).Realize rw ↔
      rw (f 1) ^ n * rw (f 0) ^ m = rw (f 0) ^ p := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1)] := by funext i; fin_cases i <;> rfl
  rw [h]
  simp only [rpowAtom, Formula.realize_equal, tpow_realize, Term.realize_var, Ring.realize_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem absLeAtom_lift {Ctx : Type} (f : Fin 4 → Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR f absLeAtom).Realize rw ↔
      |rw (f 0) - rw (f 1) * rw (f 2)| ≤ rw (f 3) * rw (f 2) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1), rw (f 2), rw (f 3)] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  rw [absLeAtom, Formula.Realize, BoundedFormula.realize_inf, BoundedFormula.realize_ex,
    BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_mul, Ring.realize_add,
    Ring.realize_neg, Term.realize_var, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  constructor
  · rintro ⟨h1, h2⟩
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have := le_of_posAtom h2; linarith
    · have := le_of_posAtom h1; linarith
  · intro h
    rw [abs_le] at h
    obtain ⟨h2', h1'⟩ := h
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz⟩ := hsq _ (by linarith :
        0 ≤ rw (f 3) * rw (f 2) - (rw (f 0) - rw (f 1) * rw (f 2)))
      exact ⟨z, by linarith [hz]⟩
    · obtain ⟨z, hz⟩ := hsq _ (by linarith :
        0 ≤ rw (f 3) * rw (f 2) + (rw (f 0) - rw (f 1) * rw (f 2)))
      exact ⟨z, by linarith [hz]⟩

/-! ## 2. The variable blocks of the sentence -/

/-- The context of the outer body: the constants `a : Fin n` and the family parameters
`c : Fin k`. -/
abbrev Gam (n k : ℕ) : Type := (Empty ⊕ Fin n) ⊕ Fin k

/-- The context of the graph condition: `Gam` together with the three variables `x, y, y'`. -/
abbrev GamG (n k : ℕ) : Type := Gam n k ⊕ Fin 3

/-- The context of the body of the consequent: `Gam` together with the quantifier blocks
`α, ε, R, (x,y), t, w` (in that order). -/
abbrev Con (n k : ℕ) : Type := ((((((Gam n k ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 2) ⊕ Fin 1) ⊕ Fin 1)

/-! ### 2.1 The variables of each context -/

def gA {n k : ℕ} (i : Fin n) : Gam n k := Sum.inl (Sum.inr i)
def gC {n k : ℕ} (j : Fin k) : Gam n k := Sum.inr j
def gG {n k : ℕ} (x : Gam n k) : GamG n k := Sum.inl x
def gX {n k : ℕ} : GamG n k := Sum.inr 0
def gY {n k : ℕ} : GamG n k := Sum.inr 1
def gY' {n k : ℕ} : GamG n k := Sum.inr 2

def cG {n k : ℕ} (x : Gam n k) : Con n k :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl x)))))
def cAl {n k : ℕ} : Con n k := Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))
def cEp {n k : ℕ} : Con n k := Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))
def cR {n k : ℕ} : Con n k := Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))
def cX {n k : ℕ} : Con n k := Sum.inl (Sum.inl (Sum.inr 0))
def cY {n k : ℕ} : Con n k := Sum.inl (Sum.inl (Sum.inr 1))
def cT {n k : ℕ} : Con n k := Sum.inl (Sum.inr 0)
def cW {n k : ℕ} : Con n k := Sum.inr 0

/-! ### 2.2 The formulas -/

/-- `φ` with its variables renamed: the `Fin n` block through `e`, and the coordinate block
`(x, y, c)` as `(xt, yt, e ∘ gC)`. -/
def phiG (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) {Ctx : Type}
    (e : Gam n k → Ctx) (xt yt : Ctx) : LRc.Formula Ctx :=
  Formula.relabel (Sum.elim (fun i => e (gA i)) (Fin.cases xt (Fin.cases yt (fun j => e (gC j))))) φ

/-- The body of the graph condition: `φ(x,y) → φ(x,y') → y = y'`. -/
def GC (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) : LRc.Formula (GamG n k) :=
  phiG n k φ gG gX gY ⟹ (phiG n k φ gG gX gY' ⟹ (liftR ![gY, gY'] eqAtom))

/-- The graph condition: the fibre is the graph of a function of `x`. -/
def graphAll (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) : LRc.Formula (Gam n k) :=
  Formula.iAlls (Fin 3) (GC n k φ)

/-- `0 < u` at the variable `u`. -/
def posStrictL {Ctx : Type} (u : Ctx) : LRc.Formula Ctx := liftR ![u] posStrictAtom

/-- The "eventually zero" branch: `α = 0` and `y = 0` for large `x`. -/
def b1 (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) : LRc.Formula (Con n k) :=
  (liftR ![cAl] zeroAtom) ⊓
    (posStrictL cEp ⟹ (posStrictL cR ⊓
      (liftR ![cR, cX] leF ⟹ (phiG n k φ cG cX cY ⟹ (liftR ![cY] zeroAtom)))))

/-- The asymptotic branch with exponent `q`: `α ≠ 0`, `t^den * x^m = x^p`, `w*w = t` and
`|y - α t| ≤ ε t`. -/
def b2 (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (q : ℚ) : LRc.Formula (Con n k) :=
  (liftR ![cAl] neZeroAtom) ⊓
    (posStrictL cEp ⟹ (posStrictL cR ⊓
      (liftR ![cR, cX] leF ⟹ (phiG n k φ cG cX cY ⟹
        ((liftR ![cX, cT] (rpowAtom q.den ((-q.num).toNat) q.num.toNat)) ⊓
          ((liftR ![cT, cW] sqAtom) ⊓
            (liftR ![cY, cAl, cT, cEp] absLeAtom)))))))

/-- The body of one disjunct of the consequent. -/
def BODYQ (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (q : ℚ) : LRc.Formula (Con n k) :=
  b1 n k φ ⊔ b2 n k φ q

/-- The consequent for the exponent `q`: `∃ α, ∀ ε, ∃ R, ∀ (x,y), ∃ t, ∃ w, BODYQ`. -/
def ConclOf (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (q : ℚ) : LRc.Formula (Gam n k) :=
  Formula.iExs (Fin 1) (Formula.iAlls (Fin 1) (Formula.iExs (Fin 1) (Formula.iAlls (Fin 2)
    (Formula.iExs (Fin 1) (Formula.iExs (Fin 1) (BODYQ n k φ q))))))

/-- The body of the sentence: `graphAll → ⋁_i ConclOf (qs i)`. -/
def BODY (n k N : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (qs : Fin N → ℚ) :
    LRc.Formula (Gam n k) :=
  graphAll n k φ ⟹ (Formula.iSup (fun i : Fin N => ConclOf n k φ (qs i)))

/-- **The transfer sentence** for the formula `φ` and the list `qs` of exponents. -/
def pbSent (n k N : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (qs : Fin N → ℚ) :
    LRc.Sentence := Formula.iAlls (Fin n) (Formula.iAlls (Fin k) (BODY n k N φ qs))

/-! ## 3. The clean semantics -/

/-- `φ(x, y)` with the constants `aa` and the family parameters `cc`. -/
def phiVal (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) {M : Type} [LRc.Structure M]
    (aa : Fin n → M) (cc : Fin k → M) (x y : M) : Prop :=
  φ.Realize (Sum.elim aa (Fin.cases x (Fin.cases y cc)))

/-- **The clean form of the sentence.**  For every choice of constants and family parameters
satisfying the graph condition, there is an exponent `qs i` and a coefficient `α` such that
either the family is eventually `0`, or it is asymptotic to `α x^{q_i}`. -/
def PBGood (n k N : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (qs : Fin N → ℚ) (M : Type)
    [LRc.Structure M] [Field M] [LinearOrder M] : Prop :=
  ∀ (aa : Fin n → M) (cc : Fin k → M),
    (∀ x y y' : M, phiVal n k φ aa cc x y → phiVal n k φ aa cc x y' → y = y') →
    ∃ (i : Fin N) (α : M),
      (α = 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
          phiVal n k φ aa cc x y → y = 0))
      ∨ (α ≠ 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
          phiVal n k φ aa cc x y →
          ∃ t : M, ∃ w : M, t ^ (qs i).den * x ^ ((-(qs i).num).toNat) = x ^ (qs i).num.toNat ∧
            (w * w = t ∧ |y - α * t| ≤ ε * t)))

end Work.WilC4
