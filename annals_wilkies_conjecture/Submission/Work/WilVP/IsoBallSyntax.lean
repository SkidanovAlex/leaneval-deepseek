/-
  WilVP/IsoBallSyntax : the first-order content of the uniform-iso-ball statement
  `Work.WilVP.IsoBallProp` (`WilVP/Defs.lean`), for a fixed parameter-free `LRc`-formula `φ`
  (the family `Y`) and a fixed parameter-free `LRc`-formula `ψ` (the set `P` of bound points).

  The mathematical content of `IsoBallProp M` is: for every `∅`-definable family of graphs `Y`
  (parameters `c`) whose fibres are bounded there are `N > 0` and an `∅`-definable `P` such that

  * every `P`-fibre has at most `N` points, and
  * for `φ(x, y₀, c)` with `y₀ ≠ 0` and `N|y − x| < |x − p|` for every `p ∈ P`, the value
    `y₁` of the `c`-fibre at `y` exists and `|y₁| ≤ N|y₀|`, `|y₀| ≤ N|y₁|`.

  To *transfer* this from `ℝ` to every model of `TR` we must exhibit, for a fixed parameter-free
  formula `φ` defining the family and a fixed parameter-free formula `ψ` defining `P`, and for a
  fixed meta-data `N : ℕ`, a single `LRc`-**sentence** `isoSent k N φ ψ` asserting the
  conclusion.  This file builds that sentence; the semantic characterisation
  `isoSent_realize : (M ⊨ isoSent k N φ ψ) ↔ IsoBallGood k N φ ψ M` (with `IsoBallGood` the
  clean semantic content, `IsoBallProp` with `Y` and `P` replaced by *formulas*) is proved in
  `WilVP/isoSentRealize.lean`.  The sentence reads

      (∀ c x y y', φ(x,y,c) → φ(x,y',c) → y = y') →
      (∀ c, ∃ R, ∀ x y, φ(x,y,c) → x² ≤ R²) →
      ∀ c, (at most `N` many `p` with ψ(p,c))
           ∧ ∀ x y₀ y, φ(x,y₀,c) → y₀ ≠ 0 →
               (∀ p, ψ(p,c) → (N(y−x))² < (x−p)²) →
               ∃ y₁, φ(y,y₁,c) ∧ y₁² ≤ (N y₀)² ∧ y₀² ≤ (N y₁)²

  The order, the absolute values and the strict inequality are expressed *inside the language of
  rings*, so that the sentence means the same thing in `ℝ` and in every model of `TR`:
  "`u ≤ v`" is `∃ z, u + z*z = v` (`leTerm`), "`N|y − x| < |x − p|`" is "`(N(y−x))² < (x−p)²`"
  (squares are monotone on the nonnegative elements), "`|u| ≤ N|v|`" is "`u² ≤ (N v)²`" and
  "`|x| ≤ R`" is "`x² ≤ R²`" (`exists_sqBound_iff_absBound`).

  Design notes (mirroring `WilC4/ULPMSyntax.lean`):

  * the contexts are `UC0 k = Empty ⊕ Fin k` (the parameters `c`), `UCI k = UC0 k ⊕ Fin 3`
    (`x, y₀, y`), `UCIP k = UCI k ⊕ Fin 1` (the bound point `p`), `UCIY k = UCI k ⊕ Fin 1`
    (the witness `y₁`), and `UCBR k = UC0 k ⊕ Fin 1`, `UCBXY k = UCBR k ⊕ Fin 2` for the
    bounded-fibre hypothesis (the bound `R` and `x, y`);
  * `ucard k N ψ` and `uGraphAll k φ` are reused verbatim from `WilC4`;
  * the constant `N` of the statement is a *numeral* (`nTerm N`), and the sentence is quantified
    over `φ, ψ` only.

  Proof plan for `isoSent_realize` (in `WilVP/isoSentRealize.lean`), one realisation lemma per
  layer of the syntax, exactly as in `WilC4/ULPMRealize.lean`:

  ```
  uBddB_realize      : (uBddB k φ).Realize rw ↔ (uphiVal ... → (rw ucbxyX)^2 ≤ (rw ucbxyR)^2)
  uBdd_all_realize   : (∀c uBdd) ↔ ∀ c, ∃ R, ∀ x y, uphiVal k φ M c x y → x*x ≤ R*R
  uBallB_realize     : (uBallB k N ψ).Realize rw ↔ (upsiVal ... → (N:M)*|rw ucipY - rw ucipX| <
                                                  |rw ucipX - rw ucipP|)
  uBall_realize      : (uBall k N ψ).Realize rw ↔ ∀ p, upsiVal k ψ M (c...) p → ... 
  uWitBody_realize   : (uWitBody k N φ).Realize rw ↔ (uphiVal k φ M c (rw uciyY) (rw uciyY1) ∧
                          |rw uciyY1| ≤ (N:M)*|rw uciyY0| ∧ |rw uciyY0| ≤ (N:M)*|rw uciyY1|)
  uIsoBody_realize   : the three-fold implication with `Formula.iExs (Fin 1)`
  uIsoAll_all_realize: (∀c (ucard ⊓ ∀(Fin 3) uIsoBody)) ↔ ∀ c, (encard ≤ N ∧ <iso clause>)
  isoSent_realize    : plus `uGraphAll_all_realize`, `ucard_realize_encard`,
                       `exists_sqBound_iff_absBound`, then `exact Iff.rfl`
  ```
-/
import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilC4.ULPMSyntax
import Submission.Work.WilC4.ULPMRealize

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilVP

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize)
open Work.WilC4

/-! ## 1. The ring atoms of the iso-ball statement

All three are written with `leTerm u v`, the ring formula `∃ z, u + z * z = v`, which realises as
`u ≤ v` in an ordered field in which every nonnegative element is a square (both `ℝ` and every
model of `TR`). -/

/-- The atom `u² ≤ (N · v)²` (variables `(u, v)`), i.e. `|u| ≤ N |v|`. -/
def isoAbsLeAtom (N : ℕ) : ring.Formula (Fin 2) :=
  leTerm (Term.var (0 : Fin 2) * Term.var 0)
    (((nTerm N : ring.Term (Fin 2)) * Term.var 1) *
      ((nTerm N : ring.Term (Fin 2)) * Term.var 1))

/-- Realisation of `isoAbsLeAtom`: `|u| ≤ (N : M) * |v|`. -/
theorem isoAbsLeAtom_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (N : ℕ)
    (v : Fin 2 → M) :
    (isoAbsLeAtom N).Realize v ↔ |v 0| ≤ (N : M) * |v 1| := by
  rw [isoAbsLeAtom, leTerm_realize hsq]
  simp only [Ring.realize_mul, nTerm_realize, Term.realize_var]
  rw [show v 0 * v 0 = v 0 ^ 2 by ring,
    show ((N : M) * v 1) * ((N : M) * v 1) = ((N : M) * v 1) ^ 2 by ring]
  have h1 : |(N : M) * v 1| = (N : M) * |v 1| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  rw [sq_le_sq, h1]

/-- The atom `(N (y − x))² < (x − p)²` (variables `(x, y, p)`), i.e. `N |y − x| < |x − p|`. -/
def isoBallLtAtom (N : ℕ) : ring.Formula (Fin 3) :=
  (leTerm ((Term.var (0 : Fin 3) + -Term.var 2) * (Term.var 0 + -Term.var 2))
    (((nTerm N : ring.Term (Fin 3)) * (Term.var (1 : Fin 3) + -Term.var 0)) *
      ((nTerm N : ring.Term (Fin 3)) * (Term.var 1 + -Term.var 0)))).not

/-- Realisation of `isoBallLtAtom`: `(N : M) * |y − x| < |x − p|`. -/
theorem isoBallLtAtom_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (N : ℕ)
    (v : Fin 3 → M) :
    (isoBallLtAtom N).Realize v ↔ (N : M) * |v 1 - v 0| < |v 0 - v 2| := by
  rw [isoBallLtAtom, Formula.realize_not, leTerm_realize hsq]
  simp only [Ring.realize_mul, Ring.realize_add, Ring.realize_neg, nTerm_realize, Term.realize_var]
  rw [not_le]
  have e1 : (v 0 + -v 2) * (v 0 + -v 2) = (v 0 - v 2) ^ 2 := by ring
  have e2 : ((N : M) * (v 1 + -v 0)) * ((N : M) * (v 1 + -v 0)) =
      ((N : M) * (v 1 - v 0)) ^ 2 := by ring
  rw [e1, e2, sq_lt_sq]
  have h1 : |(N : M) * (v 1 - v 0)| = (N : M) * |v 1 - v 0| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  rw [h1]

/-- The atom `x * x ≤ R * R` (variables `(x, R)`). -/
def sqLeAtom : ring.Formula (Fin 2) :=
  leTerm (Term.var (0 : Fin 2) * Term.var 0) (Term.var (1 : Fin 2) * Term.var 1)

/-- Realisation of `sqLeAtom` (no square-freeness hypothesis is needed: `leTerm` already has it
as its argument `hsq`). -/
theorem sqLeAtom_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (v : Fin 2 → M) :
    sqLeAtom.Realize v ↔ v 0 * v 0 ≤ v 1 * v 1 := by
  rw [sqLeAtom, leTerm_realize hsq]
  simp only [Ring.realize_mul, Term.realize_var]

/-- The bounded-fibre hypothesis is the same whether the bound is written `|x| ≤ R` or
`x * x ≤ R * R` (`R ↦ |R|` in both directions). -/
theorem exists_sqBound_iff_absBound {M : Type} [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] (P : M → M → Prop) :
    (∃ R : M, ∀ x y : M, P x y → x * x ≤ R * R) ↔
      (∃ R : M, ∀ x y : M, P x y → |x| ≤ R) := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨|R|, fun x y hxy => ?_⟩
    have h := hR x y hxy
    rw [← sq_le_sq]
    simpa [pow_two] using h
  · rintro ⟨R, hR⟩
    refine ⟨|R|, fun x y hxy => ?_⟩
    have h : |x| ≤ |R| := le_trans (hR x y hxy) (le_abs_self R)
    have h2 : x ^ 2 ≤ |R| ^ 2 :=
      (sq_le_sq).mpr (by simpa using le_trans h (le_abs_self |R|))
    simpa [pow_two] using h2

/-! ## 2. The clean semantic content -/

/-- **The clean semantic content of `isoSent`**: the statement of `IsoBallProp` with the family
`Y` and the bound set `P` replaced by the formulas `φ` and `ψ` defining them, the graph and
bounded-fibre hypotheses kept as an implication, and the constant `N` fixed. -/
def IsoBallGood (k N : ℕ) (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1)))
    (M : Type) [LRc.Structure M] [Field M] [LinearOrder M] : Prop :=
  (∀ (c : Fin k → M) (x y y' : M), uphiVal k φ M c x y → uphiVal k φ M c x y' → y = y') →
  (∀ c : Fin k → M, ∃ R : M, ∀ x y : M, uphiVal k φ M c x y → |x| ≤ R) →
  ∀ c : Fin k → M,
    {x : M | upsiVal k ψ M c x}.encard ≤ N ∧
      ∀ x y₀ y : M, uphiVal k φ M c x y₀ → y₀ ≠ 0 →
        (∀ p : M, upsiVal k ψ M c p → (N : M) * |y - x| < |x - p|) →
        ∃ y₁ : M, uphiVal k φ M c y y₁ ∧
          |y₁| ≤ (N : M) * |y₀| ∧ |y₀| ≤ (N : M) * |y₁|

/-! ## 3. The contexts of the sentence -/

/-- The context "the parameters and `(x, y₀, y)`". -/
abbrev UCI (k : ℕ) : Type := UC0 k ⊕ Fin 3
/-- The parameter variable in `UCI`. -/
def uciC {k : ℕ} (j : Fin k) : UCI k := Sum.inl (ucC j)
/-- The variable `x`. -/
def uciX {k : ℕ} : UCI k := Sum.inr 0
/-- The variable `y₀` (the value at `x`). -/
def uciY0 {k : ℕ} : UCI k := Sum.inr 1
/-- The variable `y` (the point at which the value is looked up). -/
def uciY {k : ℕ} : UCI k := Sum.inr 2

/-- The context of the ball clause: the previous variables and the bound point `p`. -/
abbrev UCIP (k : ℕ) : Type := UCI k ⊕ Fin 1
def ucipC {k : ℕ} (j : Fin k) : UCIP k := Sum.inl (uciC j)
def ucipX {k : ℕ} : UCIP k := Sum.inl uciX
def ucipY {k : ℕ} : UCIP k := Sum.inl uciY
def ucipP {k : ℕ} : UCIP k := Sum.inr 0

/-- The context of the witness clause: the previous variables and the witness `y₁`. -/
abbrev UCIY (k : ℕ) : Type := UCI k ⊕ Fin 1
def uciyC {k : ℕ} (j : Fin k) : UCIY k := Sum.inl (uciC j)
def uciyY0 {k : ℕ} : UCIY k := Sum.inl uciY0
def uciyY {k : ℕ} : UCIY k := Sum.inl uciY
def uciyY1 {k : ℕ} : UCIY k := Sum.inr 0

/-- The context of the bounded-fibre hypothesis, with the bound `R`. -/
abbrev UCBR (k : ℕ) : Type := UC0 k ⊕ Fin 1
def ucbrC {k : ℕ} (j : Fin k) : UCBR k := Sum.inl (ucC j)
def ucbrR {k : ℕ} : UCBR k := Sum.inr 0

/-- The context of the bounded-fibre hypothesis, with the bound `R` and the variables `x, y`. -/
abbrev UCBXY (k : ℕ) : Type := UCBR k ⊕ Fin 2
def ucbxyC {k : ℕ} (j : Fin k) : UCBXY k := Sum.inl (ucbrC j)
def ucbxyR {k : ℕ} : UCBXY k := Sum.inl ucbrR
def ucbxyX {k : ℕ} : UCBXY k := Sum.inr 0
def ucbxyY {k : ℕ} : UCBXY k := Sum.inr 1

/-! ## 4. The sentence -/

/-- The body of the bounded-fibre hypothesis at one value of the parameters:
`φ(x,y,c) → x² ≤ R²`. -/
def uBddB (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UCBXY k) :=
  (uphiG k φ ucbxyC ucbxyX ucbxyY) ⟹ (liftR ![ucbxyX, ucbxyR] sqLeAtom)

/-- The bounded-fibre hypothesis at one value of the parameters:
`∃ R, ∀ x y, φ(x,y,c) → x² ≤ R²`. -/
def uBdd (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UC0 k) :=
  Formula.iExs (Fin 1) (Formula.iAlls (Fin 2) (uBddB k φ))

/-- The ball hypothesis at one bound point `p`: `ψ(p,c) → N|y − x| < |x − p|`. -/
def uBallB (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) : LRc.Formula (UCIP k) :=
  (upsiG k ψ ucipC ucipP) ⟹ (liftR ![ucipX, ucipY, ucipP] (isoBallLtAtom N))

/-- The ball hypothesis: `N|y − x| < |x − p|` at every bound point `p` of the `ψ`-fibre. -/
def uBall (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) : LRc.Formula (UCI k) :=
  Formula.iAlls (Fin 1) (uBallB k N ψ)

/-- The conclusion for the witness `y₁`: `φ(y,y₁,c) ∧ y₁² ≤ (N y₀)² ∧ y₀² ≤ (N y₁)²`. -/
def uWitBody (k N : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UCIY k) :=
  (uphiG k φ uciyC uciyY uciyY1) ⊓
    ((liftR ![uciyY1, uciyY0] (isoAbsLeAtom N)) ⊓
      (liftR ![uciyY0, uciyY1] (isoAbsLeAtom N)))

/-- The iso clause at one value of the parameters: for `φ(x,y₀,c)` with `y₀ ≠ 0` and the ball
hypothesis, the value `y₁` at `y` exists with `|y₁| ≤ N|y₀| ≤ N²|y₁|`. -/
def uIsoBody (k N : ℕ) (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) :
    LRc.Formula (UCI k) :=
  (uphiG k φ uciC uciX uciY0) ⟹
    ((liftR ![uciY0] neZeroAtom) ⟹
      ((uBall k N ψ) ⟹ (Formula.iExs (Fin 1) (uWitBody k N φ))))

/-- The body of the iso-ball sentence at one value of the parameters: the cardinality clause
and the iso clause. -/
def uIsoAll (k N : ℕ) (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) :
    LRc.Formula (UC0 k) :=
  (ucard k N ψ) ⊓ (Formula.iAlls (Fin 3) (uIsoBody k N φ ψ))

/-- **The iso-ball sentence** for the formula `φ` (the family), the formula `ψ` (the bound
points) and the constant `N`. -/
def isoSent (k N : ℕ) (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) :
    LRc.Sentence :=
  (Formula.iAlls (Fin k) (uGraphAll k φ)) ⟹
    ((Formula.iAlls (Fin k) (uBdd k φ)) ⟹ (Formula.iAlls (Fin k) (uIsoAll k N φ ψ)))

end Work.WilVP
