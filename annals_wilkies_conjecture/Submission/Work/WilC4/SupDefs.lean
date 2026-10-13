import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC2.definable_fin_params
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC4

open FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (ParamFormula leF liftR liftR_realize leF_realize leF_realize_le)

/-! ## The variable layout of the two sentences

`SVar n` collects all variables of the two formulas below:
* the first block (inside the leading `Empty`) is the parameter tuple `Fin n`;
* the second block `Fin 1` is the point `z` whose being-the-sup we test;
* the third block `Fin 2` is the pair `(x,u)` (respectively `(x,w)`);
* the fourth block `Fin 1` is `x₂` (respectively `x₄`).
The quantifier blocks are stripped from the right by `Formula.iExs`/`Formula.iAlls`. -/
abbrev SVar (n : ℕ) := (((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 2) ⊕ Fin 1

namespace SVar

/-- The `i`-th parameter. -/
def param {n : ℕ} (i : Fin n) : SVar n := Sum.inl (Sum.inl (Sum.inl (Sum.inr i)))

/-- The `z`-variable. -/
def zVar {n : ℕ} : SVar n := Sum.inl (Sum.inl (Sum.inr 0))

/-- The pair `(x,u)` (or `(x,w)`) variables. -/
def qu {n : ℕ} (j : Fin 2) : SVar n := Sum.inl (Sum.inr j)

/-- The extra point variable `x₂` (or `x₄`). -/
def wV {n : ℕ} : SVar n := Sum.inr 0

end SVar

/-- The assignment produced by the four quantifier blocks. -/
def rawV {M : Type*} {n : ℕ} (d : Empty → M) (p : Fin n → M) (z : Fin 1 → M)
    (q : Fin 2 → M) (t : Fin 1 → M) : SVar n → M :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim d p) z) q) t

@[simp] lemma rawV_param {M : Type*} {n : ℕ} (d : Empty → M) (p : Fin n → M) (z : Fin 1 → M)
    (q : Fin 2 → M) (t : Fin 1 → M) (i : Fin n) :
    rawV d p z q t (SVar.param i) = p i := rfl

@[simp] lemma rawV_zVar {M : Type*} {n : ℕ} (d : Empty → M) (p : Fin n → M) (z : Fin 1 → M)
    (q : Fin 2 → M) (t : Fin 1 → M) : rawV d p z q t (SVar.zVar) = z 0 := rfl

@[simp] lemma rawV_qu {M : Type*} {n : ℕ} (d : Empty → M) (p : Fin n → M) (z : Fin 1 → M)
    (q : Fin 2 → M) (t : Fin 1 → M) (j : Fin 2) : rawV d p z q t (SVar.qu j) = q j := rfl

@[simp] lemma rawV_wV {M : Type*} {n : ℕ} (d : Empty → M) (p : Fin n → M) (z : Fin 1 → M)
    (q : Fin 2 → M) (t : Fin 1 → M) : rawV d p z q t (SVar.wV) = t 0 := rfl

/-- `φ` with its point variable renamed to `t`. -/
def phiVar {n : ℕ} (φ : ParamFormula n) (t : SVar n) : LRc.Formula (SVar n) :=
  φ.relabel (Sum.elim (fun i => SVar.param i) (fun _ => t))

/-- The relation `a ≤ b`, as an `LRc`-formula over `SVar n`. -/
def leVar {n : ℕ} (a b : SVar n) : LRc.Formula (SVar n) := liftR ![a, b] leF

/-- The body of the "nonempty and bounded above" formula. -/
def bodyP {n : ℕ} (φ : ParamFormula n) : LRc.Formula (SVar n) :=
  phiVar φ (SVar.qu 0) ⊓ (phiVar φ SVar.wV ⟹ leVar SVar.wV (SVar.qu 1))

/-- The body of the "`z` is the least upper bound" formula. -/
def bodyC {n : ℕ} (φ : ParamFormula n) : LRc.Formula (SVar n) :=
  (phiVar φ (SVar.qu 0) ⟹ leVar (SVar.qu 0) SVar.zVar) ⊓
    ((phiVar φ SVar.wV ⟹ leVar SVar.wV (SVar.qu 1)) ⟹ leVar SVar.zVar (SVar.qu 1))

/-- `premiseF φ` says (in the parameters) that the fibre of `φ` is nonempty and bounded above. -/
def premiseF {n : ℕ} (φ : ParamFormula n) : LRc.Formula ((Empty ⊕ Fin n) ⊕ Fin 1) :=
  Formula.iExs (Fin 2) (Formula.iAlls (Fin 1) (bodyP φ))

/-- `supF φ` says (in the parameters and `z`) that `z` is the least upper bound of the fibre. -/
def supF {n : ℕ} (φ : ParamFormula n) : LRc.Formula ((Empty ⊕ Fin n) ⊕ Fin 1) :=
  Formula.iAlls (Fin 2) (Formula.iExs (Fin 1) (bodyC φ))

/-- **The sup-existence sentence.** Every nonempty bounded-above fibre of `φ` has a supremum. -/
def supSent {n : ℕ} (φ : ParamFormula n) : LRc.Sentence :=
  Formula.iAlls (Fin n) (Formula.iExs (Fin 1) (premiseF φ ⟹ supF φ))

end Work.WilC4
