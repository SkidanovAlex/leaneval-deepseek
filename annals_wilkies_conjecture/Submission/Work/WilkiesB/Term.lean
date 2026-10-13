import Submission.Work.WilkiesB.Defs

/-!
# Area B (syntax) — flattening nested exponential terms

For a term `t` of the language `expRing = ring ⊕ exp` with free variables in `A ⊕ ι` (the `A`-part
is treated as a fixed real parameter `c : A → ℝ`, the `ι`-part is the ambient variable) we build:

* `numExp t` — the number of `exp`-symbols in `t`;
* `valPoly c M t k h` — a polynomial in the context `ι ⊕ Fin M` whose value, when the
  slots `k, …, k + numExp t - 1` of the witness vector hold the *arguments* of the `exp`-nodes of
  `t`, equals `t.realize (Sum.elim c u)`;
* `csq c M t k h` — the sum of squares of the defining equations of those slots;
* `nodeVals c u t` — the canonical values of those slots as functions of `u`.

Slot `j` of the witness vector holds the real number whose exponential is the value of the `j`-th
`exp`-node; the polynomial may use `X (Sum.inr (Sum.inr j))` for the exponential of that slot.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open FirstOrder FirstOrder.Language
open MvPolynomial

namespace Work.WilkiesB

variable {A ι : Type*}

/-! ## Number of exponential nodes -/

/-- The number of `exp` symbols occurring in a term. -/
def numExp : Lexp.Term (A ⊕ ι) → ℕ
  | .var _ => 0
  | .func f ts => match f with
    | Sum.inl .add => numExp (ts 0) + numExp (ts 1)
    | Sum.inl .mul => numExp (ts 0) + numExp (ts 1)
    | Sum.inl .neg => numExp (ts 0)
    | Sum.inl .zero => 0
    | Sum.inl .one => 0
    | Sum.inr .exp => numExp (ts 0) + 1

@[simp] theorem numExp_func_add (ts : Fin 2 → Lexp.Term (A ⊕ ι)) :
    numExp (Term.func (Sum.inl ringFunc.add) ts) = numExp (ts 0) + numExp (ts 1) := rfl

@[simp] theorem numExp_func_mul (ts : Fin 2 → Lexp.Term (A ⊕ ι)) :
    numExp (Term.func (Sum.inl ringFunc.mul) ts) = numExp (ts 0) + numExp (ts 1) := rfl

@[simp] theorem numExp_func_neg (ts : Fin 1 → Lexp.Term (A ⊕ ι)) :
    numExp (Term.func (Sum.inl ringFunc.neg) ts) = numExp (ts 0) := rfl

@[simp] theorem numExp_func_zero (ts : Fin 0 → Lexp.Term (A ⊕ ι)) :
    numExp (Term.func (Sum.inl ringFunc.zero) ts) = 0 := rfl

@[simp] theorem numExp_func_one (ts : Fin 0 → Lexp.Term (A ⊕ ι)) :
    numExp (Term.func (Sum.inl ringFunc.one) ts) = 0 := rfl

@[simp] theorem numExp_func_exp (ts : Fin 1 → Lexp.Term (A ⊕ ι)) :
    numExp (Term.func (Sum.inr WilkiesConjecture.expFunc.exp) ts) = numExp (ts 0) + 1 := rfl

/-- The `Fin M` index `k + j` of a slot of the witness vector. -/
def shiftFin {M k m : ℕ} (h : k + m ≤ M) (j : Fin m) : Fin M := ⟨k + j.val, by omega⟩

@[simp] theorem shiftFin_val {M k m : ℕ} (h : k + m ≤ M) (j : Fin m) :
    (shiftFin h j).val = k + j.val := rfl

/-- `Fin.snoc` for constant families. -/
def snocReal {n : ℕ} (f : Fin n → ℝ) (a : ℝ) : Fin (n + 1) → ℝ := Fin.snoc f a

@[simp] theorem snocReal_castSucc {n : ℕ} (f : Fin n → ℝ) (a : ℝ) (j : Fin n) :
    snocReal f a j.castSucc = f j :=
  Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => ℝ) a f j

@[simp] theorem snocReal_last {n : ℕ} (f : Fin n → ℝ) (a : ℝ) :
    snocReal f a (Fin.last n) = a :=
  Fin.snoc_last (α := fun _ : Fin (n + 1) => ℝ) a f

/-! ## The value polynomial and the constraints -/

/-- In the context `ι ⊕ Fin M`, `valPoly c M t k h` evaluates (provided the slots
`k, …, k + numExp t - 1` carry the arguments of the `exp`-nodes of `t`) to the value of `t`. -/
def valPoly (c : A → ℝ) (M : ℕ) : (t : Lexp.Term (A ⊕ ι)) → (k : ℕ) → k + numExp t ≤ M →
    MvPolynomial ((ι ⊕ Fin M) ⊕ (ι ⊕ Fin M)) ℝ
  | .var v, _, _ => match v with
    | Sum.inl a => MvPolynomial.C (c a)
    | Sum.inr i => MvPolynomial.X (Sum.inl (Sum.inl i))
  | .func f ts, k, h => match f with
    | Sum.inl .add =>
        valPoly c M (ts 0) k (by simp only [numExp_func_add] at h; omega) +
        valPoly c M (ts 1) (k + numExp (ts 0))
          (by simp only [numExp_func_add] at h; omega)
    | Sum.inl .mul =>
        valPoly c M (ts 0) k (by simp only [numExp_func_mul] at h; omega) *
        valPoly c M (ts 1) (k + numExp (ts 0))
          (by simp only [numExp_func_mul] at h; omega)
    | Sum.inl .neg => -valPoly c M (ts 0) k (by simp only [numExp_func_neg] at h; omega)
    | Sum.inl .zero => 0
    | Sum.inl .one => 1
    | Sum.inr .exp =>
        MvPolynomial.X (Sum.inr (Sum.inr (⟨k + numExp (ts 0),
          by simp only [numExp_func_exp] at h; omega⟩ : Fin M)))

/-- The sum of squares of the equations defining the slots `k, …, k + numExp t - 1` holding the
arguments of the `exp`-nodes of `t`. -/
def csq (c : A → ℝ) (M : ℕ) : (t : Lexp.Term (A ⊕ ι)) → (k : ℕ) → k + numExp t ≤ M →
    MvPolynomial ((ι ⊕ Fin M) ⊕ (ι ⊕ Fin M)) ℝ
  | .var _, _, _ => 0
  | .func f ts, k, h => match f with
    | Sum.inl .add =>
        csq c M (ts 0) k (by simp only [numExp_func_add] at h; omega) +
        csq c M (ts 1) (k + numExp (ts 0))
          (by simp only [numExp_func_add] at h; omega)
    | Sum.inl .mul =>
        csq c M (ts 0) k (by simp only [numExp_func_mul] at h; omega) +
        csq c M (ts 1) (k + numExp (ts 0))
          (by simp only [numExp_func_mul] at h; omega)
    | Sum.inl .neg => csq c M (ts 0) k (by simp only [numExp_func_neg] at h; omega)
    | Sum.inl .zero => 0
    | Sum.inl .one => 0
    | Sum.inr .exp =>
        csq c M (ts 0) k (by simp only [numExp_func_exp] at h; omega) +
        (MvPolynomial.X (Sum.inl (Sum.inr (⟨k + numExp (ts 0),
            by simp only [numExp_func_exp] at h; omega⟩ : Fin M))) -
          valPoly c M (ts 0) k (by simp only [numExp_func_exp] at h; omega)) ^ 2

/-! ## The canonical values of the slots -/

/-- `nodeVals c u t j` is the real number whose exponential is the value of the `j`-th `exp`-node
of `t` under the assignment `Sum.elim c u`. -/
def nodeVals (c : A → ℝ) (u : ι → ℝ) : (t : Lexp.Term (A ⊕ ι)) → Fin (numExp t) → ℝ
  | .var _, j => Fin.elim0 j
  | .func f ts, j => match f, j with
    | Sum.inl .add, j => Fin.append (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j
    | Sum.inl .mul, j => Fin.append (nodeVals c u (ts 0)) (nodeVals c u (ts 1)) j
    | Sum.inl .neg, j => nodeVals c u (ts 0) j
    | Sum.inl .zero, j => Fin.elim0 j
    | Sum.inl .one, j => Fin.elim0 j
    | Sum.inr .exp, j =>
        snocReal (nodeVals c u (ts 0)) ((ts 0).realize (Sum.elim c u)) j

end Work.WilkiesB
