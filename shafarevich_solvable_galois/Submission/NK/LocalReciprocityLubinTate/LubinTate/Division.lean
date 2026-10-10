import Mathlib.Algebra.Polynomial.Eval.Defs
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Division polynomials of the Lubin–Tate group: the polynomial iterate

For the *standard* Lubin–Tate series `f(X) = πX + X^q` (Milne, *CFT*, Example 2.10(a)) the iterates
`f^{(n)} = f ∘ f ∘ ⋯ ∘ f` are **polynomials**, and the classical theory of Milne, *CFT*, §I.3 uses
them directly:

`f^{(n)}(T) = π^n T + ⋯ + T^{q^n}`,

a monic polynomial of degree `q^n` whose roots in the algebraic closure are the `π^n`-division
points `Λ_n` of the Lubin–Tate group (`[π]` is the iterate `f`, so `f^{(n)}` is the multiplication
by `π^n`).  Milne's proof of the basic properties of the fields `K_{π,n} = K[Λ_n]` (totally
ramified of degree `(q-1)q^{n-1}`, Galois group `(𝒪/π^n)^×`, and the norm computation
`Nm(π_n) = ±π`) is a purely polynomial computation with this iterate; this file isolates the
polynomial layer.

## Main definitions

* `NK.LocalReciprocityLubinTate.LTpoly` — the standard Lubin–Tate polynomial `πX + X^q`;
* `NK.LocalReciprocityLubinTate.LTpolyIter` — its `n`-fold iterate `f^{(n)}`.

## Interface (to be proved)

* `LTpolyIter_eq` — `f^{(n)}(T) = π^n T + ⋯ + T^{q^n}` (the shape of the iteration);
* `LTpolyIter_monic`, `natDegree_LTpolyIter` — the iterate is monic of degree `q^n`.
-/

namespace NK.LocalReciprocityLubinTate

universe u

noncomputable section

variable {A : Type u} [CommRing A]

/-- The **standard Lubin–Tate polynomial** `f(X) = πX + X^q` over `A` (Milne, *CFT*, Example
2.10(a)). -/
def LTpoly (π : A) (q : ℕ) : Polynomial A := Polynomial.C π * Polynomial.X + Polynomial.X ^ q

/-- The `n`-fold iterate `f^{(n)}` of a polynomial `f`, defined by `f^{(0)} = X` and
`f^{(n+1)} = f^{(n)} ∘ f`.  For the standard Lubin–Tate polynomial this is the `π^n`-division
polynomial (Milne, *CFT*, Remark 3.1). -/
def polyIter (f : Polynomial A) : ℕ → Polynomial A
  | 0 => Polynomial.X
  | n + 1 => (polyIter f n).comp f

/-- The `π^n`-division polynomial of the standard Lubin–Tate polynomial `πX + X^q`. -/
def LTpolyIter (π : A) (q n : ℕ) : Polynomial A := polyIter (LTpoly π q) n

theorem polyIter_zero (f : Polynomial A) : polyIter f 0 = Polynomial.X := rfl

theorem polyIter_succ (f : Polynomial A) (n : ℕ) :
    polyIter f (n + 1) = (polyIter f n).comp f := rfl

theorem LTpolyIter_zero (π : A) (q : ℕ) : LTpolyIter π q 0 = Polynomial.X := rfl

theorem LTpolyIter_succ (π : A) (q n : ℕ) :
    LTpolyIter π q (n + 1) = (LTpolyIter π q n).comp (LTpoly π q) := rfl

/-- The **Eisenstein factor** `X^{q-1} + π` of the standard Lubin–Tate polynomial:
`πX + X^q = X · (X^{q-1} + π)`.  This is the polynomial which is Eisenstein at `π` and hence
irreducible over `K`; Milne, *CFT*, §I.3 writes it as `f^{[1]}(T) = f(T)/T`. -/
def LTpolyFactor (π : A) (q : ℕ) : Polynomial A := Polynomial.X ^ (q - 1) + Polynomial.C π

/-- The standard Lubin–Tate polynomial factors as `X · (X^{q-1} + π)`: the second factor is the
Eisenstein, hence irreducible, one (Milne, *CFT*, §I.3). -/
theorem LTpoly_succ_eq (π : A) (n : ℕ) :
    LTpoly π (n + 1) = Polynomial.X * LTpolyFactor π (n + 1) := by
  rw [LTpoly, LTpolyFactor, Nat.add_sub_cancel, pow_succ]
  ring

end

end NK.LocalReciprocityLubinTate
