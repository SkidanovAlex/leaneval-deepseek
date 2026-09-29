import Mathlib
import Submission.Work.KronP.defs

/-!
# KronP: the integer coefficient vocabulary of the Kronecker word

Additional definitions used by the mathematical content of paper Lemma 2.5
(`Work.KronP.kronFinal`).  `dsumL l₁ l₂ r m` is the coefficient of `y^m` of the product of the
two length-`r` polynomials `l₁`, `l₂`; `negaCoefL` is the coefficient of the product in
`ℤ[y]/(y^r+1)`; `D0c`, `D1c` are (twice over) the real and imaginary parts of `4^p·(u·v)`.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-- Coefficient of `y^m` of the product of `l₁` and `l₂`, read as polynomials of length `r`
double sum over `{(i,j) : i,j < r, i+j = m}`). -/
def dsumL (l₁ l₂ : List ℤ) (r m : ℕ) : ℤ :=
  ((Finset.range r).sum fun i => (Finset.range r).sum fun j =>
    if i + j = m then l₁.getD i 0 * l₂.getD j 0 else 0)

/-- Coefficient of `y^k` of the product of `l₁`, `l₂` in `ℤ[y]/(y^r+1)`. -/
def negaCoefL (l₁ l₂ : List ℤ) (r k : ℕ) : ℤ :=
  dsumL l₁ l₂ r k - dsumL l₁ l₂ r (k + r)

/-- The real part of `4^p·(u·v)` (negacyclic), as an integer. -/
def D0c (u v : List (ℤ × ℤ)) (r k : ℕ) : ℤ :=
  negaCoefL (u.map Prod.fst) (v.map Prod.fst) r k -
    negaCoefL (u.map Prod.snd) (v.map Prod.snd) r k

/-- The imaginary part of `4^p·(u·v)` (negacyclic), as an integer. -/
def D1c (u v : List (ℤ × ℤ)) (r k : ℕ) : ℤ :=
  negaCoefL (u.map Prod.fst) (v.map Prod.snd) r k +
    negaCoefL (u.map Prod.snd) (v.map Prod.fst) r k

end Work.KronP
