import Mathlib
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The scalar part of the AS link identity I1^AS (component `0`)

`kleinPAS a b g y` and `kleinRAS a b g z` are the Artin-Schreier (characteristic `5`) coordinates of
the Pfaffian map `P^AS` and of the inverse quadro-cubic map `R^AS`
(`Submission/Work/MotAS/ASData.lean`).  The target statement is component `0` of the AS link
identity **I1^AS**

  `kleinRAS a b g (kleinPAS a b g y) = fun i => kleinSecAS a b g y * y i`

which holds exactly in characteristic `5` (over `ℤ` the difference is `5 · (…)`).

## Status of the statement

TRUE.  Machine-checked symbolically with sympy (`python3 -c` from the workspace root): expanding
`kleinRAS0 a b g (kleinPAS a b g y) - y 0 * kleinSecAS a b g y` gives a polynomial with 3140 terms
all of whose coefficients are divisible by `5`; equivalently the exact integer certificate
`Q := (that difference) / 5` is a polynomial with 3140 terms, and it has been rendered in Lean
syntax in the file `_as2scratch/certI1_0.txt` (154 KB: `a^2*g*y 1*y 4 + ...`, no `C`, over a
`CommRing R` with variables `a b g` and `y : Fin 5 → R`).

## The trap (read before trying the one-liner)

`linear_combination (_as2scratch/certI1_0.txt) * h5` **blows the 12 GB memory cap**, and so does
`ring`/`ring_nf` on the composite `kleinRAS0 a b g (kleinPAS a b g y)`: `kleinRAS0` has 114
monomials of degree `3` in `z` and each `kleinPASi` has 16–27 monomials of degree `2` in `y`, so
the direct expansion produces ≈ 114 · 27³ ≈ 2.2 · 10⁶ intermediate monomials.  This is exactly the
wall that stopped the earlier attempts at `asTransportS`.

## Suggested route (staged, no big `ring`)

Work in `R` with `h5 : (5 : R) = 0`.  Put `Pi := kleinPASi a b g y`.

1. For each triple `(i,j,k) ∈ Fin 5³` with `i ≤ j ≤ k` (35 triples) let `T_ijk` be the explicit
   polynomial (= `Pi * Pj * Pk` as a polynomial in `a b g y 0 … y 4`, degree `6` in `y`, a few
   hundred terms) — generate it with sympy from `ASData.lean`.
   Prove `kleinPASi a b g y * kleinPASj a b g y * kleinPASk a b g y = T_ijk` by `ring`
   (cheap: ≈ 27³ = 19683 monomial operations).
2. Expand `kleinRAS0 a b g ![kleinPAS0 …, …, kleinPAS4 …]` with
   `simp only [kleinRAS0, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
     Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
     Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]`
   (this is purely syntactic, no normalisation) and then rewrite the ≈ 114 triple products that
   occur with the lemmas of step 1 (`rw`, matching the left-nested parenthesisation
   `((Pi * Pj) * Pk)` used in `ASData.lean`), and collect with `ring` into the explicit normal
   form `NF` (≈ 1500 terms, a few hundred KB).
3. Finish the characteristic-`5` step: `NF = y 0 * kleinSecAS a b g y` follows from
   `linear_combination (Q) * h5` with `Q` the certificate above, or by an equivalent
   `ring`-verified decomposition.  At that point both sides are explicit polynomials, so this
   `ring` call is small.

(Alternative, if the staging above is unwieldy: a Kronecker substitution `y i ↦ t^(7^i)` makes
both sides univariate — distinct monomials of degree `6` get distinct exponents because the digits
are `≤ 6 < 7` — and `ring` on univariate polynomials is much lighter; the injectivity on the
degree-`6` part still has to be formalised.)

Constraints: do NOT use `set_option maxHeartbeats 0`; keep each lemma under `timeout 600`; split
into per-monomial-block lemmas as needed (a sympy certificate closed by `linear_combination` per
block is the accepted technique here).
-/

-- (guidance only; the theorem statement lives at `Work/MotAS/KleinTwScalarAS`)
