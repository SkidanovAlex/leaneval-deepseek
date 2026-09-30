import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Helper definitions for the Linnik/Newton counting lemma

For a tuple `v : Fin k → ZMod p` of residues we define

* `psumEval v j = ∑ i, v i ^ j`   (the `j`-th power sum),
* `esymmEval v m`                  (the `m`-th elementary symmetric function,
  obtained by evaluating the elementary symmetric `MvPolynomial`),
* `polyOf v = ∏ i, (X - C (v i))`  (the monic polynomial with roots the entries of `v`).

These are used to show that the first `k` power sums determine an injective
`k`-tuple of residues up to permutation.
-/

namespace Work.BMF.N4chain

/-- The `j`-th power sum `∑ i, v i ^ j` of a tuple of residues. -/
def psumEval {p k : ℕ} (v : Fin k → ZMod p) (j : ℕ) : ZMod p := ∑ i, (v i) ^ j

/-- The `m`-th elementary symmetric function of a tuple of residues, obtained by
evaluating the elementary symmetric `MvPolynomial`. -/
noncomputable def esymmEval {p k : ℕ} (v : Fin k → ZMod p) (m : ℕ) : ZMod p :=
  MvPolynomial.aeval v (MvPolynomial.esymm (Fin k) (ZMod p) m)

/-- The monic polynomial whose roots are the entries of `v`. -/
noncomputable def polyOf {p k : ℕ} (v : Fin k → ZMod p) : Polynomial (ZMod p) :=
  ∏ i, (Polynomial.X - Polynomial.C (v i))

end Work.BMF.N4chain
