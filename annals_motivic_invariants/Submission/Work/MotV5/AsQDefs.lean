import Mathlib
import Submission.Work.MotK.KleinData
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.AsQDefs` — the descended quadric of the AS link

The characteristic-`5` (Artin–Schreier) branch of route V of

* H.-Y. Lin, E. Shinder, *Motivic invariants of birational maps*, Ann. of Math. **199** (2024),

needs the S-twist of the *shift-invariant* quadric `q = Σ_k p_k = Work.MotK.kleinQ` of the Klein
curve: the twisted Klein coordinates are the interpolation coordinates
`x_i = Work.MotV.asCoord W y i = ∑_j y_j (W + i)^j` with `W⁵ - W = g`, and the quadric read in the
Galois coordinates,

  `q(W, y) = kleinQ a b (asCoord W y)`,

must *descend* to a quadric `Q ∈ K[y_0, …, y_4]`, `K = 𝕜(t)`, with coefficients in `𝕜`
(`Work.MotV5.asQpoly`).  The descent is the content of `Work.MotV5.kleinQ_asCoord_eq`: in
characteristic `5` the value `kleinQ a b (asCoord W y)` is *independent of `W`* (and of `g`), so it
is given by the explicit polynomial

`asQval a b y = (-2a² + 2ab + 2b²)(y₀y₄) + (-2a² + 2ab + 2b²)(y₁y₃) + (-a² + ab + b²)y₂²
             + (-2a² - 2b²)(y₂y₄) + (2a² + 2b²)y₃² + (-2a² + ab + 2b²)y₄²`.

The coefficients are the ones obtained from the Galois trace
`∑_{i ∈ 𝔽₅} (W + i)^m = -(δ_{m,4} + δ_{m,8})` for `m ≤ 8` and the reindexing
`kleinQ a b x = -ab ∑_i x_i² + a² ∑_i x_i x_{i+1} - b² ∑_i x_i x_{i+3}`.

## Contents

* `asQval` — the value of the descended quadric (universe-`0`, any commutative ring);
* `asQpoly` — the descended quadric `Q ∈ MvPolynomial (Fin 5) (RatFunc 𝕜)`;
* `cast_mod_charP_five`, `ofNat_eq_mod_charP_five` — the characteristic-`5` numeral reductions used
  by the polynomial computation of `kleinQ_asCoord_eq`.
-/

set_option autoImplicit false

namespace Work.MotV5

noncomputable section

/-! ## §1 The value of the descended quadric -/

/-- The descended quadric, evaluated on `y : Fin 5 → R`: the value of
`kleinQ a b (asCoord W y)` in characteristic `5`, written as a quadratic form in `y` with
coefficients in `ℤ[a, b]`. -/
def asQval {R : Type*} [CommRing R] (a b : R) (y : Fin 5 → R) : R :=
  (-2 * a ^ 2 + 2 * a * b + 2 * b ^ 2) * (y 0 * y 4)
    + (-2 * a ^ 2 + 2 * a * b + 2 * b ^ 2) * (y 1 * y 3)
    + (-a ^ 2 + a * b + b ^ 2) * (y 2 * y 2)
    + (-2 * a ^ 2 - 2 * b ^ 2) * (y 2 * y 4)
    + (2 * a ^ 2 + 2 * b ^ 2) * (y 3 * y 3)
    + (-2 * a ^ 2 + a * b + 2 * b ^ 2) * (y 4 * y 4)

/-- The descended quadric `Q ∈ K[y_0, …, y_4]`, `K = 𝕜(t)`, whose coefficients lie in `𝕜`:
the S-twist of the shift-invariant quadric `q` of the Klein curve (see the module docs). -/
def asQpoly (𝕜 : Type) [Field 𝕜] (a b : 𝕜) : MvPolynomial (Fin 5) (RatFunc 𝕜) :=
  MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) (-2 * a ^ 2 + 2 * a * b + 2 * b ^ 2)) *
      (MvPolynomial.X 0 * MvPolynomial.X 4)
    + MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) (-2 * a ^ 2 + 2 * a * b + 2 * b ^ 2)) *
        (MvPolynomial.X 1 * MvPolynomial.X 3)
    + MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) (-a ^ 2 + a * b + b ^ 2)) *
        (MvPolynomial.X 2 * MvPolynomial.X 2)
    + MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) (-2 * a ^ 2 - 2 * b ^ 2)) *
        (MvPolynomial.X 2 * MvPolynomial.X 4)
    + MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) (2 * a ^ 2 + 2 * b ^ 2)) *
        (MvPolynomial.X 3 * MvPolynomial.X 3)
    + MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) (-2 * a ^ 2 + a * b + 2 * b ^ 2)) *
        (MvPolynomial.X 4 * MvPolynomial.X 4)

/-! ## §2 Numeral reduction in characteristic `5`

The polynomial computation `kleinQ_asCoord_eq` is a big expansion whose coefficients are all
divisible by `5`; these two lemmas let `simp` reduce *every* numeral `n : R` of a ring of
characteristic `5` to `n % 5`, after which `ring` closes the (small) remaining identity. -/

/-- In a ring of characteristic `5`, the numeral `n` agrees with `n % 5`. -/
lemma cast_mod_charP_five {R : Type*} [CommRing R] [CharP R 5] (n : ℕ) :
    ((n : ℕ) : R) = ((n % 5 : ℕ) : R) := by
  have h : ((n : ℕ) : R) = ((5 * (n / 5) + n % 5 : ℕ) : R) := by rw [Nat.div_add_mod]
  rw [h, Nat.cast_add, Nat.cast_mul,
    show ((5 : ℕ) : R) = 0 from CharP.cast_eq_zero R 5, zero_mul, zero_add]

/-- In a ring of characteristic `5`, a numeral `n ≥ 2` agrees with `n % 5`.  Stated for
`OfNat.ofNat`, the form in which `ring_nf` emits coefficients. -/
lemma ofNat_eq_mod_charP_five {R : Type*} [CommRing R] [CharP R 5] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : R) = ((n % 5 : ℕ) : R) := by
  rw [← Nat.cast_ofNat]
  exact cast_mod_charP_five n

end
end Work.MotV5
