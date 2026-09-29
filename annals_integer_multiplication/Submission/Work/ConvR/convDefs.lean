import Mathlib
import Submission.HvdH.Interfaces

/-!
# ConvR: the synthetic character exponent with integer coefficients

Owner: ConvR area.  This file is shared vocabulary for `convIdentity`
(the synthetic diagonalisation of the convolution over `R = ℂ[y]/(y^r+1)`).

`HvdH.synExp r ts js ks = Σᵢ (2r/tᵢ)·jᵢ·kᵢ` has *natural* digit lists `js`, `ks`.  When the
coefficients come from a difference of digit lists (as in the orthogonality relation for the
synthetic DFT, where the coefficient of `kᵢ` is `jᵢ - aᵢ - bᵢ`), the natural-number version is
not enough; `synExpZ r ts c ks = Σᵢ cᵢ·(2r/tᵢ)·kᵢ` is the signed form, with `c : List ℤ`.

## How to prove the synthetic character sums (`Work.ConvR.yCharSum1`, `yCharSumConv`)

No complex exponentials and no `Work.DFT.rootSum` are involved: the whole content is the ring
structure of `R = ℂ[y]/(y^r+1)`, where `y^r = -1`, `y` has exact order `2r`, and
`HvdH.yMul r e a` is multiplication by `y^e` (see `Submission/Work/SynFFT/yMulFacts.lean`,
`yMulExpAdd.lean`, `yMulLinear.lean`).

**One dimension.**  Let `r = 2^a` (`a ≥ 1`) and `t = 2^b` with `t ∣ 2r` (get `t = 2^b` from
`t ∣ 2^(a+1)` via `Nat.dvd_prime_pow`, using `t > 0`).  For `Z b s W := ∑ k : Fin (2^b), yMul r (s*k) W`
one has the recursion `Z (b+1) s W = Z b s W + yMul r (s * 2^b) (Z b s W)` (split the index set).
With `s := c * (2r/t)`:
* if `t ∣ c` then `s = 2r * (c/t)`, so every `yMul r (s*k)` is the identity, whence `Z = t • W`;
* if `t ∤ c`, write `c = 2^j * m` with `m` odd and `j < b` (2-adic descent on `|c|`).  Then
  `s * 2^(b-1-j) = r * m`, and `yMul r (r*m) = -id` for odd `m`, because `yMul r r = -id`,
  `yMul r (2*r) = id` and `yMul` is an action of `ℤ`.  Now prove by induction on `b`:
  if `yMul r (s * 2^i) = -id` for some `i < b` then `Z b s W = 0` — at `i = b-1` the recursion gives
  `Z = Z' - Z' = 0`, and for `i < b-1` the induction hypothesis gives `Z' = 0`, whence
  `Z = 0 + yMul r _ 0 = 0` (`yMul` is additive, so it maps `0` to `0`).
  Note the crucial point: no cancellation in a zero-divisor-free ring is needed — the factor
  `1 + y^(r·odd) = 0` appears as one of the binomial factors of the binary expansion, which is why
  this route works directly in `ℂ[y]/(y^r+1)`.

**Several dimensions.**  Induct on `ts` exactly as `Work.DFT.charSumGen` does, with
`yMul` in place of `Complex.exp` and `synExpZ` in place of `myPhase`: reindex
`Fin (t * ts'.prod)` as `k = r + ts'.prod * q` (`Work.DFT.sumFinMul`), use
`digits (t :: ts') (r + ts'.prod * q) = q :: digits ts' r` (see
`Submission/Work/SynFFT/multiCons.lean` for this computation), split the exponent with
`yMulExpAdd`, apply the induction hypothesis to the inner sum, pull the scalar out with the
`c •`-law of `yMul`, and finish with the one-dimensional sum.  The `if` bookkeeping uses
`Work.DFT.getDDvdCons` and `Work.DFT.iteMulIteZero`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- `Σᵢ cᵢ · (2r/tᵢ) · kᵢ` for an integer coefficient list `c` and a digit list `ks`. -/
def synExpZ (r : ℕ) : List ℕ → List ℤ → List ℕ → ℤ
  | t :: ts, c :: cs, k :: ks => c * (((2 * r / t) * k : ℕ) : ℤ) + synExpZ r ts cs ks
  | _, _, _ => 0

@[simp] theorem synExpZ_cons (r t : ℕ) (ts : List ℕ) (c : ℤ) (cs : List ℤ) (k : ℕ)
    (ks : List ℕ) :
    synExpZ r (t :: ts) (c :: cs) (k :: ks) =
      c * (((2 * r / t) * k : ℕ) : ℤ) + synExpZ r ts cs ks := rfl

@[simp] theorem synExpZ_nil (r : ℕ) (c : List ℤ) : synExpZ r [] c [] = 0 := rfl

end Work.ConvR
