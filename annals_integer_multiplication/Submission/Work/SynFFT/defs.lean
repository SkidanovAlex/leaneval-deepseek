import Mathlib
import Submission.HvdH.Interfaces

/-!
# SynFFT: shared definitions (area SynFFT, paper Lemma 3.2 + Prop 3.3)

We formalize the mathematics of the synthetic transforms over `R = ℂ[y]/(y^r+1)` in a shape
convenient for the StackLang program that has to be built:

* `bitrev k n` — reversal of the low `k` bits;
* `Arr r = ℕ → Fin r → ℂ` — arrays of elements of `R`, indexed by natural numbers (we always
  only look at positions `< t`, and the operators below are insensitive to the rest);
* `dftN r t sgn` — the one-dimensional synthetic transform `(1/t) Σ_k y^{sgn·(2r/t)·j·k} a_k`
  (a natural-number-indexed version of `synDFT r [t] sgn`);
* `lvlN r m sgn` — the exact version of one radix-two butterfly stage (block size `m`);
* `levels r sgn t k` — the composition of the stages of sizes `t, t/2, …, t/2^{k-1}`;
* `dftMultiN r ts sgn` — natural-number-indexed version of `synDFT r ts sgn`;
* `axisT r A t B sgn` — the one-dimensional synthetic transform along one axis of a flat
  lexicographic array of shape `A × t × B`;
* `ApproxL`, `annList` — the program-facing meaning of a list of fixed-point elements and of a
  list of annotated elements.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- `bitrev k n` = the number obtained by reversing the low `k` bits of `n`. -/
def bitrev (k n : ℕ) : ℕ := (Finset.range k).sum fun i => (n / 2 ^ i % 2) * 2 ^ (k - 1 - i)

/-- Arrays of `r` coefficient vectors. -/
abbrev Arr (r : ℕ) := ℕ → Fin r → ℂ

open scoped BigOperators

/-- One-dimensional synthetic transform:
`(dftN r t sgn a) j = (1/t) Σ_{k<t} y^{sgn·(2r/t)·j·k} a_k`. -/
noncomputable def dftN (r t : ℕ) (sgn : ℤ) (a : Arr r) : Arr r :=
  fun j c => (1 / (t : ℂ)) * ∑ k ∈ Finset.range t,
    yMul r (sgn * ((2 * r / t * j * k : ℕ) : ℤ)) (a k) c

/-- One radix-two butterfly stage of block size `m` (exact arithmetic):
for `j = p % m < m/2` the two outputs `(a_p + a_{p+m/2})/2`, `y^{sgn·(2r/m)·j}(a_{p-m/2} - a_p)/2`. -/
noncomputable def lvlN (r m : ℕ) (sgn : ℤ) (a : Arr r) : Arr r :=
  fun p c =>
    if (p % m) < m / 2 then (a p c + a (p + m / 2) c) / 2
    else yMul r (sgn * (((2 * r / m) * (p % m - m / 2) : ℕ) : ℤ))
      (fun c' => (a (p - m / 2) c' - a p c') / 2) c

/-- `levels r sgn t k a`: apply the stages of sizes `t, t/2, …, t/2^{k-1}` (first `t`). -/
noncomputable def levels (r : ℕ) (sgn : ℤ) (t : ℕ) : ℕ → Arr r → Arr r
  | 0, a => a
  | (k + 1), a => levels r sgn (t / 2) k (lvlN r t sgn a)

/-- The twiddle exponent of the level-`m` butterfly stage for an element at flat position `q`
on an axis of stride `B`: `sgn · (2r/m) · (q/B mod m/2)`. -/
def twExp (r : ℕ) (sgn : ℤ) (B m : ℕ) (q : ℕ) : ℤ := sgn * (((2 * r / m) * (q / B % (m / 2)) : ℕ) : ℤ)

/-- The level-`m` butterfly stage of an axis of stride `B` (exact operator, block-local). -/
noncomputable def lvlAx (r B m : ℕ) (sgn : ℤ) (a : Arr r) : Arr r :=
  fun q c =>
    if (q / B % m) < m / 2 then (a q c + a (q + m / 2 * B) c) / 2
    else yMul r (twExp r sgn B m q) (fun c' => (a (q - m / 2 * B) c' - a q c') / 2) c

/-- `levelsAx r B sgn t k a`: apply the level stages of sizes `t, t/2, …, t/2^{k-1}` along an
axis of stride `B` (first `t`). -/
noncomputable def levelsAx (r : ℕ) (B : ℕ) (sgn : ℤ) (t : ℕ) : ℕ → Arr r → Arr r
  | 0, a => a
  | (k + 1), a => levelsAx r B sgn (t / 2) k (lvlAx r B t sgn a)

/-- Natural-number-indexed version of `synDFT` (flat lexicographic layout, last index fastest). -/
noncomputable def dftMultiN (r : ℕ) (ts : List ℕ) (sgn : ℤ) (a : Arr r) : Arr r :=
  fun j c => (1 / (ts.prod : ℂ)) * ∑ k ∈ Finset.range ts.prod,
    yMul r (sgn * synExp r ts (digits ts j) (digits ts k)) (a k) c

/-- Synthetic transform along one axis of a flat array of shape `A × t × B`
(the axis index runs with stride `B`). -/
noncomputable def axisT (r t B : ℕ) (sgn : ℤ) (a : Arr r) : Arr r :=
  fun p c => (1 / (t : ℂ)) * ∑ u ∈ Finset.range t,
    yMul r (sgn * (((2 * r / t) * ((p / B) % t) * u : ℕ) : ℤ))
      (a (p - (p / B % t) * B + u * B)) c

/-! ## Program-facing predicates -/

/-- The fixed-point array represented by a list of `r`-coefficient vectors. -/
noncomputable def toFun (p r : ℕ) (ws : List (List (ℤ × ℤ))) : Arr r :=
  fun i j => fxC p ((ws.getD i []).getD j (0, 0))

/-- `ws` (a list of `R`-elements) approximates the array `v` with error `≤ e` in the
`2^p`-scaled sense, and every coefficient lies in the unit disc. -/
def ApproxL (p r t : ℕ) (ws : List (List (ℤ × ℤ))) (v : Fin t → Fin r → ℂ) (e : ℝ) : Prop :=
  ws.length = t ∧ (∀ w ∈ ws, InDiscVec p r w) ∧
    ∀ (i : Fin t) (j : Fin r),
      (2 : ℝ) ^ p * ‖fxC p ((ws.getD (i : ℕ) []).getD (j : ℕ) (0, 0)) - v i j‖ ≤ e

/-- The list of values of a length-`t` array of `R`-elements. -/
def cvecs (ws : List (List (ℤ × ℤ))) : List Val := ws.map cvecVal

/-- The annotated list: position `i` carries `cons (int i) (cvecVal w_i)`. -/
def annList (ws : List (List (ℤ × ℤ))) : List Val :=
  (List.range ws.length).map fun (i : ℕ) => Val.cons (.int (i : ℤ)) (cvecVal (ws.getD i []))

end Work.SynFFT
