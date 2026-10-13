/-
  WilE9 / Sharp — the *pulled-back* system of the BNZ §3 transport (definitions).

  Given a stratum `S = (X, j, h)` with `p = n` base coordinates and `q = 1 + m` fibre
  coordinates (so `X : SemiPf (n + (1+m))`, `h : Fin (1+m) → EAPoly (n + (1+m)) r`), the
  pulled-back system lives in the ambient `ℝ^{Npb n m}` with

  * the base `x : ℝⁿ` (the *original* coordinates of the function `f`), and
  * the fibre `(s, y, w, τ, u, aux)`, where `s` is the unknown, `y i = ψ (x i)`,
    `w i = psig (x i)`, `τ = ψ s`, `u = psig s` and `aux` are the stratum's auxiliary
    coordinates.

  Its `2n + m + 3` equations are

  | index          | equation                | solves for |
  |----------------|-------------------------|------------|
  | `0`            | `τ - s * u`             | `s`        |
  | `1 + i`        | `y i - x i * w i`       | `y i`      |
  | `n + 1 + i`    | `y i ^ 2 + w i ^ 2 - 1` | `w i`      |
  | `2n + 1`       | `τ ^ 2 + u ^ 2 - 1`     | `u`        |
  | `2n + 2 + a`   | `h a`                   | `τ`, `aux` |

  so that the system is *square*, and its fibre Jacobian `jm (pbChain c) (pbF h)` is invertible
  at every point that satisfies the structural relations with `w > 0`, `u > 0` and
  `∂h / ∂(τ,aux)` invertible (see `WilE9/Sharp/pb_det_ne_zero`).  `WilE9.Ift.ift_identity` then
  computes `∂_L s = P_L / Q^{2|L|}` for `P_L = pbP L`, `Q = pbQ`, with `L` a list of *`x`*-
  directions — that is the whole content of BNZ §3's implicit-function formula after the
  `ψ`-change of variables, with no Faà di Bruno expansion.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Layout
import Submission.Work.WilE9.Ift.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- A pulled-back ambient point, read in the stratum's own coordinates `(y, τ, aux)`. -/
def pbStrat {n m : ℕ} (z : Fin (Npb n m) → ℝ) : Fin (n + (1 + m)) → ℝ :=
  fun i => z (sIdxPb n m i)

/-- A stratum polynomial, reindexed into the pulled-back ambient. -/
def pbRaise {n m r : ℕ} (P : EAPoly (n + (1 + m)) r) : EAPoly (Npb n m) r :=
  P.rename (Sum.map (sIdxPb n m) id)

/-- The stratum's chain, reindexed into the pulled-back ambient: the coefficients are placed on
the coordinates `y`, `τ`, `aux` and are `0` elsewhere. -/
def pbChain {n m r : ℕ} (c : EAChain (n + (1 + m)) r) : EAChain (Npb n m) r where
  a j l := ∑ i : Fin (n + (1 + m)), if sIdxPb n m i = l then c.a j i else 0
  b := c.b

/-- The equations of the pulled-back system. -/
def pbF (n m r : ℕ) (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) :
    Fin (qpb n m) → EAPoly (Npb n m) r := fun j =>
  if _ : (j : ℕ) = 0 then
    MvPolynomial.X (Sum.inl (pbT n m)) - MvPolynomial.X (Sum.inl (pbS n m)) *
      MvPolynomial.X (Sum.inl (pbU n m))
  else if h1 : (j : ℕ) ≤ n then
    (let i : Fin n := ⟨(j : ℕ) - 1, by omega⟩
     MvPolynomial.X (Sum.inl (pbY n m i)) - MvPolynomial.X (Sum.inl (pbX n m i)) *
       MvPolynomial.X (Sum.inl (pbW n m i)))
  else if h2 : (j : ℕ) ≤ 2 * n then
    (let i : Fin n := ⟨(j : ℕ) - n - 1, by omega⟩
     MvPolynomial.X (Sum.inl (pbY n m i)) ^ 2 + MvPolynomial.X (Sum.inl (pbW n m i)) ^ 2 - 1)
  else if _ : (j : ℕ) = 2 * n + 1 then
    MvPolynomial.X (Sum.inl (pbT n m)) ^ 2 + MvPolynomial.X (Sum.inl (pbU n m)) ^ 2 - 1
  else
    (let a : Fin (1 + m) := ⟨(j : ℕ) - (2 * n + 2), by have := j.isLt; simp [qpb] at this ⊢; omega⟩
     pbRaise (n := n) (m := m) (r := r) (h a))

/-- The denominator `Q` of the pulled-back system. -/
def pbQ {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) : EAPoly (Npb n m) r :=
  jQ (pbChain c) (pbF n m r h)

/-- The numerator `P_L` of the pulled-back system, for the derivative of `s = f x` in the
`x`-directions of the list `L`. -/
def pbP {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) : EAPoly (Npb n m) r :=
  iftP (pbChain c) (pbF n m r h) (fS n m) L

end Work.WilE9.Sharp
