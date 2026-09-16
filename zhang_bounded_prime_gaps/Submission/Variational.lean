import Mathlib

/-!
# The combinatorial core of the variational (numerics) computation

The exact evaluation of the Maynard--Polymath8 variational functionals
`M_{k,ε}` over symmetric polynomials rests on the master formula

  `∫_{R^m} (1 - Σ x) ^ A · P_α · P_β dx = A! · S(α,β,m) / (A + |α| + |β| + m)!`

where `P_α` is the monomial symmetric polynomial of the signature `α` and

  `S(α,β,m) = Σ_{a ∈ Perm(α), b ∈ Perm(β)} ∏_i (a_i + b_i)!`

expresses the sum over the `m` coordinates of the products of factorials.  This
module defines `S` as a *computable* function of the two signatures and the
number of coordinates, so that (large) exact numerical certificates can be
checked by kernel evaluation (`decide`) after clearing denominators.

The recursion is

  `S(β, β', k+1) = Σ_{p ∈ {0} ∪ β} Σ_{q ∈ {0} ∪ β'} (p+q)! · S(β - p, β' - q, k)`

with `β - p` the multiset obtained by deleting one occurrence of `p ≠ 0`, and
`S(∅,∅,0) = 1`, `S(β,β',0) = 0` otherwise.

NOTE (measured): this *unmemoised* recursion is exponential in `k` and therefore
unusable for the real parameters (`k = 50`, signatures of degree ≤ 27 — a kernel
`decide` on `Ssum [2]*12 [2]*12 49` does not terminate in 20 minutes).  It is
perfectly fine for small cases, all of which are checked below by `decide`.
For the production computation one should instead use either

* a **memoised** evaluation (carry a table of `(β,β',m) ↦ S` through the
  recursion), or
* the closed **transport-matrix** formula: with `β` having distinct parts
  `u_1,…,u_A` of multiplicities `m_i` and `β'` having `v_1,…,v_B` of
  multiplicities `n_j`,

  `S(β,β',k) = Σ_T  k! · [∏_{ij}(u_i+v_j)!^{t_{ij}}] · [∏_i u_i!^{ρ_i}]
        · [∏_j v_j!^{σ_j}] / ( ∏_{ij} t_{ij}! · ∏_i ρ_i! · ∏_j σ_j! · (k-ℓ)! )`

  summed over all nonnegative integer matrices `T = (t_{ij})` with row sums
  `≤ m_i`, column sums `≤ n_j`, where `ρ_i = m_i - Σ_j t_{ij}`,
  `σ_j = n_j - Σ_i t_{ij}` and `ℓ = Σ t_{ij} + Σρ_i + Σσ_j` (the formula has
  value `0` if `ℓ > k`).  The number of such matrices is at most
  `∏_i C(m_i + B, B)`, which is tiny for the signatures that occur (e.g. `13`
  for `β = β' = (2,…,2)`).
-/

namespace Commons.NumberTheory.MaynardSieve

/-- Delete one occurrence of `v` from a multiset given as a list (a no-op if `v` is absent). -/
def eraseOne (s : List ℕ) (v : ℕ) : List ℕ :=
  match s with
  | [] => []
  | a :: t => if a = v then t else a :: eraseOne t v

theorem length_eraseOne_le (s : List ℕ) (v : ℕ) : (eraseOne s v).length ≤ s.length := by
  induction s with
  | nil => simp [eraseOne]
  | cons a t ih =>
      by_cases h : a = v
      · simp [eraseOne, h]
      · simp only [eraseOne, h, if_false, List.length_cons]
        omega

/-- The labelled-assignment sum `S(β, β', k) = Σ_{a ~ β, b ~ β'} ∏_i (a_i + b_i)!`. -/
def Ssum : List ℕ → List ℕ → ℕ → ℕ
  | β, β', 0 => if β = [] ∧ β' = [] then 1 else 0
  | β, β', (k + 1) =>
      let ps := 0 :: β.dedup
      let qs := 0 :: β'.dedup
      (ps.product qs).foldl
        (fun acc pq => acc + Nat.factorial (pq.1 + pq.2) * Ssum (eraseOne β pq.1) (eraseOne β' pq.2) k) 0

/-! ## Kernel-checked values (validating the computable recursion) -/

example : Ssum [1] [1] 2 = 6 := by decide
example : Ssum [2] [2] 1 = 24 := by decide
example : Ssum [2, 2] [2, 2] 4 = 5856 := by decide
example : Ssum [2, 2] [2, 2] 5 = 12000 := by decide
example : Ssum [2, 1] [2] 3 = 240 := by decide
example : Ssum [2, 2, 2] [2] 5 = 3200 := by decide
example : Ssum [4, 3] [3, 3] 6 = 144011520 := by decide
example : Ssum [2, 2, 2, 2] [2, 2] 6 = 254400 := by decide

end Commons.NumberTheory.MaynardSieve
