/-
# The variational (jump / oscillation) inequalities of Krause--Mirek--Tao

This directory builds the finite, purely combinatorial engine behind
Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. 195 (2022):

* `Work.Analysis.Variation.rademacher_menshov_one_dim` -- the one-dimensional
  Rademacher--Menshov inequality (MSZ, Lemma 2.5 pp. 534);
* `Work.Analysis.Variation.rademacher_menshov_two_dim` -- the paper's Lemma `2drm`;
* `Work.Analysis.Variation.rademacher_menshov_bilinear` -- the paper's Corollary `rm-bil`;
* the vector-valued Lépingle inequality (`Work.Analysis.Variation.Lepingle`).

## Conventions

Our basic object is the **truncated `r`-variation seminorm** `Vr r K a` of a sequence
`a : ℕ → ℂ`: the supremum, over all monotone sequences `0 = u 0 ≤ u 1 ≤ ⋯ ≤ u J ≤ K`, of the
`ℓ^r` norm of the jumps `a (u (j+1)) - a (u j)`.  It is `0` when `K = 0`.

The paper's Lemma `2drm` writes its right-hand side as a sum over the dyadic scales
`M ∈ 2^ℕ ∩ [K]` of the `ℓ^r` norms of the increments of `a` on the aligned blocks
`(M (j-1), M j]`.  We use the **tiling** family of blocks of size `M`, namely
`(M x, min (M (x+1)) K]` for `x ∈ range (nb K M)`, `nb K M = ⌈K / M⌉`; these blocks cover
`(0, K]` exactly (the last one possibly being short), and the family of *full* aligned blocks
used in the paper's statement is a subfamily.  All our block families are therefore *supersets*
of the paper's, which only makes the inequalities stronger; the tiling property is what makes the
sign-reindexing step of Corollary `rm-bil` exact.

The dyadic arithmetic is organised around `rnd N m`, the largest multiple of `2 ^ m` below `N`:
`a N = ∑_{m} (a (rnd N m) - a (rnd N (m+1)))`, and each summand is either `0` or the increment
of a single aligned block of size `2 ^ m`.  This is the whole combinatorial content of the
one- and two-dimensional Rademacher--Menshov inequalities; see `Work.Analysis.Variation.Dyadic`.
-/
import Mathlib

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- `rnd N m` is the largest multiple of `2 ^ m` that is `≤ N`. -/
def rnd (N m : ℕ) : ℕ := 2 ^ m * (N / 2 ^ m)

/-- `nb K M = ⌈K / M⌉` is the number of blocks of size `M` needed to cover `(0, K]`. -/
def nb (K M : ℕ) : ℕ := (K + M - 1) / M

/-- The `r`-variation seminorm of the sequence `a`, truncated at `K` and anchored at `0`:
the supremum, over all monotone `0 = u 0 ≤ u 1 ≤ … ≤ u J ≤ K`, of the `ℓ^r` norm of the
successive differences. -/
noncomputable def Vr (r : ℝ) (K : ℕ) (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → ℕ), ⨆ (_ : Monotone u) (_ : u 0 = 0) (_ : ∀ i, u i ≤ K),
    (∑ j : Fin J, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ r) ^ (1 / r)

/-- The full truncated variational norm: the supremum of `‖a‖` plus the variation. -/
noncomputable def VrFull (r : ℝ) (K : ℕ) (a : ℕ → ℂ) : ℝ≥0∞ :=
  (⨆ k : Fin (K + 1), ‖a k‖ₑ) + Vr r K a

/-- The dyadic scales up to `K`: `{2 ^ m : m ≤ log2 K}` (when `K = 0` this is `{1}`, and the
corresponding increment norms vanish, so the difference is immaterial). -/
def dyadicUpTo (K : ℕ) : Finset ℕ := (Finset.range (Nat.log2 K + 1)).image (fun m => 2 ^ m)

/-- The `ℓ^r` norm of the increments of `a` over the blocks of size `M` tiling `(0, K]`. -/
noncomputable def incLp (r : ℝ) (K M : ℕ) (a : ℕ → ℂ) : ℝ≥0∞ :=
  (∑ x ∈ Finset.range (nb K M), ‖a (min (M * (x + 1)) K) - a (M * x)‖ₑ ^ r) ^ (1 / r)

/-- The second difference of `a : ℕ → ℕ → ℂ` over the rectangle with lower-left corner
`(L₁, L₂)` and side lengths `M₁, M₂`, with right ends truncated at `K`. -/
def blockDelta2 (a : ℕ → ℕ → ℂ) (K M₁ L₁ M₂ L₂ : ℕ) : ℂ :=
  a (min (L₁ + M₁) K) (min (L₂ + M₂) K) - a L₁ (min (L₂ + M₂) K)
    - a (min (L₁ + M₁) K) L₂ + a L₁ L₂

/-- The `ℓ^r` norm of the second differences of `a` over the rectangles of side lengths
`M₁, M₂` tiling `(0, K] × (0, K]`. -/
noncomputable def incLp2 (r : ℝ) (K M₁ M₂ : ℕ) (a : ℕ → ℕ → ℂ) : ℝ≥0∞ :=
  (∑ p ∈ (Finset.range (nb K M₁)).product (Finset.range (nb K M₂)),
    ‖blockDelta2 a K M₁ (M₁ * p.1) M₂ (M₂ * p.2)‖ₑ ^ r) ^ (1 / r)

/-- The raw dyadic increment at scale `2 ^ m` and index `k`: the increment of `a` over the
block `(2 ^ m * (k - k % 2), 2 ^ m * k]`, which is empty (value `0`) when `k` is even. -/
def rawH (a : ℕ → ℂ) (m k : ℕ) : ℂ := a (2 ^ m * k) - a (2 ^ m * (k - k % 2))

/-- The raw dyadic `ℓ^r` family at scale `2 ^ m`: since `k = N / 2 ^ m` ranges over
`range (K / 2 ^ m + 1)` as `N` ranges over `[0, K]`, the sequence `N ↦ a (rnd N m) - a (rnd N (m+1))`
takes its values in this family. -/
noncomputable def rawLp (r : ℝ) (K m : ℕ) (a : ℕ → ℂ) : ℝ≥0∞ :=
  (∑ k ∈ Finset.range (K / 2 ^ m + 1), ‖rawH a m k‖ₑ ^ r) ^ (1 / r)

/-- The raw two-dimensional second difference at scales `2 ^ m₁`, `2 ^ m₂`. -/
def rawH2 (a : ℕ → ℕ → ℂ) (m₁ m₂ k₁ k₂ : ℕ) : ℂ :=
  a (2 ^ m₁ * k₁) (2 ^ m₂ * k₂) - a (2 ^ m₁ * (k₁ - k₁ % 2)) (2 ^ m₂ * k₂)
    - a (2 ^ m₁ * k₁) (2 ^ m₂ * (k₂ - k₂ % 2))
    + a (2 ^ m₁ * (k₁ - k₁ % 2)) (2 ^ m₂ * (k₂ - k₂ % 2))

/-- The raw two-dimensional dyadic `ℓ^r` family. -/
noncomputable def rawLp2 (r : ℝ) (K m₁ m₂ : ℕ) (a : ℕ → ℕ → ℂ) : ℝ≥0∞ :=
  (∑ q ∈ (Finset.range (K / 2 ^ m₁ + 1)).product (Finset.range (K / 2 ^ m₂ + 1)),
    ‖rawH2 a m₁ m₂ q.1 q.2‖ₑ ^ r) ^ (1 / r)

/-- The sign attached to a Boolean Rademacher variable, as an element of `ℂ`. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

end Work.Analysis.Variation
