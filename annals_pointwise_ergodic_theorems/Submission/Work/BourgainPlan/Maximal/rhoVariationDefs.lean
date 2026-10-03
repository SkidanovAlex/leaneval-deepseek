import Mathlib
import Submission.Work.BourgainPlan.Maximal.varSeminormDefs

/-!
# The `ρ`-variation and `ρ`-oscillation seminorms of a sequence (KMSZ §5.2)

Kosz–Mirek–Słomian–Zhang, arXiv:2606.12663, §5.2, define, for `ρ ∈ [1, ∞)` and a sequence
`(h_n)_{n ∈ I}` in a seminormed group,

* the **`ρ`-variation seminorm**
  `V^ρ(h_n : n ∈ I) = sup_{J} sup_{(n_j)_{j≤J} increasing in I} (Σ_{j<J} ‖h_{n_{j+1}} − h_{n_j}‖^ρ)^{1/ρ}`;
* the **`ρ`-oscillation seminorm**
  `O^ρ(h_n : n ∈ I) = sup_{J} sup_{(o_j)_{j≤J} increasing} (Σ_{j<J} sup_{n ∈ [o_j, o_{j+1})} ‖h_n − h_{o_j}‖^ρ)^{1/ρ}`.

Their Proposition 5.10 states that for `ρ ≥ 2` each of the `ρ`-variation, `ρ`-oscillation and
`ρ`-jump seminorms is a **Rademacher–Menshov seminorm** in the sense of their Definition 5.1, so
that the seminorm refinement of the Ionescu–Wainger multiplier theorem (their Theorem 5.2) applies
to it.  That is the interface through which the modern route obtains

* the maximal inequality (KMSZ (6.9): the maximal function is bounded by the base value plus *any*
  `ρ`-variation, `ρ ≥ 1`), and
* the variational and oscillation inequalities (KMSZ Theorem 6.4 (i)/(iii); the second is the
  challenge's `OscillationStatement`),

from a single multiplier theorem.  The `2`-variation (`ρ = 2`) is the case used for the *maximal*
half (`Work.BourgainPlan.Maximal.varTwo`, `varTwo_le_rmLevels`); the range `ρ > 2` is the one in
which the published variational inequalities hold (Bourgain §3 and §7; Krause arXiv:1402.1803,
Prop. 1.4), the `2`-variation being unbounded on `ℓ²` (Krause §8; KMSZ Remark after (6.7)).

The point of the `ρ`-variation, as opposed to the maximal function, is that it is **translation
invariant** in the index (`chainLp_shift`): this is what makes KMSZ's condition (2) applicable
with no base term, and it is why the maximal function of Bourgain's averages is bounded via the
variation in the modern route.

This file holds only the *vocabulary*; the structural lemmas (the splitting of KMSZ Definition
5.1(1), the Rademacher–Menshov inequality of condition (2), and the pointwise domination
`O^ρ ≤ V^ρ ≤ V²` of Proposition 5.10) are in the companion modules in this directory.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The `ℓ^ρ`-length of the increments of `a` along the chain of indices `t`:
`chainLp ρ J a t = (Σ_{j < J} ‖a (t (j+1)) − a (t j)‖^ρ)^{1/ρ}`.  Only the values
`t 0, …, t J` matter.  For `ρ = 2` this is `chainSq`. -/
def chainLp (ρ : ℝ) (J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) : ℝ :=
  (∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ ρ) ^ (1 / ρ)

lemma chainLp_nonneg (ρ : ℝ) (J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) : 0 ≤ chainLp ρ J a t :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _

lemma chainLp_zero {ρ : ℝ} (hρ : 0 < ρ) (a : ℕ → E) (t : ℕ → ℕ) : chainLp ρ 0 a t = 0 := by
  rw [chainLp]
  simp only [Finset.range_zero, Finset.sum_empty]
  exact Real.zero_rpow (by positivity : (1 / ρ) ≠ 0)

/-- **`ρ`-variation seminorm of a sequence over an index window `[lo, hi]`**: the supremum of the
`ℓ^ρ`-lengths of the increments of `a` along increasing chains with values in `[lo, hi]`.  For
`ρ = 2` this is `varTwo`. -/
def varRho (ρ : ℝ) (lo hi : ℕ) (a : ℕ → E) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (t : ℕ → ℕ) (_ : Monotone t) (_ : ∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi),
    ENNReal.ofReal (chainLp ρ J a t)

/-- **`ρ`-oscillation seminorm of a sequence over an index window** (KMSZ (5.6)): the supremum,
over increasing block boundaries `o 0 = lo < … < o J = hi`, of the `ℓ^ρ`-length of the blockwise
oscillation `sup_{n ∈ [o_j, o_{j+1})} ‖a n − a (o_j)‖`. -/
def varOsc (ρ : ℝ) (lo hi : ℕ) (a : ℕ → E) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (o : ℕ → ℕ) (_ : o 0 = lo) (_ : o J = hi) (_ : Monotone o),
    (∑ j ∈ Finset.range J,
        (⨆ n ∈ Finset.Ico (o j) (o (j + 1)), ‖a n - a (o j)‖ₑ) ^ ρ) ^ (1 / ρ)

/-- The **selection form** of the `ρ`-oscillation: instead of a `sup` inside each block one chooses
one index `n j` per block.  In `ℝ≥0∞` this is the *same* object as `varOsc` — a finite sum of
suprema is the supremum of the sums over independent selections — but the selection form is the one
for which the pointwise domination by the `ρ`-variation is an elementary gluing of chains. -/
def varOscSel (ρ : ℝ) (lo hi : ℕ) (a : ℕ → E) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (o : ℕ → ℕ) (n : ℕ → ℕ) (_ : o 0 = lo) (_ : o J = hi) (_ : Monotone o)
    (_ : ∀ j < J, n j ∈ Finset.Ico (o j) (o (j + 1))),
    ENNReal.ofReal ((∑ j ∈ Finset.range J, ‖a (n j) - a (o j)‖ ^ ρ) ^ (1 / ρ))

/-- **`ρ`-jump seminorm of a sequence over an index window** (KMSZ (5.8), in the equivalent
supremal form): the supremum, over `λ > 0` and over chains of `[lo, hi]` all of whose increments
have `enorm` at least `λ`, of `λ · (number of increments)^{1/ρ}`.  This is the third of the three
objects of KMSZ Proposition 5.10; it is *dominated by* both the `ρ`-variation and the
`ρ`-oscillation (`varJump_le_varRho`; conversely KMSZ remark (4) records that a bound for the jump
count of a family implies its variational bound, so as a seminorm the jump count is the strongest
of the three). -/
def varJump (ρ : ℝ) (lo hi : ℕ) (a : ℕ → E) : ℝ≥0∞ :=
  ⨆ (lam : ℝ) (_ : 0 < lam) (J : ℕ) (t : ℕ → ℕ) (_ : Monotone t)
    (_ : ∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi)
    (_ : ∀ j < J, ENNReal.ofReal lam ≤ ‖a (t (j + 1)) - a (t j)‖ₑ),
    ENNReal.ofReal lam * (J : ℝ≥0∞) ^ (1 / ρ)

/-- **Translation invariance of the chain `ℓ^ρ`-length**: shifting the window by `lo` and the chain
by `-lo` does not change `chainLp`. -/
lemma chainLp_shift (ρ : ℝ) (J lo : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (ht : Monotone t)
    (hlo : lo ≤ t 0) :
    chainLp ρ J a t = chainLp ρ J (fun r => a (lo + r)) (fun j => t j - lo) := by
  unfold chainLp
  refine congrArg (fun y : ℝ => y ^ (1 / ρ)) (Finset.sum_congr rfl fun j hj => ?_)
  have hjJ : j + 1 ≤ J := by simpa using Finset.mem_range.mp hj
  have h0 : lo ≤ t j := le_trans hlo (ht (Nat.zero_le j))
  have h1 : lo ≤ t (j + 1) := le_trans h0 (ht (by omega))
  have e1 : lo + (t (j + 1) - lo) = t (j + 1) := by omega
  have e2 : lo + (t j - lo) = t j := by omega
  simp only [e1, e2]

end

end Work.BourgainPlan.Maximal
