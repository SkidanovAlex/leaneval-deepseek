import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstRademacherMenshov

/-!
# The `2`-variation (Rademacher–Menshov) seminorm of a sequence

Kosz–Mirek–Słomian–Zhang, arXiv:2606.12663, §5.2 define the `ρ`-variation seminorm of a sequence
of functions `(f_n : n ∈ I)` by

`V^ρ(f_n : n ∈ I) := sup_{J} sup_{(n_j)_{j≤J} ∈ S^I_J} (Σ_{j<J} ‖f_{n_{j+1}} − f_{n_j}‖^ρ)^{1/ρ}`,

`S^I_J` being the set of **increasing** sequences of `J+1` indices in `I`.  For `ρ ≥ 2` this
seminorm realises, on the frequency side, the `ℓ^ρ`-square function of the *increments* of the
sequence; Theorem 5.2 there (the seminorm refinement of the Ionescu–Wainger multiplier theorem)
applies to it, and §6 uses it to obtain the maximal, oscillation and variation estimates of
Bourgain's ergodic theorem.

This file holds the *vocabulary*:

* `chainSq J a t` — the `ℓ²`-length of the increments of a sequence along a chain of indices `t`;
* `varTwo lo hi a` — the `2`-variation seminorm of `a` over the index window `[lo, hi]`, i.e. the
  supremum of `chainSq` over all increasing chains with values in `[lo, hi]` (in `ℝ≥0∞`, so that the
  supremum over the (infinite) set of chains exists without any completeness hypothesis).

The point of the variation seminorm (as opposed to the maximal function) is that it is
**translation invariant** in the index: this is what makes KMSZ's condition (2)
(`Submission.Work.BourgainPlan.Maximal.mstRademacherMenshov`) applicable with no base term, and it
is why the maximal function of Bourgain's averages is bounded via the variation in the modern route.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The `ℓ²`-length of the increments of `a` along the chain of indices `t`:
`chainSq J a t = (Σ_{j < J} ‖a (t (j+1)) − a (t j)‖²)^{1/2}`.  Only the values `t 0, …, t J`
matter. -/
def chainSq (J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2)

lemma chainSq_nonneg (J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) : 0 ≤ chainSq J a t :=
  Real.sqrt_nonneg _

lemma chainSq_zero (a : ℕ → E) (t : ℕ → ℕ) : chainSq 0 a t = 0 := by
  simp [chainSq]

/-- Squared form (avoids the square root): `chainSq J a t ^ 2 = Σ_{j<J} ‖…‖²`. -/
lemma chainSq_sq (J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) :
    chainSq J a t ^ 2 = ∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => by positivity)

/-- **`2`-variation seminorm of a sequence over an index window.**  The supremum of the `ℓ²`-lengths
of the increments of `a` along increasing chains of indices lying in `[lo, hi]`. -/
def varTwo (lo hi : ℕ) (a : ℕ → E) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (t : ℕ → ℕ) (_ : Monotone t) (_ : ∀ j ≤ J, lo ≤ t j ∧ t j ≤ hi),
    ENNReal.ofReal (chainSq J a t)

/-- **Translation invariance of the chain square function**: shifting the window by `lo` and the
chain by `-lo` does not change `chainSq`. -/
lemma chainSq_shift (J lo : ℕ) (a : ℕ → E) (t : ℕ → ℕ) (ht : Monotone t) (hlo : lo ≤ t 0) :
    chainSq J a t = chainSq J (fun r => a (lo + r)) (fun j => t j - lo) := by
  unfold chainSq
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun j hj => ?_)
  have hjJ : j + 1 ≤ J := by simpa using Finset.mem_range.mp hj
  have h0 : lo ≤ t j := le_trans hlo (ht (Nat.zero_le j))
  have h1 : lo ≤ t (j + 1) := le_trans h0 (ht (by omega))
  have e1 : lo + (t (j + 1) - lo) = t (j + 1) := by omega
  have e2 : lo + (t j - lo) = t j := by omega
  simp only [e1, e2]

end

end Work.BourgainPlan.Maximal
