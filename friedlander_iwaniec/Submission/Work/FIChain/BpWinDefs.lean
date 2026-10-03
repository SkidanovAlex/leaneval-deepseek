/-
# `Submission.Work.FIChain.BpWinDefs` — vocabulary for the `Π`-removal of the `(B′)`-window

The chain consumes the `Π`-restricted Proposition 4.1 (`Work.FITop4.Prop41StatementPiBig`, i.e.
`BformPi` with the condition `(n, Π) = 1` of the companion paper's (10.1)), while the window
hypotheses of the consumers (`BprimeWindow`/`BprimeWindowInt`) involve the `Π`-free inner sums
`Xsum atilc x m t (2t)`.  The passage from the restricted to the unrestricted form is the
companion's §10 (Theorem 3): the inner variable is written `n = n₀n₁` with `n₁ | Π` and
`(n₀, Π) = 1`, the `n₁ ≤ Δπ` part is absorbed by the change of variables `w ↦ w·n₁` in the
`w`-integral (which turns the `n₁`-sum into a `τ`-weight, at the cost of halving the saving
exponent `(log x)^{-2^26} → (log x)^{-2^25}`), and the `n₁ > Δπ` part is estimated by Rankin's
trick, using that every `n₁ > Δπ` has a divisor `d | Π` with `Δπ < d ≤ Δπ·Pz`.

This file contains *definitions only* (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FITop4.Red5.Vocab

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The small-prime product `Π = ∏_{p ≤ Pz} p` -/

/-- `Π(Pz) = ∏_{p ≤ Pz} p` (Mathlib's `primorial`). -/
abbrev ProdP (Pz : ℕ) : ℕ := primorial Pz

lemma ProdP_eq_prod (Pz : ℕ) : ProdP Pz = ∏ p ∈ Nat.primesLE Pz, p :=
  primorial_eq_prod_primesLE Pz

lemma ProdP_squarefree (Pz : ℕ) : Squarefree (ProdP Pz) := squarefree_primorial Pz

lemma ProdP_pos (Pz : ℕ) : 0 < ProdP Pz := Nat.pos_of_ne_zero (ProdP_squarefree Pz).ne_zero

/-! ## 2. The `Π`-restricted and the `Π`-free inner window sums -/

/-- The `Π`-restricted inner window sum: `Σ_{u < n ≤ 2u, cn ≤ x, (n,Π)=1} μ(n)ã(cn)`.

(`Xsum atilc x c u (2u)` is the same sum without the restriction `(n, Π) = 1`.) -/
def Xf (x Pz c : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 x).filter
      (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u ∧
        Work.FITop4.PiCond Pz n),
    (ArithmeticFunction.moebius n : ℝ) * atilc (c * n)

lemma abs_Xf_le_sum (x Pz c : ℕ) (u : ℝ) :
    |Xf x Pz c u|
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter
          (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u ∧
            Work.FITop4.PiCond Pz n),
        atilc (c * n) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  have h1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast h
  have h2 : 0 ≤ atilc (c * n) := Work.FITop.atilFIa_nonneg _
  calc |(ArithmeticFunction.moebius n : ℝ) * atilc (c * n)|
      = |(ArithmeticFunction.moebius n : ℝ)| * |atilc (c * n)| := abs_mul _ _
    _ ≤ 1 * |atilc (c * n)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = atilc (c * n) := by rw [one_mul, abs_of_nonneg h2]

/-- `|Xsum atilc x c u (2u)|` is dominated by the (unsigned) mass of the same window. -/
lemma Xsum_window_le_sum (x c : ℕ) (u : ℝ) :
    |Submission.ASP.Xsum atilc x c u (2 * u)|
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter
          (fun n => n * c ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
        atilc (n * c) := by
  rw [Submission.ASP.Xsum]
  have hset : (Finset.Icc 1 x).filter
        (fun b => u < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ 2 * u ∧ b * c ≤ x)
      = (Finset.Icc 1 x).filter
        (fun b => b * c ≤ x ∧ u < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ 2 * u) := by
    refine Finset.filter_congr (fun b _ => ?_)
    tauto
  rw [hset]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  have h1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast h
  have h2 : 0 ≤ atilc (n * c) := Work.FITop.atilFIa_nonneg _
  calc |(ArithmeticFunction.moebius n : ℝ) * atilc (n * c)|
      = |(ArithmeticFunction.moebius n : ℝ)| * |atilc (n * c)| := abs_mul _ _
    _ ≤ 1 * |atilc (n * c)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = atilc (n * c) := by rw [one_mul, abs_of_nonneg h2]

/-- `Xf` vanishes when the window `(u, 2u]` contains no integer `≥ 1`. -/
lemma Xf_eq_zero_of_le (x Pz c : ℕ) {u : ℝ} (hu : 2 * u < 1) : Xf x Pz c u = 0 := by
  rw [Xf]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  exfalso
  obtain ⟨hnI, -, -, hle, -⟩ := hn
  have h1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hnI).1
  linarith

/-! ## 3. The tail threshold `Δπ` -/

/-- `Δπ = ⌈exp(κ (log log x)^3)⌉ : the threshold of the `n₁`-split of the companion's §10
(`n₁ ≤ Δπ` is absorbed by the smoothing, `n₁ > Δπ` by Rankin's trick). -/
def Dpi (x : ℕ) (κ : ℝ) : ℕ := ⌈Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3)⌉₊

/-! ## 4. The aggregated pointwise quantities of the two Hölder factors -/

/-- The unweighted `Π`-restricted window sum `Σ_{c ≤ x} |Xf c u|`. -/
def Aw (x Pz : ℕ) (u : ℝ) : ℝ := ∑ c ∈ Finset.Icc 1 x, |Xf x Pz c u|

/-- The `τ⁶`-weighted `Π`-restricted window sum `Σ_{c ≤ x} τ(c)⁶ |Xf c u|`. -/
def Bw (x Pz : ℕ) (u : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 * |Xf x Pz c u|

lemma Aw_nonneg (x Pz : ℕ) (u : ℝ) : 0 ≤ Aw x Pz u :=
  Finset.sum_nonneg (fun c _ => abs_nonneg _)

lemma Bw_nonneg (x Pz : ℕ) (u : ℝ) : 0 ≤ Bw x Pz u :=
  Finset.sum_nonneg (fun c _ => by positivity)

end

end Work.FIChain
