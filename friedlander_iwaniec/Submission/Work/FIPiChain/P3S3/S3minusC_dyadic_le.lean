/-
# `S3minusC_dyadic_le` — §8 (8.1) in *dyadic* form

The chapter's `S₃⁻` estimate, with the `ρ`-window hypothesis of `Work.FIChain.abs_S3minusC_le`
replaced by the dyadic sum `∑_{j<J} Grho x C (2^j z)`.  Recall

`Grho N C t = ∫_{1}^{C} (Σ_{m ≤ N} wc m · |XrhoC atilc N m s t (2t)|) / s  ds`

is exactly the `s`-integral of the per-window weight sum on the window `(t,2t]`, so the RHS is the
`t`-sum over the dyadic decomposition `(z, 2^J z] = ⋃_{j<J} (2^j z, 2^{j+1} z]` of the very quantity
that `abs_S3minusC_le` bounds by a constant `J·E·log C` under its `RhoWindowC` hypothesis.

The proof is two independent estimates, each delegated and proved separately:

* `S3minusC_integral_le` — the `ℓ`-sum reduction of `abs_S3minusC_le` (steps 1–3): the
  `μ(c)·λ⁻(c)` inner `c`-sum is written as an integral of `XrhoC`, giving

  `|S₃⁻| ≤ ∫_1^C (Σ_ℓ wc ℓ·|XrhoC atilc x ℓ s z (sc x B * z)|)/s`;

* `dyadic_XrhoC_integral_le` — the dyadic splitting of the window `(z, 2^J z]` and the swap of the
  `j`-sum with the `s`-integral, giving

  `∫_1^C (Σ_ℓ wc ℓ·|XrhoC atilc x ℓ s z (2^J z)|)/s ≤ Σ_{j<J} Grho x C (2^j z)`.

The `ℓ`-weight hypothesis `hw` of the first estimate is supplied here from
`|Σ_{b ∣ ℓ, sy < b} μ b| ≤ τ(ℓ)` and `|ρ_ℓ| ≤ τ(ℓ)` (which is where `|λ| ≤ 1` enters), i.e. from
`wc ℓ = τ(ℓ)²`.  No `sorry`, no `axiom`.
-/
import Mathlib
import Submission.Work.FIPiChain.Defs
import Submission.Work.FIChain.abs_S3minusC_le
import Submission.Work.FIPiChain.P3S3.S3minusC_integral_le
import Submission.Work.FIPiChain.P3S3.dyadic_XrhoC_integral_le

namespace Work.FIPiChain.P3S3

open Finset MeasureTheory
open scoped Interval BigOperators

theorem S3minusC_dyadic_le (x : ℕ) (B : ℝ) (lam : ℕ → ℝ) (z sy C : ℝ)
    (hC : 1 ≤ C) (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) (hz : 0 < z) :
    |Work.FIChain.S3minusC Work.FIChain.atilc lam x z sy (Work.FIChain.sc x B * z) C|
      ≤ ∑ j ∈ Finset.range (Work.FIChain.Jc x B),
          Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z) := by
  -- `sc x B = 2^{Jc x B}`: unfold the dyadic scale once and for all
  rw [Work.FIChain.sc]
  -- the `ℓ`-weight bound `|Σ_{b|ℓ,sy<b} μ b|·|ρ_ℓ| ≤ wc ℓ = τ(ℓ)²`
  have hw0 : ∀ ℓ : ℕ, 0 ≤ Work.FIChain.wc ℓ := fun ℓ => by
    rw [Work.FIChain.wc, Work.FITop.w0]; positivity
  have hw : ∀ ℓ : ℕ, 1 ≤ ℓ →
      |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)| * |Submission.ASP.rhoOf lam ℓ| ≤ Work.FIChain.wc ℓ := by
    intro ℓ _
    have hcard : (0 : ℝ) ≤ (ℓ.divisors.card : ℝ) := Nat.cast_nonneg _
    have h1 : |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)| ≤ (ℓ.divisors.card : ℝ) := by
      calc |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
            (ArithmeticFunction.moebius b : ℝ)|
          ≤ ∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              |(ArithmeticFunction.moebius b : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)), (1 : ℝ) :=
            Finset.sum_le_sum (fun b _ => Submission.ASP.abs_moebius_cast_le_one b)
        _ = ((ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ))).card : ℝ) := by simp
        _ ≤ (ℓ.divisors.card : ℝ) := by
            exact_mod_cast Finset.card_le_card
              (Finset.filter_subset (fun b => sy < ((b : ℕ) : ℝ)) ℓ.divisors)
    have h2 : |Submission.ASP.rhoOf lam ℓ| ≤ (ℓ.divisors.card : ℝ) := by
      rw [Submission.ASP.rhoOf]
      calc |∑ ν ∈ ℓ.divisors, lam ν|
          ≤ ∑ ν ∈ ℓ.divisors, |lam ν| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ν ∈ ℓ.divisors, (1 : ℝ) := Finset.sum_le_sum (fun ν _ => hlam ν)
        _ = (ℓ.divisors.card : ℝ) := by simp
    calc |∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)| * |Submission.ASP.rhoOf lam ℓ|
        ≤ (ℓ.divisors.card : ℝ) * (ℓ.divisors.card : ℝ) :=
          mul_le_mul h1 h2 (abs_nonneg _) hcard
      _ = Work.FIChain.wc ℓ := by rw [Work.FIChain.wc, Work.FITop.w0]; ring
  -- step 1: the `ℓ`-sum reduction of §8 (the `μ(c)·λ⁻(c)` `c`-sum as an integral of `XrhoC`)
  refine (S3minusC_integral_le (a := Work.FIChain.atilc) (lam := lam) (w := Work.FIChain.wc)
    (N := x) (z := z) (sy := sy) (sz := (2 : ℝ) ^ (Work.FIChain.Jc x B) * z) (C := C)
    hC (fun n hn => Work.FITop.rwcp_atil_eq_zero hn) hw0 hw).trans ?_
  -- step 2: dyadic splitting of the window `(z, 2^{Jc} z]` and the `j`/`s` swap
  refine (dyadic_XrhoC_integral_le (a := Work.FIChain.atilc) (w := Work.FIChain.wc)
    (N := x) (z := z) (C := C) (J := Work.FIChain.Jc x B) hC hz hw0).trans ?_
  -- step 3: identify each summand with `Grho x C (2^j z)`
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Work.FIPiChain.Grho]
  rw [show (2 : ℝ) * ((2 : ℝ) ^ j * z) = (2 : ℝ) ^ (j + 1) * z by ring]

end Work.FIPiChain.P3S3
