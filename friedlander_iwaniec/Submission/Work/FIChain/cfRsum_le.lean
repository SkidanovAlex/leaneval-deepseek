import Mathlib
import Submission.Work.FIChain.s3RemPlus_cutfree_defs
import Submission.Work.FIChain.remainder_all_at_07
import Submission.Work.FIChain.Ad_atilc_split_real

namespace Work.FIChain

open Finset

/-- `Ad ã(d,X) = 0` for a non-squarefree modulus `d`: every `n` counted by the congruence sum
satisfies `d ∣ n`, hence is itself non-squarefree (a divisor of a squarefree number is squarefree,
so the contrapositive applies), so that `ã n = μ(n)²·a n = 0`. -/
lemma Ad_atilc_eq_zero_of_not_squarefree (d : ℕ) (X : ℝ) (h : ¬ Squarefree d) :
    Submission.ASP.Ad atilc d X = 0 := by
  rw [Submission.ASP.Ad]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  obtain ⟨_, hdn⟩ := hn
  have hnsq : ¬ Squarefree n := fun hsq => h (hsq.squarefree_of_dvd hdn)
  simp [atilc, Work.FITop.atilFIa, Submission.ASP.atil,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]

/-- The honest remainder of the `λ⁺`-half vanishes at non-squarefree moduli. -/
lemma cfR_eq_zero_of_not_squarefree {d m : ℕ} (h : ¬ Squarefree d) :
    cfR d m = 0 := by
  have hsplit := Ad_atilc_split_real d (m : ℝ)
  rw [Nat.floor_natCast] at hsplit
  have hAd : Submission.ASP.Ad atilc d (m : ℝ) = 0 :=
    Ad_atilc_eq_zero_of_not_squarefree d (m : ℝ) h
  have hg : Submission.ASP.FIgtil d = 0 := Submission.ASP.FIgtil_eq_zero h
  rw [hAd, hg, zero_mul, zero_add] at hsplit
  exact hsplit.symm

/-- The `(R′)`-weighted sum of the honest remainders over `ζ ≤ N` is bounded by `Ã(x)(log x)^{-3}`
as soon as `N ≤ ⌈x^{7/10}⌉` and `m ≤ x`: `Submission.Work.FIChain.remainder_all_at_07` gives the
bound for `RemainderSum r̃ ⌈x^{7/10}⌉₊ m` (a sum over the *squarefree* `ζ ≤ ⌈x^{7/10}⌉₊`), and the
non-squarefree `ζ ≤ N` contribute `0` (prove this internally from `Work.FIChain.Ad_atilc_split_real`
and `Submission.ASP.FIgtil_eq_zero`: `r̃(d,m) = Ad ã(d,m) − g̃(d)·Ã(m)` and both terms vanish for
non-squarefree `d`), so the given sum over all `ζ ∈ Icc 1 N` is at most the `RemainderSum` (the
terms are nonnegative, and `Icc 1 N ⊆ Icc 1 ⌈x^{7/10}⌉₊`). -/
theorem cfRsum_le :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ N m : ℕ,
      N ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ → m ≤ x →
      ∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 * |Work.FIChain.cfR ζ m|
        ≤ Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
  obtain ⟨X₀, hX⟩ := remainder_all_at_07
  refine ⟨X₀, fun x hx N m hN hm => ?_⟩
  have hsub : (Finset.Icc 1 N).filter Squarefree
      ⊆ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree := by
    intro ζ hζ
    rw [Finset.mem_filter] at hζ ⊢
    exact ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hζ.1).1, le_trans (Finset.mem_Icc.mp hζ.1).2 hN⟩, hζ.2⟩
  calc ∑ ζ ∈ Finset.Icc 1 N, ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ m|
      = ∑ ζ ∈ (Finset.Icc 1 N).filter Squarefree,
          ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ m| := by
        rw [eq_comm]
        refine Finset.sum_subset (Finset.filter_subset _ _) (fun ζ hζ hnot => ?_)
        have hnsq : ¬ Squarefree ζ := fun hs => hnot (Finset.mem_filter.mpr ⟨hζ, hs⟩)
        rw [cfR_eq_zero_of_not_squarefree hnsq, abs_zero, mul_zero]
    _ ≤ ∑ ζ ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
          ((ζ.divisors.card : ℝ)) ^ 5 * |cfR ζ m| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun ζ _ _ => mul_nonneg (by positivity) (abs_nonneg _))
    _ = Submission.ASP.RemainderSum (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
          Submission.ASP.FIgtil Submission.ASP.FIa) (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) m := by
        rfl
    _ ≤ Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := hX x hx m hm

end Work.FIChain
