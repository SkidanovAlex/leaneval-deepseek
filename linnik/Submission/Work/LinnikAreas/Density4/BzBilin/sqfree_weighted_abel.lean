import Mathlib
import Submission.Work.LinnikAreas.Density4.abel_sum_Icc
import Submission.Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le
import Submission.Work.LinnikAreas.Density4.BzBilin.abel_weighted_difference_bound_range

namespace Work.LinnikAreas.Density4.BzBilin

/-!
# Partial summation against the squarefree-coprime counting function

The weight `w m = μ²(m)·[m ⟂ c]` is realised as `if Nat.Coprime m c then μ(m)² else 0`, so that
sums over `(Finset.Icc 1 X).filter (Nat.Coprime · c)` become sums of `w` via `Finset.sum_filter`.

Two Abel identities (`abel_sum_Icc`) are applied to the weight `w` and to the constant weight `1`;
subtracting `A` times the second from the first expresses the difference of the two weighted sums
as the Abel sum of the *difference sequence* `Δ m = ∑_{k ≤ m} w k − A·m`, which is then bounded
by `abel_weighted_difference_bound_range`.
-/

open Finset

/-- The weight `m ↦ μ²(m)·[m ⟂ c]` as an explicit function. -/
private def sqfreeWeight (c : ℕ) (m : ℕ) : ℝ :=
  if Nat.Coprime m c then (ArithmeticFunction.moebius m : ℝ) ^ 2 else 0

private lemma sqfreeWeight_sum_eq (c X : ℕ) :
    (∑ k ∈ Finset.Icc 1 X, sqfreeWeight c k)
      = ∑ k ∈ (Finset.Icc 1 X).filter (fun k => Nat.Coprime k c),
          (ArithmeticFunction.moebius k : ℝ) ^ 2 := by
  rw [Finset.sum_filter]
  rfl

private lemma sqfreeWeight_mul_sum_eq (c M : ℕ) (h : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, sqfreeWeight c k * h k)
      = ∑ k ∈ (Finset.Icc 1 M).filter (fun k => Nat.Coprime k c),
          (ArithmeticFunction.moebius k : ℝ) ^ 2 * h k := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : Nat.Coprime k c <;> simp [sqfreeWeight, hk]

/-- **Two-weight Abel identity.**  Applying summation by parts (`abel_sum_Icc`) to the weight `h`
against both the weight `w` and the constant weight `1`, and subtracting `A` times the second
identity from the first, expresses the difference of the two weighted sums through the difference
sequence `m ↦ ∑_{k ≤ m} w k − A·m`. -/
theorem abel_two_weights (w h : ℕ → ℝ) (A : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, w m * h m) - A * (∑ m ∈ Finset.Icc 1 M, h m)
      = ((∑ m ∈ Finset.Icc 1 M, w m) - A * (M : ℝ)) * h M
        + ∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) *
            ((∑ k ∈ Finset.Icc 1 m, w k) - A * (m : ℝ)) := by
  have h1 := Work.LinnikAreas.Density4.abel_sum_Icc w h M
  have h2raw := Work.LinnikAreas.Density4.abel_sum_Icc (fun _ : ℕ => (1:ℝ)) h M
  -- `h2raw` for the constant weight, with `∑_{k ≤ m} 1 = m` and `∑_{m ≤ M} 1 = M`.
  have h2 : (∑ m ∈ Finset.Icc 1 M, h m)
      = (M:ℝ) * h M + ∑ m ∈ Finset.Icc 1 (M - 1), (m:ℝ) * (h m - h (m + 1)) := by
    simp only [one_mul] at h2raw
    rw [h2raw]
    congr 1
    · simp
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [show (∑ k ∈ Finset.Icc 1 m, (1:ℝ)) = (m:ℝ) by simp]
  -- The Abel sum of the difference sequence, in split form.
  have hS : (∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) *
              ((∑ k ∈ Finset.Icc 1 m, w k) - A * (m : ℝ)))
      = (∑ m ∈ Finset.Icc 1 (M - 1), (∑ k ∈ Finset.Icc 1 m, w k) * (h m - h (m + 1)))
        - A * (∑ m ∈ Finset.Icc 1 (M - 1), (m : ℝ) * (h m - h (m + 1))) := by
    rw [show (∑ m ∈ Finset.Icc 1 (M - 1), (h m - h (m + 1)) *
                ((∑ k ∈ Finset.Icc 1 m, w k) - A * (m : ℝ)))
        = ∑ m ∈ Finset.Icc 1 (M - 1),
            ((∑ k ∈ Finset.Icc 1 m, w k) * (h m - h (m + 1))
              - A * ((m : ℝ) * (h m - h (m + 1)))) from
          Finset.sum_congr rfl (fun m _ => by ring)]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [h1, h2, hS]
  ring

/-- Partial summation against the squarefree-coprime counting function, with the difference
bound imposed only in the range `m < M` (outside it `h` may be anything).  Proof: with
`C X = Σ_{m ≤ X, (m,c)=1} μ²(m)` and `Δ X = C X - A·X`, the two Abel identities
`Σ_{m ≤ M, (m,c)=1} μ²(m) h m = C M · h M + Σ_{m < M} C m (h m - h (m+1))` and
`Σ_{m ≤ M} h m = M · h M + Σ_{m < M} m (h (m+1) - h m)`
give `|...| = |Δ M · h M + Σ_{m<M} Δ m (h m - h (m+1))| ≤ ED√M·H + ED·L·Σ_{m<M} m^{-1/2}`,
and `Σ_{m<M} m^{-1/2} ≤ 2√M`.  (`Commons.Analysis.Abel.summation_by_parts` is proved and is a
convenient starting point; do not use `Work.BzHard.sum_squarefree_coprime_weighted`, which is a
`sorry`-carrier.) -/
theorem sqfree_weighted_abel (c M : ℕ) (A E D H L : ℝ) (h : ℕ → ℝ)
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hF : ∀ X : ℕ, |(∑ m ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m c),
          (ArithmeticFunction.moebius m : ℝ) ^ 2) - A * (X : ℝ)| ≤ E * D * Real.sqrt (X : ℝ))
    (hh : ∀ m : ℕ, m ∈ Finset.Icc 1 M → |h m| ≤ H)
    (hd : ∀ m : ℕ, 1 ≤ m → m < M → |h (m + 1) - h m| ≤ L / (m : ℝ)) :
    |(∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m c),
        (ArithmeticFunction.moebius m : ℝ) ^ 2 * h m) - A * (∑ m ∈ Finset.Icc 1 M, h m)|
      ≤ E * D * (H + 2 * L) * Real.sqrt (M : ℝ) := by
  have hkey := abel_two_weights (sqfreeWeight c) h A M
  rw [← sqfreeWeight_mul_sum_eq c M h, hkey]
  refine abel_weighted_difference_bound_range
    (fun m => (∑ k ∈ Finset.Icc 1 m, sqfreeWeight c k) - A * (m : ℝ))
    h M (E * D) H L (mul_nonneg hE hD) hH hL ?_ hh hd
  intro m
  rw [sqfreeWeight_sum_eq c m]
  exact hF m

end Work.LinnikAreas.Density4.BzBilin
