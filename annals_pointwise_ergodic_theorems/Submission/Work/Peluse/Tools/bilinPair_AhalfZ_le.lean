import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Analysis.InverseTheory.AhalfZAPI

namespace Work.Peluse.Tools

open scoped BigOperators

set_option linter.unusedVariables false

/-- Crude bound for the trilinear form `⟨Ã_N(f,g), h⟩`: if `f, g, h` are supported in `[-N₀,N₀]`
and bounded by `1` pointwise, then the pairing is bounded by the number of points of the support,
`2 N₀ + 1`.  No cancellation is used: the estimate is
`‖⟨Ã_N(f,g),h⟩‖ ≤ ∑_{|x| ≤ N₀} ‖Ã_N(f,g)(x)‖ ‖h x‖ ≤ (2N₀+1) · 1 · 1`. -/
theorem bilinPair_AhalfZ_le {N₀ N : ℕ} (hN : 0 < N) (P : Polynomial ℤ) (f g h : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn h N₀) (hs1 : Work.Peluse.SupportIn f N₀)
    (hs2 : Work.Peluse.SupportIn g N₀)
    (hb0 : ∀ x : ℤ, ‖h x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f x‖ ≤ 1) (hb2 : ∀ x : ℤ, ‖g x‖ ≤ 1) :
    ‖Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfZ N P f g) h‖
      ≤ 2 * (N₀ : ℝ) + 1 := by
  have _hN := hN
  -- Pointwise bound on the halved average.
  have hA : ∀ x : ℤ, ‖Work.Analysis.InverseTheory.AhalfZ N P f g x‖ ≤ 1 := by
    intro x
    have h := Work.Analysis.InverseTheory.norm_AhalfZ_le N P f g (Mf := 1) (Mg := 1)
      (by norm_num) (by norm_num) hb1 hb2 x
    simpa using h
  set S : Finset ℤ := Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) with hS
  -- The pairing only sees the support of `h`.
  have hzero : ∀ x : ℤ, x ∉ S → Work.Analysis.InverseTheory.AhalfZ N P f g x * h x = 0 := by
    intro x hx
    have hhx : h x = 0 := by
      by_contra hne
      exact hx (Work.Analysis.InverseTheory.SupportIn.mem_Icc hs0 hne)
    rw [hhx, mul_zero]
  rw [Work.Analysis.InverseTheory.bilinPair, tsum_eq_sum (s := S) hzero]
  calc ‖∑ x ∈ S, Work.Analysis.InverseTheory.AhalfZ N P f g x * h x‖
      ≤ ∑ x ∈ S, ‖Work.Analysis.InverseTheory.AhalfZ N P f g x * h x‖ :=
        norm_sum_le S _
    _ ≤ ∑ x ∈ S, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul]
        calc ‖Work.Analysis.InverseTheory.AhalfZ N P f g x‖ * ‖h x‖ ≤ 1 * 1 :=
              mul_le_mul (hA x) (hb0 x) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = 2 * (N₀ : ℝ) + 1 := by
        rw [hS, Int.card_Icc]
        have h1 : ((N₀ : ℤ) + 1 - -(N₀ : ℤ)).toNat = 2 * N₀ + 1 := by omega
        rw [h1]
        push_cast
        ring

end Work.Peluse.Tools
