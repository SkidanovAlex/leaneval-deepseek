/-
# The randomised symbol of the small-scale family is a finite sum over the *active* indices

`randSymb (smallSymbF … t) ε K = ∑_{n < K} ε n • (φ_{n+1} - φ_n)` is, by definition, a
*telescoping* linear combination of the bumps `φ_n = 1_{randAct n} · varphiNt ⌊a n⌋ k₁ t`.  Once the
index condition `randAct` fails beyond `Nlim` (`hNlim`), this collapses to a finite linear
combination of the bumps at the active indices with the coefficients `randCoeff` of
`randSymbDefs`, which is the form in which the analysis of the symbol (and hence the Rademacher--
Menshov reduction of §7) uses it.

The content is the elementary summation-by-parts identity

  `∑_{n < K} ε n * (f (n+1) - f n) = ∑_{m ≤ K} (ε (m-1) 1_{m ≤ K} - ε m 1_{m < K}) * f m`

(for `f 0 = 0`), valid for any commutative ring and proved here for `ℂ`; the rest is the harmless
bookkeeping of extending the summation range from `K + 1` to `Nlim + 1` (the extra terms vanish
because either the coefficient or the bump does).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbDefs

open Finset
open scoped BigOperators

namespace Work.KMTAreas.A7

noncomputable section

/-- The coefficient of the summation-by-parts identity: as in `randCoeff`, but *without* the
`randAct` guard, i.e. the coefficient of the bump `varphiNt ⌊a m⌋ k₁ t` in the telescoping sum. -/
private noncomputable def coeffAux (ε : ℕ → ℂ) (K : ℕ) (m : ℕ) : ℂ :=
  ε (m - 1) * (if m ≤ K then 1 else 0) - ε m * (if m < K then 1 else 0)

/-- Reindexing `∑_{m ≤ K} ε (m - 1) f m` by `m = n + 1`; the `m = 0` term is `ε 0 * f 0 = 0`. -/
private theorem sum_range_pred_mul (ε f : ℕ → ℂ) (K : ℕ) (h0 : f 0 = 0) :
    (∑ m ∈ Finset.range (K+1), ε (m-1) * f m) = ∑ n ∈ Finset.range K, ε n * f (n+1) := by
  rw [Finset.sum_range_succ']
  simp [h0]

/-- **Summation by parts** in the form used for `randSymb`: the telescoping combination
`∑_{n < K} ε n * (f (n+1) - f n)` equals the single sum `∑_{m ≤ K} coeffAux ε K m * f m`
(usable only for `f 0 = 0`). -/
private theorem telescope_coeff (ε f : ℕ → ℂ) (K : ℕ) (h0 : f 0 = 0) :
    (∑ n ∈ Finset.range K, ε n * (f (n+1) - f n))
      = ∑ m ∈ Finset.range (K+1), coeffAux ε K m * f m := by
  have hL : (∑ n ∈ Finset.range K, ε n * (f (n+1) - f n))
      = (∑ n ∈ Finset.range K, ε n * f (n+1)) - ∑ n ∈ Finset.range K, ε n * f n := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hR : (∑ m ∈ Finset.range (K+1), coeffAux ε K m * f m)
      = (∑ n ∈ Finset.range K, ε n * f (n+1)) - ∑ n ∈ Finset.range K, ε n * f n := by
    have h1 : (∑ m ∈ Finset.range (K+1), coeffAux ε K m * f m)
        = (∑ m ∈ Finset.range (K+1), ε (m-1) * f m)
          - ∑ m ∈ Finset.range (K+1), ε m * (if m < K then 1 else 0) * f m := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      have hmK : m ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      unfold coeffAux
      simp only [hmK, if_true]
      ring
    have h2 : (∑ m ∈ Finset.range (K+1), ε m * (if m < K then (1:ℂ) else 0) * f m)
        = ∑ m ∈ Finset.range K, ε m * f m := by
      rw [Finset.sum_range_succ]
      simp only [lt_irrefl, if_false, mul_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have : m < K := Finset.mem_range.mp hm
      simp only [this, if_true, mul_one]
    have h3 : (∑ n ∈ Finset.range K, ε n * f (n+1))
        = ∑ m ∈ Finset.range (K+1), ε (m-1) * f m :=
      (sum_range_pred_mul ε f K h0).symm
    rw [h1, h2, h3]
  rw [hL, hR]

theorem randSymb_eq_activeSum (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (ε : ℕ → ℂ) (K Nlim : ℕ)
    (hNlim : ∀ m, Work.KMTAreas.A7.randAct ρ C₀ a l₁ l₂ k₁ k₂ m → m ≤ Nlim) :
    Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K
      = fun ξ => ∑ m ∈ (Finset.range (Nlim + 1)).filter (Work.KMTAreas.A7.randAct ρ C₀ a l₁ l₂ k₁ k₂),
          Work.KMTAreas.A7.randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
            * Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k₁ t ξ := by
  funext ξ
  set F : ℕ → ℂ := fun m => if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
      varphiNt (Nat.floor (a m)) k₁ t ξ else 0 with hF
  have hF0 : F 0 = 0 := by simp [hF, randAct]
  have hFbig : ∀ m, Nlim < m → F m = 0 := by
    intro m hm
    have hna : ¬ randAct ρ C₀ a l₁ l₂ k₁ k₂ m := fun h => (not_lt.mpr (hNlim m h)) hm
    simp [hF, hna]
  have hSymb : ∀ m, smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m ξ = F m := by
    intro m
    rw [smallSymbF_apply, ite_apply]
    simp [hF]
  have hLHS : randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K ξ
      = ∑ n ∈ Finset.range K, ε n * (F (n+1) - F n) := by
    unfold randSymb
    apply Finset.sum_congr rfl
    intro n _
    rw [hSymb (n+1), hSymb n]
  have hRHS : (∑ m ∈ (Finset.range (Nlim + 1)).filter (randAct ρ C₀ a l₁ l₂ k₁ k₂),
          randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m * varphiNt (Nat.floor (a m)) k₁ t ξ)
      = ∑ m ∈ Finset.range (Nlim + 1), coeffAux ε K m * F m := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos hm]
      have hcoe : randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m = coeffAux ε K m := by
        rw [randCoeff, if_pos hm]; rfl
      rw [hcoe]
      have hφ : varphiNt (Nat.floor (a m)) k₁ t ξ = F m := by simp [hF, hm]
      rw [hφ]
    · rw [if_neg hm]
      have hFm : F m = 0 := by simp [hF, hm]
      rw [hFm, mul_zero]
  have hcK : ∀ m, K < m → coeffAux ε K m * F m = 0 := by
    intro m hm
    have h1 : ¬ m ≤ K := not_le.mpr hm
    have h2 : ¬ m < K := not_lt.mpr (le_of_lt hm)
    simp [coeffAux, h1, h2]
  have hB : (∑ m ∈ Finset.range (Nlim+1), coeffAux ε K m * F m)
      = ∑ m ∈ Finset.range (K+1), coeffAux ε K m * F m := by
    rcases le_total K Nlim with h | h
    · exact (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ h))
        (fun x _ hxnot => hcK x (by
          have : ¬ x < K + 1 := by simpa [Finset.mem_range] using hxnot
          omega))).symm
    · apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ h))
      intro x _ hxnot
      have hxN : Nlim < x := by
        have : ¬ x < Nlim + 1 := by simpa [Finset.mem_range] using hxnot
        omega
      rw [hFbig x hxN, mul_zero]
  have hC : (∑ m ∈ Finset.range (K+1), coeffAux ε K m * F m)
      = ∑ n ∈ Finset.range K, ε n * (F (n+1) - F n) :=
    (telescope_coeff ε F K hF0).symm
  rw [hLHS, hRHS, hB, hC]

end

end Work.KMTAreas.A7
