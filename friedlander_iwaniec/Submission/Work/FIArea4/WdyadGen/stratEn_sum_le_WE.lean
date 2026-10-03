import Mathlib
import Submission.Work.FIArea4.WdyadGen.Wdyad_strata_defs
import Submission.Work.FIArea4.WdyadGen.TZbox_stratum

/-!
# Disjointness of the `gcd`-strata energies (`stratEn_sum_le_WE`)

The `gcd = e` strata `gamE γ e` of a coefficient matrix `γ` have pairwise disjoint supports,
because a reduced pair `(a', d')` (`(a',d') = 1`) with `e ≥ 1` determines the pair
`(e a', e d')` and conversely `e = gcd (e a') (e d')`.  Consequently the summed stratum energies

`∑_{e ∈ (0, 2D]} stratEn D e γ = ∑_{e} ∑_{D/e < d' ≤ 2D/e} ∑_{a' < d', (a',d')=1} ‖γ (e a') (e d')‖²`

exhaust each pair `(a,d)` of the modulus window `D < d ≤ 2D` exactly once, so that the total
stratum energy never exceeds the full energy `WE D γ = ∑_{D<d≤2D} ∑_{a<d} ‖γ a d‖²`.

This is the "strata energies are disjoint" bookkeeping step `(i)` of the stratification of the
dyadic dual variance `Wdyad` (see `Wdyad_RgtS_NOTES.md`).
-/

namespace Work.FIArea4.WdyadGen

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The contribution `∑_{a < d} [(a,d) = e] ‖γ a d‖²` of a single modulus `d` to the energy of
the `e`-th stratum: it is the part of the row energy `rowE γ d` carried by the pairs of gcd `e`. -/
private def stratRow (e : ℕ) (γ : ℕ → ℕ → ℂ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.range d, if Nat.gcd a d = e then Complex.normSq (γ a d) else 0

theorem stratEn_sum_le_WE (D : ℕ) (γ : ℕ → ℕ → ℂ) :
    ∑ e ∈ Finset.Ioc 0 (2 * D), Work.FIArea4.WdyadGen.stratEn D e γ
      ≤ Work.FIArea4.WE D γ := by
  -- **Step 1.**  For a single stratum `e ≥ 1`, `stratEn D e γ` is bounded by the sum of the
  -- `gcd = e` parts of the row energies over the whole modulus window `(D, 2D]`.
  have hA : ∀ e ∈ Finset.Ioc 0 (2 * D),
      stratEn D e γ ≤ ∑ d ∈ Finset.Ioc D (2 * D), stratRow e γ d := by
    intro e he
    have he1 : 1 ≤ e := by rw [Finset.mem_Ioc] at he; omega
    -- the change of variable `a' ↦ e·a'` exhibited by `sum_stratum`.
    have h1 : stratEn D e γ = ∑ d' ∈ Finset.Ioc (D / e) (2 * D / e), stratRow e γ (e * d') := by
      simp only [stratEn]
      apply Finset.sum_congr rfl
      intro d' _
      rw [show stratRow e γ (e * d')
            = ∑ a ∈ Finset.range (e * d'),
                (if Nat.gcd a (e * d') = e then Complex.normSq (γ a (e * d')) else 0)
          from rfl]
      rw [sum_stratum he1 (fun a => Complex.normSq (γ a (e * d')))]
      apply Finset.sum_congr rfl
      intro a' _
      by_cases hc : Nat.Coprime a' d'
      · rw [Work.FIArea4.gamE, if_pos hc, if_pos hc]
      · rw [Work.FIArea4.gamE, if_neg hc, if_neg hc]; simp
    rw [h1]
    calc ∑ d' ∈ Finset.Ioc (D / e) (2 * D / e), stratRow e γ (e * d')
        = ∑ d ∈ (Finset.Ioc D (2 * D)).filter (fun d => e ∣ d), stratRow e γ d := by
          rw [← sum_Ioc_div (e := e) (D := D) he1 (fun d' => stratRow e γ (e * d'))]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_filter] at hd
          rw [Nat.mul_div_cancel' hd.2]
      _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), stratRow e γ d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro d _ _
          rw [stratRow]
          apply Finset.sum_nonneg
          intro a _
          split
          · exact Complex.normSq_nonneg _
          · exact le_refl 0
  -- **Step 2.**  Sum over the strata and swap the orders of summation: for fixed `(a,d)` the
  -- condition `gcd a d = e` singles out the single value `e = gcd a d`.
  calc ∑ e ∈ Finset.Ioc 0 (2 * D), stratEn D e γ
      ≤ ∑ e ∈ Finset.Ioc 0 (2 * D), ∑ d ∈ Finset.Ioc D (2 * D), stratRow e γ d :=
        Finset.sum_le_sum hA
    _ = ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d) := by
        simp only [stratRow]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        have hd1 : 0 < d := by have := (Finset.mem_Ioc.mp hd).1; omega
        have hdle : d ≤ 2 * D := (Finset.mem_Ioc.mp hd).2
        have hmem : Nat.gcd a d ∈ Finset.Ioc 0 (2 * D) := by
          rw [Finset.mem_Ioc]
          exact ⟨Nat.gcd_pos_of_pos_right a hd1, le_trans (Nat.gcd_le_right a hd1) hdle⟩
        rw [Finset.sum_ite_eq, if_pos hmem]
    _ = Work.FIArea4.WE D γ := by rw [Work.FIArea4.WE]

end

end Work.FIArea4.WdyadGen
