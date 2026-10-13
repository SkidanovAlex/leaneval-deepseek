import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowGamSlotIntegrable
import Submission.Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowZSliceLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory

/-- **The `γ`-weighted angular half of the level-`m` slice sum, `m ≤ 2`.**

For a datum `f` of the open class lying in `ℋ⁴`, every `m ≤ 2` and every `z > 0`, the angular
slice of the active `(D_z^j D_θ^i f)² · sin(2θ)^{-γ(α)}`-sum (those slots with `1 ≤ i` and
`i + j ≤ m`) is bounded by `27 · HkSq α 4 f`.

Route. The double `Finset.range (m+1)`-sum is a finite sum of `(m+1)² ≤ 9` terms, each of which
is either identically `0` (when `1 ≤ i` or `i + j ≤ m` fails) or the plain slot integrand
`(D_z^j D_θ^i f z ·)² · sin(2·)^{-γ(α)}`; every term is integrable on `Iθ` by
`lowGamSlotIntegrable` (`1 ≤ i`, `i + j ≤ m ≤ 2 ≤ 4`), so `MeasureTheory.integral_finsetSum`
splits the integral over the terms.  Each active slot obeys
`Work.FTS.StrongPersist.H6Row6Gam.mixed_slice_z_le_three` (`i + j ≤ m ≤ 2 ≤ 3`), while the
inactive ones are `≤ 0 ≤ 3 · HkSq α 4 f`.  Summing the resulting `≤ 3 · HkSq α 4 f` bounds over
the `(m+1)² ≤ 9` summands gives `≤ 27 · HkSq α 4 f`. -/
theorem psi6LowMixedHalf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
      ≤ 27 * Work.Spaces.HkSq α 4 f := by
  classical
  have hHk : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  -- Every one of the `(m+1)²` summands of the double sum is integrable on `Iθ`.
  have hterm : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) Work.Spaces.Iθ := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · have hij4 : i + j ≤ 4 := by
        have hi2 : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj2 : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        omega
      simpa only [if_pos hc] using
        (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowGamSlotIntegrable hα hα1 hF hmem
          (j := j) (i := i) hc.1 hij4 hz)
    · simpa only [if_neg hc] using
        (MeasureTheory.integrableOn_zero :
          MeasureTheory.IntegrableOn (fun θ : ℝ => (0 : ℝ)) Work.Spaces.Iθ)
  -- The same statement, indexed by a pair.
  have hIntP : ∀ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) Work.Spaces.Iθ := by
    intro p hp
    exact hterm p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2
  -- Reindex the double sum as a sum over the product of the two ranges.
  have hprod : ∀ θ : ℝ,
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := by
    intro θ
    rw [← Finset.sum_product (f := fun p : ℕ × ℕ => (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then
      (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))]
  -- Push the integral through the (finite, integrable) sum.
  have hsplit : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          ∫ θ in Work.Spaces.Iθ,
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := by
    rw [show (fun θ : ℝ => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        = (fun θ : ℝ => ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) from funext hprod]
    exact MeasureTheory.integral_finsetSum
      (s := (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)))
      (f := fun p : ℕ × ℕ => fun θ : ℝ =>
        (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) hIntP
  -- Each term of the reindexed sum is bounded by `3 · HkSq α 4 f`.
  have hper : ∀ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
      (∫ θ in Work.Spaces.Iθ,
        (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
        ≤ 3 * Work.Spaces.HkSq α 4 f := by
    intro p hp
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ m
    · have h3 : p.1 + p.2 ≤ 3 := by omega
      have h := Work.FTS.StrongPersist.H6Row6Gam.mixed_slice_z_le_three α f hα hα1 hF hmem
        p.2 p.1 hc.1 h3 z hz
      simpa only [if_pos hc] using h
    · have hz0 : (∫ θ in Work.Spaces.Iθ, (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then
            (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          else 0)) = 0 := by
        rw [show (fun θ : ℝ => (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then
            (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          else 0)) = (fun _ : ℝ => (0 : ℝ)) from funext (fun θ => if_neg hc)]
        simp
      rw [hz0]
      linarith
  calc (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          ∫ θ in Work.Spaces.Iθ,
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ m then (Work.Spaces.mixed p.2 p.1 f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := hsplit
    _ ≤ ∑ _p ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)),
          (3 * Work.Spaces.HkSq α 4 f) := Finset.sum_le_sum hper
    _ = ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).card •
          (3 * Work.Spaces.HkSq α 4 f) := Finset.sum_const _
    _ ≤ 27 * Work.Spaces.HkSq α 4 f := by
        rw [Finset.card_product, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
        have h3 : ((m + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : m + 1 ≤ 3)
        have h0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
        have hstep : ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (3 * Work.Spaces.HkSq α 4 f)
            ≤ 9 * (3 * Work.Spaces.HkSq α 4 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith [hHk])
          nlinarith
        linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
