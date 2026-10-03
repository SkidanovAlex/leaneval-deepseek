/-
# The Ionescu--Wainger symbol over `torsFinset Q`, multiplied by a level-`C₀` bump

This is the elementary circle-geometry identity underlying the KMSZ (6.22) decimation
factorisation.  For a `Q`-torsion set `T = torsFinset Q = {a/Q : a < Q}` and a subset
`A ⊆ T`, the narrow level-`L` bump over the *whole* torsion set times the wide level-`C₀`
bump over `A` collapses to the narrow level-`L` bump over `A`:

`iwSymbolSet T (bump L) · iwSymbolSet A (bump C₀) = iwSymbolSet A (bump L)`.

The mechanism is the coarseness condition `3Q < 2 ^ C₀` together with `C₀ + 1 ≤ L`:

* two distinct `Q`-torsion points are `1/Q`-separated, and `3Q < 2^{C₀}` gives
  `1/Q > 3 · 2^{-C₀} > 2^{1-C₀}`, while the closed supports of the two bumps around
  distinct torsion points force `‖α - β‖ ≤ 2^{-L} + 2^{-C₀} ≤ 2^{1-C₀}` — so the two
  bumps around *distinct* torsion points have disjoint (closed) supports and the
  off-diagonal products vanish;
* on the diagonal `α = β` the wide bump equals `1`, because `L ≥ C₀ + 1` and
  `‖ξ - α‖ ≤ 2^{-L}` whenever the narrow bump `bump L (ξ - α)` is nonzero.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Decim.bump_geometry
import Submission.Work.KMTPlan.A6.DecimComp.Defs

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi

/-- The `Q`-torsion `Finset` of `Work.KMTPlan.A6.Decim` is the one of
`Work.KMTPlan.A6.DecimComp` (the two point maps `circPt Q` and `arcPt Q` are the same
function `a ↦ a/Q`). -/
theorem decim_torsFinset_eq_decimComp (Q : ℕ) :
    Work.KMTPlan.A6.Decim.torsFinset Q = Work.KMTPlan.A6.DecimComp.torsFinset Q := rfl

/-- The dyadic bump of `Work.KMTPlan.A6.Decim` is the one of `Work.KMTPlan.A6.DecimComp`. -/
theorem decim_bump_eq_decimComp (L : ℕ) :
    Work.KMTPlan.A6.Decim.bump L = Work.KMTPlan.A6.DecimComp.bump L := rfl

theorem iwSymbolSet_torsFinset_mul_bump (Q C₀ L : ℕ) (hQ : 1 ≤ Q) (hC₀ : 1 ≤ C₀)
    (hnarrow : 3 * Q < 2 ^ C₀) (hL : C₀ + 1 ≤ L)
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (hA : A ⊆ Work.KMTPlan.A6.Decim.torsFinset Q) :
    Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTPlan.A6.Decim.torsFinset Q)
        (Work.KMTPlan.A6.Decim.bump L)
      * Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump C₀)
      = Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L) := by
  have hL1 : 1 ≤ L := by omega
  obtain ⟨hbumpL_supp, -, -⟩ := Work.KMTPlan.A6.Decim.bump_geometry L hL1
  obtain ⟨hbumpC0_supp, -, hbumpC0_one⟩ := Work.KMTPlan.A6.Decim.bump_geometry C₀ hC₀
  -- ## elementary numerics
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have h2C0pos : (0 : ℝ) < (2 : ℝ) ^ C₀ := by positivity
  have h3Q : (3 : ℝ) * (Q : ℝ) < (2 : ℝ) ^ C₀ := by
    have h : ((3 * Q : ℕ) : ℝ) < ((2 ^ C₀ : ℕ) : ℝ) := by exact_mod_cast hnarrow
    push_cast at h
    linarith
  have h3inv : (3 : ℝ) / (2 : ℝ) ^ C₀ < 1 / (Q : ℝ) := by
    rw [div_lt_div_iff₀ h2C0pos hQpos]
    linarith
  have hnegC : (2 : ℝ) ^ (-(C₀ : ℤ)) = ((2 : ℝ) ^ C₀)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hpow_eq : (2 : ℝ) ^ ((1 : ℤ) - (C₀ : ℤ)) = 2 * ((2 : ℝ) ^ C₀)⁻¹ := by
    have h1 : ((1 : ℤ) - (C₀ : ℤ)) = (1 : ℤ) + (-(C₀ : ℤ)) := by ring
    rw [h1, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (1 : ℤ) (-(C₀ : ℤ)), zpow_one,
      zpow_neg, zpow_natCast]
  have hsepNum : (2 : ℝ) ^ ((1 : ℤ) - (C₀ : ℤ)) < (Q : ℝ)⁻¹ := by
    have hA' : (3 : ℝ) * ((2 : ℝ) ^ C₀)⁻¹ < (Q : ℝ)⁻¹ := by
      simpa only [div_eq_mul_inv, one_mul] using h3inv
    rw [hpow_eq]
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ C₀)⁻¹ := by positivity
    linarith
  have hpowLe : (2 : ℝ) ^ (-(L : ℤ)) ≤ ((2 : ℝ) ^ C₀)⁻¹ := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by omega : (-(L : ℤ)) ≤ (-(C₀ : ℤ)))
    rwa [hnegC] at h
  -- ## distinct torsion points are `2^{1-C₀}`-separated
  have hdist : ∀ x ∈ Work.KMTPlan.A6.Decim.torsFinset Q,
      ∀ y ∈ Work.KMTPlan.A6.Decim.torsFinset Q, x ≠ y →
      (2 : ℝ) ^ ((1 : ℤ) - (C₀ : ℤ)) < ‖x - y‖ := by
    intro x hx y hy hxy
    have hx' : x ∈ Work.KMTPlan.A6.DecimComp.torsFinset Q :=
      decim_torsFinset_eq_decimComp Q ▸ hx
    have hy' : y ∈ Work.KMTPlan.A6.DecimComp.torsFinset Q :=
      decim_torsFinset_eq_decimComp Q ▸ hy
    have h1 : (Q : ℝ)⁻¹ ≤ ‖x - y‖ := by
      simpa only [one_div] using
        (Work.KMTPlan.A6.DecimComp.norm_le_of_ne_mem_torsFinset hQ hx' hy' hxy)
    linarith
  -- ## pointwise collapse
  funext ξ
  simp only [Pi.mul_apply, Work.Analysis.IonescuWainger.iwSymbolSet_apply]
  have hzero : ∀ α ∈ Work.KMTPlan.A6.Decim.torsFinset Q, ∀ β ∈ A, α ≠ β →
      Work.KMTPlan.A6.Decim.bump L (ξ - α) * Work.KMTPlan.A6.Decim.bump C₀ (ξ - β) = 0 := by
    intro α hα β hβ hαβ
    by_contra hcon
    have h1 : Work.KMTPlan.A6.Decim.bump L (ξ - α) ≠ 0 := left_ne_zero_of_mul hcon
    have h2 : Work.KMTPlan.A6.Decim.bump C₀ (ξ - β) ≠ 0 := right_ne_zero_of_mul hcon
    have hLα : ‖ξ - α‖ ≤ (2 : ℝ) ^ (-(L : ℤ)) := hbumpL_supp (ξ - α) h1
    have hCβ : ‖ξ - β‖ ≤ ((2 : ℝ) ^ C₀)⁻¹ := by
      simpa only [hnegC] using hbumpC0_supp (ξ - β) h2
    have htri : ‖α - β‖ ≤ (2 : ℝ) ^ ((1 : ℤ) - (C₀ : ℤ)) := by
      have heq : α - β = (ξ - β) - (ξ - α) := by abel
      rw [heq]
      calc ‖(ξ - β) - (ξ - α)‖ ≤ ‖ξ - β‖ + ‖ξ - α‖ := norm_sub_le _ _
        _ ≤ ((2 : ℝ) ^ C₀)⁻¹ + (2 : ℝ) ^ (-(L : ℤ)) := by linarith
        _ ≤ (2 : ℝ) ^ ((1 : ℤ) - (C₀ : ℤ)) := by
            rw [hpow_eq]; linarith
    exact absurd (hdist α hα β (hA hβ) hαβ) (not_lt.mpr htri)
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  have hsingle : (∑ α ∈ Work.KMTPlan.A6.Decim.torsFinset Q,
      Work.KMTPlan.A6.Decim.bump L (ξ - α) * Work.KMTPlan.A6.Decim.bump C₀ (ξ - β))
      = Work.KMTPlan.A6.Decim.bump L (ξ - β)
        * Work.KMTPlan.A6.Decim.bump C₀ (ξ - β) :=
    Finset.sum_eq_single_of_mem β (hA hβ) (fun α hα hαβ => hzero α hα β hβ hαβ)
  rw [hsingle]
  by_cases hz : Work.KMTPlan.A6.Decim.bump L (ξ - β) = 0
  · rw [hz, zero_mul]
  · rw [hbumpC0_one L (ξ - β) hL (hbumpL_supp (ξ - β) hz), mul_one]

end Work.KMTAreas.A7Hi
