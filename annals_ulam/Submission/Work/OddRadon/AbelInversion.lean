import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.abelReduceIter_abelTrans
import Submission.Work.Analysis.Radon.abel_inversion_hemisphere_assembly

/-!
# The odd-dimensional Radon inversion (`Work.OddRadon`, part 3b)

Assembles the inversion of `radonProfile (2n+1)` on even data:

* `abelTrans_neg_half_eq` — `T_{-1/2}` is the classical Abel transform;
* `abelReduceIter_congr_open`, `abelInvert_congr_of_eqOn` — locality of the inversion;
* `abel_inversion_odd` — `abelInverseData n ∘ abelTrans (n-3/2)` is the identity on `(0,1)`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- `T_{-1/2} G c = ∫_0^c G s / √(c² - s²) ds` for `c ≥ 0`: the classical Abel transform. -/
lemma abelTrans_neg_half_eq {G : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    abelTrans (-(1 / 2)) G c = ∫ s in (0 : ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2) := by
  rw [abelTrans]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hc] at hs
  have hsq : 0 ≤ c ^ 2 - s ^ 2 := by nlinarith [hs.1, hs.2]
  change G s * (c ^ 2 - s ^ 2) ^ (-(1 / 2)) = G s / Real.sqrt (c ^ 2 - s ^ 2)
  rw [show (-(1 / 2) : ℝ) = (-1) / 2 by norm_num,
    Real.rpow_div_two_eq_sqrt (-1) hsq, Real.rpow_neg_one, div_eq_mul_inv]

/-- Congruence of the iterated exponent reduction on an open set. -/
lemma abelReduceIter_congr_open {s : Set ℝ} (hs : IsOpen s) :
    ∀ (k : ℕ) (α : ℝ) {f g : ℝ → ℝ}, Set.EqOn f g s →
      Set.EqOn (abelReduceIter α k f) (abelReduceIter α k g) s := by
  intro k
  induction k with
  | zero => intro α f g h; simpa using h
  | succ k ih =>
      intro α f g h
      rw [abelReduceIter_succ, abelReduceIter_succ]
      apply ih
      intro c hc
      simp only [abelReduce]
      congr 1
      exact (h.eventuallyEq_of_mem (hs.mem_nhds hc)).deriv_eq

/-- Congruence of `abelInvert` from agreement on `(0,b)` with `u < b`. -/
lemma abelInvert_congr_of_eqOn {f g : ℝ → ℝ} {u b : ℝ} (hu : 0 < u) (hub : u < b)
    (h : Set.EqOn f g (Set.Ioo 0 b)) : abelInvert f u = abelInvert g u := by
  have hev : (fun u' : ℝ => ∫ c in (0 : ℝ)..u', c * f c / Real.sqrt (u' ^ 2 - c ^ 2))
      =ᶠ[𝓝 u] (fun u' : ℝ => ∫ c in (0 : ℝ)..u', c * g c / Real.sqrt (u' ^ 2 - c ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (Set.mem_Ioo.mpr ⟨hu, hub⟩)] with u' hu'
    apply intervalIntegral.integral_congr
    intro c hc
    rw [Set.uIcc_of_le hu'.1.le] at hc
    by_cases hc0 : c = 0
    · subst hc0; simp
    · have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
      change c * f c / Real.sqrt (u' ^ 2 - c ^ 2) = c * g c / Real.sqrt (u' ^ 2 - c ^ 2)
      rw [h ⟨hcpos, lt_of_le_of_lt hc.2 hu'.2⟩]
  simp only [abelInvert]
  rw [hev.deriv_eq]

/-- **The odd-dimensional Abel inversion.**  For `n ≥ 1` and `G` of class `C¹` on `[0,1]`,
the composite `abelInverseData n ∘ abelTrans (n - 3/2)` is the identity on `(0,1)`. -/
theorem abel_inversion_odd (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    G u = abelInverseData n (abelTrans ((n : ℝ) - 3 / 2) G) u := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  have hk : (((n - 1 : ℕ) : ℝ)) - 1 < (n : ℝ) - 3 / 2 := by
    rw [hcast]; linarith
  have hhalf : (n : ℝ) - 3 / 2 - ((n - 1 : ℕ) : ℝ) = -(1 / 2) := by
    rw [hcast]; ring
  have hred := abelReduceIter_abelTrans (G := G) hG (k := n - 1) (α := (n : ℝ) - 3 / 2) hk
  have hEq : Set.EqOn
      (abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) (abelTrans ((n : ℝ) - 3 / 2) G))
      (abelTrans (-(1 / 2)) G) (Set.Ioo 0 1) := by
    intro c hc
    have h := hred hc
    rw [hhalf] at h
    exact h
  have hcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := hG.continuousOn
  have hfinal := Commons.Analysis.Radon.abel_inversion_hemisphere_final (G := G) hcont hu
  have hev : (fun u' : ℝ => ∫ c in (0 : ℝ)..u',
        c * abelTrans (-(1 / 2)) G c / Real.sqrt (u' ^ 2 - c ^ 2))
      =ᶠ[𝓝 u] (fun u' : ℝ => ∫ c in (0 : ℝ)..u',
        c * (∫ s in (0 : ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)) /
          Real.sqrt (u' ^ 2 - c ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (Set.mem_Ioo.mpr ⟨hu.1, hu.2⟩)] with u' hu'
    apply intervalIntegral.integral_congr
    intro c hc
    rw [Set.uIcc_of_le hu'.1.le] at hc
    change c * abelTrans (-(1 / 2)) G c / Real.sqrt (u' ^ 2 - c ^ 2)
      = c * (∫ s in (0 : ℝ)..c, G s / Real.sqrt (c ^ 2 - s ^ 2)) /
          Real.sqrt (u' ^ 2 - c ^ 2)
    rw [abelTrans_neg_half_eq hc.1]
  have hinvert : abelInvert (abelTrans (-(1 / 2)) G) u = G u := by
    simp only [abelInvert]
    rw [hfinal, hev.deriv_eq]
  unfold abelInverseData
  rw [abelInvert_congr_of_eqOn hu.1 hu.2 hEq, hinvert]

end Work.OddRadon
