/-
# Geometry of the dyadic circle bump `bump L = periodize (η_{≤-L})`

`bump L` is the periodisation of the cut-off `η_{≤-L}(x) = η (2^L x)`, whose (closed) support is
`[-2^{-L}, 2^{-L}] ⊆ [-1/2, 1/2]` for `L ≥ 1`.  Since at most one period can contribute and the
two candidates `x` and `x - 1` (`x ∈ [0,1)` the canonical representative) cannot both survive
(`|x| ≥ 1/2` or `|x - 1| ≥ 1/2`), the periodisation collapses to the *single* value
`η_{≤-L} (lift ξ)`, where `lift ξ ∈ [-1/2, 1/2)` is the canonical lift of `ξ` on the circle.

This is `Work.KMTAreas.A7.periodize_eq_lift` with the closed (instead of strict) support
hypothesis, i.e. it also covers the endpoint case `L = 1` where the support half-width is exactly
`1/2`; there the two terms can only both be "in the support" at the antipode `x = 1/2`, where both
vanish.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Decim.Defs
import Submission.Work.KMTAreas.A7.liftCollapse
import Submission.Work.KMTContract.etaCutRegular
import Submission.Work.KMTContract.periodizeCoeEqTsum

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6.Decim

open Work.Analysis.IonescuWainger MeasureTheory

noncomputable section

/-- `2^{-L}` as a power of `1/2`. -/
private lemma two_zpow_neg_eq_half_pow (L : ℕ) : (2 : ℝ) ^ (-(L : ℤ)) = (1 / 2 : ℝ) ^ L := by
  rw [zpow_neg, zpow_natCast, one_div, ← inv_pow]

/-- `2^{-L} ≤ 1/2` for `L ≥ 1`. -/
private lemma two_zpow_neg_le_half {L : ℕ} (hL : 1 ≤ L) :
    (2 : ℝ) ^ (-(L : ℤ)) ≤ 1 / 2 := by
  rw [two_zpow_neg_eq_half_pow L]
  calc (1 / 2 : ℝ) ^ L ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    _ = 1 / 2 := by norm_num

/-- **The collapse of the dyadic bump to the canonical lift.**  For `L ≥ 1` and every `ξ` on the
circle, the periodisation of `η_{≤-L}` at `ξ` is `η_{≤-L}` evaluated at the canonical lift of `ξ`.
-/
theorem bump_eq_cut_lift (L : ℕ) (hL : 1 ≤ L) (ξ : Work.Analysis.IonescuWainger.Circle) :
    bump L ξ = etaCut Work.KMTContract.kmtEta (-(L : ℤ))
      (Work.KMTAreas.A7.lift ξ) := by
  set k : ℤ := -(L : ℤ) with hkdef
  set Φ : ℝ → ℂ := etaCut Work.KMTContract.kmtEta k with hΦdef
  have hΦcoe : Φ = etaCut Work.KMTContract.kmtEta (-(L : ℤ)) := by rw [hΦdef, hkdef]
  have hΦzero : ∀ x : ℝ, (2 : ℝ) ^ k ≤ |x| → Φ x = 0 := by
    intro x hx
    rw [hΦdef]
    exact (Work.KMTContract.etaCutRegular k).2.2 x hx
  have h2k : (2 : ℝ) ^ k ≤ 1 / 2 := by
    rw [hkdef]; exact two_zpow_neg_le_half hL
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hxdef
  have hxc : ((x : ℝ) : Work.Analysis.IonescuWainger.Circle) = ξ := by
    rw [hxdef]; exact AddCircle.coe_equivIco
  have hx0 : 0 ≤ x := by
    have h := (AddCircle.equivIco (1 : ℝ) 0 ξ).2
    rw [Set.mem_Ico] at h
    rw [hxdef]; exact h.1
  have hx1 : x < 1 := by
    have h := (AddCircle.equivIco (1 : ℝ) 0 ξ).2
    rw [Set.mem_Ico] at h
    rw [hxdef]; linarith [h.2]
  -- the periodisation as the `ℤ`-orbit sum
  have hper : bump L ξ = ∑' n : ℤ, Φ (x + (n : ℝ)) := by
    rw [bump, ← hΦcoe, ← hxc, Work.KMTContract.periodizeCoeEqTsum]
  -- only the terms `n = 0` and `n = -1` can survive
  have hvan : ∀ n : ℤ, n ∉ ({0, -1} : Finset ℤ) → Φ (x + (n : ℝ)) = 0 := by
    intro n hn
    refine hΦzero _ ?_
    have hn0 : n ≠ 0 := fun h => hn (by simp [h])
    have hn1 : n ≠ -1 := fun h => hn (by simp [h])
    have hcase : n ≤ -2 ∨ 1 ≤ n := by omega
    rcases hcase with h | h
    · have hle : x + (n : ℝ) ≤ -1 := by
        have : (n : ℝ) ≤ -2 := by exact_mod_cast h
        linarith
      have habs : (1 : ℝ) ≤ |x + (n : ℝ)| := by
        rw [abs_of_nonpos (by linarith)]; linarith
      linarith
    · have hge : (1 : ℝ) ≤ x + (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        linarith
      have habs : (1 : ℝ) ≤ |x + (n : ℝ)| := le_trans hge (le_abs_self _)
      linarith
  have htwo : bump L ξ = Φ x + Φ (x - 1) := by
    rw [hper, tsum_eq_sum (s := ({0, -1} : Finset ℤ)) hvan]
    rw [Finset.sum_insert (by simp : (0 : ℤ) ∉ ({(-1 : ℤ)} : Finset ℤ)), Finset.sum_singleton]
    simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, add_zero, ← sub_eq_add_neg]
  -- the two candidates: exactly the one which is the canonical lift survives
  rcases lt_or_ge x (1 / 2) with hxlt | hxge
  · have hlift : Work.KMTAreas.A7.lift ξ = x :=
      Work.KMTAreas.A7.lift_eq_of_lt hxc hx0 hxlt
    have hzero : Φ (x - 1) = 0 := by
      refine hΦzero _ ?_
      have habs : |x - 1| = 1 - x := by rw [abs_of_nonpos (by linarith)]; ring
      rw [habs]
      linarith
    rw [htwo, hzero, add_zero, hlift, hΦcoe]
  · have hlift : Work.KMTAreas.A7.lift ξ = x + (-1) :=
      Work.KMTAreas.A7.lift_eq_of_ge hxc hx1 hxge
    have hzero : Φ x = 0 := by
      refine hΦzero _ ?_
      rw [abs_of_nonneg hx0]
      linarith
    rw [htwo, hzero, zero_add, hlift, hΦcoe]
    simp only [← sub_eq_add_neg]

/-- **The three elementary properties of the dyadic circle bump.**
(i) it vanishes outside the arc of radius `2^{-L}`; (ii) it is supported in `realArc (-(L:ℤ))` in
the sense of `SupportedInArc`; (iii) it is `1` on the arc of radius `2^{-j}` for every `j ≥ L+1`. -/
theorem bump_geometry (L : ℕ) (hL : 1 ≤ L) :
    (∀ ξ : Work.Analysis.IonescuWainger.Circle,
        bump L ξ ≠ 0 → ‖ξ‖ ≤ (2 : ℝ) ^ (-(L : ℤ))) ∧
      SupportedInArc (-(L : ℤ)) (bump L) ∧
      (∀ (j : ℕ) (ξ : Work.Analysis.IonescuWainger.Circle), L + 1 ≤ j →
        ‖ξ‖ ≤ (2 : ℝ) ^ (-(j : ℤ)) → bump L ξ = 1) := by
  have hlift_mem : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      |Work.KMTAreas.A7.lift ξ| ≤ 1 / 2 := by
    intro ξ
    have h := Work.KMTAreas.A7.lift_mem ξ
    rw [Set.mem_Ico] at h
    rw [abs_le]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hnorm_lift : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖ξ‖ = |Work.KMTAreas.A7.lift ξ| := by
    intro ξ
    have h := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero
      (x := Work.KMTAreas.A7.lift ξ)).mpr (by simpa using hlift_mem ξ)
    rwa [Work.KMTAreas.A7.lift_coe ξ] at h
  have hstrict_of : ∀ ξ : Work.Analysis.IonescuWainger.Circle, bump L ξ ≠ 0 →
      |Work.KMTAreas.A7.lift ξ| < (2 : ℝ) ^ (-(L : ℤ)) := by
    intro ξ hξ
    rw [bump_eq_cut_lift L hL ξ] at hξ
    by_contra hcon
    push_neg at hcon
    exact hξ ((Work.KMTContract.etaCutRegular (-(L : ℤ))).2.2 _ hcon)
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ
    rw [hnorm_lift ξ]
    exact le_of_lt (hstrict_of ξ hξ)
  · intro ξ hξ
    refine ⟨Work.KMTAreas.A7.lift ξ, ?_, Work.KMTAreas.A7.lift_coe ξ⟩
    rw [realArc, Set.mem_Icc]
    exact abs_le.mp (le_of_lt (hstrict_of ξ hξ))
  · intro j ξ hj hξ
    rw [bump_eq_cut_lift L hL ξ]
    have hl : |Work.KMTAreas.A7.lift ξ| ≤ (2 : ℝ) ^ (-(j : ℤ)) := by
      rw [← hnorm_lift ξ]; exact hξ
    have hratio : |Work.KMTAreas.A7.lift ξ / (2 : ℝ) ^ (-(L : ℤ))| ≤ 1 / 2 := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(L : ℤ)) :=
        zpow_pos (by norm_num) (-(L : ℤ))
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      calc |Work.KMTAreas.A7.lift ξ| ≤ (2 : ℝ) ^ (-(j : ℤ)) := hl
        _ = (2 : ℝ) ^ ((L : ℤ) - (j : ℤ)) * (2 : ℝ) ^ (-(L : ℤ)) := by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            congr 1
            ring
        _ ≤ (1 / 2) * (2 : ℝ) ^ (-(L : ℤ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hpos)
            calc (2 : ℝ) ^ ((L : ℤ) - (j : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
                  zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
              _ = 1 / 2 := by norm_num
    rw [etaCut]
    exact Work.KMTContract.kmtEta_one hratio

end

end Work.KMTPlan.A6.Decim
