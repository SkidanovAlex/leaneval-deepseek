import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Xc_bounds_on_strip

namespace Work.Pert.Ksub2

/-- Deep-tail bound for the datum's curve.  For a `§4.1`-datum `d` (so that `Xc d u = τ₀ (φ₀ u)`
is asymptotic to the identity on the repelling sector) and a compact `K'`, there is `J₀` such that
for all `j ≥ J₀` and all `w ∈ K'` one has `‖d.φ (w - j)‖ ≤ 4/j`: the translates of `K'` far to the
left are so deep that `1/‖Xc d u‖ = ‖d.φ u‖` is `O(1/j)` there.

Suggested route: pick `R` with `∀ w ∈ K', ‖w‖ ≤ R` (`Bornology.IsBounded.exists_norm_le` on
`hK'c.isBounded`).  For `j` beyond the thresholds `J₀` set `M := (j:ℝ) - w.re`, `T := |w.im|`;
then `u := w - (j:ℂ) ∈ Work.Pert.Dstrip M T` (its real part is `-M` and `|u.im| ≤ R ≤ M/160`),
and `Work.Pert.Ksub2.Xc_bounds_on_strip d` on that strip gives `‖Xc d u - u‖ ≤ M/160`, so
`‖Xc d u‖ ≥ M - M/160 ≥ j/2`.  Since `Xc d u = -1/(d.φ u)` one has the identity
`1/‖Xc d u‖^2 = ‖d.φ u‖^2`, hence `‖d.φ u‖ ≤ 4/j`.  (`hK'` is only there for the caller's sake;
the strip argument does not use it.) -/
theorem Xc_deep_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j → ∀ w ∈ K', ‖d.φ (w - (j : ℂ))‖ ≤ 4 / (j : ℝ) := by
  obtain ⟨M₀, hM₀pos, hXc⟩ := Xc_bounds_on_strip d
  obtain ⟨R₀, hR₀⟩ := hK'c.isBounded.exists_norm_le
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hR : ∀ w ∈ K', ‖w‖ ≤ R := by
    intro w hw
    rw [hRdef]
    exact le_trans (hR₀ w hw) (le_max_left _ _)
  -- the threshold: everything below happens for `j` beyond a single explicit bound
  refine ⟨Nat.ceil (max (161 * R) (max (R + M₀) 1)), ?_⟩
  intro j hj w hw
  have hceil := Nat.le_ceil (max (161 * R) (max (R + M₀) 1))
  have hjcast : (Nat.ceil (max (161 * R) (max (R + M₀) 1)) : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hj
  have hB : max (161 * R) (max (R + M₀) 1) ≤ (j : ℝ) := le_trans hceil hjcast
  have hj161 : 161 * R ≤ (j : ℝ) := le_trans (le_max_left _ _) hB
  have hjR : R + M₀ ≤ (j : ℝ) :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hB)
  have hj1 : (1 : ℝ) ≤ (j : ℝ) :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hB)
  have hjpos : 0 < (j : ℝ) := by linarith
  have hwp : w.re ≤ R := le_trans (Complex.re_le_norm w) (hR w hw)
  have hwi : |w.im| ≤ R := le_trans (Complex.abs_im_le_norm w) (hR w hw)
  -- the depth `M = j - Re w`, the height `T = |Im w|`
  have hMpos : 0 < (j : ℝ) - w.re := by linarith
  have hMhalf : (j : ℝ) / 2 ≤ (j : ℝ) - w.re := by linarith
  have hM₀ : M₀ ≤ (j : ℝ) - w.re := by linarith
  have hM160 : R ≤ ((j : ℝ) - w.re) / 160 := by linarith
  set u : ℂ := w - (j : ℂ) with hudef
  have hu_re : u.re = -((j : ℝ) - w.re) := by
    rw [hudef, Complex.sub_re, Complex.natCast_re]; ring
  have hu_im : u.im = w.im := by rw [hudef]; simp
  have hstrip : u ∈ Dstrip ((j : ℝ) - w.re) |w.im| :=
    ⟨by rw [hu_re]; linarith, by rw [hu_re], by simp [hu_im]⟩
  obtain ⟨-, hbound⟩ := hXc ((j : ℝ) - w.re) hM₀ |w.im| (le_trans hwi hM160)
  have hb : ‖Work.Pert.Xc d u - u‖ ≤ ((j : ℝ) - w.re) / 160 := hbound u hstrip
  have hnu : (j : ℝ) - w.re ≤ ‖u‖ := by
    have h1 := Complex.abs_re_le_norm u
    rw [hu_re, abs_neg, abs_of_nonneg hMpos.le] at h1
    exact h1
  -- the curve is far from the origin at depth `j`
  have hXcge : (j : ℝ) / 3 ≤ ‖Work.Pert.Xc d u‖ := by
    have hb' : ‖u - Work.Pert.Xc d u‖ ≤ ((j : ℝ) - w.re) / 160 := by
      rwa [norm_sub_rev] at hb
    have h2 := norm_sub_norm_le u (Work.Pert.Xc d u)
    have h3 : (j : ℝ) / 3 ≤ (j : ℝ) - w.re - ((j : ℝ) - w.re) / 160 := by linarith
    linarith
  -- `‖Xc d u‖ = 1/‖d.φ u‖`, so `d.φ u` is small
  have hx : ‖Work.Pert.Xc d u‖ = 1 / ‖d.φ u‖ := by
    simp only [Work.Pert.Xc, MandelDim.tau0, norm_div, norm_neg, norm_one]
  have hge : (j : ℝ) / 3 ≤ 1 / ‖d.φ u‖ := by rw [← hx]; exact hXcge
  have hxpos : 0 < ‖d.φ u‖ := by
    by_contra h
    have h0 : ‖d.φ u‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0, div_zero] at hge
    linarith
  have hmul : ‖d.φ u‖ * ((j : ℝ) / 3) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hge (norm_nonneg (d.φ u))
    rwa [mul_one_div_cancel (ne_of_gt hxpos)] at h
  rw [le_div_iff₀ hjpos]
  have heq : ‖d.φ u‖ * (j : ℝ) = 3 * (‖d.φ u‖ * ((j : ℝ) / 3)) := by ring
  rw [heq]
  linarith

end Work.Pert.Ksub2
