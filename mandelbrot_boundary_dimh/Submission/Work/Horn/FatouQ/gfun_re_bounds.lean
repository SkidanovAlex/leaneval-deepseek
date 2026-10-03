import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_mapsTo
import Submission.Work.Horn.petal_facts
import Submission.Work.Horn.log_pow_eq
import Submission.Work.Horn.FatouQ.chartdict

namespace Work.Horn.FatouQ

/-- On the half plane `{Re w > M}` the chart dynamics `gfun` moves real parts forward by at
least `1/2`: this is the quantitative content of the chart estimate `Bounds.hchart` (the chart is
a translation up to `1/4` in the sup norm), transported to the petal through the inverse chart
`zBranch`, which is a left inverse of `chartQ` there. -/
theorem gfun_re_bounds {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w) :
    (∀ w : ℂ, M < w.re → M < (Work.Horn.FatouQ.gfun f q a j w).re) ∧
    (∀ w : ℂ, M < w.re → w.re + 1 / 2 ≤ (Work.Horn.FatouQ.gfun f q a j w).re) := by
  have hstep : ∀ w : ℂ, M < w.re → w.re + 1 / 2 ≤ (Work.Horn.FatouQ.gfun f q a j w).re := by
    intro w hw
    have hz : Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j := hpetal w hw
    obtain ⟨hzpos, -, -⟩ := (hd.hgeo.mem_petal_iff j (Work.Horn.FatouQ.zBranch q a j w)).mp hz
    have hznorm : ‖Work.Horn.FatouQ.zBranch q a j w‖ ^ q < ‖Work.Horn.Flower.cc q a‖ / M :=
      hd.hgeo.petal_norm_pow_lt j _ hz
    have hzlt : ‖Work.Horn.FatouQ.zBranch q a j w‖ < ρ :=
      lt_of_pow_lt_pow_left₀ q (le_of_lt hd.hb.hρ) (lt_trans hznorm hd.hRM)
    have hch := hd.hb.hchart (Work.Horn.FatouQ.zBranch q a j w) hzpos hzlt
    have hchw : Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w := hchart w hw
    have hmain : -(1 / 4 : ℝ) ≤
        (Work.Horn.Flower.chartQ q a (f (Work.Horn.FatouQ.zBranch q a j w))).re - w.re - 1 := by
      have h := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hch)).1
      rw [hchw] at h
      simpa only [Complex.sub_re, Complex.one_re] using h
    show w.re + 1 / 2 ≤ (Work.Horn.Flower.chartQ q a (f (Work.Horn.FatouQ.zBranch q a j w))).re
    linarith
  exact ⟨fun w hw => lt_of_lt_of_le (lt_of_lt_of_le hw (by linarith)) (hstep w hw), hstep⟩

end Work.Horn.FatouQ
