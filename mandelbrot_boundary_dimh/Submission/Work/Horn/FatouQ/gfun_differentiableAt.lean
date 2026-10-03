import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_mapsTo
import Submission.Work.Horn.petal_facts
import Submission.Work.Horn.FatouQ.chartdict
import Submission.Work.Horn.FatouQ.zBranch_contDiff

namespace Work.Horn.FatouQ

open Work.Horn.Flower

/-- The chart dynamics `gfun f q a j w = chartQ q a (f (zBranch q a j w))` is holomorphic on the
half plane `{Re w > M}`: the inverse chart `zBranch q a j` is holomorphic there (`zBranch_contDiff`),
its value lies in the `j`-th petal, hence in the disc `ball 0 ρ ⊆ D` where `f` is holomorphic, and
`f` does not vanish there, so that the chart `chartQ q a z = cc q a / z^q` is holomorphic at the
image point. -/
theorem gfun_differentiableAt {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j) :
    ∀ w : ℂ, M < w.re → DifferentiableAt ℂ (Work.Horn.FatouQ.gfun f q a j) w := by
  intro w hw
  have hwr : 0 < w.re := lt_trans hd.hM hw
  have hzp : zBranch q a j w ∈ petal q a M j := hpetal w hw
  have hznorm : ‖zBranch q a j w‖ ^ q < ‖cc q a‖ / M :=
    hd.hgeo.petal_norm_pow_lt j _ hzp
  have hzlt : ‖zBranch q a j w‖ < ρ :=
    lt_of_pow_lt_pow_left₀ q hd.hρ.le (lt_trans hznorm hd.hRM)
  have hzball : zBranch q a j w ∈ Metric.ball (0 : ℂ) ρ := by
    simpa [Metric.mem_ball, dist_zero_right] using hzlt
  have hzD : zBranch q a j w ∈ D := hd.hb.hsub hzball
  have hz_ne : zBranch q a j w ≠ 0 :=
    fun h => hd.hgeo.not_mem_petal_zero j (h ▸ hzp)
  have hfz_ne : f (zBranch q a j w) ≠ 0 := by
    rw [hd.hb.hf_eq (zBranch q a j w)]
    exact mul_ne_zero hz_ne (hd.hb.hunit_ne _ hzball)
  have hd_zb : DifferentiableAt ℂ (zBranch q a j) w :=
    (zBranch_contDiff hd.hS.hq hd.hS.ha j w hwr).1
  have hd_f : DifferentiableAt ℂ f (zBranch q a j w) :=
    hd.hS.hf.differentiableAt (hd.hS.hD.mem_nhds hzD)
  have hd_chart : DifferentiableAt ℂ (chartQ q a) (f (zBranch q a j w)) := by
    have h : chartQ q a = fun u : ℂ => cc q a / u ^ q := rfl
    rw [h]
    exact (differentiableAt_const _).div (differentiableAt_id.pow q) (pow_ne_zero q hfz_ne)
  have h2 : DifferentiableAt ℂ ((chartQ q a) ∘ (f ∘ (zBranch q a j))) w :=
    hd_chart.comp w (hd_f.comp w hd_zb)
  exact h2

end Work.Horn.FatouQ
