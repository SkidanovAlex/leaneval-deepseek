import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_mapsTo
import Submission.Work.Horn.petal_facts
import Submission.Work.Horn.injOn_ball
import Submission.Work.Horn.FatouQ.chartdict

/-!
# Injectivity of the chart dynamics on the half plane `{Re w > M}`

The germ `f z = z (1 + z^q H z)` has `‖deriv f - 1‖ ≤ 1/2` on the disc `ball 0 ρ`
(`Flower.Bounds.hderiv`), hence is injective there (`Work.Horn.injOn_ball_of_norm_deriv_sub_one_le`).
Every petal at level `M` lies inside that disc: `‖z‖^q < ‖cc‖/M < ρ^q` on the petal
(`PetalFacts.petal_norm_pow_lt` and `PetalDatum.hRM`), so `‖z‖ < ρ`.

The inverse chart `zBranch q a j` maps the half plane `{Re w > M}` into the `j`-th petal, and the
chart `chartQ q a` undoes it there.  Since `zBranch q a j` intertwines `gfun f q a j` with `f`
(`zBranch j (gfun w) = f (zBranch j w)`), an equality `gfun w₁ = gfun w₂` propagates to
`f (zBranch w₁) = f (zBranch w₂)`, then by injectivity of `f` on the disc to
`zBranch w₁ = zBranch w₂`, and finally `w₁ = chartQ (zBranch w₁) = chartQ (zBranch w₂) = w₂`.
-/

namespace Work.Horn.FatouQ

open Work.Horn.Flower Work.Horn

noncomputable section

/-- **The chart dynamics is injective on the half plane.**  All the hypotheses beyond the datum
are the dictionary between the petal, the chart and the dynamics; the actual content is that each
petal sits inside the disc on which `f` is univalent. -/
theorem gfun_injOn {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w)
    (hinv : ∀ w : ℂ, M < w.re →
      Work.Horn.FatouQ.zBranch q a j (Work.Horn.FatouQ.gfun f q a j w) =
        f (Work.Horn.FatouQ.zBranch q a j w)) :
    Set.InjOn (Work.Horn.FatouQ.gfun f q a j) {w : ℂ | M < w.re} := by
  -- `f` is univalent on the disc where `deriv f` is close to `1`.
  have hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) ρ) :=
    Work.Horn.injOn_ball_of_norm_deriv_sub_one_le hd.hb.hderiv
  -- each petal lies in that disc
  have hpetal_ball : ∀ w : ℂ, M < w.re →
      Work.Horn.FatouQ.zBranch q a j w ∈ Metric.ball (0 : ℂ) ρ := by
    intro w hw
    have hlt : ‖Work.Horn.FatouQ.zBranch q a j w‖ ^ q < ρ ^ q :=
      lt_trans (hd.hgeo.petal_norm_pow_lt j _ (hpetal w hw)) hd.hRM
    have hlt' : ‖Work.Horn.FatouQ.zBranch q a j w‖ < ρ :=
      lt_of_pow_lt_pow_left₀ q (le_of_lt hd.hρ) hlt
    simpa [Metric.mem_ball, dist_zero_right] using hlt'
  intro w1 hw1 w2 hw2 h
  -- `gfun` agrees with `f` in the chart, so `f` takes the same value at the two preimages
  have hf_eq : f (Work.Horn.FatouQ.zBranch q a j w1) =
      f (Work.Horn.FatouQ.zBranch q a j w2) := by
    rw [← hinv w1 hw1, ← hinv w2 hw2, h]
  have hz_eq : Work.Horn.FatouQ.zBranch q a j w1 = Work.Horn.FatouQ.zBranch q a j w2 :=
    hf_inj (hpetal_ball w1 hw1) (hpetal_ball w2 hw2) hf_eq
  -- the chart recovers the coordinate
  calc w1 = Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w1) := (hchart w1 hw1).symm
    _ = Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w2) := by rw [hz_eq]
    _ = w2 := hchart w2 hw2

end

end Work.Horn.FatouQ
