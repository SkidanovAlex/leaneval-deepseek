import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.meromorphicOrderAt_nonneg_of_seq_bounded
import Submission.Work.EQ.norm_le_half_of_schwarz_ball
import Submission.Work.EQ.norm_apply_zero_le_of_seq_eq

namespace Work.EQ

open Filter Metric Set
open scoped Topology

/-- Let `Y u := (germC a h u).2` be analytic on `Metric.ball 0 ρY` with `‖Y u‖ < ρY` for
`‖u‖ ≤ ρY`, and let `f` be meromorphic at `0`. Suppose `f (t n) = Y (w n)` for a sequence
`t n → 0` of nonzero numbers and witnesses `‖w n‖ ≤ ρY / 2`. Then `f` agrees with a function `g`
that is analytic at `0`, and the value `c := g 0` has `‖c‖ < ρY`.

Route: Schwarz (`Complex.norm_le_norm_of_mapsTo_ball`) with `hstrict` gives `‖f (t n)‖ ≤ ρY / 2`,
so `meromorphicOrderAt f 0 ≥ 0` (a pole would force `‖f (t n)‖ → ∞`); the normal form
`MeromorphicAt.meromorphicOrderAt_eq_int_iff` then produces `g`, and `‖c‖ ≤ ρY / 2 < ρY` follows
by taking the limit along `t n`. -/
theorem meromorphicAt_value_of_seq_germC_snd {a : ℝ} {h : ℂ → ℂ} {ρY : ℝ} (hρY : 0 < ρY)
    (hYan : AnalyticOnNhd ℂ (fun v : ℂ => (Work.EQ.germC a h v).2) (Metric.ball (0:ℂ) ρY))
    (hstrict : ∀ w : ℂ, ‖w‖ ≤ ρY → ‖(Work.EQ.germC a h w).2‖ < ρY)
    {f : ℂ → ℂ} (hf : MeromorphicAt f 0) {t : ℕ → ℂ} (ht0 : ∀ n, t n ≠ 0)
    (ht : Filter.Tendsto t Filter.atTop (nhds 0)) {w : ℕ → ℂ} (hw : ∀ n, ‖w n‖ ≤ ρY / 2)
    (hfw : ∀ n, f (t n) = (Work.EQ.germC a h (w n)).2) :
    ∃ (c : ℂ) (g : ℂ → ℂ), ‖c‖ < ρY ∧ AnalyticAt ℂ g 0 ∧ g 0 = c ∧
      f =ᶠ[nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ] g := by
  -- `Y := (germC a h ·).2` vanishes at `0` (the second coordinate carries a factor `u`)
  have hY0 : (germC a h 0).2 = 0 := by simp [germC]
  -- Schwarz: `‖Y (w n)‖ ≤ ρY / 2`
  have hboundY : ∀ n, ‖(germC a h (w n)).2‖ ≤ ρY / 2 := fun n =>
    norm_le_half_of_schwarz_ball hρY hYan hstrict hY0 (hw n)
  have hboundf : ∀ n, ‖f (t n)‖ ≤ ρY / 2 := fun n => by
    rw [hfw n]; exact hboundY n
  -- `t` tends to `0` inside the punctured neighbourhood
  have ht' : Filter.Tendsto t Filter.atTop (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ht, by filter_upwards with n using ht0 n⟩
  -- a pole at `0` would force `‖f (t n)‖ → ∞`, so the order is nonnegative
  have hord : 0 ≤ meromorphicOrderAt f 0 :=
    meromorphicOrderAt_nonneg_of_seq_bounded hf ht' hboundf
  -- nonnegative order yields a function analytic at `0` agreeing with `f` off `0`
  obtain ⟨g, hgan, hfg⟩ := (MeromorphicAt.meromorphicOrderAt_nonneg_iff hf).1 hord
  -- pass the bound `ρY / 2` to the limit along `t n → 0`
  have hc : ‖g 0‖ ≤ ρY / 2 := norm_apply_zero_le_of_seq_eq hgan hfg ht0 ht hboundf
  exact ⟨g 0, g, by linarith, hgan, rfl, hfg⟩

end Work.EQ
