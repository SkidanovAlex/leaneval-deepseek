import Mathlib
import Submission.Work.Horn.flower_defs
import Submission.Work.Horn.bigPetal_of_lt_chartQ_re
import Submission.Work.Horn.re_tendsto_atTop_of_step

/-!
# Orbits of the parabolic germ that converge to `0` eventually enter the big petal

`Work.Horn.exists_iterate_mem_bigPetal`: for a germ `f z = z + a z^(q+1) + o(z^(q+1))` with the
quantitative local data `Flower.Bounds f D q a ρ`, an orbit `z, f z, f² z, …` that avoids `0`
and converges to `0` eventually lands in `Flower.bigPetal q a M = {z | z^q ∈ DM q a M}`, the set
of points where `Re (cc q a / z^q) > M` (i.e. the union of the `q` attracting petals at height
`M`).

The mechanism is the chart `w = chartQ q a z = cc / z^q`, in which the germ is the translation
`w ↦ w + 1 + O(1/4)`: once the orbit is inside the disc `ball 0 ρ` (which happens eventually,
because the orbit converges to `0`) we get `Re (w_{n+1}) ≥ Re (w_n) + 3/4`, so `Re (w_n) → +∞`
and at some point exceeds `M`. The chart value at that time is then exactly the defining
inequality of `DM q a M`.
-/

namespace Work.Horn

theorem exists_iterate_mem_bigPetal {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hb : Work.Horn.Flower.Bounds f D q a ρ) (hM : 0 < M) {z : ℂ}
    (hne : ∀ n : ℕ, f^[n] z ≠ 0)
    (hconv : Filter.Tendsto (fun n : ℕ => f^[n] z) Filter.atTop (nhds 0)) :
    ∃ n : ℕ, f^[n] z ∈ Work.Horn.Flower.bigPetal q a M := by
  -- Eventually the orbit lies in the disc `ball 0 ρ` where the chart estimate is available.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ‖f^[n] z‖ < ρ := by
    rw [Metric.tendsto_atTop] at hconv
    obtain ⟨N, hN⟩ := hconv ρ hb.hρ
    exact ⟨N, fun n hn => by simpa [dist_eq_norm] using hN n hn⟩
  -- In the chart the orbit advances by at least `3/4` in real part at every step.
  have hstep : ∀ n : ℕ, N ≤ n → (Work.Horn.Flower.chartQ q a (f^[n] z)).re + 3 / 4 ≤
      (Work.Horn.Flower.chartQ q a (f^[n + 1] z)).re := by
    intro n hn
    have hc := hb.hchart (f^[n] z) (norm_pos_iff.mpr (hne n)) (hN n hn)
    have h3 : |(Work.Horn.Flower.chartQ q a (f (f^[n] z)) -
        Work.Horn.Flower.chartQ q a (f^[n] z) - 1).re| ≤ 1 / 4 :=
      le_trans (Complex.abs_re_le_norm _) hc
    have h4 := (abs_le.mp h3).1
    simp only [Complex.sub_re, Complex.one_re] at h4
    rw [Function.iterate_succ_apply']
    linarith
  -- Hence the real part of the chart value is unbounded above.
  obtain ⟨n, hn⟩ := re_tendsto_atTop_of_step (v := fun n => Work.Horn.Flower.chartQ q a (f^[n] z))
    (N := N) (c := 3 / 4) (B := M) (by norm_num) hstep
  exact ⟨n, bigPetal_of_lt_chartQ_re (hne n) hn⟩

end Work.Horn
