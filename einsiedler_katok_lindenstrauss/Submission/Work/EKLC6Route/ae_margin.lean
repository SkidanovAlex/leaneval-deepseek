import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.neverReturnSet_null
import Submission.Work.EKLC6Route.thin_margin_core

noncomputable section
namespace Work.EKLC6Route
open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

open Classical

/-- `lamExp t` is the minimal contraction exponent of `aDiag t`; it is positive because every
term of the defining infimum is (`t j - t i > 0` at a pair with `t i < t j`, or the fallback
value `1`). -/
theorem lamExp_pos (t : Fin 3 → ℝ) : 0 < lamExp t := by
  rw [lamExp, Finset.lt_inf'_iff]
  rintro ⟨i, j⟩ -
  by_cases h : t i < t j
  · simp only [h, ↓reduceIte]; linarith
  · simp only [h, ↓reduceIte]; norm_num

/-- If `w.dU z ≤ s < w.r`, then `z` lies in the `(2r,ρ)`-chart of `w` and the deviation of its
`uc`-coordinate from the level `w.r` is at most `s`.  (Below the level `w.r` the function `dU`
is exactly that deviation, and outside the chart it equals `w.r`.) -/
lemma dU_le_mem_chart {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ} (w : Window μ t)
    {z : X3} {s : ℝ} (h : w.dU z ≤ s) (hs : s < w.r) :
    z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ∧ |dev (w.uc z) - w.r| ≤ s := by
  classical
  by_cases hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
  · exact ⟨hz, by rwa [Window.dU, if_pos hz] at h⟩
  · rw [Window.dU, if_neg hz] at h
    exact absurd h (not_le.mpr hs)

/-- **The a.e. margin of a window.**  For `μ`-a.e. `x` the values `w.dU (α^{nt} x)` along the
forward orbit of `x` are bounded below by a geometric sequence of ratio `e^{-λ/2}`,
`λ = lamExp t`.

This is the Borel–Cantelli margin of the route lead (L6a): the chart's `thin` field bounds the
`μ`-mass of the shell `{|dev (uc ·) - r| ≤ ε}` by `c ε`, so the shells at the scales
`ε_n = e^{-λn/2}` have summable mass along the (measure preserving) orbit; a.e. orbit therefore
misses them from some time on.  The finitely many earlier times are taken care of by the a.e.
non-vanishing of `w.dU` along the orbit, which is what the proof of the core lemma
`Work.EKLC6Route.thin_margin_core` extracts from the same thinness. -/
theorem ae_margin {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t)
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLC6Route.Tm t) μ μ) :
    ∀ᵐ x ∂μ, ∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ,
      δ' * Real.exp (-(Work.EKLC6Route.lamExp t / 2) * n) ≤
        w.dU ((Work.EKLC6Route.Tm t)^[n] x) := by
  classical
  obtain ⟨c, hthin⟩ := w.thin
  have hlam : 0 < lamExp t := lamExp_pos t
  have hrho0 : 0 < Real.exp (-(lamExp t / 2)) := Real.exp_pos _
  have hrho1 : Real.exp (-(lamExp t / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hexp : ∀ n : ℕ, Real.exp (-(lamExp t / 2) * n) = Real.exp (-(lamExp t / 2)) ^ n := by
    intro n
    rw [mul_comm, Real.exp_nat_mul]
  -- the thinness of the chart shells, with a nonnegative constant
  have hthin' : ∀ ε : ℝ, 0 < ε →
      μ {z : X3 | z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ∧
          |dev (w.uc z) - w.r| ≤ ε} ≤ ENNReal.ofReal (max c 0 * ε) := by
    intro ε hε
    refine le_trans (hthin ε hε) (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left c 0) (le_of_lt hε)
  -- below the level `w.r`, `dU` is caught by the shells
  have hBsmall' : ∀ (z : X3) (ε : ℝ), w.dU z ≤ ε → ε < w.r →
      z ∈ {y : X3 | y ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ∧
          |dev (w.uc y) - w.r| ≤ ε} :=
    fun z ε h h' => dU_le_mem_chart w h h'
  have hcore : ∀ᵐ x ∂μ, ∃ δ' : ℝ, 0 < δ' ∧ ∀ n : ℕ,
      δ' * Real.exp (-(lamExp t / 2)) ^ n ≤ w.dU ((Tm t)^[n] x) :=
    thin_margin_core (μ := μ) (T := Tm t) (f := w.dU)
      (B := fun ε : ℝ => {z : X3 | z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ∧
          |dev (w.uc z) - w.r| ≤ ε})
      (c := max c 0) (rho := Real.exp (-(lamExp t / 2))) (r := w.r)
      hmp (le_max_right c 0) hrho0 hrho1 w.hr hthin' hBsmall'
  filter_upwards [hcore] with x hx
  obtain ⟨δ', hδ'pos, hδ'⟩ := hx
  exact ⟨δ', hδ'pos, fun n => by rw [hexp n]; exact hδ' n⟩

end Work.EKLC6Route

