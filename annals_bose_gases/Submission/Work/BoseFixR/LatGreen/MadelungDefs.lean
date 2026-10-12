import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseFixR.LatGreen.PoissonDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.MadelungDefs` — vocabulary for the Madelung bound

The Madelung bound `h(u) ≤ 1/(2π‖u‖)` for the smooth part of the `ℤ³` lattice Green's function
(`Work.BoseFixR.LatGreen.latGreenSmooth`) is proved by the Ewald splitting of the theta-integral

`h(u) = ∫_0^∞ (Σ_n p_t(u − n) − 1) dt − 1/(4π‖u‖)`

at a splitting time `η`: the short-time piece is bounded by a *direct Gaussian* (lattice-sum)
estimate and the long-time piece by the *Fourier series* of the torus heat kernel
(Poisson/Jacobi summation), which decays exponentially.

This module collects the numerical side-conditions of that splitting:

* `Q1 t x` — the heat kernel of the unit circle `ℝ/ℤ`, i.e. the periodisation `Σ_m p_t(x − m)`
  of the one-dimensional heat kernel `heatK1`;
* `etaZ` — the splitting time `1/32`;
* `tauZ t = 2 Σ_{j≥1} e^{−(j−1/2)²/(4t)}` — the short-time (direct) tail parameter: every
  lattice point other than the origin is at distance `≥ j − 1/2` in some coordinate;
* `rhoZ t = 2 Σ_{j≥1} e^{−4π²tj²}` — the long-time (Fourier) tail parameter, which is the
  two-sided bound `|Q1 t x − 1| ≤ ρ(t)`;
* `SZ t = Σ_{j≥1} e^{−4π²tj²}` so that `rhoZ t = 2 * SZ t`.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-- The heat kernel of the unit circle `ℝ/ℤ`: the periodisation of the one-dimensional heat
kernel `heatK1`.  (`heatPeriod` is the product of three of these — see
`Work.BoseFixR.LatGreen.heatPeriod_eq_prod`.) -/
noncomputable def Q1 (t x : ℝ) : ℝ := ∑' m : ℤ, heatK1 t (x - m)

/-- The splitting time of the Ewald decomposition: `1/32`. -/
def etaZ : ℝ := 1 / 32

/-- The short-time (direct/Gaussian) tail parameter `2 Σ_{j≥1} e^{−(j−1/2)²/(4t)}`. -/
noncomputable def tauZ (t : ℝ) : ℝ :=
  2 * ∑' j : ℕ, Real.exp (-(((j : ℝ) + 1 / 2) ^ 2) / (4 * t))

/-- The Fourier tail parameter `Σ_{j≥1} e^{−4π²t j²}` (`j` shifted to `j+1`). -/
noncomputable def SZ (t : ℝ) : ℝ :=
  ∑' j : ℕ, Real.exp (-(4 * Real.pi ^ 2 * t) * ((j : ℝ) + 1) ^ 2)

/-- The long-time (Fourier) tail parameter `ρ(t) = 2 Σ_{j≥1} e^{−4π²tj²}`. -/
noncomputable def rhoZ (t : ℝ) : ℝ := 2 * SZ t

/-- The direct (short-time) tail comparison family, written as a sum over `ℤ`:
`WZ t m = 0` for `m = 0` and `e^{−(|m|−1/2)²/(4t)}` otherwise.  Its total mass is `tauZ t`. -/
noncomputable def WZ (t : ℝ) (m : ℤ) : ℝ :=
  if m = 0 then 0 else Real.exp (-((|((m : ℤ) : ℝ)| - 1 / 2) ^ 2) / (4 * t))

lemma WZ_apply_of_ne {t : ℝ} {m : ℤ} (hm : m ≠ 0) :
    WZ t m = Real.exp (-((|((m : ℤ) : ℝ)| - 1 / 2) ^ 2) / (4 * t)) := by
  simp only [WZ, if_neg hm]

lemma WZ_zero {t : ℝ} : WZ t 0 = 0 := by simp [WZ]

lemma summable_WZ {t : ℝ} (ht : 0 < t) : Summable (WZ t) := by
  have hc : (0 : ℝ) < 1 / (8 * t) := by positivity
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    (Summable.mul_left (Real.exp (1 / (16 * t))) (summable_exp_neg_mul_sq_int hc))
  · simp only [WZ]; split_ifs with h
    · exact le_refl 0
    · exact Real.exp_nonneg _
  · rcases eq_or_ne m 0 with hm | hm
    · subst hm
      rw [WZ_zero]
      positivity
    · rw [WZ_apply_of_ne hm]
      have h1 : -((|((m : ℤ) : ℝ)| - 1 / 2) ^ 2) / (4 * t)
          ≤ 1 / (16 * t) - (1 / (8 * t)) * (m : ℝ) ^ 2 := by
        have hpos : 0 < 4 * t := by positivity
        rw [div_le_iff₀ hpos]
        have h4 : (1 / (16 * t) - (1 / (8 * t)) * (m : ℝ) ^ 2) * (4 * t)
            = 1 / 4 - (m : ℝ) ^ 2 / 2 := by
          field_simp
          ring
        rw [h4]
        have hsq : |((m : ℤ) : ℝ)| ^ 2 = (m : ℝ) ^ 2 := by simp
        nlinarith [sq_nonneg (|((m : ℤ) : ℝ)| - 1), hsq]
      calc Real.exp (-((|((m : ℤ) : ℝ)| - 1 / 2) ^ 2) / (4 * t))
          ≤ Real.exp (1 / (16 * t) - (1 / (8 * t)) * (m : ℝ) ^ 2) :=
            Real.exp_le_exp.mpr h1
        _ = Real.exp (1 / (16 * t)) * Real.exp (-(1 / (8 * t)) * (m : ℝ) ^ 2) := by
            rw [← Real.exp_add]; ring_nf

/-- `WZ t` is even. -/
lemma WZ_even {t : ℝ} : Function.Even (WZ t) := by
  intro m
  rcases eq_or_ne m 0 with hm | hm
  · rw [hm, neg_zero]
  · rw [WZ_apply_of_ne hm, WZ_apply_of_ne (neg_ne_zero.mpr hm), Int.cast_neg, abs_neg]

lemma tsum_WZ {t : ℝ} (ht : 0 < t) : (∑' m : ℤ, WZ t m) = tauZ t := by
  have h2 := tsum_int_eq_zero_add_two_mul_tsum_pnat WZ_even (summable_WZ ht)
  rw [WZ_zero, zero_add] at h2
  have h3 : (∑' n : ℕ+, WZ t ↑↑n)
      = ∑' j : ℕ, Real.exp (-(((j : ℝ) + 1 / 2) ^ 2) / (4 * t)) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ => WZ t (k : ℤ))]
    refine tsum_congr fun n => ?_
    rw [WZ_apply_of_ne (by omega : (((n + 1 : ℕ) : ℤ)) ≠ 0)]
    congr 1
    have h1 : |(((n + 1 : ℕ) : ℤ) : ℝ)| = ((n : ℝ) + 1) := by
      rw [abs_of_nonneg (by positivity)]
      push_cast
      ring
    rw [h1]
    ring
  rw [h3] at h2
  rw [h2]
  simp only [tauZ]
  ring

end Work.BoseFixR.LatGreen
