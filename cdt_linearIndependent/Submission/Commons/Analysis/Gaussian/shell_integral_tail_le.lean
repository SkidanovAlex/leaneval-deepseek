import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The shell-integral tail bound of Klartag's Lemma 4.3

This file formalises the analytic core of the "shell integral" estimate in Klartag's proof
of the existence of dense lattice sphere packings (Lemma 4.3 of
*Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*).

For the spherical shell `R = {x ∈ ℝⁿ | 1/a₀ ≤ ‖x‖² < 1/(a₀ - C₀ √(t n))}` we bound the
integral of `exp(-((a₀ - 1/‖x‖²)/√t)²/2)` -- an upper bound for the Gaussian tail `Φ` used
in the paper -- by a constant times `e^{n²t/8} · Vol_n(Bⁿ)`.

The proof is elementary and geometric: the weight is at most `1`, and the shell is contained
in the ball of radius `R = (a₀ - C₀ √(t n))^{-1/2}`, whose volume is `Rⁿ` times the volume of
the unit ball.  The constant is this ratio.

## Remark on the strength of the constant

The constant `C` below is existentially quantified *after* `n, a₀, t, C₀`, hence may depend on
them; the bound proved here is the purely geometric one
`∫ ≤ Rⁿ · Vol_n(Bⁿ)`, giving the explicit constant `max 1 (Rⁿ e^{-n²t/8})`.  Consequently the
estimates `ht`, `htb`, `ha₀`, `ha₀b`, `hC₀` are not used by the proof (only `hCpos` and the
positivity of the unit ball volume).  In particular, with `C₀` left completely free the shell
becomes unbounded as `a₀ - C₀ √(t n) → 0⁺` while the weight stays bounded below by
`exp(-C₀² n / 2)`, so no bound with a constant independent of `C₀` can hold.

The sharper form of Klartag's Lemma 4.3, in which the constant is universal (independent of
`a₀, t` and of the shell, given a fixed `C₀`), requires the polar-coordinate change of
variables and the three-region estimate `I₁ + I₂ + I₃` of the paper, and is not formalised
here.
-/

open MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.Gaussian

/-- A non-negative function which is everywhere at most `1` has integral over a set contained
in a ball of radius `R` at most the volume of that ball. -/
lemma setIntegral_le_volume_ball {n : ℕ} {R : ℝ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hsub : s ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    ∫ x in s, g x ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal := by
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) < ∞ :=
    MeasureTheory.measure_ball_lt_top
  have hs : volume s < ∞ := lt_of_le_of_lt (measure_mono hsub) hfin
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (f := g) (C := 1)
    hs (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hg1 x)
  simp only [one_mul] at h
  calc ∫ x in s, g x ≤ |∫ x in s, g x| := le_abs_self _
    _ = ‖∫ x in s, g x‖ := (Real.norm_eq_abs _).symm
    _ ≤ (volume s).toReal := h
    _ ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal :=
        ENNReal.toReal_mono hfin.ne (measure_mono hsub)

/-- The volume of the unit ball in `ℝⁿ` is a positive real number. -/
lemma volume_unitBall_toReal_pos (n : ℕ) :
    0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
    MeasureTheory.measure_ball_ne_top

/-- The volume of a ball of radius `R ≥ 0` in `ℝⁿ` is `Rⁿ` times the volume of the unit
ball. -/
lemma volume_ball_toReal_eq {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal
      = R ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [EuclideanSpace.volume_ball (Fin n), EuclideanSpace.volume_ball (Fin n),
    Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1), one_pow,
    one_mul]

/-- **Polar coordinates for a radial integrand over a ball.**  For `n ≥ 1` and `r ≥ 0`, the
integral over the ball of radius `r` in `ℝⁿ` of a function of the norm is
`n · Vol_n(Bⁿ) · ∫₀^r ρ^{n-1} g(ρ) dρ`.

This is the ball version of Mathlib's `MeasureTheory.integral_fun_norm_addHaar`, which
integrates over the whole space; by the convention on the Bochner integral no measurability
or integrability hypothesis is needed. -/
lemma integral_fun_norm_ball {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) (g : ℝ → ℝ) :
    ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, g ‖x‖
      = (n : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
        * ∫ ρ in (0 : ℝ)..r, ρ ^ (n - 1) * g ρ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let h : ℝ → ℝ := fun ρ => ρ ^ (n - 1) * g ρ
  let F : ℝ → ℝ := Set.indicator (Set.Iio r) g
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r = {x | ‖x‖ < r} := by
    ext x; simp [Metric.mem_ball, dist_zero_right]
  have h1 : ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, g ‖x‖
      = ∫ x : EuclideanSpace ℝ (Fin n), F ‖x‖ := by
    rw [hball, ← MeasureTheory.integral_indicator (μ := volume)
      (s := {x : EuclideanSpace ℝ (Fin n) | ‖x‖ < r}) (f := fun x => g ‖x‖)
      (isOpen_lt continuous_norm continuous_const).measurableSet]
    rfl
  have h2 := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) F
  rw [finrank_euclideanSpace_fin, Measure.real] at h2
  have hA : ∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) • F y
      = ∫ y in Set.Ioi (0 : ℝ), (Set.Ioo (0 : ℝ) r).indicator h y := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    by_cases hyr : y < r
    · simp [F, h, Set.indicator_of_mem, Set.mem_Ioo, hyr, hy0, smul_eq_mul]
    · simp [F, h, Set.indicator_of_notMem, Set.mem_Ioo, hyr, hy0, smul_eq_mul]
  have hB : ∫ y in Set.Ioi (0 : ℝ), (Set.Ioo (0 : ℝ) r).indicator h y
      = ∫ y in Set.Ioo (0 : ℝ) r, h y := by
    rw [MeasureTheory.setIntegral_indicator (μ := volume) (s := Set.Ioi (0 : ℝ))
      (f := h) measurableSet_Ioo]
    rw [Set.inter_eq_right.mpr (fun y hy => hy.1)]
  have hC : ∫ y in Set.Ioo (0 : ℝ) r, h y = ∫ y in Set.Ioc (0 : ℝ) r, h y :=
    MeasureTheory.setIntegral_congr_set (μ := volume) Ioo_ae_eq_Ioc
  have hD : ∫ y in Set.Ioc (0 : ℝ) r, h y = ∫ ρ in (0 : ℝ)..r, h ρ :=
    (intervalIntegral.integral_of_le hr).symm
  rw [h1, h2, nsmul_eq_mul, smul_eq_mul, hA.trans (hB.trans (hC.trans hD))]
  ring

/-- **Klartag's shell integral estimate (Lemma 4.3).**

For `0 < t ≤ 20 log n / n²`, `1 ≤ a₀ ≤ 1 + 10/n` and `0 < a₀ - C₀ √(tn)`, the integral of
the Gaussian-tail weight `exp(-((a₀ - 1/‖x‖²)/√t)²/2)` over the shell
`{x | 1/a₀ ≤ ‖x‖² < 1/(a₀ - C₀ √(tn))}` is at most a constant times
`e^{n²t/8} · Vol_n(Bⁿ)`.

The constant produced by the proof is
`max 1 ((a₀ - C₀ √(tn))^{-n/2} e^{-n²t/8})`: the shell lies in a ball of radius
`(a₀ - C₀ √(tn))^{-1/2}` and the weight is at most one. -/
theorem shell_integral_tail_le {n : ℕ} (hn : 1 ≤ n) {a₀ t C₀ : ℝ}
    (ht : 0 < t) (htb : t ≤ 20 * Real.log n / (n : ℝ) ^ 2)
    (ha₀ : 1 ≤ a₀) (ha₀b : a₀ ≤ 1 + 10 / (n : ℝ))
    (hC₀ : 0 ≤ C₀) (hCpos : 0 < a₀ - C₀ * Real.sqrt (t * n)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∫ x in {x : EuclideanSpace ℝ (Fin n) |
            1 / a₀ ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < 1 / (a₀ - C₀ * Real.sqrt (t * n))},
          Real.exp (-((a₀ - 1 / ‖x‖ ^ 2) / Real.sqrt t) ^ 2 / 2)
      ≤ C * Real.exp ((n : ℝ) ^ 2 * t / 8)
          * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  -- `d` is the outer threshold `a₀ - C₀ √(tn)`; `R` is the radius of the ball containing
  -- the shell; `ω` is the volume of the unit ball.
  let d : ℝ := a₀ - C₀ * Real.sqrt (t * n)
  have hd : 0 < d := hCpos
  have hd_nonneg : 0 ≤ d := le_of_lt hd
  let R : ℝ := (Real.sqrt d)⁻¹
  have hR_pos : 0 < R := inv_pos.mpr (Real.sqrt_pos.mpr hd)
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  have hR_sq : R ^ 2 = 1 / d := by
    simp only [R, inv_pow, Real.sq_sqrt hd_nonneg, one_div]
  -- The shell is contained in the ball of radius `R`.
  have hsub : {x : EuclideanSpace ℝ (Fin n) | 1 / a₀ ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < 1 / d} ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : ‖x‖ ^ 2 < R ^ 2 := by rw [hR_sq]; exact hx.2
    have h3 := sq_lt_sq.mp h2
    rwa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg hR_nonneg] at h3
  -- The integrand lies in `[0,1]`.
  have hg0 : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ Real.exp (-((a₀ - 1 / ‖x‖ ^ 2) / Real.sqrt t) ^ 2 / 2) :=
    fun x => Real.exp_nonneg _
  have hg1 : ∀ x : EuclideanSpace ℝ (Fin n),
      Real.exp (-((a₀ - 1 / ‖x‖ ^ 2) / Real.sqrt t) ^ 2 / 2) ≤ 1 := by
    intro x
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ ((a₀ - 1 / ‖x‖ ^ 2) / Real.sqrt t) ^ 2 := sq_nonneg _
    linarith
  have hint := setIntegral_le_volume_ball (g := fun x : EuclideanSpace ℝ (Fin n) =>
    Real.exp (-((a₀ - 1 / ‖x‖ ^ 2) / Real.sqrt t) ^ 2 / 2)) hsub hg0 hg1
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal :=
    volume_unitBall_toReal_pos n
  have hexp : Real.exp (-((n : ℝ) ^ 2 * t / 8)) * Real.exp ((n : ℝ) ^ 2 * t / 8) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  refine ⟨max 1 (R ^ n * Real.exp (-((n : ℝ) ^ 2 * t / 8))), le_max_left _ _, ?_⟩
  have hstep : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal ≤
      max 1 (R ^ n * Real.exp (-((n : ℝ) ^ 2 * t / 8)))
        * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rw [volume_ball_toReal_eq hn hR_nonneg]
    have h1 : R ^ n * Real.exp (-((n : ℝ) ^ 2 * t / 8))
        ≤ max 1 (R ^ n * Real.exp (-((n : ℝ) ^ 2 * t / 8))) := le_max_right _ _
    have hmid : R ^ n * Real.exp (-((n : ℝ) ^ 2 * t / 8))
          * Real.exp ((n : ℝ) ^ 2 * t / 8)
          * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
        = R ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
      rw [show R ^ n * Real.exp (-((n : ℝ) ^ 2 * t / 8))
            * Real.exp ((n : ℝ) ^ 2 * t / 8)
            * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
          = R ^ n * (Real.exp (-((n : ℝ) ^ 2 * t / 8))
              * Real.exp ((n : ℝ) ^ 2 * t / 8))
            * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal from by ring]
      rw [hexp, mul_one]
    rw [← hmid]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) hω.le
  calc ∫ x in {x : EuclideanSpace ℝ (Fin n) |
          1 / a₀ ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < 1 / (a₀ - C₀ * Real.sqrt (t * n))},
        Real.exp (-((a₀ - 1 / ‖x‖ ^ 2) / Real.sqrt t) ^ 2 / 2)
      = ∫ x in {x : EuclideanSpace ℝ (Fin n) | 1 / a₀ ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 < 1 / d},
          Real.exp (-((a₀ - 1 / ‖x‖ ^ 2) / Real.sqrt t) ^ 2 / 2) := by simp only [d]
    _ ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal := hint
    _ ≤ _ := hstep

end Commons.Analysis.Gaussian