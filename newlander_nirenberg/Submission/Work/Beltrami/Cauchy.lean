/-
# The Cauchy transform and the Beurling transform on `ℂ`

`cauchyT f` is the Cauchy potential of `f` (a solution of `∂̄(Tf) = f`), and
`beurling f` is the Beurling transform of `f` (the `∂`-derivative of `Tf`).

`cauchyT` is defined by the convolution integral against the locally integrable
kernel `(ζ - z)⁻¹`.  `beurling` is defined by the convolution integral against
the singular kernel `(ζ - z)⁻²`, regularised by *subtracting* `χ(ζ - z) · f z`,
where `χ` is a fixed smooth cutoff function equal to `1` near `0` and supported
in the unit disc.  This is legitimate because the mean of `w ↦ w⁻²` over any
punctured disc centred at `0` vanishes (`∫_{ε < ‖w‖ < R} w⁻² dA(w) = 0`), hence
`∫ χ(w) w⁻² dA(w) = 0`; it also makes the integrand compactly supported and
absolutely integrable for locally Hölder functions, so no principal value is
needed in the definition.

The analytic facts about these operators (the potential bound, `∂̄(Tf) = f`,
`∂(Tf) = Bf` and the Schauder estimates for `B`) are stated and proved
separately; this file only records the definitions and the elementary algebra.
-/
import Mathlib
import Submission.Work.Beltrami.Defs

noncomputable section

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff

/-- A fixed radial smooth cutoff on `ℂ`: `bumpC w = σ (2 - 2‖w‖)`, where
`σ = Real.smoothTransition` is the standard smooth step function (`σ x = 0` for `x ≤ 0`,
`σ x = 1` for `1 ≤ x`).  Thus `bumpC` equals `1` on the closed ball of radius `1/2`, vanishes
outside the open ball of radius `1`, and takes values in `[0,1]`.

It is defined *explicitly*, rather than through the `ContDiffBump` API, because it has to be
manifestly **radial**: `bumpC (i * w) = bumpC w`.  This radiality is exactly what makes the
regularising term in the Beurling transform vanish,
`∫ w, (1 - bumpC w) * (w^2)⁻¹ = 0` (the quarter turn `w ↦ i w` preserves the measure and changes
the sign of `w⁻²`), and hence what makes `beurling f` equal to the principal value of the `∂` of
the Cauchy transform of `f`.  An arbitrary `ContDiffBump` is only guaranteed to be *even*, and for
such a cutoff the identity `∂ (cauchyT f) = beurling f` is false. -/
noncomputable def bumpC (w : ℂ) : ℝ := Real.smoothTransition (2 - 2 * ‖w‖)

theorem bumpC_apply (w : ℂ) : bumpC w = Real.smoothTransition (2 - 2 * ‖w‖) := rfl

theorem bumpC_nonneg (z : ℂ) : 0 ≤ bumpC z := Real.smoothTransition.nonneg _

theorem bumpC_le_one (z : ℂ) : bumpC z ≤ 1 := Real.smoothTransition.le_one _

theorem bumpC_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : bumpC z = 1 := by
  rw [bumpC, Real.smoothTransition.eq_one_iff_one_le]
  linarith

theorem bumpC_eq_zero {z : ℂ} (hz : 1 ≤ ‖z‖) : bumpC z = 0 := by
  rw [bumpC, Real.smoothTransition.zero_iff_nonpos]
  linarith

theorem bumpC_contDiff : ContDiff ℝ ∞ (bumpC : ℂ → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem
      (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2)) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact bumpC_eq_one hz.le
  · have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => 2 - 2 * ‖z‖) w :=
      contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_norm ℝ hw))
    exact Real.smoothTransition.contDiff.comp_contDiffAt w h2

/-- The complex-valued version of `bumpC_contDiff`. -/
theorem bumpC_contDiffC : ContDiff ℝ ∞ (fun z : ℂ => (bumpC z : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp bumpC_contDiff

/-- `bumpC` has compact support (`support ⊆ closedBall 0 1`). -/
theorem bumpC_hasCompactSupport : HasCompactSupport (fun z : ℂ => (bumpC z : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 1) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push_neg at hlt
  exact hz (by rw [bumpC_eq_zero hlt.le]; simp)

/-- The cutoff is measurable (as a complex-valued function). -/
theorem bumpC_measurable : Measurable (fun w : ℂ => (bumpC w : ℂ)) :=
  (Complex.continuous_ofReal.comp bumpC_contDiff.continuous).measurable

/-- **The cutoff is radial**: it is invariant under the quarter turn `w ↦ i w`.  This is the key
property that distinguishes it from a general `ContDiffBump`. -/
theorem bumpC_rotI (z : ℂ) : bumpC (Complex.I * z) = bumpC z := by
  rw [bumpC, bumpC, norm_mul, Complex.norm_I, one_mul]

/-- The **Cauchy transform** (Cauchy potential) of `f`:
`T f z = -(1/π) ∫ (ζ - z)⁻¹ * f ζ dA(ζ)`, where `dA` is Lebesgue measure on `ℂ ≅ ℝ²`.
This is the standard solution operator for `∂̄`: `∂̄ (T f) = f`. -/
def cauchyT (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-(Real.pi)⁻¹) • ∫ ζ, (ζ - z)⁻¹ * f ζ ∂volume

/-- The **Beurling transform** of `f`:
`B f z = -(1/π) ∫ (f ζ - χ(ζ - z) • f z) • (ζ - z)⁻² dA(ζ)`,
with `χ = bumpC` a fixed cutoff (`1` near `0`, supported in the unit disc).
It is the `∂`-derivative of `T f`. -/
def beurling (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-(Real.pi)⁻¹) • ∫ ζ, (f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹ ∂volume

@[simp] theorem cauchyT_apply (f : ℂ → ℂ) (z : ℂ) :
    cauchyT f z = (-(Real.pi)⁻¹) • ∫ ζ, (ζ - z)⁻¹ * f ζ ∂volume := rfl

@[simp] theorem beurling_apply (f : ℂ → ℂ) (z : ℂ) :
    beurling f z =
      (-(Real.pi)⁻¹) • ∫ ζ, (f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹ ∂volume := rfl

/-- The Cauchy transform is additive on integrable functions. -/
theorem cauchyT_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : Integrable (fun ζ => (ζ - z)⁻¹ * f ζ) volume)
    (hg : Integrable (fun ζ => (ζ - z)⁻¹ * g ζ) volume) :
    cauchyT (f + g) z = cauchyT f z + cauchyT g z := by
  simp only [cauchyT_apply]
  have h : (fun ζ => (ζ - z)⁻¹ * (f + g) ζ)
      = (fun ζ => (ζ - z)⁻¹ * f ζ + (ζ - z)⁻¹ * g ζ) := by
    funext ζ; simp [mul_add]
  rw [h, integral_add hf hg, smul_add]

end Work.Beltrami
