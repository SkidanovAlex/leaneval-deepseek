/-
# The tiling bump `arcChi` is the Fourier transform of a Schwartz function

`Work.KMTAreas.A4.arcChi` (from `Work.KMTAreas.A4.lip2ArcDefs`) is the *tiling bump*
`arcChi = arcBump0 / arcTileH`, where `arcBump0 = lipSchChi (4·/3)` is the rescaled bump
(`1` on `[-3/8,3/8]`, `0` off `(-3/4,3/4)`) and `arcTileH u = Σ_m arcBump0 (u - m)` is its
`1`-periodization.  This file proves the four facts that make it usable as a partition of unity
of the frequency circle, with the smoothness/positivity of the periodization supplied by the
companion files `arcTileH_contDiff`, `arcTileH_ne_zero`, `arcTileH_periodic`:

* `arcTilingBump_arcTileH_zero  : arcTileH 0 = 1`;
* `arcTilingBump_arcChi_eq_zero  : 3/4 ≤ |u| → arcChi u = 0`   (support in `(-3/4,3/4)`);
* `arcTilingBump_arcChi_zero     : arcChi 0 = 1`;
* `arcTilingBump_tiling          : Σ_m arcChi (u - m) = 1`      (the exact tiling);
* `arcTilingBump_arcChi_contDiff`, `arcTilingBump_arcChi_hasCompactSupport`: `arcChi` is a
  compactly supported smooth function, hence a Schwartz function `arcChiS`, and its inverse
  Fourier transform `arcPsi` has `𝓕 arcPsi = arcChi`.

The target `arcTilingBump` assembles them.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.arcTileH_periodic
import Submission.Work.KMTAreas.A4.arcTileH_contDiff
import Submission.Work.KMTAreas.A4.arcTileH_ne_zero

set_option autoImplicit false

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

/-- A nonzero integer has `|(m : ℝ)| ≥ 1`. -/
theorem arcTilingBump_one_le_abs_intCast (m : ℤ) (hm : m ≠ 0) : (1 : ℝ) ≤ |((m : ℝ))| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hm

/-- At the origin only the `m = 0` term of the periodization survives: `arcTileH 0 = 1`. -/
theorem arcTilingBump_arcTileH_zero : arcTileH 0 = 1 := by
  rw [arcTileH, tsum_eq_sum (s := {0}) ?_]
  · simp [arcBump0_zero]
  · intro m hm
    rw [Finset.mem_singleton] at hm
    rw [zero_sub]
    refine arcBump0_eq_zero_of_one_le _ ?_
    rw [abs_neg]
    exact arcTilingBump_one_le_abs_intCast m hm

/-- `arcChi` is supported in `(-3/4, 3/4)`. -/
theorem arcTilingBump_arcChi_eq_zero (u : ℝ) (hu : 3 / 4 ≤ |u|) : arcChi u = 0 := by
  rw [arcChi, arcBump0_eq_zero u hu, zero_div]

/-- `arcChi 0 = 1`. -/
theorem arcTilingBump_arcChi_zero : arcChi 0 = 1 := by
  rw [arcChi, arcBump0_zero, arcTilingBump_arcTileH_zero, div_one]

/-- The exact tiling identity `Σ_m arcChi (u - m) = 1`. -/
theorem arcTilingBump_tiling (u : ℝ) : ∑' m : ℤ, arcChi (u - (m : ℝ)) = 1 := by
  have h1 : ∀ m : ℤ, arcChi (u - (m : ℝ)) = (arcTileH u)⁻¹ * arcBump0 (u - (m : ℝ)) := by
    intro m
    rw [arcChi, arcTileH_periodic u m, div_eq_inv_mul]
  rw [tsum_congr h1, tsum_mul_left]
  rw [show (∑' m : ℤ, arcBump0 (u - (m : ℝ))) = arcTileH u from rfl,
    inv_mul_cancel₀ (arcTileH_ne_zero u)]

/-- `arcChi` is smooth (a product of the smooth bump with the inverse of the nowhere vanishing
smooth periodization). -/
theorem arcTilingBump_arcChi_contDiff : ContDiff ℝ (⊤ : ℕ∞) arcChi := by
  have hfun : arcChi = fun u : ℝ => arcBump0 u * (arcTileH u)⁻¹ := by
    funext u
    rw [arcChi, div_eq_mul_inv]
  rw [hfun]
  exact arcBump0_contDiff.mul (ContDiff.inv arcTileH_contDiff arcTileH_ne_zero)

/-- `arcChi` has compact support. -/
theorem arcTilingBump_arcChi_hasCompactSupport : HasCompactSupport arcChi := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) (3 / 4)) ?_
  intro u hu
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
  by_contra h
  rw [not_le] at h
  exact hu (arcTilingBump_arcChi_eq_zero u (le_of_lt h))

/-- The tiling bump `arcChi`, packaged as a Schwartz function. -/
noncomputable def arcChiS : SchwartzMap ℝ ℂ :=
  arcTilingBump_arcChi_hasCompactSupport.toSchwartzMap arcTilingBump_arcChi_contDiff

theorem arcChiS_apply (u : ℝ) : arcChiS u = arcChi u := rfl

/-- The inverse Fourier transform of the tiling bump: the smoothing weight whose Fourier
transform is exactly `arcChi`. -/
noncomputable def arcPsi : Work.Analysis.InverseTheory.SchwartzR := 𝓕⁻ arcChiS

theorem arcPsi_fourier : 𝓕 arcPsi = arcChiS :=
  FourierInvPair.fourier_fourierInv_eq arcChiS

theorem arcTilingBump : ∃ ψ : Work.Analysis.InverseTheory.SchwartzR, (∀ u : ℝ, Work.KMTAreas.A4.schFT ψ u = Work.KMTAreas.A4.arcChi u) ∧ (∀ u : ℝ, ∑' m : ℤ, Work.KMTAreas.A4.arcChi (u - (m : ℝ)) = 1) ∧ (∀ u : ℝ, 3 / 4 ≤ |u| → Work.KMTAreas.A4.arcChi u = 0) ∧ Work.KMTAreas.A4.arcChi 0 = 1 := by
  refine ⟨arcPsi, ?_, arcTilingBump_tiling, arcTilingBump_arcChi_eq_zero,
    arcTilingBump_arcChi_zero⟩
  intro u
  show (𝓕 arcPsi) u = arcChi u
  rw [arcPsi_fourier]
  rfl

end Work.KMTAreas.A4
