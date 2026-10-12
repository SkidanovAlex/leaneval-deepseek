import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pinQLimDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Elementary support and summability facts for the periodisation

`wScaled ℓ h x = h x / (χ ⋆ χ)(x/ℓ)`, and `(χ ⋆ χ)` vanishes unless `‖x‖ ≤ |ℓ|`
(`χ` is supported in `ball 0 (1/2)`).  Hence `wScaled ℓ h` is supported in the ball of
radius `|ℓ|`, and its `ℓℤ³`-periodisation is a *finite* sum.  This is what makes the
`m = 0` term of the lattice sum splittable. -/

/-- `(χ ⋆ χ)(w) = 0` as soon as `‖w‖ > 1` (both factors of the integrand are supported in
`closedBall 0 (1/2)`). -/
private lemma conv3_chi_chi_aux {w : E3} (hw : 1 < ‖w‖) :
    Submission.BoseGases.conv3 chi chi w = 0 := by
  have hzero : ∀ z : E3, chi z * chi (w - z) = 0 := by
    intro z
    by_contra hz
    have h1 : chi z ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have h2 : chi (w - z) ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have hz1 : ‖z‖ ≤ 1 / 2 := le_of_not_gt (fun hb => h1 (chi_eq_zero_of_norm_gt z hb))
    have hz2 : ‖w - z‖ ≤ 1 / 2 :=
      le_of_not_gt (fun hb => h2 (chi_eq_zero_of_norm_gt (w - z) hb))
    have hsplit : w = z + (w - z) := by abel
    have hle : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      calc ‖w‖ = ‖z + (w - z)‖ := by conv_lhs => rw [hsplit]
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le z (w - z)
    linarith
  dsimp [conv3]
  simp [hzero]

/-- `convScale ℓ` vanishes outside the ball of radius `|ℓ|` (`ℓ ≠ 0`). -/
private lemma convScale_eq_zero_aux {ℓ : ℝ} (hℓ : ℓ ≠ 0) {x : E3}
    (hx : |ℓ| < ‖x‖) : Submission.BoseGases.convScale ℓ x = 0 := by
  have habs : 0 < |ℓ| := abs_pos.mpr hℓ
  have hu : 1 < ‖(ℓ⁻¹ : ℝ) • x‖ := by
    have hnorm : ‖(ℓ⁻¹ : ℝ) • x‖ = |ℓ|⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
    rw [hnorm]
    have hlt : |ℓ|⁻¹ * |ℓ| < |ℓ|⁻¹ * ‖x‖ := mul_lt_mul_of_pos_left hx (inv_pos.mpr habs)
    rw [inv_mul_cancel₀ (ne_of_gt habs)] at hlt
    exact hlt
  exact conv3_chi_chi_aux hu

/-- `wScaled ℓ h` vanishes outside the ball of radius `|ℓ|`. -/
private lemma wScaled_eq_zero_aux {ℓ : ℝ} (hℓ : ℓ ≠ 0) (h : E3 → ℝ) {x : E3}
    (hx : |ℓ| < ‖x‖) : Submission.BoseGases.wScaled ℓ h x = 0 := by
  rw [Submission.BoseGases.wScaled, convScale_eq_zero_aux hℓ hx, div_zero]

/-- The lattice sum of `wScaled ℓ h` is summable: the summand vanishes outside a finite set
of lattice points. -/
private lemma summable_wScaled_lat (ℓ : ℝ) (hℓ : ℓ ≠ 0) (h : E3 → ℝ) (z : E3) :
    Summable (fun m : Fin 3 → ℤ =>
      ((Submission.BoseGases.wScaled ℓ h (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) := by
  have habs : 0 < |ℓ| := abs_pos.mpr hℓ
  refine summable_of_hasFiniteSupport ?_
  refine (Work.BoseBoxFock.LatFourier.finite_latVec_norm_le ((‖z‖ + |ℓ|) / |ℓ|)).subset ?_
  intro m hm
  rw [Function.mem_support] at hm
  change ‖Work.BoseBoxFock.latVec m‖ ≤ (‖z‖ + |ℓ|) / |ℓ|
  have hne : Submission.BoseGases.wScaled ℓ h (z + ℓ • Work.BoseBoxFock.latVec m) ≠ 0 :=
    fun h0 => hm (by simp [h0])
  have hle : ‖z + ℓ • Work.BoseBoxFock.latVec m‖ ≤ |ℓ| :=
    le_of_not_gt (fun hlt => hne (wScaled_eq_zero_aux hℓ h hlt))
  have h2 : ‖ℓ • Work.BoseBoxFock.latVec m‖
      ≤ ‖z + ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := by
    calc ‖ℓ • Work.BoseBoxFock.latVec m‖
        = ‖(z + ℓ • Work.BoseBoxFock.latVec m) - z‖ := by congr 1; abel
      _ ≤ ‖z + ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := norm_sub_le _ _
  have h3 : ‖ℓ • Work.BoseBoxFock.latVec m‖ = |ℓ| * ‖Work.BoseBoxFock.latVec m‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  rw [h3] at h2
  rw [le_div_iff₀ habs]
  nlinarith [h2, hle]

theorem chiChi_latPer3_eq_wLoc_add {ℓ : ℝ} (hℓ : ℓ ≠ 0) (h : EuclideanSpace ℝ (Fin 3) → ℝ) (w y : EuclideanSpace ℝ (Fin 3)) :
    ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
        * Work.BoseBoxFock.latPer3 ℓ (Submission.BoseGases.wScaled ℓ h) (w - y)
      = ((Submission.BoseGases.chiScale ℓ w * Submission.BoseGases.wScaled ℓ h (w - y)
          * Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
        + ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ)
              else ((Submission.BoseGases.wScaled ℓ h (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) := by
  -- `latPer3 ℓ W (w-y) = ↑(ℓ³) · Σ_m W(w-y+ℓ•latVec m)`, and the lattice sum is a summable
  -- series whose `m = 0` term is `W(w-y)`; the factor `↑(ℓ³)` is then cancelled by `(↑(ℓ³))⁻¹`.
  have hsum := summable_wScaled_lat ℓ hℓ h (w - y)
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
  have hlc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  rw [Work.BoseBoxFock.latPer3, Work.BoseBoxFock.LatFourier.latPer, hsplit]
  simp only [Work.BoseBoxFock.LatFourier.latVec_zero, smul_zero, add_zero]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp [hlc]

end Work.BoseBoxFock
