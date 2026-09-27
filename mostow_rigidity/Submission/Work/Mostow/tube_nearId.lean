import Mathlib
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.disp_blk
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.tubeNrmCTransport
import Submission.Work.Mostow.blkDispFermi

/-!
# `tube_nearId`: the block isometry is near the identity on the tube

Let `R : E m ≃ₗᵢ[ℝ] E m` and let `h = blk j m 1 R` be the block isometry acting by the identity on
the standard stratum `E j ↪ E (j+m)` and by `R` on the normal fibre (Fermi coordinates).  Then `h`
moves every point within hyperbolic distance `1` of the tube `{u | ‖nrmC j m u‖ ≤ sinh ρ}` of radius
`ρ` about the stratum by less than `2 * sinh (ρ+1) * rotN R`.

The proof is a two-line computation once the normal coordinates are in place.  Write a point
`x = fermi j m v w` in Fermi coordinates.  Then

* the distance from `x` to the stratum is `‖w‖`, i.e. `‖nrmC j m x‖ = sinh ‖w‖`, and the distance
  to the stratum is 1-Lipschitz; hence a point within distance `1` of the tube of radius `ρ` has
  `‖nrmC j m x‖ ≤ sinh (ρ+1)`, i.e. `sinh ‖w‖ ≤ sinh (ρ+1)` (`tubeNrmCTransport`);
* `blk j m 1 R` fixes the stratum pointwise, so `h x = fermi j m v (R w)` and
  `sinh (hdist x (h x) / 2) = sinh ‖w‖ * ‖R ŵ - ŵ‖ / 2` where `ŵ = ‖w‖⁻¹ • w`
  (`blkDispFermi`, a corollary of the exact displacement formula `disp_blk`);
* `‖R ŵ - ŵ‖ ≤ rotN R` by definition of the operator-norm distance `rotN R`, and `‖ŵ‖ ≤ 1`.

So `sinh (hdist x (h x)/2) ≤ sinh (ρ+1) * rotN R / 2 ≤ η/4`, and since `D/2 ≤ sinh (D/2)`
(`Real.self_le_sinh_iff`) we get `hdist x (h x) ≤ η/2 < η`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### Elementary `sinhc` bookkeeping -/

/-- `sinhc` is nonnegative on the nonnegative reals. -/
private theorem tn_sinhc_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ sinhc s := by
  rw [sinhc]
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hs) hs

/-- `sinhc s * s = sinh s` in the form `s = ‖w‖`: the "removable" prefactor of `fermi`. -/
private theorem tn_sinhc_mul_norm {m : ℕ} (w : E m) :
    sinhc ‖w‖ * ‖w‖ = Real.sinh ‖w‖ := by
  rw [sinhc]
  by_cases h : ‖w‖ = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [div_mul_cancel₀ _ h]

/-- The normal coordinate of a Fermi point is `sinh` of its normal parameter: the hyperbolic
distance from `fermi k m v w` to the standard stratum is `‖w‖`. -/
private theorem tn_nrmC_fermi_norm (k m : ℕ) (v : E k) (w : E m) :
    ‖nrmC k m (fermi k m v w)‖ = Real.sinh ‖w‖ := by
  rw [nib_nrmC_fermi, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (tn_sinhc_nonneg (norm_nonneg w)), tn_sinhc_mul_norm]

/-! ### The main statement -/

theorem tube_nearId (j m : ℕ) (hAj : Submission.Mostow.POActionProp j) (hIj : Submission.Mostow.HypIsometryProp j)
    (hA : Submission.Mostow.POActionProp (j + m)) (hI : Submission.Mostow.HypIsometryProp (j + m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (ρ η : ℝ) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (h : 2 * Real.sinh (ρ + 1) * Submission.Mostow.rotN R ≤ η) :
    ∀ u : Submission.Mostow.E (j + m), u ∈ Submission.Mostow.tube j m ρ → Submission.Mostow.NearIdAt (Submission.Mostow.blk j m 1 R) u η := by
  intro u hu x hux
  -- Fermi coordinates of the test point `x`
  set v := (fermiInv j m x).1 with hv
  set w := (fermiInv j m x).2 with hw
  have hx : fermi j m v w = x := (fermi_inv j m).2.1 x
  -- (1) the normal coordinate of `x` is transported from the tube
  have hsinhw : Real.sinh ‖w‖ ≤ Real.sinh (ρ + 1) := by
    have hB : ‖nrmC j m x‖ ≤ Real.sinh (ρ + 1) := tubeNrmCTransport hI hρ hu hux
    rw [← hx, tn_nrmC_fermi_norm] at hB
    exact hB
  -- (2) the normal part `ŵ = ‖w‖⁻¹ • w` is a contraction vector for `R`
  have hX : ‖R (‖w‖⁻¹ • w) - ‖w‖⁻¹ • w‖ ≤ rotN R := by
    have h1 := nib_apply_le_rotN m R (‖w‖⁻¹ • w)
    have h2 : ‖(‖w‖⁻¹ : ℝ) • w‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w)]
      by_cases hw0 : w = 0
      · simp [hw0]
      · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
        rw [inv_mul_cancel₀ hpos.ne']
    have hrotN : 0 ≤ rotN R := by rw [rotN]; exact norm_nonneg _
    have h3 : rotN R * ‖(‖w‖⁻¹ : ℝ) • w‖ ≤ rotN R := by
      have h4 := mul_le_mul_of_nonneg_left h2 hrotN
      rwa [mul_one] at h4
    linarith
  -- (3) the exact displacement formula at a Fermi point
  have hdisp := blkDispFermi j m hAj hIj hA hI R v w
  have hD : Real.sinh (hdist x (blk j m 1 R • x) / 2) ≤ Real.sinh (ρ + 1) * rotN R / 2 := by
    have heq : hdist x (blk j m 1 R • x)
        = hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) := by rw [hx]
    rw [heq, hdisp]
    have hsw : 0 ≤ Real.sinh ‖w‖ := Real.sinh_nonneg_iff.mpr (norm_nonneg w)
    have hrotN : 0 ≤ rotN R := by rw [rotN]; exact norm_nonneg _
    have h1 : Real.sinh ‖w‖ * ‖R (‖w‖⁻¹ • w) - ‖w‖⁻¹ • w‖ / 2
        ≤ Real.sinh ‖w‖ * rotN R / 2 := by
      have h5 := mul_le_mul_of_nonneg_left hX hsw
      linarith
    have h2 : Real.sinh ‖w‖ * rotN R / 2 ≤ Real.sinh (ρ + 1) * rotN R / 2 := by
      have hrotN2 : 0 ≤ rotN R / 2 := by linarith
      have h5 := mul_le_mul_of_nonneg_right hsinhw hrotN2
      linarith
    linarith
  -- (4) `D/2 ≤ sinh (D/2)`, and the hypothesis bounds `sinh (ρ+1) * rotN R / 2` by `η/4`
  have hDnn : 0 ≤ hdist x (blk j m 1 R • x) := hI.1 x _
  have hhalf : hdist x (blk j m 1 R • x) / 2 ≤ Real.sinh (hdist x (blk j m 1 R • x) / 2) :=
    Real.self_le_sinh_iff.mpr (by linarith)
  have hη4 : Real.sinh (ρ + 1) * rotN R / 2 ≤ η / 4 := by linarith
  linarith

end

end Work.Mostow
