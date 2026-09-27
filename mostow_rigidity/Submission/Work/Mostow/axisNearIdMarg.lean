import Mathlib
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.conjCountGeodV2

/-!
# `Work.Mostow.axisNearIdMarg`

**Near-identity at one point propagates along the geodesic stratum for block isometries.**

Let `g ∈ PO (1+m) 1` preserve the standard geodesic stratum `stdTG 1 m` (`SetStabStd 1 m`) and act
trivially on it (`resStd 1 m g = 1`).  Then `g` fixes `stdTG 1 m` pointwise: by `Work.Mostow.stab_eq_blk`
it is a block isometry `g = blk 1 m 1 R`, whose displacement at `fermiW 1 m v W` is governed by the
normal rotation `R` alone (`Work.Mostow.nib_hdist_blk_le_disp`):

  `hdist (fermiW 1 m v W) (g • fermiW 1 m v W) ≤ ‖R W - W‖ ≤ rotN R · ‖W‖`.

The hypothesis `NearIdAt g u η` is at an **arbitrary** point `u`; writing `u = fermiW 1 m vu Wu`
(`Work.Mostow.nib_fermiW_surj`) the two-scale criterion `Work.Mostow.nearId_blk` (b) gives the
operator-norm bound `rotN R ≤ 4 η`.  Since every point at hyperbolic distance `≤ 1` of the stratum
has normal coordinate `‖W‖ ≤ sinh 1` (`axisNormLe`), the displacement is bounded by
`4 η · sinh 1 ≤ 4 η · 3/2 = 6 η < 48 η` everywhere, which is the claim.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### The normal coordinate of a point close to the stratum -/

/-- A point at hyperbolic distance `≤ 1` from the standard stratum has normal coordinate `≤ sinh 1`:
the distance from `fermiW 1 m v W` to the stratum `stdTG 1 m` is `arsinh ‖W‖`. -/
lemma axisNormLe (m : ℕ) {vx v : E 1} {W : E m}
    (h : hdist (fermiW 1 m vx 0) (fermiW 1 m v W) ≤ 1) : ‖W‖ ≤ Real.sinh 1 := by
  have hcosh := nib_cosh_hdist_fermiW m vx v 0 W
  rw [norm_zero, pow_two, mul_zero, add_zero, Real.sqrt_one, one_mul, inner_zero_left,
    sub_zero] at hcosh
  have hge : Real.sqrt (1 + ‖W‖ ^ 2) ≤ Real.cosh (hdist (fermiW 1 m vx 0) (fermiW 1 m v W)) := by
    rw [hcosh]
    have h1 : (1 : ℝ) ≤ Real.cosh (hdist vx v) := Real.one_le_cosh _
    have h0 : 0 ≤ Real.sqrt (1 + ‖W‖ ^ 2) := Real.sqrt_nonneg _
    nlinarith
  have hle : Real.cosh (hdist (fermiW 1 m vx 0) (fermiW 1 m v W)) ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (nib_hdist_nonneg _ _), abs_one]
    exact h
  have h1 : Real.cosh (Real.arsinh ‖W‖) ≤ Real.cosh 1 := by
    rw [Real.cosh_arsinh]
    exact le_trans hge hle
  have h2 : Real.arsinh ‖W‖ ≤ 1 := by
    have h3 := Real.cosh_le_cosh.mp h1
    rwa [abs_of_nonneg (Real.arsinh_nonneg_iff.mpr (norm_nonneg W)), abs_one] at h3
  calc ‖W‖ = Real.sinh (Real.arsinh ‖W‖) := (Real.sinh_arsinh _).symm
    _ ≤ Real.sinh 1 := Real.sinh_le_sinh.mpr h2

/-! ### The displacement bound at the stratum -/

/-- The displacement of the pure normal block `blk 1 m 1 R` at a point within distance `1` of the
stratum is `< 48 η` as soon as `rotN R ≤ 4 η`. -/
lemma axisDispLt (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (η : ℝ) (hη : 0 < η) (hrot : rotN R ≤ 4 * η)
    (vx v : E 1) (W : E m)
    (h : hdist (fermiW 1 m vx 0) (fermiW 1 m v W) ≤ 1) :
    hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W) < 48 * η := by
  have hWle : ‖W‖ ≤ Real.sinh 1 := axisNormLe m h
  have h1 : hdist (fermiW 1 m v W) (blk 1 m 1 R • fermiW 1 m v W) ≤ ‖R W - W‖ :=
    nib_hdist_blk_le_disp m hA1 hI1 hA hI R v W
  have h2 : ‖R W - W‖ ≤ rotN R * ‖W‖ := nib_apply_le_rotN m R W
  have hs : Real.sinh 1 ≤ 3 / 2 := nib_sinh_one_le_three_halves
  have h3 : rotN R * ‖W‖ ≤ (4 * η) * (3 / 2) := by
    refine mul_le_mul hrot (le_trans hWle hs) (norm_nonneg W) ?_
    linarith
  have h4 : (4 * η) * (3 / 2) < 48 * η := by linarith
  linarith

/-! ### The target -/

theorem axisNearIdMarg (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (g : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (u : Submission.Mostow.E (1 + m)) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hgS : g ∈ Submission.Mostow.SetStabStd 1 m) (hgR : Submission.Mostow.resStd 1 m g = 1) (hgN : Submission.Mostow.NearIdAt g u η) :
    ∀ x : Submission.Mostow.E (1 + m), x ∈ Submission.Mostow.stdTG 1 m → Submission.Mostow.NearIdAt g x (48 * η) := by
  -- `g` is a pure normal block: trivial on the stratum, `R` on the normal fibre
  set R : E m ≃ₗᵢ[ℝ] E m := nrmStd 1 m g with hR
  have hgblk : g = blk 1 m 1 R := by
    have h := stab_eq_blk 1 m hA1 hI1 hA hI g hgS
    rw [hgR] at h
    exact h
  have hni : NearIdAt (blk 1 m 1 R) u η := by rw [← hgblk]; exact hgN
  -- decompose the point where `g` is assumed to be near the identity
  have hni' : NearIdAt (blk 1 m 1 R)
      (fermiW 1 m ((Real.sqrt (1 + ‖nrmC 1 m u‖ ^ 2))⁻¹ • tanC 1 m u) (nrmC 1 m u)) η := by
    rwa [nib_fermiW_surj m u]
  -- the two-scale criterion `nearId_blk` (b): the normal part is `4 η`-close to the identity
  have hrot : rotN R ≤ 4 * η :=
    (nearId_blk m hA1 hI1 hA hI R _ _).2 η hni' hη1 |>.1
  intro x hx y hy
  obtain ⟨vx, hvx⟩ := hx
  have hxW : fermiW 1 m vx 0 = x := by rw [fermiW_zero_eq_coordEmb]; exact hvx
  set v : E 1 := (Real.sqrt (1 + ‖nrmC 1 m y‖ ^ 2))⁻¹ • tanC 1 m y with hv
  set W : E m := nrmC 1 m y with hW
  have hyW : fermiW 1 m v W = y := by rw [hv, hW]; exact nib_fermiW_surj m y
  have hh : hdist (fermiW 1 m vx 0) (fermiW 1 m v W) ≤ 1 := by rw [hxW, hyW]; exact hy
  have hkey := axisDispLt m hA1 hI1 hA hI R η hη hrot vx v W hh
  rw [hyW, ← hgblk] at hkey
  exact hkey

end

end Work.Mostow
