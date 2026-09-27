import Mathlib

/-!
# `Work.KT.FP.circleIntegral_conj` — conjugation by a unit commutes with circle integrals

Conjugation by a unit of a complex Banach algebra commutes with the circle integral:

`∮ (L * f z * L⁻¹) = L * (∮ f) * L⁻¹`.

The statement is *junk-value safe*: no integrability hypothesis is imposed on `f`.  This is
handled as follows.  The map `x ↦ L * x * L⁻¹` is a continuous linear map `Φ`; the map
`x ↦ L⁻¹ * x * L` is a continuous linear left inverse of `Φ`, so `Φ` is antilipschitz.  An
antilipschitz continuous linear map commutes with (totallized) circle integrals because
`ContinuousLinearMap.integral_comp_comm'` requires no integrability assumption: antilipschitzness
forces `f` to be circle integrable exactly when `Φ ∘ f` is, so in the non-integrable case both
sides of the identity are `0`.
-/

namespace Work.KT.FP

open MeasureTheory intervalIntegral
open scoped Topology Interval

/-- A continuous linear map which is antilipschitz commutes with circle integrals, for arbitrary
center `c` and radius `r`.  No integrability hypothesis is needed (the `circleIntegral` is the
totalized interval integral): antilipschitzness makes `Φ ∘ f` circle integrable iff `f` is. -/
theorem circleIntegral_comp_clm_antilipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (Φ : E →L[ℂ] F) {K : NNReal} (hΦ : AntilipschitzWith K Φ) (f : ℂ → E) (c : ℂ) (r : ℝ) :
    circleIntegral (fun z => Φ (f z)) c r = Φ (circleIntegral f c r) := by
  rw [circleIntegral, circleIntegral]
  rw [intervalIntegral.integral_congr fun θ _ =>
    (map_smul Φ (deriv (circleMap c r) θ) (f (circleMap c r θ))).symm]
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact Φ.integral_comp_comm' hΦ _

theorem circleIntegral_conj {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (L : R) (hL : IsUnit L) (f : ℂ → R) (c : ℂ) (r : ℝ) :
    circleIntegral (fun z => L * f z * Ring.inverse L) c r
      = L * circleIntegral f c r * Ring.inverse L := by
  -- `Φ` is the continuous linear map `x ↦ L * x * L⁻¹`
  let Φ : R →L[ℂ] R := ContinuousLinearMap.mulLeftRight ℂ R L (Ring.inverse L)
  have hΦ : ∀ x : R, Φ x = L * x * Ring.inverse L := fun _ => rfl
  -- `M` is a continuous linear left inverse of `Φ`, hence `Φ` is antilipschitz
  let M : R →L[ℂ] R := ContinuousLinearMap.mulLeftRight ℂ R (Ring.inverse L) L
  have hM : ∀ x : R, M x = Ring.inverse L * x * L := fun _ => rfl
  have hMΦ : ∀ x : R, M (Φ x) = x := by
    intro x
    rw [hM, hΦ]
    rw [show Ring.inverse L * (L * x * Ring.inverse L) * L
          = (Ring.inverse L * L) * x * (Ring.inverse L * L) by noncomm_ring]
    rw [Ring.inverse_mul_cancel L hL, mul_one, one_mul]
  have hanti : AntilipschitzWith ‖M‖₊ Φ := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have h := M.lipschitz.dist_le_mul (Φ x) (Φ y)
    rwa [hMΦ x, hMΦ y] at h
  have hfun : (fun z : ℂ => L * f z * Ring.inverse L) = fun z => Φ (f z) :=
    funext fun z => (hΦ (f z)).symm
  rw [hfun, circleIntegral_comp_clm_antilipschitz Φ hanti f c r, hΦ]

end Work.KT.FP
