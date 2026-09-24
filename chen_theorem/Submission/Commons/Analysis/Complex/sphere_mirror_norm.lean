import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Complex

/-!
The "sphere mirror" distance identity: if `m = a + R² · conj(u−a)⁻¹` is the
mirror (inverse) of `u` with respect to the circle `{z : ‖z − a‖ = R}`, then for
every `z` on that circle,

  ‖z − m‖ · ‖u − a‖ = ‖z − u‖ · R.

Proof sketch: with `x = z − a` and `w = u − a` (so `‖x‖ = R`, `w ≠ 0`), the
mirror satisfies `m − a = (x · conj x) · conj(w)⁻¹ = x · conj(1 − x·w⁻¹)`, hence
`‖z − m‖ = ‖x‖·‖x − w‖/‖w‖` and the identity follows by multiplying by `‖w‖`.
-/

/-- Core identity: for `w ≠ 0`, inverting `w` about the circle of radius `‖x‖`
centered at the origin satisfies `‖x − m‖·‖w‖ = ‖x − w‖·‖x‖`, where
`m = (x · conj x) · conj(w)⁻¹`. -/
lemma mirror_norm_core (x w : ℂ) (hw : w ≠ 0) :
    ‖x - (x * (starRingEnd ℂ) x) * ((starRingEnd ℂ) w)⁻¹‖ * ‖w‖ = ‖x - w‖ * ‖x‖ := by
  have hfac : x - (x * (starRingEnd ℂ) x) * ((starRingEnd ℂ) w)⁻¹ =
      x * (starRingEnd ℂ) (1 - x * w⁻¹) := by
    calc
      x - (x * (starRingEnd ℂ) x) * ((starRingEnd ℂ) w)⁻¹
          = x * (1 - (starRingEnd ℂ) x * ((starRingEnd ℂ) w)⁻¹) := by ring
      _ = x * (1 - (starRingEnd ℂ) (x * w⁻¹)) := by
        congr 1
        have hsw : (starRingEnd ℂ) x * ((starRingEnd ℂ) w)⁻¹ =
            (starRingEnd ℂ) (x * w⁻¹) := by
          calc
            (starRingEnd ℂ) x * ((starRingEnd ℂ) w)⁻¹
                = (starRingEnd ℂ) x * (starRingEnd ℂ) (w⁻¹) := by rw [map_inv₀]
            _ = (starRingEnd ℂ) (x * w⁻¹) := by rw [map_mul]
        rw [hsw]
      _ = x * (starRingEnd ℂ) (1 - x * w⁻¹) := by
        congr 1
        calc
          1 - (starRingEnd ℂ) (x * w⁻¹)
              = (starRingEnd ℂ) 1 - (starRingEnd ℂ) (x * w⁻¹) := by rw [map_one]
          _ = (starRingEnd ℂ) (1 - x * w⁻¹) := by rw [← map_sub]
  have hsub : 1 - x * w⁻¹ = (w - x) * w⁻¹ := by
    calc
      1 - x * w⁻¹ = w * w⁻¹ - x * w⁻¹ := by rw [← mul_inv_cancel₀ hw]
      _ = (w - x) * w⁻¹ := by ring
  have hnorm : ‖x - (x * (starRingEnd ℂ) x) * ((starRingEnd ℂ) w)⁻¹‖ =
      ‖x‖ * ‖x - w‖ * (‖w‖)⁻¹ := by
    calc
      ‖x - (x * (starRingEnd ℂ) x) * ((starRingEnd ℂ) w)⁻¹‖
          = ‖x * (starRingEnd ℂ) (1 - x * w⁻¹)‖ := by rw [hfac]
      _ = ‖x‖ * ‖(starRingEnd ℂ) (1 - x * w⁻¹)‖ := by rw [norm_mul]
      _ = ‖x‖ * ‖1 - x * w⁻¹‖ := by rw [Complex.norm_conj]
      _ = ‖x‖ * ‖(w - x) * w⁻¹‖ := by rw [hsub]
      _ = ‖x‖ * (‖w - x‖ * ‖w⁻¹‖) := by rw [norm_mul]
      _ = ‖x‖ * (‖w - x‖ * (‖w‖)⁻¹) := by rw [norm_inv]
      _ = ‖x‖ * (‖x - w‖ * (‖w‖)⁻¹) := by rw [norm_sub_rev]
      _ = ‖x‖ * ‖x - w‖ * (‖w‖)⁻¹ := by ring
  have hw0 : ‖w‖ ≠ 0 := by
    intro h
    exact hw (norm_eq_zero.mp h)
  calc
    ‖x - (x * (starRingEnd ℂ) x) * ((starRingEnd ℂ) w)⁻¹‖ * ‖w‖
        = (‖x‖ * ‖x - w‖ * (‖w‖)⁻¹) * ‖w‖ := by rw [hnorm]
    _ = ‖x - w‖ * ‖x‖ := by
      field_simp [hw0]

/-- **Sphere-mirror norm identity**: if `m = a + R²·conj(u−a)⁻¹` is the mirror
of `u` with respect to the circle centred at `a` of radius `R`, and `z` lies on
that circle, then `‖z − m‖·‖u − a‖ = ‖z − u‖·R`. -/
theorem sphere_mirror_norm {a u z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z - a‖ = R)
    (hu : u ≠ a) :
    ‖z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹)‖ * ‖u - a‖ =
      ‖z - u‖ * R := by
  have hw0 : u - a ≠ 0 := by exact sub_ne_zero.mpr hu
  have hcore := mirror_norm_core (z - a) (u - a) hw0
  have hR2 : ((R * R : ℝ) : ℂ) = (z - a) * (starRingEnd ℂ) (z - a) := by
    calc
      ((R * R : ℝ) : ℂ) = ((‖z - a‖ * ‖z - a‖ : ℝ) : ℂ) := by rw [← hz]
      _ = ((‖z - a‖ ^ 2 : ℝ) : ℂ) := by congr 1; rw [← pow_two]
      _ = ((Complex.normSq (z - a) : ℝ) : ℂ) := by congr 1; rw [Complex.sq_norm]
      _ = (z - a) * (starRingEnd ℂ) (z - a) := by rw [← Complex.mul_conj]
  have hfac : z - (a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹) =
      (z - a) - ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹ := by ring
  rw [hfac]
  rw [hR2]
  rw [hcore]
  have hsubring : (z - a) - (u - a) = z - u := by ring
  rw [hsubring]
  rw [hz]

end Commons.Analysis.Complex