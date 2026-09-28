import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.ball_count_schmidt
import Submission.Work.HP.BCSToE

/-!
# `Work.HP.BCS.lift_bound`

Given integer vectors `u ≠ 0` and `y` and an integer `m` such that the real number
`⟨y,u⟩/‖u‖²` is within `1/2` of `m`, the vector `y - m u` is not much longer than the
component of `y` orthogonal to `u`: writing `λ = ⟨y,u⟩/‖u‖²` and using
`projScale u y = ‖u‖² (y - λ u)`,

`‖y - m u‖ ≤ ‖y - λ u‖ + |λ - m| ‖u‖ ≤ ‖projScale u y‖/‖u‖² + ‖u‖/2`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.BCS

/-! ## Two elementary bridges between `dotZ` and the Euclidean inner product -/

/-- The Euclidean inner product of `toEZ v`, `toEZ w` is the integer `dotZ v w`. -/
lemma inner_toE_dotZ {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    inner ℝ (Work.HP.toEZ v) (Work.HP.toEZ w) = ((Work.HP.dotZ v w : ℤ) : ℝ) := by
  simp [Work.HP.toEZ, Work.HP.dotZ_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    mul_comm]

/-- `‖toEZ u‖²` is the integer `dotZ u u`. -/
lemma norm_toE_sq_dotZ {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℤ) :
    ‖Work.HP.toEZ u‖ ^ 2 = ((Work.HP.dotZ u u : ℤ) : ℝ) := by
  rw [← Work.HP.eNorm_sq_eq u, Work.HP.norm_toEZ]

/-! ## The scaled projection -/

/-- `toEZ (projScale u y)` is `‖u‖²` times the orthogonal projection of `toEZ y` onto `u^⊥`. -/
lemma toE_projScale {ι : Type*} [Fintype ι] [DecidableEq ι] (u y : ι → ℤ) (hu : u ≠ 0) :
    Work.HP.toEZ (Work.HP.projScale u y)
      = (Work.HP.eNorm u) ^ 2 • Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ y) := by
  have hA : ‖Work.HP.toEZ u‖ ^ 2 ≠ 0 := by
    rw [Work.HP.norm_toEZ]
    exact pow_ne_zero 2 (ne_of_gt (Work.HP.eNorm_pos_of_ne_zero hu))
  rw [← Work.HP.norm_toEZ u, Work.HP.projScale_apply]
  change Work.HP.toEHom (Work.HP.dotZ u u • y - Work.HP.dotZ y u • u) = _
  rw [map_sub, map_smul, map_smul]
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ]
  rw [show ((Work.HP.dotZ u u : ℤ) : ℝ) = ‖Work.HP.toEZ u‖ ^ 2 from
    (by rw [← Work.HP.eNorm_sq_eq u, Work.HP.norm_toEZ])]
  rw [show ((Work.HP.dotZ y u : ℤ) : ℝ) = inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u) from
    (by rw [inner_toE_dotZ])]
  rw [Work.HP.projU_apply, smul_sub, smul_smul,
    show ‖Work.HP.toEZ u‖ ^ 2 *
          ((‖Work.HP.toEZ u‖ ^ 2)⁻¹ * inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u))
        = inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u) from by
      rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]]
  simp only [Work.HP.toEHom_apply]

/-- The Euclidean norm of `projScale u y` is `‖u‖²` times the norm of the orthogonal
projection of `y` onto `u^⊥`. -/
lemma eNorm_projScale {ι : Type*} [Fintype ι] [DecidableEq ι] (u y : ι → ℤ) (hu : u ≠ 0) :
    Work.HP.eNorm (Work.HP.projScale u y)
      = (Work.HP.eNorm u) ^ 2 * ‖Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ y)‖ := by
  rw [← Work.HP.norm_toEZ (Work.HP.projScale u y), toE_projScale u y hu, norm_smul,
    Real.norm_of_nonneg (by positivity)]

/-! ## The triangle-inequality step -/

/-- If `⟨y,u⟩/‖u‖²` is within `1/2` of the integer `m`, then `y - m u` is longer than the
orthogonal component of `y` by at most `‖u‖/2`. -/
lemma norm_sub_smul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u y : ι → ℤ) (m : ℤ)
    (hm : |inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2 - (m : ℝ)| ≤ 1 / 2) :
    ‖Work.HP.toEZ y - (m : ℝ) • Work.HP.toEZ u‖
      ≤ ‖(Work.HP.projU (Work.HP.toEZ u)) (Work.HP.toEZ y)‖ + ‖Work.HP.toEZ u‖ / 2 := by
  set v := Work.HP.toEZ u with hv
  set x := Work.HP.toEZ y with hx
  have hgen : ∀ s : ℝ, x + s • v = (Work.HP.projU v) x + (inner ℝ x v / ‖v‖ ^ 2 + s) • v := by
    intro s
    rw [Work.HP.projU_apply, div_eq_inv_mul]
    module
  have key : x - (m : ℝ) • v
      = (Work.HP.projU v) x + (inner ℝ x v / ‖v‖ ^ 2 - (m : ℝ)) • v := by
    have h := hgen (-(m : ℝ))
    rwa [show x + (-(m : ℝ)) • v = x - (m : ℝ) • v from by rw [neg_smul, sub_eq_add_neg],
         show inner ℝ x v / ‖v‖ ^ 2 + (-(m : ℝ)) = inner ℝ x v / ‖v‖ ^ 2 - (m : ℝ) from by
           ring] at h
  have hb : |inner ℝ x v / ‖v‖ ^ 2 - (m : ℝ)| ≤ 1 / 2 := by rw [hx, hv]; exact hm
  calc ‖x - (m : ℝ) • v‖
      = ‖(Work.HP.projU v) x + (inner ℝ x v / ‖v‖ ^ 2 - (m : ℝ)) • v‖ := by rw [key]
    _ ≤ ‖(Work.HP.projU v) x‖ + ‖(inner ℝ x v / ‖v‖ ^ 2 - (m : ℝ)) • v‖ := norm_add_le _ _
    _ = ‖(Work.HP.projU v) x‖ + |inner ℝ x v / ‖v‖ ^ 2 - (m : ℝ)| * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖(Work.HP.projU v) x‖ + (1 / 2) * ‖v‖ := by
        have := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
        linarith
    _ = ‖(Work.HP.projU v) x‖ + ‖v‖ / 2 := by ring

/-! ## The main bound -/

theorem lift_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u y : ι → ℤ) (hu : u ≠ 0) (m : ℤ)
    (hm : |inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2 - (m : ℝ)| ≤ 1 / 2) :
    Work.HP.eNorm (y - m • u) ≤
      Work.HP.eNorm (Work.HP.projScale u y) / (Work.HP.eNorm u) ^ 2 + Work.HP.eNorm u / 2 := by
  have hne : (Work.HP.eNorm u) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (Work.HP.eNorm_pos_of_ne_zero hu))
  have hstep := norm_sub_smul_le u y m hm
  have h1 : Work.HP.toEZ (y - m • u) = Work.HP.toEZ y - (m : ℝ) • Work.HP.toEZ u := by
    change Work.HP.toEHom (y - m • u) = _
    rw [map_sub, map_smul, ← Int.cast_smul_eq_zsmul ℝ]
    simp only [Work.HP.toEHom_apply]
  have h2 : ‖(Work.HP.projU (Work.HP.toEZ u)) (Work.HP.toEZ y)‖
      = Work.HP.eNorm (Work.HP.projScale u y) / (Work.HP.eNorm u) ^ 2 := by
    rw [eNorm_projScale u y hu, mul_div_cancel_left₀ _ hne]
  calc Work.HP.eNorm (y - m • u) = ‖Work.HP.toEZ (y - m • u)‖ := (Work.HP.norm_toEZ _).symm
    _ = ‖Work.HP.toEZ y - (m : ℝ) • Work.HP.toEZ u‖ := by rw [h1]
    _ ≤ ‖(Work.HP.projU (Work.HP.toEZ u)) (Work.HP.toEZ y)‖ + ‖Work.HP.toEZ u‖ / 2 := hstep
    _ = Work.HP.eNorm (Work.HP.projScale u y) / (Work.HP.eNorm u) ^ 2 + Work.HP.eNorm u / 2 := by
        rw [h2, Work.HP.norm_toEZ u]

end Work.HP.BCS
