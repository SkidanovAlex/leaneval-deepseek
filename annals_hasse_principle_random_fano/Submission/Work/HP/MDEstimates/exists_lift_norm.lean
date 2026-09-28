import Mathlib
import Submission.Work.HP.BCS.lift_bound
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.ball_count_schmidt
import Submission.Work.HP.BCSToE

/-!
# `Work.HP.MDEstimates.exists_lift_norm`

Any element `y` of the image of the scaled projection `projScale u : L → L` (which is
`‖u‖²` times the orthogonal projection onto `u^⊥`) admits a lift `x ∈ L` with
`projScale u x = y` whose squared norm exceeds `‖y‖²/‖u‖⁴` by at most `‖u‖²/4`.

Indeed, if `x₀ ∈ L` satisfies `projScale u x₀ = y`, then every `x₀ - m u` (`m : ℤ`) is
another lift, since `projScale u u = 0`.  Writing `r = ⟪x₀,u⟫/‖u‖²` we have the orthogonal
decomposition `x₀ = P x₀ + r u` with `P = projU (toEZ u)`, whence
`x₀ - m u = P x₀ + (r - m) u`, and `P x₀ = y/‖u‖²`.  Choosing `m` a nearest integer to `r`
gives `‖x₀ - m u‖² = ‖y‖²/‖u‖⁴ + (r - m)² ‖u‖² ≤ ‖y‖²/‖u‖⁴ + ‖u‖²/4`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.MDEstimates

theorem exists_lift_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    {y : ι → ℤ} (hy : y ∈ Submodule.map (Work.HP.projScale u) L) :
    ∃ x ∈ L, Work.HP.projScale u x = y ∧
      Work.HP.eNorm x ^ 2 ≤
        Work.HP.eNorm y ^ 2 / Work.HP.eNorm u ^ 4 + Work.HP.eNorm u ^ 2 / 4 := by
  obtain ⟨x0, hx0L, hx0⟩ := Submodule.mem_map.mp hy
  have hu_norm_pos : 0 < ‖Work.HP.toEZ u‖ := by
    rw [Work.HP.norm_toEZ]; exact Work.HP.eNorm_pos_of_ne_zero hu0
  have hu_norm_ne : ‖Work.HP.toEZ u‖ ≠ 0 := ne_of_gt hu_norm_pos
  set r : ℝ := (‖Work.HP.toEZ u‖ ^ 2)⁻¹ * inner ℝ (Work.HP.toEZ x0) (Work.HP.toEZ u) with hr
  set m : ℤ := ⌊r + 1 / 2⌋ with hmdef
  have hm_cl : |r - (m : ℝ)| ≤ 1 / 2 := by
    have h1 : (m : ℝ) ≤ r + 1 / 2 := by rw [hmdef]; exact Int.floor_le (r + 1 / 2)
    have h2 : r + 1 / 2 < (m : ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one (r + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  refine ⟨x0 - m • u, L.sub_mem hx0L (L.smul_mem m hu), ?_, ?_⟩
  · rw [map_sub, map_smul]
    have hpu : Work.HP.projScale u u = 0 := by simp [Work.HP.projScale_apply]
    rw [hpu, smul_zero, sub_zero]; exact hx0
  · have hdec' : Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0)
        = Work.HP.toEZ x0 - r • Work.HP.toEZ u := by
      rw [Work.HP.projU_apply, ← hr]
    have htoe : Work.HP.toEZ (x0 - m • u)
        = Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0) + (r - (m : ℝ)) • Work.HP.toEZ u := by
      have hz : Work.HP.toEZ (x0 - m • u)
          = Work.HP.toEZ x0 - (m : ℝ) • Work.HP.toEZ u := by
        change Work.HP.toEHom (x0 - m • u) = _
        rw [map_sub, map_smul, Work.HP.toEHom_apply, Work.HP.toEHom_apply]
        rw [← Int.cast_smul_eq_zsmul ℝ]
      rw [hz, hdec']
      module
    have hpy : ‖Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0)‖
        = ‖Work.HP.toEZ y‖ / ‖Work.HP.toEZ u‖ ^ 2 := by
      have h := Work.HP.BCS.toE_projScale u x0 hu0
      rw [hx0] at h
      have h2 : ‖Work.HP.toEZ y‖
          = Work.HP.eNorm u ^ 2 * ‖Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0)‖ := by
        rw [h, norm_smul, Real.norm_of_nonneg (by positivity)]
      rw [h2, ← Work.HP.norm_toEZ u, mul_div_cancel_left₀ _ (pow_ne_zero 2 hu_norm_ne)]
    have herr1 : ((r - (m : ℝ)) * ‖Work.HP.toEZ u‖) ^ 2 ≤ ‖Work.HP.toEZ u‖ ^ 2 / 4 := by
      rw [mul_pow]
      have h1 : (r - (m : ℝ)) ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_abs (r - (m : ℝ)), abs_nonneg (r - (m : ℝ))]
      calc (r - (m : ℝ)) ^ 2 * ‖Work.HP.toEZ u‖ ^ 2
          ≤ (1 / 4) * ‖Work.HP.toEZ u‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = ‖Work.HP.toEZ u‖ ^ 2 / 4 := by ring
    have herr2 : (‖Work.HP.toEZ y‖ / ‖Work.HP.toEZ u‖ ^ 2) ^ 2
        = ‖Work.HP.toEZ y‖ ^ 2 / ‖Work.HP.toEZ u‖ ^ 4 := by
      rw [div_pow]; congr 1; ring
    rw [← Work.HP.norm_toEZ (x0 - m • u), ← Work.HP.norm_toEZ y, ← Work.HP.norm_toEZ u]
    rw [htoe, Work.HP.norm_sq_add_smul', hpy, herr2]
    linarith [herr1]

end Work.HP.MDEstimates
