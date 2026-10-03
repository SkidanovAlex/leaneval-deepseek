import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.coverCone.cover_cone_wedge
import Submission.Work.Parab.coverCone.inv_neg_norm_re
import Submission.Work.Parab.coordData.cover_data
import Submission.Work.Parab.coordData.qleft_close_vertex
import Submission.Work.Parab.coordData.exists_nine_log_add_lt
import Submission.Work.Parab.coordData.norm_Phi_sub_id_le

namespace Work.Parab.coordData

/-- The two descriptions of the cone angle agree: `π/2 + π/12 = 2π/3 - π/12`. -/
private lemma cone_angle_range : Real.pi / 2 + Real.pi / 12 = 2 * Real.pi / 3 - Real.pi / 12 := by
  ring

/-- `tau0` is an involution (with the junk value `tau0 0 = 0`). -/
private lemma tau0_tau0_aux (ζ : ℂ) : MandelDim.tau0 (MandelDim.tau0 ζ) = ζ := by
  simp only [MandelDim.tau0]
  by_cases h : ζ = 0
  · rw [h]; simp
  · field_simp

/-- **The covering of the repelling cone, with a prescribed vertex.**  This is
`Work.Parab.coordData.cover_data` (equivalently `Work.Parab.coverCone.cover_cone_wedge`) with the
sector vertex `ξ` under the control of the caller: for *every* `ξ : ℝ` there is `ρ > 0` such that
every small `z` in the cone `|arg z| ≤ π/2 + π/12` has `τ₀ z ∈ L` and `Φ (τ₀ z) ∈ QLeft ξ`.

The geometry is robust: `Φ (τ₀ z) = τ₀ z + O(log ‖τ₀ z‖)` is asymptotically `-1/z`, whose
direction lies in `[5π/12, 19π/12]`, i.e. at distance at least `π/12` from the forbidden cone
`{|arg| ≤ π/3}`; and the vertex shift `ξ` is negligible compared with `|1/z|` once `‖z‖` is small
enough (how small depends on `|ξ|`).  So the proof is that of `cover_cone_wedge` with the final
"membership in `QLeft 1`" step replaced by a vertex-perturbation estimate. -/
theorem cover_data_range {Φ : ℂ → ℂ} {L : Set ℂ} {M₀ M₁ : ℝ} {a b : ℂ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hL : ∀ ζ : ℂ, ζ.re < -M₀ → ζ ∈ L)
    (hLim : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L)
    (hasym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
      ‖Φ ζ - (ζ - a * Complex.log (-ζ) - b)‖ < ε) :
    ∀ ξ : ℝ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ →
      |z.arg| ≤ Real.pi / 2 + Real.pi / 12 →
        MandelDim.tau0 z ∈ L ∧ Φ (MandelDim.tau0 z) ∈ MandelDim.QLeft ξ := by
  intro ξ
  -- the covering with a *fixed* (large) vertex `ξ₀`, from `cover_cone_wedge`
  obtain ⟨ξ₀, _hξ₀, ρ₀, hρ₀, hcov⟩ := Work.Parab.coverCone.cover_cone_wedge (Φ := Φ) (L := L)
    (M₀ := M₀) (M₁ := M₁) (a := a) (b := b) hM₀ hM₁ hL hLim hasym
  -- the asymptotic hypothesis at `ε = 1`
  obtain ⟨R₁, hR₁⟩ := hasym 1 one_pos
  -- the threshold beyond which `‖ζ‖ / 9` dominates the error term `E(ζ) + |ξ|`
  obtain ⟨N, hN⟩ := exists_nine_log_add_lt ‖a‖ (1 + |ξ| + ‖b‖) (norm_nonneg a) (by positivity)
  set M : ℝ := max N (max R₁ 1) with hMdef
  have hMN : N ≤ M := le_max_left _ _
  have hMR : R₁ ≤ M := le_trans (le_max_left R₁ 1) (le_max_right N (max R₁ 1))
  have hM1 : 1 ≤ M := le_trans (le_max_right R₁ 1) (le_max_right N (max R₁ 1))
  -- `‖z‖ < 1 / (M + 1)` makes `ζ = -1 / z` satisfy `M < ‖ζ‖`
  refine ⟨min ρ₀ (1 / (M + 1)), lt_min hρ₀ (one_div_pos.mpr (by linarith)), ?_⟩
  intro z hz0 hzρ hzarg
  have hz_ne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz0; exact lt_irrefl 0 hz0
  have hρ0 : ‖z‖ < ρ₀ := lt_of_lt_of_le hzρ (min_le_left _ _)
  have hρ1 : ‖z‖ < 1 / (M + 1) := lt_of_lt_of_le hzρ (min_le_right _ _)
  have harg7 : |z.arg| ≤ 7 * Real.pi / 12 := by
    have h : Real.pi / 2 + Real.pi / 12 = 7 * Real.pi / 12 := by ring
    linarith [hzarg, h]
  -- the cone angle agrees with the one used by `cover_cone_wedge`
  have hargw : |z.arg| ≤ 2 * Real.pi / 3 - Real.pi / 12 := by
    have h : 2 * Real.pi / 3 - Real.pi / 12 = 7 * Real.pi / 12 := by ring
    linarith [harg7, h]
  -- the covering point `ζ` of the ζ-plane
  obtain ⟨_, _, ζ, hζL, _, htau⟩ := hcov z hz0 hρ0 hargw
  -- `τ₀ ζ = z` and `τ₀` is an involution, so `ζ = τ₀ z = -1 / z`
  have hζeq : ζ = MandelDim.tau0 z := by
    have h := tau0_tau0_aux ζ
    rw [htau] at h
    exact h.symm
  have hinv := Work.Parab.coverCone.inv_neg_norm_re hz_ne harg7
  have hζ3 : ζ.re ≤ ‖ζ‖ / 3 := by
    rw [hζeq]; simp only [MandelDim.tau0]; exact hinv.2
  have hζnorm : ‖ζ‖ = 1 / ‖z‖ := by
    rw [hζeq]; simp only [MandelDim.tau0]; exact hinv.1
  have hζbig : M < ‖ζ‖ := by
    rw [hζnorm, lt_div_iff₀ hz0]
    have h : (M + 1) * ‖z‖ < 1 := by
      have h1 := mul_lt_mul_of_pos_left hρ1 (by linarith : (0:ℝ) < M + 1)
      have h2 : (M + 1) * (1 / (M + 1)) = 1 := by field_simp
      linarith [h1, h2]
    nlinarith [h, hz0]
  have hζR : R₁ < ‖ζ‖ := lt_of_le_of_lt hMR hζbig
  have hζ1 : 1 ≤ ‖ζ‖ := le_of_lt (lt_of_le_of_lt hM1 hζbig)
  -- the error of the identity approximation at `ζ`
  have hE := norm_Phi_sub_id_le (R := R₁) hR₁ ζ hζL hζR hζ1
  have hNζ : 9 * (‖a‖ * (Real.log ‖ζ‖ + Real.pi) + (1 + |ξ| + ‖b‖)) < ‖ζ‖ :=
    hN ‖ζ‖ (le_trans hMN (le_of_lt hζbig))
  have hbigcur : 9 * (‖Φ ζ - ζ‖ + |ξ|) < ‖ζ‖ := by nlinarith [hE, hNζ]
  -- the perturbation/vertex-shift estimate
  have hmem := qleft_close_vertex (ζ := ζ) (w := Φ ζ) (ξ := ξ) (E := ‖Φ ζ - ζ‖) hζ3
    (norm_nonneg _) le_rfl hbigcur
  exact ⟨by rw [← hζeq]; exact hζL, by rw [← hζeq]; exact hmem⟩

end Work.Parab.coordData
