import Mathlib
import Submission.Work.EQ.TailGlueDefs
import Submission.Work.EQ.CycleDefs

namespace Work.EQ.Tl

open Work.EQ

/-- **Annulus glue bounds.** For `0 < a < 1`, a point `z` in the annulus `Ann r₁ r₂`, and a
radius `ρ` with `ρ ^ (2 ^ (2 * dep)) ≤ r₁ / 2`, the perturbation `z + t ^ (2 ^ (2 * dep))` with
`‖t‖ < ρ` stays nonzero, keeps its norm below `r₂ + 1` and below `‖z‖ - r₁/2 + ... ` in the
sense that `1 / (z + t ^ …)` is bounded by `2 / r₁`; consequently both the direct term
`λ^dep · (z + t ^ …)` and the reciprocal term `λ^dep · (c / (z + t ^ …))` are bounded by `ρg`
whenever the hypotheses `hb₁`, `hb₂` hold. -/
theorem annulus_glue_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c : ℂ}
    {r₁ r₂ ρg : ℝ} (hr₁ : 0 < r₁) {dep : ℕ} (hdep : 1 ≤ dep)
    (hb₁ : (eqLam a) ^ dep * (r₂ + 1) < ρg)
    (hb₂ : (eqLam a) ^ dep * (2 * ‖c‖ / r₁) < ρg)
    {z : ℂ} (hz : z ∈ Ann r₁ r₂)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρk : ρ ^ (2 ^ (2 * dep)) ≤ r₁ / 2) :
    z ≠ 0 ∧
      (∀ t : ℂ, ‖t‖ < ρ → z + t ^ (2 ^ (2 * dep)) ≠ 0) ∧
      (∀ t : ℂ, ‖t‖ < ρ → ‖((eqLam a : ℝ) : ℂ) ^ dep * (z + t ^ (2 ^ (2 * dep)))‖ < ρg) ∧
      (∀ t : ℂ, ‖t‖ < ρ →
        ‖((eqLam a : ℝ) : ℂ) ^ dep * (c / (z + t ^ (2 ^ (2 * dep))))‖ < ρg) := by
  have hz' : r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ := hz
  obtain ⟨hz_lo, hz_hi⟩ := hz'
  -- `0 < eqLam a < 1` for `0 < a < 1`.
  have hlam_pos : 0 < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  have hlam_lt_one : eqLam a < 1 := by
    rw [eqLam, div_lt_one (by linarith : (0:ℝ) < 1 + a)]; linarith
  have hlam_nonneg : 0 ≤ eqLam a := le_of_lt hlam_pos
  have hlam_le_one : eqLam a ≤ 1 := le_of_lt hlam_lt_one
  have hpw_pos : 0 < (eqLam a) ^ dep := pow_pos hlam_pos dep
  have hpw_le_one : (eqLam a) ^ dep ≤ 1 := pow_le_one₀ hlam_nonneg hlam_le_one
  have hnne : 2 ^ (2 * dep) ≠ 0 := by positivity
  have hnormc : ‖((eqLam a : ℝ) : ℂ) ^ dep‖ = (eqLam a) ^ dep := by
    rw [Complex.norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg hlam_nonneg
  -- The bound `r₁ / 2 < ‖z + t ^ n‖` and the two `ρg`-bounds, for each `‖t‖ < ρ`.
  have key : ∀ t : ℂ, ‖t‖ < ρ →
      r₁ / 2 < ‖z + t ^ (2 ^ (2 * dep))‖ ∧
      ‖((eqLam a : ℝ) : ℂ) ^ dep * (z + t ^ (2 ^ (2 * dep)))‖ < ρg ∧
      ‖((eqLam a : ℝ) : ℂ) ^ dep * (c / (z + t ^ (2 ^ (2 * dep))))‖ < ρg := by
    intro t ht
    have ht_lt_one : ‖t‖ < 1 := lt_of_lt_of_le ht hρ1
    -- `‖t ^ n‖ = ‖t‖ ^ n < ρ ^ n ≤ r₁ / 2`
    have htn_rho : ‖t ^ (2 ^ (2 * dep))‖ < ρ ^ (2 ^ (2 * dep)) := by
      rw [Complex.norm_pow]
      exact pow_lt_pow_left₀ ht (norm_nonneg t) hnne
    have htn_r : ‖t ^ (2 ^ (2 * dep))‖ < r₁ / 2 := lt_of_lt_of_le htn_rho hρk
    -- `‖t ^ n‖ = ‖t‖ ^ n < 1`
    have htn_one : ‖t ^ (2 ^ (2 * dep))‖ < 1 := by
      rw [Complex.norm_pow]
      have hh := pow_lt_pow_left₀ ht_lt_one (norm_nonneg t) hnne
      simpa using hh
    -- reverse triangle inequality: `‖z + t ^ n‖ ≥ ‖z‖ - ‖t ^ n‖ > r₁ - r₁ / 2 = r₁ / 2`
    have hlower : r₁ / 2 < ‖z + t ^ (2 ^ (2 * dep))‖ := by
      have h1 : ‖z‖ ≤ ‖z + t ^ (2 ^ (2 * dep))‖ + ‖t ^ (2 ^ (2 * dep))‖ := by
        have heq : (z + t ^ (2 ^ (2 * dep))) - t ^ (2 ^ (2 * dep)) = z := by ring
        calc ‖z‖ = ‖(z + t ^ (2 ^ (2 * dep))) - t ^ (2 ^ (2 * dep))‖ := by rw [heq]
          _ ≤ ‖z + t ^ (2 ^ (2 * dep))‖ + ‖t ^ (2 ^ (2 * dep))‖ := norm_sub_le _ _
      linarith
    -- triangle inequality: `‖z + t ^ n‖ ≤ ‖z‖ + ‖t ^ n‖ < r₂ + 1`
    have hupper : ‖z + t ^ (2 ^ (2 * dep))‖ < r₂ + 1 := by
      have h1 := norm_add_le z (t ^ (2 ^ (2 * dep)))
      linarith
    refine ⟨hlower, ?_, ?_⟩
    · rw [norm_mul, hnormc]
      have h := mul_lt_mul_of_pos_left hupper hpw_pos
      linarith
    · rw [norm_mul, hnormc, norm_div]
      have hratio : ‖c‖ / ‖z + t ^ (2 ^ (2 * dep))‖ ≤ 2 * ‖c‖ / r₁ := by
        have hhalf : (0:ℝ) < r₁ / 2 := by linarith
        have hle : r₁ / 2 ≤ ‖z + t ^ (2 ^ (2 * dep))‖ := le_of_lt hlower
        have hh := div_le_div_of_nonneg_left (norm_nonneg c) hhalf hle
        rwa [show ‖c‖ / (r₁ / 2) = 2 * ‖c‖ / r₁ by ring_nf] at hh
      have h := mul_le_mul_of_nonneg_left hratio (le_of_lt hpw_pos)
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz0
    rw [hz0, norm_zero] at hz_lo
    linarith
  · intro t ht
    have hp : 0 < ‖z + t ^ (2 ^ (2 * dep))‖ :=
      lt_trans (by linarith : (0:ℝ) < r₁ / 2) (key t ht).1
    exact norm_ne_zero_iff.mp (ne_of_gt hp)
  · intro t ht; exact (key t ht).2.1
  · intro t ht; exact (key t ht).2.2

end Work.EQ.Tl
