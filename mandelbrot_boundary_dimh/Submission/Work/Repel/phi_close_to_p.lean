import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.chain_v9_geom
import Submission.Work.Repel.norm_neg_inv_sub_const_le
import Submission.Work.Repel.inv_shift_close

/-!
# `Work.Repel.phi_close_to_p`

The level-0 Fatou coordinate of the perturbed germ sends the whole counting slab
`{|Re w| ≤ η/8, |Im w - η| ≤ 1/8} ⊆ Dsm η` into the disc `ball (1.05 i/η) (0.18/η)`.

Proof: write `u = τ₀ (φ w) = -1/(φ w)`.  The `PertData` field `φ_star_close` gives
`‖u - w‖ ≤ η/40` on `Dsm η`, so `φ w = -1/u` and

`φ w - 1.05 i/η = (-1/u + 1/w) + (-1/w - 1.05 i/η)`.

* the first term is `‖u - w‖/(‖u‖ ‖w‖) ≤ (η/40)/((η - 1/8 - η/40)(η - 1/8)) ≤ 1/(38 η)`
  (`Work.Repel.inv_shift_close`), the lower bound `‖w‖ ≥ Im w ≥ η - 1/8` coming from
  `|Im w - η| ≤ 1/8`;
* the second term is `≤ 0.1412/η` (`Work.Repel.norm_neg_inv_sub_const_le`), which uses
  `|Re w| ≤ η/8`, `|Im w - η| ≤ 1/8` componentwise;

and `1/38 + 1412/10000 < 18/100`. -/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

theorem phi_close_to_p {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ) (hη : 100 ≤ η) {w : ℂ}
    (hw : w ∈ MandelDim.Dsm η) (hre : |w.re| ≤ η / 8) (him : |w.im - η| ≤ 1 / 8) :
    ‖P.φ w - 1.05 * Complex.I / η‖ < 18 / (100 * η) := by
  have hη0 : 0 < η := by linarith
  set u : ℂ := MandelDim.tau0 (P.φ w) with hu
  -- `φ_star_close` at `w ∈ Dsm η`
  have hcl : ‖u - w‖ ≤ η / 40 := by
    have h := P.φ_star_close w (Or.inl hw)
    rw [abs_of_pos hη0] at h
    simpa [hu] using h
  -- location of `w`
  have hw_im : η - 1 / 8 ≤ w.im := by have h := (abs_le.mp him).1; linarith
  have hw_im_pos : 0 < w.im := by linarith
  have hw_norm : η - 1 / 8 ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    rw [abs_of_pos hw_im_pos] at h
    linarith
  have hw_ne : w ≠ 0 := by
    intro h0
    rw [h0] at hw_norm
    simp at hw_norm
    linarith
  have hu_ne : u ≠ 0 := by
    intro h0
    have h2 : ‖u - w‖ = ‖w‖ := by rw [h0, zero_sub, norm_neg]
    have h1 : ‖w‖ ≤ η / 40 := by rw [← h2]; exact hcl
    linarith
  -- `φ w = -1/u` because `u = -1/(φ w)`
  have hphi : P.φ w = -1 / u := by
    have hp_ne : P.φ w ≠ 0 := by
      intro h0
      exact hu_ne (by rw [hu, h0, MandelDim.tau0]; simp)
    rw [hu, MandelDim.tau0]
    field_simp
  rw [hphi]
  have hsplit : -1 / u - 1.05 * Complex.I / η
      = (-1 / u + 1 / w) + (-1 / w - 1.05 * Complex.I / η) := by ring
  calc ‖-1 / u - 1.05 * Complex.I / η‖
      = ‖(-1 / u + 1 / w) + (-1 / w - 1.05 * Complex.I / η)‖ := by rw [hsplit]
    _ ≤ ‖-1 / u + 1 / w‖ + ‖-1 / w - 1.05 * Complex.I / η‖ := norm_add_le _ _
    _ ≤ 1 / (38 * η) + (1412 / 10000) / η :=
        add_le_add (inv_shift_close hη hcl hw_norm) (norm_neg_inv_sub_const_le hη hre him)
    _ < 18 / (100 * η) := by
        have hsum : 1 / (38 * η) + (1412 / 10000 : ℝ) / η
            = (1 / 38 + 1412 / 10000) / η := by
          field_simp
        rw [hsum,
          show (18 : ℝ) / (100 * η) = (18 / 100) / η by ring]
        rw [div_lt_div_iff_of_pos_right hη0]
        norm_num

end

end Work.Repel
