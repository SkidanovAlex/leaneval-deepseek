import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Analysis.PertCrux.ball_subset_gates

/-!
# PertCrux · `ball_subset_Qp_of_bounds`

Rectangle-to-gate form of `ball_subset_gates`.  If `x` lies in the rectangle
`{w | m - MK ≤ w.re ≤ m + MK, |w.im| ≤ MK}` and the lower gate vertex `Ξ'` and the ball radius `R`
satisfy the two size conditions

* `Ξ' + 2R < m - MK`  (the cone at the vertex `Ξ'` keeps a slack `2R` at `x`), and
* `m + 2MK + Ξ' + 2R < 1/‖α‖`  (the far vertex `-Ξ' + 1/α` keeps a slack `2R` at `x`),

then the whole ball `ball x R` lies in the upper gate `Qp Ξ' α` (and in particular in the
one-sided region `Qreg (some Ξ') none`).

The second condition is the quantitative form of `1/‖α‖ ≤ (1/α).re + |(1/α).im|`: writing
`z = 1/α`, this inequality is `√(z.re² + z.im²) ≤ z.re + |z.im|`, which holds precisely because
`hc` gives `z.re ≥ 0` (then `z.re = |z.re|` and `(|z.re| + |z.im|)² = ‖z‖² + 2|z.re||z.im|`), and it
combined with `|x.im - z.im| ≥ |z.im| - |x.im| ≥ |z.im| - MK` bounds the horizontal distance
`|x.im - (1/α).im|` from below.
-/

namespace Work.Analysis.PertCrux

open MandelDim Complex Set Metric

noncomputable section

theorem ball_subset_Qp_of_bounds {Ξ' R m MK : ℝ} {α x : ℂ}
    (hΞ' : 1 ≤ Ξ') (hR : 0 ≤ R) (hMK : 0 ≤ MK) (hm : 0 ≤ m)
    (hc : 0 ≤ (1 / α).re)
    (hre : m - MK ≤ x.re) (hre' : x.re ≤ m + MK) (him : |x.im| ≤ MK)
    (h1 : Ξ' + 2 * R < m - MK)
    (h2 : m + 2 * MK + Ξ' + 2 * R < 1 / ‖α‖) :
    Metric.ball x R ⊆ Work.Pert.Qp Ξ' α ∧
      Metric.ball x R ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none := by
  -- the cone at the vertex `Ξ'`: `h1` and `|x.im| ≤ MK ≤ m - Ξ' - 2R`
  have hcone : Ξ' + 2 * R < x.re + |x.im| := by
    linarith [abs_nonneg x.im, h1, hre]
  -- the cone at the far vertex `-Ξ' + 1/α`
  have hfar : x.re + Ξ' - (1 / α).re + 2 * R < |x.im - (1 / α).im| := by
    -- `‖1/α‖ = 1/‖α‖`
    have hnorm : (1 : ℝ) / ‖α‖ = ‖(1 : ℂ) / α‖ := by rw [norm_div, norm_one]
    -- `‖1/α‖ ≤ (1/α).re + |(1/α).im|`, using `hc`
    have hz : ‖(1 : ℂ) / α‖ ≤ (1 / α).re + |(1 / α).im| := by
      have h := Complex.norm_le_abs_re_add_abs_im (1 / α)
      rwa [abs_of_nonneg hc] at h
    -- reverse triangle inequality, with `him`
    have htri : |(1 / α).im| - |x.im| ≤ |x.im - (1 / α).im| := by
      have h := abs_sub_abs_le_abs_sub (1 / α).im x.im
      rwa [abs_sub_comm (1 / α).im x.im] at h
    linarith [h2, hnorm, hz, hre', him, htri]
  exact ball_subset_gates hR hcone hfar

end

end Work.Analysis.PertCrux
