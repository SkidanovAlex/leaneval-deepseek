import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.BoxBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.Auxiliary

/-- **Uniform bound for `Ψ/cos θ` on the box `[0,R] × [0,π/2]`.**

For `Ψ` smooth on a neighbourhood of the closed quadrant with `Ψ z (π/2) = 0` for every `z`
and `R ≥ 0`, there is `C ≥ 0` with `|Ψ z θ / cos θ| ≤ C` on the box `[0,R] × Iθ`, and
consequently `∫_θ (Ψ z θ/cos θ)² ≤ C² · π/2` for every `z ∈ [0,R]`.

Route.  `C := Work.Spaces.boxSup R (Work.Spaces.pth Ψ)` and
`hb := Work.Spaces.bddAbove_boxSup_of_continuousOn (Work.Spaces.continuousOn_box_of_contDiffOn
(Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_U hsm))` (note `hsm : SmoothNbhd Ψ` is
definitionally `ContDiffOn ℝ ⊤ (Function.uncurry Ψ) Work.Spaces.U`), so that
`Work.Spaces.le_boxSup hb hz hs : |pth Ψ z s| ≤ C` for `z ∈ Icc 0 R`, `s ∈ Iθ`
(`Work.Spaces.boxSup_nonneg hR hb` gives `0 ≤ C`).  Then
`Work.Spaces.theta_slice_diff_half Ψ hsm hz.1 hθ (le_boxSup hb hz)` together with `h1 z` gives
`|Ψ z θ| ≤ C * (π/2 - θ)`; Jordan's inequality `Real.mul_le_sin` for `x = π/2 - θ` and
`Real.sin_pi_div_two_sub` give `(2/π)(π/2 - θ) ≤ cos θ` on `Iθ`, so for `θ < π/2` (where
`Real.cos_pos_of_mem_Ioo` gives `0 < cos θ`)
`|Ψ z θ / cos θ| = |Ψ z θ|/cos θ ≤ C·π/2`, while at `θ = π/2` the quotient is `0/0 = 0`.
The second conjunct follows from `MeasureTheory.integral_mono_of_nonneg` with the constant
function `C^2` (integrable on `Iθ`, whose volume is `π/2` by `Real.volume_Icc`). -/
theorem exists_bound_divCos_box (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (h1 : ∀ z, Ψ z (Real.pi / 2) = 0) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Work.Spaces.Iθ,
        |Ψ z θ / Real.cos θ| ≤ C) ∧
      (∀ z ∈ Set.Icc 0 R,
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2) ≤ C ^ 2 * (Real.pi / 2)) := by
  -- Smoothness of `pth Ψ` and boundedness on the box.
  have hb : BddAbove (Work.Spaces.boxSet R (Work.Spaces.pth Ψ)) :=
    Work.Spaces.bddAbove_boxSup_of_continuousOn
      (Work.Spaces.continuousOn_box_of_contDiffOn
        (Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_U hsm))
  have hCnn : 0 ≤ Work.Spaces.boxSup R (Work.Spaces.pth Ψ) :=
    Work.Spaces.boxSup_nonneg hR hb
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  set C : ℝ := Work.Spaces.boxSup R (Work.Spaces.pth Ψ) * (Real.pi / 2) with hCdef
  have hCnn' : 0 ≤ C := by rw [hCdef]; exact mul_nonneg hCnn hpi
  have hpt : ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Work.Spaces.Iθ, |Ψ z θ / Real.cos θ| ≤ C := by
    intro z hz θ hθ
    have hCbd : ∀ s ∈ Work.Spaces.Iθ,
        |Work.Spaces.pth Ψ z s| ≤ Work.Spaces.boxSup R (Work.Spaces.pth Ψ) :=
      fun s hs => Work.Spaces.le_boxSup hb hz hs
    by_cases hθ2 : θ = Real.pi / 2
    · subst hθ2
      rw [Real.cos_pi_div_two, h1 z, zero_div, abs_zero]
      exact hCnn'
    · have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hθ2
      -- the `θ`-difference of `Ψ`, bounded by `C · (π/2 - θ)`
      have habs : |Ψ z θ| ≤ Work.Spaces.boxSup R (Work.Spaces.pth Ψ) * (Real.pi / 2 - θ) := by
        have h := Work.Spaces.theta_slice_diff_half Ψ hsm hz.1 hθ hCbd
        rwa [h1 z, sub_zero] at h
      have hcos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθlt⟩
      -- Jordan's inequality `(2/π)(π/2 - θ) ≤ cos θ`
      have hj : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := by
        have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith [hθ.2])
          (by linarith [hθ.1])
        rwa [Real.sin_pi_div_two_sub] at h
      have hlin : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
        have h2 : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
        calc Real.pi / 2 - θ
            = Real.pi / 2 * (2 / Real.pi) * (Real.pi / 2 - θ) := by rw [h2, one_mul]
          _ = Real.pi / 2 * (2 / Real.pi * (Real.pi / 2 - θ)) := by ring
          _ ≤ Real.pi / 2 * Real.cos θ := mul_le_mul_of_nonneg_left hj hpi
      have hbnd : |Ψ z θ| ≤ Work.Spaces.boxSup R (Work.Spaces.pth Ψ) * (Real.pi / 2)
          * Real.cos θ := by
        have h3 : Work.Spaces.boxSup R (Work.Spaces.pth Ψ) * (Real.pi / 2 - θ)
            ≤ Work.Spaces.boxSup R (Work.Spaces.pth Ψ) * (Real.pi / 2 * Real.cos θ) :=
          mul_le_mul_of_nonneg_left hlin hCnn
        nlinarith [habs, h3]
      rw [abs_div, abs_of_pos hcos, div_le_iff₀ hcos, hCdef]
      exact hbnd
  refine ⟨C, hCnn', hpt, ?_⟩
  intro z hz
  have hle : ∀ θ ∈ Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
    intro θ hθ
    exact sq_le_sq.mpr (by rw [abs_of_nonneg hCnn']; exact hpt z hz θ hθ)
  have hmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hvol : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  calc (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, C ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => sq_nonneg _)
          (integrableOn_const hvol (by simp)) ?_
        have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
            (Ψ z θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
          rw [ae_restrict_iff' hmeas]
          exact Filter.Eventually.of_forall fun θ hθ => hle θ hθ
        exact hae
    _ = C ^ 2 * (Real.pi / 2) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring

end Work.FTS.EllipticEst.Auxiliary
