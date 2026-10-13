import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.T2SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-- The mixed "hard" summands (`k ≥ 1`) of the transport pairing, in their angular slice.
For `α ≤ 1`, `g` smooth on a neighbourhood of the closed quadrant, `i ≥ 1`, `j` any
natural number and `z ≥ 0`, the function
`θ ↦ ∂_z(mixed j i g)(z,θ) · mixed j i g(z,θ) · w(z)² · sin(2θ)^{-γ}`, `γ = 1 + α/10`,
is integrable on `Iθ`.

Strategy.  Write `i = (i-1)+1`.  By `Work.FTS.H2.mixed_sin_factor` the factor `sin(2θ)`
produced by the outermost `D_θ = sin(2θ) ∂_θ` survives the `D_z`-iterates:
`mixed j i g = fun z θ => sin(2θ) · R z θ` with `R = D_z^j (∂_θ D_θ^{i-1} g)`, and by
`Work.FTS.H2.pz_mixed_sin_factor` also `∂_z (mixed j i g) = fun z θ => sin(2θ) · ∂_z R z θ`.
Both `R` and `∂_z R` are `SmoothNbhd` (`SmoothNbhd.DthIter`, `SmoothNbhd.pth`,
`SmoothNbhd.DzIter`, `SmoothNbhd.pz` from `Submission.Work.Spaces.SmoothCompact_Aux`, which
`T2SliceAux` imports), so their angular slices are continuous on `Iθ`
(`Work.FTS.H2.continuousOn_slice`) with bounds `CS`, `CR`
(`Work.FTS.H2.exists_nonneg_bound_abs`).  Since `sin(2θ) ≥ 0` and `sin(2θ) ≤ 1` on `Iθ`,
the integrand is bounded in absolute value by
`CS · CR · w(z)² · (sin(2θ)² · sin(2θ)^{-γ}) ≤ CS · CR · w(z)²` by
`Work.FTS.H2.sq_mul_rpow_neg_le_one` (`γ < 2` and `0 ≤ 2 - γ` both follow from `α ≤ 1`).
A constant is integrable on the finite-measure set `Iθ` (`MeasureTheory.integrableOn_const`),
so `Integrable.mono'` (with a.e. strong measurability of the integrand) gives the claim. -/
theorem HardSummandMixed (α : ℝ) (g : ℝ → ℝ → ℝ) (hsmg : Work.Spaces.SmoothNbhd g)
    (hα1 : α ≤ 1) (j i : ℕ) (hi : 1 ≤ i) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz (Work.Spaces.mixed j i g) z θ * Work.Spaces.mixed j i g z θ
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
  -- Write `i = i' + 1` so that the outermost `D_θ` exhibits its factor `sin(2θ)`.
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  set R : ℝ → ℝ → ℝ := Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i' g))
    with hR
  -- Smoothness, hence continuity of the angular slices, of `R` and `∂_z R`.
  have hRsm : Work.Spaces.SmoothNbhd R := by
    rw [hR]
    exact Work.Spaces.smoothNbhd_DzIter ((Work.Spaces.smoothNbhd_DthIter hsmg i').pth) j
  have hRc : ContinuousOn (fun θ => R z θ) Work.Spaces.Iθ :=
    Work.FTS.H2.continuousOn_slice hRsm hz
  obtain ⟨CS, hCS0, hCS⟩ := Work.FTS.H2.exists_nonneg_bound_abs hRc
  have hpRsm : Work.Spaces.SmoothNbhd (Work.Spaces.pz R) := hRsm.pz
  have hpRc : ContinuousOn (fun θ => Work.Spaces.pz R z θ) Work.Spaces.Iθ :=
    Work.FTS.H2.continuousOn_slice hpRsm hz
  obtain ⟨CR, hCR0, hCR⟩ := Work.FTS.H2.exists_nonneg_bound_abs hpRc
  -- `γ < 2` and `0 ≤ 2 - γ` for `α ≤ 1`.
  have hgam_lt : Work.Spaces.gam α < 2 := by
    have h : Work.Spaces.gam α = 1 + α / 10 := rfl
    rw [h]; linarith
  have hgam2 : 0 ≤ 2 - Work.Spaces.gam α := by
    have h : Work.Spaces.gam α = 1 + α / 10 := rfl
    rw [h]; linarith
  -- The constant majorant is integrable on the finite-measure interval `Iθ`.
  have hMint : MeasureTheory.IntegrableOn (fun _ : ℝ => CR * CS * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
      (C := CR * CS * (Work.Spaces.w z) ^ 2)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- A.e. strong measurability of the integrand (a product of continuous slices and a
  -- measurable power of `sin`).
  have hFasm : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.pz (Work.Spaces.mixed j (i' + 1) g) z θ
        * Work.Spaces.mixed j (i' + 1) g z θ * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Spaces.pz (Work.Spaces.mixed j (i' + 1) g) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Work.FTS.H2.continuousOn_slice
        (Work.Spaces.smoothNbhd_mixed hsmg j (i' + 1)).pz hz).aestronglyMeasurable measurableSet_Icc
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Spaces.mixed j (i' + 1) g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Work.FTS.H2.continuousOn_slice
        (Work.Spaces.smoothNbhd_mixed hsmg j (i' + 1)) hz).aestronglyMeasurable measurableSet_Icc
    have h4 : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _).aestronglyMeasurable
    exact ((h1.mul h2).mul aestronglyMeasurable_const).mul h4
  -- The pointwise bound by the constant majorant, a.e. on `Iθ`.
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(fun θ => Work.Spaces.pz (Work.Spaces.mixed j (i' + 1) g) z θ
        * Work.Spaces.mixed j (i' + 1) g z θ * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) θ‖ ≤ CR * CS * (Work.Spaces.w z) ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsq : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ 1 :=
      Work.FTS.H2.sq_mul_rpow_neg_le_one _ _ hs0 hs1 hgam_lt hgam2
    -- The factor `sin(2θ)` in front of both `R` and `∂_z R`.
    have hpzs : Work.Spaces.pz (Work.Spaces.mixed j (i' + 1) g) z θ
        = Real.sin (2 * θ) * Work.Spaces.pz R z θ := by
      rw [hR]
      exact Work.FTS.H2.pz_mixed_sin_factor j i' g z θ
    have hmix : Work.Spaces.mixed j (i' + 1) g z θ = Real.sin (2 * θ) * R z θ := by
      rw [hR]
      exact congrFun (congrFun (Work.FTS.H2.mixed_sin_factor j i' g) z) θ
    rw [Real.norm_eq_abs, hpzs, hmix]
    have hA : |Work.Spaces.pz R z θ| * |R z θ| ≤ CR * CS :=
      mul_le_mul (hCR θ hθ) (hCS θ hθ) (abs_nonneg _) hCR0
    have hA2 : |Work.Spaces.pz R z θ| * |R z θ| * (Work.Spaces.w z) ^ 2
        ≤ CR * CS * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    have hsinnn : 0 ≤ (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hM0 : 0 ≤ CR * CS * (Work.Spaces.w z) ^ 2 := by positivity
    have hfinal := mul_le_mul hA2 hsq hsinnn hM0
    -- Extract the absolute values and collect the two `sin(2θ)` factors.
    have habs : |Real.sin (2 * θ) * Work.Spaces.pz R z θ * (Real.sin (2 * θ) * R z θ)
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))|
        = |Work.Spaces.pz R z θ| * |R z θ| * (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      simp only [abs_mul, abs_of_nonneg hs0,
        abs_of_nonneg (sq_nonneg (Work.Spaces.w z)), abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      ring
    rw [habs]
    calc |Work.Spaces.pz R z θ| * |R z θ| * (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ CR * CS * (Work.Spaces.w z) ^ 2 * 1 := hfinal
      _ = CR * CS * (Work.Spaces.w z) ^ 2 := by ring
  exact hMint.mono' hFasm hbound

end Work.FTS.H2
