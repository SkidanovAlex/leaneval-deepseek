import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.contN0_open
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

/-- (namespace `Work.FTS.MuLipC.RowN0`) **The squared angular slice of the `N₀`-field is
integrable** for every `r > 0`, for a `SmoothOpen` and `ℋ⁴`-honest datum `g` with `0 < α ≤ 1`.

Proof (the `hsl` block of `Work.FTS.MuLamOK.Rows.Rl0Open`): the pointwise bound
`(N₀ α (F_*+g) g r θ)²·w r ≤ 7(A₀ α |g|_{ℋ⁴}·HkIntegrand α 4 g r θ + B₀ α |g|_{ℋ⁴}/(1+r)²)` for
`r > 0`, `θ ∈ (0,π/2)` (`Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open`, whose `|L₁₂ g| ≤
3|g|_{ℋ⁴}` hypothesis is `Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open`) together with
`w r ≥ 1` dominates the slice by the integrable
`θ ↦ 7(A₀ α |g|_{ℋ⁴}·HkIntegrand α 4 g r θ + B₀ α |g|_{ℋ⁴}/(1+r)²)` (`HkMem α 4 g`), and the
slice is a.e. strongly measurable on `Iθ` because `N₀ α (F_*+g) g` is continuous on the open
quadrant (`Work.FTS.StrongPersist.H6Pair6Aux.contN0_open`,
`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
theorem N0_slice_sq_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2)
      Work.Spaces.Iθ := by
  intro r hr
  have hr0 : (0 : ℝ) < r := hr
  have hzr : r ∈ Work.Spaces.Iz := by
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
  have hW1 : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
    nlinarith
  have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  -- the uniform bound `|L₁₂(g)| ≤ 3|g|_{ℋ⁴}` feeding into the pointwise estimate
  have hsup : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g :=
    Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hso hmem
  -- the pointwise weighted bound for `N₀`
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) :=
    Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open hα hα1 hso hsup
  -- joint continuity of `N₀` on the open quadrant
  have hcont : ContinuousOn
      (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α g) g))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hso hmem
  have hslice : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hr0
  -- the integrable majorant
  have hmaj : MeasureTheory.Integrable
      (fun θ : ℝ => 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
          * Work.Spaces.HkIntegrand α 4 g r θ
        + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
          * (1 / (1 + r)) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (((hmem.1 r hzr).const_mul _).add ?_).const_mul 7
    refine MeasureTheory.integrableOn_const ?_
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono' hmaj (hslice.pow 2) ?_
  rw [hIoo2]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2
      ≤ (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r := by
        nlinarith [hW1,
          sq_nonneg (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ)]
    _ ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) := hpt r hr θ hθ

end Work.FTS_MuLipC.RowN0
