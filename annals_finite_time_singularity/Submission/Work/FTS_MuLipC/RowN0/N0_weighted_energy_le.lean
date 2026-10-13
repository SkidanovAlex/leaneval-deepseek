import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

open scoped Real Topology
open MeasureTheory Set Filter

/-- (namespace `Work.FTS_MuLipC.RowN0`) **The Hardy-weighted angular energy of the `N₀`-field is
dominated by an explicit integrable function**: for a.e. `r > 0`,
`(∫_θ (N₀ α (F_*+g) g r θ)²)·((1+r)/r)²
   ≤ 7·(A₀(α,|g|_{ℋ⁴})·Ψ(r) + (π/2)·B₀(α,|g|_{ℋ⁴})·(1/(1+r))²)` where `Ψ(r) = ∫_θ HkIntegrand α 4 g r θ`.

Proof (the `hbd` block of `Work.FTS.MuLamOK.Rows.Rl0Open`): integrate in `θ` the pointwise bound
`(N₀ α (F_*+g) g r θ)²·w r ≤ 7(A₀·HkIntegrand α 4 g r θ + B₀/(1+r)²)` of
`Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open` over `Iθ` (both sides are integrable there: the
first by `HkMem α 4 g`, the constant piece because `Iθ` is compact), using
`MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul` and `∫_θ 1 = π/2` (so the
`π/2` factor multiplies only the constant `B₀`-term); the set `Iθ` and the open interval
`(0,π/2)` differ by the two null endpoints, so the pointwise bound only has to hold a.e. in `θ`.
The hypothesis `|L₁₂ g| ≤ 3|g|_{ℋ⁴}` of `N0_sq_w_open` is
`Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open`. -/
theorem N0_weighted_energy_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2)
          * ((1 + r) / r) ^ 2
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
            + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
              * (1 / (1 + r)) ^ 2) := by
  -- ## the two delivered analytic inputs
  have hsup : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g :=
    Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open hα hα1 hso hmem
  have hpt : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) :=
    Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open hα hα1 hso hsup
  -- ## the pointwise bound integrated in `θ`
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0 : ℝ) < r := hr
  have hzr : r ∈ Work.Spaces.Iz := by
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr0.le
  have hW1 : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, one_le_div (pow_pos hr0 2)]
    nlinarith
  have hweq : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by rw [Work.Spaces.w, div_pow]
  rw [hweq, ← MeasureTheory.integral_mul_const]
  have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2
          * Work.Spaces.w r)
      ≤ ∫ θ in Work.Spaces.Iθ,
        7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
              * Work.Spaces.HkIntegrand α 4 g r θ
            + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
              * (1 / (1 + r)) ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall (fun θ =>
        mul_nonneg (sq_nonneg _) (le_trans zero_le_one hW1))
    · refine (((hmem.1 r hzr).const_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g))).add ?_).const_mul 7
      refine MeasureTheory.integrableOn_const ?_
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · rw [hIoo2]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => hpt r hr θ hθ)
  refine hstep.trans ?_
  have hintA : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
        * Work.Spaces.HkIntegrand α 4 g r θ) Work.Spaces.Iθ :=
    (hmem.1 r hzr).const_mul (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g))
  have hintB : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
        * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.integrableOn_const ?_
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintA hintB,
    MeasureTheory.integral_const_mul, Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra]
  exact le_of_eq (by ring)

end Work.FTS_MuLipC.RowN0
