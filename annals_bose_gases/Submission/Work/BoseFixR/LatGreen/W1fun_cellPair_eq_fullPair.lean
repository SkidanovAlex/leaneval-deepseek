import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.lattice_W1sq_over_tau_le_sharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- **The cell pair integral of the periodisation is the full-space pair integral of the charge.**

With `P = LatGreen.period (W1fun v h ℓ) ℓ` and `W = W1fun v h ℓ`,

  `∫ p in cell ℓ ×ˢ cell ℓ, P p.1 · P p.2 · (latDistL ℓ (p.1 − p.2))⁻¹
     = ∫ p : ℝ³ × ℝ³, W p.1 · W p.2 · ‖p.1 − p.2‖⁻¹`

in the small-support regime `100 R ≤ ℓ` with `tsupport v ⊆ B(0,R)`.

This is the concatenation of the three steps `hstep5`, `hstep6a`, `hstep6b` in the proof of
`Work.BoseFixR.lwsq_lattice_row_sharp`
(`Submission/Work/BoseFixR/lattice_W1sq_over_tau_le_sharp.lean`, lines ~240–270):

* on the cell, `latDistL ℓ (p.1 − p.2) = ‖p.1 − p.2‖` (`Work.BoseFixR.lwsq_latDistL_eq_norm_of_le`;
  on the support of `W₁` the pair is within `R + R ≤ ℓ/2`, and the case where one factor of the
  product is `0` is handled by `simp`);
* on the cell, `P = W` (`Work.BoseFixR.lwsq_period_eq_of_mem_cell`, whose vanishing hypothesis
  `R ≤ ‖x‖ → W x = 0` comes from `LatGreen.W1fun_eq_zero_of_le_norm h hv_supp`);
* the charge vanishes off the cell (`Work.BoseFixR.lwsq_W1fun_eq_zero_of_not_mem_cell`), so
  `MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero` extends the integral to `ℝ³ × ℝ³`.

All three steps are *unconditional* rewrites of the integrand (`setIntegral_congr_fun`,
`setIntegral_eq_integral_of_forall_compl_eq_zero`), so no integrability hypothesis on either side is
needed and the identity is not subject to the `integral_undef` trap. -/
theorem W1fun_cellPair_eq_fullPair {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hreg : 100 * R ≤ ℓ) :
    (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
          * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
      = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2
            * (‖p.1 - p.2‖)⁻¹ := by
  classical
  have hPcell : ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ Work.BoseFixR.cell ℓ →
      Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ x
        = Work.BoseFixR.W1fun v h ℓ x :=
    fun x hx => Work.BoseFixR.lwsq_period_eq_of_mem_cell hℓ hreg
      (fun y hy => Work.BoseFixR.LatGreen.W1fun_eq_zero_of_le_norm h hv_supp hy) hx
  have hmeas_cell : MeasurableSet
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ) :=
    (Work.BoseFixR.LatGreen.measurableSet_cell ℓ).prod
      (Work.BoseFixR.LatGreen.measurableSet_cell ℓ)
  -- (i) on the support of the periodisation the lattice distance is the norm
  have hstep5 : (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
          * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
      = ∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
          * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
          * (‖p.1 - p.2‖)⁻¹ := by
    refine MeasureTheory.setIntegral_congr_fun hmeas_cell fun p hp => ?_
    rw [hPcell p.1 hp.1, hPcell p.2 hp.2]
    by_cases h1 : Work.BoseFixR.W1fun v h ℓ p.1 = 0
    · simp [h1]
    by_cases h2 : Work.BoseFixR.W1fun v h ℓ p.2 = 0
    · simp [h2]
    have hnorm : ‖p.1 - p.2‖ ≤ ℓ / 2 := by
      have hsuppW := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ
      have h3 : ‖p.1‖ < R := by
        have := hsuppW (subset_tsupport _ (Function.mem_support.mpr h1))
        simpa [Metric.mem_ball, dist_zero_right] using this
      have h4 : ‖p.2‖ < R := by
        have := hsuppW (subset_tsupport _ (Function.mem_support.mpr h2))
        simpa [Metric.mem_ball, dist_zero_right] using this
      have h5 : ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
      linarith
    rw [Work.BoseFixR.lwsq_latDistL_eq_norm_of_le hℓ hnorm]
  -- (ii) the periodisation equals the charge on the cell
  have hstep6a : (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
          * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
          * (‖p.1 - p.2‖)⁻¹)
      = ∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2
          * (‖p.1 - p.2‖)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun hmeas_cell fun p hp => by
      rw [hPcell p.1 hp.1, hPcell p.2 hp.2]
  -- (iii) the charge vanishes off the cell, so the cell integral is the full integral
  have hstep6b : (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2
          * (‖p.1 - p.2‖)⁻¹)
      = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2
            * (‖p.1 - p.2‖)⁻¹ := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [Work.BoseFixR.lwsq_W1fun_eq_zero_of_not_mem_cell h hℓ hreg hv_supp hp]; ring
    · rw [Work.BoseFixR.lwsq_W1fun_eq_zero_of_not_mem_cell h hℓ hreg hv_supp hp]; ring
  rw [hstep5, hstep6a, hstep6b]

end Work.BoseFixR.LatGreen
