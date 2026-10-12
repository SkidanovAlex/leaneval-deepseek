import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.farLatParseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- **Finiteness of the cell pair kernel in the periodic-distance form at `W₁`.**

With `P = LatGreen.period (W1fun v h ℓ) ℓ`,

  `∫⁻ p in cell ℓ ×ˢ cell ℓ, ofReal (P p.1 · P p.2 · (latDistL ℓ (p.1 − p.2))⁻¹) < ⊤`.

This is exactly the computation carried out in
`Submission/Work/BoseFixR/lattice_W1sq_over_tau_le_sharp.lean` (proof of `lwsq_lattice_row_sharp`,
the `hfin` block, lines ~195–225), factored out.  Route (verbatim from that file): fold the cell
double `∫⁻` into a whole-space double `∫⁻` by `FarLat.fold_periodic_lintegral` with
`φ = (latDistL ℓ ·)⁻¹` (measurable by `measurable_infDist.inv`, nonnegative, periodic by
`latDistL_period`); dominate pointwise by the finite window `latFin9` (`ofReal_mul_le_ofReal_mul`
plus `FarLat.inv_latDistL_le_latFin9` when `‖p.1 − p.2‖ ≤ 2ℓ`, and the vanishing of one of the two
`W₁`-factors on `tsupport v ⊆ B(0,R)` with `100R ≤ ℓ` otherwise, via `tsupport_W1fun_subset`);
conclude with `W1fun_pairKernel_latFin9_lintegral_lt_top` (`farLatParseval.lean`).  No pointwise
nonnegativity of `W₁` is used — only the a.e. form `Submission.BoseGases.wScaled_g0_nonneg_ae`
(`Submission.Work.SmallBoxBogWS1Bound`, imported through `farLatParseval`). -/
theorem W1fun_pairKernel_latDistL_lintegral_lt_top {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
          * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤ := by
  -- ## 0. The basic facts about `W = W₁ = wScaled ℓ (g₀)` in the dilute regime
  have hchi : Submission.BoseGases.chiR0 ≤ 1 := Work.BoseFixR.Rb5Lin.chiR0_le_one
  have hRle : R ≤ ℓ := by
    calc R ≤ ℓ * Submission.BoseGases.chiR0 := hRℓ
      _ ≤ ℓ * 1 := by nlinarith [hchi, hℓ]
      _ = ℓ := mul_one ℓ
  have hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable (ℓ := ℓ) hR hv_supp h hℓ hRℓ
  have hWnn : 0 ≤ᵐ[MeasureTheory.volume] (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_nonneg_ae (ℓ := ℓ) hR hv hvrad hv_supp h
  have hWper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ =>
        Work.BoseFixR.W1fun v h ℓ (x - Work.BoseFixR.lat ℓ n)) :=
    fun x => Work.BoseFixR.LatGreen.W1funPeriodSummable h hR hℓ hv_supp x
  -- ## 1. The folding identity for the periodic kernel `(latDistL ℓ ·)⁻¹`
  have hφm : Measurable
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹) :=
    measurable_infDist.inv
  have hφnn : 0 ≤ᵐ[MeasureTheory.volume]
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹) :=
    Filter.Eventually.of_forall fun z => inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ z)
  have hφper : ∀ (z : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ),
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹)
          (z + Work.BoseFixR.lat ℓ n)
        = (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹) z := by
    intro z n
    simp only
    rw [Work.BoseFixR.latDistL_period]
  have hfold := Work.BoseFixR.FarLat.fold_periodic_lintegral hℓ hW hWnn hWper
    (φ := fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹)
    hφm hφnn hφper
  -- ## 2. The pointwise comparison against the finite window `latFin9`
  have hcmp : (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
          * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹))
      ≤ᵐ[MeasureTheory.volume]
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
          * (∑ p ∈ Work.BoseFixR.latFin9,
              (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹))) := by
    filter_upwards with q
    by_cases h2 : ‖q.1 - q.2‖ ≤ 2 * ℓ
    · exact Work.BoseFixR.ofReal_mul_le_ofReal_mul
        (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ _))
        (Work.BoseFixR.FarLat.inv_latDistL_le_latFin9 hℓ h2)
    · have hlt : 2 * ℓ < ‖q.1 - q.2‖ := lt_of_not_ge h2
      have hzero : Work.BoseFixR.W1fun v h ℓ q.1 = 0
          ∨ Work.BoseFixR.W1fun v h ℓ q.2 = 0 := by
        by_contra hc
        push_neg at hc
        have hsuppW := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ
        have h3 : ‖q.1‖ < R := by
          have := hsuppW (subset_tsupport _ (Function.mem_support.mpr hc.1))
          simpa [Metric.mem_ball, dist_zero_right] using this
        have h4 : ‖q.2‖ < R := by
          have := hsuppW (subset_tsupport _ (Function.mem_support.mpr hc.2))
          simpa [Metric.mem_ball, dist_zero_right] using this
        have h5 : ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
        linarith
      rcases hzero with hz | hz <;> simp [hz]
  -- ## 3. Fold, dominate by the window, and conclude by the window's finiteness
  rw [hfold]
  exact lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae hcmp)
    (Work.BoseFixR.W1fun_pairKernel_latFin9_lintegral_lt_top h hv hvrad hR hℓ hv_supp hRℓ)

end Work.BoseFixR.LatGreen
