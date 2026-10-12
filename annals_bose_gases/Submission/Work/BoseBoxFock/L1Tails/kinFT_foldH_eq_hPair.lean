import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Fourier transform of the folded kernel is the lattice pairing:
`kinFT (foldH H) (κ_n) = hPair ℓ H (-n)`.  Route: `kinFT (foldH H) p = ∫_z e^{-i⟪p,z⟫} (∫_y H (z+y) y
dy) dz`; swap the two integrals (Fubini, `H` smooth and compactly supported) and substitute
`w = z + y` (a shear of determinant one, `MeasureTheory.MeasurePreserving` of
`(z,y) ↦ (z+y, y)`) to get `∫_w ∫_y e^{-i⟪p,w-y⟫} H w y dw dy`, which at `p = kappaL ℓ n` is
`hPair ℓ H (-n)` by `Work.BoseBoxFock.L1Tails.kappaL_neg`. -/
theorem kinFT_foldH_eq_hPair {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (n : Fin 3 → ℤ) :
    Submission.BoseGases.kinFT (Work.BoseBoxFock.L1Tails.foldH H)
        (Work.BoseBoxFock.kappaL ℓ n)
      = Work.BoseBoxFock.L1Tails.hPair ℓ H (-n) := by
  -- Abbreviation for the phase `e z = e^{-i⟪κ_n,z⟫}`.
  set e : E3 → ℂ :=
    fun z => Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ))) with he
  -- `H` is bounded: it is continuous, and supported in the compact box `K × K`.
  have hKc : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
  obtain ⟨C₀, hC₀⟩ := hKc.isBounded.exists_norm_le
  have hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ w y, ‖H w y‖ ≤ M := by
    obtain ⟨D, hD⟩ := (hKc.prod hKc).exists_bound_of_continuousOn hH.continuous.continuousOn
    refine ⟨max D 0, le_max_right _ _, fun w y => ?_⟩
    by_cases hwy : w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ
    · exact le_trans (hD (w, y) hwy) (le_max_left _ _)
    · have hz : H w y = 0 := by
        by_contra hne
        exact hwy ⟨(hHs w y hne).1, (hHs w y hne).2⟩
      rw [hz, norm_zero]
      exact le_max_right _ _
  obtain ⟨M, hM0, hMle⟩ := hbound
  have he1 : ∀ z : E3, ‖e z‖ = 1 := by
    intro z
    show ‖Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) z : ℝ) : ℂ)))‖ = 1
    rw [Complex.norm_exp]
    simp
  -- The support of the joint integrand `(z,w) ↦ e z · H w (w − z)` is contained in a compact set.
  set R : ℝ := 2 * max C₀ 0 with hR
  set S : Set (E3 × E3) :=
    Metric.closedBall (0 : E3) R ×ˢ Metric.closedBall (0 : E3) (max C₀ 0) with hS
  have hScomp : IsCompact S :=
    (isCompact_closedBall (0 : E3) R).prod (isCompact_closedBall (0 : E3) (max C₀ 0))
  have hsupp : ∀ q : E3 × E3, e q.1 * H q.2 (q.2 - q.1) ≠ 0 → q ∈ S := by
    intro q hq
    have hHq : H q.2 (q.2 - q.1) ≠ 0 := fun h => hq (by rw [h, mul_zero])
    obtain ⟨h1c, h2c⟩ := hHs q.2 (q.2 - q.1) hHq
    have hb1 : ‖q.2‖ ≤ max C₀ 0 := le_trans (hC₀ q.2 h1c) (le_max_left _ _)
    have hb2 : ‖q.2 - q.1‖ ≤ max C₀ 0 := le_trans (hC₀ (q.2 - q.1) h2c) (le_max_left _ _)
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖q.1‖ = ‖q.2 - (q.2 - q.1)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖q.2‖ + ‖q.2 - q.1‖ := norm_sub_le _ _
        _ ≤ R := by rw [hR]; linarith
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hb1
  have hcont1 : Continuous fun q : E3 × E3 => H q.2 (q.2 - q.1) :=
    hH.continuous.comp (continuous_snd.prodMk (continuous_snd.sub continuous_fst))
  -- Fubini needs the joint integrand to be integrable.
  have hint : Integrable (fun q : E3 × E3 => e q.1 * H q.2 (q.2 - q.1))
      (volume.prod volume) := by
    have hg : Integrable (S.indicator fun _ : E3 × E3 => M) (volume.prod volume) := by
      rw [MeasureTheory.integrable_indicator_iff hScomp.isClosed.measurableSet]
      exact MeasureTheory.integrableOn_const (C := M) hScomp.measure_lt_top.ne (by simp)
    refine hg.mono' ?_ ?_
    · show AEStronglyMeasurable (fun q : E3 × E3 => e q.1 * H q.2 (q.2 - q.1))
        (volume.prod volume)
      have hc : Continuous fun q : E3 × E3 => e q.1 := by fun_prop
      exact (hc.mul hcont1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q => ?_
      by_cases hqs : q ∈ S
      · rw [Set.indicator_of_mem hqs]
        calc ‖e q.1 * H q.2 (q.2 - q.1)‖ = ‖e q.1‖ * ‖H q.2 (q.2 - q.1)‖ := norm_mul _ _
          _ = ‖H q.2 (q.2 - q.1)‖ := by rw [he1 q.1, one_mul]
          _ ≤ M := hMle _ _
      · rw [Set.indicator_of_notMem hqs]
        have hz : e q.1 * H q.2 (q.2 - q.1) = 0 := by
          by_contra hne
          exact hqs (hsupp q hne)
        rw [hz, norm_zero]
  -- The two translation substitutions (inner variable `y ↦ w = z + y`, then `z ↦ y = w − z`).
  have h1 : ∀ z : E3, ∫ y, e z * H (z + y) y = ∫ w, e z * H w (w - z) := by
    intro z
    have h := MeasureTheory.integral_add_left_eq_self (μ := volume)
      (fun w : E3 => e z * H w (w - z)) z
    simpa [add_sub_cancel_left] using h
  have h2 : ∀ w : E3, ∫ z, e z * H w (w - z) = ∫ y, e (w - y) * H w y := by
    intro w
    have h := MeasureTheory.integral_sub_left_eq_self (μ := volume)
      (fun y : E3 => e (w - y) * H w y) w
    simpa [sub_sub_cancel] using h
  have hint' : Integrable (Function.uncurry fun z w : E3 => e z * H w (w - z))
      (volume.prod volume) := hint
  calc Submission.BoseGases.kinFT (Work.BoseBoxFock.L1Tails.foldH H)
        (Work.BoseBoxFock.kappaL ℓ n)
      = ∫ z, e z * ∫ y, H (z + y) y := rfl
    _ = ∫ z, ∫ y, e z * H (z + y) y := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (MeasureTheory.integral_const_mul (e z) (fun y => H (z + y) y)).symm
    _ = ∫ z, ∫ w, e z * H w (w - z) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact h1 z
    _ = ∫ w, ∫ z, e z * H w (w - z) := MeasureTheory.integral_integral_swap hint'
    _ = ∫ w, ∫ y, e (w - y) * H w y := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        exact h2 w
    _ = Work.BoseBoxFock.L1Tails.hPair ℓ H (-n) := by
        rw [Work.BoseBoxFock.L1Tails.hPair]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        dsimp only
        congr 1
        show Complex.exp (-(Complex.I * ((inner ℝ (kappaL ℓ n) (w - y) : ℝ) : ℂ)))
            = Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ (-n)) (w - y) : ℝ) : ℂ))
        rw [Work.BoseBoxFock.L1Tails.kappaL_neg, inner_neg_left]
        simp only [Complex.ofReal_neg]
        ring_nf

end Work.BoseBoxFock.L1Tails
