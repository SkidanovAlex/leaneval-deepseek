import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBoxFock.L1Tails.kinFTSlice

/-- The `y`-slice of the Fourier transform of a smooth box-supported kernel is `L²`:
`y ↦ kinFT (fun w => conj (H w y)) (κ_n)` lies in `L²(ℝ³)`.  Route: `y ↦ kinFT (conj ∘ H·y) κ_n`
is a.e. strongly measurable by Fubini measurability (`AEStronglyMeasurable.integral_prod_right'`
applied to the jointly continuous integrand `(w,y) ↦ exp(-i⟪κ,w⟫)·conj (H w y)`); it is bounded by
`B·ℓ³` with `B` a global bound on `‖H‖` (`HasCompactSupport.exists_bound_of_continuous` for
`uncurry H`, whose compact support comes from `hHs` and `boxL_compact`) and it *vanishes for
`y ∉ boxL ℓ`*, so `‖·‖² ≤ (B ℓ³)²·1_{boxL ℓ}`, which is integrable
(`Work.BoseB4.BoxData.volume_boxL_toReal`: `volume.real (boxL ℓ) = ℓ³`).  Conclude with
`Integrable.mono'` and `MeasureTheory.memLp_two_iff_integrable_sq_norm`. -/
theorem memLp_kinFT_conjSlice {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (n : Fin 3 → ℤ) :
    MeasureTheory.MemLp (fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
        (Work.BoseBoxFock.kappaL ℓ n)) 2 MeasureTheory.volume := by
  classical
  -- Prove the statement for the explicit integral form of `kinFT`; the two are
  -- definitionally equal (`kinFT u p = ∫ w, exp(-i⟪p,w⟫) * u w`).
  have key : MeasureTheory.MemLp (fun y : EuclideanSpace ℝ (Fin 3) =>
      ∫ w : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) w : ℝ) : ℂ)))
          * (starRingEnd ℂ) (H w y)) 2 MeasureTheory.volume := by
    set κ : EuclideanSpace ℝ (Fin 3) := Work.BoseBoxFock.kappaL ℓ n with hκ
    have hcont : Continuous (Function.uncurry H) := hH.continuous
    -- a global bound `‖H w y‖ ≤ M`: `H` is continuous and supported in the compact
    -- `boxL ℓ × boxL ℓ` (by `hHs`, since `H w y = 0` as soon as one variable leaves the box).
    obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
      ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
        (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ))
      hcont.continuousOn
    set M : ℝ := max B 0 with hM
    have hbound : ∀ w y, ‖H w y‖ ≤ M := by
      intro w y
      by_cases h : (w, y) ∈ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ
      · have h1 : ‖H w y‖ ≤ B := by simpa using hB (w, y) h
        exact le_trans h1 (le_max_left B 0)
      · have hz : H w y = 0 := by
          by_contra hne
          exact h (hHs w y hne)
        rw [hz, norm_zero]
        exact le_max_right B 0
    -- joint continuity of the integrand
    have hFcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * ((inner ℝ κ p.1 : ℝ) : ℂ))) * (starRingEnd ℂ) (H p.1 p.2)) := by
      apply Continuous.mul
      · apply Complex.continuous_exp.comp
        apply Continuous.neg.comp
        apply Continuous.mul continuous_const
        exact Complex.continuous_ofReal.comp
          (Continuous.inner continuous_const continuous_fst)
      · exact continuous_star.comp hcont
    -- Fubini measurability of the slice
    have hmeas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        ∫ w : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)) volume :=
      ((hFcont.comp continuous_swap).aestronglyMeasurable).integral_prod_right'
    have hSmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
      Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
    have hKc : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) :=
      Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
    have hInd0 : Integrable
        ((Work.BoseK15.corpusBox.boxL ℓ).indicator (1 : EuclideanSpace ℝ (Fin 3) → ℝ)) volume := by
      rw [MeasureTheory.integrable_indicator_iff hSmeas]
      exact MeasureTheory.integrableOn_const (C := (1:ℝ)) (ne_of_lt hKc.measure_lt_top) (by simp)
    -- the integrand is dominated by `M·1_{boxL ℓ}(w)`, uniformly in `y`
    have hpt : ∀ y w : EuclideanSpace ℝ (Fin 3),
        ‖Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)‖
          ≤ M * (Work.BoseK15.corpusBox.boxL ℓ).indicator
              (1 : EuclideanSpace ℝ (Fin 3) → ℝ) w := by
      intro y w
      by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one, norm_mul]
        have h1 : ‖Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ)))‖ = 1 := by
          rw [Complex.norm_exp]; simp
        rw [h1, one_mul]
        simpa using hbound w y
      · rw [Set.indicator_of_notMem hw, mul_zero]
        have hz : H w y = 0 := by
          by_contra hne
          exact hw (hHs w y hne).1
        rw [hz, map_zero, mul_zero, norm_zero]
    -- the slice vanishes outside the box
    have hzero : ∀ y : EuclideanSpace ℝ (Fin 3), y ∉ Work.BoseK15.corpusBox.boxL ℓ →
        (∫ w : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)) = 0 := by
      intro y hy
      have hfun : (fun w : EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y))
            = fun _ => 0 := by
        funext w
        have hz : H w y = 0 := by
          by_contra hne
          exact hy (hHs w y hne).2
        simp [hz]
      rw [hfun, integral_zero]
    -- the pointwise bound `‖g y‖ ≤ B ℓ³`
    have hgb : ∀ y : EuclideanSpace ℝ (Fin 3),
        ‖∫ w : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)‖
            ≤ M * ℓ^3 := by
      intro y
      have hmaj : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
          M * (Work.BoseK15.corpusBox.boxL ℓ).indicator
              (1 : EuclideanSpace ℝ (Fin 3) → ℝ) w) volume :=
        hInd0.const_mul M
      have hcy : Continuous (fun w : EuclideanSpace ℝ (Fin 3) =>
          ‖Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)‖) :=
        (hFcont.comp (Continuous.prodMk_left y)).norm
      have hint : Integrable (fun w : EuclideanSpace ℝ (Fin 3) =>
          ‖Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)‖) volume :=
        Integrable.mono' hmaj hcy.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun w => by simpa using hpt y w))
      calc ‖∫ w : EuclideanSpace ℝ (Fin 3),
              Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)‖
          ≤ ∫ w : EuclideanSpace ℝ (Fin 3),
              ‖Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ w : EuclideanSpace ℝ (Fin 3),
              M * (Work.BoseK15.corpusBox.boxL ℓ).indicator
                (1 : EuclideanSpace ℝ (Fin 3) → ℝ) w :=
            integral_mono_ae hint hmaj (Filter.Eventually.of_forall (fun w => hpt y w))
        _ = M * ∫ w : EuclideanSpace ℝ (Fin 3),
              (Work.BoseK15.corpusBox.boxL ℓ).indicator
                (1 : EuclideanSpace ℝ (Fin 3) → ℝ) w := by
            rw [MeasureTheory.integral_const_mul]
        _ = M * (volume.real (Work.BoseK15.corpusBox.boxL ℓ)) := by
            rw [MeasureTheory.integral_indicator_one hSmeas]
        _ = M * ℓ^3 := by
            rw [MeasureTheory.measureReal_def,
              Work.BoseB4.BoxData.volume_boxL_toReal Work.BoseK15.corpusBox hℓ]
    -- `‖g y‖² ≤ (B ℓ³)² 1_{boxL ℓ}(y)`, an integrable majorant
    have hmaj2 : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        (M * ℓ^3)^2 * (Work.BoseK15.corpusBox.boxL ℓ).indicator
            (1 : EuclideanSpace ℝ (Fin 3) → ℝ) y) volume :=
      hInd0.const_mul ((M * ℓ^3)^2)
    have hInt : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        ‖∫ w : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) (H w y)‖ ^ 2) volume := by
      refine Integrable.mono' hmaj2 (hmeas.norm.pow 2) ?_
      filter_upwards with y
      by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Real.norm_of_nonneg (by positivity), Set.indicator_of_mem hy, Pi.one_apply, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgb y) 2
      · simp [hzero y hy, Set.indicator_of_notMem hy]
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).mpr hInt
  exact key

end Work.BoseBoxFock.L1Tails.kinFTSlice
