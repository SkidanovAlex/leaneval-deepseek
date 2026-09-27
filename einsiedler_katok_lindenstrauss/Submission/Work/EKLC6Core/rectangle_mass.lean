import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.near_indicator
import Submission.Work.EKLC6Core.measurable_shift_integral
import Submission.Work.EKLC6Core.rect_mass_factor
import Submission.Work.EKLC6Core.rect_mass_ccform
import Submission.Work.EKLC6Core.rect_mass_double
import Submission.Work.EKLC6Core.rect_mass_bump
import Submission.Work.EKLProd.sl3EntryBox_compact

open MeasureTheory

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.EKLC6Core

open Work.EKLContract

/-- Upgrading the test-function (compactly-supported continuous) form of the product structure
`νH x = c · ∫∫ f(g*u) ∂νU x ∂νT x` for `f ∈ C_c(SL3,ℝ)` (the conclusion of `P_Product`) to the
masses of *product rectangles*: for compact `AT ⊆ T`, `AU ⊆ U` one has
`νH x (AT * AU) = c * νT x AT * νU x AU`, with `AT * AU` written `Set.image2 (· * ·)`.

Proof sketch: approximate `1_{AT*AU}` from above by a decreasing sequence `f n ∈ C_c` with
values in `[0,1]`, all supported in a fixed compact set (`Work.EKLC6Core.near_indicator`).
By `hP`, `∫ f n ∂νH x = c * ∫ g, (∫ u, f n (g*u) ∂νU x) ∂νT x`; both sides converge: the left by
dominated convergence (dominated by `1_{K'}`, integrable for `νH x`), the right by dominated
convergence for the inner integral (dominated by the indicator of the compact set
`g ⁻¹' K' ∩ U`) and for the outer one, dominated by `g ↦ ∫ u, f 0 (g*u) ∂νU x`, which is
measurable by `Work.EKLC6Core.measurable_shift_integral`.  The required integrability of that
last dominator follows by applying `hP` to the `C_c` function `f 0 + θ`, where `θ ≥ 0` is a bump
at `1` with `θ 1 > 0`: the hypotheses then say that the real number
`∫ g, (∫ u, (f 0 + θ) (g*u) ∂νU x) ∂νT x` is positive and finite, and since it is the `toReal` of
the lintegral of the nonnegative measurable dominator, that lintegral is finite.  Finally the
double integral of `1_{AT*AU}` factorizes as `νT x AT · νU x AU` because, by `hdisj`, the product
map is injective on `T × U` and `νT x`, `νU x` are carried by `T`, `U`. -/
theorem rectangle_mass {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {νH νT νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH XT XU : Set Work.EKLContract.X3}
    (hLH : Work.EKLContract.IsLeafwise μ H νH XH)
    (hLT : Work.EKLContract.IsLeafwise μ T νT XT)
    (hLU : Work.EKLContract.IsLeafwise μ U νU XU)
    (x : Work.EKLContract.X3) (hxH : x ∈ XH) (hxT : x ∈ XT) (hxU : x ∈ XU)
    {c : ℝ} (hc : 0 < c)
    (hP : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∫ g, f g ∂(νH x) = c * ∫ g, (∫ u, f (g * u) ∂(νU x)) ∂(νT x))
    {AT AU : Set Work.EKLContract.SL3} (hATc : IsCompact AT) (hAUc : IsCompact AU)
    (hAT : AT ⊆ (T : Set Work.EKLContract.SL3)) (hAU : AU ⊆ (U : Set Work.EKLContract.SL3)) :
    νH x (Set.image2 (fun a b : Work.EKLContract.SL3 => a * b) AT AU)
      = ENNReal.ofReal c * (νT x AT * νU x AU) := by
  classical
  haveI hHf : IsFiniteMeasureOnCompacts (νH x) := hLH.radon x hxH
  haveI hTf : IsFiniteMeasureOnCompacts (νT x) := hLT.radon x hxT
  haveI hUf : IsFiniteMeasureOnCompacts (νU x) := hLU.radon x hxU
  have hcarT : νT x (T : Set SL3)ᶜ = 0 := hLT.carried x hxT
  have hcarU : νU x (U : Set SL3)ᶜ = 0 := hLU.carried x hxU
  set A : Set SL3 := Set.image2 (fun a b : SL3 => a * b) AT AU with hA
  have hAc : IsCompact A := by
    rw [hA]
    have heq : Set.image2 (fun a b : SL3 => a * b) AT AU
        = (fun p : SL3 × SL3 => p.1 * p.2) '' (AT ×ˢ AU) := by
      ext z
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [heq]
    exact (hATc.prod hAUc).image (by fun_prop)
  have hAmeas : MeasurableSet A := hAc.isClosed.measurableSet
  obtain ⟨f, K', hK'c, hK'supp, hfnn, hfone, hfle, hfmono, hftend⟩ := near_indicator hAc
  have hfm : ∀ n, Measurable (fun y : SL3 => f n y) := fun n => (f n).continuous.measurable
  have hpre_c : ∀ g : SL3, IsCompact ((fun u : SL3 => g * u) ⁻¹' K') := by
    intro g
    have heq : (fun u : SL3 => g * u) ⁻¹' K' = (fun w : SL3 => g⁻¹ * w) '' K' := by
      ext u
      constructor
      · intro hu
        exact ⟨g * u, hu, by group⟩
      · rintro ⟨w, hw, rfl⟩
        show g * (g⁻¹ * w) ∈ K'
        rwa [show g * (g⁻¹ * w) = w from by group]
    rw [heq]
    exact hK'c.image (by fun_prop)
  -- finiteness of the inner lintegrals
  have hfin_g : ∀ n g, (∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x)) ≠ ⊤ := by
    intro n g
    have hle1 : (∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x))
        ≤ ∫⁻ u, (K'.indicator (fun _ : SL3 => (1 : ENNReal))) (g * u) ∂(νU x) := by
      refine lintegral_mono (fun u => ?_)
      by_cases h : g * u ∈ K'
      · rw [Set.indicator_of_mem h]
        exact ENNReal.ofReal_le_one.mpr (hfle n (g * u))
      · rw [Set.indicator_of_notMem h]
        have h0 : f n (g * u) = 0 := by
          by_contra hne
          exact h (hK'supp n (by simpa [Function.mem_support] using hne))
        rw [h0, ENNReal.ofReal_zero]
    have hle2 : (∫⁻ u, (K'.indicator (fun _ : SL3 => (1 : ENNReal))) (g * u) ∂(νU x))
        = (νU x) ((fun u : SL3 => g * u) ⁻¹' K') := by
      rw [show (fun u : SL3 => (K'.indicator (fun _ : SL3 => (1 : ENNReal))) (g * u))
          = ((fun u : SL3 => g * u) ⁻¹' K').indicator (fun _ : SL3 => (1 : ENNReal)) from by
            funext u
            by_cases h : g * u ∈ K'
            · rw [Set.indicator_of_mem h,
                Set.indicator_of_mem (show u ∈ (fun u : SL3 => g * u) ⁻¹' K' from h)]
            · rw [Set.indicator_of_notMem h,
                Set.indicator_of_notMem (show u ∉ (fun u : SL3 => g * u) ⁻¹' K' from h)]]
      have h := lintegral_indicator_const (μ := νU x) (s := (fun u : SL3 => g * u) ⁻¹' K')
        (measurableSet_preimage ((continuous_const.mul continuous_id).measurable)
          hK'c.isClosed.measurableSet) (1 : ENNReal)
      rw [one_mul] at h
      exact h
    exact (lt_of_le_of_lt (le_of_le_of_eq hle1 hle2) (hUf.lt_top_of_isCompact (hpre_c g))).ne
  -- a compact set of positive νH x-measure inside V (1/2)
  set K₀ : Set SL3 := {g : SL3 | ∀ i j : Fin 3,
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - (1/2 : ℝ) ≤ g i j ∧
      g i j ≤ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + (1/2 : ℝ)} with hK₀
  have hK₀c : IsCompact K₀ := by
    rw [hK₀]
    exact Work.EKLProd.sl3EntryBox_compact _ _
  have hVsub : V (1/2 : ℝ) ⊆ K₀ := by
    intro g hg
    rw [hK₀]
    intro i j
    have h := abs_lt.mp (hg i j)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hVpos : 0 < νH x (V (1/2 : ℝ)) := hLH.pos x hxH (1/2) (by norm_num)
  have hK₀pos : 0 < νH x K₀ := lt_of_lt_of_le hVpos (measure_mono hVsub)
  obtain ⟨θ, hθnn, hθle, hθone, hθpos⟩ := rect_mass_bump hHf hK₀c hK₀pos
  -- the perturbed function f 0 + θ
  have hsum_nn : ∀ y : SL3, 0 ≤ (f 0 + θ) y := by
    intro y
    rw [CompactlySupportedContinuousMap.add_apply]
    exact add_nonneg (hfnn 0 y) (hθnn y)
  have hcc2 := rect_mass_ccform hHf hUf hP (f 0 + θ) hsum_nn
  have hL'fin : (∫⁻ y, ENNReal.ofReal ((f 0 + θ) y) ∂(νH x)) ≠ ⊤ := by
    have hb : (∫⁻ y, ENNReal.ofReal ((f 0 + θ) y) ∂(νH x))
        ≤ ∫⁻ y, (K' ∪ tsupport (⇑θ)).indicator (fun _ : SL3 => (2 : ENNReal)) y ∂(νH x) := by
      refine lintegral_mono (fun y => ?_)
      by_cases hy : y ∈ K' ∪ tsupport (⇑θ)
      · rw [Set.indicator_of_mem hy]
        have h1 : (f 0 + θ) y ≤ 2 := by
          rw [CompactlySupportedContinuousMap.add_apply]
          linarith [hfle 0 y, hθle y]
        exact le_trans (ENNReal.ofReal_le_ofReal h1) (by norm_num)
      · rw [Set.indicator_of_notMem hy]
        have hy1 : y ∉ K' := fun h => hy (Set.mem_union_left _ h)
        have hy2 : y ∉ tsupport (⇑θ) := fun h => hy (Set.mem_union_right _ h)
        have h0 : f 0 y = 0 := by
          by_contra hne
          exact hy1 (hK'supp 0 (by simpa [Function.mem_support] using hne))
        have h0' : θ y = 0 := image_eq_zero_of_notMem_tsupport hy2
        rw [CompactlySupportedContinuousMap.add_apply, h0, h0', add_zero, ENNReal.ofReal_zero]
    refine ne_top_of_le_ne_top ?_ hb
    rw [lintegral_indicator_const
      ((hK'c.union θ.hasCompactSupport).isClosed.measurableSet) (2 : ENNReal)]
    exact ENNReal.mul_ne_top (by norm_num) ((hHf.lt_top_of_isCompact (hK'c.union θ.hasCompactSupport)).ne)
  have hL'pos : 0 < (∫⁻ y, ENNReal.ofReal ((f 0 + θ) y) ∂(νH x)) := by
    have hpoint : ∀ y : SL3, K₀.indicator (fun _ : SL3 => (1 : ENNReal)) y
        ≤ ENNReal.ofReal ((f 0 + θ) y) := by
      intro y
      by_cases hy : y ∈ K₀
      · rw [Set.indicator_of_mem hy]
        have h1 : (1 : ℝ) ≤ (f 0 + θ) y := by
          rw [CompactlySupportedContinuousMap.add_apply, hθone y hy]
          linarith [hfnn 0 y]
        exact le_trans (le_of_eq ENNReal.ofReal_one.symm) (ENNReal.ofReal_le_ofReal h1)
      · rw [Set.indicator_of_notMem hy]
        exact bot_le
    have hb : (νH x) K₀ ≤ (∫⁻ y, ENNReal.ofReal ((f 0 + θ) y) ∂(νH x)) := by
      calc (νH x) K₀
          = ∫⁻ y, K₀.indicator (fun _ : SL3 => (1 : ENNReal)) y ∂(νH x) := by
            rw [lintegral_indicator_const hK₀c.isClosed.measurableSet (1 : ENNReal), one_mul]
        _ ≤ ∫⁻ y, ENNReal.ofReal ((f 0 + θ) y) ∂(νH x) := lintegral_mono hpoint
    exact lt_of_lt_of_le hK₀pos hb
  have hR'ne : (∫⁻ g, (∫⁻ u, ENNReal.ofReal ((f 0 + θ) (g * u)) ∂(νU x)) ∂(νT x)) ≠ ⊤ := by
    have hRpos : 0 < (∫⁻ g, (∫⁻ u, ENNReal.ofReal ((f 0 + θ) (g * u)) ∂(νU x)) ∂(νT x)).toReal := by
      have h1 : 0 < c * (∫⁻ g, (∫⁻ u, ENNReal.ofReal ((f 0 + θ) (g * u)) ∂(νU x)) ∂(νT x)).toReal := by
        rw [← hcc2]
        exact ENNReal.toReal_pos hL'pos.ne' hL'fin
      by_contra hle
      push Not at hle
      nlinarith [hc, h1, hle]
    intro htop
    rw [htop] at hRpos
    simp at hRpos
  have hfin_int : (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f 0 (g * u)) ∂(νU x)) ∂(νT x)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hR'ne ?_
    refine lintegral_mono (fun g => lintegral_mono (fun u => ?_))
    rw [CompactlySupportedContinuousMap.add_apply]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hθnn (g * u)))
  -- the LHS limit
  have hL_tend : Filter.Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (f n y) ∂(νH x)) Filter.atTop
      (nhds (νH x A)) := by
    have hL_eq : (∫⁻ y, ENNReal.ofReal ((A.indicator (fun _ : SL3 => (1 : ℝ))) y) ∂(νH x))
        = νH x A := by
      rw [show (fun y : SL3 => ENNReal.ofReal ((A.indicator (fun _ : SL3 => (1 : ℝ))) y))
          = A.indicator (fun _ : SL3 => (1 : ENNReal)) from by
            funext y
            by_cases hy : y ∈ A
            · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ENNReal.ofReal_one]
            · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.ofReal_zero]]
      rw [lintegral_indicator_const hAmeas (1 : ENNReal), one_mul]
    have h := tendsto_lintegral_of_dominated_convergence (μ := νH x)
      (F := fun n y => ENNReal.ofReal (f n y))
      (f := fun y => ENNReal.ofReal ((A.indicator (fun _ : SL3 => (1 : ℝ))) y))
      (K'.indicator (fun _ : SL3 => (1 : ENNReal)))
      (fun n => ENNReal.measurable_ofReal.comp (hfm n))
      (fun n => by
        filter_upwards with y
        by_cases hy : y ∈ K'
        · rw [Set.indicator_of_mem hy]
          exact ENNReal.ofReal_le_one.mpr (hfle n y)
        · rw [Set.indicator_of_notMem hy]
          have h0 : f n y = 0 := by
            by_contra hne
            exact hy (hK'supp n (by simpa [Function.mem_support] using hne))
          rw [h0, ENNReal.ofReal_zero])
      (by
        rw [lintegral_indicator_const hK'c.isClosed.measurableSet (1 : ENNReal), one_mul]
        exact (hHf.lt_top_of_isCompact hK'c).ne)
      (by
        filter_upwards with y
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hftend y))
    rwa [hL_eq] at h
  -- the RHS limit
  have hmeasG : ∀ n, Measurable (fun g : SL3 => ∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x)) := by
    intro n
    have hcongr : (fun g : SL3 => ∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x))
        = fun g => ENNReal.ofReal (∫ u, f n (g * u) ∂(νU x)) := by
      funext g
      have h1 := integral_eq_lintegral_of_nonneg_ae (μ := νU x) (f := fun u : SL3 => f n (g * u))
        (Filter.Eventually.of_forall (fun u => hfnn n (g * u)))
        (((hfm n).comp (continuous_const.mul continuous_id).measurable).aestronglyMeasurable)
      rw [h1, ENNReal.ofReal_toReal (hfin_g n g)]
    rw [hcongr]
    exact ENNReal.measurable_ofReal.comp (measurable_shift_integral (α := νU x) (f n))
  have hR_tend : Filter.Tendsto
      (fun n => ∫⁻ g, (∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x)) ∂(νT x)) Filter.atTop
      (nhds (∫⁻ g, (∫⁻ u, ENNReal.ofReal (((A.indicator (fun _ : SL3 => (1 : ℝ))) (g * u))) ∂(νU x)) ∂(νT x))) :=
    rect_mass_double hfm
      (Measurable.indicator measurable_const hAmeas)
      hmeasG (fun y => hftend y) hfnn
      (fun n y => hfmono n (n + 1) (Nat.le_succ n) y)
      (fun g => hfin_g 0 g) hfin_int
  -- value of the RHS limit
  have hJ : (∫⁻ g, (∫⁻ u, ENNReal.ofReal (((A.indicator (fun _ : SL3 => (1 : ℝ))) (g * u))) ∂(νU x)) ∂(νT x))
      = νT x AT * νU x AU := by
    have hcongr : (fun g : SL3 => ∫⁻ u, ENNReal.ofReal (((A.indicator (fun _ : SL3 => (1 : ℝ))) (g * u))) ∂(νU x))
        = fun g => ∫⁻ u, (A.indicator (fun _ : SL3 => (1 : ENNReal))) (g * u) ∂(νU x) := by
      funext g
      refine lintegral_congr (fun u => ?_)
      by_cases h : g * u ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, ENNReal.ofReal_one]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.ofReal_zero]
    rw [hcongr, hA]
    exact rect_mass_factor hdisj hcarT hcarU hATc.isClosed.measurableSet hAUc.isClosed.measurableSet hAT hAU
  have hJne : νT x AT * νU x AU ≠ ⊤ :=
    ENNReal.mul_ne_top (hTf.lt_top_of_isCompact hATc).ne (hUf.lt_top_of_isCompact hAUc).ne
  have hLne : νH x A ≠ ⊤ := (hHf.lt_top_of_isCompact hAc).ne
  -- limits of the toReals
  have hlim2 : Filter.Tendsto
      (fun n => (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x)) ∂(νT x)).toReal) Filter.atTop
      (nhds ((νT x AT * νU x AU).toReal)) :=
    (ENNReal.tendsto_toReal hJne).comp (hJ ▸ hR_tend)
  have hlim1 : Filter.Tendsto
      (fun n => (∫⁻ y, ENNReal.ofReal (f n y) ∂(νH x)).toReal) Filter.atTop
      (nhds ((νH x A).toReal)) :=
    (ENNReal.tendsto_toReal hLne).comp hL_tend
  have hPn : ∀ n, (∫⁻ y, ENNReal.ofReal (f n y) ∂(νH x)).toReal
      = c * (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x)) ∂(νT x)).toReal :=
    fun n => rect_mass_ccform hHf hUf hP (f n) (hfnn n)
  have heq : (νH x A).toReal = c * (νT x AT * νU x AU).toReal := by
    refine tendsto_nhds_unique hlim1 ?_
    rw [show (fun n => (∫⁻ y, ENNReal.ofReal (f n y) ∂(νH x)).toReal)
        = fun n => c * (∫⁻ g, (∫⁻ u, ENNReal.ofReal (f n (g * u)) ∂(νU x)) ∂(νT x)).toReal
        from funext hPn]
    exact hlim2.const_mul c
  -- conclude
  have hRHSne : ENNReal.ofReal c * (νT x AT * νU x AU) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJne
  have htoReal : (νH x A).toReal = (ENNReal.ofReal c * (νT x AT * νU x AU)).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
    exact heq
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp htoReal with h | ⟨-, h2⟩ | ⟨h2, -⟩
  · exact h
  · exact absurd h2 hRHSne
  · exact absurd h2 hLne

end Work.EKLC6Core
