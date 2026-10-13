import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonAux

open MeasureTheory Filter
open scoped Topology ENNReal

/-- The increasing family of subintervals `(1/(m+1), π/2 - 1/(m+1))` exhausting `(0, π/2)`. -/
private def sliceIoo (m : ℕ) : Set ℝ :=
  Set.Ioo (1 / ((m : ℝ) + 1)) (Real.pi / 2 - 1 / ((m : ℝ) + 1))

private lemma measurableSet_sliceIoo (m : ℕ) : MeasurableSet (sliceIoo m) := measurableSet_Ioo

private lemma sliceIoo_left_pos (m : ℕ) : 0 < 1 / ((m : ℝ) + 1) :=
  div_pos one_pos (by positivity)

private lemma sliceIoo_subset (m : ℕ) : sliceIoo m ⊆ Set.Ioo 0 (Real.pi / 2) :=
  Set.Ioo_subset_Ioo (le_of_lt (sliceIoo_left_pos m))
    (sub_le_self _ (le_of_lt (sliceIoo_left_pos m)))

private lemma sliceIoo_mono_succ (m : ℕ) : sliceIoo m ⊆ sliceIoo (m + 1) := by
  have hm : 1 / (((m + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast
    linarith
  refine Set.Ioo_subset_Ioo hm ?_
  linarith

private lemma sliceIoo_mono : Monotone sliceIoo := monotone_nat_of_le_succ sliceIoo_mono_succ

private lemma mem_sliceIoo_cover {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∃ m : ℕ, x ∈ sliceIoo m := by
  have hε : 0 < min x (Real.pi / 2 - x) := lt_min hx.1 (by linarith [hx.2])
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨m, lt_of_lt_of_le hm (min_le_left _ _), ?_⟩
  have h2 := lt_of_lt_of_le hm (min_le_right _ _)
  linarith

/-- **From integral bounds on shrinking intervals to global integrability.**

If `g` is continuous and nonnegative on `(0, π/2)`, if the subintervals `(u n, v n)` shrink to
`(0, π/2)` and the integrals of `g` over them are bounded by `L n → C`, then `g` is integrable
on `(0, π/2)` and its integral is at most `C`. -/
theorem integrableOn_Ioo_of_le {g : ℝ → ℝ} {u v L : ℕ → ℝ} {C : ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hnn : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ g x)
    (hu : Filter.Tendsto u Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hv : Filter.Tendsto v Filter.atTop (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))))
    (huv : ∀ᶠ n in Filter.atTop, u n < v n)
    (hL : Filter.Tendsto L Filter.atTop (nhds C))
    (hb : ∀ n : ℕ, (∫ x in Set.Ioo (u n) (v n), g x) ≤ L n) :
    MeasureTheory.IntegrableOn g (Set.Ioo 0 (Real.pi / 2)) ∧
      (∫ x in Set.Ioo 0 (Real.pi / 2), g x) ≤ C := by
  classical
  -- ## Eventual properties of the two moving endpoints
  have hu0 : Tendsto u atTop (𝓝 (0 : ℝ)) := hu.mono_right nhdsWithin_le_nhds
  have hv0 : Tendsto v atTop (𝓝 (Real.pi / 2)) := hv.mono_right nhdsWithin_le_nhds
  have hu_pos : ∀ᶠ n in atTop, 0 < u n := hu.eventually self_mem_nhdsWithin
  have hv_lt : ∀ᶠ n in atTop, v n < Real.pi / 2 := hv.eventually self_mem_nhdsWithin
  -- the interval `(u n, v n)` lies in `(0, π/2)` and `g` is integrable there
  have hgood : ∀ᶠ n in atTop,
      (Set.Ioo (u n) (v n) ⊆ Set.Ioo 0 (Real.pi / 2))
        ∧ (u n < v n) ∧ IntegrableOn g (Set.Ioo (u n) (v n)) := by
    filter_upwards [hu_pos, hv_lt, huv] with n hn1 hn2 hn3
    refine ⟨Set.Ioo_subset_Ioo (le_of_lt hn1) (le_of_lt hn2), hn3, ?_⟩
    have hIcc : Set.Icc (u n) (v n) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      fun x hx => ⟨lt_of_lt_of_le hn1 hx.1, lt_of_le_of_lt hx.2 hn2⟩
    exact ((hg.mono hIcc).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  -- ## `C` is nonnegative
  have hC0 : 0 ≤ C := by
    refine ge_of_tendsto hL ?_
    filter_upwards [hgood] with n hn
    refine le_trans (integral_nonneg_of_ae ?_) (hb n)
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => hnn x (hn.1 hx))
  -- ## The `lintegral` of `g` over `(0, π/2)` is at most `ofReal C`
  have hmain : ∫⁻ x in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (g x) ≤ ENNReal.ofReal C := by
    let F : ℕ → ℝ → ℝ≥0∞ := fun m =>
      (sliceIoo m).indicator (fun y => ENNReal.ofReal (g y))
    have hF_meas : ∀ m, AEMeasurable (F m) volume := by
      intro m
      show AEMeasurable ((sliceIoo m).indicator (fun y => ENNReal.ofReal (g y))) volume
      refine (aemeasurable_indicator_iff measurableSet_Ioo).mpr ?_
      exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (((hg.mono (sliceIoo_subset m)).aestronglyMeasurable measurableSet_Ioo).aemeasurable)
    have hF_mono : Monotone F := by
      intro m m' hmm'
      show (sliceIoo m).indicator (fun y => ENNReal.ofReal (g y))
        ≤ (sliceIoo m').indicator (fun y => ENNReal.ofReal (g y))
      intro x
      by_cases hx : x ∈ sliceIoo m
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (sliceIoo_mono hmm' hx)]
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    have hSup : ∀ x, (⨆ m, F m x)
        = (Set.Ioo 0 (Real.pi / 2)).indicator (fun y => ENNReal.ofReal (g y)) x := by
      intro x
      by_cases hx : x ∈ Set.Ioo 0 (Real.pi / 2)
      · obtain ⟨m₀, hm₀⟩ := mem_sliceIoo_cover hx
        rw [Set.indicator_of_mem hx (fun y => ENNReal.ofReal (g y))]
        refine le_antisymm (iSup_le (fun m => ?_)) ?_
        · by_cases hm : x ∈ sliceIoo m
          · rw [show F m x = ENNReal.ofReal (g x)
              from Set.indicator_of_mem hm (fun y => ENNReal.ofReal (g y))]
          · rw [show F m x = 0
              from Set.indicator_of_notMem hm (fun y => ENNReal.ofReal (g y))]
            exact zero_le
        · calc ENNReal.ofReal (g x)
              = (sliceIoo m₀).indicator (fun y => ENNReal.ofReal (g y)) x :=
                (Set.indicator_of_mem hm₀ (fun y => ENNReal.ofReal (g y))).symm
            _ ≤ ⨆ m, F m x := le_iSup (fun m => F m x) m₀
      · rw [Set.indicator_of_notMem hx (fun y => ENNReal.ofReal (g y))]
        have hzero : ∀ m, F m x = 0 := fun m =>
          Set.indicator_of_notMem (fun h => hx (sliceIoo_subset m h))
            (fun y => ENNReal.ofReal (g y))
        rw [show (⨆ m, F m x) = 0 from
          le_antisymm (iSup_le (fun m => le_of_eq (hzero m))) zero_le]
    -- each `sliceIoo m` integral is bounded by `ofReal C`
    have hlin : ∀ m, ∫⁻ x in sliceIoo m, ENNReal.ofReal (g x) ≤ ENNReal.ofReal C := by
      intro m
      have hEv : ∀ᶠ n in atTop, sliceIoo m ⊆ Set.Ioo (u n) (v n) := by
        have h1 : ∀ᶠ n in atTop, u n < 1 / ((m : ℝ) + 1) :=
          hu0.eventually (isOpen_Iio.mem_nhds (sliceIoo_left_pos m))
        have h2 : ∀ᶠ n in atTop, Real.pi / 2 - 1 / ((m : ℝ) + 1) < v n :=
          hv0.eventually (isOpen_Ioi.mem_nhds (sub_lt_self _ (sliceIoo_left_pos m)))
        filter_upwards [h1, h2] with n hn1 hn2
        exact Set.Ioo_subset_Ioo (le_of_lt hn1) (le_of_lt hn2)
      have hEv2 : ∀ᶠ n in atTop,
          ∫⁻ x in sliceIoo m, ENNReal.ofReal (g x) ≤ ENNReal.ofReal (L n) := by
        filter_upwards [hEv, hgood] with n hn hn2
        calc
          ∫⁻ x in sliceIoo m, ENNReal.ofReal (g x)
              ≤ ∫⁻ x in Set.Ioo (u n) (v n), ENNReal.ofReal (g x) :=
                lintegral_mono' (Measure.restrict_mono hn le_rfl) le_rfl
          _ = ENNReal.ofReal (∫ x in Set.Ioo (u n) (v n), g x) :=
                (ofReal_integral_eq_lintegral_ofReal hn2.2.2
                  (ae_restrict_of_forall_mem measurableSet_Ioo
                    (fun x hx => hnn x (hn2.1 hx)))).symm
          _ ≤ ENNReal.ofReal (L n) := ENNReal.ofReal_le_ofReal (hb n)
      exact ge_of_tendsto ((ENNReal.continuous_ofReal.tendsto C).comp hL) hEv2
    have hmono_ae : ∀ᶠ x in ae (volume : Measure ℝ), Monotone (fun m => F m x) :=
      Eventually.of_forall (fun x m m' hmm' => hF_mono hmm' x)
    have h_iSup := lintegral_iSup' hF_meas hmono_ae
    calc
      ∫⁻ x in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (g x)
          = ∫⁻ x, (Set.Ioo 0 (Real.pi / 2)).indicator (fun y => ENNReal.ofReal (g y)) x :=
            (lintegral_indicator measurableSet_Ioo _).symm
      _ = ∫⁻ x, (⨆ m, F m x) :=
            lintegral_congr (fun x => (hSup x).symm)
      _ = ⨆ m, ∫⁻ x, F m x := h_iSup
      _ = ⨆ m, ∫⁻ x in sliceIoo m, ENNReal.ofReal (g x) := by
            refine iSup_congr (fun m => ?_)
            show ∫⁻ x, (sliceIoo m).indicator (fun y => ENNReal.ofReal (g y)) x
              = ∫⁻ x in sliceIoo m, ENNReal.ofReal (g x)
            rw [lintegral_indicator (measurableSet_sliceIoo m)]
      _ ≤ ENNReal.ofReal C := iSup_le (fun m => hlin m)
  -- ## Conclusion
  have hfin : ∫⁻ x in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (g x) < ⊤ :=
    lt_of_le_of_lt hmain ENNReal.ofReal_lt_top
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 (Real.pi / 2))] g :=
    ae_restrict_of_forall_mem measurableSet_Ioo hnn
  have haesm : AEStronglyMeasurable g (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  refine ⟨⟨haesm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_of_ae_nonneg hnonneg]
    exact hfin
  · rw [integral_eq_lintegral_of_nonneg_ae hnonneg haesm]
    calc
      (∫⁻ x in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (g x)).toReal
          ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
      _ = C := ENNReal.toReal_ofReal hC0

end Work.EllipticEst.Core.i0Aux.SliceAgmonAux
