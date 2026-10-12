import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBesselDefs
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.slotU_measurable_sqIntegrable`

The measurability and square-integrability of the **slot integral**

    ŷ ↦ U_l(ŷ) := ∫ z, conj(e_l z) · Θ(σ_j z ŷ)          (`σ_j = sliceRestore j`),

which is the quantity appearing when the `j`-th slot of a first-quantised box sum is isolated
(`slotJ`, `slotBesselDefs`): after fixing the `n − 1` remaining coordinates `ŷ`, the slot becomes a
one-particle (finite-dimensional) expression in the vector `U_l = ∫ z, conj(e_l z) Θ(σ z ŷ)`
(see the `slotJ` docstring).  For the Fubini/slicing reduction one needs `U_l` to be a measurable,
`L²` function of `ŷ`.

Everything is elementary:

* `(z, ŷ) ↦ sliceRestore j z ŷ` is *continuous* (each coordinate is a projection), hence the
  integrand `(z, ŷ) ↦ star (e l z) · Θ (sliceRestore j z ŷ)` is jointly measurable; the Bochner
  integral over `z` is therefore strongly measurable in `ŷ`
  (`StronglyMeasurable.integral_prod_right`).
* the integral is **uniformly bounded**: `e l` is bounded and supported in the box `boxL ℓ` of
  finite measure, so `‖U_l(ŷ)‖ ≤ vol(boxL ℓ) · ‖e l‖_∞ · ‖Θ‖_∞` for every `ŷ`
  (`Work.MB.integrable_of_bdd_of_support`, `norm_integral_le_integral_norm`,
  `MeasureTheory.integral_indicator_const`).
* `U_l` **vanishes** outside the set of `ŷ` whose coordinates all lie in `acube ℓ`: if some
  coordinate `ŷ i` (`i ≠ j`) misses the cube, then every configuration `sliceRestore j z ŷ` misses
  the `n`-particle box, where `Θ` vanishes (`hΘsupp`).  That set has finite measure (it is contained
  in the product of the cubes `acube |ℓ|`, of measure `(|ℓ|³)^{n-1}`), so a bounded function
  supported on it is square integrable (`Integrable.mono'`).

-/

open MeasureTheory

namespace Work.BoseBoxFock.PotCubicLowBandAux

/-- The centred cube of side `ℓ` is contained in the centred cube of side `|ℓ|` (for `ℓ < 0` the
former is empty). -/
theorem acube_subset_abs (ℓ : ℝ) :
    Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube |ℓ| := by
  intro y hy
  rw [Submission.BoseGases.mem_acube_iff] at hy ⊢
  intro m
  rcases le_or_gt 0 ℓ with h | h
  · rw [abs_of_nonneg h]; exact hy m
  · exact absurd hy (by
      intro hcon
      have h1 := (hcon m).1
      have h2 := (hcon m).2
      simp only at h1 h2
      linarith)

theorem slotU_measurable_sqIntegrable {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (∀ l : Fin m, AEMeasurable (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
        ∫ z : Work.BoseDict.Sp, star (e l z)
          * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ))) ∧
      (∀ l : Fin m, MeasureTheory.Integrable
        (fun ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp =>
          ‖(∫ z : Work.BoseDict.Sp, star (e l z)
            * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ))‖ ^ 2)) := by
  classical
  choose Ce hCe using hbdd
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  -- the uniform bound on the slot integral
  let M : Fin m → ℝ := fun l => (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal
      * (max (Ce l) 0 * max CΘ 0)
  -- continuity of the slicing map
  have hcont : Continuous (fun p : Work.BoseDict.Sp × ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) =>
      Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j p.1 p.2) := by
    apply continuous_pi
    intro i
    by_cases h : i = j
    · have h1 : (fun p : Work.BoseDict.Sp × ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) =>
          Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j p.1 p.2 i) = fun p => p.1 := by
        funext p; rw [h]
        exact Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore_apply_self j p.1 p.2
      rw [h1]; exact continuous_fst
    · have h1 : (fun p : Work.BoseDict.Sp × ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) =>
          Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j p.1 p.2 i) = fun p => p.2 ⟨i, h⟩ := by
        funext p; exact Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore_apply_of_ne h p.1 p.2
      rw [h1]; exact (continuous_apply _).comp continuous_snd
  -- joint measurability of the integrand (in the variable order of `Function.uncurry`)
  have hF : ∀ l : Fin m, StronglyMeasurable
      (fun p : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) × Work.BoseDict.Sp =>
        star (e l p.2) * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j p.2 p.1)) := by
    intro l
    refine ((Complex.continuous_conj.measurable.comp
      ((hmeas l).comp measurable_snd)).mul ?_).stronglyMeasurable
    exact hΘm.comp ((hcont.comp (continuous_snd.prodMk continuous_fst)).measurable)
  -- the parametrised integral is strongly measurable
  have hgsm : ∀ l : Fin m, StronglyMeasurable
      (fun ŷ : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) =>
        ∫ z : Work.BoseDict.Sp, star (e l z)
          * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)) := by
    intro l
    exact MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (ŷ : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp)) (z : Work.BoseDict.Sp) =>
        star (e l z) * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)) (hF l)
  -- the uniform bound
  have hbound : ∀ l : Fin m, ∀ ŷ : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp),
      ‖∫ z : Work.BoseDict.Sp, star (e l z)
        * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)‖ ≤ M l := by
    intro l ŷ
    have hInt : Integrable (fun z : Work.BoseDict.Sp => star (e l z)
        * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)) := by
      refine Work.MB.integrable_of_bdd_of_support (S := Work.BoseK15.corpusBox.boxL ℓ)
        (C := max (Ce l) 0 * max CΘ 0)
        (hS := Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)
        (hSfin := (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne)
        ?_ ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        have hcontŷ : Continuous (fun z : Work.BoseDict.Sp =>
            Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ) :=
          hcont.comp (continuous_id.prodMk continuous_const)
        exact (Complex.continuous_conj.measurable.comp (hmeas l)).mul (hΘm.comp hcontŷ.measurable)
      · intro z
        rw [norm_mul, norm_star]
        exact mul_le_mul ((hCe l z).trans (le_max_left _ _))
          ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
      · intro z hz
        rw [Function.notMem_support.mp (fun h => hz (hsupp l h)), star_zero, zero_mul]
    have hmaj : Integrable (fun z : Work.BoseDict.Sp =>
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => max (Ce l) 0 * max CΘ 0) z) := by
      refine (integrable_indicator_iff (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)).mpr ?_
      refine integrableOn_const (C := max (Ce l) 0 * max CΘ 0)
        (hs := (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne) ?_
      exact ENNReal.coe_ne_top
    calc ‖∫ z : Work.BoseDict.Sp, star (e l z)
            * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)‖
        ≤ ∫ z : Work.BoseDict.Sp, ‖star (e l z)
            * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ z : Work.BoseDict.Sp,
            (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => max (Ce l) 0 * max CΘ 0) z := by
          refine integral_mono hInt.norm hmaj (fun z => ?_)
          by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
          · rw [Set.indicator_of_mem hz, norm_mul, norm_star]
            exact mul_le_mul ((hCe l z).trans (le_max_left _ _))
              ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
          · rw [Set.indicator_of_notMem hz,
              Function.notMem_support.mp (fun h => hz (hsupp l h)), star_zero, zero_mul, norm_zero]
      _ = M l := by
          rw [MeasureTheory.integral_indicator_const _
            (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)]
          simp only [Measure.real, smul_eq_mul, M]
  constructor
  · intro l
    exact (hgsm l).aemeasurable
  · intro l
    -- the support set of the slot integral has finite measure
    have hSsub : (Set.univ.pi fun _ : {i : Fin n // i ≠ j} => Submission.BoseGases.acube ℓ)
        ⊆ (Set.univ.pi fun _ : {i : Fin n // i ≠ j} => Submission.BoseGases.acube |ℓ|) :=
      Set.pi_mono (fun i _ => acube_subset_abs ℓ)
    have hS'fin : (volume : Measure (({i : Fin n // i ≠ j} → Work.BoseDict.Sp)))
        (Set.univ.pi fun _ : {i : Fin n // i ≠ j} => Submission.BoseGases.acube |ℓ|) < ⊤ := by
      have h : (volume : Measure (({i : Fin n // i ≠ j} → Work.BoseDict.Sp)))
          (Set.univ.pi fun _ : {i : Fin n // i ≠ j} => Submission.BoseGases.acube |ℓ|)
          = ∏ i : {i : Fin n // i ≠ j},
              (volume : Measure Work.BoseDict.Sp) (Submission.BoseGases.acube |ℓ|) := by
        rw [show (volume : Measure (({i : Fin n // i ≠ j} → Work.BoseDict.Sp)))
            = Measure.pi (fun _ : {i : Fin n // i ≠ j} =>
                (volume : Measure Work.BoseDict.Sp)) from rfl]
        exact Measure.pi_pi _ _
      rw [h]
      exact ENNReal.prod_lt_top (fun i _ =>
        Submission.BoseGases.acube_lt_top |ℓ| (abs_nonneg ℓ))
    have hmaj : Integrable (fun ŷ : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) =>
        max (M l ^ 2) 0
        * (Set.univ.pi fun _ : {i : Fin n // i ≠ j} =>
            Submission.BoseGases.acube |ℓ|).indicator (fun _ => (1 : ℝ)) ŷ) := by
      have h1 : Integrable ((Set.univ.pi fun _ : {i : Fin n // i ≠ j} =>
          Submission.BoseGases.acube |ℓ|).indicator (fun _ => (1 : ℝ))) := by
        refine (integrable_indicator_iff ?_).mpr ?_
        · exact MeasurableSet.pi Set.countable_univ
            (fun i _ => Submission.BoseGases.acube_measurable |ℓ|)
        · refine integrableOn_const (C := (1 : ℝ)) (hs := hS'fin.ne) ?_
          exact ENNReal.coe_ne_top
      exact h1.const_mul _
    refine Integrable.mono' (f := fun ŷ : ({i : Fin n // i ≠ j} → Work.BoseDict.Sp) =>
        ‖(∫ z : Work.BoseDict.Sp, star (e l z)
          * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ))‖ ^ 2) hmaj ?_ ?_
    · exact ((hgsm l).norm.pow 2).aestronglyMeasurable
    · filter_upwards with ŷ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hŷ : ŷ ∈ Set.univ.pi (fun _ : {i : Fin n // i ≠ j} => Submission.BoseGases.acube ℓ)
      · have hŷ' : ŷ ∈ Set.univ.pi (fun _ : {i : Fin n // i ≠ j} =>
            Submission.BoseGases.acube |ℓ|) := hSsub hŷ
        rw [Set.indicator_of_mem hŷ', mul_one, max_eq_left (sq_nonneg (M l))]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound l ŷ) 2
      · -- some coordinate of `ŷ` misses the cube: the integrand vanishes identically
        rw [Set.mem_univ_pi] at hŷ
        push Not at hŷ
        obtain ⟨i, hi⟩ := hŷ
        have h0 : (∫ z : Work.BoseDict.Sp, star (e l z)
            * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)) = 0 := by
          have hzero : ∀ z : Work.BoseDict.Sp, star (e l z)
              * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ) = 0 := by
            intro z
            have hnot : Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ
                ∉ Submission.BoseGases.abox n ℓ := by
              intro hmem
              have hmem' : (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ) i.1
                  ∈ Submission.BoseGases.acube ℓ := hmem i.1
              rw [Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore_apply_of_ne i.2 z ŷ] at hmem'
              exact hi hmem'
            rw [Function.notMem_support.mp (fun h => hnot (hΘsupp h)), mul_zero]
          rw [show (fun z : Work.BoseDict.Sp => star (e l z)
              * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)) = fun _ => 0
              from funext hzero]
          simp
        rw [h0]
        simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), Set.indicator_apply]
        exact mul_nonneg (le_max_right _ _) (by split_ifs <;> norm_num)

end Work.BoseBoxFock.PotCubicLowBandAux
