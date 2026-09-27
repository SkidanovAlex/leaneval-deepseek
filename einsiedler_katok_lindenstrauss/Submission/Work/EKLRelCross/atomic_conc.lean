import Mathlib
import Submission.Work.EKLRelCross.atomic_defs
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `Work.EKLRelCross.atomic_conc` — concentration of `ν x` under `relPsi t0 n`

For a Radon measure `m` on `SL₃(ℝ)` carried by a horospherical subgroup `U` contracted by
`aDiag t₀`, and a compactly supported continuous `f`,

`∫ g, f (relPsi t₀ n g) ∂m → f 1 · m {1}`.

Because `relPsi t₀ n` is conjugation by the inverse power `aDiag(t₀)⁻ⁿ` it *expands* `U`, so for
`g ∈ U`, `g ≠ 1` the points `relPsi t₀ n g` leave every compact set and `f (relPsi t₀ n g) = 0`
for large `n`, while `relPsi t₀ n 1 = 1`.  Dominated convergence (with the dominating function
`B · 1_{|entries| ≤ 1+R}` coming from the compact support of `f`) gives the limit.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- A compactly supported continuous real function on `SL₃(ℝ)` is bounded in absolute value. -/
lemma exists_bound_cc (f : CompactlySupportedContinuousMap SL3 ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g, |f g| ≤ B := by
  obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuousOn f.continuous.continuousOn
  refine ⟨max C 0, le_max_right C 0, fun g => ?_⟩
  by_cases hg : g ∈ tsupport (f : SL3 → ℝ)
  · have h1 : ‖f g‖ ≤ C := hC g hg
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left C 0)
  · have h0 : f g = 0 := by
      by_contra h
      exact hg (subset_tsupport (f : SL3 → ℝ) (by simpa [Function.mem_support] using h))
    rw [h0, abs_zero]
    exact le_max_right C 0

/-- The support of a compactly supported continuous function is contained in some entry ball. -/
lemma supp_subset_V (f : CompactlySupportedContinuousMap SL3 ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ g, f g ≠ 0 → g ∈ V R := by
  have hcont : Continuous (fun g : SL3 => ∑ p : Fin 3 × Fin 3,
      |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) := by fun_prop
  obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0 + 2, by linarith [le_max_right C 0], fun g hg => ?_⟩
  intro i j
  have hgt : g ∈ tsupport (f : SL3 → ℝ) :=
    subset_tsupport _ (by simpa [Function.mem_support] using hg)
  have hle : ∑ p : Fin 3 × Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| ≤ C := by
    have h1 := hC g hgt
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun p _ => abs_nonneg _))] at h1
  have hsingle : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ ∑ p : Fin 3 × Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| :=
    Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 => |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
  have hij : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ max C 0 :=
    le_trans (le_trans hsingle hle) (le_max_left C 0)
  calc |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
        abs_sub _ _
    _ ≤ max C 0 + 1 := by
        gcongr
        rcases eq_or_ne i j with rfl | hne
        · rw [Matrix.one_apply_eq, abs_one]
        · rw [Matrix.one_apply_ne hne, abs_zero]; norm_num
    _ < max C 0 + 2 := by linarith

/-- If `g ∈ U` and `relPsi t0 n g` lies in the displacement ball `V R`, then all entries of `g`
are bounded by `1 + R`. -/
lemma mem_entryBox_of_relPsi_mem_V {U : Subgroup SL3} {t0 : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (nhds 1))
    {R : ℝ} {n : ℕ} {g : SL3} (hgU : g ∈ U) (hmem : relPsi t0 n g ∈ V R) (i j : Fin 3) :
    |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + R := by
  have h1 : |(relPsi t0 n g : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < R := hmem i j
  rw [relPsi_apply] at h1
  rcases eq_or_ne i j with rfl | hne
  · have h2 : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by simp
    have hgii : (g : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by
      have h := Work.EKLC6Core.box_facts_entry_eq_one hcontr hgU (le_refl (t0 i))
      rw [h, h2]
    rw [hgii, Matrix.one_apply_eq] at h1
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul, abs_zero] at h1
    rw [hgii, abs_one]
    linarith
  · rw [Matrix.one_apply_ne hne] at h1
    have hfac : Real.exp ((n:ℝ) * (t0 j - t0 i)) * |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| < R := by
      rw [sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)] at h1
      exact h1
    by_cases hlt : t0 i < t0 j
    · have hexp : 1 ≤ Real.exp ((n:ℝ) * (t0 j - t0 i)) := by
        rw [Real.one_le_exp_iff]; positivity
      have hgg : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| < R :=
        lt_of_le_of_lt (le_mul_of_one_le_left (abs_nonneg _) hexp) hfac
      linarith
    · have hzero : (g : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
        have h := Work.EKLC6Core.box_facts_entry_eq_one hcontr hgU (not_lt.mp hlt)
        have h2 : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hne
        rw [h, h2]
      rw [hzero, abs_zero] at hfac
      simp only [mul_zero] at hfac
      rw [hzero, abs_zero]
      linarith

/-- For `g ∈ U`, `g ≠ 1`, the conjugates `relPsi t0 n g` leave the ball `V R`. -/
lemma eventually_relPsi_notMem_V {U : Subgroup SL3} {t0 : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (nhds 1))
    {R : ℝ} {g : SL3} (hgU : g ∈ U) (hg1 : g ≠ 1) :
    ∀ᶠ n : ℕ in atTop, relPsi t0 n g ∉ V R := by
  have hne : (g : Matrix (Fin 3) (Fin 3) ℝ) ≠ ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) :=
    fun h => hg1 (Subtype.ext h)
  obtain ⟨i, j, hij⟩ : ∃ i j, (g : Matrix (Fin 3) (Fin 3) ℝ) i j
      ≠ ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    by_contra h
    push_neg at h
    exact hne (funext (fun i => funext (fun j => h i j)))
  have hij' : i ≠ j := fun h => by
    subst h
    exact hij (Work.EKLC6Core.box_facts_entry_eq_one hcontr hgU (le_refl (t0 i)))
  have hgij : (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≠ 0 := by
    have h1 : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij'
    rwa [h1] at hij
  have hlt : t0 i < t0 j := by
    by_contra h
    push_neg at h
    exact hgij (by
      have h1 := Work.EKLC6Core.box_facts_entry_eq_one hcontr hgU h
      have h2 : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij'
      rw [h1, h2])
  have htend : Tendsto (fun n : ℕ =>
      Real.exp ((n:ℝ) * (t0 j - t0 i)) * |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|) atTop atTop :=
    (Work.EKLC6Core.boxi_tendsto_exp_nat_mul_atTop (by linarith)).atTop_mul_const
      (abs_pos.mpr hgij)
  filter_upwards [htend.eventually_ge_atTop R] with n hn
  intro hmem
  have h2 : Real.exp ((n:ℝ) * (t0 j - t0 i)) * |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| < R := by
    have h3 := hmem i j
    rw [relPsi_apply] at h3
    rw [Matrix.one_apply_ne hij'] at h3
    rw [sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)] at h3
    exact h3
  linarith

/-- The closed entrywise box of radius `1 + R` is compact. -/
lemma isCompact_entryBox_aux (R : ℝ) :
    IsCompact {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + R} := by
  rw [show {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + R}
      = {g : SL3 | ∀ i j, -(1 + R) ≤ (g : Matrix (Fin 3) (Fin 3) ℝ) i j
          ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ 1 + R} from by
    ext g
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h i j; exact abs_le.mp (h i j)
    · intro h i j; exact abs_le.mpr (h i j)]
  exact Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(1 + R)) (fun _ _ => 1 + R)

/-- **Concentration.**  Pushing forward a measure carried by the contracted subgroup `U` along
the expanding conjugations `relPsi t0 n` concentrates it at the identity. -/
theorem integral_relPsi_tendsto' {U : Subgroup SL3} (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (nhds 1))
    {m : Measure SL3} (hcar : m (U : Set SL3)ᶜ = 0) (hfin : IsFiniteMeasureOnCompacts m)
    (f : CompactlySupportedContinuousMap SL3 ℝ) :
    Tendsto (fun n : ℕ => ∫ g, f (relPsi t0 n g) ∂m) atTop (nhds (f 1 * (m {1}).toReal)) := by
  have hUmeas : MeasurableSet (U : Set SL3) := hU.1.measurableSet
  obtain ⟨B, hB0, hB⟩ := exists_bound_cc f
  obtain ⟨R, hR0, hR⟩ := supp_subset_V f
  set K : Set SL3 := {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + R} with hK
  have hKc : IsCompact K := isCompact_entryBox_aux R
  have hKm : MeasurableSet K := hKc.measurableSet
  have hcar' : ∀ᵐ g ∂m, g ∈ (U : Set SL3) := by
    rw [MeasureTheory.ae_iff, show {g : SL3 | ¬ g ∈ (U : Set SL3)} = (U : Set SL3)ᶜ from by
      ext g; simp]
    exact hcar
  have hres : m.restrict (U : Set SL3) = m := Measure.restrict_eq_self_of_ae_mem hcar'
  have hbdd_int : Integrable (fun g => K.indicator (fun _ => B) g) (m.restrict (U : Set SL3)) := by
    rw [integrable_indicator_iff hKm]
    refine MeasureTheory.integrableOn_const ?_
    rw [Measure.restrict_apply hKm]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (hfin.lt_top_of_isCompact hKc))
  have h_bound : ∀ n : ℕ, ∀ᵐ g ∂(m.restrict (U : Set SL3)),
      ‖f (relPsi t0 n g)‖ ≤ K.indicator (fun _ => B) g := by
    intro n
    filter_upwards [MeasureTheory.ae_restrict_mem hUmeas] with g hgU
    by_cases hgK : g ∈ K
    · rw [Real.norm_eq_abs, Set.indicator_of_mem hgK]
      exact hB (relPsi t0 n g)
    · have hnVR : relPsi t0 n g ∉ V R := fun hmem =>
        hgK (by
          rw [hK]
          intro i j
          exact mem_entryBox_of_relPsi_mem_V hcontr hgU hmem i j)
      have hzero : f (relPsi t0 n g) = 0 := by
        by_contra hne
        exact hnVR (hR _ hne)
      rw [hzero, norm_zero, Set.indicator_of_notMem hgK]
  have h_lim : ∀ᵐ g ∂(m.restrict (U : Set SL3)),
      Tendsto (fun n : ℕ => f (relPsi t0 n g)) atTop
        (nhds ((({1} : Set SL3).indicator (fun _ => f 1)) g)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hUmeas] with g hgU
    by_cases hg1 : g = 1
    · subst hg1
      have hconst : (fun n : ℕ => f (relPsi t0 n (1 : SL3))) = fun _ => f 1 := by
        funext n
        rw [show relPsi t0 n (1 : SL3) = 1 from by simp [relPsi]]
      rw [hconst, Set.indicator_of_mem (Set.mem_singleton (1 : SL3))]
      exact tendsto_const_nhds
    · rw [Set.indicator_of_notMem (by simpa using hg1)]
      have hev : ∀ᶠ n in atTop, f (relPsi t0 n g) = 0 := by
        filter_upwards [eventually_relPsi_notMem_V hcontr hgU hg1] with n hn
        by_contra hne
        exact hn (hR _ hne)
      exact tendsto_const_nhds.congr' (hev.mono (fun n hn => hn.symm))
  have hdc := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := m.restrict (U : Set SL3))
    (F := fun n g => f (relPsi t0 n g))
    (f := fun g => ({1} : Set SL3).indicator (fun _ => f 1) g)
    (fun g => K.indicator (fun _ => B) g)
    (fun n => (f.continuous.comp (continuous_relPsi t0 n)).aestronglyMeasurable)
    hbdd_int h_bound h_lim
  have hIntLim : ∫ g, ({1} : Set SL3).indicator (fun _ => f 1) g ∂(m.restrict (U : Set SL3))
      = f 1 * (m {1}).toReal := by
    rw [MeasureTheory.integral_indicator (measurableSet_singleton (1 : SL3)),
      MeasureTheory.setIntegral_const]
    have h1 : (m.restrict (U : Set SL3)) {1} = m {1} := by
      rw [Measure.restrict_apply (measurableSet_singleton (1 : SL3)),
        Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (U.one_mem))]
    rw [Measure.real_def, h1, smul_eq_mul, mul_comm]
  rw [hIntLim] at hdc
  rwa [hres] at hdc


end Work.EKLRelCross

end
