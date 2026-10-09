import Mathlib
import Submission.Work.SSGRoute.PTW.logSectionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local content section at an infinite place

For an infinite place `w` of a number field we construct a continuous family of local units
`t c` in the identity component of `(K_wˣ)` whose normalized absolute value is `c` for every
positive unit `c`, and which is multiplicative on positive units.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.PTW

open NK.GlobalCFT

/-- **Local content section at an infinite place.** -/
theorem localContentSection (K : Type*) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) :
    ∃ t : ℝˣ → (w.Completion)ˣ,
      Continuous t ∧ t 1 = 1 ∧
      (∀ c : ℝˣ, t c ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ)) ∧
      (∀ c : ℝˣ, 0 < (c : ℝ) →
        NK.GlobalCFT.Idele.localAbs K (NK.GlobalCFT.Place.ofInfinite w) (t c) = c) ∧
      (∀ c c' : ℝˣ, 0 < (c : ℝ) → 0 < (c' : ℝ) → t (c * c') = t c * t c') := by
  classical
  haveI hpc : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioi
  rcases w.isReal_or_isComplex with hw | hw
  · -- ## real place
    set φ : w.Completion ≃+* ℝ :=
      NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw with hφ
    have hcont : Continuous fun y : ℝ => φ.symm y := by
      rw [Metric.continuous_iff]
      intro y ε hε
      refine ⟨ε, hε, fun y' hy => ?_⟩
      have hd : dist (φ.symm y') (φ.symm y) = dist y' y :=
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.dist_eq y' y
      rwa [hd]
    have hnorm : ∀ x : w.Completion, ‖x‖ = |φ x| := by
      intro x
      have h1 : ‖φ x‖ = ‖x‖ :=
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
          |>.norm_map_of_map_zero (map_zero _) x
      rw [Real.norm_eq_abs] at h1
      exact h1.symm
    have hne : ∀ c : ℝˣ, φ.symm |(c : ℝ)| ≠ 0 := by
      intro c h0
      have h1 : |(c : ℝ)| = 0 := by
        have h2 := congrArg φ h0
        simpa using h2
      exact Units.ne_zero c (abs_eq_zero.mp h1)
    have hne' : ∀ y : ℝ, 0 < y → φ.symm y ≠ 0 := by
      intro y hy h0
      have h1 : y = 0 := by
        have h2 := congrArg φ h0
        simpa using h2
      exact absurd h1 (ne_of_gt hy)
    set F : Set.Ioi (0 : ℝ) → (w.Completion)ˣ :=
      fun y => Units.mk0 (φ.symm (y : ℝ)) (hne' _ y.2) with hF
    have hFcont : Continuous F := by
      rw [Units.isEmbedding_val₀.continuous_iff]
      show Continuous fun y : Set.Ioi (0:ℝ) => φ.symm (y : ℝ)
      exact hcont.comp continuous_subtype_val
    have hrange : IsPreconnected (Set.range F) := isPreconnected_range hFcont
    have h1mem : (1 : (w.Completion)ˣ) ∈ Set.range F :=
      ⟨⟨1, by norm_num⟩, by simp [hF]⟩
    have hsub : ∀ u ∈ Set.range F, u ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ) :=
      fun u hu => hrange.subset_connectedComponent h1mem hu
    refine ⟨fun c => Units.mk0 (φ.symm |(c : ℝ)|) (hne c), ?_, ?_, ?_, ?_, ?_⟩
    · -- continuity
      rw [Units.isEmbedding_val₀.continuous_iff]
      show Continuous fun c : ℝˣ => φ.symm |(c : ℝ)|
      exact hcont.comp (continuous_abs.comp Units.continuous_val)
    · -- `t 1 = 1`
      apply Units.ext
      simp
    · -- membership in the identity component
      intro c
      exact hsub _ ⟨⟨|(c : ℝ)|, abs_pos.mpr (Units.ne_zero c)⟩, by simp [hF]⟩
    · -- the prescribed absolute value
      intro c hc
      rw [NK.GlobalCFT.Idele.localAbs_ofInfinite, hw.mult_eq_one, pow_one]
      apply Units.ext
      rw [Units.val_mk0, Units.val_mk0]
      have hval : ‖(φ.symm |(c : ℝ)| : w.Completion)‖ = |(c : ℝ)| := by
        rw [hnorm, φ.apply_symm_apply]
        exact Real.norm_of_nonneg (abs_nonneg _)
      rw [hval, abs_of_pos hc]
    · -- multiplicativity on positive units
      intro c c' hc hc'
      apply Units.ext
      simp only [Units.val_mul, Units.val_mk0]
      rw [← map_mul]
      congr 1
      rw [abs_mul]
  · -- ## complex place
    set φ : w.Completion ≃+* ℂ :=
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw with hφ
    have hcont : Continuous fun z : ℂ => φ.symm z := by
      rw [Metric.continuous_iff]
      intro z ε hε
      refine ⟨ε, hε, fun z' hz => ?_⟩
      have hd : dist (φ.symm z') (φ.symm z) = dist z' z :=
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.dist_eq z' z
      rwa [hd]
    have hnorm : ∀ x : w.Completion, ‖x‖ = ‖φ x‖ := by
      intro x
      have h1 : ‖φ x‖ = ‖x‖ :=
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w)
          |>.norm_map_of_map_zero (map_zero _) x
      exact h1.symm
    have hne : ∀ c : ℝˣ, φ.symm ((Real.sqrt |(c : ℝ)| : ℝ) : ℂ) ≠ 0 := by
      intro c h0
      have h1 : ((Real.sqrt |(c : ℝ)| : ℝ) : ℂ) = 0 := by
        have h2 := congrArg φ h0
        simpa using h2
      have h2 : Real.sqrt |(c : ℝ)| = 0 := by simpa using h1
      have h4 : (Real.sqrt |(c : ℝ)|) ^ 2 = |(c : ℝ)| := Real.sq_sqrt (abs_nonneg (c : ℝ))
      rw [h2] at h4
      exact Units.ne_zero c (abs_eq_zero.mp (by simpa using h4.symm))
    have hne' : ∀ y : ℝ, 0 < y → φ.symm ((y : ℝ) : ℂ) ≠ 0 := by
      intro y hy h0
      have h1 : ((y : ℝ) : ℂ) = 0 := by
        have h2 := congrArg φ h0
        simpa using h2
      have h2 : y = 0 := by simpa using h1
      exact absurd h2 (ne_of_gt hy)
    set F : Set.Ioi (0 : ℝ) → (w.Completion)ˣ :=
      fun y => Units.mk0 (φ.symm ((y : ℝ) : ℂ)) (hne' _ y.2) with hF
    have hFcont : Continuous F := by
      rw [Units.isEmbedding_val₀.continuous_iff]
      show Continuous fun y : Set.Ioi (0:ℝ) => φ.symm ((y : ℝ) : ℂ)
      exact hcont.comp (Complex.continuous_ofReal.comp continuous_subtype_val)
    have hrange : IsPreconnected (Set.range F) := isPreconnected_range hFcont
    have h1mem : (1 : (w.Completion)ˣ) ∈ Set.range F :=
      ⟨⟨1, by norm_num⟩, by simp [hF]⟩
    have hsub : ∀ u ∈ Set.range F, u ∈ Subgroup.connectedComponentOfOne ((w.Completion)ˣ) :=
      fun u hu => hrange.subset_connectedComponent h1mem hu
    refine ⟨fun c => Units.mk0 (φ.symm ((Real.sqrt |(c : ℝ)| : ℝ) : ℂ)) (hne c),
      ?_, ?_, ?_, ?_, ?_⟩
    · -- continuity
      rw [Units.isEmbedding_val₀.continuous_iff]
      show Continuous fun c : ℝˣ => φ.symm ((Real.sqrt |(c : ℝ)| : ℝ) : ℂ)
      exact hcont.comp (Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (continuous_abs.comp Units.continuous_val)))
    · -- `t 1 = 1`
      apply Units.ext
      simp
    · -- membership in the identity component
      intro c
      exact hsub _ ⟨⟨Real.sqrt |(c : ℝ)|,
        Real.sqrt_pos.mpr (abs_pos.mpr (Units.ne_zero c))⟩, by simp [hF]⟩
    · -- the prescribed absolute value
      intro c hc
      rw [NK.GlobalCFT.Idele.localAbs_ofInfinite, hw.mult_eq_two]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]
      have hval : ‖(φ.symm ((Real.sqrt |(c : ℝ)| : ℝ) : ℂ) : w.Completion)‖
          = Real.sqrt |(c : ℝ)| := by
        rw [hnorm, φ.apply_symm_apply]
        exact Complex.norm_of_nonneg (Real.sqrt_nonneg _)
      rw [hval, Real.sq_sqrt (abs_nonneg (c : ℝ)), abs_of_pos hc]
    · -- multiplicativity on positive units
      intro c c' hc hc'
      apply Units.ext
      simp only [Units.val_mul, Units.val_mk0]
      rw [← map_mul]
      congr 1
      rw [abs_mul, Real.sqrt_mul (abs_nonneg (c : ℝ)) |(c' : ℝ)|, Complex.ofReal_mul]

end Work.SSGRoute.PTW
