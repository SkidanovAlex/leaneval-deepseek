import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem hasDerivWithinAt_of_sub_eq_integral
    {τ : ℝ} (hτ : 0 < τ) {F G : ℝ → ℝ}
    (hG : ContinuousOn G (Set.Icc (0 : ℝ) τ))
    (hint : ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ t ∈ Set.Icc (0 : ℝ) τ,
      F s - F t = ∫ σ in t..s, G σ) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ, HasDerivWithinAt F (G t) (Set.Ico (0 : ℝ) τ) t := by
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) τ := ⟨ht.1, ht.2.le⟩
  -- `F` agrees on `[0, τ]` with the primitive `A = fun s ↦ ∫ σ in 0..s, G σ`, up to the constant
  -- `F 0`, by the subtraction identity applied with lower endpoint `0`.
  set A : ℝ → ℝ := fun s => ∫ σ in (0 : ℝ)..s, G σ with hAdef
  have hFA : ∀ s ∈ Set.Icc (0 : ℝ) τ, F s = F 0 + A s := by
    intro s hs
    have h := hint s hs 0 ⟨le_refl 0, hτ.le⟩
    have hA0 : A 0 = 0 := by simp [hAdef]
    linarith
  -- Fundamental theorem of calculus: the primitive of a continuous function differentiates back
  -- to the integrand, within the closed interval.
  have hA : HasDerivWithinAt A (G t) (Set.Icc (0 : ℝ) τ) t := by
    have hfact : Fact (t ∈ Set.Icc (0 : ℝ) τ) := ⟨htIcc⟩
    have hInt : IntervalIntegrable G MeasureTheory.volume (0 : ℝ) t :=
      (hG.mono (Set.Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1
    refine intervalIntegral.integral_hasDerivWithinAt_right (f := G) (a := (0 : ℝ)) (b := t)
      (s := Set.Icc (0 : ℝ) τ) (t := Set.Icc (0 : ℝ) τ) hInt ?_ ?_
    · exact hG.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
    · exact hG.continuousWithinAt htIcc
  have hmain : HasDerivWithinAt (fun s => F 0 + A s) (G t) (Set.Ico (0 : ℝ) τ) t :=
    (hA.const_add (F 0)).mono Set.Ico_subset_Icc_self
  exact hmain.congr (fun x hx => hFA x ⟨hx.1, hx.2.le⟩) (hFA t htIcc)

end Work.Diff.STE.Lead
