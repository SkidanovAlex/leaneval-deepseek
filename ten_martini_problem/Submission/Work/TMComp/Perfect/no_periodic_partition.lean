import Mathlib

namespace Work.TMComp.Perfect

open MeasureTheory Set Function
open scoped ENNReal

set_option linter.unusedVariables false

/-- Auxiliary lemma: for a measurable `1`-periodic function `F : ℝ → ℝ≥0∞`, the lower integral
over the fundamental domain `Ioc 0 1` is invariant under real translations, i.e.
`∫⁻ x in Ioc 0 1, F (x + a) = ∫⁻ x in Ioc 0 1, F x` for every `a : ℝ`. -/
private lemma lintegral_Ioc_zero_one_add (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (hperF : Function.Periodic F 1) (a : ℝ) :
    ∫⁻ x in Set.Ioc 0 1, F (x + a) = ∫⁻ x in Set.Ioc 0 1, F x := by
  -- The `ℤ ∙ 1`-action on `ℝ` preserves Lebesgue measure and acts measurably.
  have : MeasurableConstVAdd (AddSubgroup.zmultiples (1 : ℝ)) ℝ :=
    ⟨fun c => by simpa [AddSubgroup.vadd_def, vadd_eq_add] using measurable_const_add (c : ℝ)⟩
  have : VAddInvariantMeasure (AddSubgroup.zmultiples (1 : ℝ)) ℝ volume :=
    ⟨fun c s _ => by
      simpa only [AddSubgroup.vadd_def, vadd_eq_add] using
        measure_preimage_add (volume : Measure ℝ) (c : ℝ) s⟩
  -- Step 1: change of variables, translating the domain of integration.
  have hshift : ∫⁻ x in Set.Ioc 0 1, F (x + a) = ∫⁻ y in Set.Ioc a (a + 1), F y := by
    have hg := measurePreserving_add_right (volume : Measure ℝ) a
    have h := hg.setLIntegral_comp_preimage (s := Set.Ioc a (a + 1)) measurableSet_Ioc hF
    rw [Set.preimage_add_const_Ioc] at h
    simpa using h
  -- Step 2: `Ioc a (a + 1)` and `Ioc 0 1` are both fundamental domains of the `ℤ ∙ 1`-action,
  -- and the integrand is invariant under that action.
  have hfd : ∫⁻ y in Set.Ioc a (a + 1), F y = ∫⁻ y in Set.Ioc 0 1, F y := by
    have hs := isAddFundamentalDomain_Ioc (T := (1 : ℝ)) zero_lt_one 0
    have ht := isAddFundamentalDomain_Ioc (T := (1 : ℝ)) zero_lt_one a
    have h := IsAddFundamentalDomain.setLIntegral_eq hs ht F hperF.map_vadd_zmultiples
    simpa using h.symm
  rw [hshift, hfd]

/-- There is no measurable `1`-periodic nonnegative `G : ℝ → ℝ` whose translates along the progression `x ↦ x + n α` sum to `1` for every `x`. -/
theorem no_periodic_partition (G : ℝ → ℝ) (α : ℝ) (hmeas : Measurable G)
    (hnn : ∀ x : ℝ, 0 ≤ G x) (hper : ∀ x : ℝ, G (x + 1) = G x)
    (hsum : ∀ x : ℝ, ∑' n : ℤ, ENNReal.ofReal (G (x + (n : ℝ) * α)) = 1) : False := by
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (G x) with hFdef
  have hF : Measurable F := hmeas.ennreal_ofReal
  have hperF : Function.Periodic F 1 := fun x => by simp [hFdef, hper x]
  have hshift : ∀ a : ℝ, ∫⁻ x in Set.Ioc 0 1, F (x + a) = ∫⁻ x in Set.Ioc 0 1, F x :=
    fun a => lintegral_Ioc_zero_one_add F hF hperF a
  -- Tonelli: interchange the sum over `ℤ` with the integral over `Ioc 0 1`.
  have hT := lintegral_tsum (μ := volume.restrict (Set.Ioc 0 1))
    (f := fun n : ℤ => fun x : ℝ => F (x + (n : ℝ) * α))
    (fun n => (hF.comp (measurable_add_const _)).aemeasurable)
  -- The integrand is identically `1` by hypothesis, and `volume (Ioc 0 1) = 1`.
  have hleft : ∫⁻ x in Set.Ioc 0 1, (∑' n : ℤ, F (x + (n : ℝ) * α)) = 1 := by
    have : (fun x : ℝ => ∑' n : ℤ, F (x + (n : ℝ) * α)) = fun _ => (1 : ℝ≥0∞) := by
      funext x
      simp only [hFdef]
      exact hsum x
    rw [this, setLIntegral_const, one_mul, Real.volume_Ioc]
    norm_num
  -- Hence `1 = ∑' n, c` where `c = ∫⁻ x in Ioc 0 1, F x` is independent of `n`.
  have key : (1 : ℝ≥0∞) = ∑' _n : ℤ, ∫⁻ x in Set.Ioc 0 1, F x := by
    rw [← hleft, hT]
    exact tsum_congr (fun n => hshift ((n : ℝ) * α))
  -- A constant `ℤ`-indexed series equals `0` or `⊤`, never `1`.
  have hc0 : (∫⁻ x in Set.Ioc 0 1, F x) ≠ 0 := by
    intro h0
    rw [h0, tsum_zero] at key
    exact one_ne_zero key
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hc0] at key
  exact ENNReal.one_ne_top key

end Work.TMComp.Perfect
