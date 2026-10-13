/-
Copyright: work module for the Elgindi finite-time singularity project.

# Fatou's lemma for the `ℋ⁰`-functional

The level-`0` estimate is applied to the *difference quotient* data `(dq c F', dq c Ψ')`, which
is in the class for every `c > 1` but whose `c → 1⁺` limit — the radially differentiated data —
is *not* known to be.  The passage to the limit is Fatou's lemma, in the following form: if
`u n → v` pointwise a.e. on the quadrant, all the `u n` are honestly in `ℋ⁰`, and the values
`HkSq α 0 (u n)` are eventually bounded by a constant `y`, then `HkSq α 0 v ≤ y`.

The proof is the standard Fatou argument for the product measure `μz.prod μθ`, together with the
two-sided bridges between the iterated Bochner integral `HkSq α 0` and the `ℝ≥0∞`-lintegral of
the (nonnegative) integrand, which are available because of the `HkMem` hypotheses.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The level-`0` `ℋ`-integrand is the single squared weighted slot. -/
theorem HkIntegrand_zero_apply (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- The product measure of the quadrant `Iz ×ˢ Iθ`. -/
abbrev quadMeasure : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- **A.e. strong measurability of the level-`0` integrand of a function continuous on `Q0`.**
The integrand is continuous on the open quadrant, which differs from the closed quadrant
`Iz ×ˢ Iθ` by the null set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`. -/
theorem aemeasurable_ofReal_HkIntegrand_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) Q0) :
    AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f p.1 p.2))
      quadMeasure := by
  have hQ0 : MeasurableSet Q0 := isOpen_Q0.measurableSet
  have hsub : Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    rintro ⟨z, θ⟩ ⟨hz, hθ0, hθ1⟩
    refine ⟨?_, ?_, ?_⟩
    · show (0 : ℝ) ≤ z
      exact le_of_lt hz
    · show (0 : ℝ) ≤ θ
      exact le_of_lt hθ0
    · show θ ≤ Real.pi / 2
      exact le_of_lt hθ1
  have hnull1 : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      (Q0 \ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) = 0 := by
    rw [Set.sdiff_eq_empty.mpr hsub, MeasureTheory.measure_empty]
  have hnull2 : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) \ Q0) = 0 := by
    have hsub2 : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) \ Q0
        ⊆ (({0} : Set ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0} : Set ℝ))
          ∪ (Set.univ ×ˢ ({Real.pi / 2} : Set ℝ)) := by
      rintro ⟨z, θ⟩ ⟨⟨hzI, hθI⟩, hQ⟩
      rw [Work.Spaces.Iz, Set.mem_Ici] at hzI
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
      by_cases hz0 : z = 0
      · exact Or.inl (Or.inl ⟨hz0, Set.mem_univ _⟩)
      · have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
        have hnp : ¬ (0 < θ ∧ θ < Real.pi / 2) := fun hcon =>
          hQ (mem_Q0.mpr ⟨hzpos, hcon.1, hcon.2⟩)
        by_cases hθ0 : θ = 0
        · exact Or.inl (Or.inr ⟨Set.mem_univ _, hθ0⟩)
        · refine Or.inr ⟨Set.mem_univ _, ?_⟩
          have hθpos : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm hθ0)
          have hge : ¬ (θ < Real.pi / 2) := fun hlt => hnp ⟨hθpos, hlt⟩
          exact le_antisymm hθI.2 (not_lt.mp hge)
    refine MeasureTheory.measure_mono_null hsub2 ?_
    rw [MeasureTheory.measure_union_null_iff, MeasureTheory.measure_union_null_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [MeasureTheory.Measure.prod_prod]; simp
    · rw [MeasureTheory.Measure.prod_prod]; simp
    · rw [MeasureTheory.Measure.prod_prod]; simp
  have hrc : quadMeasure
      = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict Q0 := by
    show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.ae_eq_set.mpr ⟨hnull2, hnull1⟩)
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict Q0) :=
    hf.aestronglyMeasurable hQ0
  rw [hrc]
  exact ENNReal.measurable_ofReal.comp_aemeasurable haesm.aemeasurable

/-- **The bridge**: for a function in `ℋ⁰`, the `ofReal` of its iterated `ℋ⁰`-integral is the
product-measure lintegral of the `ofReal` of its integrand. -/
theorem ofReal_HkSq_zero {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 g)
    (hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2)) quadMeasure) :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂quadMeasure := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ) := fun z hz =>
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  have houter := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.2)
    (Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  show ENNReal.ofReal (Work.Spaces.HkSq α 0 g) = _
  rw [Work.Spaces.HkSq]
  rw [show quadMeasure
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl,
    MeasureTheory.lintegral_prod _ hmeas]
  rw [houter]
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
  exact hinner z hz

/-- **Fatou for the `ℋ⁰`-functional.**  If `u n` converges pointwise a.e. to `v`, each `u n` is in
`ℋ⁰` (honestly), `v` is in `ℋ⁰`, the integrands are a.e. measurable, and the `ℋ⁰`-norms of the
`u n` are eventually bounded by `y`, then the `ℋ⁰`-norm of `v` is at most `y`. -/
theorem HkSq_zero_le_of_eventually_le {α : ℝ} {u : ℕ → ℝ → ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    (hmeasn : ∀ n : ℕ, AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2)) quadMeasure)
    (hmeasv : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2)) quadMeasure)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 0 (u n))
    (hmemv : Work.Spaces.HkMem α 0 v)
    (hae : ∀ᵐ p ∂quadMeasure,
      Filter.Tendsto (fun n : ℕ => u n p.1 p.2) Filter.atTop (nhds (v p.1 p.2)))
    {y : ℝ} (hy : ∀ᶠ n : ℕ in Filter.atTop, Work.Spaces.HkSq α 0 (u n) ≤ y) :
    Work.Spaces.HkSq α 0 v ≤ y := by
  -- the pointwise convergence of the integrands
  have hpoint : ∀ᵐ p ∂quadMeasure,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2)
        = Filter.liminf
            (fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2))
            Filter.atTop := by
    filter_upwards [hae] with p hp
    rw [HkIntegrand_zero_apply α v p.1 p.2,
      show (fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2))
        = fun n : ℕ => ENNReal.ofReal
            ((u n p.1 p.2 * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2)
        from funext fun n => by rw [HkIntegrand_zero_apply]]
    have hstep : Filter.Tendsto
        (fun n : ℕ => u n p.1 p.2
          * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2)))
        Filter.atTop (nhds (v p.1 p.2
          * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2)))) :=
      hp.mul tendsto_const_nhds
    have hsq := hstep.pow 2
    have hoF : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal
          ((u n p.1 p.2 * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2))
        Filter.atTop (nhds (ENNReal.ofReal
          ((v p.1 p.2 * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2))) :=
      (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hsq
    exact hoF.liminf_eq.symm
  -- Fatou
  have hfatou : ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2) ∂quadMeasure
      ≤ Filter.liminf (fun n : ℕ =>
          ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure)
          Filter.atTop := by
    calc ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2) ∂quadMeasure
        = ∫⁻ p, Filter.liminf (fun n : ℕ =>
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2)) Filter.atTop
            ∂quadMeasure := MeasureTheory.lintegral_congr_ae hpoint
      _ ≤ Filter.liminf (fun n : ℕ =>
            ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure)
            Filter.atTop := MeasureTheory.lintegral_liminf_le' hmeasn
  -- the bridges
  have hbridge : ∀ n : ℕ,
      ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure
        = ENNReal.ofReal (Work.Spaces.HkSq α 0 (u n)) :=
    fun n => (ofReal_HkSq_zero (hmem n) (hmeasn n)).symm
  -- assemble
  have hle : ENNReal.ofReal (Work.Spaces.HkSq α 0 v) ≤ ENNReal.ofReal y := by
    rw [ofReal_HkSq_zero hmemv hmeasv]
    refine hfatou.trans ?_
    rw [show (fun n : ℕ =>
        ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure)
        = fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkSq α 0 (u n)) from funext hbridge]
    refine Filter.liminf_le_of_le ⟨0, ?_⟩ ?_
    · filter_upwards with n
      exact bot_le
    · intro b hb
      have hy' : ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (Work.Spaces.HkSq α 0 (u n)) ≤ ENNReal.ofReal y :=
        hy.mono fun n hn => ENNReal.ofReal_le_ofReal hn
      obtain ⟨n, hn⟩ := (hb.and hy').exists
      exact hn.1.trans hn.2
  by_cases hy0 : 0 ≤ y
  · exact (ENNReal.ofReal_le_ofReal_iff hy0).mp hle
  · exfalso
    obtain ⟨n, hn⟩ := hy.exists
    have := Work.Spaces.HkSq_nonneg α 0 (u n)
    linarith

end Work.FTS.EllipticEst.Cores.Dil
