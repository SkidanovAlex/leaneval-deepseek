import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.Core
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripFacts
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.sinpow_mixed_Jeps_le_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sinpow_mixed_Jeps_le_strip` — sub-leaf (A) of the θ-uniformity of `J_ε`

The pointwise bound (with the `sin^{γ-1}` gain kept) of the routed slot of the log-coordinate
mollifier against the **strip** energy of the truncations `stripLo`/`stripHi`:

  `sin(2θ)^{1-γ} · (D_z^b D_θ^a (J_ε g) z θ)² ≤ C · EpsSq α (stripLo (thShift θ (-ε)) g)`

(and the symmetric statement at the `π/2`-end).  The whole analytic content is in
`ThetaFromEpsLeafA/Core.core_bound`: the routed identity, the (unweighted) Cauchy–Schwarz, the
log-coordinate substitution `subst_kernel_iter`, and the pointwise density comparison on the
kernel window.  Here the two truncations are only *instantiated*:

* `EpsMem_strip` gives the honesty of the truncated profiles;
* `stripLo_stripHi_eq_of_logrel` says that on the window (`|p₂| ≤ ε` and
  `p₂ = log tan θ − log tan θ'`) each truncation agrees with `g`.
-/

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

theorem sinpow_mixed_Jeps_le_strip {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn,
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.FTS.StrongEps.EpsMem α g →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
          ≤ C * Work.FTS.StrongEps.EpsSq α
              (Work.FTS.EpsEngine.ThetaFromEps.stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g) ∧
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
          ≤ C * Work.FTS.StrongEps.EpsSq α
              (Work.FTS.EpsEngine.ThetaFromEps.stripHi
                (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g) := by
  obtain ⟨C, hC0, hcore⟩ := core_bound (ρ := ρ) hρ hα hε hε1 a b
  refine ⟨C, hC0, ?_⟩
  intro g hsm hg z θ hz hθ0 hθπ
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθπ⟩
  have hLo : Work.FTS.StrongEps.EpsMem α
      (Work.FTS.EpsEngine.ThetaFromEps.stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g) :=
    (EpsMem_strip hg (Work.FTS.StrongEps.thShift θ (-ε))).1
  have hHi : Work.FTS.StrongEps.EpsMem α
      (Work.FTS.EpsEngine.ThetaFromEps.stripHi
        (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g) :=
    (EpsMem_strip hg (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε)).2
  constructor
  · exact hcore g hsm z θ hz hθI _ hLo
      (fun z' θ' p₂ _ hθ' hp₂ hrel =>
        (stripLo_stripHi_eq_of_logrel hθI hε hθ' hp₂ hrel).1)
  · exact hcore g hsm z θ hz hθI _ hHi
      (fun z' θ' p₂ _ hθ' hp₂ hrel =>
        (stripLo_stripHi_eq_of_logrel hθI hε hθ' hp₂ hrel).2)

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci.tendsto_setIntegral_Ici =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci

set_option autoImplicit false

theorem tendsto_setIntegral_Ici {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Filter.Tendsto (fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (if Real.pi / 2 - φ ≤ p.2 then F p else 0)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hs : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  set F' : ℝ × ℝ → ℝ := (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator F with hF'
  have hF'int : MeasureTheory.Integrable F' MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff hs).mpr hF
  have hane : ∀ᵐ p : ℝ × ℝ ∂MeasureTheory.volume, p.2 ≠ Real.pi / 2 :=
    Work.FTS.EpsEngine.ThetaFromEpsLeafB.ae_snd_ne (Real.pi / 2)
  have key : Filter.Tendsto (fun φ : ℝ => ∫ p, (if Real.pi / 2 - φ ≤ p.2 then F' p else 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p : ℝ × ℝ, (0 : ℝ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ)) (F := fun φ p => if Real.pi / 2 - φ ≤ p.2 then F' p else 0)
      (f := fun _ : ℝ × ℝ => (0 : ℝ)) (fun p : ℝ × ℝ => ‖F' p‖) ?_ ?_ hF'int.norm ?_
    · filter_upwards with φ
      have hset : MeasurableSet {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} :=
        measurableSet_le (measurable_const : Measurable (fun _ : ℝ × ℝ => Real.pi / 2 - φ))
          measurable_snd
      refine ((hF'int.aestronglyMeasurable).indicator hset).congr ?_
      filter_upwards with p
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    · filter_upwards with φ
      filter_upwards with p
      by_cases hp : Real.pi / 2 - φ ≤ p.2 <;> simp [hp]
    · refine hane.mono fun p hp => ?_
      by_cases hlt : p.2 < Real.pi / 2
      · have hpos : 0 < Real.pi / 2 - p.2 := by linarith
        have hmem : Set.Iio (Real.pi / 2 - p.2) ∈ 𝓝[>] (0 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hpos)
        have hcong : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun φ : ℝ => if Real.pi / 2 - φ ≤ p.2 then F' p else 0) := by
          filter_upwards [hmem] with φ hφ
          have hφ' : φ < Real.pi / 2 - p.2 := Set.mem_Iio.mp hφ
          have hle : ¬ (Real.pi / 2 - φ ≤ p.2) := by linarith
          simp [hle]
        exact Filter.Tendsto.congr' hcong tendsto_const_nhds
      · have hgt : Real.pi / 2 < p.2 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hp)
        have hnotmem : p ∉ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
          intro hp'
          have h2 : p.2 ∈ Work.Spaces.Iθ := hp'.2
          rw [Work.Spaces.Iθ] at h2
          linarith [h2.2]
        have hzero : F' p = 0 := by rw [hF', Set.indicator_of_notMem hnotmem]
        have hcong : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun φ : ℝ => if Real.pi / 2 - φ ≤ p.2 then F' p else 0) := by
          filter_upwards with φ
          simp [hzero]
        exact Filter.Tendsto.congr' hcong tendsto_const_nhds
  have key' : Filter.Tendsto (fun φ : ℝ => ∫ p, (if Real.pi / 2 - φ ≤ p.2 then F' p else 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using key
  have hrel : (fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        (if Real.pi / 2 - φ ≤ p.2 then F p else 0))
      = fun φ : ℝ => ∫ p, (if Real.pi / 2 - φ ≤ p.2 then F' p else 0) := by
    funext φ
    rw [← MeasureTheory.integral_indicator hs]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have key2 : ∀ q : ℝ × ℝ, (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (fun p => if Real.pi / 2 - φ ≤ p.2 then F p else 0) q
      = (if Real.pi / 2 - φ ≤ q.2 then F' q else 0) := by
      intro q
      by_cases hq : q ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      · rw [Set.indicator_of_mem hq, hF', Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, hF', Set.indicator_of_notMem hq]
        simp
    exact key2 p
  rw [hrel]
  exact key'

end Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripPlumb =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafB

set_option autoImplicit false

/-- The pointwise unfolding of the truncated weighted integrand: multiplying an `ite` whose
"else" branch is `0` by anything and squaring gives the corresponding truncation. -/
private theorem ite_zero_mul_sq (c : Prop) [Decidable c] (a b : ℝ) :
    ((if c then a else (0 : ℝ)) * b) ^ 2 = if c then (a * b) ^ 2 else 0 := by
  by_cases h : c <;> simp [h]

/-- **The lower strip energy is the integral of the truncated weighted integrand.** -/
theorem EpsSq_stripLo_eq (α φ : ℝ) (g : Work.FTS.Galerkin.Fn)
    (hg : Work.FTS.StrongEps.EpsMem α g) :
    Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g)
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          (if p.2 ≤ φ then (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 else 0) := by
  have hs : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hA : MeasurableSet {p : ℝ × ℝ | p.2 ≤ φ} :=
    measurableSet_le measurable_snd (measurable_const : Measurable (fun _ : ℝ × ℝ => φ))
  have hpt : ∀ p : ℝ × ℝ,
      (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
      = ({p : ℝ × ℝ | p.2 ≤ φ}).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) p := by
    intro p
    have hstrip : Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g p.1 p.2
        = if p.2 ≤ φ then g p.1 p.2 else 0 := rfl
    rw [hstrip, ite_zero_mul_sq]
    by_cases hp : p.2 ≤ φ
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_pos hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_neg hp]
  have hIntA : MeasureTheory.IntegrableOn
      (({p : ℝ × ℝ | p.2 ≤ φ}).indicator
        (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (MeasureTheory.integrable_indicator_iff hs).mp ?_
    have h1 : MeasureTheory.Integrable
        (({p : ℝ × ℝ | p.2 ≤ φ} ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)) :=
      (MeasureTheory.integrable_indicator_iff (hA.inter hs)).mpr
        (hg.mono_set Set.inter_subset_right)
    have hEq : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (({p : ℝ × ℝ | p.2 ≤ φ}).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
        = ({p : ℝ × ℝ | p.2 ≤ φ} ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) := by
      funext p
      by_cases hp : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      · rw [Set.indicator_of_mem hp]
        by_cases hq : p ∈ {p : ℝ × ℝ | p.2 ≤ φ}
        · rw [Set.indicator_of_mem hq,
            Set.indicator_of_mem (s := {p : ℝ × ℝ | p.2 ≤ φ} ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
              (Set.mem_inter hq hp)]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq h.1)]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp h.2)]
    rwa [hEq]
  have hFint' : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [funext hpt]
    exact hIntA
  rw [EpsSq_eq_setIntegral hFint']
  rw [funext hpt]
  refine MeasureTheory.setIntegral_congr_fun hs (fun p _ => ?_)
  by_cases hp : p.2 ≤ φ
  · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_pos hp]
  · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 ≤ φ} from hp), if_neg hp]

/-- **The upper strip energy is the integral of the truncated weighted integrand.** -/
theorem EpsSq_stripHi_eq (α φ : ℝ) (g : Work.FTS.Galerkin.Fn)
    (hg : Work.FTS.StrongEps.EpsMem α g) :
    Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g)
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          (if Real.pi / 2 - φ ≤ p.2 then
            (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 else 0) := by
  have hs : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hA : MeasurableSet {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} :=
    measurableSet_le (measurable_const : Measurable (fun _ : ℝ × ℝ => Real.pi / 2 - φ))
      measurable_snd
  have hpt : ∀ p : ℝ × ℝ,
      (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
      = ({p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2}).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) p := by
    intro p
    have hstrip : Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g p.1 p.2
        = if Real.pi / 2 - φ ≤ p.2 then g p.1 p.2 else 0 := rfl
    rw [hstrip, ite_zero_mul_sq]
    by_cases hp : Real.pi / 2 - φ ≤ p.2
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp),
        if_pos hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp),
        if_neg hp]
  have hIntA : MeasureTheory.IntegrableOn
      (({p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2}).indicator
        (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (MeasureTheory.integrable_indicator_iff hs).mp ?_
    have h1 : MeasureTheory.Integrable
        (({p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)) :=
      (MeasureTheory.integrable_indicator_iff (hA.inter hs)).mpr
        (hg.mono_set Set.inter_subset_right)
    have hEq : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (({p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2}).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
        = ({p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)).indicator
          (fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) := by
      funext p
      by_cases hp : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      · rw [Set.indicator_of_mem hp]
        by_cases hq : p ∈ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2}
        · rw [Set.indicator_of_mem hq,
            Set.indicator_of_mem (s := {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2}
              ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) (Set.mem_inter hq hp)]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq h.1)]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp h.2)]
    rwa [hEq]
  have hFint' : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [funext hpt]
    exact hIntA
  rw [EpsSq_eq_setIntegral hFint']
  rw [funext hpt]
  refine MeasureTheory.setIntegral_congr_fun hs (fun p _ => ?_)
  by_cases hp : Real.pi / 2 - φ ≤ p.2
  · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp), if_pos hp]
  · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | Real.pi / 2 - φ ≤ p.2} from hp),
      if_neg hp]

end Work.FTS.EpsEngine.ThetaFromEpsLeafB
end
end
