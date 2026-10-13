/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ThetaFromEpsLeafB/StripPlumb.lean` — the two strip energies as plain integrals

The two truncations of a profile `g` to an angular strip,

    stripLo φ g = (z,θ) ↦ if θ ≤ φ then g z θ else 0 ,
    stripHi φ g = (z,θ) ↦ if π/2 - φ ≤ θ then g z θ else 0 ,

have energies whose integrands are the corresponding truncations of the *weighted* integrand
`(g · epsW α)²`.  Since the truncated integrand is dominated by the untruncated one — and the
latter is integrable on the quarter plane by `EpsMem α g` — Fubini
(`EpsSq_eq_setIntegral`) applies and the junk value `0` is avoided:

    EpsSq α (stripLo φ g) = ∫_{Iz ×ˢ Iθ} 1_{θ ≤ φ} · (g · epsW α)² ,
    EpsSq α (stripHi φ g) = ∫_{Iz ×ˢ Iθ} 1_{π/2 - φ ≤ θ} · (g · epsW α)² .

Combined with `tendsto_setIntegral_Iic` / `tendsto_setIntegral_Ici` these give the vanishing of
the strip energies as `φ → 0⁺`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripFacts

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
