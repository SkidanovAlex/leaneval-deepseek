import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.acubePVFacts
import Submission.Work.BoseBoxFock.sectorSelection
import Submission.Work.MB.SlotWeakDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Submission.BoseGases

/-- **The state-class repair of the BF3c selection chain, step 1.**  `Work.BoseBoxFock.box_to_model`
quantifies over `Φ : Work.BoseKinLoc.BoxState n ℓ`, a class with **no support hypothesis**; the weak
(`Submission/Work/MB/`) selection chain needs a state that is measurable, *everywhere bounded* and
supported in `Work.MB.boxPow n ℓ`.  The box restriction `Θ := (Φ : ℂ)·1_{abox n ℓ}` of this statement
is such a state: it agrees with `Φ` on the box (so every box integral `normB`, `wordB` and the
derived quantity `IsLowB` is unchanged), it is supported in the box, and — the point — it is
**globally bounded**, because `Φ` is `ContDiff ℝ ∞`, hence bounded on the *compact* box, and `Θ`
vanishes off it.  (`Φ·1_abox` is not continuous, which is why the *top-level* statements of the MB
chain, currently phrased with `Continuous`/`HasCompactSupport`, must be re-stated with
`Measurable`+bounded+box-supported hypotheses; the rest of that chain already carries exactly those
three hypotheses.) -/
theorem boxRestrictState {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    (let Θ : Submission.BoseGases.X n → ℂ := fun x =>
      ((Φ x : ℝ) : ℂ) * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x
     Measurable Θ ∧ (∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) ∧
     Function.support Θ ⊆ Work.MB.boxPow n ℓ ∧
     (∀ σ : Equiv.Perm (Fin n), (fun x : Submission.BoseGases.X n => Θ (x ∘ σ)) = Θ) ∧
     Work.BoseBoxFock.massR Θ
       = Work.BoseKinLoc.sqNormB n ℓ (Φ : Submission.BoseGases.X n → ℝ)) := by
  classical
  let Θ : Submission.BoseGases.X n → ℂ := fun x =>
      ((Φ x : ℝ) : ℂ) * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x
  change Measurable Θ ∧ (∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) ∧
     Function.support Θ ⊆ Work.MB.boxPow n ℓ ∧
     (∀ σ : Equiv.Perm (Fin n), (fun x : Submission.BoseGases.X n => Θ (x ∘ σ)) = Θ) ∧
     Work.BoseBoxFock.massR Θ
       = Work.BoseKinLoc.sqNormB n ℓ (Φ : Submission.BoseGases.X n → ℝ)
  -- the box is measurable and `Φ` is continuous
  have hboxm : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hcont : Continuous fun x : Submission.BoseGases.X n => (Φ x : ℝ) :=
    Φ.contDiff.continuous
  -- the two pointwise values of `Θ`
  have hΘmem : ∀ x : Submission.BoseGases.X n, x ∈ Submission.BoseGases.abox n ℓ →
      Θ x = ((Φ x : ℝ) : ℂ) := by
    intro x hx
    dsimp only [Θ]
    rw [Set.indicator_of_mem hx (fun _ => (1 : ℝ))]
    simp
  have hΘnot : ∀ x : Submission.BoseGases.X n, x ∉ Submission.BoseGases.abox n ℓ →
      Θ x = 0 := by
    intro x hx
    dsimp only [Θ]
    rw [Set.indicator_of_notMem hx (fun _ => (1 : ℝ))]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- measurability
    exact (Complex.continuous_ofReal.measurable.comp hcont.measurable).mul
      (Complex.continuous_ofReal.measurable.comp
        (Measurable.indicator measurable_const hboxm))
  · -- global boundedness: `Φ` is bounded on the compact box, `Θ` vanishes off it
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (f := fun x : Submission.BoseGases.X n => (Φ x : ℝ)) hcont.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · have h1 : ‖((Φ x : ℝ) : ℂ)‖ = |Φ x| := by
        have hsq : ‖((Φ x : ℝ) : ℂ)‖ ^ 2 = |Φ x| ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
          ring
        exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hsq
      rw [hΘmem x hx, h1]
      have h2 := hC x hx
      rw [Real.norm_eq_abs] at h2
      exact le_trans h2 (le_max_left C 0)
    · rw [hΘnot x hx, norm_zero]
      exact le_max_right C 0
  · -- support: `Θ` vanishes off the box
    intro x hx
    rw [Function.mem_support] at hx
    simp only [Work.MB.boxPow, Set.mem_univ_pi]
    intro i
    have hxab : x ∈ Submission.BoseGases.abox n ℓ := by
      by_contra h
      exact hx (hΘnot x h)
    rw [Work.BoseBoxFock.boxL_eq_acube hℓ]
    exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hxab i
  · -- permutation invariance
    intro σ
    funext x
    have hm : Submission.BoseGases.actPerm n σ x ∈ Submission.BoseGases.abox n ℓ ↔
        x ∈ Submission.BoseGases.abox n ℓ := by
      simp only [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.actPerm]
      exact ⟨fun h j => by simpa using h (σ.symm j), fun h i => h (σ i)⟩
    show Θ (Submission.BoseGases.actPerm n σ x) = Θ x
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [hΘmem (Submission.BoseGases.actPerm n σ x) (hm.mpr hx), hΘmem x hx]
      exact congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) (Φ.symm σ x)
    · rw [hΘnot (Submission.BoseGases.actPerm n σ x) (fun h => hx (hm.mp h)), hΘnot x hx]
  · -- the mass identity
    rw [Work.BoseBoxFock.massR_eq_integral_normSq]
    rw [show (fun x : Submission.BoseGases.X n => ‖Θ x‖ ^ 2)
        = (Submission.BoseGases.abox n ℓ).indicator (fun y => (Φ y : ℝ) ^ 2) from ?_]
    · rw [MeasureTheory.integral_indicator hboxm]
      rfl
    · funext x
      by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
      · have hind : (Submission.BoseGases.abox n ℓ).indicator (fun y => (Φ y : ℝ) ^ 2) x
            = (Φ x : ℝ) ^ 2 :=
          (Set.indicator_of_mem hx (fun y => (Φ y : ℝ) ^ 2)).trans rfl
        rw [hind, hΘmem x hx, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      · have hind : (Submission.BoseGases.abox n ℓ).indicator (fun y => (Φ y : ℝ) ^ 2) x = 0 :=
          Set.indicator_of_notMem hx (fun y => (Φ y : ℝ) ^ 2)
        rw [hind, hΘnot x hx, norm_zero]
        norm_num

end Work.BoseBoxFock
