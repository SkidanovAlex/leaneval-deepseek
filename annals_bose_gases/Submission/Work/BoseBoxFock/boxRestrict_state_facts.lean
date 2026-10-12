import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.assembly_of_row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The four state facts about the box restriction `boxRestrictC ℓ Φ` that the slot calculus
needs, for *every* `ℓ : ℝ` (no positivity hypothesis on `ℓ`).**

* measurable: `Φ` is continuous and `abox n ℓ` is measurable;
* everywhere bounded: for `0 < ℓ` this is `Work.BoseBoxFock.boxRestrictState` (the box is compact
  and `Φ` is continuous there); for `ℓ < 0` one has `abox n ℓ = ∅` (each coordinate lies in the
  empty `Icc (-ℓ/2) (ℓ/2)`), so `Θ ≡ 0` and `C = 0` works; for `ℓ = 0` every `x ∈ abox n ℓ` has all
  coordinates zero (`|x i m| ≤ 0` from `Submission.BoseGases.mem_abox_iff`), so `Θ` is bounded by
  `|Φ 0|`;
* support in `Work.MB.boxPow n ℓ`: `Θ` is supported in `abox n ℓ = Set.univ.pi (fun _ => acube ℓ)`,
  and `Submission.BoseGases.acube ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ` for every `ℓ`
  (`Work.MB.acube_subset_boxL_all`), so `abox n ℓ ⊆ boxPow n ℓ` (`Work.MB.mem_boxPow_iff`);
* permutation invariance: the same argument as in `Work.BoseBoxFock.boxRestrictState`
  (`Φ.symm` together with the invariance of `abox n ℓ` under coordinate permutations; note that the
  statement there is already phrased as `fun x => Θ (x ∘ σ) = Θ`, which is what is wanted here). -/
theorem boxRestrict_state_facts {n : ℕ} {ℓ : ℝ} (Φ : Work.BoseKinLoc.BoxState n ℓ) :
    Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) ∧
    (∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.boxRestrictC ℓ Φ x‖ ≤ C) ∧
    Function.support (Work.BoseBoxFock.boxRestrictC ℓ Φ) ⊆ Work.MB.boxPow n ℓ ∧
    (∀ σ : Equiv.Perm (Fin n),
      (fun x => Work.BoseBoxFock.boxRestrictC ℓ Φ (x ∘ σ)) = Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
  classical
  -- `Φ` is continuous and the box is measurable
  have hboxm : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hcont : Continuous fun x : Submission.BoseGases.X n => (Φ x : ℝ) :=
    Φ.contDiff.continuous
  -- the two pointwise values of the box restriction
  have hΘmem : ∀ x : Submission.BoseGases.X n, x ∈ Submission.BoseGases.abox n ℓ →
      boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) := by
    intro x hx
    rw [boxRestrictC, Set.indicator_of_mem hx (fun _ => (1 : ℝ))]
    simp
  have hΘnot : ∀ x : Submission.BoseGases.X n, x ∉ Submission.BoseGases.abox n ℓ →
      boxRestrictC ℓ Φ x = 0 := by
    intro x hx
    rw [boxRestrictC, Set.indicator_of_notMem hx (fun _ => (1 : ℝ))]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- measurability: `Φ` is continuous and the box indicator is measurable
    show Measurable (fun x : Submission.BoseGases.X n =>
      ((Φ x : ℝ) : ℂ) * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x)
    exact (Complex.continuous_ofReal.measurable.comp hcont.measurable).mul
      (Complex.continuous_ofReal.measurable.comp
        (Measurable.indicator measurable_const hboxm))
  · -- everywhere bounded, uniformly in `ℓ`: pass to the enlarged box `max ℓ 1 > 0`, on which `Φ`
    -- is bounded by compactness; off the box the restriction vanishes
    have hsub : Submission.BoseGases.abox n ℓ ⊆ Submission.BoseGases.abox n (max ℓ 1) := by
      intro x hx
      rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
      intro i
      have hi := hx i
      rw [Submission.BoseGases.mem_acube_iff] at hi
      rw [Submission.BoseGases.mem_acube_iff]
      intro m
      obtain ⟨h1, h2⟩ := hi m
      rw [Set.mem_Icc]
      exact ⟨by linarith [h1, le_max_left ℓ 1], by linarith [h2, le_max_left ℓ 1]⟩
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n
        (by exact lt_of_lt_of_le zero_lt_one (le_max_right ℓ 1) :
          (0 : ℝ) < max ℓ 1)).exists_bound_of_continuousOn
        (f := fun x : Submission.BoseGases.X n => (Φ x : ℝ)) hcont.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [hΘmem x hx, Complex.norm_real]
      have h2 := hC x (hsub hx)
      rw [Real.norm_eq_abs] at h2
      exact le_trans h2 (le_max_left C 0)
    · rw [hΘnot x hx, norm_zero]
      exact le_max_right C 0
  · -- support: `Θ` vanishes off `abox n ℓ`, and `acube ℓ ⊆ boxL ℓ` for every `ℓ`
    intro x hx
    rw [Function.mem_support] at hx
    rw [Work.MB.mem_boxPow_iff]
    intro i
    have hxab : x ∈ Submission.BoseGases.abox n ℓ := by
      by_contra h
      exact hx (hΘnot x h)
    exact Work.MB.acube_subset_boxL_all ((Submission.BoseGases.mem_abox_iff n ℓ x).mp hxab i)
  · -- permutation invariance
    intro σ
    funext x
    have hm : Submission.BoseGases.actPerm n σ x ∈ Submission.BoseGases.abox n ℓ ↔
        x ∈ Submission.BoseGases.abox n ℓ := by
      simp only [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.actPerm]
      exact ⟨fun h j => by simpa using h (σ.symm j), fun h i => h (σ i)⟩
    show boxRestrictC ℓ Φ (Submission.BoseGases.actPerm n σ x) = boxRestrictC ℓ Φ x
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [hΘmem (Submission.BoseGases.actPerm n σ x) (hm.mpr hx), hΘmem x hx]
      exact congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) (Φ.symm σ x)
    · rw [hΘnot (Submission.BoseGases.actPerm n σ x) (fun h => hx (hm.mp h)), hΘnot x hx]

end Work.BoseBoxFock
