import Mathlib
import Submission.Work.Drive.mixedFactorF1
import Submission.Work.Drive.exists_lift_classLoop_rotCapping
import Submission.Work.Drive.referenceFunctional

/-!
# The two mixed factors of the `hn2` reference triple, ready for the assembly

This is the end-point of the `(F1)` lane (`F1_GENERICITY_RESOLUTION.md`): from the configuration chart
`Q` alone (plus its level band and the design's level inequalities `c₂ < c`, `β < lam`), there is a
*reference functional* `φ` and a radius `δ > 0` such that, for **every** triple of perturbation
parameters `(τ₀, τ₁, τ₂)` of norm below `δ`, both mixed factors of the reference triple are odd:

* `ε(R; chart P₀) = coreSideCountPt (chartPert τ₀ ∘ rotCapping u₀ ∘ Q) (diskPlane (chartPert τ₂ ∘ R))`,
* `ε(R; chart P₁) = coreSideCountPt (chartPert τ₁ ∘ rotCapping u₁ ∘ Q) (diskPlane (chartPert τ₂ ∘ R))`,

where `R = linPlaneChart φ lam hlampos` is the linear reference plane.  The construction is

1. the class lifts `V₀`, `V₁` of the two rotated configuration charts with their essentiality, by
   `Work.Drive.exists_lift_classLoop_rotCapping`;
2. **one** functional `ℓ`, generic along both lifts and robust under all small class perturbations, by
   `Work.Drive.exists_genAlong_family_classEquiv`;
3. `φ` with `linFun φ = ℓ`, by `Work.Drive.exists_linFun_eq`;
4. the level radius of `Work.Drive.exists_levelScale_bounds_ball`, and
   `Work.Drive.exists_delta_odd_coreSideCountPt_rotCapping` at the two blocks.

The remaining freedom is the reference-triple genericity lemma (which produces the parameters `τ` of
arbitrarily small norm), the engine's `hdisj`/`hbot`, the three `T6` instances and the six
`CntAt → sideGerm` conversions; see `HN2_MIXED_FACTOR_STATUS.md` §3.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The two mixed factors of the `hn2` reference triple.** -/
theorem exists_delta_odd_coreSideCountPt_mixed {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (u₀ u₁ : UnitAddCircle)
    {c β lam c₂ : ℝ} (hc : 0 < c) (hβpos : 0 < β) (hlampos : 0 < lam) (hc₂ : 0 < c₂)
    (hc₂c : c₂ < c) (hβlam : β < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) :
    ∃ (φ : Eucl 3 ≃L[ℝ] Eucl 3) (δ : ℝ), 0 < δ ∧
      ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δ → ‖τ₁‖ < δ → ‖τ₂‖ < δ →
        Odd (coreSideCountPt (chartPert τ₀ ∘ fun z => rotCapping u₀ (Q z)) c₂
          (diskPlane (chartPert τ₂ ∘ linPlaneChart φ lam hlampos))) ∧
        Odd (coreSideCountPt (chartPert τ₁ ∘ fun z => rotCapping u₁ (Q z)) c₂
          (diskPlane (chartPert τ₂ ∘ linPlaneChart φ lam hlampos))) := by
  classical
  -- ## 1. the class lifts of the two rotated configuration charts
  obtain ⟨V₀, hV₀ne, hV₀sm, hV₀cls, κ₀, hκ₀, hκ₀e⟩ := exists_lift_classLoop_rotCapping hγ hQ u₀
  obtain ⟨V₁, hV₁ne, hV₁sm, hV₁cls, κ₁, hκ₁, hκ₁e⟩ := exists_lift_classLoop_rotCapping hγ hQ u₁
  -- ## 2. one functional, generic along both and robust under small class perturbations
  have hVs : ∀ i : Fin 2, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (![V₀, V₁] i) := by
    intro i
    fin_cases i
    · simpa using hV₀sm
    · simpa using hV₁sm
  have hVne : ∀ (i : Fin 2) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → ![V₀, V₁] i t ≠ 0 := by
    intro i t _
    fin_cases i
    · simpa using hV₀ne t
    · simpa using hV₁ne t
  obtain ⟨ℓ, hℓne, δ₁, hδ₁pos, hδ₁⟩ :=
    exists_genAlong_family_classEquiv (fun i : Fin 2 => ![V₀, V₁] i) hVs hVne
  -- ## 3. the reference functional
  obtain ⟨φ, hφ⟩ := exists_linFun_eq ℓ hℓne
  -- ## 4. the level radius
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_levelScale_bounds_ball hc hβpos hlampos hc₂ hc₂c hβlam
  refine ⟨φ, min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun τ₀ τ₁ τ₂ h₀ h₁ h₂ => ⟨?_, ?_⟩⟩
  · -- block `0`
    have h₀₁ : ‖τ₀‖ < δ₁ := lt_of_lt_of_le h₀ (min_le_left _ _)
    have h₂₁ : ‖τ₂‖ < δ₁ := lt_of_lt_of_le h₂ (min_le_left _ _)
    have hlev := hδ₂ τ₀ τ₂ (lt_of_lt_of_le h₀ (min_le_right _ _))
      (lt_of_lt_of_le h₂ (min_le_right _ _))
    refine odd_coreSideCountPt_rotCapping_of_genAlong hγ hQ φ u₀ hc hc₂ hβpos hlampos
      hclow hβ hlev.1 hlev.2 V₀ hV₀sm hV₀ne hV₀cls hκ₀ hκ₀e ?_
    have hg : GenAlong (ℓ ∘L (((classEquiv τ₂).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ₀ : Eucl 3 →L[ℝ] Eucl 3))) V₀ := by
      simpa using hδ₁ τ₀ τ₂ h₀₁ h₂₁ 0
    refine (GenAlong_congr (V := V₀)
      (ℓ := ℓ ∘L (((classEquiv τ₂).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ₀ : Eucl 3 →L[ℝ] Eucl 3)))
      (ℓ' := (linFunCLM φ) ∘L (((classEquiv τ₂).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ₀ : Eucl 3 →L[ℝ] Eucl 3))) ?_).mp hg
    intro v
    simp only [ContinuousLinearMap.comp_apply, linFunCLM_apply]
    exact (hφ _).symm
  · -- block `1`
    have h₁₁ : ‖τ₁‖ < δ₁ := lt_of_lt_of_le h₁ (min_le_left _ _)
    have h₂₁ : ‖τ₂‖ < δ₁ := lt_of_lt_of_le h₂ (min_le_left _ _)
    have hlev := hδ₂ τ₁ τ₂ (lt_of_lt_of_le h₁ (min_le_right _ _))
      (lt_of_lt_of_le h₂ (min_le_right _ _))
    refine odd_coreSideCountPt_rotCapping_of_genAlong hγ hQ φ u₁ hc hc₂ hβpos hlampos
      hclow hβ hlev.1 hlev.2 V₁ hV₁sm hV₁ne hV₁cls hκ₁ hκ₁e ?_
    have hg : GenAlong (ℓ ∘L (((classEquiv τ₂).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ₁ : Eucl 3 →L[ℝ] Eucl 3))) V₁ := by
      simpa using hδ₁ τ₁ τ₂ h₁₁ h₂₁ 1
    refine (GenAlong_congr (V := V₁)
      (ℓ := ℓ ∘L (((classEquiv τ₂).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ₁ : Eucl 3 →L[ℝ] Eucl 3)))
      (ℓ' := (linFunCLM φ) ∘L (((classEquiv τ₂).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ₁ : Eucl 3 →L[ℝ] Eucl 3))) ?_).mp hg
    intro v
    simp only [ContinuousLinearMap.comp_apply, linFunCLM_apply]
    exact (hφ _).symm

end

end Work.Drive
