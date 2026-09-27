import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# Splitting an `A`-invariant measure along an a.e.-invariant set (C4c, step 5)

Let `μ` be an `A`-invariant probability measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, let `E` be a measurable
set which is a.e. invariant under **every** diagonal element `aDiag t` (`t : Fin 3 → ℝ`), and
suppose `μ E ≠ 0`, `μ Eᶜ ≠ 0` and `μ (Drho ρ) = 1`.  Then `μ` splits as the convex combination

  `μ = μ E • ν₁ + μ Eᶜ • ν₂`

of two `A`-invariant probability measures, with `ν₁` carried by `E`, `ν₂` carried by `Eᶜ`,
both of them carried by `Drho ρ`, and `ν₁ ≠ μ`.

This is the "extreme implies ergodic" step of the ergodic maximiser (EKL Theorem 10.1 proof,
step (5) of `Submission/Work/EKLPlan/ROUTE_LEAD.md`, §C4c): if `μ` were an extreme point of the
convex set of `A`-invariant probabilities carried by `Drho ρ`, such a decomposition with
`ν₁ ≠ μ` would be a contradiction.

The witnesses are the normalised restrictions `ν₁ = (μ E)⁻¹ • μ|_E` and
`ν₂ = (μ Eᶜ)⁻¹ • μ|_Eᶜ`:

* `νᵢ` is `A`-invariant because the restriction of an invariant measure to an a.e.-invariant
  measurable set is again invariant (here `A` acts by homeomorphisms, and `aDiag t ⁻¹' E =ᵐ E`);
* `ν₁ Eᶜ = 0` and `ν₂ E = 0` because `E ∩ Eᶜ = ∅`;
* `νᵢ (Drho ρ) = 1` because `Drho ρ` covers `E` and `Eᶜ` in outer measure.  Note that `Drho ρ`
  need *not* be measurable for this: by subadditivity of the outer measure,
  `μ (Drho ρ) ≤ μ (Drho ρ ∩ E) + μ (Drho ρ ∩ Eᶜ) ≤ μ E + μ Eᶜ = μ (Drho ρ)`, so both terms are
  equalities;
* `ν₁ ≠ μ` because `ν₁ Eᶜ = 0` while `μ Eᶜ ≠ 0`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.EKLComp.ErgMax

open Work.EKLContract

/-- If `T` preserves `μ` and `E` is a measurable set with `T ⁻¹' E =ᵐ[μ] E`, then the restricted
measure `μ.restrict E` is again `T`-invariant.  This is `MeasurePreserving.restrict_preimage`
applied to `E` (for a self-map the source and target sets agree up to a null set). -/
theorem measurePreserving_restrict_of_ae_preimage {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} {E : Set α} (hT : MeasurePreserving T μ μ) (hE : MeasurableSet E)
    (hinv : T ⁻¹' E =ᵐ[μ] E) : MeasurePreserving T (μ.restrict E) (μ.restrict E) := by
  have h := hT.restrict_preimage (μa := μ) (μb := μ) hE
  rwa [Measure.restrict_congr_set hinv] at h

/-- The same statement for an `ℝ≥0∞`-multiple of the restricted measure: every scalar multiple
of `μ.restrict E` is `T`-invariant as soon as `μ.restrict E` is. -/
theorem measurePreserving_smul_restrict_of_ae_preimage {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} {E : Set α} (hT : MeasurePreserving T μ μ)
    (hE : MeasurableSet E) (hinv : T ⁻¹' E =ᵐ[μ] E) (c : ℝ≥0∞) :
    MeasurePreserving T (c • μ.restrict E) (c • μ.restrict E) := by
  have h := hT.restrict_preimage (μa := μ) (μb := μ) hE
  rw [Measure.restrict_congr_set hinv] at h
  exact ⟨h.measurable, by rw [Measure.map_smul _ h.measurable.aemeasurable, h.map_eq]⟩

/-- If a probability measure gives `Drho ρ` full mass, then it gives `Drho ρ ∩ E` the mass of `E`
(for any measurable `E`).  No measurability of `Drho ρ` is needed: the two sets `Drho ρ ∩ E` and
`Drho ρ ∩ Eᶜ` cover `Drho ρ`, so their outer measures squeeze the two summands of
`μ E + μ Eᶜ = μ univ = μ (Drho ρ)`. -/
theorem measure_inter_Drho_eq {μ : Measure X3} [IsProbabilityMeasure μ] {E : Set X3}
    (hE : MeasurableSet E) (ρ : ℝ) (hρ : μ (Drho ρ) = 1) :
    μ (Drho ρ ∩ E) = μ E ∧ μ (Drho ρ ∩ Eᶜ) = μ Eᶜ := by
  have hsum : μ (Drho ρ ∩ E) + μ (Drho ρ ∩ Eᶜ) = μ E + μ Eᶜ := by
    refine le_antisymm (add_le_add (measure_mono Set.inter_subset_right)
      (measure_mono Set.inter_subset_right)) ?_
    calc μ E + μ Eᶜ = μ Set.univ := measure_add_measure_compl hE
      _ = μ (Drho ρ) := by rw [measure_univ, hρ]
      _ ≤ μ ((Drho ρ ∩ E) ∪ (Drho ρ ∩ Eᶜ)) := measure_mono (by
            intro x hx
            by_cases h : x ∈ E
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr ⟨hx, h⟩)
      _ ≤ μ (Drho ρ ∩ E) + μ (Drho ρ ∩ Eᶜ) := measure_union_le _ _
  have hEctop : μ Eᶜ ≠ ⊤ := measure_ne_top μ Eᶜ
  have hEtop : μ E ≠ ⊤ := measure_ne_top μ E
  have ha : μ (Drho ρ ∩ E) ≤ μ E := measure_mono Set.inter_subset_right
  have hb : μ (Drho ρ ∩ Eᶜ) ≤ μ Eᶜ := measure_mono Set.inter_subset_right
  have ha' : μ E ≤ μ (Drho ρ ∩ E) := by
    refine ENNReal.le_of_add_le_add_right hEctop ?_
    calc μ E + μ Eᶜ = μ (Drho ρ ∩ E) + μ (Drho ρ ∩ Eᶜ) := hsum.symm
      _ ≤ μ (Drho ρ ∩ E) + μ Eᶜ := add_le_add (le_refl _) hb
  have hb' : μ Eᶜ ≤ μ (Drho ρ ∩ Eᶜ) := by
    refine ENNReal.le_of_add_le_add_right hEtop ?_
    calc μ Eᶜ + μ E = μ E + μ Eᶜ := add_comm _ _
      _ = μ (Drho ρ ∩ E) + μ (Drho ρ ∩ Eᶜ) := hsum.symm
      _ ≤ μ E + μ (Drho ρ ∩ Eᶜ) := add_le_add ha (le_refl _)
      _ = μ (Drho ρ ∩ Eᶜ) + μ E := add_comm _ _
  exact ⟨le_antisymm ha ha', le_antisymm hb hb'⟩

theorem exists_split_ae_invariant (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (hμ : Work.EKLContract.IsAInvariant μ)
    {E : Set Work.EKLContract.X3} (hE : MeasurableSet E)
    (hinv : ∀ t : Fin 3 → ℝ,
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E)
    (h0 : μ E ≠ 0) (h1 : μ Eᶜ ≠ 0) (ρ : ℝ) (hρ : μ (Work.EKLContract.Drho ρ) = 1) :
    ∃ ν₁ ν₂ : MeasureTheory.Measure Work.EKLContract.X3,
      MeasureTheory.IsProbabilityMeasure ν₁ ∧ MeasureTheory.IsProbabilityMeasure ν₂ ∧
      Work.EKLContract.IsAInvariant ν₁ ∧ Work.EKLContract.IsAInvariant ν₂ ∧
      ν₁ Eᶜ = 0 ∧ ν₂ E = 0 ∧ ν₁ (Work.EKLContract.Drho ρ) = 1 ∧
      ν₂ (Work.EKLContract.Drho ρ) = 1 ∧ ν₁ ≠ μ ∧ μ = μ E • ν₁ + μ Eᶜ • ν₂ := by
  have hEtop : μ E ≠ ⊤ := measure_ne_top μ E
  have hEctop : μ Eᶜ ≠ ⊤ := measure_ne_top μ Eᶜ
  -- `Eᶜ` is a.e. invariant as well, since `aDiag t ⁻¹' Eᶜ = (aDiag t ⁻¹' E)ᶜ`
  have hinvc : ∀ t : Fin 3 → ℝ, (fun x : X3 => aDiag t • x) ⁻¹' Eᶜ =ᵐ[μ] Eᶜ := by
    intro t
    rw [Set.preimage_compl]
    exact (hinv t).compl
  obtain ⟨hDE, hDEc⟩ := measure_inter_Drho_eq hE ρ hρ
  have hν1_prob : IsProbabilityMeasure ((μ E)⁻¹ • μ.restrict E) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, Measure.restrict_apply' hE, Set.univ_inter]
    exact ENNReal.inv_mul_cancel h0 hEtop
  have hν2_prob : IsProbabilityMeasure ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, Measure.restrict_apply' hE.compl, Set.univ_inter]
    exact ENNReal.inv_mul_cancel h1 hEctop
  have hν1_inv : IsAInvariant ((μ E)⁻¹ • μ.restrict E) := fun t =>
    measurePreserving_smul_restrict_of_ae_preimage (hμ t) hE (hinv t) ((μ E)⁻¹)
  have hν2_inv : IsAInvariant ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) := fun t =>
    measurePreserving_smul_restrict_of_ae_preimage (hμ t) hE.compl (hinvc t) ((μ Eᶜ)⁻¹)
  have hν1_Ec : ((μ E)⁻¹ • μ.restrict E) Eᶜ = 0 := by
    rw [Measure.smul_apply, Measure.restrict_apply' hE]
    simp
  have hν2_E : ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) E = 0 := by
    rw [Measure.smul_apply, Measure.restrict_apply' hE.compl]
    simp
  have hν1_Drho : ((μ E)⁻¹ • μ.restrict E) (Drho ρ) = 1 := by
    rw [Measure.smul_apply, Measure.restrict_apply' hE, hDE]
    exact ENNReal.inv_mul_cancel h0 hEtop
  have hν2_Drho : ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) (Drho ρ) = 1 := by
    rw [Measure.smul_apply, Measure.restrict_apply' hE.compl, hDEc]
    exact ENNReal.inv_mul_cancel h1 hEctop
  have hne : ((μ E)⁻¹ • μ.restrict E) ≠ μ := by
    intro h
    have hh := hν1_Ec
    rw [h] at hh
    exact h1 hh
  have hA : μ E • ((μ E)⁻¹ • μ.restrict E) = μ.restrict E := by
    rw [smul_smul, ENNReal.mul_inv_cancel h0 hEtop, one_smul]
  have hB : μ Eᶜ • ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) = μ.restrict Eᶜ := by
    rw [smul_smul, ENNReal.mul_inv_cancel h1 hEctop, one_smul]
  have hdecomp : μ = μ E • ((μ E)⁻¹ • μ.restrict E) + μ Eᶜ • ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) := by
    rw [hA, hB, Measure.restrict_add_restrict_compl hE]
  exact ⟨_, _, hν1_prob, hν2_prob, hν1_inv, hν2_inv, hν1_Ec, hν2_E, hν1_Drho, hν2_Drho,
    hne, hdecomp⟩

end Work.EKLComp.ErgMax
