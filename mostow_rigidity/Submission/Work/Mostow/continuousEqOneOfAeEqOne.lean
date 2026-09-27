import Mathlib
import Submission.Work.Mostow.VolDefs

/-!
# A continuous `Γ`-invariant function equal to `1` a.e. on a fundamental domain is `1`

A continuous real function on `ℍⁿ = E n` which is `Γ`-invariant and equals `1` almost everywhere
on a fundamental domain of `Γ` is identically `1`. The proof avoids any group-action API on sets:
the bad set `{g ≠ 1}` is open; its intersection with the fundamental domain is null by hypothesis,
and each translate of that intersection is null by `SMulInvariantMeasure`; countability of `Γ`
makes the union null, and `IsFundamentalDomain.ae_covers` then shows the bad set itself is null.
An open null set is empty because `volH` is positive on nonempty open sets (`volHPosOpen`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- A continuous `Γ`-invariant real function which equals `1` a.e. on a fundamental domain is
identically `1`. -/
theorem continuousEqOneOfAeEqOne (n : ℕ) (hI : HypIsometryProp n) {Γ : Subgroup (PO n 1)}
    [Countable Γ] [MeasurableConstSMul Γ (E n)] [SMulInvariantMeasure Γ (E n) (volH n)]
    {D : Set (E n)} (hD : IsFundamentalDomain Γ D (volH n)) {g : E n → ℝ} (hg : Continuous g)
    (hinv : ∀ (γ : Γ) (u : E n), g (γ • u) = g u)
    (hae : ∀ᵐ u ∂(volH n), u ∈ D → g u = 1) : ∀ u, g u = 1 := by
  have hAopen : IsOpen {u : E n | g u ≠ 1} := isOpen_ne.preimage hg
  have hDAnull : volH n (D ∩ {u : E n | g u ≠ 1}) = 0 := by
    have hset : {u : E n | ¬ (u ∈ D → g u = 1)} = D ∩ {u : E n | g u ≠ 1} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, not_imp]
    rw [← hset]
    exact ae_iff.mp hae
  have hbadnull : volH n (⋃ γ : Γ, (fun v : E n => γ • v) ⁻¹' (D ∩ {u : E n | g u ≠ 1})) = 0 := by
    refine measure_iUnion_null fun γ => ?_
    obtain ⟨T, hTsub, hTmeas, hT0⟩ := exists_measurable_superset_of_null hDAnull
    refine measure_mono_null (Set.preimage_mono hTsub) ?_
    rw [SMulInvariantMeasure.measure_preimage_smul γ hTmeas]
    exact hT0
  have hNnull : volH n {u : E n | ¬ ∃ γ : Γ, γ • u ∈ D} = 0 := ae_iff.mp hD.ae_covers
  have hAnull : volH n {u : E n | g u ≠ 1} = 0 := by
    have hsub : {u : E n | g u ≠ 1} ⊆
        (⋃ γ : Γ, (fun v : E n => γ • v) ⁻¹' (D ∩ {u : E n | g u ≠ 1}))
          ∪ {u : E n | ¬ ∃ γ : Γ, γ • u ∈ D} := by
      rintro u hu
      by_cases hex : ∃ γ : Γ, γ • u ∈ D
      · obtain ⟨γ, hγ⟩ := hex
        refine Or.inl (Set.mem_iUnion.mpr ⟨γ, ⟨hγ, ?_⟩⟩)
        show g (γ • u) ≠ 1
        rwa [hinv γ u]
      · exact Or.inr hex
    have hunion : volH n ((⋃ γ : Γ, (fun v : E n => γ • v) ⁻¹' (D ∩ {u : E n | g u ≠ 1}))
        ∪ {u : E n | ¬ ∃ γ : Γ, γ • u ∈ D}) = 0 := by
      rw [measure_union_null_iff]
      exact ⟨hbadnull, hNnull⟩
    exact measure_mono_null hsub hunion
  intro u
  by_contra hu
  have hne : ({u : E n | g u ≠ 1}).Nonempty := ⟨u, hu⟩
  have hpos := volHPosOpen n hAopen hne
  rw [hAnull] at hpos
  exact lt_irrefl 0 hpos

end Work.Mostow
