import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The preimage of a `volH`-fundamental domain under the orbit map

Let `π g = g • 0` be the orbit map `PO n 1 → ℍⁿ` and suppose `π` pushes Haar measure on `PO n 1`
to the scalar multiple `c • volH n` of hyperbolic volume (`hmap`).  Then for every subgroup
`Γ ≤ PO n 1` and every `volH`-fundamental domain `D` of `Γ` (`hD`) the preimage `π ⁻¹' D` is a
fundamental domain for the left action of `Γ` on `PO n 1` with respect to Haar measure, and its
Haar measure is `c * volH n D`.

Both statements are proved from `hmap` alone (plus `π (γ • g) = γ • π g`, which is the multiplication
law of `POActionProp`):
* the measure of the preimage of *any* set `Z` satisfies
  `volume (π ⁻¹' Z) ≤ c * volH n Z` (`Measure.le_map_apply`), so preimages of `volH`-null sets are
  Haar-null;
* `ae_covers` follows because `D` covers `ℍⁿ` up to a `volH`-null set and `π` is `Γ`-equivariant;
* `aedisjoint` follows because `γ • (π ⁻¹' D) ⊆ π ⁻¹' (γ • D)` and two distinct translates of `D`
  meet in a `volH`-null set (`IsFundamentalDomain.aedisjoint` of `hD`);
* the measure identity is `Measure.map_apply` at the measurable set `D`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Pointwise

theorem pullback_dirichletSet (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) [Countable Γ]
    {c : ENNReal}
    (hmap : MeasureTheory.Measure.map
        (fun g : LeanEval.Geometry.MostowRigidity.PO n 1 => g • (0 : Submission.Mostow.E n))
        (MeasureTheory.MeasureSpace.volume :
          MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1)) =
        c • Submission.Mostow.volH n)
    {D : Set (Submission.Mostow.E n)}
    (hD : MeasureTheory.IsFundamentalDomain Γ D (Submission.Mostow.volH n))
    (hDmeas : MeasurableSet D) :
    MeasureTheory.IsFundamentalDomain Γ
        ((fun g : LeanEval.Geometry.MostowRigidity.PO n 1 => g • (0 : Submission.Mostow.E n)) ⁻¹' D)
        (MeasureTheory.MeasureSpace.volume :
          MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1)) ∧
      (MeasureTheory.MeasureSpace.volume :
          MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1))
        ((fun g : LeanEval.Geometry.MostowRigidity.PO n 1 => g • (0 : Submission.Mostow.E n)) ⁻¹' D)
        = c * Submission.Mostow.volH n D := by
  classical
  have hB : POBasic n := POBasic.ofProp hA
  let π : PO n 1 → E n := fun g => g • (0 : E n)
  have hπ_meas : Measurable π :=
    (hB.continuous_smul.comp (Continuous.prodMk continuous_id continuous_const)).measurable
  have hπ_aemeas : AEMeasurable π (MeasureSpace.volume : Measure (PO n 1)) :=
    hπ_meas.aemeasurable
  have hmap' : Measure.map π (MeasureSpace.volume : Measure (PO n 1)) = c • volH n := hmap
  -- `π` is `Γ`-equivariant
  have hπ_smul : ∀ (γ : Γ) (x : PO n 1), π (γ • x) = γ • π x := by
    intro γ x
    show ((γ • x : PO n 1) • (0 : E n)) = γ • (x • (0 : E n))
    rw [show (γ • x : PO n 1) = (γ : PO n 1) * x from rfl]
    exact hB.mul_smul (γ : PO n 1) x (0 : E n)
  -- a translate of the preimage sits in the preimage of the translate
  have hsub : ∀ γ : Γ, γ • (π ⁻¹' D) ⊆ π ⁻¹' (γ • D) := by
    intro γ y hy
    rw [Set.mem_smul_set] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [Set.mem_preimage, ← hzy, hπ_smul γ z]
    exact Set.mem_smul_set.mpr ⟨π z, hz, rfl⟩
  refine ⟨?_, ?_⟩
  · change IsFundamentalDomain Γ (π ⁻¹' D) (MeasureSpace.volume : Measure (PO n 1))
    refine ⟨?_, ?_, ?_⟩
    · exact (hπ_meas hDmeas).nullMeasurableSet
    · rw [ae_iff]
      have hTvol : volH n {x : E n | ¬ ∃ γ : Γ, γ • x ∈ D} = 0 := by
        simpa only using (ae_iff.mp hD.ae_covers)
      have hT : (Measure.map π (MeasureSpace.volume : Measure (PO n 1)))
          {x : E n | ¬ ∃ γ : Γ, γ • x ∈ D} = 0 := by
        rw [hmap', Measure.smul_apply, hTvol]
        simp
      have hnull : (MeasureSpace.volume : Measure (PO n 1))
          (π ⁻¹' {x : E n | ¬ ∃ γ : Γ, γ • x ∈ D}) = 0 :=
        Measure.preimage_null_of_map_null hπ_aemeas hT
      refine le_antisymm ?_ (by simp)
      calc (MeasureSpace.volume : Measure (PO n 1))
            {g : PO n 1 | ¬ ∃ γ : Γ, γ • g ∈ π ⁻¹' D}
          ≤ (MeasureSpace.volume : Measure (PO n 1))
            (π ⁻¹' {x : E n | ¬ ∃ γ : Γ, γ • x ∈ D}) := measure_mono (by
              intro g hg
              rintro ⟨γ, hγ⟩
              exact hg ⟨γ, by rw [Set.mem_preimage, hπ_smul γ g]; exact hγ⟩)
        _ = 0 := hnull
    · intro a b hab
      have hZ : (Measure.map π (MeasureSpace.volume : Measure (PO n 1)))
          ((a • D) ∩ (b • D)) = 0 := by
        rw [hmap', Measure.smul_apply, hD.aedisjoint hab]
        simp
      have hnull : (MeasureSpace.volume : Measure (PO n 1))
          (π ⁻¹' ((a • D) ∩ (b • D))) = 0 :=
        Measure.preimage_null_of_map_null hπ_aemeas hZ
      change (MeasureSpace.volume : Measure (PO n 1))
        ((a • (π ⁻¹' D)) ∩ (b • (π ⁻¹' D))) = 0
      refine le_antisymm ?_ (by simp)
      calc (MeasureSpace.volume : Measure (PO n 1))
            ((a • (π ⁻¹' D)) ∩ (b • (π ⁻¹' D)))
          ≤ (MeasureSpace.volume : Measure (PO n 1)) (π ⁻¹' ((a • D) ∩ (b • D))) :=
            measure_mono (by rintro y ⟨hy1, hy2⟩; exact ⟨hsub a hy1, hsub b hy2⟩)
        _ = 0 := hnull
  · change (MeasureSpace.volume : Measure (PO n 1)) (π ⁻¹' D) = c * volH n D
    rw [← Measure.map_apply hπ_meas hDmeas, hmap', Measure.smul_apply]
    exact smul_eq_mul c _

end Work.Mostow
