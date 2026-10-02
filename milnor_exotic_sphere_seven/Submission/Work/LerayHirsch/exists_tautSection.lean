import Mathlib
import Submission.Work.LerayHirsch.TwistSection
import Submission.Work.LerayHirsch.TautTwist
import Submission.Work.LerayHirsch.TautEmbedCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The tautological nowhere-zero section of `ℓ^* ⊗ π^*E`

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι` be complex gluing data,
`P(E) = Work.LerayHirsch.ProjSpace Z` its projectivisation and `ℓ = Work.LerayHirsch.tautLine Z` the
tautological line bundle over it.  The twist `V = Work.LerayHirsch.tautTwist Z = ℓ^* ⊗ π^*E` carries
the **tautological section** whose value at `x` is the identity map `ℓ_x ≅ ℂ → E_{π x}` read through
`ℓ^* ⊗ π^*E ≅ Hom(ℓ, π^*E)`.  This module constructs it.

The fibre coordinate of that section, in the preferred chart `(tautLine Z).indexAt x` of `ℓ` and the
preferred chart `Z.indexAt (π x)` of `E`, is `Work.LerayHirsch.tautSectionVec Z x`
(`Work.LerayHirsch.TwistSection`), so the section is the map
`x ↦ ⟨x, tautSectionVec Z x⟩ : (realification (tautTwist Z)).TotalSpace`.

The content is therefore:

* `tautSectionVec_eq_normLift` — the fibre coordinate is the preferred-chart normalisation
  `TautEmbed.normLift` of the tautological point (the same vector that makes the embedding
  `ℓ ↪ π^*E` injective); in particular `tautSectionVec_ne_zero`, so the section misses the zero
  section and really is a section of the punctured bundle;
* `tautTwist_coordChange_tautSectionVec` — in a chart `p = ((i₁,k₁), i)` the trivialised coordinate
  of the section is exactly the local matrix `TautEmbed.chartRatioVec Z i₁ k₁ i x`, i.e. the two
  transitions coming from `ℓ^*` and the preferred chart of `ℓ` cancel;
* `continuous_tautSectionTotal` — continuity, read off in the preferred trivialisation (the total
  space of a bundle carries the bundle topology, not the product topology);
* `exists_tautSection` — the section, as a continuous map into the punctured realification.

-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The fibre coordinate of the tautological section is the preferred-chart normalisation**: in
the preferred chart of `ℓ` at `x` and the preferred chart of `E` at `π x`, the two definitions
coincide. -/
theorem tautSectionVec_eq_normLift
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (x : ProjSpace Z) :
    tautSectionVec Z x = TautEmbed.normLift Z x := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [TautEmbed.normLift_mk]
  simp only [tautSectionVec, TautEmbed.chartRatioVec_mk, TautEmbed.chartRatioRaw,
    TautEmbed.normFun, projMap_mkProj]
  rw [if_pos (TautEmbed.chartCoord_indexAt_ne_zero Z p)]

/-- **The tautological section misses the zero section.**  (This is the same non-vanishing that makes
the tautological embedding `ℓ ↪ π^*E` fibrewise injective.) -/
theorem tautSectionVec_ne_zero
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (x : ProjSpace Z) :
    tautSectionVec Z x ≠ 0 := by
  rw [tautSectionVec_eq_normLift Z x]
  exact TautEmbed.normLift_ne_zero Z x

/-- **The trivialised coordinate of the tautological section.**  In the chart
`p = ((i₁,k₁), i)` of the twist the transition functions of `ℓ^*` and the passage from the
preferred chart of `ℓ` at `x` cancel, and the coordinate is the local matrix of the tautological
embedding. -/
theorem tautTwist_coordChange_tautSectionVec
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : (ι × Fin (m + 1)) × ι) (x : ProjSpace Z)
    (hx : x ∈ tautBaseSetProj Z p.1) (hx2 : projMap Z x ∈ Z.baseSet p.2) :
    (tautTwist Z).coordChange ((tautTwist Z).indexAt x) p x (tautSectionVec Z x)
      = TautEmbed.chartRatioVec Z p.1.1 p.1.2 p.2 x := by
  have hidx : (tautTwist Z).indexAt x
      = ((tautLine Z).indexAt x, Z.indexAt (projMap Z x)) := rfl
  rw [hidx, twistCore_coordChange_eq, tautSectionVec_eq_normLift Z x]
  have hscl : Work.Gen.scl
      ((Work.Gen.dualLineCore (tautLine Z)).coordChange ((tautLine Z).indexAt x) p.1 x)
      = tautCoeffLift Z p.1 ((tautLine Z).indexAt x) x :=
    Work.Gen.scl_eq_of_apply _ _
      (fun v => tautLine_coordChange_apply Z p.1 ((tautLine Z).indexAt x) x v)
  rw [hscl]
  rw [show (bundleComap Z (projMap Z)).coordChange
        ((tautLine Z).indexAt x, Z.indexAt (projMap Z x)).2 p.2 x
      = Z.coordChange (Z.indexAt (projMap Z x)) p.2 (projMap Z x) from rfl]
  rw [TautEmbed.coordChange_normLift Z p.1.1 p.1.2 p.2 x hx hx2]
  rw [smul_smul]
  have h2 : x ∈ tautBaseSetProj Z ((tautLine Z).indexAt x) := (tautLine Z).mem_baseSet_at x
  have hcomp := tautCoeffLift_comp Z p.1 ((tautLine Z).indexAt x) p.1 (x := x) ⟨⟨hx, h2⟩, hx⟩
  rw [tautCoeffLift_self Z p.1 hx] at hcomp
  rw [mul_comm, hcomp, one_smul]

/-- **The tautological section of `ℓ^* ⊗ π^*E`, as a map of total spaces** (of the realification of
the twist). -/
abbrev tautSectionTotal (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    ProjSpace Z → (realification (tautTwist Z)).TotalSpace :=
  fun x => ⟨x, tautSectionVec Z x⟩

/-- **The local trivialisation of the tautological section.**  The chart `p = ((i₁,k₁), i)` of the
twist identifies the section with the continuous local matrix of the tautological embedding. -/
theorem realification_localTriv_tautSection
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : (ι × Fin (m + 1)) × ι) (x : ProjSpace Z)
    (hx : x ∈ tautBaseSetProj Z p.1) (hx2 : projMap Z x ∈ Z.baseSet p.2) :
    ((realification (tautTwist Z)).localTriv p) (tautSectionTotal Z x)
      = (⟨x, TautEmbed.chartRatioVec Z p.1.1 p.1.2 p.2 x⟩ :
          ProjSpace Z × EuclideanSpace ℂ (Fin (m + 1))) := by
  rw [VectorBundleCore.localTriv_apply]
  rw [show (tautSectionTotal Z x).proj = x from rfl,
    show (tautSectionTotal Z x).snd = tautSectionVec Z x from rfl]
  rw [show (realification (tautTwist Z)).indexAt x = (tautTwist Z).indexAt x
      from congrFun (realification_indexAt (tautTwist Z)) x]
  rw [show ⇑((realification (tautTwist Z)).coordChange ((tautTwist Z).indexAt x) p x)
      = ⇑((tautTwist Z).coordChange ((tautTwist Z).indexAt x) p x)
      from realification_coordChange (tautTwist Z) ((tautTwist Z).indexAt x) p x]
  exact Prod.ext rfl (tautTwist_coordChange_tautSectionVec Z p x hx hx2)

/-- **The tautological section of `ℓ^* ⊗ π^*E` is continuous** (in the bundle topology of the
punctured total space, which is what `zeroComplement` carries). -/
theorem continuous_tautSectionTotal
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    Continuous (tautSectionTotal Z) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set p : (ι × Fin (m + 1)) × ι := ((tautLine Z).indexAt x₀, Z.indexAt (projMap Z x₀)) with hp
  have hx₀₁ : x₀ ∈ tautBaseSetProj Z p.1 := (tautLine Z).mem_baseSet_at x₀
  have hx₀₂ : projMap Z x₀ ∈ Z.baseSet p.2 := Z.mem_baseSet_at _
  have hmem : tautBaseSetProj Z p.1 ∩ projMap Z ⁻¹' Z.baseSet p.2 ∈ 𝓝 x₀ :=
    ((isOpen_tautBaseSetProj Z p.1).inter
      ((Z.isOpen_baseSet p.2).preimage (projMap Z).continuous)).mem_nhds ⟨hx₀₁, hx₀₂⟩
  refine Bundle.Trivialization.continuousAt_of_comp_left
    ((realification (tautTwist Z)).localTriv p) ?_ ?_ ?_
  · exact continuousAt_id
  · rw [← VectorBundleCore.baseSet_at]
    rw [show (realification (tautTwist Z)).baseSet p = (tautTwist Z).baseSet p
        from congrFun (realification_baseSet (tautTwist Z)) p]
    exact ⟨hx₀₁, hx₀₂⟩
  · have hg : ContinuousAt (fun y : ProjSpace Z =>
        (⟨y, TautEmbed.chartRatioVec Z p.1.1 p.1.2 p.2 y⟩ :
          ProjSpace Z × EuclideanSpace ℂ (Fin (m + 1)))) x₀ :=
      ContinuousAt.prodMk continuousAt_id
        ((TautEmbed.continuousOn_chartRatioVec Z p.1.1 p.1.2 p.2).continuousAt hmem)
    refine hg.congr ?_
    filter_upwards [hmem] with y hy
    rw [Function.comp_apply]
    exact (realification_localTriv_tautSection Z p y hy.1 hy.2).symm

/-- The tautological section lies in the punctured total space. -/
theorem tautSectionTotal_mem_zeroComplement
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (x : ProjSpace Z) :
    tautSectionTotal Z x ∈ zeroComplement (realification (tautTwist Z)) :=
  (mem_zeroComplement _).mpr (tautSectionVec_ne_zero Z x)

theorem exists_tautSection {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    ∃ σ : C(Work.LerayHirsch.ProjSpace Z,
        ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.LerayHirsch.tautTwist Z)))),
      (∀ x, ((σ x : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.LerayHirsch.tautTwist Z))))
        : (Work.Thom.realification (Work.LerayHirsch.tautTwist Z)).TotalSpace).1 = x) ∧
      (∀ x, ((σ x : ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.LerayHirsch.tautTwist Z))))
        : (Work.Thom.realification (Work.LerayHirsch.tautTwist Z)).TotalSpace).2
        = Work.LerayHirsch.tautSectionVec Z x) := by
  refine ⟨⟨fun x => ⟨tautSectionTotal Z x, tautSectionTotal_mem_zeroComplement Z x⟩,
    Continuous.subtype_mk (continuous_tautSectionTotal Z) _⟩, ?_, ?_⟩
  · intro x; rfl
  · intro x; rfl

end

end Work.LerayHirsch
