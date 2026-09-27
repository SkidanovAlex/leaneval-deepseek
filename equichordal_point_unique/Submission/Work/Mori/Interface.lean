import Submission.Work.Mori.Defs
import Submission.Work.Mori.holomorphicOnX_opens_sub_const
import Submission.Work.Parabolic.holomorphicOnX_comp_biholomorph
import Submission.Work.Parabolic.Transport

/-!
# Interface lemmas for the parabolic case

Small glue for the two assemblies of `Submission/Work/Mori/Main.lean`:

* `Work.Mori.hasHolomorphicEmbedding_of_diffeomorph` — holomorphic embeddability into `ℂ`
  transports along a biholomorphism;
* `Work.Mori.hasHolomorphicEmbedding_opens` — every open subset of `ℂ` embeds holomorphically into
  `ℂ` (the inclusion);
* `Work.Mori.hasHolomorphicEmbedding_of_hasMoriNormalForm` — a surface in Mori normal form embeds
  holomorphically into `ℂ`, so the planarity hypothesis of `Work.Mori.MoriNormalFormTheorem` is a
  *consequence* of its conclusion (the corrected statement is not circular);
* `Work.Mori.isParabolic_of_diffeomorph` — parabolicity is a biholomorphic invariant.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.Mori

/-- **Holomorphic embeddability into `ℂ` transports along biholomorphisms.** -/
theorem hasHolomorphicEmbedding_of_diffeomorph {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X Y
      ((⊤ : ℕ∞) : WithTop ℕ∞))
    (h : HasHolomorphicEmbedding Y) : HasHolomorphicEmbedding X := by
  obtain ⟨φ, hφ, hinj⟩ := h
  refine ⟨fun x => φ (Φ x), ?_, fun x y hxy => Φ.injective (hinj hxy)⟩
  have hcomp := Work.Parabolic.holomorphicOnX_comp_biholomorph Φ (s := Set.univ) hφ
  simpa using hcomp

/-- **Every open subset of `ℂ` embeds holomorphically into `ℂ`** (the inclusion). -/
theorem hasHolomorphicEmbedding_opens (U : TopologicalSpace.Opens ℂ) :
    HasHolomorphicEmbedding ↥U :=
  ⟨fun z => (z : ℂ), by simpa using holomorphicOnX_opens_sub_const U 0,
    fun _ _ hxy => Subtype.ext hxy⟩

/-- **A surface in Mori normal form embeds holomorphically into `ℂ`.**  In particular the planarity
hypothesis of `Work.Mori.MoriNormalFormTheorem` follows from its conclusion, so the corrected
statement of that result is not circular. -/
theorem hasHolomorphicEmbedding_of_hasMoriNormalForm {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (h : HasMoriNormalForm X) : HasHolomorphicEmbedding X := by
  obtain ⟨U, -, ⟨Φ⟩⟩ := h
  exact hasHolomorphicEmbedding_of_diffeomorph Φ (hasHolomorphicEmbedding_opens U)

/-- **Parabolicity is invariant under biholomorphism.** -/
theorem isParabolic_of_diffeomorph {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X Y
      ((⊤ : ℕ∞) : WithTop ℕ∞))
    (h : Work.Parabolic.IsParabolic X) : Work.Parabolic.IsParabolic Y :=
  fun hY => h (Work.Parabolic.hasGreenFunction_of_diffeomorph Φ hY)

end Work.Mori
