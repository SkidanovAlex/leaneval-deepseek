import Mathlib
import Submission.Work.Drive.diskLiftHomotopy
import Submission.Work.Drive.projTimesLine

/-!
# The chain of the disk homotopy is `C^∞` into `ℝP³ × ℝ`

`Work.Drive.exists_diskClassHomotopy` produces a homotopy `H : ℝ × ℝ² → ℝP³` whose chain in the first
parameter is `C^∞` into `ℝP³` and which is invariant under the antipodal involution of the parameter
square on the whole seam.  The engine (`Work.Drive.Meet3Hyp`,
`Work.Drive.even_ncard_classCount_add_of_homotopy`) consumes the chains as maps into the `4`-manifold
`M = ℝP³ × ℝ` — the second coordinate being the fixed level `c₀` of the `(3,2,2)` encoding.

This file supplies the smoothness of the chain `x ↦ (H (x 2, (x 0, x 1)), c₀)`:

* `Work.Drive.contMDiff_chain_prodCharted` — for `ℝP³ × ℝ` with the **product** smooth structure
  (model `ℝ³ × ℝ`): the smoothness of the pair is the pair of smoothnesses
  (`ContMDiff.prodMk`), the `ℝP³`-component being exactly the hypothesis;
* `Work.Drive.contMDiff_chain_projTimesLine` — the same statement for the transported structure
  `Work.Drive.projTimesLineCharted` (model `ℝ⁴`), which is the structure the workspace uses for
  `ℝP³ × ℝ` (`Submission/Work/Drive/projTimesLine.lean`).  It is the model change along the *linear*
  homeomorphism `Work.Drive.psiLin`, i.e.
  `Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel'`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- The product smooth structure on `ℝP³ × ℝ` (model `ℝ³ × ℝ`), the one from which
`Work.Drive.projTimesLineCharted` is obtained by the linear model change `Work.Drive.psiLin`. -/
local instance instProdChartedPlaneLevel :
    ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) (Projectivization ℝ (Eucl 3) × ℝ) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  exact prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-- **The chain of the disk homotopy is `C^∞` into `ℝP³ × ℝ` with the product structure.** -/
theorem contMDiff_chain_prodCharted
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => (H (x 2, mk2 (x 0) (x 1)), c₀)) := by
  rw [modelWithCornersSelf_prod]
  exact hH.prodMk contMDiff_const

section ProjTimesLine

attribute [local instance] Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-- **The chain of the disk homotopy is `C^∞` into the `4`-manifold `ℝP³ × ℝ`** carrying the transported
structure `Work.Drive.projTimesLineCharted`; this is the `Meet3Hyp.smooth` input of the encoded chains
built from `Work.Drive.exists_diskClassHomotopy`. -/
theorem contMDiff_chain_projTimesLine
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (c₀ : ℝ)
    (hH : ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => (H (x 2, mk2 (x 0) (x 1)), c₀)) := by
  unfold Work.Drive.projTimesLineCharted
  exact fun x => (Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ) (I := 𝓡 3)
    (E := EuclideanSpace ℝ (Fin 3) × ℝ) (E' := EuclideanSpace ℝ (Fin 4))
    (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin.toHomeomorph psiLin.contDiff
    psiLin.symm.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun x : EuclideanSpace ℝ (Fin 3) => (H (x 2, mk2 (x 0) (x 1)), c₀)) Set.univ x).mpr
      (contMDiff_chain_prodCharted H c₀ hH x)

/-- **The `2`-chain of a plane presentation is `C^∞` into `ℝP³ × ℝ` with the product structure**: this
is the chain `x ↦ (A (x 0, x 1), x 2)` of `Work.Drive.encodedChains` (its blocks `1` and `2`), for a
`C^∞` class map `A` of the plane. -/
theorem contMDiff_chain_prodCharted_plane
    (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) A) :
    ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) × ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => (A (mk2 (x 0) (x 1)), x 2)) := by
  rw [modelWithCornersSelf_prod]
  refine ContMDiff.prodMk ?_ ?_
  · exact hA.comp (fun x => contMDiffAt_mk2_proj x)
  · exact coordCLM2.contDiff.contMDiff

/-- **The `2`-chain of a plane presentation is `C^∞` into the `4`-manifold `ℝP³ × ℝ`** carrying the
transported structure `Work.Drive.projTimesLineCharted`; with `Work.Drive.contMDiff_chain_projTimesLine`
for the homotopy chain this is the `Meet3Hyp.smooth` field of the three encoded chains. -/
theorem contMDiff_chain_projTimesLine_plane
    (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hA : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) A) :
    ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => (A (mk2 (x 0) (x 1)), x 2)) := by
  unfold Work.Drive.projTimesLineCharted
  exact fun x => (Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel' (𝕜 := ℝ) (I := 𝓡 3)
    (E := EuclideanSpace ℝ (Fin 3) × ℝ) (E' := EuclideanSpace ℝ (Fin 4))
    (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin.toHomeomorph psiLin.contDiff
    psiLin.symm.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun x : EuclideanSpace ℝ (Fin 3) => (A (mk2 (x 0) (x 1)), x 2)) Set.univ x).mpr
      (contMDiff_chain_prodCharted_plane A hA x)

end ProjTimesLine

end

end Work.Drive
