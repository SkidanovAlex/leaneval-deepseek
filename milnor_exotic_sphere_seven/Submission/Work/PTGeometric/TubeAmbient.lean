import Submission.Work.PTGeometric.contMDiff_normalProjCLM

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the ambient coordinates of the collapse of a tube chart, and their smoothness

The Pontryagin–Thom construction consumes the collapse map of a tubular neighbourhood in **ambient
coordinates**: the pair `(P, v)` of

* `P y` — the orthogonal projection of the ambient space `ℝ^{8+k}` onto the **normal space** at the
  foot of `y` (the plane of the Gauss map), and
* `v y = normalCoord E C y` — the normal coordinate (the vector of the plane),

with `P y (v y) = v y`, `v` vanishing exactly on the embedded manifold, and — the content of this
file — **both `C^∞` on the open tube**.

TUBULAR has the smoothness of `v` (`Work.Tubular.contMDiffOn_normalCoord`) and the zero-set theorem
(`Work.Tubular.normalCoord_eq_zero_iff`), but only the *continuity* of the Gauss plane field
(`Work.Tubular.continuousOn_orthFrame` / the Gauss map of `Work.ThomBordism.gaussMapGrassmann`).
The missing smoothness of `P` is `Work.PTGeometric.contMDiff_normalProjCLM` (the projection onto the
normal space of a smooth embedding is smooth), and this file composes it with the (smooth) foot map
of the tube chart.  This is the input that G2
(`Work.PTGeometric.smoothMap_into_tautTotal_eqOn`) needs in order to be applied with the collapse end
as prescribed set `S`: the ambient data of the collapse are `C^∞` near the core.

## Main results

* `Work.PTGeometric.tubeFoot`, `Work.PTGeometric.tubeNormalProj`
* `Work.PTGeometric.contMDiffOn_tubeNormalProj` / `_tubeNormalCoord`
* `Work.PTGeometric.tubeNormalProj_fixes`
* `Work.PTGeometric.tube_ambient_data`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

variable {V : Work.ThomBordism.Man8} {k : ℕ} {N : ℕ}

/-- **The foot of a point of the tube**: the point of the embedded manifold of which it is the
normal translate. -/
def tubeFoot (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (y : Work.Tubular.Euc (8 + k)) : V.pt := (C.inv y).1.1

/-- **The ambient projection of the tube chart**: the orthogonal projection of `ℝ^{8+k}` onto the
normal space at the foot of `y` (the plane of the Gauss map, as an endomorphism of the ambient
space). -/
def tubeNormalProj (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (y : Work.Tubular.Euc (8 + k)) :
    Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k) :=
  ((Work.Tubular.normalSpace E (tubeFoot E C y)).subtypeL).comp
    ((Work.Tubular.normalSpace E (tubeFoot E C y)).orthogonalProjectionOnto)

/-- **The normal coordinate of the tube chart**, as the vector part of the ambient data. -/
def tubeNormalCoord (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (y : Work.Tubular.Euc (8 + k)) :
    Work.Tubular.Euc (8 + k) :=
  Work.Tubular.normalCoord E C y

/-- The foot map is `C^∞` on the open tube (it is the first component of `C.inv`). -/
theorem contMDiffOn_tubeFoot (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Work.Tubular.Euc (8 + k)) (𝓡 8)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeFoot E C) C.openTube :=
  (contMDiff_fst (I := 𝓡 8) (J := 𝓘(ℝ, Work.Tubular.Euc (8 + k)))).comp_contMDiffOn
    C.contMDiffOn_inv

/-- **The ambient projection of the tube chart is `C^∞` on the open tube.** -/
theorem contMDiffOn_tubeNormalProj (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Work.Tubular.Euc (8 + k))
      (𝓘(ℝ, Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeNormalProj E C) C.openTube :=
  fun y hy => ContMDiffAt.comp_contMDiffWithinAt (f := tubeFoot E C) y
    ((contMDiff_normalProjCLM E).contMDiffAt) (contMDiffOn_tubeFoot E C y hy)

/-- **The normal coordinate is `C^∞` on the open tube** (TUBULAR). -/
theorem contMDiffOn_tubeNormalCoord (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Work.Tubular.Euc (8 + k)) 𝓘(ℝ, Work.Tubular.Euc (8 + k))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeNormalCoord E C) C.openTube :=
  Work.Tubular.contMDiffOn_normalCoord E C

/-- **The projection fixes the normal coordinate**: `P y (v y) = v y` on the open tube. -/
theorem tubeNormalProj_fixes (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) {y : Work.Tubular.Euc (8 + k)}
    (hy : y ∈ C.openTube) :
    tubeNormalProj E C y (tubeNormalCoord E C y) = tubeNormalCoord E C y := by
  show ((Work.Tubular.normalSpace E (tubeFoot E C y)).subtypeL)
      ((Work.Tubular.normalSpace E (tubeFoot E C y)).orthogonalProjectionOnto
        ((C.inv y).1.2)) = (C.inv y).1.2
  have hmem : (C.inv y).1.2 ∈ Work.Tubular.normalSpace E (tubeFoot E C y) := (C.inv y).2
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨(C.inv y).1.2, hmem⟩]
  rfl

/-- **The normal coordinate vanishes exactly on the embedded manifold.** -/
theorem tubeNormalCoord_eq_zero_iff (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) {y : Work.Tubular.Euc (8 + k)}
    (hy : y ∈ C.openTube) :
    tubeNormalCoord E C y = 0 ↔ y ∈ Set.range E.e :=
  Work.Tubular.normalCoord_eq_zero_iff E C hy

/-- **The ambient data of the collapse of a tube chart.**  On the open tube there are a `C^∞`
projection-valued map `P` and a `C^∞` vector field `v` with `P y (v y) = v y`, whose zero set is
exactly the embedded manifold.  This is the "collapse end" input of the last mile (the ambient
coordinates of the collapse map near the core, in the sense of
`Work.PTGeometric.AmbientCollapseEnd.smooth_near_S` and of G2). -/
theorem tube_ambient_data (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    ContMDiffOn 𝓘(ℝ, Work.Tubular.Euc (8 + k))
      (𝓘(ℝ, Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeNormalProj E C) C.openTube ∧
    ContMDiffOn 𝓘(ℝ, Work.Tubular.Euc (8 + k)) 𝓘(ℝ, Work.Tubular.Euc (8 + k))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeNormalCoord E C) C.openTube ∧
    (∀ y ∈ C.openTube, tubeNormalProj E C y (tubeNormalCoord E C y) = tubeNormalCoord E C y) ∧
    (∀ y ∈ C.openTube, tubeNormalCoord E C y = 0 ↔ y ∈ Set.range E.e) :=
  ⟨contMDiffOn_tubeNormalProj E C, contMDiffOn_tubeNormalCoord E C,
    fun y hy => tubeNormalProj_fixes E C hy, fun y hy => tubeNormalCoord_eq_zero_iff E C hy⟩

end

end Work.PTGeometric
