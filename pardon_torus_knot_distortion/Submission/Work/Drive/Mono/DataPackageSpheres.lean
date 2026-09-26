import Mathlib
import Submission.Work.Drive.Mono.DataPackage
import Submission.Work.Drive.Mono.exists_levelFrontierGen

/-!
# The data package from the genericity of the level frontier

`Work.Drive.Mono.DataPackage` bundles, at one datum, everything the analysis of the sweep's levels
needs: the tilt data, the corrected stratified genericity `JunctionGenC`, the face regularity, the
cutting condition, the slicing of the box sphere, the disjoint-sphere decomposition of the level
frontier and the level count.

The only one of these which is *not* an assumption in this module is the disjoint-sphere
decomposition: it is derived from the explicit genericity `Work.Drive.Mono.LevelFrontierGen` and the
(proved) brick `Work.Drive.Mono.tiltedLevel_disjoint_spheres`, via
`Work.Drive.Mono.levelSphereDecomposition_of_levelFrontierGen`.  So a producer of the package needs
only the *genericity* of the level frontier — and `Work.Drive.Mono.exists_levelFrontierGen` shows
that this genericity can always be arranged by enlarging `exc` by a finite set of levels inside the
window (the `ℓ`-values of the box edges in the directions in which `ℓ` vanishes, the `ℓ`-values of
the vertices, and the three seam values).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- **The data package from the genericity of the level frontier.**  The disjoint-sphere
decomposition of the level frontier (`DataPackage.spheres`) is produced from `LevelFrontierGen` and
the proved brick. -/
theorem dataPackage_of_levelFrontierGen {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hcut : SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hgen : LevelFrontierGen s c σ u v h ℓ exc lam0 lam1)
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hface : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ pp = z ∧
        fderiv ℝ (fun qq : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ qq)) pp ≠ 0)
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hcount : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q :=
  { tilt := hT
    junc := hJ
    faceReg := hface
    slabCuts := hcut
    slicing := hslice
    spheres := levelSphereDecomposition_of_levelFrontierGen hs hT hcut hgen
    count := hcount }

end

end Work.Drive.Mono
