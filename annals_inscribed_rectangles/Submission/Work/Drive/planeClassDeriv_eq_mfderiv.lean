import Mathlib
import Submission.Work.Drive.meet3Generic_trans_clampedSweeps
import Submission.Work.Drive.clampedSweepCommonDir
import Submission.Work.Drive.meet3Generic_face_clampedSweeps

/-!
# The plane's class derivative is chart-free

`Work.Drive.planeClassDeriv c ψ P k x` is the derivative of `projChartMap i ∘ cls ∘ P k` at
`(x k 0, x k 1)`, where `i` is the **canonical** projective chart index at the class of the sweep
(`Work.Drive.projChartIndexOf`, so the choice is harmless).  This file proves that it is *literally*
the manifold derivative of the projective class of the plane,

> `planeClassDeriv c ψ P k x = mfderiv (𝓡 2) (𝓡 3) (y ↦ (cappingSpaceHomeoProj (P k y)).2) (x k 0, x k 1)`,

so that the two hypotheses `hc` (immersion) and `hV` (general position) of
`Work.Drive.meet3Generic_trans_clampedSweeps` — and therefore of the assembled parity identity
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes` — are **chart-free statements
about the plane presentation `P k`**.

The ingredient is the `ℝP³`-analogue of `Work.Drive.fderiv_chart_comp` (`Submission/Work/Drive/ChartBridge.lean`,
which is stated for a charted `4`-manifold): the derivative of the charted map is the manifold
derivative composed with the change-of-coordinates linear map, and at the *own* chart point that map is
the identity (`tangentCoordChange_self`).
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 1. The chart bridge in a charted `3`-manifold -/


/-! ## 1bis. The chart bridge in a charted manifold of any dimension

The `𝓡 m` case, which covers both the `4`-dimensional version of `Submission/Work/Drive/ChartBridge.lean`
and the `3`-dimensional version used for `ℝP³` below. -/

section ChartGen

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The chart bridge in a charted `m`-manifold**: the derivative of `chartAt p ∘ f` is the manifold
derivative of `f` composed with the change-of-coordinates map.  (A gap in Mathlib: the ingredients
`mfderiv_chartAt_eq_tangentCoordChange` and `mfderiv_comp` are both there, the combination is not.) -/
theorem mfderiv_chartAt_comp (f : EuclideanSpace ℝ (Fin n) → M)
    {s : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞) f s) (p : M)
    (hs : f s ∈ (chartAt (EuclideanSpace ℝ (Fin m)) p).source) :
    mfderiv (𝓡 n) (𝓡 m) (fun u => chartAt (EuclideanSpace ℝ (Fin m)) p (f u)) s =
      (tangentCoordChange (𝓡 m) (f s) p (f s)).comp (mfderiv (𝓡 n) (𝓡 m) f s) := by
  have hφ : MDifferentiableAt (𝓡 m) (𝓡 m) (chartAt (EuclideanSpace ℝ (Fin m)) p) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have hfs : MDifferentiableAt (𝓡 n) (𝓡 m) f s := hf.mdifferentiableAt (by simp)
  have hmain := mfderiv_comp s hφ hfs
  rw [mfderiv_chartAt_eq_tangentCoordChange hs] at hmain
  exact hmain

/-- The same, for the Fréchet derivative. -/
theorem fderiv_chartAt_comp (f : EuclideanSpace ℝ (Fin n) → M)
    {s : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞) f s) (p : M)
    (hs : f s ∈ (chartAt (EuclideanSpace ℝ (Fin m)) p).source) :
    fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin m)) p (f u)) s =
      (tangentCoordChange (𝓡 m) (f s) p (f s)).comp (mfderiv (𝓡 n) (𝓡 m) f s) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_chartAt_comp f hf p hs


end ChartGen



section Chart3

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The derivative of the chart-composition `φ ∘ f`** for a chart of a charted `3`-manifold, in
terms of `mfderiv f` and the change-of-coordinates map (the `𝓡 3` analogue of
`Work.Drive.mfderiv_chart_comp`). -/
theorem mfderiv_chart_comp3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → M)
    {s : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) f s) (p : M)
    (hs : f s ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) p).source) :
    mfderiv (𝓡 n) (𝓡 3) (fun u => chartAt (EuclideanSpace ℝ (Fin 3)) p (f u)) s =
      (tangentCoordChange (𝓡 3) (f s) p (f s)).comp (mfderiv (𝓡 n) (𝓡 3) f s) := by
  have hφ : MDifferentiableAt (𝓡 3) (𝓡 3) (chartAt (EuclideanSpace ℝ (Fin 3)) p) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have hfs : MDifferentiableAt (𝓡 n) (𝓡 3) f s := hf.mdifferentiableAt (by simp)
  have hmain := mfderiv_comp s hφ hfs
  rw [mfderiv_chartAt_eq_tangentCoordChange hs] at hmain
  exact hmain

/-- The same, for the Fréchet derivative (the source is a vector space). -/
theorem fderiv_chart_comp3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → M)
    {s : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) f s) (p : M)
    (hs : f s ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) p).source) :
    fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 3)) p (f u)) s =
      (tangentCoordChange (𝓡 3) (f s) p (f s)).comp (mfderiv (𝓡 n) (𝓡 3) f s) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_chart_comp3 f hf p hs

end Chart3

/-! ## 2. The concrete form in `ℝP³` -/

section Proj3

attribute [local instance] Work.Drive.projCharted

/-- **The derivative of `projChartMap i ∘ g` is `mfderiv g`** when `i` is the chart index at the value
`g z` (so that `projChartMap i` is the preferred chart there and the change of coordinates is the
identity). -/
theorem fderiv_projChartMap_of_chartAt_eq {k : ℕ}
    (g : EuclideanSpace ℝ (Fin k) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (z : EuclideanSpace ℝ (Fin k))
    (hg : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) g z) (i : Fin 4)
    (hchart : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        (Work.Drive.projCharted 3) (g z) :
        OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
          (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart i) :
    fderiv ℝ (fun y => Work.Drive.projChartMap i (g y)) z =
      mfderiv (𝓡 k) (𝓡 3) g z := by
  haveI : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := Work.Drive.isManifold_projCharted 3
  have hs : g z ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) (g z)).source := mem_chart_source _ _
  have h1 := fderiv_chart_comp3 g hg (g z) hs
  have h3 : (fun y => Work.Drive.projChartMap i (g y)) =
      fun y => chartAt (EuclideanSpace ℝ (Fin 3)) (g z) (g y) := by
    funext y
    simp only [hchart, Work.Drive.projChart_apply]
  rw [h3, h1]
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply]
  exact tangentCoordChange_self (I := 𝓡 3) (x := g z) (z := g z) (v := (mfderiv (𝓡 k) (𝓡 3) g z) v)
    (mem_extChartAt_source (g z))


end Proj3

/-! ## 3. The plane's class derivative is chart-free -/

section Plane

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The class derivative of a plane is its manifold derivative.**  `Work.Drive.planeClassDeriv` is
the derivative of the charted class map in the *canonical* chart of the class of the sweep; since the
class of the sweep is the class of the plane, that chart is the preferred chart at the value, and the
change of coordinates is the identity.

Consequently the hypotheses `hc` (immutability) and `hV` (general position) of
`Work.Drive.meet3Generic_trans_clampedSweeps`, hence of the assembled identity
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes`, are statements about the
*plane presentation* `P k` alone, with no reference to a chart. -/
theorem planeClassDeriv_eq_mfderiv
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    Work.Drive.planeClassDeriv c ψ P k x
      = mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
          (Work.Drive.cappingSpaceHomeoProj (P k y)).2) (Work.Drive.mk2 (x k 0) (x k 1)) := by
  haveI : IsManifold (𝓡 3) Work.Drive.Ctop
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := Work.Drive.isManifold_projCharted 3
  have hcls : ContMDiffAt (𝓡 2) (𝓡 3) Work.Drive.Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => (Work.Drive.cappingSpaceHomeoProj (P k y)).2)
      (Work.Drive.mk2 (x k 0) (x k 1)) := by
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
      Work.Drive.halfLineProjectiveCharted
    have hG : ContMDiffAt (𝓡 2) (𝓡 4) Work.Drive.Ctop
        (fun w => Work.Drive.cappingSpaceHomeoProj (P k w))
        (Work.Drive.mk2 (x k 0) (x k 1)) := by
      have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
        (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (E' := EuclideanSpace ℝ (Fin 2)) (H' := EuclideanSpace ℝ (Fin 2)) (𝓡 2)
        (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
        (M' := Work.Drive.CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
        Work.Drive.cappingSpaceHomeoProj.symm (P k) Set.univ (Work.Drive.mk2 (x k 0) (x k 1))
      exact hiff.mp ((hP k).contMDiffAt)
    exact ((Work.Drive.contMDiffAt_halfLineProjective_iff
      (fun w => Work.Drive.cappingSpaceHomeoProj (P k w))
      (Work.Drive.mk2 (x k 0) (x k 1))).mp hG).2
  have hclsEq : (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2
      = (Work.Drive.cappingSpaceHomeoProj (P k (Work.Drive.mk2 (x k 0) (x k 1)))).2 :=
    Work.Drive.cappingSpaceHomeoProj_clampedSweep_snd (c k) ψ (P k) (x k)
  have hchart : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
      (Work.Drive.projCharted 3)
      (Work.Drive.cappingSpaceHomeoProj (P k (Work.Drive.mk2 (x k 0) (x k 1)))).2 :
      OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
        (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart (Work.Drive.projChartIndexOf ((Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2)) := by
    rw [← hclsEq]
    exact Work.Drive.projCharted_chartAt_eq_projChart _
  exact fderiv_projChartMap_of_chartAt_eq
    (fun y : EuclideanSpace ℝ (Fin 2) => (Work.Drive.cappingSpaceHomeoProj (P k y)).2)
    (Work.Drive.mk2 (x k 0) (x k 1)) hcls _ hchart

/-- **The immersion condition `hc` is intrinsic.** -/
theorem planeClassDeriv_injective_iff
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    Function.Injective (Work.Drive.planeClassDeriv c ψ P k x)
      ↔ Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
          (Work.Drive.cappingSpaceHomeoProj (P k y)).2) (Work.Drive.mk2 (x k 0) (x k 1))) := by
  rw [planeClassDeriv_eq_mfderiv c ψ P hP k x]
  rfl

/-- **The general-position condition `hV` is intrinsic.** -/
theorem planeClassDeriv_range_generalPosition_iff
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    ((Work.Drive.planeClassDeriv c ψ P 0 x).range
        ⊓ (Work.Drive.planeClassDeriv c ψ P 1 x).range
        ⊓ (Work.Drive.planeClassDeriv c ψ P 2 x).range = ⊥)
      ↔ ((mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Work.Drive.cappingSpaceHomeoProj (P 0 y)).2) (Work.Drive.mk2 (x 0 0) (x 0 1))).range
          ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Work.Drive.cappingSpaceHomeoProj (P 1 y)).2) (Work.Drive.mk2 (x 1 0) (x 1 1))).range
          ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Work.Drive.cappingSpaceHomeoProj (P 2 y)).2) (Work.Drive.mk2 (x 2 0) (x 2 1))).range
        = ⊥) := by
  rw [planeClassDeriv_eq_mfderiv c ψ P hP 0 x, planeClassDeriv_eq_mfderiv c ψ P hP 1 x,
    planeClassDeriv_eq_mfderiv c ψ P hP 2 x]

/-- **The parity identity `Σ_k top_k ≡ Σ_k bottom_k` for three radial sweeps, with intrinsic
hypotheses.**  This is `Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes` with the
*chart-dependent* conditions `hc` (injectivity of `Work.Drive.planeClassDeriv`) and `hV` (general
position of its three ranges) replaced, via
`Work.Drive.planeClassDeriv_injective_iff` and
`Work.Drive.planeClassDeriv_range_generalPosition_iff`, by the corresponding statements about the
manifold derivative of the projective class of the plane presentation.  These are the forms in which
the geometric input of the route (`GENERICITY_ASSEMBLY_STATUS.md` §5) has to be supplied.

The two plane conditions are required only at triple points whose **class coordinates** are in the open
square: `Work.Drive.class_coords_mem_Ioo_of_hface` shows that `hface` puts every class coordinate of a
triple point strictly inside the cube, so this is no restriction at all.  It matters for the concrete
presentations: a *folded* presentation of the plane such as `Work.Drive.diskPlane` is an immersion
exactly on the open square (its fold `foldFun x = (1 - cos (π x))/2` has vanishing derivative at the
integers), so `hc`/`hV` are exactly the statements the geometry can supply there. -/
theorem even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (ha : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, deriv ψ (x k 2) * (Real.log (c k) - Real.log
          (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hc : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        (∀ k, x k 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ x k 1 ∈ Set.Ioo (0 : ℝ) 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, Function.Injective (mfderiv (𝓡 2) (𝓡 3)
          (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Work.Drive.cappingSpaceHomeoProj (P k y)).2)
          (Work.Drive.mk2 (x k 0) (x k 1))))
    (hV : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        (∀ k, x k 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ x k 1 ∈ Set.Ioo (0 : ℝ) 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Work.Drive.cappingSpaceHomeoProj (P 0 y)).2)
            (Work.Drive.mk2 (x 0 0) (x 0 1))).range
          ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Work.Drive.cappingSpaceHomeoProj (P 1 y)).2)
            (Work.Drive.mk2 (x 1 0) (x 1 1))).range
          ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
            (Work.Drive.cappingSpaceHomeoProj (P 2 y)).2)
            (Work.Drive.mk2 (x 2 0) (x 2 1))).range = ⊥)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
        ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
          (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)) :
    Even (((topBdryMeet CappingSpace
          (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 0).ncard
        + (bottomBdryMeet CappingSpace
          (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 0).ncard)
      + ((topBdryMeet CappingSpace
          (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 1).ncard
        + (bottomBdryMeet CappingSpace
          (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 1).ncard)
      + ((topBdryMeet CappingSpace
          (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 2).ncard
        + (bottomBdryMeet CappingSpace
          (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 2).ncard)) := by
  have hinterior : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
        = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
        = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
      (∀ k, x k 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ x k 1 ∈ Set.Ioo (0 : ℝ) 1) := by
    intro x hx h1 h2 k
    exact ⟨Work.Drive.class_coords_mem_Ioo_of_hface c ψ P hface x hx h1 h2 k 0 (by decide),
      Work.Drive.class_coords_mem_Ioo_of_hface c ψ P hface x hx h1 h2 k 1 (by decide)⟩
  exact Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes P c ψ hψ hP hPseam ha
    (fun x hx h1 h2 k =>
      (Work.Drive.planeClassDeriv_injective_iff c ψ P hP k x).mpr
        (hc x hx (hinterior x hx h1 h2) h1 h2 k))
    (fun x hx h1 h2 =>
      (Work.Drive.planeClassDeriv_range_generalPosition_iff c ψ P hP x).mpr
        (hV x hx (hinterior x hx h1 h2) h1 h2))
    hface

end Plane

end

end Work.Drive
