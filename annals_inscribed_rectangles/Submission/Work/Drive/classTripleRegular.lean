import Mathlib
import Submission.Work.Drive.planeClassDeriv_eq_mfderiv
import Submission.Work.Drive.meet3Generic_face_clampedSweeps
import Submission.Work.Drive.ha_clampedSweeps
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.hcLinCappingManifold

/-!
# `ClassTripleRegular`: the design's regularity of a triple of plane presentations (L5's target)

This file fixes **the definition the genericity design must produce** (the lead's `L5`,
`exists_small_classTripleRegular`) and **the consumer** (the lead's `L4`,
`meet3Hyp_of_classTripleRegular`): the plane-local hypotheses under which the counting engine
(`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet`,
`Work.Drive.manifold_triple_inter_boundary_parity`) applies to the three **radial sweeps**
`k ↦ clampedSweep (c k) ψ (P k)`.

## What the definition contains, and what it does *not*

`ClassTripleRegular P` is a predicate of the **three plane presentations alone** (no levels, no cutoff),
because that is the shape in which `L5` must produce it:
`∀ ε > 0, ∃ A, ClassTripleRegular (linCapping (A k) ∘ P k)`.  Its four fields are

* `hP` — each presentation is `C^∞` (`Work.Drive.contMDiff_clampedSweep` consumes it);
* `hPseam` — each presentation is invariant under the seam involution (`clampedSweep_seamInv`);
* `hci` — the **immersion** condition: the class map `y ↦ class (P k y)` is an immersion on the open
  square (the engine's `hc`, in the intrinsic `mfderiv` form of `planeClassDeriv_injective_iff`);
* `hV` — the **general position** condition: the three class-derivative `2`-planes are in general
  position on the open square (the engine's `hV`, in the intrinsic form of
  `planeClassDeriv_range_generalPosition_iff`).

Two remarks on the *restrictions* chosen here.

* The conditions are required **only on the open square**.  This is not cosmetic: for the folded disk
  presentation `diskPlane Q = Q ∘ sqDisk ∘ foldBox` the class derivative degenerates on the seam, so the
  unrestricted form of `hci` is *false* (`GENERICITY_ASSEMBLY_STATUS.md` §8).
* The conditions are phrased at the *class* points `mk2 (y k 0) (y k 1)`, because at a triple point of
  the three sweeps all class coordinates are interior (`class_coords_mem_Ioo_of_hface`), so the engine's
  pointwise `hc`/`hV` at triple points are recovered from the open-square versions.

**Not** in the definition: the levels `c k`, the cutoff `ψ`, the level bound `c 0 < levelOf (P k y)`, the
face condition, and the collision data (`q`, `hy`, `huniq`, `hyint`, `hrne`).  Those are *design
parameters* (or consequences of the collision data), not regularity of the triple of planes: they are
hypotheses of the assembly lemmas below, and `hface_clampedSweeps_local` (`hlev` + collision data →
face condition) and `ha_clampedSweeps` (`hψ'`, `hcpos`, `hck`, `hlev` → `ha`) are the proved providers.

## The assembly (`L4`)

Given `ClassTripleRegular P`, the cutoff data `ψ` (`C^∞`, `ψ 0 = 1`, `ψ 1 = 0`, `[0,1]`-valued on
`[0,1]`, `deriv ψ ≠ 0` there), the level data `c` (`0 < c k`, `c k ≤ c 0`) and the level bound
`c 0 < levelOf (P k y)`, and — only for the *face* field — the face condition itself, the three sweeps
satisfy `Meet3Generic` (`meet3Generic_of_classTripleRegular`) and hence `Meet3Hyp`
(`meet3Hyp_of_classTripleRegular`), which is exactly the `hyp` field of the three structures
`ChainAntisymmetry`/`ChainFunctional`/`ChainLocality` of `Submission/Work/Drive/ChainInterface.lean`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The class map of a plane presentation**: the second coordinate of the capping model, i.e.
`y ↦ [P y]` in `ℝP³ ≅ (0,∞) × ℝP³`. -/
def planeClassMap (Q : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
  fun y => (cappingSpaceHomeoProj (Q y)).2

/-- **The open unit square** of plane parameters: the set on which the disk presentations of the planes
are immersions. -/
def openSquare (y : EuclideanSpace ℝ (Fin 2)) : Prop :=
  y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ y 1 ∈ Set.Ioo (0 : ℝ) 1

/-- **The three plane parameters have a common class**: the condition under which the engine's
`hc`/`hV` are required.  At a triple point of the three radial sweeps the three classes coincide
automatically (`Work.Drive.cls_clampedSweep`), so this is exactly the restriction that the triple-point
set imposes, and no more. -/
def CommonClass (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ k, planeClassMap (P k) (y k) = planeClassMap (P 0) (y 0)

/-- **The design's regularity of a triple of plane presentations** (the lead's `L5` target, consumed by
`L4`).  It bundles the four plane-local hypotheses of the counting engine: smoothness, seam invariance,
and — at every triple of parameters lying in the open square whose **classes coincide** — the
immersion of each class map (`hci`) and the general position of the three class `2`-planes (`hV`).

The restriction to *coincident* classes is essential, not cosmetic: the engine needs `hc`/`hV` only at
triple points of the three sweeps, and there the classes coincide.  Requiring `hV` at *all* triples of
parameters would be **unsatisfiable** (three nearby parameters give three nearly equal `2`-planes, whose
triple intersection is a line, not `⊥`). -/
structure ClassTripleRegular (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop where
  /-- each presentation is `C^∞` -/
  hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Ctop (P k)
  /-- each presentation is invariant under the seam involution -/
  hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y)
  /-- **immersion**: at every triple of parameters in the open square the class map of each plane is an
  immersion there.  (No common-class restriction: the immersion is an *open* condition of the plane
  presentation, it holds for the folded disk presentation everywhere on the open square, and it survives
  the class perturbation `linCapping` — see `hci_linCapping_of_classTripleRegular`.) -/
  hci : ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ k, openSquare (y k)) → ∀ k,
    Function.Injective
      (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P k)) (mk2 (y k 0) (y k 1)))
  /-- **general position**: at every triple of parameters in the open square with a common class, the
  three class-derivative `2`-planes are in general position -/
  hV : ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ k, openSquare (y k)) → CommonClass P y →
    (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P 0)) (mk2 (y 0 0) (y 0 1))).range
      ⊓ (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P 1)) (mk2 (y 1 0) (y 1 1))).range
      ⊓ (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P 2)) (mk2 (y 2 0) (y 2 1))).range = ⊥

/-- The open square in the `Ioo`-coordinate form used by the engine's `hc`/`hV` consumers. -/
lemma openSquare_iff {y : EuclideanSpace ℝ (Fin 2)} :
    openSquare y ↔ y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ y 1 ∈ Set.Ioo (0 : ℝ) 1 := Iff.rfl

/-- The class coordinates of a triple point of the three sweeps have a common class: the clamped sweep
does not change the projective class (`Work.Drive.cls_clampedSweep`). -/
lemma commonClass_of_sweep_eq
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (h01 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1))
    (h02 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2)) :
    CommonClass P (fun k => mk2 (x k 0) (x k 1)) := by
  intro k
  have hk : ((cappingSpaceHomeoProj (clampedSweep (c k) ψ (P k) (x k))).2)
      = ((cappingSpaceHomeoProj (clampedSweep (c 0) ψ (P 0) (x 0))).2) := by
    fin_cases k
    · rfl
    · simpa using congrArg (fun p => (cappingSpaceHomeoProj p).2) h01.symm
    · simpa using congrArg (fun p => (cappingSpaceHomeoProj p).2) h02.symm
  simpa only [planeClassMap, cls_clampedSweep] using hk

/-- **The engine's pointwise `hc` from `ClassTripleRegular` at a triple point of the sweeps.**  Only the
interiority of the class coordinates (a consequence of the face condition,
`Work.Drive.class_coords_mem_Ioo_of_hface`) and the class coincidence (free at triple points) are used. -/
theorem planeClassDeriv_injective_of_classTripleRegular
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hreg : ClassTripleRegular P) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hint : ∀ k : Fin 3, ∀ i : Fin 3, i ≠ 2 → x k i ∈ Set.Ioo (0 : ℝ) 1)
    (k : Fin 3) :
    Function.Injective (planeClassDeriv c ψ P k x) := by
  rw [planeClassDeriv_injective_iff c ψ P hreg.hP k x]
  exact hreg.hci (fun j => mk2 (x j 0) (x j 1))
    (fun j => ⟨by simpa using hint j 0 (by decide), by simpa using hint j 1 (by decide)⟩) k

/-- **The engine's pointwise general position from `ClassTripleRegular`.** -/
theorem planeClassDeriv_range_generalPosition_of_classTripleRegular
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hreg : ClassTripleRegular P) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hint : ∀ k : Fin 3, ∀ i : Fin 3, i ≠ 2 → x k i ∈ Set.Ioo (0 : ℝ) 1)
    (hcc : CommonClass P (fun k => mk2 (x k 0) (x k 1))) :
    (planeClassDeriv c ψ P 0 x).range ⊓ (planeClassDeriv c ψ P 1 x).range
      ⊓ (planeClassDeriv c ψ P 2 x).range = ⊥ := by
  rw [planeClassDeriv_range_generalPosition_iff c ψ P hreg.hP x]
  exact hreg.hV (fun j => mk2 (x j 0) (x j 1))
    (fun j => ⟨by simpa using hint j 0 (by decide), by simpa using hint j 1 (by decide)⟩) hcc


/-! ## The assembly: `ClassTripleRegular` + the design data `⟹ Meet3Generic` / `Meet3Hyp` (L4) -/

/-- **The face condition of the engine, in the form in which the collision data provide it.**  This is
exactly the hypothesis of `Work.Drive.meet3Generic_face_clampedSweeps`; its proved provider from the
collision data (`q`, `hy`, `huniq`, `hyint`, `hrne`) is `Work.Drive.hface_clampedSweeps_local`. -/
def FaceCondition (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) : Prop :=
  ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
    (∀ k, x k ∈ Submission.Drive.unitBox 2) →
    clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
    clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
    (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
    ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
      (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)

/-- **L4, at the level of `Meet3Generic`.**  A `ClassTripleRegular` triple of plane presentations,
together with the cutoff and level data of the design (`ψ` smooth with `ψ 0 = 1`, `ψ 1 = 0` and
non-vanishing derivative on `[0,1]`; the levels `c` positive with `c k ≤ c 0`; the level bound
`c 0 < levelOf (P k y)`) and the face condition of the collision data, gives the engine's genericity
`Meet3Generic` for the three radial sweeps. -/
theorem meet3Generic_of_classTripleRegular
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hreg : ClassTripleRegular P)
    (hψ : ContDiff ℝ Ctop ψ)
    (hψ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hface : FaceCondition P c ψ) :
    Meet3Generic CappingSpace (fun k => clampedSweep (c k) ψ (P k)) :=
  meet3Generic_clampedSweeps c ψ P hψ hreg.hP
    (ha_clampedSweeps P c ψ hcpos hck hψ' hlev)
    (fun x hbox h01 h02 k =>
      planeClassDeriv_injective_of_classTripleRegular hreg c ψ x
        (fun k i hi => class_coords_mem_Ioo_of_hface c ψ P hface x hbox h01 h02 k i hi) k)
    (fun x hbox h01 h02 =>
      planeClassDeriv_range_generalPosition_of_classTripleRegular hreg c ψ x
        (fun k i hi => class_coords_mem_Ioo_of_hface c ψ P hface x hbox h01 h02 k i hi)
        (commonClass_of_sweep_eq P c ψ x h01 h02))
    hface

/-- **L4: `ClassTripleRegular` and the design data give the engine's `Meet3Hyp`.**  This is the `hyp`
field of the three structures `ChainAntisymmetry`/`ChainFunctional`/`ChainLocality` for the design's
chains `k ↦ clampedSweep (c k) ψ (P k)`. -/
theorem meet3Hyp_of_classTripleRegular
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hreg : ClassTripleRegular P)
    (hψ : ContDiff ℝ Ctop ψ)
    (hψ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hface : FaceCondition P c ψ) :
    Meet3Hyp CappingSpace (fun k => clampedSweep (c k) ψ (P k)) :=
  meet3Hyp_clampedSweeps P c ψ hψ hreg.hP hreg.hPseam
    (meet3Generic_of_classTripleRegular P c ψ hreg hψ hψ' hcpos hck hlev hface)

/-- The same, together with the seam/slice separation (`Work.Drive.not_seam_and_slice_of_generic`) that
the parity engine consumes as `hdisj`. -/
theorem meet3Hyp_and_separation_of_classTripleRegular
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hreg : ClassTripleRegular P)
    (hψ : ContDiff ℝ Ctop ψ)
    (hψ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hface : FaceCondition P c ψ) :
    Meet3Hyp CappingSpace (fun k => clampedSweep (c k) ψ (P k)) ∧
      (∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
        x ∈ tripleBdryMeet CappingSpace (fun j => clampedSweep (c j) ψ (P j)) k →
        ¬ (onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1))) :=
  ⟨meet3Hyp_of_classTripleRegular P c ψ hreg hψ hψ' hcpos hck hlev hface,
    fun k x hx =>
      not_seam_and_slice_of_generic _ (meet3Generic_of_classTripleRegular P c ψ hreg hψ hψ' hcpos
        hck hlev hface) k x hx⟩


/-! ## The transport of the *immersion* half under a class perturbation (the `L5`-facing companion)

`ClassTripleRegular.hV` is *not* preserved by independent class perturbations — it is the condition the
design's genericity argument has to produce (see `Work.Drive.hV_projMap_perChain_iff`).  `hci` however
**is** preserved, because the perturbation acts by a diffeomorphism of `ℝP³`:

* `Work.Drive.cls_linCapping_eq` — `classMap (linCapping A ∘ Q) = Projectivization.map A ∘ classMap Q`;
* `Work.Drive.injective_mfderiv_cls_linCapping` — injectivity of the manifold derivative transfers.

So `L5` only has to produce the *existence* of a perturbation satisfying `hci` (free, below) and `hV`
(the genericity statement), plus the seam invariance and smoothness of the perturbed presentations
(`linCapping` is a homeomorphism of the capping space and `ContMDiff` — `Work.Drive.contMDiff_linCapping`).
-/

/-- **The immersion half of `ClassTripleRegular` transports to any class perturbation.** -/
theorem hci_linCapping_of_classTripleRegular
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace} (hreg : ClassTripleRegular P)
    (A : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) :
    ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ k, openSquare (y k)) → ∀ k,
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (fun y' => linCapping (A k) (P k y')))
          (mk2 (y k 0) (y k 1))) := by
  intro y hy k
  have hmd : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (P k y')).2) (mk2 (y k 0) (y k 1)) :=
    mdifferentiableAt_cls_of_contMDiff (hreg.hP k) _
  exact injective_mfderiv_cls_linCapping (A k) (P k) (mk2 (y k 0) (y k 1)) hmd
    (hreg.hci y hy k)

end

end Work.Drive
