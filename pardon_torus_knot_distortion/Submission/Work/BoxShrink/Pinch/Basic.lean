import Submission.Work.BoxShrink.Bubble.Smooth
import Submission.Work.Smooth.Plane.All
import Submission.Work.Smooth.Morse.Regular
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous

/-!
# The pinch: the parameter-plane dictionary

This is the first module of the chapter `Work.BoxShrink.Pinch`, whose object is Pardon's
**pinch**: the one-parameter family of spheres which starts at the boundary sphere `∂PBox s c σ`
of Pardon's box and ends at the two halves of the box cut by the plane
`{y (σ 2) = c (σ 2) + u}`, pinching along the flat disc `cutDisc s c σ u` (Pardon, *On the
distortion of knots on embedded surfaces*, Lemma `doublebubble`).

The chapter works with the **smooth tori of the challenge**,
`F = ψ(F_standard)`, `ψ : Submission.Diffeo`, and records everything in the parameter plane
`ℝ × ℝ` of the parametrisation

  `par ψ : ℝ × ℝ → ℝ³`,  `par ψ (x, y) = ψ (torusMap x y)`.

The two basic functions are

* `boxB ψ c σ = Submission.boxNorm c σ ∘ par ψ` — the box norm;
* `planeG ψ c σ u = planeCoord c σ u ∘ par ψ` — the signed distance to the cutting plane.

The dictionary proved here is the one the plan of the chapter uses:

* `par ⁻¹' PBox s c σ = {p | boxB ψ c σ p < s}` (`preimage_PBox`);
* `par ⁻¹' sphereSet c σ s = {p | boxB ψ c σ p = s}` (`preimage_sphereSet`);
* `par ⁻¹' boxRegion = {p | boxB ψ c σ p < s}` (`preimage_boxRegion`);
* `par ⁻¹' upperRegion = {p | boxB ψ c σ p < s ∧ 0 < planeG ψ c σ u p}`
  (`preimage_upperRegion`), and the lower half analogously;
* `par ⁻¹' sliceRegion = {p | boxB ψ c σ p < s ∧ planeG ψ c σ u p = 0}`
  (`preimage_sliceRegion`);
* `par ⁻¹' (upperRegion ∪ lowerRegion) = {p | boxB ψ c σ p < s ∧ planeG ψ c σ u p ≠ 0}`
  (`preimage_union_halfRegions`).

So the preimage of the region inside the box is `{B < s}`, of the slice is `{G = 0}`, and of the
union of the two half-regions is `{B < s, G ≠ 0}`.

We also record the two hypotheses on the configuration which Pardon's construction needs and which
this chapter states explicitly rather than deriving:

* `TransverseSlice ψ s c σ u` — **transversality of the cutting plane along the slice**, i.e.
  `∇G ≠ 0` everywhere on `{G = 0} ∩ {B < s}` (in the parameter plane: the derivative of `G` never
  vanishes on the slice).  It is implied by `IsRegularValue ψ (planeCoord c σ u) 0`
  (`transverseSlice_of_isRegularValue`), the global regularity of the level `0` of the plane
  coordinate, which is the form in which the sibling chapter `Work.Smooth.Morse` states it;
* `TameSlice ψ s c σ u` — **tameness of the slice**: the flat disc `cutDisc s c σ u` meets the
  surface in finitely many simple closed curves and embedded arcs
  (`Work.Smooth.Plane.TransversePlane`).  It is *proved* in `Work.BoxShrink.Pinch.Slice` from the
  transversality together with the two inputs isolated by `Work.Smooth.Morse`
  (`LocallyFiniteCriticalValues`, `CompactOneManifoldInput`): the plane trace is a compact
  locally-arc subset of the surface, hence a finite disjoint union of simple closed curves
  (`Work.Smooth.Morse.niceLevel_of_regularValue`), and the slice is its trace in the open box.

Nothing in this file uses the pinch itself: it is the exact dictionary of the reduction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-! ## The parametrisation and the two basic functions -/

/-- The parametrisation of the surface `ψ(F_standard)` of the challenge: `par ψ (x, y) = ψ
(torusMap x y)`.  (`Work.Smooth.Morse.param`, re-exported for the vocabulary of this chapter.) -/
def par (ψ : Submission.Diffeo) : ℝ × ℝ → R3 := Work.Smooth.Morse.param ψ

@[simp] theorem par_def (ψ : Submission.Diffeo) : par ψ = Work.Smooth.Morse.param ψ := rfl

@[simp] theorem par_apply (ψ : Submission.Diffeo) (x y : ℝ) :
    par ψ (x, y) = ψ (Work.Core.torusMap x y) := rfl

theorem par_contDiff (ψ : Submission.Diffeo) : ContDiff ℝ (⊤ : ℕ∞) (par ψ) :=
  Work.Smooth.Morse.param_contDiff ψ

theorem par_continuous (ψ : Submission.Diffeo) : Continuous (par ψ) :=
  (par_contDiff ψ).continuous

/-- The surface of the challenge is the image of the parametrisation. -/
theorem carrier_eq_range (ψ : Submission.Diffeo) :
    (Work.Smooth.Morse.torus ψ).carrier = Set.range (par ψ) :=
  Work.Smooth.Morse.torus_carrier ψ

theorem par_mem_carrier (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    par ψ p ∈ (Work.Smooth.Morse.torus ψ).carrier := ⟨p, rfl⟩

/-- **The pull-back of the box norm**: `boxB ψ c σ = Submission.boxNorm c σ ∘ par ψ`. -/
def boxB (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) : ℝ × ℝ → ℝ :=
  Work.Smooth.Morse.pullback ψ (Submission.boxNorm c σ)

@[simp] theorem boxB_apply (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (p : ℝ × ℝ) : boxB ψ c σ p = Submission.boxNorm c σ (par ψ p) := rfl

theorem boxB_continuous (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (boxB ψ c σ) :=
  (Work.Topology.SphereSlicing.boxNorm_continuous c σ).comp (par_continuous ψ)

/-- **The pull-back of the plane coordinate**: the signed `σ 2`-distance
`y ↦ y (σ 2) - (c (σ 2) + u)` to the cutting plane, read in the parameter plane. -/
def planeG (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : ℝ × ℝ → ℝ :=
  Work.Smooth.Morse.pullback ψ (Work.BoxShrink.Bubble.planeCoord c σ u)

@[simp] theorem planeG_apply (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (p : ℝ × ℝ) :
    planeG ψ c σ u p = Work.BoxShrink.Bubble.planeCoord c σ u (par ψ p) := rfl

/-- The pull-back of the plane coordinate is `C²`: the plane coordinate is linear and the
parametrisation is `C^∞`. -/
theorem planeG_contDiff (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    ContDiff ℝ 2 (planeG ψ c σ u) := by
  have hpar : ContDiff ℝ 2 (par ψ) := (par_contDiff ψ).of_le (by decide)
  exact (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).comp hpar

/-- A parameter lies in the preimage of the slice exactly when its box norm is below `s` and the
plane coordinate vanishes there.  This is the "`{B < s, G = 0}`" of the plan. -/
theorem mem_boxB_planeG_slice {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {p : ℝ × ℝ} :
    boxB ψ c σ p < s ∧ planeG ψ c σ u p = 0 ↔
      par ψ p ∈ Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
  rw [Work.BoxShrink.Core.mem_sliceRegion, boxB_apply, planeG_apply,
    Work.BoxShrink.Bubble.planeCoord_apply, Submission.mem_PBox_iff, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨par_mem_carrier ψ p, h1, h2⟩
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩

/-- The plane coordinate is `C¹` (it is linear). -/
theorem contDiff_one_planeCoord (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    ContDiff ℝ 1 (Work.BoxShrink.Bubble.planeCoord c σ u) := by
  show ContDiff ℝ 1 (fun y : R3 => y (σ 2) - (c (σ 2) + u))
  exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ 2) : R3 →L[ℝ] ℝ).contDiff).sub contDiff_const

/-! ## The dictionary: preimages of the regions -/

/-- The preimage of Pardon's box is the sublevel set `{boxB < s}` of the pull-back box norm. -/
theorem preimage_PBox (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    par ψ ⁻¹' Submission.PBox s c σ = {p : ℝ × ℝ | boxB ψ c σ p < s} := by
  ext p
  rw [Set.mem_preimage, Set.mem_ofPred_eq, boxB_apply, Submission.mem_PBox_iff]

/-- The preimage of the boundary sphere `∂PBox s c σ` is the level set `{boxB = s}`. -/
theorem preimage_sphereSet (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    par ψ ⁻¹' Work.BoxShrink.Core.sphereSet c σ s = {p : ℝ × ℝ | boxB ψ c σ p = s} := by
  ext p
  rw [Set.mem_preimage, Set.mem_ofPred_eq, boxB_apply, Work.BoxShrink.Core.mem_sphereSet]

/-- The preimage of the region inside the box is `{boxB < s}` (the parametrisation surjects onto
the surface, so the carrier adds nothing). -/
theorem preimage_boxRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    par ψ ⁻¹' Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ =
      {p : ℝ × ℝ | boxB ψ c σ p < s} := by
  ext p
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Work.BoxShrink.Core.mem_boxRegion, boxB_apply,
    Submission.mem_PBox_iff]
  exact ⟨fun h => h.2, fun h => ⟨par_mem_carrier ψ p, h⟩⟩

/-- The preimage of the upper half-region is `{boxB < s, 0 < planeG}`. -/
theorem preimage_upperRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    par ψ ⁻¹' Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u =
      {p : ℝ × ℝ | boxB ψ c σ p < s ∧ 0 < planeG ψ c σ u p} := by
  ext p
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Work.BoxShrink.Core.mem_upperRegion, boxB_apply,
    planeG_apply, Submission.mem_PBox_iff, Work.BoxShrink.Bubble.planeCoord_apply]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨par_mem_carrier ψ p, h1, by linarith⟩

/-- The preimage of the lower half-region is `{boxB < s, planeG < 0}`. -/
theorem preimage_lowerRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    par ψ ⁻¹' Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u =
      {p : ℝ × ℝ | boxB ψ c σ p < s ∧ planeG ψ c σ u p < 0} := by
  ext p
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Work.BoxShrink.Core.mem_lowerRegion, boxB_apply,
    planeG_apply, Submission.mem_PBox_iff, Work.BoxShrink.Bubble.planeCoord_apply]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨par_mem_carrier ψ p, h1, by linarith⟩

/-- The preimage of the slice is `{boxB < s, planeG = 0}`. -/
theorem preimage_sliceRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    par ψ ⁻¹' Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u =
      {p : ℝ × ℝ | boxB ψ c σ p < s ∧ planeG ψ c σ u p = 0} := by
  ext p
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Work.BoxShrink.Core.mem_sliceRegion, boxB_apply,
    planeG_apply, Submission.mem_PBox_iff, Work.BoxShrink.Bubble.planeCoord_apply, sub_eq_zero]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨par_mem_carrier ψ p, h1, h2⟩

/-- **The preimage of the union of the two half-regions is `{boxB < s, planeG ≠ 0}`** — this is
the set the pinch has to land in. -/
theorem preimage_union_halfRegions (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    par ψ ⁻¹'
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) =
      {p : ℝ × ℝ | boxB ψ c σ p < s ∧ planeG ψ c σ u p ≠ 0} := by
  rw [Set.preimage_union, preimage_upperRegion, preimage_lowerRegion]
  ext p
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, ne_of_gt h2⟩
    · exact ⟨h1, ne_of_lt h2⟩
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy (planeG ψ c σ u p) 0 with h | h | h
    · exact Or.inr ⟨h1, h⟩
    · exact absurd h h2
    · exact Or.inl ⟨h1, h⟩

/-- The image form of the slice dictionary: the slice is the image under the parametrisation of
`{B < s, G = 0}`. -/
theorem sliceRegion_eq_image (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u =
      par ψ '' {p : ℝ × ℝ | boxB ψ c σ p < s ∧ planeG ψ c σ u p = 0} := by
  rw [← preimage_sliceRegion]
  exact (Set.image_preimage_eq_of_subset (fun y hy => by
    have h : y ∈ (Work.Smooth.Morse.torus ψ).carrier :=
      (Work.BoxShrink.Core.sliceRegion_subset (Work.Smooth.Morse.torus ψ) s c σ u hy).1
    rwa [carrier_eq_range] at h)).symm

/-! ## Periodicity of the dictionary -/

/-- The parametrisation is equivariant under the period lattice `2πℤ²`: shifting a parameter by
`2π k` in either variable does not move the point of `ℝ³`. -/
theorem torusMap_period (x y : ℝ) (k l : ℤ) :
    Work.Core.torusMap (x + (k : ℝ) * (2 * Real.pi)) (y + (l : ℝ) * (2 * Real.pi)) =
      Work.Core.torusMap x y := by
  unfold Work.Core.torusMap
  simp only [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- The parametrisation is `2πℤ²`-periodic: shifting either parameter by an integer multiple of
`2π` does not move the point of `ℝ³`. -/
theorem par_period' (ψ : Submission.Diffeo) (x y : ℝ) (k l : ℤ) :
    par ψ (x + (k : ℝ) * (2 * Real.pi), y + (l : ℝ) * (2 * Real.pi)) = par ψ (x, y) := by
  simp only [par_apply]
  rw [torusMap_period]

theorem par_period (ψ : Submission.Diffeo) (p : ℝ × ℝ) (k l : ℤ) :
    par ψ (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) = par ψ p := by
  cases p with
  | mk x y => exact par_period' ψ x y k l

/-- The pull-back of any function of `ℝ³` is `2πℤ²`-periodic in the parameter plane. -/
theorem pullback_period (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) (k l : ℤ) :
    g (par ψ (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi))) = g (par ψ p) := by
  rw [par_period]

theorem boxB_period (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (p : ℝ × ℝ) (k l : ℤ) :
    boxB ψ c σ (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
      boxB ψ c σ p := by
  simp only [boxB_apply]
  rw [par_period]

theorem planeG_period (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (p : ℝ × ℝ) (k l : ℤ) :
    planeG ψ c σ u (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
      planeG ψ c σ u p := by
  simp only [planeG_apply]
  rw [par_period]

/-! ## The two hypotheses on the configuration -/

/-- **Transversality of the cutting plane along the slice.**  In the parameter plane: the
derivative of the pull-back `G = planeG ψ c σ u` never vanishes at a parameter mapping into the
slice.  This is "`∇G ≠ 0` on `{G = 0} ∩ {boxRegion}`", the general position of the cutting plane
with respect to the surface which Pardon's count supplies. -/
def TransverseSlice (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∀ p : ℝ × ℝ, boxB ψ c σ p < s → planeG ψ c σ u p = 0 →
    fderiv ℝ (planeG ψ c σ u) p ≠ 0

/-- **Transversality is implied by the regularity of the level `0` of the plane coordinate** (the
form in which `Work.Smooth.Morse` states the general position of a level). -/
theorem transverseSlice_of_isRegularValue (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : Work.Smooth.Morse.IsRegularValue ψ (Work.BoxShrink.Bubble.planeCoord c σ u) 0) :
    TransverseSlice ψ s c σ u := by
  intro p _ hG
  exact (Work.Smooth.Morse.isRegularValue_iff ψ _ 0).mp h p hG

/-- The equivalent "regular value" form of `TransverseSlice` when the transversality is known on
all of the surface (not just inside the box). -/
theorem isRegularValue_of_transverseSlice_all (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : ∀ p : ℝ × ℝ, planeG ψ c σ u p = 0 → fderiv ℝ (planeG ψ c σ u) p ≠ 0) :
    Work.Smooth.Morse.IsRegularValue ψ (Work.BoxShrink.Bubble.planeCoord c σ u) 0 :=
  (Work.Smooth.Morse.isRegularValue_iff ψ _ 0).mpr fun p hp => h p hp

/-- **Tameness of the slice**: the flat disc cut out of the box by the cutting plane meets the
surface in finitely many simple closed curves and embedded arcs
(`Work.Smooth.Plane.TransversePlane`, i.e. the classical "finite union of arcs and circles" of the
plan).  This is the form in which the chapter consumes the tameness input; it is *derived* from
the transversality and the classification of compact `1`-manifolds in
`Work.BoxShrink.Pinch.Slice`. -/
def TameSlice (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.Smooth.Plane.TransversePlane (Work.Smooth.Morse.torus ψ)
    (Work.BoxShrink.Core.cutDisc s c σ u)

/-- The flat disc of the plane inside the box is Pardon's planar slice. -/
theorem cutDisc_eq_PardonSlice (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.cutDisc s c σ u = Work.Smooth.Plane.PardonSlice s c σ u := rfl

/-- The slice of the plane inside the box is convex and planar, so the classical planar
innermost-disc machinery (`Work.Smooth.Plane`) applies to it. -/
theorem isConvexPlanar_cutDisc (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.Smooth.Plane.IsConvexPlanar (Work.BoxShrink.Core.cutDisc s c σ u) :=
  Work.Smooth.Plane.isConvexPlanar_PardonSlice s c σ u

end

end Work.BoxShrink.Pinch
