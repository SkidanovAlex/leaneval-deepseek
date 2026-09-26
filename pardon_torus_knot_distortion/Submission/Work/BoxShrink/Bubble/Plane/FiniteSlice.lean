import Submission.Work.BoxShrink.Bubble.Plane.Perturb
import Submission.Work.BoxShrink.Bubble.Plane.thinPath
import Submission.Work.BoxShrink.Bubble.Plane.finite_preimage
import Submission.Work.BoxShrink.Bubble.Plane.descent
import Submission.Work.BoxShrink.Bubble.Reduce

/-!
# The field from the push-off when the slicing plane meets the region in finitely many points

This file applies the perturbation method of the parameter plane
(`Work.BoxShrink.Bubble.Plane`) to the *finite* case of the push-off: whenever the slice
`sliceRegion P s c σ u` is **finite**, every loop of the region inside the box can be replaced, with
the *same* winding vector, by a loop of `upperRegion ∪ lowerRegion`.  Hence Pardon's double bubble
(`Work.BoxShrink.Core.BubbleSweep`, the field `bubble` of `Work.BoxShrink.Core.BubbleInput`) holds
for every such configuration — with no hypothesis on the sphere `∂PBox s c σ` and none on the
winding span of the slice beyond finiteness.

**The construction.**  Let `Ω = {q | P.psi q.1 q.2 ∈ boxRegion}` be the preimage in the parameter
plane of the region inside the box (open) and `W = {q | P.psi q.1 q.2 ∈ sliceRegion}` the preimage of
the slice.  Both are invariant under the period lattice `2πℤ²`.

* a loop `γ` of `boxRegion` has a lift `L`; the map `t ↦ (L.Θ (2πt), L.Φ (2πt))` is a path in `Ω`
  whose endpoints differ by the lattice vector `2π·(L.winding)`;
* a path in `Ω` can be replaced by a *thin* path with the same endpoints, closed with empty interior
  and compactly contained in `Ω` (`Work.BoxShrink.Bubble.Plane.thinPath`);
* a small *translation* of a thin path avoids `W`: the bad translations form a finite union of
  translates of the path's image, closed with empty interior, hence have empty interior
  (`Work.BoxShrink.Bubble.Plane.exists_translate_disjoint`), and only finitely many points of `W` can
  matter because `W ∩ K` is finite for every compact `K`
  (`Work.BoxShrink.Bubble.Plane.finite_preimage`);
* the translated path lies in `Ω ∖ W` and still joins points differing by the lattice vector, so it
  descends to a loop of `P` with the *same* winding vector, whose image lies in
  `P.psi '' (Ω ∖ W) = upperRegion ∪ lowerRegion`
  (`Work.BoxShrink.Bubble.Plane.descent`).

The push-off is `SlicePushOff` and the field is `bubble_of_slicePushOff`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The two preimages in the parameter plane -/

/-- The preimage, in the parameter plane, of the region inside the box. -/
def boxPreimage (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Set (ℝ × ℝ) :=
  {q | P.psi q.1 q.2 ∈ Work.BoxShrink.Core.boxRegion P s c σ}

/-- The preimage, in the parameter plane, of the slice. -/
def slicePreimage (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set (ℝ × ℝ) :=
  {q | P.psi q.1 q.2 ∈ Work.BoxShrink.Core.sliceRegion P s c σ u}

theorem boxPreimage_eq (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    boxPreimage P s c σ = {q : ℝ × ℝ | P.psi q.1 q.2 ∈ Submission.PBox s c σ} := by
  ext q
  rw [boxPreimage, Set.mem_setOf_eq, Work.BoxShrink.Core.mem_boxRegion]
  exact ⟨fun h => h.2, fun h => ⟨P.psi_mem_carrier _ _, h⟩⟩

theorem isOpen_boxPreimage (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : IsOpen (boxPreimage P s c σ) := by
  rw [boxPreimage_eq]
  exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).preimage P.cont

/-- The parametrisation is invariant under lattice translations. -/
theorem psi_lattice (P : Work.CoreTopology.ParamTorus) (q : ℝ × ℝ) (a b : ℤ) :
    P.psi (q.1 + a * (2 * Real.pi)) (q.2 + b * (2 * Real.pi)) = P.psi q.1 q.2 :=
  (P.psi_eq_iff _ _ _ _).mpr ⟨⟨a, by ring⟩, ⟨b, by ring⟩⟩

theorem boxPreimage_lattice (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {q : ℝ × ℝ} (hq : q ∈ boxPreimage P s c σ) (a b : ℤ) :
    (q.1 + a * (2 * Real.pi), q.2 + b * (2 * Real.pi)) ∈ boxPreimage P s c σ := by
  rw [boxPreimage, Set.mem_setOf_eq] at hq ⊢
  rw [psi_lattice]
  exact hq

theorem slicePreimage_lattice (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) {q : ℝ × ℝ} (hq : q ∈ slicePreimage P s c σ u)
    (a b : ℤ) :
    (q.1 + a * (2 * Real.pi), q.2 + b * (2 * Real.pi)) ∈ slicePreimage P s c σ u := by
  rw [slicePreimage, Set.mem_setOf_eq] at hq ⊢
  rw [psi_lattice]
  exact hq

/-- The descent of the preimage of the region minus the preimage of the slice is the union of the
two half-regions. -/
theorem psi_image_boxPreimage_sdiff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    (fun q : ℝ × ℝ => P.psi q.1 q.2) '' (boxPreimage P s c σ \ slicePreimage P s c σ u) ⊆
      Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u := by
  rintro y ⟨q, hq, rfl⟩
  have hb : P.psi q.1 q.2 ∈ Work.BoxShrink.Core.boxRegion P s c σ := hq.1
  have hs : P.psi q.1 q.2 ∉ Work.BoxShrink.Core.sliceRegion P s c σ u := hq.2
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u] at hb
  rcases hb with h | h
  · exact h
  · exact absurd h hs

/-- A finite slice has finite intersection with every compact set of the parameter plane. -/
theorem finite_slicePreimage (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hfin : (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) : (K ∩ slicePreimage P s c σ u).Finite :=
  Plane.finite_preimage hfin hK

/-! ## The push-off in the finite case -/

/-- **The push-off when the plane meets the region inside the box in finitely many points.** -/
theorem slicePushOff_of_finite_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hfin : (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite) :
    SlicePushOff P s c σ u := by
  refine (Toolkit.subset_realizedWindings_iff).mpr ?_
  intro γ hγ
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  -- the path of parameters
  set p₀ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ) :=
    ⟨fun t => (L.Θ (2 * Real.pi * (t : ℝ)), L.Φ (2 * Real.pi * (t : ℝ))),
      (L.contΘ.comp (continuous_const.mul continuous_subtype_val)).prodMk
        (L.contΦ.comp (continuous_const.mul continuous_subtype_val))⟩ with hp₀def
  have hp₀mem : ∀ t : Set.Icc (0 : ℝ) 1, p₀ t ∈ boxPreimage P s c σ := by
    intro t
    rw [boxPreimage, Set.mem_setOf_eq]
    show P.psi (L.Θ (2 * Real.pi * (t : ℝ))) (L.Φ (2 * Real.pi * (t : ℝ))) ∈
      Work.BoxShrink.Core.boxRegion P s c σ
    rw [L.lifts (2 * Real.pi * (t : ℝ))]
    exact hγ _
  -- the endpoints differ by the lattice vector of the winding
  have hp₀shift : (p₀ ⟨1, by norm_num⟩).1 = (p₀ ⟨0, by norm_num⟩).1 +
        (L.winding).1 * (2 * Real.pi) ∧
      (p₀ ⟨1, by norm_num⟩).2 = (p₀ ⟨0, by norm_num⟩).2 +
        (L.winding).2 * (2 * Real.pi) := by
    have h1 := (L.winding_spec).1
    have h2 := (L.winding_spec).2
    constructor
    · show L.Θ (2 * Real.pi * (1 : ℝ)) = L.Θ (2 * Real.pi * (0 : ℝ)) + _
      rw [show (2 : ℝ) * Real.pi * (1 : ℝ) = 2 * Real.pi by ring,
        show (2 : ℝ) * Real.pi * (0 : ℝ) = 0 by ring, h1]
    · show L.Φ (2 * Real.pi * (1 : ℝ)) = L.Φ (2 * Real.pi * (0 : ℝ)) + _
      rw [show (2 : ℝ) * Real.pi * (1 : ℝ) = 2 * Real.pi by ring,
        show (2 : ℝ) * Real.pi * (0 : ℝ) = 0 by ring, h2]
  -- thin the path
  obtain ⟨p₁, hp₁₀, hp₁₁, hp₁mem, hp₁closed, hp₁int, δ, hδ, hδtube⟩ :=
    Plane.thinPath (isOpen_boxPreimage P s c σ) p₀ hp₀mem
  -- translate it off the preimage of the slice
  obtain ⟨v, hv, hvavoid⟩ :=
    Plane.exists_path_avoiding_of_thin hp₁closed hp₁int hδ hδtube
      (fun K hK => finite_slicePreimage P s c σ u hfin hK)
  -- the translated path
  set p₂ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ) :=
    ⟨fun t => p₁ t + v, p₁.continuous.add continuous_const⟩ with hp₂def
  have hp₂mem : ∀ t : Set.Icc (0 : ℝ) 1, p₂ t ∈ boxPreimage P s c σ \ slicePreimage P s c σ u :=
    fun t => hvavoid t
  have hp₂shift : (p₂ ⟨1, by norm_num⟩).1 = (p₂ ⟨0, by norm_num⟩).1 +
        (L.winding).1 * (2 * Real.pi) ∧
      (p₂ ⟨1, by norm_num⟩).2 = (p₂ ⟨0, by norm_num⟩).2 +
        (L.winding).2 * (2 * Real.pi) := by
    have h1 := hp₁₁
    have h0 := hp₁₀
    have := hp₀shift
    constructor
    · show (p₁ ⟨1, by norm_num⟩ + v).1 =
        (p₁ ⟨0, by norm_num⟩ + v).1 + (L.winding).1 * (2 * Real.pi)
      rw [Prod.fst_add, Prod.fst_add, h1, h0, this.1]
      ring
    · show (p₁ ⟨1, by norm_num⟩ + v).2 =
        (p₁ ⟨0, by norm_num⟩ + v).2 + (L.winding).2 * (2 * Real.pi)
      rw [Prod.snd_add, Prod.snd_add, h1, h0, this.2]
      ring
  -- descend
  obtain ⟨γ', hγ'mem, hγ'wind⟩ :=
    Plane.descent (V := boxPreimage P s c σ \ slicePreimage P s c σ u)
      (fun q hq a b =>
        ⟨boxPreimage_lattice P s c σ hq.1 a b, fun hcon => hq.2 (by
          have h := slicePreimage_lattice P s c σ u hcon (-a) (-b)
          have hx : (q.1 + (a : ℝ) * (2 * Real.pi)) + ((-a : ℤ) : ℝ) * (2 * Real.pi) = q.1 := by
            push_cast
            ring
          have hy : (q.2 + (b : ℝ) * (2 * Real.pi)) + ((-b : ℤ) : ℝ) * (2 * Real.pi) = q.2 := by
            push_cast
            ring
          rw [hx, hy] at h
          exact h)⟩)
      p₂ hp₂mem hp₂shift
  refine ⟨γ', fun t => psi_image_boxPreimage_sdiff P s c σ u (hγ'mem t), ?_⟩
  rw [hγ'wind, ← Work.SurgeryInvariance.windingOf_eq P γ L]

/-- **Pardon's double bubble when the plane meets the region inside the box in finitely many
points.**  This is the field `bubble` of `Work.BoxShrink.Core.BubbleInput` in that case. -/
noncomputable def bubbleSweep_of_finite_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hfin : (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite) :
    Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubble_of_slicePushOff (slicePushOff_of_finite_slice (P := P) hfin)

/-- **The field for every configuration whose slice is finite**, in the shape of the structure
`Work.BoxShrink.Core.BubbleInput` (with the finiteness of the slice in place of the hypothesis that
the slice carries no essential loop, which finiteness implies: a finite set of points carries only
constant loops). -/
noncomputable def bubble_of_finite_slice :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  fun P s c σ u _ hfin => bubbleSweep_of_finite_slice (P := P) hfin

end

end Work.BoxShrink.Bubble
