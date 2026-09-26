import Submission.Work.BoxShrink.Bubble.Plane.PerturbCountable
import Submission.Work.BoxShrink.Bubble.Plane.countable_preimage
import Submission.Work.BoxShrink.Bubble.Plane.FiniteSlice

/-!
# The field from the push-off when the slicing plane meets the region in countably many points

The perturbation method of `Work.BoxShrink.Bubble.Plane` proves the push-off as soon as the preimage
of the slice in the parameter plane is *countable on compact sets* (rather than finite): the bad-set
argument of `Plane/Perturb` works with `Plane/interior_iUnion_empty`, which is Baire's theorem for a
countable union of closed sets of empty interior.

So **Pardon's double bubble (the field `bubble` of `Work.BoxShrink.Core.BubbleInput`) holds whenever
the slicing plane meets the region inside the box in countably many points**.  This strictly contains
`Plane/FiniteSlice`.  What it does *not* contain is the case of the crux — a slice which is locally an
arc or a circle: there the preimage is not countable on compacta, the bad set of translations
genuinely contains a neighbourhood of the origin, and the collar/pinch is needed (see `PLAN.md`,
stretch 13).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

theorem slicePushOff_of_countable_preimage {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcount : ∀ K : Set (ℝ × ℝ), IsCompact K →
      (K ∩ slicePreimage P s c σ u).Countable) :
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
    Plane.exists_path_avoiding_of_thin_of_countable hp₁closed hp₁int hδ hδtube hcount
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

/-- A countable slice has countable intersection with every compact set of the parameter plane. -/
theorem countable_slicePreimage (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hcount : (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable) {K : Set (ℝ × ℝ)}
    (_hK : IsCompact K) : (K ∩ slicePreimage P s c σ u).Countable :=
  Plane.countable_preimage hcount _hK

/-- **The push-off when the plane meets the region inside the box in countably many points.** -/
theorem slicePushOff_of_countable_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcount : (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable) :
    SlicePushOff P s c σ u :=
  slicePushOff_of_countable_preimage (P := P)
    (fun K hK => countable_slicePreimage P s c σ u hcount hK)

/-- **Pardon's double bubble (the field `bubble`) when the plane meets the region inside the box in
countably many points.** -/
noncomputable def bubbleSweep_of_countable_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcount : (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable) :
    Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubble_of_slicePushOff (slicePushOff_of_countable_slice (P := P) hcount)

/-- The field in the shape of `Work.BoxShrink.Core.BubbleInput`. -/
noncomputable def bubble_of_countable_slice :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  fun P _s _c _σ _u _ hcount => bubbleSweep_of_countable_slice (P := P) hcount

end

end Work.BoxShrink.Bubble
