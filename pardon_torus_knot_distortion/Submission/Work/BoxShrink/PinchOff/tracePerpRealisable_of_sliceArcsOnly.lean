import Mathlib
import Submission.Work.BoxShrink.PinchOff.ArcsOnly
import Submission.Work.BoxShrink.PinchOff.Perp
import Submission.Work.BoxShrink.PinchOff.CirclesCase
import Submission.Work.BoxShrink.Pinch.Trace
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.Smooth.OneManifold.Classify
import Submission.Work.Smooth.OneManifold.isLocallyArc_levelSet_of_fderiv_ne_zero
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_of_forall
import Submission.Work.Smooth.OneManifold.Consumer

/-!
# The residual when the slice is covered by arcs: the arcs are compact

The hypothesis `SliceArcsOnly` asks that the slice `Σ` be covered by *finitely many* arcs
`a j : ArcInterval → ℝ³`, each continuous and injective, with image in `Σ`.  Since `ArcInterval =
Icc 0 1` is **compact** and `a j` is continuous, each `Set.range (a j)` is compact, so the cover
exhibits `Σ` as a *finite union of compact sets*: `Σ` is compact, and every connected component of
`Σ` is a compact subset of `Σ`.

Combined with the box-local transversality `TransverseSlice` — which says precisely that the
cutting plane is transverse to the surface along the slice, hence that `Σ` is locally Euclidean of
dimension one (a compact topological `1`-manifold without boundary, embedded in the surface) — the
classification of compact one-dimensional subsets of the surface
(`Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean`) applies and shows
that `Σ` is a **finite disjoint union of embedded circles** of the surface.  The hypothesis `hZ`
says that none of these circles is essential, so the peeling theorem
(`windingSpan_sdiff_iUnion_range_eq_of_not_isEssential`, `CirclesCase.lean`) applies verbatim: the
region inside the box and the two half-regions realise the same winding vectors, i.e. the *first*
alternative of `TracePerpRealisable` holds.

The mathematics is the observation — forced by the formalisation of `SliceArcsOnly`, in which the
arcs are parametrised on the *compact* interval — that a slice coverable by finitely many compact
arcs can have no "loose end" in the open box: it consists of whole components of the plane trace,
which are circles.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The slice, in the parameter plane -/

/-- **The slice is the image of the parameter region `{B < s, G = 0}`** (the dictionary of the
parent chapter's `Basic.lean`, read for the slice of this chapter). -/
theorem sigma_eq_param_image :
    Sigma ψ s c σ u = Work.Smooth.Morse.param ψ '' {p : ℝ × ℝ |
      Work.BoxShrink.Pinch.boxB ψ c σ p < s ∧
        Work.BoxShrink.Pinch.planeG ψ c σ u p = 0} := by
  show Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u = _
  rw [Work.BoxShrink.Pinch.sliceRegion_eq_image, Work.BoxShrink.Pinch.par_def]

/-- The slice is contained in the carrier of the surface. -/
theorem sigma_subset_carrier :
    Sigma ψ s c σ u ⊆ (Work.Smooth.Morse.torus ψ).carrier :=
  fun _ hx => (Work.BoxShrink.Core.mem_sliceRegion.mp hx).1

/-! ## Compactness of the slice -/

/-- **The slice is compact** as soon as it is covered by finitely many arcs: it is then a finite
union of images of the compact interval `ArcInterval = Icc 0 1`. -/
theorem isCompact_sigma_of_sliceArcsOnly (h : SliceArcsOnly ψ s c σ u) :
    IsCompact (Sigma ψ s c σ u) := by
  obtain ⟨κ, hκ, a, _hinj, ha_mem, hcover⟩ := h
  have hEq : Sigma ψ s c σ u = ⋃ j : κ, Set.range (a j) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := hcover x hx
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht⟩ := hj
      exact ht ▸ ha_mem j t
  rw [hEq]
  exact isCompact_iUnion (fun j => isCompact_range (a j).continuous)

/-! ## The slice is locally Euclidean -/

/-- **The slice is locally Euclidean of dimension one** under the box-local transversality: at
every point of the slice the cutting plane is transverse to the surface, so the slice is locally
the graph of a `C¹` function of one variable. -/
theorem isLocallyEuclidean_sigma_of_transverseSlice
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (Sigma ψ s c σ u) := by
  refine Work.Smooth.OneManifold.isLocallyEuclidean_of_forall_exists sigma_subset_carrier ?_
  intro x
  -- a parameter point over `x`, inside the box and on the plane
  obtain ⟨p, hp_mem, hp_eq⟩ : ∃ p : ℝ × ℝ,
      p ∈ {p : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ p < s ∧
        Work.BoxShrink.Pinch.planeG ψ c σ u p = 0} ∧
      Work.Smooth.Morse.param ψ p = (x : R3) := by
    have hx : (x : R3) ∈ Work.Smooth.Morse.param ψ '' {p : ℝ × ℝ |
        Work.BoxShrink.Pinch.boxB ψ c σ p < s ∧
          Work.BoxShrink.Pinch.planeG ψ c σ u p = 0} := by
      rw [← sigma_eq_param_image]
      exact x.2
    obtain ⟨p, hp, hpeq⟩ := hx
    exact ⟨p, hp, hpeq⟩
  obtain ⟨hBp, hGp⟩ := hp_mem
  -- the level set of the pull-back of the plane coordinate is locally an arc near `p`
  have hf : ContDiffAt ℝ 1 (Work.BoxShrink.Pinch.planeG ψ c σ u) p :=
    (Work.Smooth.Morse.pullback_contDiff_one ψ
      (Work.BoxShrink.Pinch.contDiff_one_planeCoord c σ u)).contDiffAt
  obtain ⟨V, hVopen, hpV, hVloc⟩ :=
    Work.Smooth.OneManifold.isLocallyArc_levelSet_of_fderiv_ne_zero
      (f := Work.BoxShrink.Pinch.planeG ψ c σ u) (p := p) (t := 0) hf hGp (hT p hBp hGp)
  -- the parametrisation is injective on a small ball
  obtain ⟨ε, hε, hinj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  set B : Set (ℝ × ℝ) :=
    Metric.ball p ε ∩ V ∩ {q : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ q < s} with hBdef
  have hBopen : IsOpen B := by
    rw [hBdef]
    exact (Metric.isOpen_ball.inter hVopen).inter
      (isOpen_lt (Work.BoxShrink.Pinch.boxB_continuous ψ c σ) continuous_const)
  have hpB : p ∈ B := by
    rw [hBdef]
    exact ⟨⟨Metric.mem_ball_self hε, hpV⟩, hBp⟩
  have hBsubV : B ⊆ V := by
    rw [hBdef]; exact fun q hq => hq.1.2
  have hBsubball : B ⊆ Metric.ball p ε := by
    rw [hBdef]; exact fun q hq => hq.1.1
  have hBsubbox : B ⊆ {q : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ q < s} := by
    rw [hBdef]; exact fun q hq => hq.2
  set P : Set (ℝ × ℝ) := B ∩ {q : ℝ × ℝ |
    Work.BoxShrink.Pinch.planeG ψ c σ u q = 0} with hPdef
  have hBP : B ∩ P = B ∩ {q : ℝ × ℝ | Work.BoxShrink.Pinch.planeG ψ c σ u q = 0} := by
    rw [hPdef, ← Set.inter_assoc, Set.inter_self]
  have hloc : Work.Smooth.OneManifold.IsLocallyArcP (B ∩ P) := by
    rw [hBP]
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc
        ↥((V ∩ {q : ℝ × ℝ | Work.BoxShrink.Pinch.planeG ψ c σ u q = 0}) ∩ B) :=
      Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen hVloc hBopen
    refine Work.Smooth.OneManifold.isLocallyArc_of_eq ?_ h1
    ext q
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hBsubV h1, h2⟩, h1⟩
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.Smooth.Morse.param ψ '' (B' ∩ P) =
        Work.Smooth.Morse.param ψ '' B' ∩ Sigma ψ s c σ u := by
    intro B' _ hB'sub
    have hsubbox : B' ⊆ {q : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ q < s} :=
      hB'sub.trans hBsubbox
    have hB'P : B' ∩ P = B' ∩ {q : ℝ × ℝ |
        Work.BoxShrink.Pinch.planeG ψ c σ u q = 0} := by
      rw [hPdef, ← Set.inter_assoc, Set.inter_eq_left.mpr hB'sub]
    rw [hB'P]
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqB', hqG⟩ := hq
      refine ⟨⟨q, hqB', rfl⟩, ?_⟩
      rw [sigma_eq_param_image]
      exact ⟨q, ⟨hsubbox hqB', hqG⟩, rfl⟩
    · rintro ⟨hy1, hy2⟩
      obtain ⟨q, hqB', rfl⟩ := hy1
      rw [sigma_eq_param_image] at hy2
      obtain ⟨q', hq', hq'eq⟩ := hy2
      have htm : Work.Core.torusMap q.1 q.2 = Work.Core.torusMap q'.1 q'.2 :=
        ψ.injective hq'eq.symm
      obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ :=
        (Work.Core.torusMap_eq_iff q.1 q.2 q'.1 q'.2).mp htm
      refine ⟨q, ⟨hqB', ?_⟩, rfl⟩
      have hqeq : q = (q'.1 + (k : ℝ) * (2 * Real.pi), q'.2 + (l : ℝ) * (2 * Real.pi)) := by
        ext <;> simp [hk, hl]
      rw [hqeq]
      exact (Work.BoxShrink.Pinch.planeG_period ψ c σ u q' k l).trans hq'.2
  exact ⟨Work.Smooth.Morse.param ψ '' B,
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen,
    ⟨p, hpB, hp_eq⟩,
    Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param sigma_subset_carrier hBopen
      (fun q hq => hq.1) hident (hinj.mono hBsubball) hloc⟩

/-! ## The slice is a finite disjoint union of circles -/

/-- **The slice is a finite disjoint union of embedded circles** of the surface: it is compact
(`isCompact_sigma_of_sliceArcsOnly`) and locally Euclidean
(`isLocallyEuclidean_sigma_of_transverseSlice`). -/
theorem isCircleUnion_sigma_of_sliceArcsOnly
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (h : SliceArcsOnly ψ s c σ u) :
    Work.Smooth.Morse.IsCircleUnion ψ (Sigma ψ s c σ u) :=
  Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean ψ
    sigma_subset_carrier (isCompact_sigma_of_sliceArcsOnly h)
    (isLocallyEuclidean_sigma_of_transverseSlice hT)

/-- **The slice is covered by circles only**, from `SliceArcsOnly` and the box-local
transversality. -/
theorem sliceCirclesOnly_of_sliceArcsOnly
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (h : SliceArcsOnly ψ s c σ u) :
    SliceCirclesOnly ψ s c σ u := by
  obtain ⟨n, γ, hsimple, hdisj, hcover⟩ := isCircleUnion_sigma_of_sliceArcsOnly hT h
  refine ⟨n, γ, hsimple, hdisj, ?_, ?_⟩
  · intro i t
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  · intro x hx
    rw [hcover] at hx
    simpa using hx

/-! ## The residual -/

/-- The residual restricted to the arcs of the slice: for every smooth configuration whose cutting plane is transverse along the slice and whose slice is covered by finitely many embedded arcs, and which carries no essential loop in the slice, the parent chapter's factored residual `TracePerpRealisable` holds. -/
theorem tracePerpRealisable_of_sliceArcsOnly {ψ : Submission.Diffeo} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (h : Work.BoxShrink.PinchOff.SliceArcsOnly ψ s c σ u)
    (hZ : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.PinchOff.Sigma ψ s c σ u)) :
    Work.BoxShrink.Pinch.TracePerpRealisable (Work.Smooth.Morse.torus ψ) s c σ u :=
  tracePerpRealisable_of_trace_circles_holds hZ (sliceCirclesOnly_of_sliceArcsOnly hT h)

end

end Work.BoxShrink.PinchOff
