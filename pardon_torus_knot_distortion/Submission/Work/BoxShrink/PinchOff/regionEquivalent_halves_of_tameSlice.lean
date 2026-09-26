import Mathlib
import Submission.Work.BoxShrink.PinchOff.Drop
import Submission.Work.BoxShrink.PinchOff.peel_curve_sdiff_discRegion
import Submission.Work.BoxShrink.PinchOff.CompactSlice
import Submission.Work.BoxShrink.PinchOff.CirclesCase
import Submission.Work.BoxShrink.PinchOff.Extras

/-!
# The pinch-off: the loop-level transport at a tame configuration

`Work.BoxShrink.Pinch.RegionTransportSpanBotTame` -- Pardon's push-off in the loop-transport form,
at the configurations whose slice is *tame* -- is the datum the parent chapter carries (and the
first of the three named targets of the assignment that was neither refuted nor inhabited).  This
module proves it, in the form named by the assignment:

  `regionEquivalent_halves_of_tameSlice`:
  `RegionEquivalent (surface ψ) (Halves ψ s c σ u) (Omega ψ s c σ)`
  whenever the cutting plane is transverse along the slice, the slice is tame, and the slice carries
  no essential loop of the surface.

## Why tameness makes the transport true, although the transport form is false in general

Without tameness the transport form is false (`Work.BoxShrink.PinchOff.not_transport`): the witness
has a slice of two *open arcs* running to the box sphere, and those arcs separate the region inside
the box into two cells, each of which fails to realise the longitude.  Tameness rules exactly that
case out.  `Work.BoxShrink.Pinch.TameSlice` is a `Work.Smooth.Plane.TransversePlane` datum for the
flat disc `cutDisc s c σ u`, whose pieces are a finite family of closed curves of the surface and of
maps `ArcInterval = [0,1] → ℝ³` landing *in* the disc.  Since `ArcInterval` is compact and the
box's face with the disc is open, no arc of the datum can have an endpoint on the box sphere, so
`TameSlice` **forces the slice to be compact** (`isCompact_sliceRegion_of_tameSlice`), and hence --
under the transversality of the plane -- to be a *finite disjoint union of circles of the surface*
(`sliceCirclesOnly_of_isCompact`).

## The argument

So let `Ω = F ∩ PBox s c σ` be the region inside the box, `Σ` the slice, `Ω⁺ ∪ Ω⁻ = Ω \ Σ` the two
half-regions, and `γ i` (`i : Fin n`) the trace circles, pairwise disjoint, covering `Σ`.  By the
hypothesis `hZ` (no essential loop of the slice) each `γ i` is inessential, hence bounds an
embedded disc `D i` of the surface (`exists_discRegion_of_not_isEssential`).  The region `Ω` is open
in the carrier and contains every `γ i`, so

* the single-curve peel `peel_curve_sdiff_discRegion_aux` pushes every loop of `Ω` off the disc
  `D i` -- in particular off `γ i` -- along a curve of the same winding vector
  (`RegionEquivalent` at the loop level, `regionEquivalent_sdiff_range_closedCurve`);
* peeling one curve at a time (`regionEquivalent_sdiff_biUnion_range`) is legitimate because the
  intermediate region `Ω \ ⋃_{i ∈ S} range (γ i)` is again open in the carrier and still contains
  the next curve (pairwise disjointness): this is the *loop-level* counterpart of the parent
  chapter's span statement `windingSpan_sdiff_iUnion_range_eq_of_not_isEssential`.

Since the `γ i` cover `Σ`, the region left over is `Ω \ Σ = Ω⁺ ∪ Ω⁻` (`omega_sdiff_sigma_eq_halves`),
and the transport -- for a loop of `Ω` into the halves, and trivially back -- is
`RegionEquivalent (surface ψ) (Halves ψ s c σ u) (Omega ψ s c σ)`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Peeling a single inessential simple closed curve, at the level of loops -/

/-- **The loop-level peel of one inessential simple closed curve.**  Let `γ` be a simple,
inessential closed curve of the surface, and `X` a region of the surface which is open in the
carrier and contains the image of `γ`.  Then every loop of `X` is matched by a loop of
`X \ range γ` with the same winding vector, and conversely (the converse being the inclusion);
i.e. `RegionEquivalent P X (X \ range γ)`.

The proof is `peel_curve_sdiff_discRegion_aux` applied to the disc `D` bounded by `γ`
(`exists_discRegion_of_not_isEssential`) with the neighbourhood `N = X` of `D.boundary = range γ`. -/
theorem regionEquivalent_sdiff_range_closedCurve {X : Set R3}
    {γ : Work.CoreTopology.ClosedCurve P}
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsub : ∀ t : ℝ, γ t ∈ X) :
    Work.SurgeryInvariance.RegionEquivalent P X (X \ Set.range γ.γ) := by
  refine ⟨?_, ?_⟩
  · -- a loop of `X` is pushed off `D.carrier`, hence off `range γ`
    intro δ hδ
    obtain ⟨D, hD⟩ := exists_discRegion_of_not_isEssential γ hsimple hiness
    have hbX : D.boundary ⊆ X := by
      rw [hD]
      rintro x ⟨t, rfl⟩
      exact hsub t
    obtain ⟨δ', hδ', hw⟩ := peel_curve_sdiff_discRegion_aux (X := X) (D := D)
      ⟨X, hX, hbX, subset_rfl⟩ δ hδ
    refine ⟨δ', ?_, hw⟩
    intro t
    exact ⟨(hδ' t).1,
      fun h => (hδ' t).2 (Work.SurgeryInvariance.DiscRegion.boundary_subset_carrier D (hD.symm ▸ h))⟩
  · -- a loop avoiding `range γ` is a loop of `X`
    intro δ hδ
    exact ⟨δ, fun t => (hδ t).1, rfl⟩

/-! ## Peeling a finite family, at the level of loops -/

/-- **Peeling finitely many pairwise disjoint inessential simple closed curves out of a region**,
at the level of loops (the loop-level counterpart of
`windingSpan_sdiff_biUnion_range_eq`).  For every finite set `S` of indices the relation
`RegionEquivalent P X (X \ ⋃ i ∈ S, range (γ i))` holds.

This is an induction on `S`: the single-curve step `regionEquivalent_sdiff_range_closedCurve` is
applied to the intermediate region `X \ ⋃ i ∈ S, range (γ i)`, which is open in the carrier
(`isOpenInCarrier_sdiff_iUnion_range`) and contains the image of the next curve by pairwise
disjointness; transitivity of `RegionEquivalent`
(`Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans`) assembles the steps. -/
theorem regionEquivalent_sdiff_biUnion_range {n : ℕ} {X : Set R3}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hiness : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hsub : ∀ (i : Fin n) (t : ℝ), γ i t ∈ X) (S : Finset (Fin n)) :
    Work.SurgeryInvariance.RegionEquivalent P X (X \ ⋃ i ∈ S, Set.range (γ i).γ) := by
  induction S using Finset.induction_on with
  | empty => simpa using Work.SurgeryInvariance.RegionEquivalent.refl (P := P) X
  | insert a S ha ih =>
    have hset : (X \ ⋃ i ∈ S, Set.range (γ i).γ) \ Set.range (γ a).γ
        = X \ ⋃ i ∈ insert a S, Set.range (γ i).γ := by
      rw [Finset.set_biUnion_insert, Set.union_comm, ← Set.sdiff_sdiff]
    rw [← hset]
    refine Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans ih ?_
    refine regionEquivalent_sdiff_range_closedCurve (P := P) (X := X \ ⋃ i ∈ S, Set.range (γ i).γ)
      (γ := γ a) (hsimple a) (hiness a) (isOpenInCarrier_sdiff_iUnion_range hX γ S) ?_
    intro t
    refine ⟨hsub a t, ?_⟩
    intro hcon
    obtain ⟨i, hcon'⟩ := Set.mem_iUnion.mp hcon
    obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hcon'
    obtain ⟨t', ht'⟩ := hxi
    have hne : a ≠ i := by rintro rfl; exact ha hiS
    exact Set.disjoint_left.mp (hdisj a i hne) ⟨t, rfl⟩ ⟨t', ht'⟩

/-- **Removing a finite family of pairwise disjoint inessential simple closed curves from a region
does not change its loop content.**  Every loop of `X` is matched by a loop of `X` avoiding the
union of the curves, with the same winding vector, and conversely. -/
theorem regionEquivalent_sdiff_iUnion_range_of_not_isEssential {X : Set R3} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hiness : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hsub : ∀ (i : Fin n) (t : ℝ), γ i t ∈ X) :
    Work.SurgeryInvariance.RegionEquivalent P X (X \ ⋃ i, Set.range (γ i).γ) := by
  have h := regionEquivalent_sdiff_biUnion_range hX hsimple hiness hdisj hsub
    (Finset.univ : Finset (Fin n))
  have huniv : (⋃ i ∈ (Finset.univ : Finset (Fin n)), Set.range (γ i).γ)
      = ⋃ i, Set.range (γ i).γ := by
    ext x
    simp
  rwa [huniv] at h

/-! ## The transport at a tame configuration -/

/-- **The loop-level transport of the pinch at a tame configuration** (the target of the
assignment): if the cutting plane is transverse along the slice, the slice is tame, and the slice
carries no essential loop of the surface, then the two half-regions and the region inside the box
realise the same winding vectors -- `RegionEquivalent (Halves) (Omega)`.

Tameness forces the slice to be compact, hence a finite disjoint union of circles of the surface
(`sliceCirclesOnly_of_isCompact`); each is inessential by `hZ`, so each bounds a disc of the surface
and can be peeled away from `Ω` (`regionEquivalent_sdiff_iUnion_range_of_not_isEssential`).  Since
the circles cover the slice, the region left over is `Ω \ Σ = Ω⁺ ∪ Ω⁻`. -/
theorem regionEquivalent_halves_of_tameSlice {ψ : Submission.Diffeo} {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u) (hZ : ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop (Work.BoxShrink.PinchOff.Sigma ψ s c σ u)) : Work.SurgeryInvariance.RegionEquivalent (Work.BoxShrink.PinchOff.surface ψ) (Work.BoxShrink.PinchOff.Halves ψ s c σ u) (Work.BoxShrink.PinchOff.Omega ψ s c σ) := by
  classical
  -- the slice is compact, hence a finite disjoint union of circles of the surface
  obtain ⟨n, γ, hsimple, hdisj, hmem, hcover⟩ :=
    sliceCirclesOnly_of_isCompact (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u) hT
      (isCompact_sliceRegion_of_tameSlice (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u) hTa)
  -- each circle is inessential (`hZ`) and lies in the region inside the box
  have hiness : ∀ i, ¬ Work.CoreTopology.IsEssential (surface ψ) (γ i) :=
    fun i hess => hZ ⟨γ i, hess, fun t => hmem i t⟩
  have hsub : ∀ (i : Fin n) (t : ℝ), γ i t ∈ Omega ψ s c σ :=
    fun i t => Sigma_subset_Omega (hmem i t)
  -- peel all of them off the region at once
  have hpeel : Work.SurgeryInvariance.RegionEquivalent (surface ψ) (Omega ψ s c σ)
      (Omega ψ s c σ \ ⋃ i, Set.range (γ i).γ) :=
    regionEquivalent_sdiff_iUnion_range_of_not_isEssential (P := surface ψ) (X := Omega ψ s c σ)
      (γ := γ) isOpenInCarrier_omega hsimple hiness hdisj hsub
  -- the circles cover the slice, so what is left is the union of the two half-regions
  have hset : Omega ψ s c σ \ ⋃ i, Set.range (γ i).γ = Halves ψ s c σ u := by
    rw [← omega_sdiff_sigma_eq_halves]
    congr 1
    refine Set.Subset.antisymm ?_ ?_
    · rintro x hx
      obtain ⟨i, ⟨t, ht⟩⟩ := Set.mem_iUnion.mp hx
      exact ht ▸ hmem i t
    · rintro x hx
      exact Set.mem_iUnion.mpr (hcover x hx)
  rw [← hset]
  exact Work.SurgeryInvariance.RegionEquivalent.symm hpeel

end

end Work.BoxShrink.PinchOff
