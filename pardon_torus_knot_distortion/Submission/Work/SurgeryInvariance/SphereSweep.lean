import Submission.Work.SurgeryInvariance.API

/-!
# Pardon's family of spheres with `2`-surgeries, in the geometry

The deliverable of this subproject is Pardon's Lemma about a one-parameter family `{S_t}` of
embedded spheres in `ℝ³` which are transverse to the torus `F = P.carrier` except at finitely many
parameters, where a single `2`-surgery occurs.  `Work.SurgeryInvariance.Sweep` records such a family
through the regions `A_t = F ∩ int(S_t)`; `SphereSweep` below records the family through the spheres
`S_t` themselves, so that the hypotheses can be read off the geometry:

* away from the exceptional parameters the *regions* are moved by an ambient isotopy of `ℝ³`
  preserving `F` (this is the isotopy-extension statement for the family of spheres);
* at an exceptional parameter the region gains or loses the interior of an embedded disc of `F`
  (the local model of the saddle).

The conversion to a `Sweep` is `SphereSweep.toSweep`; it is where the (automatic) openness of the
regions `F ∩ int(S_t)` is supplied, so a user of `SphereSweep` never has to produce it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The openness certificates of `SurgeryShapeRaw` are automatic when the regions are traces of
open sets. -/
theorem surgeryShape_of_raw {A A' : Set R3} (h : SurgeryShapeRaw P A A')
    (hA : IsOpenInCarrier P A) (hA' : IsOpenInCarrier P A') : SurgeryShape P A A' := by
  obtain ⟨D, hcase⟩ := h
  exact ⟨D, hA, hA', hcase⟩

/-- **A one-parameter family of spheres in `ℝ³` with finitely many `2`-surgeries**, recorded
through the spheres themselves.  The region cut out of the torus at parameter `t` is
`P.carrier ∩ int(S_t)`. -/
structure SphereSweep (P : Work.CoreTopology.ParamTorus) where
  /-- the spheres `S_t` -/
  S : ℝ → Set R3
  /-- the exceptional (surgery) parameters -/
  exc : Finset ℝ
  /-- away from the exceptional parameters the region moves by an ambient isotopy -/
  regular : ∀ t : ℝ, t ∉ exc → ∃ ε : ℝ, 0 < ε ∧ (∀ s : ℝ, |s - t| < ε → s ∉ exc) ∧
    ∀ s : ℝ, |s - t| < ε →
      RegionIsotopic P (P.carrier ∩ interior (S t)) (P.carrier ∩ interior (S s))
  /-- at an exceptional parameter the region changes by a single `2`-surgery inside an embedded
  disc of `F`, or is moved by an ambient isotopy -/
  surgery : ∀ t : ℝ, t ∈ exc → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
    SurgeryShapeRaw P (P.carrier ∩ interior (S t)) (P.carrier ∩ interior (S s)) ∨
      RegionIsotopic P (P.carrier ∩ interior (S t)) (P.carrier ∩ interior (S s))

/-- The region cut out of the torus by the sphere family at parameter `t`. -/
def SphereSweep.region (S : SphereSweep P) (t : ℝ) : Set R3 := P.carrier ∩ interior (S.S t)

/-- A sphere sweep is a sweep of regions: the openness of `F ∩ int(S_t)` in `F` is automatic. -/
def SphereSweep.toSweep (S : SphereSweep P) : Sweep P where
  region := S.region
  exc := S.exc
  regular := S.regular
  surgery t ht := by
    obtain ⟨ε, hε, hshape⟩ := S.surgery t ht
    refine ⟨ε, hε, fun s hs => ?_⟩
    rcases hshape s hs with h | h
    · exact Or.inl (surgeryShape_of_raw h (isOpenInCarrier_carrier_inter (P := P) isOpen_interior)
        (isOpenInCarrier_carrier_inter (P := P) isOpen_interior))
    · exact Or.inr h

/-- **Pardon's `spherefamily` for a family of spheres.** -/
theorem SphereSweep.spherefamily (S : SphereSweep P)
    (h : P.ContainsEssentialLoop (S.region 0)) : P.ContainsEssentialLoop (S.region 1) :=
  S.toSweep.spherefamily h

/-- The essential-piece invariant is constant along the family of spheres. -/
theorem SphereSweep.containsEssentialLoop_iff (S : SphereSweep P) (t : ℝ) :
    P.ContainsEssentialLoop (S.region t) ↔ P.ContainsEssentialLoop (S.region 0) :=
  S.toSweep.containsEssentialLoop_iff t

/-- The winding span is constant along the family of spheres. -/
theorem SphereSweep.windingSpan_eq (S : SphereSweep P) (t : ℝ) :
    WindingSpan P (S.region t) = WindingSpan P (S.region 0) :=
  S.toSweep.windingSpan_eq t

/-- **Pardon's `doublebubble` for a family of spheres**: if the family ends in the region bounded by
the two halves of a double bubble together with a disc, one of the halves contains an essential
loop. -/
theorem SphereSweep.double_bubble (S : SphereSweep P) {H₁ H₂ : Set R3} {D : DiscRegion P}
    (hopen₁ : IsOpenInCarrier P H₁) (hopen₂ : IsOpenInCarrier P H₂) (hdisj : Disjoint H₁ H₂)
    (hdisjZ : Disjoint (H₁ ∪ H₂) D.interior)
    (hcover : S.region 1 = (H₁ ∪ H₂) ∪ D.interior)
    (h0 : P.ContainsEssentialLoop (S.region 0)) :
    P.ContainsEssentialLoop H₁ ∨ P.ContainsEssentialLoop H₂ :=
  S.toSweep.double_bubble hopen₁ hopen₂ hdisj hdisjZ hcover h0

end

end Work.SurgeryInvariance
