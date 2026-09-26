import Submission.Work.Smooth.SphereJordan.Basic
import Submission.Work.Smooth.SphereJordan.mobiusAddInv

/-!
# Moving curves and their two-disc data around the Riemann sphere

The planar Jordan–Schoenflies theorem is available (as `PlaneHypothesis`) only for curves *in the
plane*, i.e. for curves of `ℂ ∪ {∞}` which miss `∞`.  To apply it to an arbitrary simple closed
curve `c` on the sphere one moves `c` by a Möbius transformation `Φ` with `Φ ∞` a point off `c`
(`exists_homeomorph_infty_eq`), obtains the two-disc datum for `Φ.symm ∘ c` from the planar theorem,
and transports it back along `Φ` (`TwoDiscs.mapHomeomorph`, `Basic.lean`).

This file provides the elementary scaffolding of that reduction: the invariance of the curve
predicate and of the two-disc data under pointwise equality of curves, the transport of a whole
family datum along a homeomorphism, and the existence of a homeomorphism of the sphere sending `∞`
to any prescribed point.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Pointwise equality of curves -/

theorem IsSimpleClosedCurve.congr {c c' : ℝ → RiemannSphere} (h : IsSimpleClosedCurve c)
    (hcc : ∀ t, c t = c' t) : IsSimpleClosedCurve c' :=
  ⟨h.1.congr hcc,
    fun t => by rw [← hcc (t + 2 * Real.pi), h.2.1 t, hcc t],
    fun a ha b hb hab => h.2.2 ha hb (by rw [hcc a, hcc b]; exact hab)⟩

namespace TwoDiscs

/-- **A two-disc datum only depends on the trace of the curve.** -/
def congr {c c' : ℝ → RiemannSphere} (hcc : ∀ t, c t = c' t) (h : TwoDiscs c) :
    TwoDiscs c' where
  simple := h.simple.congr hcc
  e := h.e
  e' := h.e'
  inj := h.inj
  inj' := h.inj'
  boundary := fun θ => by rw [h.boundary θ, hcc θ]
  boundary' := fun θ => by rw [h.boundary' θ, hcc θ]
  open_interior := h.open_interior
  open_interior' := h.open_interior'
  cover := h.cover
  meet := by rw [h.meet, show Set.range c = Set.range c' from congrArg Set.range (funext hcc)]

end TwoDiscs

/-! ## Transport of a family datum along a homeomorphism -/

/-- **The standard-position datum of a finite family is transported along a homeomorphism** of the
Riemann sphere (the nesting rank is unchanged). -/
def FamilyData.mapHomeomorph {ι : Type} [Fintype ι] {c : ι → ℝ → RiemannSphere}
    (Φ : RiemannSphere ≃ₜ RiemannSphere) (h : FamilyData c) :
    FamilyData (fun i t => Φ (c i t)) where
  e := fun i => ⟨fun z => Φ (h.e i z), Φ.continuous.comp (h.e i).continuous⟩
  e' := fun i => ⟨fun z => Φ (h.e' i z), Φ.continuous.comp (h.e' i).continuous⟩
  rank := h.rank
  inj := fun i a b hab => h.inj i (Φ.injective hab)
  inj' := fun i a b hab => h.inj' i (Φ.injective hab)
  boundary := fun i θ => by simp [h.boundary i θ]
  boundary' := fun i θ => by simp [h.boundary' i θ]
  open_interior := fun i => by
    have h1 : {x : RiemannSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧
          (⟨fun z => Φ (h.e i z), Φ.continuous.comp (h.e i).continuous⟩ :
            C(Disc, RiemannSphere)) z = x} = Φ '' {x : RiemannSphere |
              ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.e i z = x} := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨h.e i z, ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [h1]
    exact Φ.isOpenMap _ (h.open_interior i)
  open_interior' := fun i => by
    have h1 : {x : RiemannSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧
          (⟨fun z => Φ (h.e' i z), Φ.continuous.comp (h.e' i).continuous⟩ :
            C(Disc, RiemannSphere)) z = x} = Φ '' {x : RiemannSphere |
              ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.e' i z = x} := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨h.e' i z, ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [h1]
    exact Φ.isOpenMap _ (h.open_interior' i)
  cover := fun i => by
    show Set.range (fun z : Disc => Φ (h.e i z)) ∪
      Set.range (fun z : Disc => Φ (h.e' i z)) = Set.univ
    have h1 : Set.range (fun z : Disc => Φ (h.e i z)) = Φ '' Set.range (h.e i) := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e i z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    have h2 : Set.range (fun z : Disc => Φ (h.e' i z)) = Φ '' Set.range (h.e' i) := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e' i z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    rw [h1, h2, ← Set.image_union, h.cover i, Set.image_univ]
    exact Φ.surjective.range_eq
  meet := fun i => by
    show Set.range (fun z : Disc => Φ (h.e i z)) ∩
      Set.range (fun z : Disc => Φ (h.e' i z)) = Set.range (fun t : ℝ => Φ (c i t))
    have h1 : Set.range (fun z : Disc => Φ (h.e i z)) = Φ '' Set.range (h.e i) := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e i z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    have h2 : Set.range (fun z : Disc => Φ (h.e' i z)) = Φ '' Set.range (h.e' i) := by
      ext x; constructor
      · rintro ⟨z, rfl⟩; exact ⟨h.e' i z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    have h3 : Set.range (fun t : ℝ => Φ (c i t)) = Φ '' Set.range (c i) := by
      ext x; constructor
      · rintro ⟨t, rfl⟩; exact ⟨c i t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
    rw [h1, h2, h3, ← Set.image_inter Φ.injective, h.meet i]
  nested := by
    intro i j hij
    obtain ⟨z, hz, hmem⟩ := hij
    obtain ⟨t, ht⟩ := hmem
    exact h.nested i j ⟨z, hz, ⟨t, Φ.injective ht⟩⟩

/-! ## A point off the curve can be sent to `∞` -/

/-- **Every point of the Riemann sphere can be sent to `∞` by a Möbius transformation** — and then
the curve is a plane curve. -/
theorem exists_homeomorph_infty_eq (p : RiemannSphere) :
    ∃ Φ : RiemannSphere ≃ₜ RiemannSphere, Φ infty = p := by
  by_cases hp : p = infty
  · exact ⟨Homeomorph.refl _, hp.symm⟩
  · obtain ⟨lam, hlam⟩ := OnePoint.ne_infty_iff_exists.mp hp
    obtain ⟨Φ, hΦ, -, -⟩ := mobiusAddInv lam
    exact ⟨Φ, by rw [hΦ, hlam]⟩

end

end Work.Smooth.SphereJordan
