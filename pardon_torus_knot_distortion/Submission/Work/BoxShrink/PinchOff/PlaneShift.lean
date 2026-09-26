import Mathlib
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.Schoenflies.All

/-!
# Translates of a plane Jordan configuration

This file provides the elementary translation API for the planar Jordan/Schoenflies
vocabulary of `Work.Smooth.Jordan`: the translate `shiftSet T z` of a set of complex
numbers, and the translate `shiftSchoenflies h z` of a `PlaneSchoenflies` datum by a
vector `z : ℂ`.

It is the prerequisite of `Work.BoxShrink.PinchOff.disjoint_closure_shift`, where the
disjointness of a Jordan domain from its translates is used to show that the universal
covering `ℝ² → F` of a torus is injective on the closed disc bounded by a simple closed
curve.
-/

open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## Translating sets of complex numbers -/

/-- The translate `T + z = {x | x - z ∈ T}` of a set of complex numbers by `z`. -/
def shiftSet (T : Set ℂ) (z : ℂ) : Set ℂ := {x | x - z ∈ T}

theorem mem_shiftSet {T : Set ℂ} {z x : ℂ} : x ∈ shiftSet T z ↔ x - z ∈ T := Iff.rfl

theorem shiftSet_eq_image (T : Set ℂ) (z : ℂ) :
    shiftSet T z = (fun y => y + z) '' T := by
  ext x
  constructor
  · intro hx
    exact ⟨x - z, hx, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    show y + z - z ∈ T
    rwa [add_sub_cancel_right]

theorem isOpen_shiftSet {T : Set ℂ} (hT : IsOpen T) (z : ℂ) : IsOpen (shiftSet T z) := by
  rw [shiftSet_eq_image]
  exact ((Homeomorph.addRight z).isOpen_image).mpr hT

theorem isPreconnected_shiftSet {T : Set ℂ} (hT : IsPreconnected T) (z : ℂ) :
    IsPreconnected (shiftSet T z) := by
  rw [shiftSet_eq_image]
  exact hT.image (fun y => y + z) (continuous_id.add continuous_const).continuousOn

theorem isBounded_shiftSet {T : Set ℂ} (hT : Bornology.IsBounded T) (z : ℂ) :
    Bornology.IsBounded (shiftSet T z) := by
  rw [isBounded_iff_forall_norm_le] at hT ⊢
  obtain ⟨C, hC⟩ := hT
  refine ⟨C + ‖z‖, ?_⟩
  intro x hx
  have h1 : x - z ∈ T := hx
  have h2 := hC (x - z) h1
  calc ‖x‖ = ‖(x - z) + z‖ := by ring_nf
    _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ C + ‖z‖ := by linarith

theorem nonempty_shiftSet {T : Set ℂ} (hT : T.Nonempty) (z : ℂ) :
    (shiftSet T z).Nonempty := by
  rw [shiftSet_eq_image]
  exact hT.image (fun y => y + z)

theorem shiftSet_union (T T' : Set ℂ) (z : ℂ) :
    shiftSet (T ∪ T') z = shiftSet T z ∪ shiftSet T' z := by
  ext x; simp [shiftSet]

theorem disjoint_shiftSet {T T' : Set ℂ} (h : Disjoint T T') (z : ℂ) :
    Disjoint (shiftSet T z) (shiftSet T' z) := by
  rw [Set.disjoint_left] at h ⊢
  intro x hx hx'
  exact h hx hx'

/-- Translating by `z` then by `w` is translating by `w + z`. -/
theorem shiftSet_shiftSet (T : Set ℂ) (z w : ℂ) :
    shiftSet (shiftSet T z) w = shiftSet T (w + z) := by
  ext x
  simp only [mem_shiftSet]
  rw [show x - w - z = x - (w + z) from by ring]

/-- `shiftSet T z` contains exactly the points of `T`, translated by `z`. -/
theorem shiftSet_image (T : Set ℂ) (z : ℂ) :
    shiftSet T z = Set.image (fun y => y + z) T := shiftSet_eq_image T z

/-! ## Translating a plane curve and its Schoenflies datum -/

/-- The translate `c + z` of a closed plane curve by a vector `z`. -/
def shiftCurve (c : Work.Smooth.Jordan.PlaneCurve) (z : ℂ) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := fun t => c.γ t + z
  cont := c.cont.add continuous_const
  periodic := fun t => by
    show c.γ (t + 2 * Real.pi) + z = c.γ t + z
    rw [c.periodic t]

theorem shiftCurve_apply (c : Work.Smooth.Jordan.PlaneCurve) (z : ℂ) (t : ℝ) :
    (shiftCurve c z).γ t = c.γ t + z := rfl

theorem shiftCurve_trace (c : Work.Smooth.Jordan.PlaneCurve) (z : ℂ) :
    (shiftCurve c z).trace = shiftSet c.trace z := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    show x - z ∈ c.trace
    rw [← ht]
    exact ⟨t, by rw [shiftCurve_apply]; ring⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [shiftCurve_apply, ht]; ring⟩

theorem shiftCurve_isSimple {c : Work.Smooth.Jordan.PlaneCurve} (hc : c.IsSimple) (z : ℂ) :
    (shiftCurve c z).IsSimple := by
  intro s hs t ht hst
  exact hc hs ht (add_right_cancel hst)

theorem isSimple_of_shiftCurve_isSimple {c : Work.Smooth.Jordan.PlaneCurve} {z : ℂ}
    (h : (shiftCurve c z).IsSimple) : c.IsSimple := by
  intro s hs t ht hst
  exact h hs ht (by show c.γ s + z = c.γ t + z; rw [hst])

/-- **The translate of a Schoenflies datum.**  The translate `c + z` of a simple closed plane
curve has the translate of the bounded/unbounded side of `c` as its bounded/unbounded side, and
the translate of the spanning disc as its spanning disc. -/
def shiftSchoenflies {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies c) (z : ℂ) :
    Work.Smooth.Jordan.PlaneSchoenflies (shiftCurve c z) where
  toPlaneSeparation :=
    { simple := shiftCurve_isSimple h.toPlaneSeparation.simple z
      U := shiftSet h.U z
      V := shiftSet h.V z
      isOpen_U := isOpen_shiftSet h.isOpen_U z
      isOpen_V := isOpen_shiftSet h.isOpen_V z
      preconn_U := isPreconnected_shiftSet h.preconn_U z
      preconn_V := isPreconnected_shiftSet h.preconn_V z
      nonempty_U := nonempty_shiftSet h.nonempty_U z
      nonempty_V := nonempty_shiftSet h.nonempty_V z
      disjoint_UV := disjoint_shiftSet h.disjoint_UV z
      union_eq := by
        rw [← shiftSet_union, h.toPlaneSeparation.union_eq, shiftCurve_trace]
        ext x
        simp only [mem_shiftSet, Set.mem_compl_iff]
      bounded_V := isBounded_shiftSet h.bounded_V z }
  e := ⟨fun w => h.e w + z, h.e.continuous.add continuous_const⟩
  inj := fun a b hab => h.inj (add_right_cancel hab)
  boundary := fun θ => by
    show h.e (Work.Smooth.Jordan.circlePoint θ) + z = (shiftCurve c z).γ θ
    rw [h.boundary θ]
    rfl
  range_e := by
    change Set.range (fun w => h.e w + z) = closure (shiftSet h.V z)
    have h1 : Set.range (fun w => h.e w + z) = (fun y => y + z) '' closure h.V := by
      rw [show (fun w => h.e w + z) = (fun y => y + z) ∘ (⇑h.e) from rfl, Set.range_comp,
        h.range_e]
    have h2 : (fun y => y + z) '' closure h.V = closure ((fun y => y + z) '' h.V) :=
      Homeomorph.image_closure (Homeomorph.addRight z) h.V
    have h3 : (fun y => y + z) '' h.V = shiftSet h.V z := (shiftSet_eq_image h.V z).symm
    rw [h1, h2, h3]

theorem shiftSchoenflies_V {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies c) (z : ℂ) :
    (shiftSchoenflies h z).V = shiftSet h.V z := rfl

theorem shiftSchoenflies_U {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSchoenflies c) (z : ℂ) :
    (shiftSchoenflies h z).U = shiftSet h.U z := rfl

end

end Work.BoxShrink.PinchOff
