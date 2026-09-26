import Submission.Work.Collar3D.PushOff.Main

/-!
# The push-off theorem: the cap of the innermost sub-disc

This file assembles the cap of `Work.Collar3D.DiscCollar.cap` with the side condition
`Work.Collar3D.DiscCollar.clearOfInteriorSide` into the *conclusion* of the sibling chapter's
`Work.Smooth.PushThrough3D.SurfacePushOffInput`:

**`Work.Collar3D.exists_cap_of_discCollar`.**  Let `β : 𝔻 → ℝ³` be an embedded disc with a collar
`c : DiscCollar β`, let `F ⊆ ℝ³` be a surface which, inside the collar, does not enter the `s`-side
of `β` over the interior of the disc (`c.clearOfInteriorSide F s` — the orientation datum of the
transverse pair `(β, F)` along `γ`), and let `e : 𝔻 → ℝ³` be the slice disc, coinciding with `β`
inside the collar (`Set.range e ∩ c.U ⊆ Set.range β`).  Then there is an embedded disc `cap` with

* the same boundary curve as `β`,
* whose interior misses `F` (the point of the push-off), and
* whose interior misses the slice disc `e`.

The cap is the explicit `z ↦ c.Φ.symm (z, s · (1 - ‖z‖))`: the profile vanishes on the boundary
circle and points towards the `s`-side of `β` on the interior, where `F` is not; and it leaves the
slice disc because the slice disc coincides with `β` in the collar.

Nothing else is used: the only classical input left is the existence of the collar `c`, i.e. the
regular-neighbourhood theorem for the locally flat disc `β`
(`Work.Collar3D.RegularNeighbourhoodDisc`), together with the two local side conditions.  The
weaker (stronger-hypothesis) variant with `liesOnOneSide` is
`Work.Collar3D.DiscCollar.cap_notMem_of_liesOnOneSide`.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

namespace DiscCollar

variable {e : C(Disc, R3)} (c : DiscCollar e)

/-- **The cap of a profile pointing to the `s`-side misses a surface which does not enter that side
over the interior of the disc.**  This is the local heart of the push-off. -/
theorem cap_notMem_of_clearOfInteriorSide {F : Set R3} {ψ : Disc → ℝ} {s : ℝ}
    (hψ : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → 0 < s * ψ z)
    (hF : c.clearOfInteriorSide F s) {z : Disc} (hz : ‖(z : ℂ)‖ < 1) :
    c.cap ψ z ∉ F := by
  intro hmem
  have h := hF ((z : ℂ), ψ z) hmem hz
  exact h (hψ z hz)

/-- The cap of a profile which does not vanish on the open disc misses the disc in the interior. -/
theorem cap_notMem_range_of_ne {ψ : Disc → ℝ}
    (hψ : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → ψ z ≠ 0) {z : Disc} (hz : ‖(z : ℂ)‖ < 1) :
    c.cap ψ z ∉ Set.range e :=
  c.cap_notMem_range hψ hz

/-- **A disc agrees with the collar's disc over the interior**: inside the collar, every point of the
disc `e'` whose *disc coordinate* is strictly inside `𝔻` lies on the middle sheet `{p.2 = 0}` of the
collar.

This is the correct local coincidence condition of the push-off, replacing the inclusion
`Set.range e' ∩ c.U ⊆ Set.range e` — which is only satisfiable when `Set.range e' = Set.range e`
(the part of a strictly larger disc accumulates on the boundary curve `∂e` inside the *open* collar
`c.U`), hence useless for the innermost sub-disc of a strictly larger slice disc.  What the cap
actually needs is only that the slice disc does not leave the middle sheet over the interior of the
sub-disc. -/
def agreesOnInterior (e' : C(Disc, R3)) : Prop :=
  ∀ p : ℂ × ℝ, (c.Φ.symm p : R3) ∈ Set.range e' → ‖p.1‖ < 1 → p.2 = 0

/-- The inclusion form of the local coincidence implies the interior form. -/
theorem agreesOnInterior_of_subset {e' : C(Disc, R3)}
    (h : Set.range e' ∩ c.U ⊆ Set.range e) : c.agreesOnInterior e' := by
  intro p hp hz
  have hpU : (c.Φ.symm p : R3) ∈ c.U := (c.Φ.symm p).2
  obtain ⟨z, hz'⟩ := h ⟨hp, hpU⟩
  have hu : c.Φ.symm p = ⟨e z, c.mem_range ⟨z, rfl⟩⟩ := Subtype.ext hz'.symm
  have h2 : p = ((z : ℂ), 0) := by
    rw [← Homeomorph.apply_symm_apply c.Φ p, hu, c.Φ_e z]
  rw [h2]

/-- **The cap misses a disc which agrees with the collar over the interior.** -/
theorem cap_notMem_range_of_agreesOnInterior {e' : C(Disc, R3)} {ψ : Disc → ℝ}
    (hψ : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → ψ z ≠ 0) (h : c.agreesOnInterior e') {z : Disc}
    (hz : ‖(z : ℂ)‖ < 1) : c.cap ψ z ∉ Set.range e' := by
  intro hmem
  exact hψ z hz (h ((z : ℂ), ψ z) hmem hz)

end DiscCollar

/-- The signed profile of the push-off: positive on the interior of the disc, of sign `s`, and
vanishing on the boundary circle. -/
def signedCapProfile (s : ℝ) (z : Disc) : ℝ := s * capProfile z

theorem signedCapProfile_continuous (s : ℝ) : Continuous (signedCapProfile s) :=
  continuous_const.mul capProfile_continuous

@[simp] theorem signedCapProfile_circlePoint (s : ℝ) (θ : ℝ) :
    signedCapProfile s (Work.Smooth.Jordan.circlePoint θ) = 0 := by
  simp [signedCapProfile]

theorem signedCapProfile_pos {s : ℝ} (hs : s ≠ 0) {z : Disc} (hz : ‖(z : ℂ)‖ < 1) :
    0 < s * signedCapProfile s z := by
  have h := capProfile_pos hz
  have hs2 : 0 < s * s := mul_self_pos.mpr hs
  have : s * (s * capProfile z) = (s * s) * capProfile z := by ring
  rw [signedCapProfile, this]
  exact mul_pos hs2 h

theorem signedCapProfile_ne_zero {s : ℝ} (hs : s ≠ 0) {z : Disc} (hz : ‖(z : ℂ)‖ < 1) :
    signedCapProfile s z ≠ 0 := by
  exact mul_ne_zero hs (ne_of_gt (capProfile_pos hz))

/-- **The push-off of the innermost sub-disc: the cap.**  Let `c` be a collar of the disc `β`, let
the surface `F` not enter the `s`-side of `β` over the interior of the disc, and let the slice disc
`e` agree with `β` inside the collar.  Then the explicit cap `z ↦ c.Φ.symm (z, s(1 - ‖z‖))` is an
embedded disc with the same boundary curve as `β` whose interior misses both `F` and the slice
disc `e`.

This discharges the substance of the push-off input `Work.Smooth.PushThrough3D.SurfacePushOffInput`
(the clauses "(a) embedded", "(b) same boundary", "(c) interior off the surface", "(d) interior
meeting the slice disc only along the boundary curve"). -/
theorem exists_cap_of_discCollar {F : Set R3} {e β : C(Disc, R3)} (c : DiscCollar β) (s : ℝ)
    (hs : s ≠ 0) (hside : c.clearOfInteriorSide F s)
    (h_e : c.agreesOnInterior e) :
    ∃ cap : C(Disc, R3), Function.Injective cap ∧
      (∀ θ : ℝ, cap (Work.Smooth.Jordan.circlePoint θ)
        = β (Work.Smooth.Jordan.circlePoint θ)) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ F) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ Set.range e) := by
  refine ⟨⟨c.cap (signedCapProfile s), c.cap_continuous (signedCapProfile_continuous s)⟩,
    c.cap_injective, ?_, ?_, ?_⟩
  · intro θ
    exact c.cap_boundary (fun θ => signedCapProfile_circlePoint s θ) θ
  · intro z hz
    exact c.cap_notMem_of_clearOfInteriorSide (fun w hw => signedCapProfile_pos hs hw) hside hz
  · intro z hz hmem
    exact c.cap_notMem_range_of_agreesOnInterior (fun w hw => signedCapProfile_ne_zero hs hw)
      h_e hz hmem

/-- **The push-off theorem with the inclusion form of the local coincidence** (only satisfiable when
the slice disc *is* the sub-disc, see `Work.Collar3D.DiscCollar.agreesOnInterior`); kept so that
callers holding the inclusion can use it directly. -/
theorem exists_cap_of_discCollar_of_subset {F : Set R3} {e β : C(Disc, R3)} (c : DiscCollar β)
    (s : ℝ) (hs : s ≠ 0) (hside : c.clearOfInteriorSide F s)
    (h_e : Set.range e ∩ c.U ⊆ Set.range β) :
    ∃ cap : C(Disc, R3), Function.Injective cap ∧
      (∀ θ : ℝ, cap (Work.Smooth.Jordan.circlePoint θ)
        = β (Work.Smooth.Jordan.circlePoint θ)) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ F) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ Set.range e) :=
  exists_cap_of_discCollar c s hs hside (c.agreesOnInterior_of_subset h_e)

end

end Work.Collar3D
