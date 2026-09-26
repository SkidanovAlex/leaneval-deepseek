import Submission.Work.Collar3D.PushOff.Basic

/-!
# The push-off of a sub-disc of a slice disc: the cap of Pardon's cut-and-paste

This is the *application* of the disc collar (`Work.Collar3D.DiscCollar`) to the configuration in
which Pardon's cut-and-paste consumes it — the conclusion of the sibling chapter's
`Work.Smooth.PushThrough3D.SurfacePushOffInput`:

let `β : 𝔻 → ℝ³` be an embedded disc whose boundary circle `γ` lies on a surface `F` and whose
interior misses `F` (the *innermost* sub-disc of the slice disc `e`), and let `c : DiscCollar β` be
a collar of `β`.  Assume

* **the side condition** `c.liesOnOneSide F (-1)`: inside the collar, the surface `F` lies on the
  *other* side of `β` — `F ∩ c.U ⊆ β(𝔻) ∪ side (-1)`; locally this is the statement that `β` and
  `F` cross transversely along `γ` with `int β` on the positive side (the shape in which the
  transverse-pair collar of `γ` presents them);
* **the local coincidence** `range e ∩ c.U ⊆ range β`: inside the collar, the slice disc `e` is
  exactly the sub-disc `β` (a consequence of `β` being a sub-disc of `e` and both being
  two-dimensional, for a collar thin enough, i.e. of the collar being adapted to `e`).

Then the cap `z ↦ c.Φ.symm (z, 1 - ‖z‖)` is an embedded disc with the same boundary curve as `β`,
whose interior misses `F` and meets the slice disc only along that curve: the conclusion of
`SurfacePushOffInput`.  The only classical input left is the existence of the collar `c`
(`Work.Collar3D.RegularNeighbourhoodDisc`).
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

namespace DiscCollar

variable {e : C(Disc, R3)} (c : DiscCollar e)

/-- The two sides of a disc collar are disjoint. -/
theorem disjoint_side (s s' : ℝ) (h : s * s' < 0) : Disjoint (c.side s) (c.side s') := by
  rw [Set.disjoint_left]
  intro x hxs hxs'
  have hx : ∃ hx : x ∈ c.U, 0 < s * (c.Φ ⟨x, hx⟩).2 := (DiscCollar.mem_side c s x).mp hxs
  have hx' : ∃ hx : x ∈ c.U, 0 < s' * (c.Φ ⟨x, hx⟩).2 := (DiscCollar.mem_side c s' x).mp hxs'
  obtain ⟨hxU, hx1⟩ := hx
  obtain ⟨_, hx2⟩ := hx'
  have hn0 : (c.Φ ⟨x, hxU⟩).2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hx1
    exact lt_irrefl _ hx1
  have hsq : 0 < (c.Φ ⟨x, hxU⟩).2 ^ 2 := sq_pos_of_ne_zero hn0
  have hprod : 0 < (s * (c.Φ ⟨x, hxU⟩).2) * (s' * (c.Φ ⟨x, hxU⟩).2) := mul_pos hx1 hx2
  nlinarith [hprod, hsq, h]

/-- **`F` lies on one side of the disc inside its collar.**  This is the local position hypothesis
of the cut-and-paste: within the collar, the surface `F` meets the disc `β(𝔻)` only along the
boundary curve and lies on the side of sign `s`. -/
def liesOnOneSide (F : Set R3) (s : ℝ) : Prop :=
  F ∩ c.U ⊆ Set.range e ∪ c.side s

theorem liesOnOneSide_iff (F : Set R3) (s : ℝ) :
    c.liesOnOneSide F s ↔ ∀ x ∈ F, x ∈ c.U → x ∈ Set.range e ∨ x ∈ c.side s := by
  constructor
  · intro h x hxF hxU
    exact h ⟨hxF, hxU⟩
  · intro h x hx
    exact h x hx.1 hx.2

/-- **`F` does not enter the `s`-side of the disc over the interior of the disc.**  A point of `F`
inside the collar whose *disc coordinate* is strictly inside the unit disc has normal coordinate
which is not of sign `s` (`‖(Φ u).1‖ < 1` says that the point projects to the interior of the disc,
and the conclusion says `s · (Φ u).2 ≤ 0`).

This is the local side condition that the push-off actually consumes, and it is *weaker* than
`liesOnOneSide`: a surface crossing the plane of the disc *transversely* along the boundary circle
meets both sides of the disc outside the disc, so `liesOnOneSide` fails there, while over the
interior of the disc it lies on one side — that is exactly the orientation datum of the transverse
pair `(β, F)` along `γ`.  `clearOfInteriorSide_of_liesOnOneSide` records the implication from the
stronger condition. -/
def clearOfInteriorSide (F : Set R3) (s : ℝ) : Prop :=
  ∀ p : ℂ × ℝ, (c.Φ.symm p : R3) ∈ F → ‖p.1‖ < 1 → ¬ 0 < s * p.2

theorem clearOfInteriorSide_iff (F : Set R3) (s : ℝ) :
    c.clearOfInteriorSide F s ↔
      ∀ p : ℂ × ℝ, (c.Φ.symm p : R3) ∈ F → ‖p.1‖ < 1 → ¬ 0 < s * p.2 := Iff.rfl

/-- A surface lying on the `-s`-side of the disc inside the collar does not enter the `s`-side over
the interior of the disc. -/
theorem clearOfInteriorSide_of_liesOnOneSide {F : Set R3} {s : ℝ} (h : c.liesOnOneSide F (-s)) :
    c.clearOfInteriorSide F s := by
  intro p hpF hz hpos
  have hU : (c.Φ.symm p : R3) ∈ c.U := (c.Φ.symm p).2
  rcases (c.liesOnOneSide_iff F (-s)).mp h (c.Φ.symm p : R3) hpF hU with hcase | hcase
  · obtain ⟨z, hzu⟩ := hcase
    have hu : c.Φ.symm p = ⟨e z, c.mem_range ⟨z, rfl⟩⟩ := Subtype.ext hzu.symm
    have h1 : c.Φ (c.Φ.symm p) = ((z : ℂ), 0) := by rw [hu, c.Φ_e]
    rw [Homeomorph.apply_symm_apply] at h1
    rw [h1] at hpos
    simp at hpos
  · obtain ⟨hx, hneg⟩ := hcase
    have heq : (⟨(c.Φ.symm p : R3), hx⟩ : c.U) = c.Φ.symm p := rfl
    rw [heq, Homeomorph.apply_symm_apply] at hneg
    nlinarith

end DiscCollar

/-- The standard profile of the push-off: positive on the interior of the disc and vanishing on
the boundary circle. -/
def capProfile (z : Disc) : ℝ := 1 - ‖(z : ℂ)‖

theorem capProfile_continuous : Continuous capProfile := by
  unfold capProfile
  fun_prop

@[simp] theorem capProfile_circlePoint (θ : ℝ) :
    capProfile (Work.Smooth.Jordan.circlePoint θ) = 0 := by
  have h : ((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ) = Complex.exp (θ * Complex.I) :=
    Work.Smooth.Jordan.circlePoint_coe θ
  rw [capProfile, h, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem capProfile_pos {z : Disc} (hz : ‖(z : ℂ)‖ < 1) : 0 < capProfile z := by
  simp only [capProfile]; linarith

end

end Work.Collar3D
