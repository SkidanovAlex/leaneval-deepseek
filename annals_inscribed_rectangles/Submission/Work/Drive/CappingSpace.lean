import Mathlib
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.ProjectiveDefs
import Submission.Work.Drive.ProjectiveTopology

/-!
# The Heegaard (lens-space) model of the capping of the configuration Möbius strip

Hugelmeyer's fifth auxiliary result caps the configuration Möbius strip `M` of a smooth plane curve by
gluing the boundary torus of the configuration space (minus its axis) to the boundary of a solid torus of
"caps".  In coordinates the gluing is

`f (r, e^{iθ}, e^{iφ}) = (r cos φ, r sin φ, e^{i(2φ + θ)}, 0)`,

i.e. on the boundary tori it is the map `(θ, φ) ↦ (ψ, η) = (φ, θ + 2φ)` of
`Submission.Work.Drive.glueTorus`: the *meridian* of the cap solid torus is glued to the `(2,1)`-torus
knot of the configuration boundary torus (`glueTorus_preimage_t21`).

The glued space is a product except for the radial coordinate:

> `Y = (0,∞) × L`,  `L := (S¹ × D²) ∪_f (D² × S¹)`,

with `f` the torus map above, because the gluing preserves the radius `r`.  `L` is the classical lens
space `L(2,1) = ℝP³` (gluing two solid tori with the meridian of one identified with the `(2,1)`-curve
of the other), whence `Y ≅ ℝ × ℝP³`, Hugelmeyer's Lemma 5.

This file contains the *definitions*: the boundary circle `bdy` of the disk inside `ℂ`, the two solid
tori `CapTorus` (`S¹ × D²`, the cap) and `ConfTorus` (`D² × S¹`, the configuration fibration), the
gluing relation `lensRel` and the glued space `LensSpace`.  The homeomorphism
`LensSpace ≃ₜ Projectivization ℝ (EuclideanSpace ℝ (Fin 4))` (i.e. `L(2,1) ≅ ℝP³`) is the statement
proved on top of this file.
-/

namespace Work.Drive

noncomputable section

open scoped Topology

/-- The canonical parametrisation of the unit circle of `ℂ` by `ℝ/ℤ`: the homeomorphism
`AddCircle.homeomorphCircle` followed by the coercion into `ℂ`. -/
def circleOf (φ : UnitAddCircle) : ℂ :=
  ((AddCircle.homeomorphCircle (T := 1) one_ne_zero) φ : ℂ)

@[simp] lemma norm_circleOf (φ : UnitAddCircle) : ‖circleOf φ‖ = 1 :=
  Circle.norm_coe _

lemma circleOf_injective : Function.Injective circleOf := fun a b h =>
  (AddCircle.homeomorphCircle (T := 1) one_ne_zero).injective (Subtype.ext h)

/-- The real part of `circleOf`, in terms of the angle in turns: this is the component form of the
identification of `circleOf` with the standard parametrisation of the unit circle. -/
lemma circleOf_coe_re (t : ℝ) :
    (circleOf ((t : ℝ) : UnitAddCircle) : ℂ).re = Real.cos (2 * Real.pi * t) := by
  rw [circleOf, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk (T := 1),
    Circle.coe_exp, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Real.exp_zero, one_mul]
  congr 1
  ring

/-- The imaginary part of `circleOf`, in terms of the angle in turns. -/
lemma circleOf_coe_im (t : ℝ) :
    (circleOf ((t : ℝ) : UnitAddCircle) : ℂ).im = Real.sin (2 * Real.pi * t) := by
  rw [circleOf, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk (T := 1),
    Circle.coe_exp, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Real.exp_zero, one_mul]
  congr 1
  ring

/-- **The polar lift of `Submission.Work.Drive.CappingDefs` is `r` times the boundary point.**  This
identifies the position-angle coordinate of the configuration boundary torus with the boundary circle
parametrisation `circleOf` used for the solid tori of the capping. -/
lemma polarLift_eq_circleOf (r t : ℝ) :
    (⟨(Work.Drive.polarLift (r, t)).1, (Work.Drive.polarLift (r, t)).2⟩ : ℂ) =
      (r : ℂ) * (circleOf ((t : ℝ) : UnitAddCircle) : ℂ) := by
  rw [Work.Drive.polarLift]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, circleOf_coe_re, circleOf_coe_im]

/-- The point of the boundary circle of the closed unit disk of `ℂ` of angle `φ ∈ ℝ/ℤ`. -/
def bdy (φ : UnitAddCircle) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨circleOf φ, by simp [Metric.mem_closedBall, norm_circleOf]⟩

@[simp] lemma bdy_coe (φ : UnitAddCircle) :
    ((bdy φ : Metric.closedBall (0 : ℂ) 1) : ℂ) = circleOf φ := rfl

lemma bdy_injective : Function.Injective bdy := fun a b h =>
  circleOf_injective (by simpa using congrArg Subtype.val h)

/-- The cap solid torus `S¹ × D²`, with coordinates `(θ, z)`: the `S¹`-coordinate `θ` of the cap and
the disk coordinate `z`.  Its core is `S¹ × {0}` and its meridian circles are `{θ = θ₀} × ∂D²`. -/
abbrev CapTorus : Type := UnitAddCircle × Metric.closedBall (0 : ℂ) 1

/-- The configuration solid torus `D² × S¹` (one fibre of the solid-torus fibration of the
configuration space minus its axis), with coordinates `(z, η)`: the normalised midpoint/length
coordinate `z` and the doubled direction `η`.  Its core is `{0} × S¹` and its meridian circles are
`∂D² × {η = η₀}`. -/
abbrev ConfTorus : Type := Metric.closedBall (0 : ℂ) 1 × UnitAddCircle

/-- The boundary-identification relation of the capping: the cap boundary point `(θ, φ)` is glued to
the configuration boundary point `(φ, θ + 2φ)` — the meridian `{θ = const}` of the cap becoming the
`(2,1)`-curve of the configuration torus (`glueTorus_preimage_t21`). -/
def lensRel (x y : CapTorus ⊕ ConfTorus) : Prop :=
  x = y ∨ ∃ (θ φ : UnitAddCircle),
    (x = Sum.inl (θ, bdy φ) ∧ y = Sum.inr (bdy φ, θ + 2 • φ)) ∨
    (y = Sum.inl (θ, bdy φ) ∧ x = Sum.inr (bdy φ, θ + 2 • φ))

lemma lensRel_refl (x : CapTorus ⊕ ConfTorus) : lensRel x x := Or.inl rfl

lemma lensRel_symm {x y : CapTorus ⊕ ConfTorus} (h : lensRel x y) : lensRel y x := by
  rcases h with h | ⟨θ, φ, h | h⟩
  · exact Or.inl h.symm
  · obtain ⟨hx, hy⟩ := h
    exact Or.inr ⟨θ, φ, Or.inr ⟨hx, hy⟩⟩
  · obtain ⟨hy, hx⟩ := h
    exact Or.inr ⟨θ, φ, Or.inl ⟨hy, hx⟩⟩

lemma inl_ne_inr {A B : Type*} {a : A} {b : B} : (Sum.inl a : A ⊕ B) ≠ Sum.inr b :=
  fun h => by cases h

lemma inr_ne_inl {A B : Type*} {a : A} {b : B} : (Sum.inr b : A ⊕ B) ≠ Sum.inl a :=
  fun h => by cases h

lemma lensRel_trans {x y z : CapTorus ⊕ ConfTorus} (h1 : lensRel x y) (h2 : lensRel y z) :
    lensRel x z := by
  rcases h1 with hxy | ⟨θ, φ, hxy | hxy⟩
  · subst hxy; exact h2
  · -- `x = inl (θ, bdy φ)`, `y = inr (bdy φ, θ + 2 • φ)`
    obtain ⟨hx, hy⟩ := hxy
    rcases h2 with hyz | ⟨θ', φ', hyz | hyz⟩
    · subst hyz; exact Or.inr ⟨θ, φ, Or.inl ⟨hx, hy⟩⟩
    · obtain ⟨hy', _⟩ := hyz
      have hbad : (Sum.inr (bdy φ, θ + 2 • φ) : CapTorus ⊕ ConfTorus) = Sum.inl (θ', bdy φ') :=
        hy.symm.trans hy'
      exact absurd hbad inr_ne_inl
    · obtain ⟨hz, hy'⟩ := hyz
      have hyy : Sum.inr (bdy φ, θ + 2 • φ) = Sum.inr (bdy φ', θ' + 2 • φ') := hy.symm.trans hy'
      simp only [Sum.inr.injEq, Prod.mk.injEq] at hyy
      obtain ⟨hφ, hη⟩ := hyy
      have hφ' : φ = φ' := bdy_injective hφ
      subst hφ'
      have hθ : θ = θ' := add_right_cancel hη
      subst hθ
      exact Or.inl (hx.trans hz.symm)
  · -- `y = inl (θ, bdy φ)`, `x = inr (bdy φ, θ + 2 • φ)`
    obtain ⟨hy, hx⟩ := hxy
    rcases h2 with hyz | ⟨θ', φ', hyz | hyz⟩
    · subst hyz; exact Or.inr ⟨θ, φ, Or.inr ⟨hy, hx⟩⟩
    · obtain ⟨hy', hz⟩ := hyz
      have hyy : Sum.inl (θ, bdy φ) = Sum.inl (θ', bdy φ') := hy.symm.trans hy'
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hyy
      obtain ⟨hθ, hφ⟩ := hyy
      have hφ' : φ = φ' := bdy_injective hφ
      subst hφ'
      subst hθ
      exact Or.inl (hx.trans hz.symm)
    · obtain ⟨_, hy'⟩ := hyz
      have hbad : (Sum.inl (θ, bdy φ) : CapTorus ⊕ ConfTorus) = Sum.inr (bdy φ', θ' + 2 • φ') :=
        hy.symm.trans hy'
      exact absurd hbad inl_ne_inr

/-- **The glued space of the capping, in its three-dimensional (Heegaard) presentation.** -/
def lensSetoid : Setoid (CapTorus ⊕ ConfTorus) where
  r := lensRel
  iseqv := ⟨lensRel_refl, fun {_ _} => lensRel_symm, fun {_ _ _} => lensRel_trans⟩

/-- **The lens space `L(2,1)` of the capping**: the quotient of the disjoint union of the cap solid
torus and the configuration solid torus by the boundary identification `lensRel`.  The full capping
space of Hugelmeyer's Lemma 5 is `(0,∞) × LensSpace`, and the statement proved on top of this file is
`LensSpace ≃ₜ ℝP³`. -/
abbrev LensSpace : Type := Quotient lensSetoid

lemma continuous_lensMk : Continuous (Quotient.mk'' : CapTorus ⊕ ConfTorus → LensSpace) :=
  isQuotientMap_quotient_mk'.continuous

/-! ## The four-dimensional capping space

The gluing `glueSpace` of `Submission.Work.Drive.CappingDefs` preserves the radial coordinate
`r = ‖(midpoint, length)‖`, so the capping space is the product of `(0,∞)` (the radial direction, whose
two ends are the `±λ` ends of the paper's model `ℝ × ℝP³`) with the *slice* glued above.  In the
polar coordinates of the configuration fibration (`cappingFibration`,
`cappingRadial_identification`) the configuration piece is `(0,∞) × D² × S¹` (the second factor being
the normalised midpoint/length vector in the closed hemisphere, which we identify with the closed unit
disk of `ℂ` by forgetting the third coordinate) and the cap piece is `(0,∞) × S¹ × D²`; the gluing
identifies `(r, circleOf φ, θ + 2 • φ)` with `(r, θ, circleOf φ)`.  Both pieces keep the radial
coordinate, so the relation only ever relates points with the same `r`. -/

/-- The configuration piece in polar coordinates: `(0,∞) × D² × S¹` (radial coordinate, normalised
midpoint/length vector in the closed hemisphere `≅` closed unit disk of `ℂ`, doubled direction). -/
abbrev ConfigPiece : Type := {q : ℝ × ℂ × UnitAddCircle // 0 < q.1 ∧ ‖q.2.1‖ ≤ 1}

/-- The cap piece: `(0,∞) × S¹ × D²` (radial coordinate, the cap's `S¹` coordinate `θ`, the disk
coordinate). -/
abbrev CapPiece : Type := {q : ℝ × UnitAddCircle × ℂ // 0 < q.1 ∧ ‖q.2.2‖ ≤ 1}

/-- The boundary point of the configuration piece with parameters `(r, φ, η)`: the normalised
midpoint/length vector lies on the equator (the boundary circle of the hemisphere), at angle `φ`. -/
def confBdy (r : ℝ) (hr : 0 < r) (φ η : UnitAddCircle) : ConfigPiece :=
  ⟨(r, circleOf φ, η), ⟨hr, by rw [norm_circleOf]⟩⟩

/-- The boundary point of the cap piece with parameters `(r, θ, φ)`. -/
def capBdy (r : ℝ) (hr : 0 < r) (θ φ : UnitAddCircle) : CapPiece :=
  ⟨(r, θ, circleOf φ), ⟨hr, by rw [norm_circleOf]⟩⟩

@[simp] lemma confBdy_val (r : ℝ) (hr : 0 < r) (φ η : UnitAddCircle) :
    (confBdy r hr φ η : ℝ × ℂ × UnitAddCircle) = (r, circleOf φ, η) := rfl

@[simp] lemma capBdy_val (r : ℝ) (hr : 0 < r) (θ φ : UnitAddCircle) :
    (capBdy r hr θ φ : ℝ × UnitAddCircle × ℂ) = (r, θ, circleOf φ) := rfl

/-- The boundary identification of the four-dimensional capping: the configuration boundary point
`(r, φ, θ + 2φ)` is glued to the cap boundary point `(r, θ, φ)` — the meridian `{θ = const}` of the cap
becoming the `(2,1)`-curve of the configuration torus (`glueTorus_preimage_t21`), at every radial
value `r > 0`. -/
def cappingRel (x y : ConfigPiece ⊕ CapPiece) : Prop :=
  x = y ∨ ∃ (r : ℝ) (hr : 0 < r) (θ φ : UnitAddCircle),
    (x = Sum.inl (confBdy r hr φ (θ + 2 • φ)) ∧ y = Sum.inr (capBdy r hr θ φ)) ∨
    (y = Sum.inl (confBdy r hr φ (θ + 2 • φ)) ∧ x = Sum.inr (capBdy r hr θ φ))

lemma cappingRel_refl (x : ConfigPiece ⊕ CapPiece) : cappingRel x x := Or.inl rfl

lemma cappingRel_symm {x y : ConfigPiece ⊕ CapPiece} (h : cappingRel x y) : cappingRel y x := by
  rcases h with h | ⟨r, hr, θ, φ, h | h⟩
  · exact Or.inl h.symm
  · obtain ⟨hx, hy⟩ := h
    exact Or.inr ⟨r, hr, θ, φ, Or.inr ⟨hx, hy⟩⟩
  · obtain ⟨hy, hx⟩ := h
    exact Or.inr ⟨r, hr, θ, φ, Or.inl ⟨hy, hx⟩⟩

lemma confBdy_inj {r r' : ℝ} {hr : 0 < r} {hr' : 0 < r'} {φ η φ' η' : UnitAddCircle}
    (h : confBdy r hr φ η = confBdy r' hr' φ' η') : r = r' ∧ φ = φ' ∧ η = η' := by
  have h' := congrArg Subtype.val h
  simp only [confBdy_val, Prod.mk.injEq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  exact ⟨h1, circleOf_injective h2, h3⟩

lemma capBdy_inj {r r' : ℝ} {hr : 0 < r} {hr' : 0 < r'} {θ φ θ' φ' : UnitAddCircle}
    (h : capBdy r hr θ φ = capBdy r' hr' θ' φ') : r = r' ∧ θ = θ' ∧ φ = φ' := by
  have h' := congrArg Subtype.val h
  simp only [capBdy_val, Prod.mk.injEq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  exact ⟨h1, h2, circleOf_injective h3⟩

lemma cappingRel_trans {x y z : ConfigPiece ⊕ CapPiece} (h1 : cappingRel x y)
    (h2 : cappingRel y z) : cappingRel x z := by
  rcases h1 with hxy | ⟨r, hr, θ, φ, hxy | hxy⟩
  · subst hxy; exact h2
  · obtain ⟨hx, hy⟩ := hxy
    rcases h2 with hyz | ⟨r', hr', θ', φ', hyz | hyz⟩
    · subst hyz; exact Or.inr ⟨r, hr, θ, φ, Or.inl ⟨hx, hy⟩⟩
    · obtain ⟨hy', _⟩ := hyz
      have hbad : (Sum.inr (capBdy r hr θ φ) : ConfigPiece ⊕ CapPiece) =
          Sum.inl (confBdy r' hr' φ' (θ' + 2 • φ')) := hy.symm.trans hy'
      exact absurd hbad inr_ne_inl
    · obtain ⟨hz, hy'⟩ := hyz
      have hyy : capBdy r hr θ φ = capBdy r' hr' θ' φ' := by
        have h := hy.symm.trans hy'
        simpa only [Sum.inr.injEq] using h
      obtain ⟨hrr, hθθ, hφφ⟩ := capBdy_inj hyy
      subst hrr; subst hθθ; subst hφφ
      exact Or.inl (hx.trans hz.symm)
  · obtain ⟨hy, hx⟩ := hxy
    rcases h2 with hyz | ⟨r', hr', θ', φ', hyz | hyz⟩
    · subst hyz; exact Or.inr ⟨r, hr, θ, φ, Or.inr ⟨hy, hx⟩⟩
    · obtain ⟨hy', hz⟩ := hyz
      have hyy : confBdy r hr φ (θ + 2 • φ) = confBdy r' hr' φ' (θ' + 2 • φ') := by
        have h := hy.symm.trans hy'
        simpa only [Sum.inl.injEq] using h
      obtain ⟨hrr, hφφ, hηη⟩ := confBdy_inj hyy
      subst hrr; subst hφφ
      have hθθ : θ + 2 • φ = θ' + 2 • φ := hηη
      have : θ = θ' := add_right_cancel hθθ
      subst this
      exact Or.inl (hx.trans hz.symm)
    · obtain ⟨_, hy'⟩ := hyz
      have hbad : (Sum.inl (confBdy r hr φ (θ + 2 • φ)) : ConfigPiece ⊕ CapPiece) =
          Sum.inr (capBdy r' hr' θ' φ') := hy.symm.trans hy'
      exact absurd hbad inl_ne_inr

/-- **The four-dimensional capping space**: `(0,∞) × LensSpace`, presented as the quotient of the
configuration piece and the cap piece by the boundary identification `cappingRel`. -/
def cappingSetoid : Setoid (ConfigPiece ⊕ CapPiece) where
  r := cappingRel
  iseqv := ⟨cappingRel_refl, fun {_ _} => cappingRel_symm, fun {_ _ _} => cappingRel_trans⟩

abbrev CappingSpace : Type := Quotient cappingSetoid

lemma continuous_cappingMk : Continuous (Quotient.mk'' : ConfigPiece ⊕ CapPiece → CappingSpace) :=
  isQuotientMap_quotient_mk'.continuous

/-! ## The rotation action

The `S¹`-rotation of Hugelmeyer's configuration space acts on the configuration piece by adding the
angle to the *doubled direction* and on the cap piece by adding it to the cap's `S¹` coordinate.  By
`Submission.Work.Drive.glueSpace` these two actions match on the glued boundary tori (the gluing sends
`(θ, φ)` to the configuration point with direction `2φ + θ`, so adding `v` to `θ` — respectively to the
direction — gives the same identification), hence the rotation descends to the four-dimensional capping
space.  This is what makes the order relation of `Work.Drive.StripRel` invariant under simultaneous
rotation of the planes. -/

/-- The rotation of the cap torus: addition of the angle to the cap's `S¹` coordinate. -/
def rotCapTorus (v : UnitAddCircle) (p : CapTorus) : CapTorus := (p.1 + v, p.2)

/-- The rotation of the configuration torus: addition of the angle to the doubled direction. -/
def rotConfTorus (v : UnitAddCircle) (p : ConfTorus) : ConfTorus := (p.1, p.2 + v)

/-- The rotation on the disjoint union of the two solid tori of the slice. -/
def rotLensSum (v : UnitAddCircle) : CapTorus ⊕ ConfTorus → CapTorus ⊕ ConfTorus
  | Sum.inl p => Sum.inl (rotCapTorus v p)
  | Sum.inr p => Sum.inr (rotConfTorus v p)

/-- The rotation of the configuration piece: addition of the angle to the doubled direction. -/
def rotConfig (v : UnitAddCircle) (p : ConfigPiece) : ConfigPiece :=
  ⟨(p.1.1, p.1.2.1, p.1.2.2 + v), p.2⟩

/-- The rotation of the cap piece: addition of the angle to the cap's `S¹` coordinate. -/
def rotCap (v : UnitAddCircle) (p : CapPiece) : CapPiece :=
  ⟨(p.1.1, p.1.2.1 + v, p.1.2.2), p.2⟩

/-- The rotation on the disjoint union of the two pieces of the four-dimensional capping. -/
def rotSum (v : UnitAddCircle) : ConfigPiece ⊕ CapPiece → ConfigPiece ⊕ CapPiece
  | Sum.inl p => Sum.inl (rotConfig v p)
  | Sum.inr p => Sum.inr (rotCap v p)

@[simp] lemma rotSum_inl (v : UnitAddCircle) (p : ConfigPiece) :
    rotSum v (Sum.inl p) = Sum.inl (rotConfig v p) := rfl

@[simp] lemma rotSum_inr (v : UnitAddCircle) (p : CapPiece) :
    rotSum v (Sum.inr p) = Sum.inr (rotCap v p) := rfl

@[simp] lemma rotLensSum_inl (v : UnitAddCircle) (p : CapTorus) :
    rotLensSum v (Sum.inl p) = Sum.inl (rotCapTorus v p) := rfl

@[simp] lemma rotLensSum_inr (v : UnitAddCircle) (p : ConfTorus) :
    rotLensSum v (Sum.inr p) = Sum.inr (rotConfTorus v p) := rfl

/-- **The boundary identification of the slice is invariant under rotation.** -/
theorem lensRel_rot (v : UnitAddCircle) {x y : CapTorus ⊕ ConfTorus}
    (h : lensRel x y) : lensRel (rotLensSum v x) (rotLensSum v y) := by
  rcases h with h | ⟨θ, φ, h | h⟩
  · subst h; exact Or.inl rfl
  · obtain ⟨hx, hy⟩ := h
    subst hx; subst hy
    refine Or.inr ⟨θ + v, φ, Or.inl ⟨?_, ?_⟩⟩
    · show Sum.inl (rotCapTorus v (θ, bdy φ)) = Sum.inl ((θ + v, bdy φ) : CapTorus)
      rfl
    · show Sum.inr (rotConfTorus v (bdy φ, θ + 2 • φ)) =
        Sum.inr ((bdy φ, θ + v + 2 • φ) : ConfTorus)
      rw [Sum.inr.injEq, rotConfTorus]
      exact Prod.ext rfl (by ac_rfl)
  · obtain ⟨hy, hx⟩ := h
    subst hx; subst hy
    refine Or.inr ⟨θ + v, φ, Or.inr ⟨?_, ?_⟩⟩
    · show Sum.inl (rotCapTorus v (θ, bdy φ)) = Sum.inl ((θ + v, bdy φ) : CapTorus)
      rfl
    · show Sum.inr (rotConfTorus v (bdy φ, θ + 2 • φ)) =
        Sum.inr ((bdy φ, θ + v + 2 • φ) : ConfTorus)
      rw [Sum.inr.injEq, rotConfTorus]
      exact Prod.ext rfl (by ac_rfl)

/-- **The boundary identification of the four-dimensional capping is invariant under rotation.** -/
theorem cappingRel_rot (v : UnitAddCircle) {x y : ConfigPiece ⊕ CapPiece}
    (h : cappingRel x y) : cappingRel (rotSum v x) (rotSum v y) := by
  rcases h with h | ⟨r, hr, θ, φ, h | h⟩
  · subst h; exact Or.inl rfl
  · obtain ⟨hx, hy⟩ := h
    subst hx; subst hy
    refine Or.inr ⟨r, hr, θ + v, φ, Or.inl ⟨?_, ?_⟩⟩
    · show Sum.inl (rotConfig v (confBdy r hr φ (θ + 2 • φ))) =
        Sum.inl (confBdy r hr φ (θ + v + 2 • φ))
      show Sum.inl (confBdy r hr φ ((θ + 2 • φ) + v)) =
        Sum.inl (confBdy r hr φ (θ + v + 2 • φ))
      rw [show (θ + 2 • φ) + v = θ + v + 2 • φ by abel]
    · show Sum.inr (rotCap v (capBdy r hr θ φ)) = Sum.inr (capBdy r hr (θ + v) φ)
      rfl
  · obtain ⟨hy, hx⟩ := h
    subst hx; subst hy
    refine Or.inr ⟨r, hr, θ + v, φ, Or.inr ⟨?_, ?_⟩⟩
    · show Sum.inl (rotConfig v (confBdy r hr φ (θ + 2 • φ))) =
        Sum.inl (confBdy r hr φ (θ + v + 2 • φ))
      show Sum.inl (confBdy r hr φ ((θ + 2 • φ) + v)) =
        Sum.inl (confBdy r hr φ (θ + v + 2 • φ))
      rw [show (θ + 2 • φ) + v = θ + v + 2 • φ by abel]
    · show Sum.inr (rotCap v (capBdy r hr θ φ)) = Sum.inr (capBdy r hr (θ + v) φ)
      rfl

end

end Work.Drive
