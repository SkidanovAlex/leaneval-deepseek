import Mathlib
import ChallengeDeps
import Submission.Work.Smooth.Jordan.Defs
import Submission.Work.InnermostDisk.Defs
import Submission.Work.Topology.Classical.Defs
import Submission.Work.Smooth.PushThrough3D.Defs

/-!
# `Work.Collar3D` — the local three-dimensional topology of a locally flat surface in `ℝ³`

This is the chapter of the *collar* (regular neighbourhood) toolkit for a locally flat surface
`F ⊆ ℝ³`: the structure that Mathlib does not have and that both remaining inputs of Pardon's
theorem consume.

## What a collar is

* `Work.Collar3D.Collar F γ` — a **collar of the surface `F` along the curve `γ`**: an open
  neighbourhood `U` of `γ` and a homeomorphism `Φ : U ≃ₜ S¹ × ℝ × ℝ` carrying `γ` to the core
  circle `S¹ × {0} × {0}` and `F ∩ U` onto the "middle sheet" `S¹ × ℝ × {0}`.  Since the model
  has *two* normal coordinates, a collar is two-sided: it simultaneously carries a neighbourhood
  of `γ` in `F` to the annulus `S¹ × ℝ × {0}` and exhibits the two sides of `F`.
* `Work.Collar3D.DiscCollar e` — a **collar of an embedded disc `e`**: an open neighbourhood `U`
  of the disc and a homeomorphism `Φ : U ≃ₜ ℂ × ℝ` carrying the disc to `ℂ × {0}` and `e` to the
  standard parametrisation `z ↦ (z, 0)`.  This is the *bicollar of a disc*, the datum from which
  the push-off ("cap") of Pardon's surgery is constructed.

## The names of the pieces

Both structures come with the pieces that the applications consume
(`Collar.surfacePiece`, `Collar.offsetPiece`, `Collar.sideAbove`, `Collar.sideBelow`): the part of
the surface carried by an interval of the collar parameter, the same piece pushed to a level
`ε ≠ 0` of the normal coordinate (the *push-off* of a piece of the surface), and the two open
sides of the surface inside the collar.

## Conventions

* `R3 = EuclideanSpace ℝ (Fin 3)`, written `Work.Collar3D.R3`;
* the circle is `Work.Smooth.Jordan.Circ = Metric.sphere (0 : ℂ) 1`, written
  `Work.Collar3D.Circle`, and `circlePoint θ = e^{iθ}` is its standard `2π`-periodic
  parametrisation (`Work.Collar3D.circlePoint`), matching the workspace convention for closed
  curves (`γ : ℝ → R3` continuous, `2π`-periodic, injective on `[0, 2π)`);
* the model disc is `Work.Smooth.Jordan.Disc = Metric.closedBall (0 : ℂ) 1`;
* local flatness (tameness) of a surface is the notion of the sibling chapter
  `Work.Smooth.PushThrough3D` (`LocallyFlatSetAt`, `LocallyFlatSet`), imported here so that the
  collar theorem can be stated in the vocabulary in which it is consumed.
-/

open Set

namespace Work.Collar3D

noncomputable section

/-- The ambient Euclidean space `ℝ³`. -/
abbrev R3 : Type := LeanEval.KnotTheory.PardonDistortion.R3

/-- The model circle `S¹ = {z : ℂ | ‖z‖ = 1}`, in the workspace convention. -/
abbrev Circle : Type := Work.Smooth.Jordan.Circ

/-- The model disc `𝔻 = {z : ℂ | ‖z‖ ≤ 1}`. -/
abbrev Disc : Type := Work.Smooth.Jordan.Disc

/-- The standard `2π`-periodic parametrisation `θ ↦ e^{iθ}` of the circle `S¹`. -/
def circlePoint (θ : ℝ) : Circle :=
  ⟨(Work.Smooth.Jordan.circlePoint θ : ℂ), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact Complex.norm_exp_ofReal_mul_I θ⟩

@[simp] theorem circlePoint_coe (θ : ℝ) :
    ((circlePoint θ : Circle) : ℂ) = Complex.exp (θ * Complex.I) := rfl

/-! ## Simple closed curves in `ℝ³` -/

/-- A **simple closed curve** in `ℝ³`, in the convention of the workspace: a continuous
`2π`-periodic map which is injective on one period `[0, 2π)`. -/
def IsCircleCurve (γ : ℝ → R3) : Prop :=
  Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧ Set.InjOn γ (Set.Ico 0 (2 * Real.pi))

theorem IsCircleCurve.continuous {γ : ℝ → R3} (h : IsCircleCurve γ) : Continuous γ := h.1
theorem IsCircleCurve.periodic {γ : ℝ → R3} (h : IsCircleCurve γ) :
    Function.Periodic γ (2 * Real.pi) := h.2.1
theorem IsCircleCurve.injOn {γ : ℝ → R3} (h : IsCircleCurve γ) :
    Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) := h.2.2

/-! ## The collar of a surface along a curve -/

/-- **A collar of the surface `F` along the curve `γ`.**

`U` is an open neighbourhood of `γ` and `Φ` is a homeomorphism of `U` onto the model
`S¹ × ℝ × ℝ` which carries

* the curve `γ` to the core circle `S¹ × {0} × {0}` (in the given parametrisation), and
* the surface `F ∩ U` onto the middle sheet `S¹ × ℝ × {0}`.

Consequently `F ∩ U` is an open annulus and the curve `γ` is its core: the collar exhibits both
a neighbourhood of `γ` *in* the surface and the two *sides* of the surface inside `U`, which is
what the local surgery of Pardon's argument runs on.  The existence of such a collar for a
locally flat (tame) surface, along a curve with an annular neighbourhood, is the
regular-neighbourhood theorem (see `Work.Collar3D.RegularNeighbourhoodCurve`). -/
structure Collar (F : Set R3) (γ : ℝ → R3) where
  /-- the open neighbourhood of the curve -/
  U : Set R3
  /-- it is open -/
  isOpen_U : IsOpen U
  /-- it contains the curve -/
  mem_γ : ∀ θ : ℝ, γ θ ∈ U
  /-- the product chart -/
  Φ : U ≃ₜ Circle × ℝ × ℝ
  /-- the chart carries the curve to the core circle -/
  Φ_γ : ∀ θ : ℝ, Φ ⟨γ θ, mem_γ θ⟩ = (circlePoint θ, 0, 0)
  /-- the chart carries the surface onto the middle sheet -/
  Φ_F : ∀ u : U, (u : R3) ∈ F ↔ (Φ u).2.2 = 0

/-- **There is a collar of `F` along `γ`.** -/
def HasCollar (F : Set R3) (γ : ℝ → R3) : Prop := Nonempty (Collar F γ)

namespace Collar

variable {F : Set R3} {γ : ℝ → R3} (c : Collar F γ)
include c

/-- The curve of a collar lies on the surface. -/
theorem γ_mem (θ : ℝ) : γ θ ∈ F :=
  (c.Φ_F ⟨γ θ, c.mem_γ θ⟩).mpr (by rw [c.Φ_γ θ])

/-- The collar chart, applied to a point of the surface. -/
theorem Φ_F_iff (u : c.U) : (u : R3) ∈ F ↔ (c.Φ u).2.2 = 0 := c.Φ_F u

/-- A point of the model with vanishing normal coordinate lies on the surface. -/
theorem Φ_symm_mem_of_zero (p : Circle × ℝ × ℝ) (hp : p.2.2 = 0) :
    (c.Φ.symm p : R3) ∈ F :=
  (c.Φ_F (c.Φ.symm p)).mpr (by rw [Homeomorph.apply_symm_apply]; exact hp)

/-- **The piece of the surface carried by the collar between the levels `a` and `b`** (the
`s`-parameter of the collar runs along the surface): `S¹ × (a,b) × {0}` pulled back. -/
def surfacePiece (a b : ℝ) : Set R3 :=
  {x : R3 | ∃ hx : x ∈ c.U,
    (c.Φ ⟨x, hx⟩).2.1 ∈ Set.Ioo a b ∧ (c.Φ ⟨x, hx⟩).2.2 = 0}

/-- **The piece of the surface carried by the collar, pushed to the level `ε` in the normal
direction**: `S¹ × (a,b) × {ε}` pulled back.  For `ε ≠ 0` this is a piece parallel to the surface
and disjoint from it; it is the shape of the *push-off* of a piece of the surface along a
collar. -/
def offsetPiece (a b ε : ℝ) : Set R3 :=
  {x : R3 | ∃ hx : x ∈ c.U,
    (c.Φ ⟨x, hx⟩).2.1 ∈ Set.Ioo a b ∧ (c.Φ ⟨x, hx⟩).2.2 = ε}

/-- The **upper side** of the surface inside the collar. -/
def sideAbove : Set R3 := {x : R3 | ∃ hx : x ∈ c.U, 0 < (c.Φ ⟨x, hx⟩).2.2}

/-- The **lower side** of the surface inside the collar. -/
def sideBelow : Set R3 := {x : R3 | ∃ hx : x ∈ c.U, (c.Φ ⟨x, hx⟩).2.2 < 0}

theorem mem_surfacePiece (a b : ℝ) {x : R3} :
    x ∈ c.surfacePiece a b ↔ ∃ hx : x ∈ c.U,
      (c.Φ ⟨x, hx⟩).2.1 ∈ Set.Ioo a b ∧ (c.Φ ⟨x, hx⟩).2.2 = 0 := Iff.rfl

theorem mem_offsetPiece (a b ε : ℝ) {x : R3} :
    x ∈ c.offsetPiece a b ε ↔ ∃ hx : x ∈ c.U,
      (c.Φ ⟨x, hx⟩).2.1 ∈ Set.Ioo a b ∧ (c.Φ ⟨x, hx⟩).2.2 = ε := Iff.rfl

theorem mem_sideAbove {x : R3} :
    x ∈ c.sideAbove ↔ ∃ hx : x ∈ c.U, 0 < (c.Φ ⟨x, hx⟩).2.2 := Iff.rfl

theorem mem_sideBelow {x : R3} :
    x ∈ c.sideBelow ↔ ∃ hx : x ∈ c.U, (c.Φ ⟨x, hx⟩).2.2 < 0 := Iff.rfl

/-- The piece of the surface carried by the collar lies on the surface. -/
theorem surfacePiece_subset_F (a b : ℝ) : c.surfacePiece a b ⊆ F := by
  rintro x ⟨hx, -, h0⟩
  exact (c.Φ_F ⟨x, hx⟩).mpr h0

/-- The piece of the surface carried by the collar lies in the collar. -/
theorem surfacePiece_subset_U (a b : ℝ) : c.surfacePiece a b ⊆ c.U :=
  fun x hx => hx.1

/-- The offset piece lies in the collar. -/
theorem offsetPiece_subset_U (a b ε : ℝ) : c.offsetPiece a b ε ⊆ c.U :=
  fun x hx => hx.1

/-- A point of the offset piece at level `ε ≠ 0` is off the surface. -/
theorem offsetPiece_notMem_F (a b ε : ℝ) (hε : ε ≠ 0) : c.offsetPiece a b ε ∩ F = ∅ := by
  ext x
  constructor
  · rintro ⟨hx, hxF⟩
    exact hε (hx.2.2 ▸ (c.Φ_F ⟨x, hx.1⟩).mp hxF)
  · intro h
    exact h.elim

/-- The core circle of the collar, as a subset of the surface: the image of `γ`. -/
theorem range_γ_subset_surfacePiece {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    Set.range γ ⊆ c.surfacePiece a b := by
  rintro x ⟨θ, rfl⟩
  refine ⟨c.mem_γ θ, ?_, ?_⟩
  · rw [c.Φ_γ θ]; exact ⟨ha, hb⟩
  · rw [c.Φ_γ θ]

end Collar

/-! ## The collar of an embedded disc -/

/-- **A collar (bicollar) of an embedded disc `e : 𝔻 → ℝ³`.**

`U` is an open neighbourhood of the disc and `Φ : U ≃ₜ ℂ × ℝ` is a homeomorphism carrying the
disc onto the plane `ℂ × {0}` and the parametrisation `e` to the standard one `z ↦ (z, 0)`; the
second coordinate of `Φ` is the *normal coordinate* of the disc, and its sign labels the two
sides of the disc.

This is the datum from which the push-off ("cap") of Pardon's surgery is built: if `ψ : 𝔻 → ℝ`
is a continuous function vanishing exactly on the boundary circle `∂𝔻`, then

`z ↦ Φ.symm (z, ψ z)`

is an embedded disc with the same boundary curve as `e`, disjoint from `e` except along that
curve, and lying on the side of `e` prescribed by the sign of `ψ`
(`Work.Collar3D.DiscCollar.cap`). -/
structure DiscCollar (e : C(Disc, R3)) where
  /-- the open neighbourhood of the disc -/
  U : Set R3
  /-- it is open -/
  isOpen_U : IsOpen U
  /-- it contains the disc -/
  mem_range : Set.range e ⊆ U
  /-- the product chart -/
  Φ : U ≃ₜ ℂ × ℝ
  /-- the chart carries the parametrisation `e` to the standard parametrisation of `ℂ × {0}` -/
  Φ_e : ∀ z : Disc, Φ ⟨e z, mem_range ⟨z, rfl⟩⟩ = ((z : ℂ), 0)
  /-- the chart carries the disc onto the standard disc of the middle sheet -/
  Φ_range : ∀ u : U, ((u : R3) ∈ Set.range e ↔ ∃ z : Disc, Φ u = ((z : ℂ), 0))

/-- **There is a collar of the disc `e`.** -/
def HasDiscCollar (e : C(Disc, R3)) : Prop := Nonempty (DiscCollar e)

namespace DiscCollar

variable {e : C(Disc, R3)} (c : DiscCollar e)
include c

/-- The chart `Φ` recovers the parametrisation on the middle sheet. -/
theorem Φ_symm_zero (z : Disc) : (c.Φ).symm ((z : ℂ), 0) = ⟨e z, c.mem_range ⟨z, rfl⟩⟩ := by
  apply (c.Φ).injective
  rw [Homeomorph.apply_symm_apply, c.Φ_e]

/-- **The disc is embedded.**  Injectivity of the parametrisation is a consequence of the
existence of the collar, not an extra hypothesis. -/
theorem injective : Function.Injective e := by
  intro z z' h
  have h1 : (c.Φ).symm ((z : ℂ), 0) = (c.Φ).symm ((z' : ℂ), 0) := by
    rw [c.Φ_symm_zero z, c.Φ_symm_zero z']
    exact Subtype.ext h
  have h2 : ((z : ℂ), (0 : ℝ)) = ((z' : ℂ), (0 : ℝ)) := (c.Φ).symm.injective h1
  exact Subtype.ext (congrArg Prod.fst h2)

/-- **The two sides of the disc.**  `side s` is the (open) set of points of the collar whose normal
coordinate has the sign `s`: `side 1` and `side (-1)` are the two sides of the disc. -/
def side (s : ℝ) : Set R3 := {x : R3 | ∃ hx : x ∈ c.U, 0 < s * (c.Φ ⟨x, hx⟩).2}

theorem mem_side (s : ℝ) (x : R3) :
    x ∈ c.side s ↔ ∃ hx : x ∈ c.U, 0 < s * (c.Φ ⟨x, hx⟩).2 := Iff.rfl

/-- A point of the collar off the disc lies in one of the two sides. -/
theorem mem_side_one_or_side_neg_one (x : R3) (hx : x ∈ c.U) (hne : (c.Φ ⟨x, hx⟩).2 ≠ 0) :
    x ∈ c.side 1 ∨ x ∈ c.side (-1) := by
  rcases lt_or_gt_of_ne (Ne.symm hne) with h | h
  · exact Or.inl ⟨hx, by simpa using h⟩
  · exact Or.inr ⟨hx, by simpa using h⟩

end DiscCollar

end

end Work.Collar3D
