/-
# Assembly of the space `M̂`

This file is the *topological layer* of the area `Space/`: the definition of the Ratcliffe--Tschantz
space

  `M̂ = M̄ ⊔ (⊔_{v=1..5} [-1,1]² × T_v) / ~₃`

as an adjunction space (a quotient of a coproduct by a relation with closed graph), together with
the basic maps and topological instances the rest of the project needs.

## Conventions (aligned with `Work.Cusp`)

* `E2 := EuclideanSpace ℝ (Fin 2)`; `Sq = [-1,1]²` is `{p : E2 | |p 0| ≤ 1 ∧ |p 1| ≤ 1}` (a
  *square*, not a disc: the norm used for the layer parameter is the sup norm `nrm`).
* `SquarePt := {p : E2 // p ∈ Sq}`; `nrm p = max |p 0| |p 1|`; `sqBdry = {p | nrm p = 1}`.
  The layer parameter of the filling is `nrm`; the core is `nrm = 0`, the gluing boundary is
  `nrm = 1`.
* there are `5` cusps (`Cusp := Fin 5`, the exact data of `rtdata/`).
* the `v`-th filling piece is `W_v = SquarePt × T_v`, where `T_v` is the flat torus `ℝ³/Λ_v`
  (for the concrete assembly, `T_v = (ℝ/ℤ)²`).
* the gluing `~₃` is an adjunction along a homeomorphism
  `glue : ∂M̄ = ⊔_v T_v → ⊔_v (∂Square × T_v)`, i.e. the cusped boundary of `M̄` is identified
  with the boundary of the filling pieces.

## Main definitions

* `Work.Space.Assembly` — the assembly datum (all of the above).
* `Work.Space.Assembly.Mhat` — the space `M̂ = Quotient a.glueData.setoid`.
* `Work.Space.Assembly.incMbar`, `incW` — the canonical maps of the pieces into `M̂`.

## Main results

* `Work.Space.Assembly.instTopologicalSpace`, `instCompactSpace`, `instT2Space`, `instT1Space`,
  `instConnectedSpace` — the topological instances on `M̂`.
* `Work.Space.Assembly.incMbar_injective`, `incY_injective`, `incW_injective`,
  `incMbar_ne_incY` — the pieces sit inside `M̂` as disjoint closed pieces.
-/
import Mathlib
import Submission.Work.QuotientT2.Basic
import Submission.Work.QuotientT2.Adjunction
import Submission.Work.QuotientT2.AdjunctionT2
import Submission.Work.QuotientT2.isClosedEmbedding_quotient_restrict

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Space

/-- The index type of the cusps of `M̂`: exactly `5` cusps. -/
abbrev Cusp : Type := Fin 5

/-- The plane `ℝ²` of the filling collar. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The closed square `[-1,1]² ⊆ ℝ²` (the filling disk `D²`). -/
def Sq : Set E2 := {p | |p 0| ≤ 1 ∧ |p 1| ≤ 1}

/-- The sup norm of a point of the plane: the layer parameter of the filling. -/
def nrm (p : E2) : ℝ := max |p 0| |p 1|

@[simp] theorem nrm_nonneg (p : E2) : 0 ≤ nrm p :=
  le_max_of_le_left (abs_nonneg _)

/-- The closed square `[-1,1]²`, as a topological space. -/
abbrev SquarePt : Type := {p : E2 // p ∈ Sq}

/-- The `i`-th coordinate of the plane, as a continuous linear map. -/
def coord2 (i : Fin 2) : E2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i

@[simp] theorem coord2_apply (i : Fin 2) (p : E2) : coord2 i p = p i := PiLp.proj_apply 2 _ i p

theorem isClosed_sq : IsClosed Sq := by
  have h0 : IsClosed {p : E2 | |p 0| ≤ 1} :=
    isClosed_le (continuous_abs.comp (coord2 0).continuous) continuous_const
  have h1 : IsClosed {p : E2 | |p 1| ≤ 1} :=
    isClosed_le (continuous_abs.comp (coord2 1).continuous) continuous_const
  have h : {p : E2 | |p 0| ≤ 1} ∩ {p : E2 | |p 1| ≤ 1} = Sq := rfl
  rw [← h]
  exact h0.inter h1

theorem convex_sq : Convex ℝ Sq := by
  have h0 : Convex ℝ (coord2 0 ⁻¹' (Set.Icc (-1 : ℝ) 1)) :=
    Convex.linear_preimage (𝕜 := ℝ) (E := E2) (F := ℝ) (convex_Icc (-1 : ℝ) 1)
      (coord2 0 : E2 →ₗ[ℝ] ℝ)
  have h1 : Convex ℝ (coord2 1 ⁻¹' (Set.Icc (-1 : ℝ) 1)) :=
    Convex.linear_preimage (𝕜 := ℝ) (E := E2) (F := ℝ) (convex_Icc (-1 : ℝ) 1)
      (coord2 1 : E2 →ₗ[ℝ] ℝ)
  have h : Sq = coord2 0 ⁻¹' (Set.Icc (-1 : ℝ) 1) ∩ coord2 1 ⁻¹' (Set.Icc (-1 : ℝ) 1) := by
    ext p
    simp only [Sq, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
      coord2_apply, abs_le]
  exact h.symm ▸ h0.inter h1

theorem isCompact_sq : IsCompact Sq := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_sq, ?_⟩
  refine (Metric.isBounded_closedBall (x := (0 : E2)) (r := 2)).subset ?_
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have h0 : ‖p.ofLp 0‖ ≤ 1 := by simpa using hp.1
  have h1 : ‖p.ofLp 1‖ ≤ 1 := by simpa using hp.2
  have hsum : ∑ i, ‖p.ofLp i‖ ^ 2 ≤ 2 := by
    rw [Fin.sum_univ_two]
    nlinarith [norm_nonneg (p.ofLp 0), norm_nonneg (p.ofLp 1)]
  calc Real.sqrt (∑ i, ‖p.ofLp i‖ ^ 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hsum
    _ ≤ 2 := by
        rw [Real.sqrt_le_iff]
        norm_num

instance instCompactSpaceSquarePt : CompactSpace SquarePt :=
  isCompact_iff_compactSpace.mp isCompact_sq

instance instConnectedSpaceSquarePt : ConnectedSpace SquarePt := by
  rw [← isConnected_iff_connectedSpace]
  exact convex_sq.isConnected ⟨0, by simp [Sq]⟩

/-- The sup norm of a point of the square, as a function of the subtype. -/
def sqNorm (p : SquarePt) : ℝ := nrm (p : E2)

theorem sqNorm_nonneg (p : SquarePt) : 0 ≤ sqNorm p := nrm_nonneg _

theorem continuous_nrm : Continuous nrm := by
  have h0 : Continuous fun p : E2 => p 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous fun p : E2 => p 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  exact Continuous.max h0.abs h1.abs

theorem continuous_sqNorm : Continuous sqNorm :=
  continuous_nrm.comp continuous_subtype_val

/-- The boundary `∂[-1,1]²` of the square: the glued boundary of a filling piece. -/
def sqBoundary : Set SquarePt := {p | sqNorm p = 1}

theorem isClosed_sqBoundary : IsClosed sqBoundary :=
  isClosed_eq continuous_sqNorm continuous_const

theorem sqNorm_le_one (p : SquarePt) : sqNorm p ≤ 1 := by
  rcases p.2 with ⟨h0, h1⟩
  exact max_le h0 h1

/-- The disjoint union `⊔_v [-1,1]² × T_v` of the filling pieces attached to the hyperbolic
piece along the five cusps. -/
abbrev Filling (Torus : Cusp → Type*) : Type _ := Σ v : Cusp, SquarePt × Torus v

/-- The boundary `⊔_v ∂[-1,1]² × T_v` of the filling pieces, inside `Filling`. -/
def FillingBdry (Torus : Cusp → Type*) : Set (Filling Torus) := {q | sqNorm q.2.1 = 1}

theorem continuous_fillingNorm (Torus : Cusp → Type*) [∀ v, TopologicalSpace (Torus v)] :
    Continuous (fun q : Filling Torus => sqNorm q.2.1) := by
  apply continuous_sigma
  intro v
  exact continuous_sqNorm.comp continuous_fst

theorem isClosed_fillingBdry (Torus : Cusp → Type*) [∀ v, TopologicalSpace (Torus v)] :
    IsClosed (FillingBdry Torus) :=
  isClosed_eq (continuous_fillingNorm Torus) continuous_const

/-- **The assembly datum.**  It is a *class* so that the instances of the assembled space
(`Work.Space.Main`) can be declared for a variable `[a : Assembly]`. -/
class Assembly where
  /-- The hyperbolic piece `M̄`. -/
  Mbar : Type*
  [topMbar : TopologicalSpace Mbar]
  [compactMbar : CompactSpace Mbar]
  [t2Mbar : T2Space Mbar]
  [connMbar : ConnectedSpace Mbar]
  /-- The torus factors `T_v` of the filling pieces. -/
  Torus : Cusp → Type*
  [topTorus : ∀ v, TopologicalSpace (Torus v)]
  [compactTorus : ∀ v, CompactSpace (Torus v)]
  [t2Torus : ∀ v, T2Space (Torus v)]
  [connTorus : ∀ v, ConnectedSpace (Torus v)]
  /-- The cusped boundary `∂M̄ = ⊔_v T_v` of the hyperbolic piece, as a closed subset of `M̄`. -/
  Tset : Set Mbar
  /-- It is closed. -/
  Tset_closed : IsClosed Tset
  /-- The gluing of the cusp boundary with the boundary of the filling pieces. -/
  glue : Tset ≃ₜ {q : Filling Torus // q ∈ FillingBdry Torus}

attribute [instance] Assembly.topMbar Assembly.compactMbar Assembly.t2Mbar Assembly.connMbar
attribute [instance] Assembly.topTorus Assembly.compactTorus Assembly.t2Torus Assembly.connTorus

namespace Assembly

variable (a : Assembly)

/-- The disjoint union `⊔_v [-1,1]² × T_v` of the filling pieces of this assembly. -/
abbrev Y : Type _ := Filling a.Torus

/-- The boundary `⊔_v ∂[-1,1]² × T_v` of the filling pieces, inside `Y`. -/
abbrev boundarySet : Set a.Y := FillingBdry a.Torus

theorem isClosed_boundarySet : IsClosed a.boundarySet := isClosed_fillingBdry a.Torus

/-- The glue data of the assembly: the adjunction along `glue`. -/
def glueData : Work.QuotientT2.GlueData a.Mbar a.Y where
  s := a.Tset
  t := a.boundarySet
  s_closed := a.Tset_closed
  t_closed := a.isClosed_boundarySet
  h := a.glue

/-- **The space `M̂`**: the layered quotient `(M̄ ⊔ ⊔_v [-1,1]² × T_v)/~₃`. -/
abbrev Mhat : Type _ := Quotient a.glueData.setoid

instance : TopologicalSpace a.Mhat :=
  inferInstanceAs (TopologicalSpace (Quotient a.glueData.setoid))

/-- The quotient map from the coproduct onto `M̂`. -/
abbrev mkq (x : a.Mbar ⊕ a.Y) : a.Mhat := Quotient.mk a.glueData.setoid x

theorem continuous_mkq : Continuous a.mkq := continuous_quotient_mk'

/-- The canonical map `M̄ → M̂`. -/
abbrev incMbar (x : a.Mbar) : a.Mhat := a.mkq (Sum.inl x)

/-- The canonical map from the filling pieces to `M̂`. -/
abbrev incY (y : a.Y) : a.Mhat := a.mkq (Sum.inr y)

/-- The canonical map from the `v`-th filling piece `[-1,1]² × T_v` to `M̂`. -/
abbrev incW (v : Cusp) (p : SquarePt × a.Torus v) : a.Mhat := a.incY ⟨v, p⟩

theorem continuous_incMbar : Continuous a.incMbar :=
  a.continuous_mkq.comp continuous_inl

theorem continuous_incY : Continuous a.incY :=
  a.continuous_mkq.comp continuous_inr

theorem continuous_incW (v : Cusp) : Continuous (a.incW v) :=
  a.continuous_incY.comp (continuous_sigmaMk.comp continuous_id')

@[simp] theorem mk_inl_eq_incMbar (x : a.Mbar) : a.mkq (Sum.inl x) = a.incMbar x := rfl

@[simp] theorem mk_inr_eq_incY (y : a.Y) : a.mkq (Sum.inr y) = a.incY y := rfl

/-- The gluing relation identifies a boundary point of `M̄` with the corresponding boundary point
of the filling pieces. -/
theorem incMbar_eq_incY {x : a.Mbar} (hx : x ∈ a.Tset) :
    a.incMbar x = a.incY ((a.glue ⟨x, hx⟩ : {q : a.Y // q ∈ a.boundarySet}) : a.Y) :=
  Quotient.sound (Work.QuotientT2.GlueData.rel_inl_inr a.glueData ⟨x, hx⟩)

theorem incMbar_eq_incW {x : a.Mbar} (hx : x ∈ a.Tset) :
    a.incMbar x =
      a.incW (a.glue ⟨x, hx⟩).1.1 ((a.glue ⟨x, hx⟩).1.2) := by
  have h := a.incMbar_eq_incY hx
  rwa [show ((a.glue ⟨x, hx⟩ : {q : a.Y // q ∈ a.boundarySet}) : a.Y)
      = (⟨(a.glue ⟨x, hx⟩).1.1, (a.glue ⟨x, hx⟩).1.2⟩ : a.Y) from rfl,
    show a.incY ⟨(a.glue ⟨x, hx⟩).1.1, (a.glue ⟨x, hx⟩).1.2⟩
      = a.incW (a.glue ⟨x, hx⟩).1.1 ((a.glue ⟨x, hx⟩).1.2) from rfl] at h

/-- Two points of the same filling piece have the same image in `M̂` only if they are equal. -/
theorem incY_injective : Function.Injective a.incY := by
  intro y y' h
  exact (Work.QuotientT2.GlueData.rel_inr_inr (G := a.glueData)).mp (Quotient.exact h)

theorem incW_injective (v : Cusp) : Function.Injective (a.incW v) := by
  intro p q h
  have h' : (⟨v, p⟩ : a.Y) = ⟨v, q⟩ := a.incY_injective h
  cases h'
  rfl

theorem incMbar_injective : Function.Injective a.incMbar := by
  intro x x' h
  exact (Work.QuotientT2.GlueData.rel_inl_inl (G := a.glueData)).mp (Quotient.exact h)

/-- Points of `M̄` and of the filling pieces are distinct in `M̂` unless the point of `M̄` lies on
the glued boundary and corresponds to the point of the filling pieces. -/
theorem incMbar_ne_incY {x : a.Mbar} {y : a.Y} (h : ¬ ∃ hx : x ∈ a.Tset,
    ((a.glue ⟨x, hx⟩ : {q : a.Y // q ∈ a.boundarySet}) : a.Y) = y) :
    a.incMbar x ≠ a.incY y :=
  Work.QuotientT2.GlueData.mk_inl_ne_mk_inr a.glueData h

/-! ### Topological instances on `M̂` -/

instance instCompactSpace : CompactSpace a.Mhat :=
  inferInstanceAs (CompactSpace (Quotient a.glueData.setoid))

instance instT2Space : T2Space a.Mhat := a.glueData.t2Space_quotient

instance instT1Space : T1Space a.Mhat := inferInstance

/-- The corner point `(1,1)` of the plane. -/
def sqCorner : E2 := WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ))

theorem sqCorner_mem : sqCorner ∈ Sq := by
  simp [Sq, sqCorner]

theorem sqNorm_sqCorner : sqNorm ⟨sqCorner, sqCorner_mem⟩ = 1 := by
  simp [sqNorm, nrm, sqCorner]

/-- The boundary of the square is nonempty (it contains, for instance, the corner). -/
theorem sqBoundary_nonempty : sqBoundary.Nonempty :=
  ⟨⟨sqCorner, sqCorner_mem⟩, sqNorm_sqCorner⟩

/-- A point of the boundary of the `v`-th filling piece: `(v, (corner, t))`. -/
def bdryPt (Torus : Cusp → Type*) (v : Cusp) (t : Torus v) : Filling Torus :=
  ⟨v, (⟨sqCorner, sqCorner_mem⟩, t)⟩

theorem bdryPt_mem (Torus : Cusp → Type*) (v : Cusp) (t : Torus v) :
    bdryPt Torus v t ∈ FillingBdry Torus := by
  simpa [bdryPt, FillingBdry] using sqNorm_sqCorner

/-- **Every filling piece meets the image of `M̄`.**  The boundary of the `v`-th filling piece is
nonempty, and it is glued to a point of the cusped boundary of `M̄`. -/
theorem exists_meet (v : Cusp) : (range a.incMbar ∩ range (a.incW v)).Nonempty := by
  haveI : Nonempty (a.Torus v) := (inferInstance : ConnectedSpace (a.Torus v)).toNonempty
  obtain ⟨t⟩ := (inferInstance : Nonempty (a.Torus v))
  have hb : bdryPt a.Torus v t ∈ a.boundarySet := bdryPt_mem a.Torus v t
  let e : a.Tset := a.glue.symm ⟨bdryPt a.Torus v t, hb⟩
  refine ⟨a.incMbar e.1, ⟨⟨e.1, rfl⟩, ⟨(⟨sqCorner, sqCorner_mem⟩, t), ?_⟩⟩⟩
  have h2 : a.glue e = ⟨bdryPt a.Torus v t, hb⟩ := Homeomorph.apply_symm_apply a.glue _
  have h := a.incMbar_eq_incW e.2
  rw [h2] at h
  simpa [bdryPt] using h.symm

/-- The cusped boundary of `M̄` is nonempty. -/
theorem Tset_nonempty : a.Tset.Nonempty := by
  haveI : Nonempty (a.Torus 0) := (inferInstance : ConnectedSpace (a.Torus 0)).toNonempty
  obtain ⟨t⟩ := (inferInstance : Nonempty (a.Torus 0))
  exact ⟨(a.glue.symm ⟨bdryPt a.Torus 0 t, bdryPt_mem a.Torus 0 t⟩ : a.Tset),
    (a.glue.symm ⟨bdryPt a.Torus 0 t, bdryPt_mem a.Torus 0 t⟩ : a.Tset).2⟩

/-- The covering family of `M̂` by the image of `M̄` (`none`) and the images of the five filling
pieces (`some v`). -/
abbrev coverFam : Option Cusp → Set a.Mhat
  | none => range a.incMbar
  | some v => range (a.incW v)

theorem iUnion_coverFam : (univ : Set a.Mhat) = ⋃ i, a.coverFam i := by
  ext z
  constructor
  · intro _
    obtain ⟨w, rfl⟩ := Quotient.exists_rep z
    rcases w with x | y
    · exact mem_iUnion.mpr ⟨none, x, rfl⟩
    · obtain ⟨v, p⟩ := y
      exact mem_iUnion.mpr ⟨some v, p, rfl⟩
  · intro _; exact mem_univ _

theorem coverFam_meet : ∀ i : Option Cusp, (a.coverFam i ∩ a.coverFam none).Nonempty := by
  intro i
  cases i with
  | none => exact ⟨a.incMbar (Classical.arbitrary a.Mbar), ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  | some v => exact (a.exists_meet v).mono (fun x hx => ⟨hx.2, hx.1⟩)

/-- **`M̂` is connected.**  It is the union of the (connected) image of `M̄` and the images of the
five filling pieces, and every filling piece meets the image of `M̄` in its glued boundary. -/
theorem isPreconnected_univ : IsPreconnected (univ : Set a.Mhat) := by
  rw [a.iUnion_coverFam]
  refine IsPreconnected.iUnion_of_reflTransGen (fun i => ?_) (fun i j => ?_)
  · cases i with
    | none => exact isPreconnected_range a.continuous_incMbar
    | some v => exact isPreconnected_range (a.continuous_incW v)
  · exact (Relation.ReflTransGen.single (a.coverFam_meet i)).tail
      ((a.coverFam_meet j).mono (fun x hx => ⟨hx.2, hx.1⟩))

instance instConnectedSpace : ConnectedSpace a.Mhat where
  toPreconnectedSpace := ⟨a.isPreconnected_univ⟩
  toNonempty := ⟨a.incMbar (Classical.arbitrary a.Mbar)⟩

/-! ### Openness and closedness criteria for `M̂` -/

/-- A set is open in `M̂` iff its traces on the two pieces are open. -/
theorem isOpen_iff_sum {U : Set a.Mhat} :
    IsOpen U ↔ IsOpen {x : a.Mbar | a.incMbar x ∈ U} ∧ IsOpen {y : a.Y | a.incY y ∈ U} :=
  Work.QuotientT2.isOpen_quotient_iff_sum a.glueData.setoid

/-- A set is closed in `M̂` iff its traces on the two pieces are closed. -/
theorem isClosed_iff_sum {U : Set a.Mhat} :
    IsClosed U ↔ IsClosed {x : a.Mbar | a.incMbar x ∈ U} ∧ IsClosed {y : a.Y | a.incY y ∈ U} :=
  Work.QuotientT2.isClosed_quotient_iff_sum a.glueData.setoid

/-- The preimage of a set of `M̂` under `incMbar` and `incY` determine it. -/
theorem ext_of_preimages {U V : Set a.Mhat}
    (h₁ : ∀ x : a.Mbar, a.incMbar x ∈ U ↔ a.incMbar x ∈ V)
    (h₂ : ∀ y : a.Y, a.incY y ∈ U ↔ a.incY y ∈ V) : U = V := by
  ext z
  obtain ⟨w, rfl⟩ := Quotient.exists_rep z
  rcases w with x | y
  · exact h₁ x
  · exact h₂ y

end Assembly

end Work.Space
