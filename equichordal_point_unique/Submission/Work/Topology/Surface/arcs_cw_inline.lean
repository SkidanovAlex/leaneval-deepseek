import Mathlib

open Set
open Classical
open scoped Topology

/-!
# One-dimensional CW structure on a locally finite union of arcs (own development)

The walls of the spine are locally finite unions of embedded arcs meeting only in marked vertices.
This file proves, for my own use, that such a union carries a CW-complex structure with no cells of
dimension `≥ 2` (cells: endpoints in dimension `0`, arcs in dimension `1`).  It is developed here
because the equivalent lemma in a colleague's Work file is not published into the commons and the
fleet is not accepting requests.

Planned content (mirroring the standard construction):
* `endSet`, `toIcc` (the affine identification `[-1,1] ≅ [0,1]`), `arcHomeo`;
* the characteristic maps `cellToFun`/`cellInvFun` for the `1`-cells and `pointMap` for the `0`-cells;
* the six CW axioms, with `closed'` discharged through local finiteness of the arc family.
-/

namespace ArcCWInline

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] {ι : Type u}

/-- The set of endpoints of all the arcs. -/
def endSet (γ : ι → C(Set.Icc (0:ℝ) 1, X)) : Set X :=
  Set.range (fun i => (γ i) 0) ∪ Set.range (fun i => (γ i) 1)

/-- The affine identification of `[-1,1]` with `[0,1]`, clamped so as to be total. -/
noncomputable def toIcc (v : Fin 1 → ℝ) : Set.Icc (0:ℝ) 1 :=
  ⟨max 0 (min 1 ((v 0 + 1) / 2)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma norm_fin_one (v : Fin 1 → ℝ) : ‖v‖ = |v 0| := by
  rw [Pi.norm_def]; simp

lemma ball_fin_one {v : Fin 1 → ℝ} (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) : |v 0| < 1 := by
  have h' : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hv
  rwa [norm_fin_one v] at h'

lemma toIcc_coe (v : Fin 1 → ℝ) (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    (toIcc v : ℝ) = (v 0 + 1) / 2 := by
  have h := ball_fin_one hv
  rw [abs_lt] at h
  simp only [toIcc]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma toIcc_mem_ball {v : Fin 1 → ℝ} (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    0 < (toIcc v : ℝ) ∧ (toIcc v : ℝ) < 1 := by
  have h := ball_fin_one hv
  rw [abs_lt] at h
  rw [toIcc_coe v hv]
  constructor <;> linarith

/-- A continuous injection from the compact interval onto its range in a Hausdorff space is a
homeomorphism onto the range. -/
noncomputable def arcHomeo (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : Set.Icc (0:ℝ) 1 ≃ₜ Set.range (γ i) := by
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective (γ i) (hinj i))
    ((γ i).continuous.subtype_mk (fun x => ⟨x, rfl⟩))

@[simp] lemma arcHomeo_coe (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) (s : Set.Icc (0:ℝ) 1) :
    ((arcHomeo γ hinj i s : Set.range (γ i)) : X) = (γ i) s := rfl

/-- The parametrisation of the `i`-th arc by `Fin 1 → ℝ` (through `toIcc`). -/
noncomputable def cellToFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) (v : Fin 1 → ℝ) : X := (arcHomeo γ hinj i (toIcc v) : X)

/-- The inverse parametrisation. -/
noncomputable def cellInvFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) (x : X) : Fin 1 → ℝ :=
  fun _ => if h : x ∈ Set.range (γ i) then
    2 * (((arcHomeo γ hinj i).symm ⟨x, h⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1 else 0

lemma cellInvFun_apply_zero (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {x : X} (hx : x ∈ Set.range (γ i)) :
    cellInvFun γ hinj i x 0 =
      2 * (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1 := by
  classical
  simp only [cellInvFun, dif_pos hx]

/-- **First interior lemma.**  A point of the arc that is neither endpoint has *strictly interior*
parameter, so its inverse image under the characteristic map lies in the open ball.  This is what
makes the `1`-cell map a `PartialEquiv` with source `Metric.ball 0 1`: the only points left out are
the two endpoints, which are `0`-cells. -/
lemma cellInvFun_mem_ball (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {x : X} (hx : x ∈ Set.range (γ i) \ {(γ i) 0, (γ i) 1}) :
    cellInvFun γ hinj i x ∈ Metric.ball (0 : Fin 1 → ℝ) 1 := by
  classical
  have hx' : x ∈ Set.range (γ i) := hx.1
  -- the arc parameter of `x` is neither `0` nor `1`
  have hne0 : (((arcHomeo γ hinj i).symm ⟨x, hx'⟩ : Set.Icc (0:ℝ) 1) : ℝ) ≠ 0 := by
    intro h
    have hs : (arcHomeo γ hinj i).symm ⟨x, hx'⟩ = (0 : Set.Icc (0:ℝ) 1) := Subtype.ext h
    have h2 := congrArg (fun t : Set.Icc (0:ℝ) 1 => ((arcHomeo γ hinj i) t : X)) hs
    rw [show (arcHomeo γ hinj i) ((arcHomeo γ hinj i).symm ⟨x, hx'⟩) = ⟨x, hx'⟩ from
      (arcHomeo γ hinj i).apply_symm_apply ⟨x, hx'⟩, arcHomeo_coe] at h2
    exact hx.2 (Or.inl h2)
  have hne1 : (((arcHomeo γ hinj i).symm ⟨x, hx'⟩ : Set.Icc (0:ℝ) 1) : ℝ) ≠ 1 := by
    intro h
    have hs : (arcHomeo γ hinj i).symm ⟨x, hx'⟩ = (1 : Set.Icc (0:ℝ) 1) := Subtype.ext h
    have h2 := congrArg (fun t : Set.Icc (0:ℝ) 1 => ((arcHomeo γ hinj i) t : X)) hs
    rw [show (arcHomeo γ hinj i) ((arcHomeo γ hinj i).symm ⟨x, hx'⟩) = ⟨x, hx'⟩ from
      (arcHomeo γ hinj i).apply_symm_apply ⟨x, hx'⟩, arcHomeo_coe] at h2
    exact hx.2 (Or.inr h2)
  obtain ⟨hge, hle⟩ := Set.mem_Icc.mp ((arcHomeo γ hinj i).symm ⟨x, hx'⟩).2
  have hlt0 : (0:ℝ) < (((arcHomeo γ hinj i).symm ⟨x, hx'⟩ : Set.Icc (0:ℝ) 1) : ℝ) :=
    lt_of_le_of_ne hge (Ne.symm hne0)
  have hlt1 : (((arcHomeo γ hinj i).symm ⟨x, hx'⟩ : Set.Icc (0:ℝ) 1) : ℝ) < 1 :=
    lt_of_le_of_ne hle hne1
  rw [Metric.mem_ball, dist_eq_norm, norm_fin_one, sub_zero, cellInvFun_apply_zero γ hinj i hx',
    abs_lt]
  constructor <;> linarith

/-- The *coerced value* of `toIcc`, stated without unfolding the structure (unfolding `toIcc` under
a coercion makes the motive depend on the proof fields, which `rw` rejects). -/
lemma toIcc_eq (v : Fin 1 → ℝ) :
    ((toIcc v : Set.Icc (0:ℝ) 1) : ℝ) = max 0 (min 1 ((v 0 + 1) / 2)) := rfl

/-- `toIcc` undoes the affine parametrisation of the inverse map (no strictness needed: the
clamping in `toIcc` handles both endpoints). -/
lemma toIcc_cellInvFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {x : X} (hx : x ∈ Set.range (γ i)) :
    toIcc (cellInvFun γ hinj i x) = (arcHomeo γ hinj i).symm ⟨x, hx⟩ := by
  classical
  obtain ⟨hge, hle⟩ := Set.mem_Icc.mp ((arcHomeo γ hinj i).symm ⟨x, hx⟩).2
  apply Subtype.ext
  rw [toIcc_eq, cellInvFun_apply_zero γ hinj i hx]
  rw [show (2 * (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) - 1 + 1) / 2
      = (((arcHomeo γ hinj i).symm ⟨x, hx⟩ : Set.Icc (0:ℝ) 1) : ℝ) by ring]
  rw [min_eq_right hle, max_eq_right hge]

/-- **First inverse identity.**  The characteristic map followed by its inverse is the identity on
the arc. -/
lemma cellToFun_inv (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {x : X} (hx : x ∈ Set.range (γ i)) :
    cellToFun γ hinj i (cellInvFun γ hinj i x) = x := by
  show ((arcHomeo γ hinj i (toIcc (cellInvFun γ hinj i x))) : X) = x
  rw [toIcc_cellInvFun γ hinj i hx]
  rw [show (arcHomeo γ hinj i) ((arcHomeo γ hinj i).symm ⟨x, hx⟩) = ⟨x, hx⟩ from
    (arcHomeo γ hinj i).apply_symm_apply ⟨x, hx⟩]

/-- **Second inverse identity.**  The inverse followed by the characteristic map is the identity on
the open ball — this is exactly `PartialEquiv.left_inv'` for the `1`-cells. -/
lemma cellInvFun_toFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {v : Fin 1 → ℝ} (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    cellInvFun γ hinj i (cellToFun γ hinj i v) = v := by
  classical
  have hxr : cellToFun γ hinj i v ∈ Set.range (γ i) := ⟨toIcc v, rfl⟩
  have hs : (arcHomeo γ hinj i).symm ⟨cellToFun γ hinj i v, hxr⟩ = toIcc v := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext rfl
  funext k
  fin_cases k
  show cellInvFun γ hinj i (cellToFun γ hinj i v) 0 = v 0
  rw [cellInvFun_apply_zero γ hinj i hxr, hs, toIcc_coe v hv]
  ring

/-- **Interior points never parametrise an endpoint.**  A point of the open ball gives a *strictly
interior* value of `toIcc`, and the arc is injective, so it cannot be `γ i 0`.  This is what makes the
`1`-cell's target `Set.range (γ i) \ {(γ i) 0, (γ i) 1}` consist exactly of the cell's image under
its source. -/
lemma cellToFun_ne_left (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {v : Fin 1 → ℝ} (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    cellToFun γ hinj i v ≠ (γ i) 0 := by
  intro h
  have h' : (γ i) (toIcc v) = (γ i) 0 := by
    rw [← arcHomeo_coe γ hinj i (toIcc v)]
    exact h
  have hsub : toIcc v = (0 : Set.Icc (0:ℝ) 1) := hinj i h'
  have h0 : ((toIcc v : Set.Icc (0:ℝ) 1) : ℝ) = 0 := congrArg Subtype.val hsub
  have hpos := (toIcc_mem_ball hv).1
  linarith

/-- The same at the other endpoint. -/
lemma cellToFun_ne_right (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) {v : Fin 1 → ℝ} (hv : v ∈ Metric.ball (0 : Fin 1 → ℝ) 1) :
    cellToFun γ hinj i v ≠ (γ i) 1 := by
  intro h
  have h' : (γ i) (toIcc v) = (γ i) 1 := by
    rw [← arcHomeo_coe γ hinj i (toIcc v)]
    exact h
  have hsub : toIcc v = (1 : Set.Icc (0:ℝ) 1) := hinj i h'
  have h1 : ((toIcc v : Set.Icc (0:ℝ) 1) : ℝ) = 1 := congrArg Subtype.val hsub
  have hlt := (toIcc_mem_ball hv).2
  linarith

/-- `toIcc` is continuous (it is a clamped affine map of `v 0`). -/
lemma continuous_toIcc : Continuous (toIcc : (Fin 1 → ℝ) → Set.Icc (0:ℝ) 1) := by
  apply Continuous.subtype_mk
  show Continuous fun v : Fin 1 → ℝ => max 0 (min 1 ((v 0 + 1) / 2))
  fun_prop

/-- The characteristic map of a `1`-cell is continuous: a homeomorphism onto the arc, composed with
the (clamped, affine) identification of `[-1,1]` with the parameter interval. -/
lemma continuous_cellToFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : Continuous (cellToFun γ hinj i) := by
  show Continuous fun v : Fin 1 → ℝ =>
    ((arcHomeo γ hinj i (toIcc v) : Set.range (γ i)) : X)
  exact continuous_subtype_val.comp ((arcHomeo γ hinj i).continuous.comp continuous_toIcc)

/-- **The characteristic map of a `1`-cell as a `PartialEquiv`.**  Its source is the open unit ball
of the model space `Fin 1 → ℝ` (i.e. the interval `(-1,1)`, mapped by `toIcc` onto `(0,1)`) and its
target is the arc minus its two endpoints.  All four `PartialEquiv` conditions are the lemmas proved
above: `cellToFun_ne_left`/`_right` and the interior lemma for `map_source'`, and the two round-trip
identities for `left_inv'`/`right_inv'`. -/
noncomputable def cellMap (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : PartialEquiv (Fin 1 → ℝ) X where
  toFun := cellToFun γ hinj i
  invFun := cellInvFun γ hinj i
  source := Metric.ball 0 1
  target := Set.range (γ i) \ {(γ i) 0, (γ i) 1}
  map_source' := fun v hv =>
    ⟨⟨toIcc v, rfl⟩, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨cellToFun_ne_left γ hinj i hv, cellToFun_ne_right γ hinj i hv⟩⟩
  map_target' := fun x hx => cellInvFun_mem_ball γ hinj i hx
  left_inv' := fun v hv => cellInvFun_toFun γ hinj i hv
  right_inv' := fun x hx => cellToFun_inv γ hinj i hx.1

@[simp] lemma cellMap_source (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    (cellMap γ hinj i).source = Metric.ball (0 : Fin 1 → ℝ) 1 := rfl

@[simp] lemma cellMap_toFun (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    (cellMap γ hinj i) = fun v => cellToFun γ hinj i v := rfl

/-- **`cellInvFun` is continuous on the arc minus its endpoints.**  There the `if` in its definition
takes the positive branch, and the map is the composite of the (continuous) inverse homeomorphism onto
the parameter interval with the affine map `t ↦ 2t - 1` into the model space `Fin 1 → ℝ`. -/
lemma continuousOn_cellInvFun (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) :
    ContinuousOn (cellInvFun γ hinj i) (Set.range (γ i) \ {(γ i) 0, (γ i) 1}) := by
  classical
  have hg : Continuous fun p : ↥(Set.range (γ i) \ {(γ i) 0, (γ i) 1}) =>
      (fun _ : Fin 1 => 2 *
        ((((arcHomeo γ hinj i).symm ⟨(p : X), p.2.1⟩ : Set.Icc (0:ℝ) 1)) : ℝ) - 1) := by
    have h1 : Continuous fun p : ↥(Set.range (γ i) \ {(γ i) 0, (γ i) 1}) =>
        (⟨(p : X), p.2.1⟩ : Set.range (γ i)) :=
      Continuous.subtype_mk continuous_subtype_val (fun p => p.2.1)
    have h2 : Continuous fun q : ↥(Set.range (γ i)) => (arcHomeo γ hinj i).symm q :=
      (arcHomeo γ hinj i).symm.continuous
    have h3 : Continuous fun t : Set.Icc (0:ℝ) 1 =>
        (fun _ : Fin 1 => 2 * (t : ℝ) - 1 : Fin 1 → ℝ) := by
      apply continuous_pi
      intro k
      fun_prop
    exact h3.comp (h2.comp h1)
  rw [continuousOn_iff_continuous_domRestrict]
  refine hg.congr (fun p => ?_)
  rw [Set.domRestrict_apply]
  funext k
  fin_cases k
  show 2 * ((((arcHomeo γ hinj i).symm ⟨(p : X), p.2.1⟩ : Set.Icc (0:ℝ) 1)) : ℝ) - 1
      = cellInvFun γ hinj i (p : X) 0
  rw [cellInvFun_apply_zero γ hinj i p.2.1]

/-- **CW axiom (continuity).**  The `1`-cell map is continuous on the closed unit ball of the model
space. -/
lemma cellMap_continuousOn (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : ContinuousOn (cellMap γ hinj i) (Metric.closedBall (0 : Fin 1 → ℝ) 1) :=
  (continuous_cellToFun γ hinj i).continuousOn

/-- **CW axiom (continuity of the inverse).**  The inverse of the `1`-cell map is continuous on the
cell's target (the arc minus its endpoints). -/
lemma cellMap_continuousOn_symm (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) (i : ι) :
    ContinuousOn (cellMap γ hinj i).symm (cellMap γ hinj i).target :=
  continuousOn_cellInvFun γ hinj i

/-- **CW axiom (`source_eq`) for the `1`-cells**: the source is the open unit ball of the model
space `Fin 1 → ℝ`. -/
lemma cellMap_source_eq (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : (cellMap γ hinj i).source = Metric.ball (0 : Fin 1 → ℝ) 1 := rfl

/-- The characteristic map of a `0`-cell: the collapse of the one-point model space `Fin 0 → ℝ` onto
the endpoint `e`. -/
noncomputable def pointMap (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    PartialEquiv (Fin 0 → ℝ) X :=
  PartialEquiv.single (α := Fin 0 → ℝ) (β := X) ![] (e : X)

lemma pointMap_apply (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) (v : Fin 0 → ℝ) :
    pointMap γ e v = (e : X) := rfl

/-- The whole model space of a `0`-cell is a single point, so its norm vanishes. -/
lemma norm_fin_zero (v : Fin 0 → ℝ) : ‖v‖ = 0 := by rw [Pi.norm_def]; simp

lemma ball_fin_zero : Metric.ball (0 : Fin 0 → ℝ) 1 = Set.univ := by
  apply eq_univ_iff_forall.mpr
  intro v
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_fin_zero]
  norm_num

/-- **CW axiom (`source_eq`) for the `0`-cells.**  The model space `Fin 0 → ℝ` is a single point, so
its open unit ball is all of it — and the single point is the source of `pointMap`. -/
lemma pointMap_source_eq (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    (pointMap γ e).source = Metric.ball (0 : Fin 0 → ℝ) 1 := by
  rw [pointMap, PartialEquiv.single_source, ball_fin_zero]
  apply eq_univ_iff_forall.mpr
  intro v
  have hv : v = ![] := Subsingleton.elim v ![]
  rw [hv]
  exact Set.mem_singleton_iff.mpr rfl

/-- **CW axiom (continuity) for the `0`-cells.** -/
lemma pointMap_continuousOn (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    ContinuousOn (pointMap γ e) (Metric.closedBall (0 : Fin 0 → ℝ) 1) :=
  continuous_const.continuousOn

/-- **CW axiom (continuity of the inverse) for the `0`-cells.** -/
lemma pointMap_continuousOn_symm (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (e : ↥(endSet γ)) :
    ContinuousOn (pointMap γ e).symm (pointMap γ e).target :=
  continuous_const.continuousOn

/-- **The `0`-cell ⫽ `1`-cell case.**  The open cell of an endpoint is the singleton `{e}`, and the
open cell of an arc is the arc minus its two endpoints; these meet only if `e` is an interior point of
the arc.  That is exactly what the hypothesis on pairwise intersections forbids: a point common to two
arcs must be an endpoint of *both*, so an endpoint of one arc interior to another is impossible.
(When the endpoint belongs to the arc itself, the exclusion is immediate from
`cellToFun_ne_left`/`_right`.) -/
lemma pointMap_disjoint_cellMap (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    ∀ (e : ↥(endSet γ)) (i : ι),
      Disjoint ((pointMap γ e) '' Metric.ball (0 : Fin 0 → ℝ) 1)
        ((cellMap γ hinj i) '' Metric.ball (0 : Fin 1 → ℝ) 1) := by
  intro e i
  rw [Set.disjoint_left]
  intro x hx0 hx1
  -- the `0`-cell contributes exactly the point `e`
  obtain ⟨v, -, hv⟩ := hx0
  rw [pointMap_apply] at hv
  -- `x` is an interior point of the arc `i`
  obtain ⟨w, hw, hwv⟩ := hx1
  have hxarc : x ∈ Set.range (γ i) := ⟨toIcc w, by rw [← hwv]; rfl⟩
  have hne0 : x ≠ (γ i) 0 := by
    rw [← hwv]
    exact cellToFun_ne_left γ hinj i hw
  have hne1 : x ≠ (γ i) 1 := by
    rw [← hwv]
    exact cellToFun_ne_right γ hinj i hw
  -- `x = e` is an endpoint of some arc, by definition of `endSet` (oriented towards `x`)
  have hend : ∃ j, (γ j) 0 = x ∨ (γ j) 1 = x := by
    have hmem : (e : X) ∈ endSet γ := e.2
    simp only [endSet, Set.mem_union] at hmem
    rcases hmem with hmem | hmem
    · obtain ⟨j, hj⟩ := hmem
      exact ⟨j, Or.inl (by simpa only [hv] using hj)⟩
    · obtain ⟨j, hj⟩ := hmem
      exact ⟨j, Or.inr (by simpa only [hv] using hj)⟩
  obtain ⟨j, hj | hj⟩ := hend
  · rcases eq_or_ne j i with rfl | hji
    · exact hne0 hj.symm
    · rcases (hint i j (Ne.symm hji) ⟨hxarc, ⟨0, hj⟩⟩).1 with h | h
      · exact hne0 h
      · exact hne1 h
  · rcases eq_or_ne j i with rfl | hji
    · exact hne1 hj.symm
    · rcases (hint i j (Ne.symm hji) ⟨hxarc, ⟨1, hj⟩⟩).1 with h | h
      · exact hne0 h
      · exact hne1 h

/-- **The `1`-cell ⫽ `1`-cell case.**  The open cell of an arc is the arc minus its endpoints.  If two
such open cells met at `x`, then `x` would be a point of *both* arcs, so by the hypothesis on pairwise
intersections it would be an endpoint of both — contradicting that it lies in the open cell of the
first arc. -/
lemma cellMap_openCell_disjoint (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint ((cellMap γ hinj i) '' Metric.ball (0 : Fin 1 → ℝ) 1)
        ((cellMap γ hinj j) '' Metric.ball (0 : Fin 1 → ℝ) 1) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨v, hv, hvx⟩ := hx
  obtain ⟨w, hw, hwx⟩ := hx'
  simp only [cellMap_toFun] at hvx hwx
  have hxarc : x ∈ Set.range (γ i) := ⟨toIcc v, by rw [← hvx]; rfl⟩
  have hxarc' : x ∈ Set.range (γ j) := ⟨toIcc w, by rw [← hwx]; rfl⟩
  rcases (hint i j hij ⟨hxarc, hxarc'⟩).1 with h | h
  · exact (cellToFun_ne_left γ hinj i hv) (hvx.trans h)
  · exact (cellToFun_ne_right γ hinj i hv) (hvx.trans h)

/-- **The `0`-cell ⫽ `0`-cell case.**  Two distinct endpoints have distinct (singleton) open cells:
the only way for the singletons to meet is for the endpoints to be equal as points of `X`, hence equal
as elements of `endSet γ`. -/
lemma pointMap_disjoint (γ : ι → C(Set.Icc (0:ℝ) 1, X)) {e e' : ↥(endSet γ)} (h : e ≠ e') :
    Disjoint ((pointMap γ e) '' Metric.ball (0 : Fin 0 → ℝ) 1)
      ((pointMap γ e') '' Metric.ball (0 : Fin 0 → ℝ) 1) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨v, -, hv⟩ := hx
  obtain ⟨w, -, hw⟩ := hx'
  rw [pointMap_apply] at hv hw
  exact h (Subtype.ext (hv.trans hw.symm))

/-- **The cell-type family.**  `0`-cells are the endpoints, `1`-cells are the arcs, and there is
nothing above.  It lives in the same universe as `X`, which is what `Topology.CWComplex` requires of
its cell families. -/
def Cell (γ : ι → C(Set.Icc (0:ℝ) 1, X)) : ℕ → Type u
  | 0 => ↥(endSet γ)
  | 1 => ι
  | (_ + 2) => ULift.{u, 0} PEmpty

/-- **The characteristic map of an `n`-cell**, by dimension dispatch. -/
noncomputable def cellMapAll (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) :
    (n : ℕ) → Cell γ n → PartialEquiv (Fin n → ℝ) X
  | 0, e => pointMap γ e
  | 1, i => cellMap γ hinj i
  | (_ + 2), i => i.down.elim

/-- **CW axiom (`source_eq`)**, all dimensions: every characteristic map has the open unit ball of its
model space as its source. -/
lemma cellMapAll_source_eq (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) :
    ∀ (n : ℕ) (i : Cell γ n), (cellMapAll γ hinj n i).source = Metric.ball (0 : Fin n → ℝ) 1 := by
  intro n
  cases n with
  | zero => exact fun e => pointMap_source_eq γ e
  | succ n' =>
      cases n' with
      | zero => exact fun i => cellMap_source_eq γ hinj i
      | succ n'' => exact fun i => i.down.elim

/-- **CW axiom (`continuousOn`)**, all dimensions. -/
lemma cellMapAll_continuousOn (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) :
    ∀ (n : ℕ) (i : Cell γ n),
      ContinuousOn (cellMapAll γ hinj n i) (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  intro n
  cases n with
  | zero => exact fun e => pointMap_continuousOn γ e
  | succ n' =>
      cases n' with
      | zero => exact fun i => cellMap_continuousOn γ hinj i
      | succ n'' => exact fun i => i.down.elim

/-- **CW axiom (`continuousOn_symm`)**, all dimensions. -/
lemma cellMapAll_continuousOn_symm (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i)) :
    ∀ (n : ℕ) (i : Cell γ n),
      ContinuousOn (cellMapAll γ hinj n i).symm (cellMapAll γ hinj n i).target := by
  intro n
  cases n with
  | zero => exact fun e => pointMap_continuousOn_symm γ e
  | succ n' =>
      cases n' with
      | zero => exact fun i => cellMap_continuousOn_symm γ hinj i
      | succ n'' => exact fun i => i.down.elim

/-- **CW axiom (`pairwiseDisjoint'`)**: the open cells of distinct cells are disjoint.  The three
nontrivial dimension pairs are exactly the three disjointness lemmas; everything involving a cell of
dimension `≥ 2` is vacuous, the cell type being empty there. -/
lemma cellMapAll_pairwiseDisjoint (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    (Set.univ : Set (Σ n, Cell γ n)).PairwiseDisjoint
      (fun ni => cellMapAll γ hinj ni.1 ni.2 '' Metric.ball (0 : Fin ni.1 → ℝ) 1) := by
  rintro ⟨n, i⟩ - ⟨m, j⟩ - hab
  cases n with
  | zero =>
      cases m with
      | zero => exact pointMap_disjoint γ (fun hh => hab (by cases hh; rfl))
      | succ m' =>
          cases m' with
          | zero => exact pointMap_disjoint_cellMap γ hinj hint i j
          | succ m'' => exact j.down.elim
  | succ n' =>
      cases n' with
      | zero =>
          cases m with
          | zero => exact (pointMap_disjoint_cellMap γ hinj hint j i).symm
          | succ m' =>
              cases m' with
              | zero =>
                  exact cellMap_openCell_disjoint γ hinj hint (fun hh => hab (by cases hh; rfl))
              | succ m'' => exact j.down.elim
      | succ n'' => exact i.down.elim

/-- **The cells attached to a `1`-cell**: its two endpoints, as `0`-cells.  This is the `I` of the
CW axiom `mapsTo`: the boundary sphere of the model interval consists of the two parameters `±1`, whose
images under the characteristic map are exactly the endpoints. -/
noncomputable def targetCells (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (i : ι) :
    Π m, Finset (Cell γ m) := by
  letI : DecidableEq ↥(endSet γ) := Classical.decEq _
  intro m
  match m with
  | 0 => exact {⟨(γ i) 0, Or.inl ⟨i, rfl⟩⟩, ⟨(γ i) 1, Or.inr ⟨i, rfl⟩⟩}
  | (_ + 1) => exact ∅

@[simp] lemma targetCells_zero (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (i : ι) :
    targetCells γ i 0 = ({⟨(γ i) 0, Or.inl ⟨i, rfl⟩⟩, ⟨(γ i) 1, Or.inr ⟨i, rfl⟩⟩} :
      Finset (Cell γ 0)) := rfl

@[simp] lemma targetCells_succ (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (i : ι) (m : ℕ) :
    targetCells γ i (m + 1) = (∅ : Finset (Cell γ (m + 1))) := rfl

/-- **The attached cells of an arbitrary cell**, by dimension dispatch. -/
noncomputable def targetCellsAll (γ : ι → C(Set.Icc (0:ℝ) 1, X)) :
    Π (n : ℕ), Cell γ n → Π m, Finset (Cell γ m)
  | 0, _ => fun _ => ∅
  | 1, i => targetCells γ i
  | (_ + 2), i => i.down.elim

/-- **CW axiom (`mapsTo`)**: the boundary sphere of the model space of a cell maps into the union of
the closed-ball images of its attached cells.  For a `1`-cell the sphere is the two parameters `±1`,
whose images are the two endpoints — exactly `targetCells`; for a `0`-cell the sphere is empty. -/
lemma cellMapAll_mapsTo (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i)) :
    ∀ (n : ℕ) (i : Cell γ n),
      ∃ (I : Π m, Finset (Cell γ m)),
        Set.MapsTo (cellMapAll γ hinj n i) (Metric.sphere (0 : Fin n → ℝ) 1)
        (∅ ∪ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m,
          (cellMapAll γ hinj m j) '' Metric.closedBall (0 : Fin m → ℝ) 1) := by
  intro n
  cases n with
  | zero =>
      intro e
      refine ⟨fun _ => ∅, fun x hx => ?_⟩
      have h : (0 : ℝ) = 1 := by
        have := Metric.mem_sphere.mp hx
        rwa [dist_eq_norm, sub_zero, norm_fin_zero] at this
      norm_num at h
  | succ n' =>
      cases n' with
      | zero =>
          intro i
          letI : DecidableEq ↥(endSet γ) := Classical.decEq _
          let ii : ι := i
          refine ⟨targetCells γ ii, fun x hx => ?_⟩
          have hnorm : ‖x‖ = 1 := by
            have := Metric.mem_sphere.mp hx
            rwa [dist_eq_norm, sub_zero] at this
          have habs : |x 0| = 1 := by rw [← norm_fin_one x]; exact hnorm
          rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp habs with h | h
          · have htoIcc : toIcc x = (1 : Set.Icc (0:ℝ) 1) := by
              apply Subtype.ext
              rw [toIcc_eq, h]; norm_num
            have hval : (cellMap γ hinj ii) x = (γ ii) 1 := by
              show ((arcHomeo γ hinj ii (toIcc x)) : X) = (γ ii) 1
              rw [htoIcc]; exact arcHomeo_coe γ hinj ii 1
            have hj : (⟨(γ ii) 1, Or.inr ⟨ii, rfl⟩⟩ : ↥(endSet γ)) ∈ targetCells γ ii 0 := by
              rw [targetCells_zero]
              exact Finset.mem_insert_of_mem
                (Finset.mem_singleton_self (⟨(γ ii) 1, Or.inr ⟨ii, rfl⟩⟩ : ↥(endSet γ)))
            rw [Set.empty_union]
            exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by norm_num,
              Set.mem_iUnion.mpr ⟨⟨(γ ii) 1, Or.inr ⟨ii, rfl⟩⟩,
                Set.mem_iUnion.mpr ⟨hj, ⟨![] , Metric.mem_closedBall.mpr (by
                  rw [dist_eq_norm, sub_zero, norm_fin_zero]; norm_num), by
                  show ((⟨(γ ii) 1, Or.inr ⟨ii, rfl⟩⟩ : ↥(endSet γ)) : X) = (cellMap γ hinj ii) x
                  rw [hval]⟩⟩⟩⟩⟩
          · have htoIcc : toIcc x = (0 : Set.Icc (0:ℝ) 1) := by
              apply Subtype.ext
              rw [toIcc_eq, h]; norm_num
            have hval : (cellMap γ hinj ii) x = (γ ii) 0 := by
              show ((arcHomeo γ hinj ii (toIcc x)) : X) = (γ ii) 0
              rw [htoIcc]; exact arcHomeo_coe γ hinj ii 0
            have hj : (⟨(γ ii) 0, Or.inl ⟨ii, rfl⟩⟩ : ↥(endSet γ)) ∈ targetCells γ ii 0 := by
              rw [targetCells_zero]
              exact Finset.mem_insert_self (⟨(γ ii) 0, Or.inl ⟨ii, rfl⟩⟩ : ↥(endSet γ)) _
            rw [Set.empty_union]
            exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by norm_num,
              Set.mem_iUnion.mpr ⟨⟨(γ ii) 0, Or.inl ⟨ii, rfl⟩⟩,
                Set.mem_iUnion.mpr ⟨hj, ⟨![] , Metric.mem_closedBall.mpr (by
                  rw [dist_eq_norm, sub_zero, norm_fin_zero]; norm_num), by
                  show ((⟨(γ ii) 0, Or.inl ⟨ii, rfl⟩⟩ : ↥(endSet γ)) : X) = (cellMap γ hinj ii) x
                  rw [hval]⟩⟩⟩⟩⟩
      | succ n'' => intro i; exact i.down.elim

/-- The open cell of a `1`-cell is the arc: `toIcc` surjects the closed ball onto `[0,1]`. -/
lemma cellMap_image_closedBall (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i))
    (i : ι) : (cellMap γ hinj i) '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = Set.range (γ i) := by
  ext y
  constructor
  · rintro ⟨v, -, rfl⟩
    exact ⟨toIcc v, arcHomeo_coe γ hinj i (toIcc v)⟩
  · rintro ⟨s, rfl⟩
    refine ⟨fun _ : Fin 1 => 2 * (s : ℝ) - 1, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_fin_one, abs_le]
      exact ⟨by linarith [s.2.1], by linarith [s.2.2]⟩
    · show ((arcHomeo γ hinj i (toIcc (fun _ : Fin 1 => 2 * (s : ℝ) - 1))) : X) = (γ i) s
      have htoIcc : toIcc (fun _ : Fin 1 => 2 * (s : ℝ) - 1) = s := by
        apply Subtype.ext
        rw [toIcc_eq]
        change max 0 (min 1 ((2 * (s : ℝ) - 1 + 1) / 2)) = ((s : ℝ))
        rw [show (2 * (s : ℝ) - 1 + 1) / 2 = (s : ℝ) by ring]
        rw [min_eq_right s.2.2, max_eq_right s.2.1]
      rw [htoIcc]
      exact arcHomeo_coe γ hinj i s

/-- **CW axiom (`union'`)**: the closed cells cover exactly the union of the arcs.  The `1`-cells
already give the arcs (previous lemma); a `0`-cell contributes one endpoint, which lies in the range of
its own arc; higher cells are empty. -/
lemma cellMapAll_union (γ : ι → C(Set.Icc (0:ℝ) 1, X)) (hinj : ∀ i, Function.Injective (γ i)) :
    (∅ ∪ ⋃ n, ⋃ j, (cellMapAll γ hinj n j) '' Metric.closedBall (0 : Fin n → ℝ) 1)
      = ⋃ i, Set.range (γ i) := by
  ext y
  constructor
  · intro hy
    rcases hy with h | h
    · exact absurd h (Set.notMem_empty y)
    · obtain ⟨n, h⟩ := Set.mem_iUnion.mp h
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      cases n with
      | zero =>
          obtain ⟨v, -, hvx⟩ := hj
          let jj : ↥(endSet γ) := j
          rw [← hvx]
          show (pointMap γ jj v : X) ∈ ⋃ i, Set.range (γ i)
          rw [pointMap_apply]
          rcases jj.2 with ⟨i, hi⟩ | ⟨i, hi⟩
          · exact Set.mem_iUnion.mpr ⟨i, ⟨0, hi⟩⟩
          · exact Set.mem_iUnion.mpr ⟨i, ⟨1, hi⟩⟩
      | succ n' =>
          cases n' with
          | zero =>
              have hy' : y ∈ (cellMap γ hinj j) '' Metric.closedBall (0 : Fin 1 → ℝ) 1 := hj
              rw [cellMap_image_closedBall γ hinj j] at hy'
              exact Set.mem_iUnion.mpr ⟨j, hy'⟩
          | succ n'' => exact j.down.elim
  · intro hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    refine Or.inr ?_
    refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    show y ∈ (cellMap γ hinj i) '' Metric.closedBall (0 : Fin 1 → ℝ) 1
    rw [cellMap_image_closedBall γ hinj i]
    exact hi

/-- **There are no cells in dimension `≥ 2`.**  The cell type above dimension `1` is
`ULift PEmpty`, which is empty. -/
lemma isEmpty_Cell_of_two_le (γ : ι → C(Set.Icc (0:ℝ) 1, X)) {n : ℕ} (hn : 2 ≤ n) :
    IsEmpty (Cell γ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm]
  exact ⟨fun i => i.down.elim⟩

/-!
## The remaining CW axioms: `closed'` and the assembly
-/

/-- **CW axiom (`closed'`).**  If `A` is covered by the arcs and each `A ∩ (closed cell)` is closed,
then `A` is closed: locally only finitely many arcs meet a point, so `A` agrees near that point with
a finite union of closed pieces. -/
lemma cellMapAll_closed' (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hlf : LocallyFinite (fun i => Set.range (γ i)))
    (A : Set X) (hA : A ⊆ ⋃ i, Set.range (γ i))
    (hcl : ∀ (n : ℕ) (j : Cell γ n),
      IsClosed (A ∩ (cellMapAll γ hinj n j) '' Metric.closedBall (0 : Fin n → ℝ) 1)) :
    IsClosed A := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨t, ht, hfin⟩ := hlf x
  obtain ⟨W, hWt, hWopen, hxW⟩ := mem_nhds_iff.mp ht
  have hcell : ∀ i : ι,
      (cellMapAll γ hinj 1 i) '' Metric.closedBall (0 : Fin 1 → ℝ) 1 = Set.range (γ i) :=
    fun i => cellMap_image_closedBall γ hinj i
  haveI : Finite ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty} := hfin.to_subtype
  have hBclosed : IsClosed (⋃ (i : ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty}),
      A ∩ Set.range (γ i)) :=
    isClosed_iUnion_of_finite fun i => by
      have h1 : A ∩ Set.range (γ (i : ι)) =
          A ∩ (cellMapAll γ hinj 1 (i : ι)) '' Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
        rw [hcell (i : ι)]
      rw [h1]
      exact hcl 1 (i : ι)
  have hxcl : x ∈ closure (A ∩ W) := by
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨y, hys⟩ := mem_closure_iff.mp hx (o ∩ W)
      (ho.inter hWopen) ⟨hxo, hxW⟩
    exact ⟨y, ⟨hys.1.1, ⟨hys.2, hys.1.2⟩⟩⟩
  have hsub : A ∩ W ⊆ ⋃ (i : ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty}),
      A ∩ Set.range (γ i) := by
    intro y hy
    obtain ⟨hyA, hyW⟩ := hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hA hyA)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨y, hi, hWt hyW⟩⟩, ⟨hyA, hi⟩⟩
  have hxB : x ∈ ⋃ (i : ↥{i : ι | (Set.range (γ i) ∩ t).Nonempty}), A ∩ Set.range (γ i) :=
    hBclosed.closure_subset (closure_mono hsub hxcl)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxB
  exact hi.1

/-- **The CW-complex structure on a locally finite union of arcs** (cells: endpoints in dimension
`0`, arcs in dimension `1`, nothing above). -/
noncomputable def cwComplex (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hlf : LocallyFinite (fun i => Set.range (γ i)))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    Topology.CWComplex (X := X) (⋃ i, Set.range (γ i)) :=
  Topology.CWComplex.mk (Cell γ) (cellMapAll γ hinj)
    (cellMapAll_source_eq γ hinj)
    (cellMapAll_continuousOn γ hinj)
    (cellMapAll_continuousOn_symm γ hinj)
    (cellMapAll_pairwiseDisjoint γ hinj hint)
    (fun n i => by
      obtain ⟨I, hI⟩ := cellMapAll_mapsTo γ hinj n i
      exact ⟨I, by simpa only [Set.empty_union] using hI⟩)
    (fun A hA hcl => cellMapAll_closed' γ hinj hlf A hA hcl)
    (by simpa only [Set.empty_union] using cellMapAll_union γ hinj)

/-- **A locally finite family of embedded arcs whose pairwise intersections consist of common
endpoints carries a CW-complex structure with no cells of dimension `≥ 2`.** -/
theorem cwComplex_of_locallyFinite_arcs (γ : ι → C(Set.Icc (0:ℝ) 1, X))
    (hinj : ∀ i, Function.Injective (γ i))
    (hlf : LocallyFinite (fun i => Set.range (γ i)))
    (hint : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) ⊆
      ({(γ i) 0, (γ i) 1} : Set X) ∩ ({(γ j) 0, (γ j) 1} : Set X)) :
    ∃ hC : @Topology.CWComplex X _ (⋃ i, Set.range (γ i)),
      (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ _ hC n)) :=
  ⟨cwComplex γ hinj hlf hint, fun _ hn => isEmpty_Cell_of_two_le γ hn⟩

end ArcCWInline
