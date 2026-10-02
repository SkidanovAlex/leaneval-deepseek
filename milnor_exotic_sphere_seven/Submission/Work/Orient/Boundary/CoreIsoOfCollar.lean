import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The core isomorphism of a manifold with boundary, from a collar

This file proves `Work.Orient.Boundary.CoreIsoOfCollar`: the collar neighbourhood theorem
(`Work.Surgery.HasCollar`, the named input of the Surgery area) implies the geometric input
`Work.Orient.CoreIsoProp` of the ORIENT area.

For a compact manifold `W` with boundary `B = ∂W` and a collar
`c : B × [0,∞) ↪ W` (`c x 0 = x`), the core is the complement

`C₀ = W ∖ c(B × [0,ε))`

of the **collar region** `c(B × [0,ε))` (an open neighbourhood of `B`).  The complement
`U = c(B × [0,ε))` is a collar of the boundary and deformation retracts onto `B` *inside itself*
(straight-line homotopy in the collar parameter `t ↦ (1-u) t`), so the inclusion
`B ↪ U` is a homotopy equivalence and the five-lemma for pairs
(`Work.Cohomology.relChainsMapOf_homologyMap_isIso`) gives the isomorphism
`H_{n+1}(W,B) ⟶ H_{n+1}(W, W∖C₀)`.

The connectivity clause is elementary: every `x ∈ W°` is joined **inside the interior** to a point
of `C₀` — if `x ∉ U` take `x` itself, and if `x = c(p,t)` with `t < ε` move along the collar fibre
`u ↦ c(p, (1-u) t + u ε)`; all its points with parameter `> 0` lie in the interior (the collar meets
`B` only in `c(B × {0})`) and the endpoint has parameter `ε`, i.e. lies outside `U`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology
open Function Set

namespace Work.Orient.Boundary

noncomputable section

variable {n : ℕ}

/-! ## The collar region -/

/-- The **collar region** `c(∂M × [0,ε))`: the image of the collar over the half-open interval of
parameters `[0,ε)`.  It is an open neighbourhood of `∂M`. -/
def collarRegion {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M)
    (ε : ℝ) : Set M :=
  c.toFun '' (Set.univ ×ˢ {t : Work.Surgery.HalfLine | (t : ℝ) < ε})

/-- The collar region is open. -/
theorem isOpen_collarRegion {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) (ε : ℝ) :
    IsOpen (collarRegion c ε) := by
  refine c.isOpenEmbedding.isOpenMap _ ?_
  exact isOpen_univ.prod (isOpen_lt continuous_subtype_val continuous_const)

/-- The boundary is contained in the collar region (for `ε > 0`). -/
theorem boundary_subset_collarRegion {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) :
    (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M ⊆ collarRegion c ε := by
  intro x hx
  exact ⟨(⟨x, hx⟩, ⟨0, le_refl 0⟩), ⟨trivial, hε⟩, c.toFun_zero ⟨x, hx⟩⟩

/-- Membership in the collar region, unfolded. -/
theorem mem_collarRegion_iff {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) (ε : ℝ)
    (y : M) :
    y ∈ collarRegion c ε ↔
      ∃ w : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M × Work.Surgery.HalfLine,
        (w.2 : ℝ) < ε ∧ c.toFun w = y := by
  constructor
  · rintro ⟨w, hw, hwy⟩
    exact ⟨w, hw.2, hwy⟩
  · rintro ⟨w, hw, hwy⟩
    exact ⟨w, ⟨trivial, hw⟩, hwy⟩

/-- **The collar meets the boundary only in `c(∂M × {0})`**: a point of a collar fibre with
strictly positive parameter lies in the interior of `M`. -/
theorem not_mem_boundary_of_collar_pos {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M)
    (p : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (t : Work.Surgery.HalfLine)
    (ht : 0 < (t : ℝ)) :
    c.toFun (p, t) ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
  intro hmem
  have h1 : c.toFun (p, t) = c.toFun (⟨c.toFun (p, t), hmem⟩, ⟨0, le_refl 0⟩) := by
    rw [c.toFun_zero]
  have h2 := c.injective_toFun h1
  have h3 : (t : ℝ) = 0 :=
    congrArg (fun w : ((𝓡∂ (n + 1)).boundary M) × Work.Surgery.HalfLine => (w.2 : ℝ)) h2
  linarith

/-! ## The straight path along a collar fibre -/

/-- **The straight path along a collar fibre.**  For positive parameters `a, b` the two points
`c(p,a)` and `c(p,b)` of the collar are joined by a path lying entirely in the interior of `M`,
namely `u ↦ c(p, (1-u)a + u b)`. -/
theorem exists_path_collar_fiber {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M)
    (p : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (a b : Work.Surgery.HalfLine)
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) :
    Nonempty (Path (⟨c.toFun (p, a), not_mem_boundary_of_collar_pos c p a ha⟩ :
        {z : M // z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M})
      ⟨c.toFun (p, b), not_mem_boundary_of_collar_pos c p b hb⟩) := by
  let σ : unitInterval → Work.Surgery.HalfLine := fun u =>
    ⟨(1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ), by
      have h1 : (0 : ℝ) ≤ 1 - (u : ℝ) := by linarith [u.2.2]
      have h2 : (0 : ℝ) ≤ (u : ℝ) := u.2.1
      exact add_nonneg (mul_nonneg h1 (le_of_lt ha)) (mul_nonneg h2 (le_of_lt hb))⟩
  have hσ : Continuous σ :=
    Continuous.subtype_mk (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)) _
  have hpos : ∀ u : unitInterval, (0 : ℝ) < (σ u : ℝ) := by
    intro u
    have h2 : (0 : ℝ) ≤ (u : ℝ) := u.2.1
    have h1' : (0 : ℝ) ≤ 1 - (u : ℝ) := by linarith [u.2.2]
    rcases le_or_gt (u : ℝ) (1 / 2) with h | h
    · show (0 : ℝ) < (1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)
      nlinarith [mul_nonneg h2 (le_of_lt hb), ha, h, mul_nonneg h1' (le_of_lt ha)]
    · show (0 : ℝ) < (1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)
      nlinarith [mul_nonneg h1' (le_of_lt ha), hb, h, mul_nonneg h2 (le_of_lt hb)]
  have hσ0 : σ 0 = a := Subtype.ext (by simp [σ])
  have hσ1 : σ 1 = b := Subtype.ext (by simp [σ])
  let γ : unitInterval → {z : M // z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M} :=
    fun u => ⟨c.toFun (p, σ u), not_mem_boundary_of_collar_pos c p (σ u) (hpos u)⟩
  have hγ : Continuous γ :=
    Continuous.subtype_mk (c.continuous_toFun.comp (continuous_const.prodMk hσ))
      (fun u => not_mem_boundary_of_collar_pos c p (σ u) (hpos u))
  refine ⟨Path.mk ⟨γ, hγ⟩ ?_ ?_⟩
  · apply Subtype.ext
    change c.toFun (p, σ 0) = c.toFun (p, a)
    rw [hσ0]
  · apply Subtype.ext
    change c.toFun (p, σ 1) = c.toFun (p, b)
    rw [hσ1]

/-! ## The connectivity clause of `CoreIsoProp` -/

/-- **Every interior point is joined to the complement of the collar region inside the interior.**
This is the connectivity clause `hconn` of `CoreIsoProp`: the core `C₀ = W ∖ c(∂W × [0,ε))` meets
every path component of the interior. -/
theorem exists_path_to_compl_collarRegion {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) (x : M) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    ∃ (y : M) (hy : y ∈ (collarRegion c ε)ᶜ)
      (hy' : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
      Nonempty (Path (⟨x, hx⟩ :
        {z : M // z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M}) ⟨y, hy'⟩) := by
  by_cases hxc : x ∈ collarRegion c ε
  · obtain ⟨w, hwlt, hwx⟩ := (mem_collarRegion_iff c ε x).mp hxc
    have hpos : 0 < (w.2 : ℝ) := by
      rcases lt_or_eq_of_le w.2.2 with h | h
      · exact h
      · exfalso
        have hw0 : w.2 = (⟨0, le_refl 0⟩ : Work.Surgery.HalfLine) := Subtype.ext h.symm
        have hb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := by
          have hxw : x = c.toFun (w.1, (⟨0, le_refl 0⟩ : Work.Surgery.HalfLine)) := by
            rw [← hwx]
            exact congrArg c.toFun (Prod.ext rfl hw0)
          rw [hxw, c.toFun_zero]
          exact w.1.2
        exact hx hb
    refine ⟨c.toFun (w.1, ⟨ε, le_of_lt hε⟩), ?_, ?_, ?_⟩
    · intro hyc
      obtain ⟨w', hw'lt, hw'eq⟩ := (mem_collarRegion_iff c ε _).mp hyc
      have heq : w' = (w.1, (⟨ε, le_of_lt hε⟩ : Work.Surgery.HalfLine)) :=
        c.injective_toFun hw'eq
      have : (w'.2 : ℝ) = ε := congrArg (fun z => (z.2 : ℝ)) heq
      linarith
    · exact not_mem_boundary_of_collar_pos c w.1 ⟨ε, le_of_lt hε⟩ hε
    · obtain ⟨γ⟩ := exists_path_collar_fiber c w.1 w.2 ⟨ε, le_of_lt hε⟩ hpos hε
      exact ⟨γ.cast (Subtype.ext hwx.symm) (Subtype.ext rfl)⟩
  · exact ⟨x, hxc, hx, ⟨Path.refl _⟩⟩

/-! ## The collar coordinates, retraction and inclusion -/

/-- The collar coordinates of a point of the collar region: the element of `∂M × [0,∞)` whose
collar image is the point. -/
def collarPair {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (y : ↥(collarRegion c ε)) :
    (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M × Work.Surgery.HalfLine :=
  c.invFun ⟨y.1, by obtain ⟨w, _, hw⟩ := y.2; exact ⟨w, hw⟩⟩

/-- The retraction of the collar region onto the boundary, along the collar fibres. -/
def collarRetract {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    ↥(collarRegion c ε) → (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M :=
  fun y => (collarPair c y).1

/-- The collar parameter of a point of the collar region. -/
def collarCoord {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    ↥(collarRegion c ε) → Work.Surgery.HalfLine :=
  fun y => (collarPair c y).2

/-- The inclusion of the boundary into the collar region (given by `c(·,0)`). -/
def collarIncl {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) :
    (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M → ↥(collarRegion c ε) :=
  fun x => ⟨x.1, boundary_subset_collarRegion c hε x.2⟩

theorem collarPair_toFun {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (y : ↥(collarRegion c ε)) : c.toFun (collarPair c y) = y.1 := c.toFun_invFun _

theorem collarRetract_coord_toFun {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (y : ↥(collarRegion c ε)) :
    c.toFun (collarRetract c y, collarCoord c y) = y.1 := by
  rw [collarRetract, collarCoord]
  exact collarPair_toFun c y

theorem continuous_collarPair {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    Continuous (collarPair c (ε := ε)) :=
  c.toHomeomorph.symm.continuous.comp (Continuous.subtype_mk continuous_subtype_val _)

theorem continuous_collarRetract {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    Continuous (collarRetract c (ε := ε)) :=
  continuous_fst.comp (continuous_collarPair c)

theorem continuous_collarCoord {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    Continuous (collarCoord c (ε := ε)) :=
  continuous_snd.comp (continuous_collarPair c)

/-- The collar parameter of a point of the collar region is `< ε`. -/
theorem collarCoord_lt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (y : ↥(collarRegion c ε)) : (collarCoord c y : ℝ) < ε := by
  obtain ⟨w, hw, hwy⟩ := (mem_collarRegion_iff c ε y.1).mp y.2
  have h1 : collarPair c y = w :=
    c.injective_toFun (by rw [collarPair_toFun, hwy])
  have : (collarCoord c y : ℝ) = (w.2 : ℝ) := congrArg (fun z => (z.2 : ℝ)) h1
  rw [this]; exact hw

theorem continuous_collarIncl {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) : Continuous (collarIncl c hε) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem collarPair_incl {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) (x : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    collarPair c (collarIncl c hε x) = (x, ⟨0, le_refl 0⟩) := by
  have h : collarIncl c hε x = ⟨c.toFun (x, ⟨0, le_refl 0⟩), by
      rw [c.toFun_zero]; exact boundary_subset_collarRegion c hε x.2⟩ :=
    Subtype.ext (c.toFun_zero x).symm
  rw [h, collarPair]
  exact c.invFun_toFun (x, ⟨0, le_refl 0⟩)

theorem collarPair_incl_coord {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) (x : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    collarCoord c (collarIncl c hε x) = ⟨0, le_refl 0⟩ :=
  congrArg Prod.snd (collarPair_incl c hε x)

theorem collarRetract_incl {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) (x : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    collarRetract c (collarIncl c hε x) = x :=
  congrArg Prod.fst (collarPair_incl c hε x)

/-! ## The deformation retraction of the collar region onto the boundary -/

/-- The straight-line shift of the collar parameter: `t ↦ (1-u) t`. -/
def collarShift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (z : unitInterval × ↥(collarRegion c ε)) : Work.Surgery.HalfLine :=
  ⟨(1 - (z.1 : ℝ)) * (collarCoord c z.2 : ℝ),
    mul_nonneg (by linarith [z.1.2.2]) (collarCoord c z.2).2⟩

theorem continuous_collarShift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    Continuous (collarShift c (ε := ε)) :=
  Continuous.subtype_mk
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp ((continuous_collarCoord c).comp continuous_snd)))
    (fun z => (collarShift c z).2)

theorem collarShift_lt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (z : unitInterval × ↥(collarRegion c ε)) : (collarShift c z : ℝ) < ε := by
  have h2 : (0 : ℝ) ≤ (collarCoord c z.2 : ℝ) := (collarCoord c z.2).2
  have hlt := collarCoord_lt c z.2
  have h1 : (1 - (z.1 : ℝ)) ≤ 1 := by linarith [z.1.2.1]
  have : (collarShift c z : ℝ) ≤ (collarCoord c z.2 : ℝ) := by
    show (1 - (z.1 : ℝ)) * (collarCoord c z.2 : ℝ) ≤ (collarCoord c z.2 : ℝ)
    nlinarith
  linarith

theorem collarShift_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (y : ↥(collarRegion c ε)) : collarShift c (0, y) = collarCoord c y := by
  apply Subtype.ext
  show (1 - ((0 : unitInterval) : ℝ)) * (collarCoord c y : ℝ) = (collarCoord c y : ℝ)
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_mul]

theorem collarShift_one {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (y : ↥(collarRegion c ε)) : collarShift c (1, y) = ⟨0, le_refl 0⟩ := by
  apply Subtype.ext
  show (1 - ((1 : unitInterval) : ℝ)) * (collarCoord c y : ℝ) = (0 : ℝ)
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_mul]

/-- The straight-line deformation of the collar region. -/
def collarHomotopyFun {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    unitInterval × ↥(collarRegion c ε) → ↥(collarRegion c ε) :=
  fun z => ⟨c.toFun (collarRetract c z.2, collarShift c z),
    ⟨(collarRetract c z.2, collarShift c z), ⟨trivial, collarShift_lt c z⟩, rfl⟩⟩

theorem continuous_collarHomotopyFun {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    Continuous (collarHomotopyFun c (ε := ε)) :=
  Continuous.subtype_mk
    (c.continuous_toFun.comp (((continuous_collarRetract c).comp continuous_snd).prodMk
      (continuous_collarShift c)))
    (fun z => ⟨(collarRetract c z.2, collarShift c z), ⟨trivial, collarShift_lt c z⟩, rfl⟩)

/-- The inclusion `∂M → c(∂M × [0,ε))`, `x ↦ c(x,0)`, as a morphism of `TopCat`. -/
def collarInclHom {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) :
    TopCat.of ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) ⟶
      TopCat.of ↥(collarRegion c ε) :=
  TopCat.ofHom ⟨collarIncl c hε, continuous_collarIncl c hε⟩

/-- The retraction `c(∂M × [0,ε)) → ∂M` as a morphism of `TopCat`. -/
def collarRetractHom {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ} :
    TopCat.of ↥(collarRegion c ε) ⟶
      TopCat.of ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :=
  TopCat.ofHom ⟨collarRetract c, continuous_collarRetract c⟩

/-- **The straight-line deformation retraction of the collar region onto the boundary.** -/
def collarHomotopy {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(collarRegion c ε))
      ((collarInclHom c hε).hom.comp (collarRetractHom c).hom) :=
  ContinuousMap.Homotopy.mk ⟨collarHomotopyFun c, continuous_collarHomotopyFun c⟩
    (fun y => by
      apply Subtype.ext
      change c.toFun (collarRetract c y, collarShift c ((0 : unitInterval), y)) = y.1
      rw [collarShift_zero]
      exact collarRetract_coord_toFun c y)
    (fun y => by
      apply Subtype.ext
      change c.toFun (collarRetract c y, collarShift c ((1 : unitInterval), y)) = (collarRetract c y).1
      rw [collarShift_one, c.toFun_zero])

/-! ## The isomorphism of relative homology -/

/-- **The five-lemma step**: if `U = c(∂M × [0,ε))` is the collar region of `M`, then the relative
chain inclusion `C_*(M, ∂M) ⟶ C_*(M, U)` is a quasi-isomorphism (in every degree), because
`∂M ↪ U` is a homotopy equivalence and this is the map induced on the relative complexes of the
pair `(M, ∂M) → (M, U)` by the identity of `M`. -/
theorem isIso_relChainsIncl_of_collar {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : Work.Surgery.Collar n M) {ε : ℝ}
    (hε : 0 < ε) (U : Set M) (hU : U = collarRegion c ε)
    (h : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M ⊆ U) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Orient.relChainsIncl (TopCat.of M)
        (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := U) h) k) := by
  subst hU
  have hcomp : (collarInclHom c hε ≫ collarRetractHom c) =
      𝟙 (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)) := by
    apply TopCat.ext
    intro x
    exact collarRetract_incl c hε x
  have h1 : TopCat.Homotopy (collarInclHom c hε ≫ collarRetractHom c)
      (𝟙 (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M))) :=
    hcomp.symm ▸ (ContinuousMap.Homotopy.refl
      (ContinuousMap.id ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)))
  have h2 : TopCat.Homotopy (collarRetractHom c ≫ collarInclHom c hε)
      (𝟙 (TopCat.of ↥(collarRegion c ε))) := (collarHomotopy c hε).symm
  have hw : Work.Cohomology.subtypeIncl (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) ≫ 𝟙 (TopCat.of M) =
      collarInclHom c hε ≫ Work.Cohomology.subtypeIncl (TopCat.of M) (collarRegion c ε) := by
    apply TopCat.ext
    intro x
    rfl
  refine Work.Cohomology.relChainsMapOf_homologyMap_isIso
    (X := TopCat.of M) (Y := TopCat.of M)
    (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (B := collarRegion c ε)
    (f := 𝟙 (TopCat.of M)) (g := collarInclHom c hε) (w := hw) (n := k) ?_ ?_
  · intro j
    have hc : Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of M) (𝟙 (TopCat.of M)) =
        𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of M)) := by
      simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
    rw [hc, HomologicalComplex.homologyMap_id]
    infer_instance
  · intro j
    exact Work.Cohomology.homologyEquiv ℤ
      (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M))
      (TopCat.of ↥(collarRegion c ε)) (collarInclHom c hε) (collarRetractHom c) h1 h2 j

/-- **The core isomorphism of a compact manifold with boundary, from a collar.** -/
theorem CoreIsoOfCollar (n : ℕ)
    (h : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
      [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M],
      Work.Surgery.HasCollar n M) :
    Work.Orient.CoreIsoProp n := by
  unfold Work.Orient.CoreIsoProp
  intro W _ _ _ _
  obtain ⟨c⟩ := (show Nonempty (Work.Surgery.Collar n ↥W) from h W)
  refine ⟨(collarRegion c 1)ᶜ, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_collarRegion c 1).isClosed_compl.isCompact
  · intro x hx hxb
    exact hx (boundary_subset_collarRegion c one_pos hxb)
  · intro x hx
    exact exists_path_to_compl_collarRegion c one_pos x hx
  · have hb : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary ↥W ⊆
        (((collarRegion c 1)ᶜ)ᶜ) :=
      fun y hy hyc => hyc (boundary_subset_collarRegion c one_pos hy)
    exact isIso_relChainsIncl_of_collar c one_pos (((collarRegion c 1)ᶜ)ᶜ)
      (compl_compl _) hb (n + 1)

end

end Work.Orient.Boundary
