import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Orient.Boundary.Machinery

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The localisation isomorphism for coordinate half-balls

`Work.Orient.Boundary.HalfRestrictIso` : for a coordinate half-ball `K = halfBallPiece (n+1) W z r`
whose points are **not** boundary points of `W`, the restriction
`H_{n+1}(W, W∖K) ⟶ H_{n+1}(W, W∖{z})` is an isomorphism.

The proof has four parts, all in this file:

1. `chartAt_interior_pos` — **chart independence of the interior of the model**: if `x` is not a
   boundary point of `W` and `x` lies in the source of the chart `chartAt H z`, then `chartAt H z`
   sends `x` into the *interior* of the half-space.  This is where the hypothesis of the statement
   is used: the local group `H_{n+1}(W, W∖{x})` is `ℤ` at an interior point and `0` at a boundary
   point (`Work.Orient.Boundary.localHomology_corner`), and through the chart `chartAt H z` it is
   the local group of the half-space at the image of `x`; hence the image cannot be a frontier
   point.
2. `closedBall_halfIncl_pos` — consequently the closed ball of the model whose preimage is `K` is
   contained in the open half-space.
3. `HalfPuncturedVanishing` — the flat model: for a compact ball inside the open half-space, the
   punctured pair `(H ∖ {c}, (H ∖ {c}) ∖ closedBall c ρ)` has vanishing homology (Mayer–Vietoris
   reduces it to `Work.Cohomology.isZero_relChains_punctured_euclid`).
4. `HalfPuncturedChart` — the chart-level statement: `H_i(W∖{z}, (W∖{z})∖K) = 0` (Mayer–Vietoris
   twice plus the chart homeomorphism), which is what the triple sequence of `Kᶜ ⊆ {z}ᶜ ⊆ W`
   consumes in the same way as `Work.ThomBordism.convexLocalIso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **Chart independence of the interior of the model.**

If `x` is not a boundary point of `W` (in the sense of the chart at `x`) and `x` lies in the source
of the chart `e = chartAt H z`, then `e x` lies in the interior of the half-space model, i.e. its
first coordinate is positive. -/
theorem chartAt_interior_pos {n : ℕ} {W : TopCat.{0}} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {z x : W}
    (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source)
    (hb : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    0 < ((chartAt (EuclideanHalfSpace (n + 1)) z) x).1 0 := by
  classical
  by_contra hneg
  have hc0 : ((chartAt (EuclideanHalfSpace (n + 1)) z) x).1 0 = 0 :=
    le_antisymm (not_lt.mp hneg) ((chartAt (EuclideanHalfSpace (n + 1)) z) x).2
  haveI : T1Space (EuclideanHalfSpace (n + 1)) := t1Space_halfSpace n
  haveI : T1Space W := ChartedSpace.t1Space (EuclideanHalfSpace (n + 1)) W
  -- the flat model at a frontier point of the half-space
  have hflat : IsZero ((Work.Cohomology.relChains
      (TopCat.of (EuclideanHalfSpace (n + 1)))
      {y : EuclideanHalfSpace (n + 1) | y ≠ (chartAt (EuclideanHalfSpace (n + 1)) z) x}).homology
        (n + 1)) :=
    halfspace_boundary_isZero n (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) z) x) hc0
  -- the chart identifies the local group of `W` at `x` with the flat model
  obtain ⟨e1⟩ := relChains_chart_iso (X := W) (Y := EuclideanHalfSpace (n + 1))
    (chartAt (EuclideanHalfSpace (n + 1)) z) x hx (n + 1)
  have hArg : IsOpen {y : EuclideanHalfSpace (n + 1) | y ≠
      (chartAt (EuclideanHalfSpace (n + 1)) z) x} := isClosed_singleton.isOpen_compl
  have hcov : (chartAt (EuclideanHalfSpace (n + 1)) z).target ∪
      {y : EuclideanHalfSpace (n + 1) | y ≠ (chartAt (EuclideanHalfSpace (n + 1)) z) x}
      = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : y = (chartAt (EuclideanHalfSpace (n + 1)) z) x
    · exact Or.inl (h ▸ (chartAt (EuclideanHalfSpace (n + 1)) z).map_source hx)
    · exact Or.inr h
  obtain ⟨e2⟩ := excision_iso (TopCat.of (EuclideanHalfSpace (n + 1)))
    (chartAt (EuclideanHalfSpace (n + 1)) z).target
    {y : EuclideanHalfSpace (n + 1) | y ≠ (chartAt (EuclideanHalfSpace (n + 1)) z) x}
    (chartAt (EuclideanHalfSpace (n + 1)) z).open_target hArg hcov (n + 1)
  have hz : IsZero ((Work.Cohomology.relChains W {y : W | y ≠ x}).homology (n + 1)) :=
    IsZero.of_iso (IsZero.of_iso hflat e2) e1
  -- but the local group at an interior point is `ℤ ≠ 0`
  obtain ⟨e3⟩ := (localHomology_corner n W x).1 hb
  have hZ : IsZero (ModuleCat.of ℤ ℤ) := IsZero.of_iso hz e3.symm
  have hsub : Subsingleton (ModuleCat.of ℤ ℤ) := ModuleCat.subsingleton_of_isZero hZ
  exact one_ne_zero (Subsingleton.elim (1 : ℤ) 0)

/-- **The coordinate piece of the half-space lies inside the interior of the model.**

If none of the points of the piece `K = halfBallPiece (n+1) W z r` is a boundary point of `W`, then
the closed ball of the half-space model whose chart preimage is `K` is contained in the *open*
half-space: every point of the ball has positive first coordinate. -/
theorem closedBall_halfIncl_pos {n : ℕ} {W : TopCat.{0}} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {z : W} {r : ℝ} (hr : 0 < r)
    (hball : Work.Orient.halfBallGood (n + 1) W z r)
    (hint : ∀ x ∈ Work.Orient.halfBallPiece (n + 1) W z r,
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    ∀ v ∈ Metric.closedBall (Work.Orient.halfIncl (n + 1)
      ((chartAt (EuclideanHalfSpace (n + 1)) z) z)) (r / 2), 0 < v 0 := by
  classical
  intro v hv
  by_contra hneg
  have hv0 : v 0 ≤ 0 := not_lt.mp hneg
  set c : EuclideanSpace ℝ (Fin (n + 1)) :=
    Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) z) z) with hcdef
  have hcpos : 0 < c 0 := by
    have hzK : z ∈ Work.Orient.halfBallPiece (n + 1) W z r := mem_halfBallPiece_center hr
    exact chartAt_interior_pos (mem_chart_source _ z) (hint z hzK)
  have hden : 0 < c 0 - v 0 := by linarith
  set t : ℝ := c 0 / (c 0 - v 0) with htdef
  have ht0 : 0 ≤ t := div_nonneg (le_of_lt hcpos) (le_of_lt hden)
  have ht1 : t ≤ 1 := by
    rw [div_le_one hden]
    linarith
  set w : EuclideanSpace ℝ (Fin (n + 1)) := (1 - t) • c + t • v with hwdef
  have hcball : c ∈ Metric.closedBall c (r / 2) := by
    rw [Metric.mem_closedBall, dist_self]
    linarith
  have hwball : w ∈ Metric.closedBall c (r / 2) := by
    have hsm := (convex_closedBall c (r / 2)) hcball hv (show (0:ℝ) ≤ 1 - t by linarith) ht0
      (show (1 - t) + t = 1 by ring)
    exact hsm
  have hkey : t * (c 0 - v 0) = c 0 := by
    rw [htdef, div_mul_cancel₀ _ (ne_of_gt hden)]
  have hw0 : w 0 = 0 := by
    show ((1 - t) • c + t • v).ofLp 0 = 0
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
    nlinarith [hkey]
  -- `w` lies in the half-space, so it is the image of a point of the model
  have hwmem : w ∈ Set.range (Work.Orient.halfIncl (n + 1)) := by
    rw [show Set.range (Work.Orient.halfIncl (n + 1)) =
      {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ y.ofLp 0} from range_euclideanHalfSpace (n + 1)]
    show 0 ≤ w.ofLp 0
    rw [hw0]
  obtain ⟨y, hy⟩ := Set.mem_range.mp hwmem
  have hytgt : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).target := by
    apply hball
    show Work.Orient.halfIncl (n + 1) y ∈
      Metric.ball (Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) z) z)) r
    rw [hy]
    exact Metric.closedBall_subset_ball (by linarith) hwball
  let x : W := (chartAt (EuclideanHalfSpace (n + 1)) z).symm y
  have hxsrc : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source :=
    (chartAt (EuclideanHalfSpace (n + 1)) z).map_target hytgt
  have hxe : (chartAt (EuclideanHalfSpace (n + 1)) z) x = y :=
    (chartAt (EuclideanHalfSpace (n + 1)) z).right_inv hytgt
  have hxK : x ∈ Work.Orient.halfBallPiece (n + 1) W z r := by
    refine ⟨?_, hxsrc⟩
    show Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) z) x) ∈
      Metric.closedBall c (r / 2)
    rw [hxe, hy]
    exact hwball
  have hpos := chartAt_interior_pos hxsrc (hint x hxK)
  rw [hxe, show y.1 = Work.Orient.halfIncl (n + 1) y from rfl, hy, hw0] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- The identity homeomorphism between the two presentations of the punctured open half-space. -/
def halfPunctHomeo (m : ℕ) [NeZero m] (c : EuclideanHalfSpace m) :
    ↥{y : {y : EuclideanHalfSpace m | y ≠ c} | 0 < ((y : EuclideanHalfSpace m).1) 0} ≃ₜ
    ↥{v : {v : EuclideanSpace ℝ (Fin m) | v ≠ c.1} | 0 < (v : EuclideanSpace ℝ (Fin m)) 0} where
  toFun y := ⟨⟨y.1.1.1, fun h => y.1.2 (Subtype.ext h)⟩, y.2⟩
  invFun v := ⟨⟨⟨v.1.1, le_of_lt v.2⟩, fun h => v.1.2 (congrArg Subtype.val h)⟩, v.2⟩
  left_inv y := rfl
  right_inv v := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem puncturedVanishing_flat (m : ℕ) [NeZero m] (hm : 1 ≤ m)
    (c : EuclideanHalfSpace m) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ v ∈ Metric.closedBall c.1 ρ, 0 < v 0) :
    ∀ i : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of {y : EuclideanHalfSpace m | y ≠ c})
      {y : {y : EuclideanHalfSpace m | y ≠ c} |
        (y : EuclideanHalfSpace m).1 ∉ Metric.closedBall c.1 ρ}).homology i) := by
  intro i
  let X : TopCat := TopCat.of {y : EuclideanHalfSpace m | y ≠ c}
  let g : X → EuclideanSpace ℝ (Fin m) :=
    fun y => (y : {y : EuclideanHalfSpace m | y ≠ c}).1.1
  let A : Set X := {y | g y ∉ Metric.closedBall c.1 ρ}
  let B : Set X := {y | 0 < (g y) 0}
  have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  have hBopen : IsOpen B := by
    show IsOpen {y : X | 0 < (g y) 0}
    exact isOpen_lt continuous_const ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) 0).comp hg)
  have hAopen : IsOpen A :=
    ((Metric.isClosed_closedBall (x := c.1) (ε := ρ)).isOpen_compl).preimage hg
  have hcov : B ∪ A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : g y ∈ Metric.closedBall c.1 ρ
    · exact Or.inl (hball (g y) h)
    · exact Or.inr h
  obtain ⟨E1⟩ := Work.Cohomology.homologyTwoCover X B A hBopen hAopen hcov i
  refine IsZero.of_iso ?_ E1
  -- the punctured open half-space, presented as a punctured Euclidean space
  let Y : TopCat := TopCat.of {v : EuclideanSpace ℝ (Fin m) | v ≠ c.1}
  let B'' : Set Y := {v | 0 < ((v : Y) : EuclideanSpace ℝ (Fin m)) 0}
  let A'' : Set ↥B'' := {v | ((v : Y) : EuclideanSpace ℝ (Fin m)) ∉ Metric.closedBall c.1 ρ}
  have hcorr : ∀ y : ↥B, (y ∈ {y : ↥B | (y : X) ∈ A} ↔ halfPunctHomeo m c y ∈ A'') := by
    intro y
    have h1 : ((y : ↥B) : X) ∈ A ↔ g ((y : ↥B) : X) ∉ Metric.closedBall c.1 ρ := Iff.rfl
    have h2 : halfPunctHomeo m c y ∈ A'' ↔ g ((y : ↥B) : X) ∉ Metric.closedBall c.1 ρ := Iff.rfl
    exact h1.trans h2.symm
  obtain ⟨E2⟩ := Work.Cohomology.relChains_homeomorph ↥B ↥B''
    {y : ↥B | (y : X) ∈ A} A'' (halfPunctHomeo m c) hcorr i
  refine IsZero.of_iso ?_ E2
  have hcontY : Continuous (fun v : Y => ((v : Y) : EuclideanSpace ℝ (Fin m))) :=
    continuous_subtype_val
  have hUopen : IsOpen B'' := by
    show IsOpen {v : Y | 0 < ((v : Y) : EuclideanSpace ℝ (Fin m)) 0}
    exact isOpen_lt continuous_const ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) 0).comp hcontY)
  have hVopen : IsOpen {v : Y | ((v : Y) : EuclideanSpace ℝ (Fin m)) ∉
      Metric.closedBall c.1 ρ} := by
    show IsOpen ((fun v : Y => ((v : Y) : EuclideanSpace ℝ (Fin m))) ⁻¹'
      (Metric.closedBall c.1 ρ)ᶜ)
    exact ((Metric.isClosed_closedBall (x := c.1) (ε := ρ)).isOpen_compl).preimage hcontY
  have hcovY : B'' ∪ {v : Y | ((v : Y) : EuclideanSpace ℝ (Fin m)) ∉
      Metric.closedBall c.1 ρ} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    by_cases h : ((v : Y) : EuclideanSpace ℝ (Fin m)) ∈ Metric.closedBall c.1 ρ
    · exact Or.inl (hball _ h)
    · exact Or.inr h
  obtain ⟨E3⟩ := Work.Cohomology.homologyTwoCover Y B''
    {v : Y | ((v : Y) : EuclideanSpace ℝ (Fin m)) ∉ Metric.closedBall c.1 ρ}
    hUopen hVopen hcovY i
  have hset : {y : ↥B'' | (y : Y) ∈ {v : Y | ((v : Y) : EuclideanSpace ℝ (Fin m)) ∉
      Metric.closedBall c.1 ρ}} = A'' := rfl
  rw [hset] at E3
  exact IsZero.of_iso
    (Work.Cohomology.isZero_relChains_punctured_euclid m hm c.1 (Metric.closedBall c.1 ρ)
      (isCompact_closedBall c.1 ρ) (convex_closedBall c.1 ρ)
      (Metric.mem_closedBall_self (le_of_lt hρ)) i) E3.symm


/-- The chart homeomorphism between the punctured chart source and the punctured chart target. -/
def chartPunctHomeo {n : ℕ} {W : TopCat.{0}} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (z : W) :
    ↥{w : {y : W | y ≠ z} | (w : W) ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source} ≃ₜ
    ↥{y : {y : EuclideanHalfSpace (n + 1) | y ≠ (chartAt (EuclideanHalfSpace (n + 1)) z) z} |
        (y : EuclideanHalfSpace (n + 1)) ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).target} where
  toFun w := ⟨⟨(chartAt (EuclideanHalfSpace (n + 1)) z) (w : W), fun h =>
      (w : {y : W | y ≠ z}).2 ((chartAt (EuclideanHalfSpace (n + 1)) z).toPartialEquiv.injOn
        w.2 (mem_chart_source _ z) h)⟩,
    (chartAt (EuclideanHalfSpace (n + 1)) z).map_source w.2⟩
  invFun v := ⟨⟨(chartAt (EuclideanHalfSpace (n + 1)) z).symm
      (v : {y : EuclideanHalfSpace (n + 1) | y ≠ (chartAt (EuclideanHalfSpace (n + 1)) z) z}),
      fun h => (v : {y : EuclideanHalfSpace (n + 1) | y ≠
        (chartAt (EuclideanHalfSpace (n + 1)) z) z}).2 (by
          rw [← (chartAt (EuclideanHalfSpace (n + 1)) z).right_inv v.2]
          exact congrArg _ h)⟩,
    (chartAt (EuclideanHalfSpace (n + 1)) z).map_target v.2⟩
  left_inv w := Subtype.ext (Subtype.ext ((chartAt (EuclideanHalfSpace (n + 1)) z).left_inv w.2))
  right_inv v := Subtype.ext (Subtype.ext ((chartAt (EuclideanHalfSpace (n + 1)) z).right_inv v.2))
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk
    ((chartAt (EuclideanHalfSpace (n + 1)) z).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun w => w.2)) _) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
    ((chartAt (EuclideanHalfSpace (n + 1)) z).symm.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun v => v.2)) _) _


theorem puncturedVanishing_chart (n : ℕ) {W : TopCat.{0}} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (z : W) (r : ℝ) (hr : 0 < r)
    (hball : Work.Orient.halfBallGood (n + 1) W z r)
    (hint : ∀ v ∈ Metric.closedBall (Work.Orient.halfIncl (n + 1)
        ((chartAt (EuclideanHalfSpace (n + 1)) z) z)) (r / 2), 0 < v 0) :
    ∀ i : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of {y : W | y ≠ z})
      {y : {y : W | y ≠ z} | (y : W) ∉ Work.Orient.halfBallPiece (n + 1) W z r}).homology i) := by
  intro i
  let e := chartAt (EuclideanHalfSpace (n + 1)) z
  let K : Set W := Work.Orient.halfBallPiece (n + 1) W z r
  let X : TopCat := TopCat.of {y : W | y ≠ z}
  let U : Set X := {w | (w : W) ∈ e.source}
  let V : Set X := {w | (w : W) ∉ K}
  have hKclosed : IsClosed K :=
    (IsCoordHalfBall.isCompact (n := n + 1) ⟨z, r, hr, hball, rfl⟩).isClosed
  have hUopen : IsOpen U := by
    show IsOpen {w : X | (w : W) ∈ e.source}
    exact e.open_source.preimage continuous_subtype_val
  have hVopen : IsOpen V := by
    show IsOpen {w : X | (w : W) ∉ K}
    exact hKclosed.isOpen_compl.preimage continuous_subtype_val
  have hcov : U ∪ V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    by_cases h : (w : W) ∈ K
    · exact Or.inl h.2
    · exact Or.inr h
  obtain ⟨E1⟩ := Work.Cohomology.homologyTwoCover X U V hUopen hVopen hcov i
  refine IsZero.of_iso ?_ E1
  -- the punctured chart target
  let Y : TopCat := TopCat.of {y : EuclideanHalfSpace (n + 1) | y ≠ e z}
  let K₀ : Set (EuclideanHalfSpace (n + 1)) := Work.Orient.halfIncl (n + 1) ⁻¹'
    Metric.closedBall (Work.Orient.halfIncl (n + 1) (e z)) (r / 2)
  let U' : Set Y := {y | (y : EuclideanHalfSpace (n + 1)) ∈ e.target}
  let V'' : Set Y := {y | (y : EuclideanHalfSpace (n + 1)) ∉ K₀}
  have hcorr : ∀ w : ↥U, (w ∈ {w : ↥U | (w : X) ∈ V} ↔
      chartPunctHomeo (n := n) z w ∈ {y : ↥U' | (y : Y) ∈ V''}) := by
    intro w
    have hw : (w : W) ∈ e.source := (w : ↥U).2
    show (w : W) ∉ K ↔ ((chartPunctHomeo (n := n) z w :
      {y : EuclideanHalfSpace (n + 1) | y ≠ e z}) : EuclideanHalfSpace (n + 1)) ∉ K₀
    rw [show ((chartPunctHomeo (n := n) z w :
      {y : EuclideanHalfSpace (n + 1) | y ≠ e z}) : EuclideanHalfSpace (n + 1)) = e (w : W)
      from rfl]
    show (w : W) ∉ (e ⁻¹' K₀ ∩ e.source) ↔ e (w : W) ∉ K₀
    constructor
    · intro h hk; exact h ⟨hk, hw⟩
    · intro h hk; exact h hk.1
  obtain ⟨E2⟩ := Work.Cohomology.relChains_homeomorph ↥U ↥U'
    {w : ↥U | (w : X) ∈ V} {y : ↥U' | (y : Y) ∈ V''} (chartPunctHomeo (n := n) z) hcorr i
  refine IsZero.of_iso ?_ E2
  have hU'open : IsOpen U' := by
    show IsOpen {y : Y | (y : EuclideanHalfSpace (n + 1)) ∈ e.target}
    exact e.open_target.preimage continuous_subtype_val
  have hK₀closed : IsClosed K₀ :=
    (Metric.isClosed_closedBall (x := Work.Orient.halfIncl (n + 1) (e z)) (ε := r / 2)).preimage
      (continuous_subtype_val : Continuous (fun y : EuclideanHalfSpace (n + 1) => y.1))
  have hV''open : IsOpen V'' := by
    show IsOpen {y : Y | (y : EuclideanHalfSpace (n + 1)) ∉ K₀}
    exact hK₀closed.isOpen_compl.preimage continuous_subtype_val
  have hcov' : U' ∪ V'' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : (y : EuclideanHalfSpace (n + 1)) ∈ K₀
    · refine Or.inl ?_
      apply hball
      exact Metric.closedBall_subset_ball (by linarith) h
    · exact Or.inr h
  obtain ⟨E3⟩ := Work.Cohomology.homologyTwoCover Y U' V'' hU'open hV''open hcov' i
  exact IsZero.of_iso
    (puncturedVanishing_flat (n + 1) (by omega) (e z) (r / 2) (by linarith) hint i) E3.symm


/-- **`Work.Orient.Boundary.HalfRestrictIso`**: for a coordinate half-ball `K = halfBallPiece (n+1) W z r`
all of whose points are non-boundary points of `W`, the restriction
`H_{n+1}(W, W∖K) ⟶ H_{n+1}(W, W∖{z})` is an isomorphism.

The proof is the half-space analogue of `Work.ThomBordism.convexLocalIso`: the long exact sequence of
the triple `Kᶜ ⊆ {z}ᶜ ⊆ W` identifies the map with an isomorphism as soon as the punctured pair
`(W∖{z}, (W∖{z})∖K)` has vanishing homology in degrees `n` and `n+1`, which is
`puncturedVanishing_chart` above. -/
theorem HalfRestrictIso (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (z : W) (r : ℝ) (hr : 0 < r)
    (hball : Work.Orient.halfBallGood (n + 1) W z r)
    (hint : ∀ x ∈ Work.Orient.halfBallPiece (n + 1) W z r,
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W
      (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ ({z} : Set W)ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
        (Work.Orient.mem_halfBallPiece_center hr)))) (n + 1)) := by
  have hzK : z ∈ Work.Orient.halfBallPiece (n + 1) W z r :=
    Work.Orient.mem_halfBallPiece_center hr
  have hsub : (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ ⊆ ({z} : Set W)ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hzK)
  -- the punctured vanishing, in the form consumed by the triple sequence
  have hvanish : ∀ i : ℕ, IsZero ((Work.Cohomology.relChains (TopCat.of {y : W | y ≠ z})
      {y : {y : W | y ≠ z} |
        (y : W) ∉ Work.Orient.halfBallPiece (n + 1) W z r}).homology i) :=
    puncturedVanishing_chart n z r hr hball (closedBall_halfIncl_pos hr hball hint)
  -- the triple `Kᶜ ⊆ {z}ᶜ ⊆ W`
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.tripleShort W (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ
      ({z} : Set W)ᶜ hsub
  have hSEX : S.ShortExact :=
    Work.Cohomology.relChains_triple_shortExact W _ _ hsub
  have hSg : S.g = Work.Cohomology.relCokerMap W (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ
      ({z} : Set W)ᶜ hsub :=
    Work.Cohomology.tripleShort_g W _ _ hsub
  have hz0 : IsZero (S.X₁.homology (n + 1)) := by
    obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso W z
      (Work.Orient.halfBallPiece (n + 1) W z r) hzK (n + 1)
    exact IsZero.of_iso (hvanish (n + 1)) eiso
  have hz1 : IsZero (S.X₁.homology ((n + 1) - 1)) := by
    obtain ⟨eiso⟩ := Work.Cohomology.relSubPunctured_homology_iso W z
      (Work.Orient.halfBallPiece (n + 1) W z r) hzK ((n + 1) - 1)
    exact IsZero.of_iso (hvanish ((n + 1) - 1)) eiso
  have hinj : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))) := by
    have hf0 : HomologicalComplex.homologyMap S.f (n + 1) = 0 :=
      IsZero.eq_zero_of_src hz0 _
    have hr2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f (n + 1))).range =
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))).ker :=
      ShortComplex.Exact.moduleCat_range_eq_ker (hSEX.homology_exact₂ (n + 1))
    rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero] at hr2
    exact LinearMap.ker_eq_bot.mp hr2.symm
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))) := by
    have hij : (ComplexShape.down ℕ).Rel (n + 1) ((n + 1) - 1) :=
      Nat.sub_add_cancel (by omega)
    have hδ0 : hSEX.δ (n + 1) ((n + 1) - 1) hij = 0 := IsZero.eq_zero_of_tgt hz1 _
    have hr3 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (n + 1))).range =
        (ModuleCat.Hom.hom (hSEX.δ (n + 1) ((n + 1) - 1) hij)).ker :=
      ShortComplex.Exact.moduleCat_range_eq_ker
        (hSEX.homology_exact₃ (n + 1) ((n + 1) - 1) hij)
    rw [hδ0, ModuleCat.hom_zero, LinearMap.ker_zero] at hr3
    exact LinearMap.range_eq_top.mp hr3
  have hbij : Function.Bijective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap W (Work.Orient.halfBallPiece (n + 1) W z r)ᶜ
        ({z} : Set W)ᶜ hsub) (n + 1))) := by
    rw [← hSg]
    exact ⟨hinj, hsurj⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- **The missing chapter's localisation statement is now proved**: the component
`Work.Orient.HalfRestrictIsoProp` of the half-space port of Hatcher 3.27 (see
`Submission/Work/Orient/Boundary.lean`) holds for every `n`. -/
theorem halfRestrictIsoProp (n : ℕ) : Work.Orient.HalfRestrictIsoProp n :=
  fun W _ _ _ z r hr hball hint => HalfRestrictIso n W z r hr hball hint


/-- **The half-space port of Hatcher 3.27 is complete**: the bundle `Work.Orient.HalfSpaceHatcher`
of `Submission/Work/Orient/Boundary.lean` now holds.  (Its components `HalfVanishingProp` and
`HalfCoverProp` were already proved in `Submission/Work/Orient/Boundary/HalfVanishing.lean` and
`…/HalfCover.lean`; the third is `halfRestrictIsoProp` above.) -/
theorem halfSpaceHatcher (n : ℕ) : Work.Orient.HalfSpaceHatcher n :=
  ⟨Work.Orient.halfVanishingProp n, Work.Orient.halfCoverProp n, halfRestrictIsoProp n⟩


end

end Work.Orient.Boundary
