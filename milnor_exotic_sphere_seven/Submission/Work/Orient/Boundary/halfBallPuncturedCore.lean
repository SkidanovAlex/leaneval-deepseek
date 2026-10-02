import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.localHomology_corner
import Submission.Work.Orient.Boundary.CoreHomotopyData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **The punctured half-ball core of the half-space has vanishing top relative homology.**

The geometric input of the boundary-orientation chapter: for the half-space model
`EuclideanHalfSpace (n+1)`, a point `x` of its interior, a point `c` of the hyperplane and
`ρ > 0` with `dist x c ≤ ρ`, the pair consisting of the punctured half-space
`{y | y ≠ x}` and the complement of the *punctured half-ball*
`{y | dist y c ≤ ρ ∧ 0 < y 0}` has vanishing homology in degree `n + 1`.

The proof is the one explained in `CoreHomotopyData`: pushing every point away from `x` until it
is at distance `C = ρ + dist x c + 1` from `x` (and clamping back into the half-space) is a
homotopy equivalence of the pair `(Y, Z)` carrying `Y` into `Z` while preserving `Z`, so that
`Work.Orient.Boundary.isZero_relChains_of_homotopyEquiv_incl` applies. -/
theorem halfBallPuncturedCore (n : ℕ) (c : EuclideanHalfSpace (n + 1))
    (hc : c.1 0 = 0)
    (ρ : ℝ) (hρ : 0 < ρ) (x : EuclideanHalfSpace (n + 1))
    (hx0 : 0 < x.1 0)
    (hx : dist x.1 c.1 ≤ ρ) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {y : EuclideanHalfSpace (n + 1) | y ≠ x})
      {y : {y : EuclideanHalfSpace (n + 1) | y ≠ x} |
        ¬ (dist y.1.1 c.1 ≤ ρ ∧ 0 < y.1.1 0)}).homology (n + 1)) := by
  classical
  let Yt : Type := {y : EuclideanHalfSpace (n + 1) | y ≠ x}
  let Zt : Set Yt := {y : Yt | ¬ (dist y.1.1 c.1 ≤ ρ ∧ 0 < y.1.1 0)}
  -- the path stays in the punctured half-space
  have hpath : ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : Yt),
      0 ≤ corePath n ρ c x t y 0 ∧ corePath n ρ c x t y ≠ x.1 :=
    fun t ht0 ht1 y => corePath_mem_halfspace n ρ c x y ht0 ht1
  -- the time-one point lies in the core
  have hend : ∀ y : Yt, ¬ (dist (corePath n ρ c x 1 y) c.1 ≤ ρ ∧
      0 < corePath n ρ c x 1 y 0) :=
    fun y => corePath_one_mem_core n ρ c x hρ hx y
  -- the path as a point of `Yt`
  let toY : (t : ℝ) → 0 ≤ t → t ≤ 1 → Yt → Yt := fun t ht0 ht1 y =>
    ⟨⟨corePath n ρ c x t y, (hpath t ht0 ht1 y).1⟩,
      fun h => (hpath t ht0 ht1 y).2 (congrArg Subtype.val h)⟩
  have htoYcont : ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1), Continuous (toY t ht0 ht1) := by
    intro t ht0 ht1
    have hbase : Continuous fun y : Yt => corePath n ρ c x t y :=
      (continuous_corePath n ρ c x).comp (continuous_const.prodMk continuous_id)
    have h1 : Continuous fun y : Yt =>
        (⟨corePath n ρ c x t y, (hpath t ht0 ht1 y).1⟩ : EuclideanHalfSpace (n + 1)) :=
      Continuous.subtype_mk hbase (fun y => (hpath t ht0 ht1 y).1)
    exact Continuous.subtype_mk h1
      (fun y => fun h => (hpath t ht0 ht1 y).2 (congrArg Subtype.val h))
  -- the homotopy of the punctured half-space
  let Hmap : C(↑unitInterval × Yt, Yt) :=
    ⟨fun q => toY (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2, by
      have hbase : Continuous fun q : ↑unitInterval × Yt => corePath n ρ c x (q.1 : ℝ) q.2 :=
        (continuous_corePath n ρ c x).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      have h1 : Continuous fun q : ↑unitInterval × Yt =>
          (⟨corePath n ρ c x (q.1 : ℝ) q.2,
            (hpath (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2).1⟩ : EuclideanHalfSpace (n + 1)) :=
        Continuous.subtype_mk hbase (fun q => (hpath (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2).1)
      exact Continuous.subtype_mk h1
        (fun q => fun h => (hpath (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2).2 (congrArg Subtype.val h))⟩
  -- the endpoint map into the core
  let g : TopCat.of Yt ⟶ TopCat.of Zt := TopCat.ofHom
    ⟨fun y => ⟨toY 1 zero_le_one le_rfl y, hend y⟩,
      Continuous.subtype_mk (htoYcont 1 zero_le_one le_rfl) (fun y => hend y)⟩
  have hY : TopCat.Homotopy (𝟙 (TopCat.of Yt))
      (g ≫ Work.Cohomology.subtypeIncl (TopCat.of Yt) Zt) :=
    ContinuousMap.Homotopy.mk Hmap
      (fun y => by
        apply Subtype.ext
        apply Subtype.ext
        exact corePath_zero n ρ c x y)
      (fun y => rfl)
  -- the same homotopy, restricted to the core
  let hZm : C(↑unitInterval × (TopCat.of Zt), TopCat.of Zt) :=
    ⟨fun q => ⟨toY (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2.1,
        corePath_mem_core n ρ c x hx q.2.1 q.2.2 q.1.2.1 q.1.2.2⟩, by
      have hbase : Continuous fun q : ↑unitInterval × (TopCat.of Zt) =>
          toY (q.1 : ℝ) q.1.2.1 q.1.2.2 q.2.1 :=
        Hmap.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      exact Continuous.subtype_mk hbase
        (fun q => corePath_mem_core n ρ c x hx q.2.1 q.2.2 q.1.2.1 q.1.2.2)⟩
  have hZhom : TopCat.Homotopy (𝟙 (TopCat.of Zt))
      (Work.Cohomology.subtypeIncl (TopCat.of Yt) Zt ≫ g) :=
    ContinuousMap.Homotopy.mk hZm
      (fun z => by
        show hZm (0, z) = z
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact corePath_zero n ρ c x z.1)
      (fun z => rfl)
  exact isZero_relChains_of_homotopyEquiv_incl g hZhom.symm hY.symm (n + 1)

end

end Work.Orient.Boundary
