import Mathlib
import Submission.Work.StemsB.RelCohMapPairHomotopyR
import Submission.Work.StemsB.AToolsR
import Submission.Work.Thom.bijective_relCohMap_discFull

set_option synthInstance.maxHeartbeats 400000

/-!
# The disc-full relative cohomology bijection, with rational coefficients

`Work.Thom.bijective_relCohMap_discFull` proves, over `ℤ`, that the pair inclusion

`(B × Dⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × Sⁿ⁻¹)`

induces a bijection on relative cohomology in every degree: it is a homotopy equivalence of pairs,
the radial projection `clamp` onto the closed unit ball being a homotopy inverse fixing the sphere
pointwise.

The rational model Thom induction of this chapter needs the same statement over `ℚ`; the
coefficient-generic transfer `Work.StemsB.relCohMap_pairHomotopyR` (a homotopy equivalence of pairs
induces a bijection on relative cohomology over an arbitrary commutative ring) gives it, at the cost
of exhibiting the two homotopies of pairs explicitly:

* `discFullPairHomotopy`: `clamp ∘ incl` is homotopic to the identity of `B × Dⁿ` by the constant
  homotopy (the composite *is* the identity there), which manifestly preserves the sphere pair;
* `discFullPairHomotopyRight`: `incl ∘ clamp` is homotopic to the identity of `B × ℝⁿ` by linear
  interpolation of the radial scaling `(t,p) ↦ (p.1, ((1-t)·(max 1 ‖p.2‖)⁻¹ + t) • p.2)`; on the
  sphere the radial coefficient is `1`, so the interpolated coefficient is `1` for every `t` and the
  sphere is preserved.

The proof is the rational analogue of the one in
`Submission/Work/Thom/bijective_relCohMap_discFull.lean`; nothing there is rebuilt.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.StemsB

open scoped Topology

noncomputable section

/-- The constant homotopy from `clamp ∘ incl` to the identity of `B × Dⁿ`: the composite is
literally the identity, so the interpolation can be taken constant.  Its tracks lie in the sphere
pair because the homotopy does not move points at all. -/
def discFullPairHomotopy (B : Type) [TopologicalSpace B] (n : ℕ) :
    ContinuousMap.Homotopy
      ((Work.Thom.DiscFull.discFullRetract n B).comp (Work.Thom.DiscFull.discFullIncl n B))
      (ContinuousMap.id (B × Work.Thom.MBall n)) where
  toContinuousMap := ⟨fun p : unitInterval × (B × Work.Thom.MBall n) => p.2, continuous_snd⟩
  map_zero_left := fun q => by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (Work.Thom.DiscFull.clamp_coe_eq_self_of_norm_le n q.2.1 q.2.2).symm
  map_one_left := fun q => rfl

/-- The homotopy from `incl ∘ clamp` to the identity of `B × ℝⁿ` given by linear interpolation of
the radial scaling.  (This is the homotopy already used in the `right_inv` field of
`Work.Thom.DiscFull.discFullHomotopyEquiv`; here it is exposed as a named homotopy so that its
preservation of the sphere pair can be stated.) -/
def discFullPairHomotopyRight (B : Type) [TopologicalSpace B] (n : ℕ) :
    ContinuousMap.Homotopy
      ((Work.Thom.DiscFull.discFullIncl n B).comp (Work.Thom.DiscFull.discFullRetract n B))
      (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n))) where
  toContinuousMap := Work.Thom.DiscFull.homotopyMap n B
  map_zero_left := fun p => by
    apply Prod.ext
    · rfl
    · show ((1 - ((0 : unitInterval) : ℝ)) * Work.Thom.DiscFull.clampCoeff n p.2 +
          ((0 : unitInterval) : ℝ)) • p.2
        = (Work.Thom.DiscFull.clamp n p.2 : EuclideanSpace ℝ (Fin n))
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
      simp [Work.Thom.DiscFull.clampPoint]
  map_one_left := fun p => by
    apply Prod.ext
    · rfl
    · show ((1 - ((1 : unitInterval) : ℝ)) * Work.Thom.DiscFull.clampCoeff n p.2 +
          ((1 : unitInterval) : ℝ)) • p.2 = p.2
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
      simp

/-- On the unit sphere the radial interpolation coefficient `(1-t)·(max 1 ‖v‖)⁻¹ + t` is `1` for
every `t`, so the right homotopy preserves the sphere pair. -/
theorem discFull_homotopyMap_mem_sphere {B : Type} [TopologicalSpace B] (n : ℕ)
    (t : unitInterval) {y : B × EuclideanSpace ℝ (Fin n)}
    (hy : y.2 ∈ Work.Thom.mSph n) :
    (Work.Thom.DiscFull.homotopyMap n B (t, y)).2 ∈ Work.Thom.mSph n := by
  show ((1 - (t : ℝ)) * Work.Thom.DiscFull.clampCoeff n y.2 + (t : ℝ)) • y.2 ∈ Work.Thom.mSph n
  rw [Work.Thom.DiscFull.clampCoeff_eq_one_of_norm_le n (le_of_eq hy), mul_one]
  rw [show (1 - (t : ℝ)) + (t : ℝ) = 1 by ring, one_smul]
  exact hy

/-- **The pair inclusion `(B × Dⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × Sⁿ⁻¹)` induces a bijection on relative
cohomology with rational coefficients.**  This is the `ℚ` form of
`Work.Thom.bijective_relCohMap_discFull`. -/
theorem bijective_relCohMap_discFullRat (B : Type) [TopologicalSpace B] (n m : ℕ) :
    Function.Bijective
      ((Work.Thom.relCohMap
          (⟨fun q : B × Work.Thom.MBall n => (q.1, q.2.1),
            continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩ :
            C(B × Work.Thom.MBall n, B × EuclideanSpace ℝ (Fin n)))
          {q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n}
          {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ Work.Thom.mSph n}
          (fun q hq => hq) ℚ m).hom) := by
  refine relCohMap_pairHomotopyR ℚ
    {q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n}
    {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ Work.Thom.mSph n}
    (⟨fun q : B × Work.Thom.MBall n => (q.1, q.2.1),
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩ :
      C(B × Work.Thom.MBall n, B × EuclideanSpace ℝ (Fin n)))
    (⟨fun p : B × EuclideanSpace ℝ (Fin n) => (p.1, Work.Thom.DiscFull.clamp n p.2),
      continuous_fst.prodMk ((Work.Thom.DiscFull.continuous_clamp n).comp continuous_snd)⟩ :
      C(B × EuclideanSpace ℝ (Fin n), B × Work.Thom.MBall n))
    (fun _ hq => hq) ?_ (discFullPairHomotopy B n) ?_ (discFullPairHomotopyRight B n) ?_ m
  · -- the radial projection carries the sphere into the sphere
    intro y hy
    show ((Work.Thom.DiscFull.clamp n y.2 : Work.Thom.MBall n) :
      EuclideanSpace ℝ (Fin n)) ∈ Work.Thom.mSph n
    rw [Work.Thom.DiscFull.clamp_coe_eq_self_of_norm_le n y.2 (le_of_eq hy)]
    exact hy
  · -- the left homotopy fixes points
    intro _ x hx
    exact hx
  · -- the right homotopy fixes the sphere pointwise
    intro t y hy
    exact discFull_homotopyMap_mem_sphere n t hy

end

end Work.StemsB
