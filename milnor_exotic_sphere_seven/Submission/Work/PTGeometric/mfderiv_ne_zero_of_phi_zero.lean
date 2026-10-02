import Mathlib
import Submission.Work.PTGeometric.SourceRegionPhiSign
import Submission.Work.PTGeometric.regionNhdBoundaryZero
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt
import Submission.Work.PTGeometric.mfderiv_surjective_of_isSubmersionAt_real

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `mfderiv Φ x ≠ 0` at every zero of `Φ`

`Work.PTGeometric.mfderiv_ne_zero_of_phi_zero`: if `Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ` is
`C^∞`, is a submersion (Mathlib's local-normal-form notion) at each of its *interior* zeros, and at
each boundary zero its differential is a negative multiple of the differential of a
boundary-defining chart coordinate, then `mfderiv Φ x ≠ 0` at *every* zero `x` of `Φ` — this is the
`hweak` regularity clause of `Work.PTGeometric.RegionSetupWeak` (see
`Submission/Work/PTGeometric/WeakRegion/Setup.lean`), i.e. the "weak" derivative condition of the
region-charting statement.

## Proof

* At an *interior* zero (`x.1 0 ≠ 0`, so `x` is not on the boundary hyperplane), `hsub` makes `Φ` a
  submersion at `x`; by `Work.PTGeometric.mfderiv_surjective_of_isSubmersionAt_real` its `mfderiv` is
  then surjective onto `ℝ`, hence nonzero.
* At a *boundary* zero, `hone` writes `mfderiv Φ x = c • mfderiv (y ↦ (e y).1 0) x` with `c < 0`,
  and `Work.PTGeometric.chartCoordMfderiv` shows that the derivative of the `0`-th coordinate of a
  chart of the (smooth) maximal atlas at a boundary point is a *positive* multiple of the coordinate
  functional `PiLp.proj 2 _ 0`, which is nonzero.

A separate file (a delegated piece of work) provides the interior-point statement for the target
`ℝ`, which Mathlib's `Submersion.lean` lists as a TODO.
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- The `0`-th coordinate functional `z ↦ z 0` of the model space, as a continuous linear map, is
nonzero. -/
private theorem piLp_proj_zero_ne (n : ℕ) [NeZero n] :
    (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ≠ 0 := by
  intro h
  have h1 := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (PiLp.single 2 (0 : Fin n) 1)) h
  simp only [zero_apply] at h1
  rw [show (PiLp.proj 2 (fun _ : Fin n => ℝ) 0) (PiLp.single 2 (0 : Fin n) 1) = 1 from by
    rw [PiLp.proj_apply]; simp] at h1
  exact one_ne_zero h1

/-- **The boundary of the half-space model is the hyperplane `{x | x.1 0 = 0}`.**  A specialisation
of `Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero` to the
identity chart of the model space. -/
private theorem mem_boundary_halfSpace_iff (n : ℕ) [NeZero n] {x : EuclideanHalfSpace n} :
    x ∈ (modelWithCornersEuclideanHalfSpace n).boundary (EuclideanHalfSpace n) ↔ x.1 0 = 0 := by
  have hmem : (OpenPartialHomeomorph.refl (EuclideanHalfSpace n)) ∈
      IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace n)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (EuclideanHalfSpace n) :=
    IsManifold.chart_mem_maximalAtlas (I := modelWithCornersEuclideanHalfSpace n) (x := x)
  rw [Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
    hmem (mem_univ x)]
  have hcoe : (OpenPartialHomeomorph.refl (EuclideanHalfSpace n)).extend
      (modelWithCornersEuclideanHalfSpace n) x = x.1 := by
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      OpenPartialHomeomorph.refl_apply, modelWithCornersEuclideanHalfSpace_apply]
    rfl
  rw [hcoe]

theorem mfderiv_ne_zero_of_phi_zero {k : ℕ} {Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ}
    (hΦ : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsub : ∀ x : EuclideanHalfSpace ((8 + k) + 1), Φ x = 0 → x.1 0 ≠ 0 →
      IsSubmersionAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ x)
    (hone : ∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
        (EuclideanHalfSpace ((8 + k) + 1)), Φ x = 0 →
      ∃ (e : OpenPartialHomeomorph (EuclideanHalfSpace ((8 + k) + 1))
            (EuclideanHalfSpace ((8 + k) + 1))) (c : ℝ),
        e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
              ((⊤ : ℕ∞) : WithTop ℕ∞) (EuclideanHalfSpace ((8 + k) + 1)) ∧
        x ∈ e.source ∧ c < 0 ∧
        (∀ y ∈ e.source, (e y).1 0 = 0 ↔
          y ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
            (EuclideanHalfSpace ((8 + k) + 1))) ∧
        mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
            (modelWithCornersSelf ℝ ℝ) Φ x
          = c • mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
              (modelWithCornersSelf ℝ ℝ)
              (fun y : EuclideanHalfSpace ((8 + k) + 1) => (e y).1 0) x) :
    ∀ x : EuclideanHalfSpace ((8 + k) + 1), Φ x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) Φ x ≠ 0 := by
  intro x hx
  by_cases hx0 : x.1 0 = 0
  · -- ## A boundary zero: the normal derivative of `Φ` is a nonzero multiple of the normal vector
    have hxb : x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
        (EuclideanHalfSpace ((8 + k) + 1)) := (mem_boundary_halfSpace_iff _).mpr hx0
    obtain ⟨e, c, he, hxe, _hc, _hzero, hder⟩ := hone x hxb hx
    obtain ⟨ce, hce_pos, hce_eq⟩ :=
      Work.PTGeometric.chartCoordMfderiv (n := (8 + k) + 1) e he hxe hxb
    have hcoord : (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ)
        (fun y : EuclideanHalfSpace ((8 + k) + 1) => (e y).1 0) x) ≠ 0 := by
      rw [hce_eq]
      exact smul_ne_zero (ne_of_gt hce_pos) (piLp_proj_zero_ne _)
    intro hz
    rw [hder] at hz
    exact (smul_ne_zero (ne_of_lt _hc) hcoord) hz
  · -- ## An interior zero: `hsub` says that `Φ` is a submersion there, hence `mfderiv Φ x` is onto
    have hint : (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).IsInteriorPoint x := by
      rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
      intro hb
      exact hx0 ((mem_boundary_halfSpace_iff _).mp hb)
    intro hz
    obtain ⟨v, hv⟩ := Work.PTGeometric.mfderiv_surjective_of_isSubmersionAt_real
      (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) hint (hsub x hx hx0) 1
    rw [hz] at hv
    simp only [zero_apply] at hv
    change (0 : ℝ) = 1 at hv
    exact zero_ne_one hv

end

end Work.PTGeometric
