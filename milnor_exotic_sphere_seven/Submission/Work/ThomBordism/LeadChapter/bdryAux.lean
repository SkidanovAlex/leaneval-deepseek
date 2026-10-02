import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.boundarySign_boundaryChartAt_univ
import Submission.Work.ThomBordism.bsuTransfer
import Submission.Work.ThomBordism.bcu_profile2_properties
import Submission.Work.ThomBordism.continuous_bcuPhi_and_mem
import Submission.Work.ThomBordism.chartTr_relHmapOf
import Submission.Work.ThomBordism.PosAtlas.chartTr_eq_of_affine_transition
import Submission.Work.Orient.exists_halfBallGood_piece

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary definitions for `chapter_bdryTransfer` (S2)

The `ψ`-analogue of the boundary collapse `bcuPhi` of `boundarySign_boundaryChartAt_univ`:

  `psiPhi ψ y τ χ z = profile2 0 (χ z) (τ • ((ψ z).1 - (ψ y).1))`,

for an arbitrary half-space-valued open partial homeomorphism `ψ` (not only `chartAt y`), together
with its elementary value lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory
open scoped Manifold Topology ContDiff

namespace Work.ThomBordism.LeadChapter

noncomputable section

open Work.PTGeometric

variable {n : ℕ} {W : TopCat}

/-- The `ψ`-chart value: the ambient coordinates of `ψ z`. -/
abbrev psiCh (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1))) :
    W → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun z => (ψ z).1

/-- The `ψ`-chart value, normalised at `y` and scaled by `τ`. -/
def psiVa (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1))) (y : W) (τ : ℝ)
    (z : W) : EuclideanSpace ℝ (Fin (n + 1)) :=
  τ • (psiCh ψ z - psiCh ψ y)

/-- **The boundary collapse attached to `ψ`**, the scale `τ` and the bump `χ`. -/
def psiPhi (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1))) (y : W) (τ : ℝ)
    (χ : W → ℝ) (z : W) : EuclideanSpace ℝ (Fin (n + 1)) :=
  BCU.profile2 (0 : EuclideanSpace ℝ (Fin (n + 1))) (χ z) (psiVa ψ y τ z)

@[simp] theorem psiVa_apply (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (y : W) (τ : ℝ) (z : W) :
    psiVa ψ y τ z = τ • (psiCh ψ z - psiCh ψ y) := rfl

@[simp] theorem psiPhi_apply (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (y : W) (τ : ℝ) (χ : W → ℝ) (z : W) :
    psiPhi ψ y τ χ z = BCU.profile2 (0 : EuclideanSpace ℝ (Fin (n + 1))) (χ z) (psiVa ψ y τ z) :=
  rfl

variable [ChartedSpace (EuclideanHalfSpace (n + 1)) W]

/-- The `0`-th coordinate of `psiVa`. -/
theorem psiVa_coord (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (y : W) (τ : ℝ) (z : W) :
    (psiVa ψ y τ z) 0 = τ * (psiCh ψ z 0 - psiCh ψ y 0) := by
  simp [psiVa]

/-- `psiVa` vanishes at `y`. -/
theorem psiVa_self (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (y : W) (τ : ℝ) : psiVa ψ y τ y = 0 := by
  simp [psiVa]

/-- Every value of `ψ` has nonnegative `0`-th coordinate. -/
theorem psiCh_coord_nonneg (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (z : W) : 0 ≤ psiCh ψ z 0 := (ψ z).2

/-- The `0`-th coordinate of `ψ y` is `0` at a boundary point of `ψ.source`. -/
theorem psiCh_coord_eq_zero_of_bdry (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    {y : W} (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    (hy : y ∈ ψ.source) (hyb : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    psiCh ψ y 0 = 0 :=
  (hbd y hy).mp hyb

/-- An interior point of `ψ.source` has strictly positive `0`-th coordinate. -/
theorem psiCh_coord_pos_of_not_bdry (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    {x : W} (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    (hx : x ∈ ψ.source)
    (hxb : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    0 < psiCh ψ x 0 :=
  lt_of_le_of_ne (psiCh_coord_nonneg ψ x) (fun h => hxb ((hbd x hx).mpr h.symm))

/-- On the source of `ψ`, `psiVa` vanishes only at `y`. -/
theorem psiVa_eq_zero_iff (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    {y z : W} {τ : ℝ} (hτ : τ ≠ 0) (hy : y ∈ ψ.source) (hz : z ∈ ψ.source) :
    psiVa ψ y τ z = 0 ↔ z = y := by
  rw [psiVa_apply, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hτ
    · have h1 : psiCh ψ z = psiCh ψ y := sub_eq_zero.mp h
      exact ψ.injOn hz hy (Subtype.ext h1)
  · rintro rfl
    simp

/-- `psiVa` is injective on the source of `ψ`. -/
theorem psiVa_injOn (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    {y z z' : W} {τ : ℝ} (hτ : τ ≠ 0) (hz : z ∈ ψ.source) (hz' : z' ∈ ψ.source)
    (h : psiVa ψ y τ z = psiVa ψ y τ z') : z = z' := by
  have h1 : psiCh ψ z - psiCh ψ y = psiCh ψ z' - psiCh ψ y := by
    have := h
    rw [psiVa_apply, psiVa_apply] at this
    exact smul_right_injective (EuclideanSpace ℝ (Fin (n + 1))) hτ this
  have h2 : psiCh ψ z = psiCh ψ z' := by
    have := congrArg (fun v => v + psiCh ψ y) h1
    simpa using this
  exact ψ.injOn hz hz' (Subtype.ext h2)

/-- `psiVa` is nonnegative in its `0`-th coordinate on the source of `ψ`. -/
theorem psiVa_coord_nonneg (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    {y : W} (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    (hy : y ∈ ψ.source)
    (hyb : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 ≤ τ) {z : W} (hz : z ∈ ψ.source) :
    0 ≤ (psiVa ψ y τ z) 0 := by
  rw [psiVa_coord, psiCh_coord_eq_zero_of_bdry ψ hbd hy hyb, sub_zero]
  exact mul_nonneg hτ (psiCh_coord_nonneg ψ z)

/-- `psiVa` vanishes in its `0`-th coordinate at boundary points. -/
theorem psiVa_coord_eq_zero_of_boundary (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    {y z : W} (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    (hy : y ∈ ψ.source) (hyb : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (hz : z ∈ ψ.source) (hzb : z ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} : (psiVa ψ y τ z) 0 = 0 := by
  rw [psiVa_coord, psiCh_coord_eq_zero_of_bdry ψ hbd hy hyb,
    psiCh_coord_eq_zero_of_bdry ψ hbd hz hzb, sub_zero, mul_zero]

/-- The collapse at `y` itself is the origin (for a bump equal to `1` at `y`). -/
theorem psiPhi_self (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (y : W) (τ : ℝ) (χ : W → ℝ) (h1 : χ y = 1) : psiPhi ψ y τ χ y = 0 := by
  rw [psiPhi_apply, h1, psiVa_self]
  exact bcu_profile2_one_zero n

/-- At a point where the bump vanishes the collapse is the north pole. -/
theorem psiPhi_eq_northPole (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (y : W) (τ : ℝ) (χ : W → ℝ) (z : W) (h : χ z = 0) :
    psiPhi ψ y τ χ z = BCU.northPole n := by
  rw [psiPhi_apply, h]
  simp [BCU.profile2]

/-- The closed ball of the half-space model is compact (measured in the ambient space). -/
theorem isCompact_halfSpace_closedBall (n : ℕ) [NeZero (n + 1)]
    (c : EuclideanSpace ℝ (Fin (n + 1))) (ρ : ℝ) :
    IsCompact {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ ρ} := by
  have hemb : Topology.IsEmbedding
      (Subtype.val : EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) :=
    Topology.IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff]
  have himg : Subtype.val '' {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ ρ}
      = (Metric.closedBall c ρ) ∩
        Set.range (Subtype.val : EuclideanHalfSpace (n + 1) →
          EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Set.image_preimage_eq_inter_range]
    rfl
  rw [himg]
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · refine Metric.isClosed_closedBall.inter ?_
    have h : Set.range (Subtype.val : EuclideanHalfSpace (n + 1) →
        EuclideanSpace ℝ (Fin (n + 1))) = {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ x.ofLp 0} :=
      Subtype.range_coe
    rw [h]
    exact isClosed_le continuous_const (by fun_prop)
  · exact Metric.isBounded_closedBall.subset Set.inter_subset_left

/-- The affine homeomorphism `v ↦ τ • (v - c)` of the model space `ℝ^N`. -/
def affHomeo (N : ℕ) (c : EuclideanSpace ℝ (Fin N)) (τ : ℝ) (hτ : τ ≠ 0) :
    EuclideanSpace ℝ (Fin N) ≃ₜ EuclideanSpace ℝ (Fin N) where
  toFun v := τ • (v - c)
  invFun u := τ⁻¹ • u + c
  left_inv v := by
    show τ⁻¹ • (τ • (v - c)) + c = v
    rw [smul_smul, inv_mul_cancel₀ hτ, one_smul, sub_add_cancel]
  right_inv u := by
    show τ • ((τ⁻¹ • u + c) - c) = u
    rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hτ, one_smul]
  continuous_toFun := (continuous_const_smul τ).comp (continuous_id.sub continuous_const)
  continuous_invFun := (continuous_const_smul τ⁻¹).add continuous_const

@[simp] theorem affHomeo_apply (N : ℕ) (c : EuclideanSpace ℝ (Fin N)) (τ : ℝ) (hτ : τ ≠ 0)
    (v : EuclideanSpace ℝ (Fin N)) : affHomeo N c τ hτ v = τ • (v - c) := rfl

@[simp] theorem affHomeo_symm_apply (N : ℕ) (c : EuclideanSpace ℝ (Fin N)) (τ : ℝ)
    (hτ : τ ≠ 0) (u : EuclideanSpace ℝ (Fin N)) :
    (affHomeo N c τ hτ).symm u = τ⁻¹ • u + c := rfl

end

end Work.ThomBordism.LeadChapter
