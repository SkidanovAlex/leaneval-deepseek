import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.RealCond
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ANALYTIC.exists_realNullSeq

/-!
# The null sequence `c : P ⟶ ∏^bnd ℤ`

The map `c` of REFS/03 §2: the element `e_n ∈ P` is sent to the `n`-th standard basis vector
`δ_n` of `∏^bnd ℤ`.  It is defined through the free-Yoneda equivalence
`freeHomEquiv : (ℤ[ℕ∪∞] ⟶ M) ≃ M(ℕ∪∞)` from the element
`n ↦ (k ↦ if k = n then 1 else 0)` of `boundedSeq(ℕ∪∞)` (vanishing at `∞`, so that it factors
through the quotient `P = ℤ[ℕ∪∞]/ℤ[∞]`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite
open Classical
open OnePoint

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The continuous function `ℕ∪∞ → ℤ` which is `1` at `n` and `0` elsewhere. -/
def deltaFun (n : ℕ) : C(ℕ∪{∞}, ℤ) where
  toFun x := if x = (n : ℕ∪{∞}) then 1 else 0
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat]
    refine Filter.Tendsto.congr' (Filter.eventually_atTop.mpr ⟨n + 1, fun j hj => ?_⟩)
      tendsto_const_nhds
    have hj' : j ≠ n := by omega
    simp [hj']

theorem deltaFun_eq (n : ℕ) (x : ℕ∪{∞}) :
    deltaFun n x = if x = (n : ℕ∪{∞}) then 1 else 0 := rfl

@[simp] theorem deltaFun_at (n : ℕ) : deltaFun n (n : ℕ∪{∞}) = 1 := by
  rw [deltaFun_eq, if_pos rfl]

theorem coe_ne_infty' (n : ℕ) : (n : ℕ∪{∞}) ≠ ∞ :=
  fun h => OnePoint.coe_ne_infty n h

@[simp] theorem deltaFun_infty (n : ℕ) : deltaFun n ∞ = 0 := by
  rw [deltaFun_eq, if_neg (by simp)]

/-- The element `n ↦ δ_n` of `boundedSeq(ℕ∪∞)`: a null sequence (vanishing at `∞`) of basis
vectors, uniformly bounded by `1`. -/
def deltaElem : ↥(boundedSeqSet (ℕ∪{∞})) :=
  ⟨fun n => deltaFun n, ⟨1, fun n k => by
    rw [deltaFun_eq]
    split <;> norm_num⟩⟩

/-- `δ_n` vanishes at `∞`, which is exactly the condition that the element `n ↦ δ_n` of
`boundedSeq(ℕ∪∞)` kills `ℤ[∞] ⊆ ℤ[ℕ∪∞]`. -/
theorem map_iota_deltaElem :
    boundedSeq.obj.map (LightCondensed.ι.op) deltaElem = 0 := by
  refine Subtype.ext (funext fun n => ContinuousMap.ext fun s => ?_)
  rw [show ((boundedSeq.obj.map (LightCondensed.ι.op)) deltaElem).1 n s = deltaFun n ∞ by rfl]
  exact (deltaFun_infty n).trans rfl

/-- **The null sequence `c : P ⟶ ∏^bnd ℤ` of REFS/03 §2**, sending `e_n` to the `n`-th basis
vector `δ_n`. -/
noncomputable def cBounded : P ⟶ boundedSeq :=
  P_homMk boundedSeq ((freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem) (by
    refine (freeHomEquiv (LightProfinite.of PUnit) boundedSeq).injective ?_
    rw [freeHomEquiv_zero]
    simp only [P_map]
    have hval : freeHomEquiv (ℕ∪{∞}) boundedSeq
        ((freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem) = deltaElem :=
      Equiv.apply_symm_apply _ _
    rw [freeHomEquiv_naturality, hval, map_iota_deltaElem])

/-- The defining property of `cBounded`: on `ℤ[ℕ∪∞]` it is the element `n ↦ δ_n` of
`boundedSeq(ℕ∪∞)`. -/
theorem P_proj_cBounded :
    P_proj ≫ cBounded = (freeHomEquiv (ℕ∪{∞}) boundedSeq).symm deltaElem :=
  P_proj_P_homMk _ _

end Work.ANALYTIC
