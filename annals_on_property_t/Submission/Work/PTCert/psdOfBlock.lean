import Mathlib
import Submission.Work.PTCert.Chain

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions in `Submission/Work/PTCert/Chain.lean` (also Math.lean, Interfaces.lean).
Prove `PSDOfBlock`: for `v : ι → ℝ`, `vᵀMv = Σ_{x,y∈S} v x M x y v y` (rows/cols outside S vanish) `= (v|S)ᵀ M_S (v|S) ≥ 0`.
Symmetry: `M x y = M y x` holds on S×S by the block's hermitian-ness, and is `0 = 0` off S. ~60 lines.
-/

open scoped BigOperators

namespace Work.PTCert

open Submission.PTCert

/-- **(C4) PSD from a PSD principal block and zero elsewhere.**

If all rows and all columns of `M` indexed outside the finset `S` vanish and the principal
block `M x.1 y.1` on `S` is positive semidefinite, then `M` itself is positive semidefinite.

Hermitian-ness: on `S × S` it is the block's hermitian-ness, and off `S` both entries vanish
(one by the row condition, one by the column condition).  Quadratic form: the double sum
`Σ_{x,y} v x * (M x y * v y)` vanishes outside `S × S`, so it collapses to the double sum over
the subtype `S`, which is the quadratic form of the block evaluated at `v|S`. -/
theorem psdOfBlock : PSDOfBlock := by
  intro ι _instF _instD M S hrow hcol hblock
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- hermitian: `M` is symmetric
    rw [Matrix.isHermitian_iff_isSymm]
    ext x y
    rw [Matrix.transpose_apply]
    have hb : ∀ x y : S, M x.1 y.1 = M y.1 x.1 := by
      have hsym := Matrix.isHermitian_iff_isSymm.mp hblock.1
      intro x y
      have h := congr_fun (congr_fun hsym x) y
      simpa only [Matrix.transpose_apply, Matrix.of_apply] using h.symm
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact (hb ⟨x, hx⟩ ⟨y, hy⟩).symm
      · rw [hrow y x hy, hcol x y hy]
    · rw [hcol y x hx, hrow x y hx]
  · intro v
    -- the quadratic form of the block, at the restriction of `v` to `S`
    have hbq := hblock.dotProduct_mulVec_nonneg (fun x : S => v x.1)
    have hbq' : 0 ≤ ∑ x : S, ∑ y : S, v x.1 * (M x.1 y.1 * v y.1) := by
      simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
        using hbq
    -- the quadratic form of `M` collapses onto `S × S`
    have hexp : dotProduct (star v) (Matrix.mulVec M v)
        = ∑ x : S, ∑ y : S, v x.1 * (M x.1 y.1 * v y.1) := by
      rw [show dotProduct (star v) (Matrix.mulVec M v)
            = ∑ x : ι, ∑ y : ι, v x * (M x y * v y) from by
        simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]]
      -- restrict the outer sum to `S`
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by
        apply Finset.sum_eq_zero
        intro y _
        rw [hrow x y hx]; ring)]
      -- reindex `∑ x : S` as `∑ x ∈ S`
      rw [Finset.sum_coe_sort S (fun x : ι => ∑ y : S, v x * (M x y.1 * v y.1))]
      apply Finset.sum_congr rfl
      intro x hx
      -- restrict the inner sum to `S` as well
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun y _ hy => by rw [hcol x y hy]; ring)]
      rw [Finset.sum_coe_sort S (fun y : ι => v x * (M x y * v y))]
    rw [hexp]
    exact hbq'

end Work.PTCert
