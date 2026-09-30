import Mathlib
import Submission.Work.BW.sieg2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The `q`-th mixed coordinate of an algebraic integer `x : 𝓞 F`, viewed as a `ℤ`-linear
functional.  It is the composition of the (integer linear) embedding of `𝓞 F` into the mixed
space `mixedSpace F = ℝ^{r₁} × ℂ^{r₂}` with the coordinate functional `repr q` of the standard
basis `mixedEmbedding.stdBasis F`. -/
noncomputable def siegCoordLin {F : Type*} [Field F] [NumberField F]
    (q : NumberField.mixedEmbedding.index F) : NumberField.RingOfIntegers F →ₗ[ℤ] ℝ where
  toFun x := (NumberField.mixedEmbedding.stdBasis F).repr
    (NumberField.mixedEmbedding F ((x : NumberField.RingOfIntegers F) : F)) q
  map_add' x y := by
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add]
    rfl
  map_smul' n x := by
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_zsmul, Finsupp.smul_apply]
    simp

/-- `siegCoordLin` evaluates on a single element to `siegCoord` evaluated on the corresponding
one-term tuple. -/
theorem siegCoordLin_apply {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (v : Fin N → NumberField.RingOfIntegers F) (j : Fin N)
    (q : NumberField.mixedEmbedding.index F) :
    siegCoordLin q (v j) = siegCoord v j q := rfl

theorem sieg2_coord_sum {F : Type*} [Field F] [NumberField F] {N K : ℕ}
    (t : Fin K → ℤ) (v : Fin K → (Fin N → NumberField.RingOfIntegers F)) (j : Fin N)
    (q : NumberField.mixedEmbedding.index F) :
    (NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F
          ((∑ i, t i • v i j : NumberField.RingOfIntegers F) : F)) q
      = ∑ i, (t i : ℝ) * Work.BW.siegCoord (v i) j q := by
  simp only [Work.BW.siegCoord]
  have h : siegCoordLin (F := F) q (∑ i, t i • v i j)
      = ∑ i, (t i : ℝ) * siegCoordLin (F := F) q (v i j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, zsmul_eq_mul]
  exact h

end Work.BW
