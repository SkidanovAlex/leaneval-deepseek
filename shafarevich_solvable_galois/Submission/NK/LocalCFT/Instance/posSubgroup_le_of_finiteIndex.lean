import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalCFT.Instance

/-- Every finite-index subgroup of `ℝˣ` contains the positive units.

`ℝˣ ≅ ℝ_{>0} × {±1}` and `ℝ_{>0}` is divisible, so it has no proper finite-index
subgroup: if `M` has index `n ≠ 0` and `x > 0`, write `x = y ^ n` with `y > 0`; then
`y ^ n ∈ M` because `Subgroup.index`-many powers of any element lie in the subgroup,
so `x ∈ M`. -/
theorem posSubgroup_le_of_finiteIndex (M : Subgroup ℝˣ) (hM : M.FiniteIndex) :
    Units.posSubgroup ℝ ≤ M := by
  intro x hx
  have hxpos : 0 < (x : ℝ) := hx
  have hn0 : M.index ≠ 0 := hM.index_ne_zero
  let y : ℝˣ := Units.mk0 ((x : ℝ) ^ ((M.index : ℝ)⁻¹))
    (ne_of_gt (Real.rpow_pos_of_pos hxpos _))
  have hyx : y ^ M.index = x := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact Real.rpow_inv_natCast_pow hxpos.le hn0
  have hmem : y ^ M.index ∈ M := Subgroup.pow_index_mem M y
  rwa [hyx] at hmem

end NK.LocalCFT.Instance
