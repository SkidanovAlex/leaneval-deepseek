import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7A

theorem completing_square {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (b Y : F.H →ₗ[ℝ] F.H) (c : ℝ) (hc : 0 < c) (Φ : F.H) :
    0 ≤ c * F.bp (b Φ) (b Φ) + 2 * F.bp (b Φ) (Y Φ) + c⁻¹ * F.bp (Y Φ) (Y Φ) := by
  -- Completing the square in the quadratic form `bp`:
  -- `c·⟨bx,bx⟩ + 2⟨bx,Yx⟩ + c⁻¹⟨Yx,Yx⟩ = c⁻¹·⟨c·bx + Yx, c·bx + Yx⟩ ≥ 0`.
  set x := b Φ
  set y := Y Φ
  have hexp : F.bp (c • x + y) (c • x + y)
      = c ^ 2 * F.bp x x + 2 * c * F.bp x y + F.bp y y := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [F.bp_symm y x]
    ring
  have hz : 0 ≤ F.bp (c • x + y) (c • x + y) := F.bp_nonneg _
  have hgoal : c * F.bp x x + 2 * F.bp x y + c⁻¹ * F.bp y y
      = c⁻¹ * F.bp (c • x + y) (c • x + y) := by
    rw [hexp]
    field_simp
  rw [hgoal]
  exact mul_nonneg (inv_nonneg.mpr hc.le) hz

end Work.BoseB7A
