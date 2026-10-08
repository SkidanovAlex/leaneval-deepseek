import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.odd_subgroup_cyclic_or_fixes_line
import Submission.Work.L2F.Props.inverted_commute_of_common_fixed_point
import Submission.Work.L2F.Props.odd_order_mem_toPGL_range

namespace Work.L2F.Props

-- The normalization hypothesis `hN` is not needed by the argument below: an odd-order subgroup of
-- `PGL(2,F)` is cyclic or fixes a projective point, independently of `t`.
set_option linter.unusedVariables false in

/-- **Two `t`-inverted elements of an odd-order subgroup commute.**

In `PGL(2,F)`, let `K` have odd order, `t` an involution normalizing `K`, and `x, y ∈ K` be
inverted by `t` (`t x t⁻¹ = x⁻¹`, `t y t⁻¹ = y⁻¹`).  Then `x y = y x`.

The mechanism is the structure of odd-order subgroups of `PGL(2,F)`
(`Work.L2F.Props.odd_subgroup_cyclic_or_fixes_line`): such a subgroup is cyclic — and then
everything commutes — or fixes a point of the projective line, i.e. is contained in a Borel
subgroup; in a Borel subgroup the `t`-inverted elements of odd order are unipotent and commute
(`Work.L2F.Props.inverted_commute_of_common_fixed_point`). -/
theorem inverted_commute (F : Type*) [Field F] (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F))
    (hodd : Odd (Nat.card K)) (t : Matrix.ProjGenLinGroup (Fin 2) F) (ht : orderOf t = 2)
    (hN : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (x y : Matrix.ProjGenLinGroup (Fin 2) F) (hx : x ∈ K)
    (hy : y ∈ K) (hix : t * x * t⁻¹ = x⁻¹) (hiy : t * y * t⁻¹ = y⁻¹) : x * y = y * x := by
  have hxodd : Odd (orderOf x) := by
    rw [← Subgroup.orderOf_mk x hx]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_natCard (⟨x, hx⟩ : K))
  have hyodd : Odd (orderOf y) := by
    rw [← Subgroup.orderOf_mk y hy]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_natCard (⟨y, hy⟩ : K))
  rcases Work.L2F.Props.odd_subgroup_cyclic_or_fixes_line F K hodd with hcyc | ⟨v, hv, hfix⟩
  · -- `K` is cyclic, hence commutative: both `x` and `y` are powers of a generator.
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have hxi : (g : Matrix.ProjGenLinGroup (Fin 2) F) ^ i = x := by
      simpa using congrArg Subtype.val hi
    have hyj : (g : Matrix.ProjGenLinGroup (Fin 2) F) ^ j = y := by
      simpa using congrArg Subtype.val hj
    rw [← hxi, ← hyj, ← zpow_add, add_comm, zpow_add]
  · -- `K` fixes the line `F v`; both `x` and `y` are inverted and unipotent.
    obtain ⟨X, hX⟩ := Work.L2F.Props.odd_order_mem_toPGL_range F x hxodd
    obtain ⟨Y, hY⟩ := Work.L2F.Props.odd_order_mem_toPGL_range F y hyodd
    exact Work.L2F.Props.inverted_commute_of_common_fixed_point F t x y ht hix hiy hxodd hyodd
      v hv ⟨X, hX, hfix X (hX.symm ▸ hx)⟩ ⟨Y, hY, hfix Y (hY.symm ▸ hy)⟩

end Work.L2F.Props
