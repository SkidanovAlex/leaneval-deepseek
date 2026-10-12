import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem normSq_a_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn M : ℝ)
    (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (k : Mode) (f : F.H) (hf : T.NWindow M f) :
    F.normSq (F.a k f) ≤ Cn * M * F.normSq f := by
  -- `‖a_k f‖² = ⟨f, a_k†a_k f⟩`
  have h1 : F.normSq (F.a k f) = F.bp (F.nOp k f) f := by
    show F.bp (F.a k f) (F.a k f) = F.bp (F.nOp k f) f
    exact (F.aDag_adjoint k (F.a k f) f).symm
  -- the quadratic form of the full sum is the sum of the (nonnegative) quadratic forms
  have hsum : F.bp ((∑ j : Mode, F.nOp j) f) f = ∑ j : Mode, F.bp (F.nOp j f) f := by
    simp only [LinearMap.sum_apply, map_sum]
  -- the `k`-th term is dominated by the whole sum
  have h2 : F.bp (F.nOp k f) f ≤ F.bp ((∑ j : Mode, F.nOp j) f) f := by
    rw [hsum]
    exact Finset.single_le_sum (fun j _ => Work.BoseB7.bp_nOp_nonneg F j f) (Finset.mem_univ k)
  -- the window converts `n₊` into `𝓜`
  have h4 : F.bp (T.N f) f ≤ M * F.normSq f := Work.BoseB7A.NWindow_bp_N_le F T hM hf
  calc F.normSq (F.a k f) = F.bp (F.nOp k f) f := h1
    _ ≤ F.bp ((∑ j : Mode, F.nOp j) f) f := h2
    _ ≤ Cn * F.bp (T.N f) f := hBessel f
    _ ≤ Cn * (M * F.normSq f) := mul_le_mul_of_nonneg_left h4 hCn0
    _ = Cn * M * F.normSq f := by ring

end Work.BoseBoxFock
