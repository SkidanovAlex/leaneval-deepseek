import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.SuppSmall
import Submission.Work.EKLC7.SupportFacts
import Submission.Work.EKLC7.SuppSmallDerive

/-!
# C7: the support of a nontrivial leafwise measure on `U_ij`

`RootSupp` is component C7's final statement, but with the leafwise-measure input restricted to
the C7 interface `Work.EKLC7.P_RootProps` (clauses (U3), (U4), (U5), (U7), (U8) of the frozen
contract `P_Leafwise` for the root groups `U_ij`) rather than the full `P_Leafwise`.

Everything the statement needs from the leafwise system other than the ergodic dichotomy (U8) —
carriedness by `U_ij`, positivity on the neighbourhoods `V δ` of the identity, normalisation —
is a *field* of `Work.EKLContract.IsLeafwise`, which is the standing hypothesis here.  So the
proof is: extract (U8) from `P_RootProps`, which under `¬ CrossSection μ (U_ij)` gives
`ν x {1} = 0` a.e., and then combine

* `ν x ≠ δ₁` (since `δ₁ {1} = 1 ≠ 0`),
* `0 < ν x (ballU hij ε)` (`ballU_pos_of_carried_pos` from the `V δ`-positivity), and
* `∃ r ≠ 0, u_ij(r) ∈ (ν x).support` (`exists_uij_mem_support_of_carried`)

on the conull set of `IsLeafwise.conull`.
-/

namespace Work.EKLC7

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedSimpArgs false

/-- **C7 root-support statement, from the `P_RootProps` interface.**  If `ν` is a system of
leafwise measures for the root group `U_ij` of an `A`-ergodic probability measure `μ` on `X₃`
with no `U_ij`-cross-section, then a.e. `ν x` is not the Dirac mass at `1`, charges every ball
`ballU hij ε` (`ε > 0`), gives no mass to `{1}`, and has some `u_ij(r)`, `r ≠ 0`, in its
support. -/
theorem RootSupp :
    Work.EKLC7.P_RootProps →
    ∀ (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ],
      Work.EKLContract.IsAErgodic μ →
      ∀ {i j : Fin 3} (hij : i ≠ j)
        (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
        (X' : Set Work.EKLContract.X3),
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X' →
        ¬ Work.EKLContract.CrossSection μ (Work.EKLContract.Uij hij) →
        ∀ᵐ x ∂μ, ν x ≠ MeasureTheory.Measure.dirac 1
          ∧ (∀ ε : ℝ, 0 < ε → 0 < ν x (Work.EKLContract.ballU hij ε))
          ∧ ν x {1} = 0
          ∧ (∃ r : ℝ, r ≠ 0 ∧ Work.EKLContract.uij hij r ∈ (ν x).support) := by
  intro hPR μ _ hErg i j hij ν X' hLeaf hNoCross
  -- (U8) of the C7 interface: ergodicity + no cross-section ⇒ no atom at the identity a.e.
  obtain ⟨-, -, -, -, hU8⟩ := hPR μ hErg hij ν X' hLeaf
  have hν1 : ∀ᵐ x ∂μ, ν x {1} = 0 := hU8.resolve_left hNoCross
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := mem_ae_iff.mpr hLeaf.conull
  filter_upwards [hν1, hX'] with x hx1 hxX
  have hcarried := hLeaf.carried x hxX
  have hnorm := hLeaf.normalised x hxX
  -- the leafwise measure is non-zero: it is normalised by `ν x (Box1 U_ij) = 1`
  have hne : ν x ≠ 0 := by
    intro h0
    have hz : ν x (Box1 (Uij hij)) = 0 := by rw [h0]; simp
    rw [hz] at hnorm
    exact zero_ne_one hnorm
  refine ⟨?_, ?_, hx1, ?_⟩
  · -- `ν x ≠ δ₁` because `δ₁ {1} = 1` while `ν x {1} = 0`
    intro hdirac
    rw [hdirac, Measure.dirac_apply_of_mem (Set.mem_singleton 1)] at hx1
    exact one_ne_zero hx1
  · -- positivity on the balls, from positivity on the `V δ` and carriedness by `U_ij`
    exact ballU_pos_of_carried_pos hij (ν x) hcarried (hLeaf.pos x hxX)
  · -- a non-trivial point of the support, from `ν x ≠ 0` and `ν x {1} = 0`
    exact exists_uij_mem_support_of_carried hij (ν x) hcarried hx1 hne

end Work.EKLC7
