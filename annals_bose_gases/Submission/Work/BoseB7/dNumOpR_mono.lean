import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.dNumOpR_mono` — monotonicity of `dNumOpR` in the region

FS's quadratic Bogoliubov operator restricted to a momentum region is
`dNumOpR E R = (2π)^{-3}ℓ³∫_R 𝒟_k b_k†b_k dk = ∑_{k ∈ R} 𝒟_k b_k†b_k`, and
`b_k†b_k` is a positive operator, exactly as `a_k†a_k` is: `b_k†` is the adjoint
of `b_k = a_k + α_k a_{-k}†` **for every** `α` (no evenness needed).  Hence for a
nonnegative symbol `𝒟 ≥ 0` the quadratic form `⟨f, dNumOpR E R f⟩` is monotone in
the region `R`.

This is used throughout the small-box program (`SmallBoxD1Final`, the `P_H`/`P_L`
splittings of FS §7–§10), where one enlarges a region and needs
`⟨f, (∫_R D b†b) f⟩ ≤ ⟨f, (∫_{R'} D b†b) f⟩`.

## Contents

* `bp_bOpDag` — `b_k†` is the adjoint of `b_k` (any squeezing `α`),
* `bp_bNumOp_nonneg` — `⟨f, b_k†b_k f⟩ = ‖b_k f‖² ≥ 0`,
* `bp_dNumOpR` — the quadratic form of `dNumOpR` as the region sum of the above,
* `dNumOpR_mono` — the requested monotonicity.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

section Helpers

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

omit [DecidableEq Mode] in
/-- `b_k† = a_k† + α_k a_{-k}` is the adjoint of `b_k = a_k + α_k a_{-k}†`, for
*every* squeezing function `α` (evenness of `α` is not needed). -/
theorem bp_bOpDag (F : FockData Mode) (α : Mode → ℝ) (i : Mode) (f g : F.H) :
    F.bp (F.bOpDag α i f) g = F.bp f (F.bOp α i g) := by
  simp only [FockData.bOpDag, FockData.bOp, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [F.aDag_adjoint i f g, F.bp_symm (F.a (-i) f) g, ← F.aDag_adjoint (-i) g f,
    F.bp_symm (F.aDag (-i) g) f]

omit [DecidableEq Mode] in
/-- The quadratic form `⟨f, b_k†b_k f⟩` is the square of the Fock norm of `b_kf`,
hence nonnegative. -/
theorem bp_bNumOp_nonneg (F : FockData Mode) (α : Mode → ℝ) (i : Mode) (f : F.H) :
    0 ≤ F.bp (F.bNumOp α i f) f := by
  rw [FockData.bNumOp, LinearMap.comp_apply, bp_bOpDag F α i (F.bOp α i f) f]
  exact F.bp_nonneg _

/-- The quadratic form of `dNumOpR E R = ∑_{k∈R} 𝒟_k b_k†b_k` is the region sum
of the weighted single-mode forms `𝒟_k ⟨f, b_k†b_k f⟩`
(the `(2π)^{-3}ℓ³∫_R … dk` of FS is the normalised sum `∑_{k∈R}`). -/
theorem bp_dNumOpR (F : FockData Mode) (E : Q3Env Mode) (R : Mode → Prop)
    [DecidablePred R] (g : F.H) :
    F.bp (F.dNumOpR E R g) g =
      ∑ i ∈ (excited Mode).filter R, E.D i * F.bp (F.bNumOp E.alpha i g) g := by
  simp only [FockData.dNumOpR, FockData.regionSum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]

end Helpers

/-- **Monotonicity of `dNumOpR` in the region.**  If `R ⊆ R'` and the Bogoliubov
symbol `𝒟` is nonnegative, then enlarging the region can only increase the
quadratic form `⟨f, (2π)^{-3}ℓ³∫_R 𝒟_k b_k†b_k dk f⟩`. -/
theorem dNumOpR_mono {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    {R R' : Mode → Prop} [DecidablePred R] [DecidablePred R']
    (hsub : ∀ i, R i → R' i) (hD : ∀ i, 0 ≤ E.D i) (f : F.H) :
    F.bp (F.dNumOpR E R f) f ≤ F.bp (F.dNumOpR E R' f) f := by
  rw [bp_dNumOpR F E R f, bp_dNumOpR F E R' f]
  have hst : (excited Mode).filter R ⊆ (excited Mode).filter R' := by
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hsub i hi.2⟩
  have hsd := Finset.sum_sdiff hst (f := fun i => E.D i * F.bp (F.bNumOp E.alpha i f) f)
  have hnn : 0 ≤ ∑ x ∈ (excited Mode).filter R' \ (excited Mode).filter R,
      E.D x * F.bp (F.bNumOp E.alpha x f) f :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hD i) (bp_bNumOp_nonneg F E.alpha i f)
  linarith [hsd, hnn]

end Work.BoseB7
