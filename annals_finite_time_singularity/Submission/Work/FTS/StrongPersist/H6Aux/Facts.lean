/-
# `Work.FTS.StrongPersist.H6Aux.Facts` — smoothness, membership and norm facts

The level-six one-sided bound of `H6Lin` is proved by the paper's *commutator* induction on the
family `IPnG 1 1 α n`, `n ≤ 5`, for the clean operator `Lhat = 𝓛 − Transport` (whose `D_z`- and
`D_θ`-commutators `Dth (Lhat h) = Lhat (Dth h)`,
`Dz (Lhat h) = Lhat (Dz h) + Ê₂ h` are the paper's defect identities).  Running the induction
needs a handful of elementary facts about `Lhat` and the level comparisons of the weighted
norms, collected here:

* `smoothOpen_Lhat`, `q0Sm_Lhat` — smoothness of `Lhat g` on the open quadrant;
* `HkSq_mono_order` — monotonicity of `HkSq` in the order (pointwise in the integrand);
* `HkSq_Dth_le_succ'`, `HkSq_Dz_le_succ'` — the two shift dominations `D_θ`, `D_z`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.IPChains
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6LocOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Smoothness of `Lhat` -/

/-- `Lhat g` is `C^∞` on the open quadrant whenever `g` is. -/
theorem smoothOpen_Lhat {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Lhat g) := by
  have hloc := Work.FTS.StrongPersist.locOp_smoothOpen hg
  have hneg : Work.FTS.CoercivityFix.Lhat g = fun z θ => -(Work.FTS.StrongPersist.locOp g z θ) := by
    funext z θ
    simp only [Work.FTS.CoercivityFix.Lhat, Work.FTS.StrongPersist.locOp, Pi.sub_apply,
      Pi.neg_apply]
    ring
  rw [hneg]
  rw [Work.FTS.EllipticEst.SmoothOpen] at hloc ⊢
  have hfun : Function.uncurry (fun z θ => -(Work.FTS.StrongPersist.locOp g z θ))
      = fun p : ℝ × ℝ => -(Function.uncurry (Work.FTS.StrongPersist.locOp g) p) := rfl
  rw [hfun]
  exact hloc.neg

/-- `Lhat g` is `C^m` on the open quadrant for every `m`. -/
theorem q0Sm_Lhat {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) (m : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm m (Work.FTS.CoercivityFix.Lhat g) :=
  Work.FTS.StrongPersist.q0Sm_of_smoothOpen (smoothOpen_Lhat hg) m

/-! ## Monotonicity and shift dominations of `HkSq` -/

/-- **Monotonicity of `HkSq` in the order.** -/
theorem HkSq_mono_order (α : ℝ) {m k : ℕ} (hmk : m ≤ k) {f : Fn}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α m f ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m f z θ) hf.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m f z θ)
    (hf.1 z hz) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => ?_
  exact Work.FTS.StrongPersist.HkIntegrand_le_of_le α hmk f z θ

/-- **The `D_θ`-shift domination**: `|D_θ f|²_{ℋ^m} ≤ |f|²_{ℋ^{m+1}}`. -/
theorem HkSq_Dth_le_succ' (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (m : ℕ) {f : Fn}
    (hm : Work.Spaces.HkMem α (m + 1) f) :
    Work.Spaces.HkSq α m (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (m + 1) f :=
  Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α hα m hm

/-- **The `D_z`-shift domination**: `|D_z f|²_{ℋ^m} ≤ |f|²_{ℋ^{m+1}}`. -/
theorem HkSq_Dz_le_succ' (α : ℝ) (m : ℕ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α (m + 1) f) :
    Work.Spaces.HkSq α m (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (m + 1) f :=
  Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α m
    (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (m + 1)) hm

end Work.FTS.StrongPersist.H6Aux
