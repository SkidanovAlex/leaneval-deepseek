import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSBase
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSBnd
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000


/-- **The expansion of `D_z^j (radS α f)`** on `(0,∞)`, `j ≤ 3`, in the open class. -/
theorem radS_DzdIter_eq_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) {j : ℕ} (hj : j ≤ 3) :
    ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z
      = -(Work.FTS.CoercivityFix.Transfer.E2pkg.W1 α f j z)
        + Work.FTS.CoercivityFix.Transfer.E2pkg.W2 α f j z
        + Work.FTS.CoercivityFix.Transfer.E2pkg.W3 α f j z := by
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5
  have hsmA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) IoiA :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α
  have hsmB5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) IoiA :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampB_five α
  -- the three summands
  set U1 : ℝ → ℝ := fun z =>
    -(Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) with hU1
  set U2 : ℝ → ℝ := fun z =>
    Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Elliptic.Qang f 0 z with hU2
  set U3 : ℝ → ℝ := fun z =>
    (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
      * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 with hU3
  -- differentiability of the coefficient iterates
  have hA1diff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)) z := by
    intro c hc z hz
    have hdc : Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)
        = Work.Elliptic.DzdIter (c + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) := by
      rw [show Work.FTS.CoercivityFix.Transfer.dAmpA α
          = Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampA α) from rfl]
      exact Work.FTS.Nonlinear.Pieces.DzdIter_add c 1 _
    rw [hdc]
    have hc4 : c + 1 ≤ 4 := by omega
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
      hsmA5 hc4 hz
  have hA2diff : ∀ c ≤ 4, ∀ z ∈ IoiA,
      DifferentiableAt ℝ
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampA α)) z :=
    fun c hc z hz =>
      Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
        hsmA5 hc hz
  have hsmL : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) IoiA :=
    contDiffOn_four_L12f α hα hα1 hO hmem5
  have hLdiff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z := by
    intro c hc z hz
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_general
      (N := 4) hsmL (by omega) hz
  have hQdiff : ∀ c ≤ 2, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Elliptic.Qang f 0 z)) z := by
    intro c hc z hz
    refine (differentiableAt_Qang_open hO hmem4 hc hz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact DzdIter_Qang_open hO hmem4 c (by omega) w hw
  have hA3sm : ContDiffOn ℝ 4
      (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α) IoiA := by
    have h1 : (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
        = fun z => Work.Spaces.Zop^[1] (Work.FTS.CoercivityFix.Transfer.ampB α) z
            / Work.Spaces.c α := by
      funext z; rfl
    rw [h1]
    exact (Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' 1 4
      (hsmB5.of_le (Nat.cast_le.mpr (by norm_num : 5 ≤ 5)))).div_const _
  have hA3diff : ∀ c ≤ 3, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z : ℝ =>
        Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)) z := by
    intro c hc z hz
    have hc4 : c + 1 ≤ 4 := by omega
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_general
      (N := 4) hA3sm hc4 hz
  have hU12 : ∀ b < j, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (U1 + U2)) z := by
    intro b hb z hz
    have hu : ∀ c ≤ b, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c U1) z' := by
      intro c hc z' hz'
      have hcons : U1 = fun z => (-1 : ℝ) *
          (Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) := by
        rw [hU1]; funext w; ring
      rw [hcons]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
      exact (Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA1diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hLdiff c (by omega) z'' hz'') hz').const_mul (-1)
    have hv : ∀ c ≤ b, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c U2) z' := by
      intro c hc z' hz'
      exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA2diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hQdiff c (by omega) z'' hz'') hz'
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_add_of (j := b) hu hv hz
  have hU3diff : ∀ b < j, ∀ z ∈ IoiA,
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b U3) z := by
    intro b hb z hz
    have hcons : U3 = fun z => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α) := by
      rw [hU3]; funext w; ring
    rw [hcons, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
    exact (hA3diff b (by omega) z hz).const_mul _
  -- the expansion
  have hsplit : ∀ z ∈ IoiA,
      Work.FTS.CoercivityFix.Transfer.radS α f z = (U1 + U2 + U3) z := by
    intro z hz
    have h := radS_split_O α hα hα1 hO hmem4 hl12 z hz
    rw [h]
    simp only [hU1, hU2, hU3, Pi.add_apply]
  have hexp : ∀ z ∈ IoiA,
      Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z
        = Work.Elliptic.DzdIter j (U1 + U2 + U3) z :=
    fun z hz => Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hsplit j z hz
  have e1 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (U1 + U2 + U3) z
      = Work.Elliptic.DzdIter j (U1 + U2) z + Work.Elliptic.DzdIter j U3 z := by
    intro z hz
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j (U1 + U2) U3 hU12 hU3diff
      z hz
  have e2 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j (U1 + U2) z
      = Work.Elliptic.DzdIter j U1 z + Work.Elliptic.DzdIter j U2 z := by
    intro z hz
    have h1 : ∀ b < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b U1) z' := by
      intro b hb z' hz'
      have hcons : U1 = fun z => (-1 : ℝ) *
          (Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z) := by
        rw [hU1]; funext w; ring
      rw [hcons]
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
      exact (Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA1diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hLdiff c (by omega) z'' hz'') hz').const_mul (-1)
    have h2 : ∀ b < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b U2) z' := by
      intro b hb z' hz'
      exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of
        (hu := fun c _ z'' hz'' => hA2diff c (by omega) z'' hz'')
        (hv := fun c _ z'' hz'' => hQdiff c (by omega) z'' hz'') hz'
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j U1 U2 h1 h2 z hz
  have e3 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U1 z
      = -(Work.FTS.CoercivityFix.Transfer.E2pkg.W1 α f j z) := by
    intro z hz
    have hub : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ
          (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.dAmpA α)) z' :=
      fun c hc z' hz' => hA1diff c (by omega) z' hz'
    have hvb : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z' :=
      fun c hc z' hz' => hLdiff c (by omega) z' hz'
    have hlei := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
      (Work.FTS.CoercivityFix.Transfer.dAmpA α) (Work.Coercivity.L12f f) hub hvb z hz
    have hA1 : ∀ b, Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.dAmpA α)
        = Work.Elliptic.DzdIter (b + 1) (Work.FTS.CoercivityFix.Transfer.ampA α) := by
      intro b
      rw [show Work.FTS.CoercivityFix.Transfer.dAmpA α
          = Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampA α) from rfl]
      exact Work.FTS.Nonlinear.Pieces.DzdIter_add b 1 _
    have hneg : Work.Elliptic.DzdIter j U1 z = - Work.Elliptic.DzdIter j (fun w =>
        Work.FTS.CoercivityFix.Transfer.dAmpA α w * Work.Coercivity.L12f f w) z := by
      rw [hU1, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_neg]
    rw [hneg, hlei, Work.FTS.CoercivityFix.Transfer.E2pkg.W1]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hA1 b]
    ring
  have e4 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U2 z
      = Work.FTS.CoercivityFix.Transfer.E2pkg.W2 α f j z := by
    intro z hz
    have hub : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ
          (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampA α)) z' :=
      fun c hc z' hz' => hA2diff c (by omega) z' hz'
    have hvb : ∀ c < j, ∀ z' ∈ IoiA,
        DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Elliptic.Qang f 0 z)) z' :=
      fun c hc z' hz' => hQdiff c (by omega) z' hz'
    have hlei := Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j
      (Work.FTS.CoercivityFix.Transfer.ampA α) (fun z => Work.Elliptic.Qang f 0 z) hub hvb z hz
    rw [show U2 = fun z => Work.FTS.CoercivityFix.Transfer.ampA α z
        * Work.Elliptic.Qang f 0 z from hU2, hlei, Work.FTS.CoercivityFix.Transfer.E2pkg.W2]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [DzdIter_Qang_open hO hmem4 (j - b) (by
      have := Finset.mem_range.mp hb; omega) z hz]
    ring
  have e5 : ∀ z ∈ IoiA, Work.Elliptic.DzdIter j U3 z
      = Work.FTS.CoercivityFix.Transfer.E2pkg.W3 α f j z := by
    intro z hz
    have hfun : U3 = fun z => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * ((Work.Spaces.c α)⁻¹
            * Work.Elliptic.DzdIter 1 (Work.FTS.CoercivityFix.Transfer.ampB α) z) := by
      rw [hU3]; funext w
      simp only [Work.FTS.CoercivityFix.Transfer.dAmpB, Work.Elliptic.DzdIter_succ,
        Work.Elliptic.DzdIter_zero, Work.Elliptic.Dzd]
      ring
    rw [hfun, Work.FTS.CoercivityFix.Transfer.E2pkg.W3,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul,
      show Work.Elliptic.DzdIter j (Work.Elliptic.DzdIter 1
            (Work.FTS.CoercivityFix.Transfer.ampB α))
          = Work.Elliptic.DzdIter (j + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) from
        Work.FTS.Nonlinear.Pieces.DzdIter_add j 1 _]
    ring
  intro z hz
  rw [hexp z hz, e1 z hz, e2 z hz, e3 z hz, e4 z hz, e5 z hz]

/-! ## The pointwise majorant -/

end Work.FTS.StrongEps.EpsE4Thr.E2O
