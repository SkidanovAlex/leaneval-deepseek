import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.OpenPkg.QangOpen
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.Coercivity.L12_facts_n
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadS

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

abbrev IoiA : Set ℝ := Set.Ioi (0 : ℝ)

/-! ## Bridges between the two `L₁₂` vocabularies -/

/-- `Coercivity.L12f` is the paper's `L₁₂`. -/
theorem L12f_eq_elliptic (f : ℝ → ℝ → ℝ) :
    Work.Coercivity.L12f f = Work.Elliptic.L12 f :=
  Work.Coercivity.L12f_eq_Elliptic_L12 f

/-- `Construction.L12` is the paper's `L₁₂`. -/
theorem constructionL12_eq_elliptic (f : ℝ → ℝ → ℝ) :
    Work.Construction.L12 f = Work.Elliptic.L12 f :=
  Work.FTS.H2.constructionL12_eq_ellipticL12 f

/-! ## `L₁₂ f` is `C⁴` on `(0,∞)` in the open class -/

/-- **`L₁₂ f` is `C⁴` on `(0,∞)`** for a smooth-open, `ℋ⁵`-honest datum. -/
theorem contDiffOn_four_L12f (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi 0) := by
  have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 5 f hO hmem5
    (by norm_num : 2 ≤ 5)).1
  rw [← L12f_eq_elliptic f] at h
  exact h

/-! ## The index-raising recursion for `L₁₂ f` -/

/-- **`D_z^c (L₁₂ f) = −Qang f (c−1)`** on `(0,∞)`, for `1 ≤ c ≤ 3` (the `OpenPkg` bundle). -/
theorem DzdIter_L12f_eq_neg_Qang_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem4 : Work.Spaces.HkMem α 4 f)
    (hl12 : Work.Construction.L12 f 0 = 0) :
    ∀ c : ℕ, 1 ≤ c → c ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z = - Work.Elliptic.Qang f (c - 1) z := by
  have h0e : Work.Elliptic.L12 f 0 = 0 := by
    rw [← constructionL12_eq_elliptic f]; exact hl12
  have hb := Work.FTS.OpenPkg.l12_open_bundle α f hα hα1 hO hmem4 h0e
  intro c hc hc3 z hz
  have h := hb.1 (c - 1) (by omega) z hz
  rw [show c - 1 + 1 = c from by omega] at h
  rw [L12f_eq_elliptic]
  exact h

/-! ## The angular-moment tower in the open class -/

/-- **`D_z^i (Qang f 0) = Qang f i` on `(0,∞)`** for `i ≤ 3`. -/
theorem DzdIter_Qang_open {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ i ≤ 3, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z) z = Work.Elliptic.Qang f i z := by
  have hderiv : ∀ j ≤ 2, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang f j z) (Work.Elliptic.Qang f (j + 1) z / z) z :=
    fun j hj z hz => Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α f hO hmem hj hz
      (Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α f hO hmem (by omega))
  intro i
  induction i with
  | zero => intro _ z _; rfl
  | succ i ih =>
      intro hi z hz
      have hprev : Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z)
          =ᶠ[𝓝 z] (fun w => Work.Elliptic.Qang f i w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih (by omega) w hw
      show z * deriv (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z)) z
        = Work.Elliptic.Qang f (i + 1) z
      rw [hprev.deriv_eq, (hderiv i (by omega) z hz).deriv]
      field_simp

/-- The angular moments `Qang f i` are differentiable on `(0,∞)` for `i ≤ 2`. -/
theorem differentiableAt_Qang_open {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {i : ℕ}
    (hi : i ≤ 2) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z => Work.Elliptic.Qang f i z) z :=
  ((Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α f hO hmem hi hz
    (Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α f hO hmem (by omega))).differentiableAt)

/-! ## The decomposition of `radS` on `(0,∞)` -/

/-- **The decomposition of `radS` on `(0,∞)`**: with `z·(L₁₂ f)' = −Qang f 0`, the middle term
`−a(z)·z·(L₁₂ f)'(z)` becomes `+a(z)·Qang f 0 z`. -/
theorem radS_split_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem4 : Work.Spaces.HkMem α 4 f)
    (hl12 : Work.Construction.L12 f 0 = 0) :
    ∀ z ∈ IoiA,
      Work.FTS.CoercivityFix.Transfer.radS α f z
        = -(Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z)
          + Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Elliptic.Qang f 0 z
          + (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
  intro z hz
  have hQ := Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_zero_eq_integral f z
  have h := DzdIter_L12f_eq_neg_Qang_O α hα hα1 hO hmem4 hl12 1 le_rfl (by norm_num) z hz
  have h1 : Work.Elliptic.DzdIter 1 (Work.Coercivity.L12f f) z
      = z * deriv (Work.Coercivity.L12f f) z := rfl
  rw [h1] at h
  simp only [Work.FTS.CoercivityFix.Transfer.radS]
  rw [h, show (1 : ℕ) - 1 = 0 from rfl, hQ]
  ring_nf


end Work.FTS.StrongEps.EpsE4Thr.E2O
