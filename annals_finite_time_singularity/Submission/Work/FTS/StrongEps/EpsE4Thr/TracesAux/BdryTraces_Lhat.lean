import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

open Work.FTS.Galerkin (Fn)

/-! ## Two glue lemmas for the radial multiplier `ψ(z) = 1/(1+z)` -/

/-- `ψ(z) = 1/(1+z)` is `C^∞` on `(0,∞)` in every finite order.  (This is the smoothness input
of `TracesAux.BdryTraces_psi_mul_open`, which asks for `∀ n, ContDiffOn ℝ n ψ (Ioi 0)`.) -/
private theorem contDiffOn_oneDiv :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 1 / (1 + z)) (Set.Ioi 0) := by
  intro n
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  positivity

/-- A radial multiplier preserves `SmoothOpen`: the product of a function `C^∞` on `(0,∞)` with a
function `C^∞` on the open quadrant is `C^∞` on the open quadrant. -/
private theorem smoothOpen_psi_mul {ψ : ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => ψ z * g z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => ψ p.1) Work.FTS.EllipticEst.Q0 :=
    (hψ n).comp contDiff_fst.contDiffOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hg.forall n
  exact h1.mul h2

/-- `BdryTraces` is closed under multiplication by a constant, in the pointwise form (the frozen
`ClassC.bdryTraces_smul` is stated with `c • f`). -/
private theorem bdryTraces_const_mul {α : ℝ} {k : ℕ} {f : Fn} (c : ℝ)
    (hf : Work.FTS.Nonlin.BdryTraces α k f) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => c * f z θ) :=
  Work.FTS.ClassC.bdryTraces_smul (α := α) (k := k) hf c

/-- **`BdryTraces α 4` of the clean operator `𝓛̂` on the class `ClassC`.**

`𝓛̂x = x + D_z x − 2x/(1+z) − 3D_θx/(1+z)` (`CoercivityFix.Lhat_eq`).  Its summands are

* `x` and `D_z x`: the `RegQo`-ports `EpsE4Thr.regQo_dth_dz` applied to `RegQo α 5 x` (which
  `ClassC` supplies: `SmoothOpen x`, `HkMem α 7 x`, `BdryTraces α 6 x`), plus monotonicity of
  `BdryTraces` in the level;
* `2x/(1+z)` and `3D_θx/(1+z)`: the open radial-multiplier lemma
  `TracesAux.BdryTraces_psi_mul_open` with `ψ = 1/(1+z)`, whose `Zop`-iterate bound is
  `PsiMul.zop_psi_bound` and whose smoothness is `PsiMul.contDiffOn_psi`;

the combinations are glued with `ClassC.bdryTraces_add` / `ClassC.bdryTraces_smul`
(which need the two summands to be `SmoothOpen`; the products with `ψ` are handled by
`NonlinRows.smoothOpen_mul` + `NonlinRows.smoothOpen_radial`). -/
theorem BdryTraces_Lhat {α : ℝ} (hα : 0 < α) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    Work.FTS.Nonlin.BdryTraces α 4 (Work.FTS.CoercivityFix.Lhat x) := by
  -- the `Zop`-iterate bound for `ψ(z) = 1/(1+z)` up to order `4`
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.PsiMul.zop_psi_bound 4
  -- `ClassC` supplies `RegQo α 5 x` (smoothness, `ℋ⁵`-membership, traces up to order `5`)
  have hsmQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry x)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall x).mp hx.reg
  have hreg5 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 x :=
    ⟨hx.reg,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 5) (l := 7)
        (by norm_num) hsmQ hx.mem,
      Work.FTS.ClassC.bdryTraces_mono (k := 5) (l := 6) (by norm_num) hx.tr⟩
  -- the two `RegQo`-ports at level `4`
  obtain ⟨hdth, hdz⟩ := Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz hα hreg5
  have htX : Work.FTS.Nonlin.BdryTraces α 4 x :=
    Work.FTS.ClassC.bdryTraces_mono (k := 4) (l := 6) (by norm_num) hx.tr
  have htZ : Work.FTS.Nonlin.BdryTraces α 4 (Work.Spaces.Dz x) := hdz.2.2
  have htT : Work.FTS.Nonlin.BdryTraces α 4 (Work.Spaces.Dth x) := hdth.2.2
  -- the first radial multiple `2x/(1+z)`
  have h2xsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * x z θ) :=
    hx.reg.const_mul' 2
  have h2xtr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ => 2 * x z θ) := bdryTraces_const_mul 2 htX
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (1 / (1 + z)) * (2 * x z θ)) :=
    smoothOpen_psi_mul (ψ := fun z => 1 / (1 + z)) (g := fun z θ => 2 * x z θ)
      contDiffOn_oneDiv h2xsm
  have hXtr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ => (1 / (1 + z)) * (2 * x z θ)) :=
    BdryTraces_psi_mul_open (k := 4)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 2 * x z θ)
      hK0 hKb contDiffOn_oneDiv h2xsm h2xtr
  -- the second radial multiple `3D_θx/(1+z)`
  have h3Tsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Work.Spaces.Dth x z θ) :=
    hx.reg.Dth.const_mul' 3
  have h3Ttr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ => 3 * Work.Spaces.Dth x z θ) :=
    bdryTraces_const_mul 3 htT
  have hYsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    smoothOpen_psi_mul (ψ := fun z => 1 / (1 + z)) (g := fun z θ => 3 * Work.Spaces.Dth x z θ)
      contDiffOn_oneDiv h3Tsm
  have hYtr : Work.FTS.Nonlin.BdryTraces α 4
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    BdryTraces_psi_mul_open (k := 4)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 3 * Work.Spaces.Dth x z θ)
      hK0 hKb contDiffOn_oneDiv h3Tsm h3Ttr
  -- the summand `x + D_z x`
  have hPsm : Work.FTS.EllipticEst.SmoothOpen (x + Work.Spaces.Dz x) :=
    Work.FTS.EllipticEst.smoothOpen_add (f := x) (g := Work.Spaces.Dz x) hx.reg hx.reg.Dz
  have hPtr : Work.FTS.Nonlin.BdryTraces α 4 (x + Work.Spaces.Dz x) :=
    Work.FTS.ClassC.bdryTraces_add (f := x) (g := Work.Spaces.Dz x) hx.reg hx.reg.Dz htX htZ
  -- the sum of the two radial multiples
  have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (1 / (1 + z)) * (2 * x z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add (f := fun z θ => (1 / (1 + z)) * (2 * x z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) hXsm hYsm
  have hQtr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ =>
      (1 / (1 + z)) * (2 * x z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    Work.FTS.ClassC.bdryTraces_add (f := fun z θ => (1 / (1 + z)) * (2 * x z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) hXsm hYsm hXtr hYtr
  -- its negative
  have hNQsm : Work.FTS.EllipticEst.SmoothOpen ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * x z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ))) :=
    hQsm.const_mul' (-1)
  have hNQtr : Work.FTS.Nonlin.BdryTraces α 4 ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * x z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ))) :=
    Work.FTS.ClassC.bdryTraces_smul hQtr (-1)
  -- the operator unfolds to that sum
  have hL : Work.FTS.CoercivityFix.Lhat x = (x + Work.Spaces.Dz x) + (-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * x z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) := by
    funext z θ
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hL]
  exact Work.FTS.ClassC.bdryTraces_add (f := x + Work.Spaces.Dz x)
    (g := (-1 : ℝ) • (fun z θ => (1 / (1 + z)) * (2 * x z θ)
      + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)))
    hPsm hNQsm hPtr hNQtr

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
