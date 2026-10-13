/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/EllExist.SmoothOpenSep` — separated-variable smoothness on the open quadrant

Two small closure facts for `Work.FTS.EllipticEst.SmoothOpen` used by
`FTS/EllExist/hkMem_orthSource_of_Fstar_smooth.lean`:

* `sep_mul_open` — a radial factor that is `C^n` on `(0,∞)` for every `n` times a factor that is
  `C^∞` (indeed analytic) in `θ` is `C^∞` on the open quadrant;
* `const_mul_open` — `SmoothOpen` is closed under multiplication by a constant.

They are verbatim copies of `Work.FTS.EllipticEst.SmoothOpen.sep_mul` and
`Work.FTS.EllipticEst.SmoothOpen.const_mul'` of
`Submission/Work/FTS/EllipticEst/EllHyp_certificates.lean`, reproduced here under local names
because that module is **import-incompatible** with the chain
`FTS/EllipticEst/Gsing_contDiffOn_ode_of_Fstar_facts` (which the area's existence nodes
`ellClassOk_exists_of_Fstar_smooth` need): both `FTS/EllipticEst/Fstar_Hk_le.lean` and
`FTS/EllipticEst/HkMem_FstarSin_open.lean` declare a constant named
`Work.FTS.EllipticEst.hasDerivAt_PsiInt`, so no module may import both, and a consumer that wants
the level-`k` existence node *and* the `HkMem` transfer for `orthSource g` would otherwise be
stuck.  **Action for the workspace owner: rename one of the two clashing declarations** (they are
in other areas' files, hence not edited here).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

set_option autoImplicit false

/-- A radial factor `C^n` on `(0,∞)` for every `n` times a `C^∞` angular factor is `C^∞` on the
open quadrant. -/
theorem sep_mul_open {g χ : ℝ → ℝ} (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0))
    (hχ : ContDiff ℝ ⊤ χ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z * χ θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => g p.1)
      Work.FTS.EllipticEst.Q0 :=
    (hg n).comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => χ p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hχn : ContDiff ℝ (n : WithTop ℕ∞) χ := hχ.of_le le_top
    exact hχn.contDiffOn.comp contDiffOn_snd fun p _ => Set.mem_univ p.2
  have hfun : Function.uncurry (fun z θ => g z * χ θ)
      = fun p : ℝ × ℝ => g p.1 * χ p.2 := rfl
  rw [hfun]
  exact h1.mul h2

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem const_mul_open (c : ℝ) {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * F z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at h ⊢
  intro n
  have hfun : Function.uncurry (fun z θ => c * F z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry F p := rfl
  rw [hfun]
  exact (contDiffOn_const (c := c)).mul (h n)

end Work.FTS.EllExist
