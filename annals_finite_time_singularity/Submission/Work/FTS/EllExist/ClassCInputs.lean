/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.EllExist.ClassCInputs` — the easy adapters from `ClassC`-shaped data to the area's inputs

The lead design of 2026-10-08 (`FTS/FTS_HARD_DESIGN.md` §(A), item **A2**) feeds the area's
corrected existence node `Work.FTS.EllExist.ellClassOk_exists_of_Fstar_smooth k` from the new
linear class `ClassC` (`Submission/Work/FTS/FTS_HARD_STMTS.lean.txt`):

```
structure ClassC (α : ℝ) (g : Fn) : Prop where
  norm  : normTh g = g
  reg   : SmoothOpen g
  mem   : HkMem α 7 g
  tr    : BdryTraces α 6 g
  fsm   : ∀ m : ℕ, ContDiffOn ℝ m (Fstar g) (Ioi 0)
  axis  : ∀ θ ∈ Ioo 0 (π/2), Tendsto (fun z => g z θ / z) (𝓝[>] 0) (𝓝 0)
  l12   : L12 g 0 = 0
```

The existence node consumes, for the *orthogonalised* source `orthSource g`:

* `SmoothOpen (orthSource g)`                           — **proved here** (`smoothOpen_orthSource_of_Fstar_smooth`);
* the decay of `orthSource g` at `z → ∞`                — **proved here**
  (`tendsto_orthSource_atTop_of`), from the pointwise decay of `g` and of `F_*(g)`;
* `HkMem α k (orthSource g)`                            — delegated, see
  `FTS/EllExist/hkMem_orthSource_of_Fstar_smooth.lean`;
* the remaining inputs (`F_* ∈ C^∞(0,∞)`, `IntegrableOn (F_*(r)/r)`, `L2Mem g`) come from the
  class fields `fsm` and from `mem` (`L2Mem g` follows from `HkMem α 0 g` and `SmoothOpen g`).

The instantiation at `k = 7` is therefore

```
ellClassOk_exists_of_Fstar_smooth 7 α g
  (smoothOpen_orthSource_of_Fstar_smooth hreg hfsm)
  (hkMem_orthSource_of_Fstar_smooth hα hα1 hreg hmem hfsm)
  (tendsto_orthSource_atTop_of hdecg hdecF)
  hfsm hFint hL2
: ∃ Ψ, EllClassOk 7 α g Ψ
```
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllExist.Defs
import Submission.Work.FTS.EllExist.Shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `(z,θ) ↦ sin 2θ · F_*(g) z` is `C^n` on the open quadrant as soon as `F_*(g)` is `C^n` on
`(0,∞)`. -/
theorem contDiffOn_Fstar_mul_sin_two {g : Fn} (n : ℕ)
    (hF : ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Elliptic.Fstar g p.1 * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.Elliptic.Fstar g p.1)
      Work.FTS.EllipticEst.Q0 :=
    hF.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  exact h1.mul h2

/-- **Smoothness of the orthogonalised source.**  If `g` is `C^∞` on the open quadrant and its
angular moment `F_*(g)` is `C^∞` on `(0,∞)`, then so is
`orthSource g = g - (15/4)·sin 2θ·F_*(g)`. -/
theorem smoothOpen_orthSource_of_Fstar_smooth {g : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hF : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry g) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hsm n
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (15 / 4) * (Work.Elliptic.Fstar g p.1 * Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const (c := (15 / 4 : ℝ))).mul (contDiffOn_Fstar_mul_sin_two n (hF n))
  have hfun : Function.uncurry (Work.Elliptic.orthSource g)
      = fun p : ℝ × ℝ => Function.uncurry g p
          - (15 / 4) * (Work.Elliptic.Fstar g p.1 * Real.sin (2 * p.2)) := by
    funext p
    simp only [Function.uncurry, Work.Elliptic.orthSource]
    ring
  rw [hfun]
  exact h1.sub h2

/-- **Decay of the orthogonalised source.**  If every angular slice of `g` and the angular moment
`F_*(g)` tend to `0` at `z → ∞`, then so does every slice of `orthSource g`. -/
theorem tendsto_orthSource_atTop_of {g : Fn}
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => g z θ) atTop (𝓝 0))
    (hFdec : Tendsto (fun z => Work.Elliptic.Fstar g z) atTop (𝓝 0)) :
    ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0) := by
  intro θ hθ
  have hfun : (fun z => Work.Elliptic.orthSource g z θ)
      = fun z => g z θ - (15 / 4) * (Real.sin (2 * θ) * Work.Elliptic.Fstar g z) := by
    funext z
    simp only [Work.Elliptic.orthSource]
    ring
  rw [hfun]
  simpa using (hdec θ hθ).sub ((hFdec.const_mul (Real.sin (2 * θ))).const_mul (15 / 4))

end Work.FTS.EllExist
