/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/RegQoClosure.lean` — the linear closure of the open
# class `RegQo`, and its `CoerAdmO` companion

`OpenClass.RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f` is the class on which the
open-quadrant coercivity interface `UnifIPO` is stated, and it is the class the level-four barrier
of the projected `ε`-scheme meets (`OpenBarrier.coerAdmO_slice_JfamP`).  The chapter already had
`regQo_mono` (`RegQo α l → RegQo α k` for `k ≤ l`) and `regQo_const_mul` (`f ↦ c * f`).

What this module adds is the closure of `RegQo` under **addition, negation and subtraction** — the
three operations by which the explicit pieces of the scheme's right-hand side (and their
mollification defects) are built.  The three ingredients are all already in the tree:

* `EllipticEst.smoothOpen_add` / `smoothOpen_sub` (`SmoothOpenAdd.lean`, `EllHyp_certificates.lean`);
* `EllipticEst.HkMem_add_open` / `HkMem_sub_open` (`EllHyp_certificates.lean`,
  `HkMem_sub_open.lean`);
* `ClassC.bdryTraces_add` / `bdryTraces_smul` (`ClassC/A1.lean`), which give `BdryTraces` for
  `f + g` and for `c • f`;  the difference is written `f - g = f + (-1) • g`.

Everything here is `sorry`-free.

*Consumption.*  A caller who needs `RegQo α 4 (J_ε w - w)` (the shape in which the `O(ε)`
mollification defect enters the `hneg` pairing bound `IP_perturb`, `EpsE4Thr/IP_perturb.lean`)
combines `regQo_sub` with the two membership lemmas of the two summands.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.EllipticEst.HkMem_sub_open
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.ClassC.A1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `BdryTraces` and `SmoothOpen` for the pieces of a difference -/

/-- `BdryTraces` is closed under pointwise difference: write `f - g = f + (-1) • g` and use the
additivity and the scalar-linearity (`ClassC.bdryTraces_add`, `ClassC.bdryTraces_smul`). -/
theorem bdryTraces_sub {α : ℝ} {k : ℕ} {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf' : Work.FTS.Nonlin.BdryTraces α k f) (hg' : Work.FTS.Nonlin.BdryTraces α k g) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => f z θ - g z θ) := by
  have hfg : (fun z θ => f z θ - g z θ) = f + (-1 : ℝ) • g := by
    funext z θ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfg]
  exact Work.FTS.ClassC.bdryTraces_add hf (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-1) hg)
    hf' (Work.FTS.ClassC.bdryTraces_smul hg' (-1))

/-- `BdryTraces` is closed under negation. -/
theorem bdryTraces_neg {α : ℝ} {k : ℕ} {f : Fn}
    (hf' : Work.FTS.Nonlin.BdryTraces α k f) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => -f z θ) := by
  have hfg : (fun z θ => -f z θ) = (-1 : ℝ) • f := by
    funext z θ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfg]
  exact Work.FTS.ClassC.bdryTraces_smul hf' (-1)

/-! ## The closure of `RegQo` -/

/-- **`RegQo` is closed under pointwise addition.** -/
theorem regQo_add {α : ℝ} {k : ℕ} {f g : Fn} (hf : RegQo α k f) (hg : RegQo α k g) :
    RegQo α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.EllipticEst.smoothOpen_add hf.1 hg.1,
    Work.FTS.EllipticEst.HkMem_add_open hf.1 hg.1 hf.2.1 hg.2.1,
    Work.FTS.ClassC.bdryTraces_add hf.1 hg.1 hf.2.2 hg.2.2⟩

/-- **`RegQo` is closed under pointwise difference.**  This is the operation under which the
mollification defect `J_ε w - w` and the projection correction are built. -/
theorem regQo_sub {α : ℝ} {k : ℕ} {f g : Fn} (hf : RegQo α k f) (hg : RegQo α k g) :
    RegQo α k (fun z θ => f z θ - g z θ) :=
  ⟨Work.FTS.EllipticEst.smoothOpen_sub hf.1 hg.1,
    Work.FTS.EllipticEst.HkMem_sub_open hf.1 hg.1 hf.2.1 hg.2.1,
    bdryTraces_sub hf.1 hg.1 hf.2.2 hg.2.2⟩

/-- **`RegQo` is closed under pointwise negation.** -/
theorem regQo_neg {α : ℝ} {k : ℕ} {f : Fn} (hf : RegQo α k f) :
    RegQo α k (fun z θ => -f z θ) := by
  have hz : (fun z θ => -f z θ) = fun z θ => (-1 : ℝ) * f z θ := by
    funext z θ; ring
  rw [hz]
  exact regQo_const_mul (c := (-1 : ℝ)) hf

/-- `RegQo α k` of the `n`-fold sum `f + g`-shape used by the explicit pieces of `epsWP`: the
three-term combination `f + g - h` (the form in which `HnegCore.epsRHSP_split` presents the
nonlinear part `w`). -/
theorem regQo_add_sub {α : ℝ} {k : ℕ} {f g h : Fn} (hf : RegQo α k f) (hg : RegQo α k g)
    (hh : RegQo α k h) : RegQo α k (fun z θ => f z θ + g z θ - h z θ) :=
  regQo_sub (regQo_add hf hg) hh

end Work.FTS.StrongEps.EpsE4Thr
