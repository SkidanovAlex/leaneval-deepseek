/-
# `Work.FTS.EllSol` — the linear elliptic solution operator `EllSol` of the Galerkin design

This area (`Submission/Work/FTS/EllSol/`) implements §1 items **(a), (c), (d), (e)** of
`Submission/Work/FTS/FTS_ELL_GALERKIN.md`:

> `exists_ellSol : ∃ Ce > 0, ∃ α₀ > 0, ∀ α ∈ (0, α₀], ∃ EllSol : Fn →ₗ[ℝ] Fn,
>     ∀ g, GalClass α g → EllPkgGo α Ce g (EllSol g)`

The route (no uniqueness needed) is

* **(a)** `galClass_lin` — `GalClass α` is a subspace (`GalClassLin.lean`);
* **(b)** `ellClassO_exists` — existence of a solution in the class `EllClassO`
  (this is the **single hypothesis** taken here, to be delivered by `FTS/EllExist`);
* **(c)** `ellClassO_lin` — `EllClassO` is closed under linear combinations (`EllClassOLin.lean`);
* **(d)** `ellPkgGo_of_class` — the estimates hold for *every* solution of the class
  (`Transfer/` and `EllPkgGo.lean`);
* **(e)** the Hamel-basis assembly (`Hamel.lean`, `Exists.lean`).

## What this file fixes

* `EllClassO α g Ψ` — the solution class, copied **verbatim** from the design's statement file
  (`Submission/Work/FTS/FTS_ELL_GALERKIN_STMTS.lean.txt`, namespace `Work.FTS.ScratchC46`) into
  the namespace `Work.FTS.EllSol`;
* `EllClassOExists` — the same with the existence quantifier of `ellClassO_exists`;
* `EllPkgGoOfClass` — item (d) as a `Prop`;
* `ExistsEllSol` — the target `exists_ellSol` as a `Prop`.

Everything downstream (`GalerkinFix`, `Open2`, the a-priori fields) consumes the *conclusions*
`exists_ellSol`, so the `Prop`-form `ExistsEllSol` is what the assembly produces.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn Fam slice galFun)

set_option autoImplicit false

/-- **The shifted unknown** `Ψ ↦ Ψ + Gsing α g · sin 2θ` of §'The singular term': the function
to which the paper's elliptic estimates (`TT.EllWeakPos`/`TT.EllEstUnif`) are applied.  It is the
third component of `EllClassO`, and the difference `ellShift α g Ψ - Ψ = Gsing α g · sin 2θ`
carries the singular part of the stream function. -/
def ellShift (α : ℝ) (g Ψ : Fn) : Fn :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)

@[simp] theorem ellShift_apply (α : ℝ) (g Ψ : Fn) (z θ : ℝ) :
    ellShift α g Ψ z θ = Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- **The solution class of the Hamel construction** (item (b) of the design, verbatim).

`Ψ` solves the elliptic problem `bslOp α Ψ = g` on the open quadrant (`IsBslSol`), is `C^∞` on
the open quadrant (`SmoothOpen`), and the *straightened* unknown `Ψ + Gsing α g · sin 2θ` is an
honest weak solution of the elliptic problem with source `orthSource g` (`TT.EllWeakPos`, the
class in which the paper's Proposition `prop:Hk` is stated — see
`Submission/Work/FTS/EllipticEst/TT/WeakDefs.lean`). -/
def EllClassO (α : ℝ) (g Ψ : Fn) : Prop :=
  Work.Elliptic.IsBslSol α g Ψ ∧ Work.FTS.EllipticEst.SmoothOpen Ψ ∧
  Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) (ellShift α g Ψ)

/-- The difference `ellShift α g Ψ - Ψ` is the rank-one singular term `Gsing α g · sin 2θ`. -/
theorem ellShift_sub (α : ℝ) (g Ψ : Fn) :
    ellShift α g Ψ - Ψ = fun z θ => Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := by
  funext z θ
  simp

/-- The third component of `EllClassO`, stated with the named shift `ellShift`. -/
theorem EllClassO.weakPos' {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) (ellShift α g Ψ) :=
  h.2.2

/-- **Item (b)** `ellClassO_exists`: every profile of the Galerkin class has a solution in
`EllClassO`.  This is the one hypothesis of the present area; it is delivered by `FTS/EllExist`
(honest truncated modal limit) and is *not* proved here. -/
def EllClassOExists : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α, 0 < α → α ≤ α₀ → ∀ g, Work.FTS.Nonlin.GalClass α g →
    ∃ Ψ, EllClassO α g Ψ

/-- **Item (d)** `ellPkgGo_of_class`: the estimates of `EllPkgGo` hold for *every* solution in
the class `EllClassO` (no uniqueness of the elliptic solution is used). -/
def EllPkgGoOfClass : Prop :=
  ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧ ∀ α, 0 < α → α ≤ α₀ → ∀ g Ψ,
    Work.FTS.Nonlin.GalClass α g → EllClassO α g Ψ → Work.FTS.VocabO.EllPkgGo α Ce g Ψ

/-- **The target** `exists_ellSol`, verbatim, as a `Prop`: a *linear* solution operator on the
whole space `Fn` whose values on `GalClass α` are elliptic solutions with the package
`EllPkgGo`. -/
def ExistsEllSol : Prop :=
  ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ EllSol : Fn →ₗ[ℝ] Fn, ∀ g, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g)

/-- The design's `ellPkgGo_of_class` as a `Prop` (same content as `EllPkgGoOfClass`; the
statement file writes the same `∃ Ce α₀, 0 < Ce ∧ 0 < α₀ ∧ …`). -/
def EllClassOExistsAt (α₀ : ℝ) : Prop :=
  0 < α₀ ∧ ∀ α, 0 < α → α ≤ α₀ → ∀ g, Work.FTS.Nonlin.GalClass α g → ∃ Ψ, EllClassO α g Ψ

/-! ## Elementary API of the class -/

theorem EllClassO.sol {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.Elliptic.IsBslSol α g Ψ := h.1

theorem EllClassO.smooth {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ := h.2.1

theorem EllClassO.weak {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) := h.2.2

theorem EllClassO.ellShift_eq {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) :
    ellShift α g Ψ = fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- The weak class is inhabited at `(F, Ψ) = (0, 0)`. -/
theorem ellWeakPos_zero (α : ℝ) (k : ℕ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k (0 : Fn) (0 : Fn) := by
  have hz2 : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : Fn) z θ) = 0 := by
    funext z θ; rw [Work.FTS.EllipticEst.pzIter_zero_fun]; simp
  have hd2 : Work.Spaces.pthIter 2 (0 : Fn) = 0 :=
    Work.FTS.EllipticEst.pthIter_zero_fun 2
  have hzp : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 (0 : Fn)) z θ) = 0 := by
    funext z θ; rw [hd2, Work.FTS.EllipticEst.pz_zero_fun]; simp
  refine ⟨?_, fun z => rfl, fun z => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ h0 h1
    have h := (Work.FTS.EllipticEst.IsBslSol_zero α).1 z hz θ h0 h1
    simpa using h
  · intro z hz; simp [Work.Elliptic.Fstar]
  · intro z hz; simp [Work.Elliptic.Fstar]
  · intro n
    change ContDiffOn ℝ n (fun _ : ℝ × ℝ => (0 : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
    exact contDiffOn_const
  · exact Work.FTS.EllipticEst.HkMem_zero α k
  · rw [hz2]; exact Work.FTS.EllipticEst.HkMem_zero α k
  · rw [hd2]; exact Work.FTS.EllipticEst.HkMem_zero α k
  · rw [hzp]; exact Work.FTS.EllipticEst.HkMem_zero α k

/-- `Gsing α 0 = 0`. -/
theorem Gsing_zero (α : ℝ) : Work.Elliptic.Gsing α (0 : Fn) = 0 := by
  funext z
  simp [Work.Elliptic.Gsing, Work.Elliptic.Gstar, Work.Elliptic.Gbar,
    Work.Elliptic.Fstar, Work.Elliptic.L12, Work.Elliptic.L12dens]

/-- `orthSource 0 = 0`. -/
theorem orthSource_zero : Work.Elliptic.orthSource (0 : Fn) = 0 := by
  funext z θ
  simp [Work.Elliptic.orthSource, Work.Elliptic.Fstar]

/-- The class is inhabited at `(g, Ψ) = (0, 0)`. -/
theorem ellClassO_zero {α : ℝ} (hα : 0 < α) : EllClassO α 0 0 := by
  have hsin : ellShift α (0 : Fn) (0 : Fn) = 0 := by
    funext z θ
    rw [ellShift_apply, Gsing_zero]
    simp
  refine ⟨Work.FTS.EllipticEst.IsBslSol_zero α, ?_, ?_⟩
  · change ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => (0 : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
    exact contDiffOn_const
  · simpa only [orthSource_zero, hsin] using ellWeakPos_zero α 4

end Work.FTS.EllSol
