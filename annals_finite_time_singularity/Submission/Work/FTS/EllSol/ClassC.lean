/-
# `Work.FTS.EllSol.ClassC` — the re-targeted interface of the design §A (lead, 01:30)

The lead replaced the Galerkin class (whose linearity is false: `Refute/`) by the class `ClassC`
of `Submission/Work/FTS/FTS_HARD_STMTS.lean.txt`, and split the work: `FTS/ClassC` owns A1
(`classC_add`/`classC_smul`), A2, A3 and A6 (the Hamel step); **this area owns A4** (the packages
`EllPkgGo` and `EllPkgK` at `k = 4, 6`, via `propHkWeakFts k`) **and A5** (the `V`-transfer
without `∂²_θV`, replacing the false `pth2V_hk`).

This module copies the class and the package **verbatim** from the statements file into the
namespace `Work.FTS.EllSol`, so that A4/A5 can be stated against them here; `FTS/ClassC` keeps
its own copy and imports the proved lemmas of this area.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.StrongGlobal.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- canonical angular normalisation: kills the junk at θ ∉ (0,π/2) (verbatim from the
statements file). -/
def normTh (g : Fn) : Fn := fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then g z θ else 0

def normThL : Fn →ₗ[ℝ] Fn where
  toFun := normTh
  map_add' f g := by
    funext z θ; by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]
  map_smul' c f := by
    funext z θ; by_cases h : θ ∈ Set.Ioo 0 (π / 2) <;> simp [normTh, h]

/-- the source class C: open-quadrant, finite-order, linear-closed (verbatim).  Note the field
`fsm` (all-order smoothness of the angular moment) — the ingredient the old class was missing. -/
structure ClassC (α : ℝ) (g : Fn) : Prop where
  norm  : normTh g = g
  reg   : Work.FTS.EllipticEst.SmoothOpen g
  mem   : Work.Spaces.HkMem α 7 g
  tr    : Work.FTS.Nonlin.BdryTraces α 6 g
  fsm   : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0)
  axis  : ∀ θ ∈ Set.Ioo 0 (π / 2), Tendsto (fun z => g z θ / z) (𝓝[>] 0) (𝓝 0)
  l12   : Work.Construction.L12 g 0 = 0

/-- the elliptic package at order `k` (verbatim). -/
structure EllPkgK (α : ℝ) (k : ℕ) (Ce : ℝ) (g Φg : Fn) : Prop where
  sol : Work.FTS.StrongGlobal.IsBslSolPos α g Φg
  smooth : Work.FTS.EllipticEst.SmoothOpen Φg
  R : Work.FTS.VocabO.HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.Spaces.HkNorm α k g
  U : Work.FTS.VocabO.HQo α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ)
        ≤ Ce * Work.Spaces.HkNorm α k g
  V : Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.Spaces.HkNorm α k g

/-- **(A)** the linear solution operator on the class C, packages at orders 4 and 6 (verbatim). -/
def ExistsEllSolC : Prop :=
  ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ E : Fn →ₗ[ℝ] Fn, ∀ g, ClassC α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧ EllPkgK α 6 Ce g (E g)

end Work.FTS.EllSol
