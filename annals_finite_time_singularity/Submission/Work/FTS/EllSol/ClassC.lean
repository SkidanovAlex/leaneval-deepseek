import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.StrongGlobal.Main
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open

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


end Work.FTS.EllSol
