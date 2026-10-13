import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.RegQDefs
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Scratch type-check of the statements of `FTS/ELL_H2_LEAD.md` (Claude, 2026-10-04).
Definitions only (no theorems, no sorry); the node statements are in ELL_H2_STATEMENTS.lean.txt. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-! LEAD-FROZEN (curric-46, 2026-10-04): open-quadrant packages and transport clauses replacing the uninhabited EllPkgG/StarPkg of FTS/Vocab.lean. Design: Submission/Work/FTS/ELL_H2_LEAD.md. Do not edit. -/

namespace Work.FTS.VocabO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Part A -/

/-! ## Part B: the flat angular coefficient norm, and the transport replacements -/

/-- open-quadrant sups of `D_z^b D_θ^i ∂_θ f`, `b + i ≤ l` -/
def CoefTh (l : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∑ b ∈ Finset.range (l + 1), ∑ i ∈ Finset.range (l + 1),
    if b + i ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0

def CoefThMem (l : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ b i : ℕ, b + i ≤ l → ∃ K : ℝ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ K

/-- B3. the replacement `N4Extra` transport clauses (IP form). -/
def T2Clause (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → CoefThMem 1 f →
    Work.FTS.Nonlin.RegQ α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f + CoefTh 1 f) * Work.FTS.Nonlin.Xn α g ^ 2

def T3Clause (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f → CoefThMem 3 f →
    Work.FTS.Nonlin.RegQ α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2

/-! ## Part B: the open-quadrant packages (replacing the uninhabited frozen ones) -/

/-- coefficient class: interior `C^∞` (z > 0 only) + honesty, NO `BdryTraces`. -/
def HQo (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α k f

/-- the plain D-type `𝒲^{l,∞}` norm: open-quadrant sups of `D_z^b D_θ^j f`, `b + j ≤ l`
(no `(z+1)^k∂_z^k`, no angular weight; `WDp α l f ≤ C_l · WlInf α l f` on `SmoothOpen`). -/
def WDp (l : ℕ) (f : Fn) : ℝ :=
  ∑ b ∈ Finset.range (l + 1), ∑ j ∈ Finset.range (l + 1),
    if b + j ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0

def WDMem (l : ℕ) (f : Fn) : Prop :=
  ∀ b j : ℕ, b + j ≤ l → ∃ K : ℝ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed b j f z θ| ≤ K

structure EllPkgGo (α Ce : ℝ) (g Φg : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α g Φg
  smooth : Work.FTS.EllipticEst.SmoothOpen Φg
  R : HQo α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α g
  U : HQo α 4 (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
        / Work.Construction.s2 θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
        / Work.Construction.s2 θ) ≤ Ce * Work.FTS.Nonlin.Xn α g
  V : HQo α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α g
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.Construction.PhiTil α g Φg))
  Vth : CoefThMem 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g

structure StarPkgo (α Cs : ℝ) (Φs : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs
  smooth : Work.FTS.EllipticEst.SmoothOpen Φs
  R : WDMem 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ) ∧
      WDp 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
        ≤ Cs * α
  dU : WDMem 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) ∧
      WDp 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) ≤ Cs * α
  V : WDMem 4 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ∧
      WDp 4 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ≤ Cs * α
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
  Vth : CoefThMem 3 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ∧
      CoefTh 3 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ≤ Cs * α

/-! ## Part B: the `Φ_*` decomposition -/

/-- angular part of `F_*` with the `sin 2θ`-moment removed: `∫ Γ̄ sinθcos²θ = 0`. -/
def GamBar (α θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α - (5 / 4) * Real.sin (2 * θ)

/-- the radial profile `φ = 2z/(1+z)²` and `𝒜φ = αz²φ'' + (5+α)zφ'`. -/
def phiR (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2
def phiA (α z : ℝ) : ℝ :=
  α * z ^ 2 * iteratedDeriv 2 phiR z + (5 + α) * z * deriv phiR z

end Work.FTS.VocabO
