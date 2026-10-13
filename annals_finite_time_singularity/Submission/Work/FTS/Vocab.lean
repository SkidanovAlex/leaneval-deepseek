/- FTS/Vocab.lean — LEAD-OWNED, FROZEN 2026-10-03 (curric-46). Shared vocabulary for N4/N5 and the interface fixes: RegQ REPLACES SmoothNbhd (which is real-analyticity); UnifIP is N2s corrected obligation. Design: FTS/N45_DESIGN_LEAD.md §3.1. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.CoercivityStep.Assembly
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Construction.Apriori
import Submission.Work.Construction.Terms
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false

/-- the size `|g|_{ℋ⁴}` -/
abbrev Xn (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 4 g

/-- vanishing of the integration-by-parts boundary terms (slot by slot, up to order `k`) -/
def BdryTraces (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  ∀ a b : ℕ, a + b ≤ k →
    (∀ θ ∈ Set.Ioo 0 (π / 2),
      Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) atTop (𝓝 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (𝓝[<] (π / 2)) (𝓝 0))

/-- the interior-regular class replacing `SmoothNbhd` (= analyticity on a neighbourhood!) -/
def RegQ (α : ℝ) (k : ℕ) (f : Fn) : Prop :=
  Work.FTS.LocData.SmoothQuad f ∧ Work.Spaces.HkMem α k f ∧ BdryTraces α k f

/-- the class of Galerkin profiles (and of the perturbation along the a-priori argument) -/
structure GalClass (α : ℝ) (g : Fn) : Prop where
  reg : RegQ α 6 g
  vanish : Work.Spaces.VanishTheta g
  axis : ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 ∧ Work.Spaces.pz g 0 θ = 0
  decay : Work.Spaces.DecayAll 6 g
  l12 : Work.Construction.L12 g 0 = 0

/-- the coercivity class (what N2 must deliver coercivity on): only the zero mode `L₁₂(f)(0)=0`. -/
structure CoerAdm (α : ℝ) (f : Fn) : Prop where
  reg : RegQ α 5 f
  vanish : Work.Spaces.VanishTheta f
  axis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0
  l12 : Work.Construction.L12 f 0 = 0

/-- **N2 obligation**: a coercive `ℋ⁴` inner product with constants uniform in `α ∈ (0,α₂]`. -/
structure UnifIP (IP : ℝ → Fn → Fn → ℝ) (α₂ cc clo Cup Ccs : ℝ) : Prop where
  pos : 0 < α₂ ∧ 0 < cc ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Ccs
  symm : ∀ α f g, IP α f g = IP α g f
  add_fst : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g, RegQ α 4 f₁ → RegQ α 4 f₂ → RegQ α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  smul_fst : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) f g, RegQ α 4 f → RegQ α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  congr_qd : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g, RegQ α 4 f → RegQ α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  nonneg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, RegQ α 4 f → 0 ≤ IP α f f
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g, RegQ α 4 f → RegQ α 4 g →
    |IP α f g| ≤ Ccs * Xn α f * Xn α g
  lo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdm α f → clo * Work.Spaces.HkSq α 4 f ≤ IP α f f
  up : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdm α f → IP α f f ≤ Cup * Work.Spaces.HkSq α 4 f
  coer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdm α f →
    cc * Work.Spaces.HkSq α 4 f ≤ IP α (Work.Coercivity.LGammaT α f) f
  Dz_self : ∀ α ∈ Set.Ioc 0 α₂, ∀ f, CoerAdm α f →
    |IP α (Work.Spaces.Dz f) f| ≤ Ccs * Xn α f ^ 2

/-- elliptic outputs for the perturbation's stream function (N1 obligation, canonical solution) -/
structure EllPkgG (α Ce : ℝ) (g Φg : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α g Φg
  smooth : Work.FTS.LocData.SmoothQuad Φg
  R : RegQ α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ≤ Ce * Xn α g
  U : RegQ α 4 (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
        / Work.Construction.s2 θ) ∧
      Xn α (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
        / Work.Construction.s2 θ) ≤ Ce * Xn α g
  V : RegQ α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Xn α (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ≤ Ce * Xn α g
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.Construction.PhiTil α g Φg))

/-- the stream function of `F_*` and its `𝒲^{l,∞}` package (N3 `PhiStarRegularity` + Cor.) -/
structure StarPkg (α Cs : ℝ) (Φs : Fn) : Prop where
  sol : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs
  smooth : Work.FTS.LocData.SmoothQuad Φs
  R : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
        ≤ Cs * α
  dU : Work.Spaces.WlInfMem α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) ∧
      Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) ≤ Cs * α
  V : Work.Spaces.WlInfMem α 4 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ∧
      Work.Spaces.WlInf α 4 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ≤ Cs * α
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))

/-- the polynomial of the a-priori estimate -/
def Pbd (α X : ℝ) : ℝ :=
  α ^ 2 * X + Real.sqrt α * X ^ 2 + α ^ (-(3 / 2 : ℝ)) * X ^ 3 + α ^ (-(5 / 2 : ℝ)) * X ^ 4


def PsiCan (Φs : Fn) (EllSol : Fn → Fn) : Fam → Fam :=
  fun G z θ τ => Φs z θ + EllSol (slice G τ) z θ

/-- the Galerkin basis class (N6 step 2, corrected) -/
structure GalBasis (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop where
  orth : ∀ i j : ℕ, IP α (φ i) (φ j) = if i = j then 1 else 0
  cls : ∀ n (c : Fin n → ℝ), GalClass α (galFun φ c)


end Work.FTS.Nonlin
