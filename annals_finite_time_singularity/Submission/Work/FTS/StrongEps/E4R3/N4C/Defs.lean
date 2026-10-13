/-
# `E4R3/N4C/Defs` — the **honest** (open-quadrant) interface of the level-four pairing

This module fixes the vocabulary of the *class-C* (open-quadrant) version of the N4 pairing
estimate, i.e. the estimate

  `|rhsPair (IP4 c…) α g (Φs + Φg)| ≤ CcN · Pbd α (Xn α g)`

for profiles `g` carrying only the *honest* data (`SmoothOpen`, `HkMem`, `DecayAll`, …) rather
than the frozen `GalClass`/`RegQ` bundle (`SmoothQuad`, i.e. `C^∞` on the strip `z > -1`).

The frozen N4 chapter (`Nonlinear.Open.n4Rows2`, `Open2.pairing_bound_open2`) is stated over
`GalClass α g`; the consumers of the E4R3 chapter (the projected mollified slices
`Pz (J_ε (slice g τ))`) carry only the open-quadrant class, so a *separate* row table in the
honest class is needed.  This file provides the *interface*: the clause bundle `N4ExtraH`
(the honest, coefficient-free form of the clause list of `OpenPkg.N4Extra'`, read off from the
clauses which are needed by the rows: `cs`, `add`, `smul`, `neg`, `congr`, `dz`, `t1`, `t2`,
`t3`, `t4`), the honest profile bundle `HAdm`, and the elementary projections which let the
class-`C` data of the route feed the bundle.

The *content* — the instantiation of `N4ExtraH (IP4 c…)` from the honest per-slot transport
estimates, the honest row table, and the assembly — lives in the sibling modules of
`Submission/Work/FTS/StrongEps/E4R3/N4C/`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.Nonlinear.Pieces.Rows

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo CoefTh CoefThMem WDp WDMem)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth)

set_option autoImplicit false

/-- The abbreviation of the concrete level-four coercive pairing of the a-priori chapter. -/
abbrev IP4 (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : ℝ → Fn → Fn → ℝ :=
  Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''

/-- **The honest `g`-side bundle of the level-four transport clauses**, in the form in which the
class-`C` data of the route supplies them: open-quadrant smoothness, `ℋ⁴`- and `ℋ⁵`-honesty
and the `L¹`-decay of the plain partials (`DecayAll 4`).

`ClassC α g` together with `CoerAdmO α g` gives `SmoothOpen g` and `HkMem α k g` for every
`k ≤ 10`; the `DecayAll 4 g` conjunct follows from `BdryTraces α 6 g` (a field of `ClassC`) by
`N4C.decayAll_of_bdryTraces`. -/
def HAdm (α : ℝ) (g : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ HkMem α 6 g ∧
    Work.Spaces.DecayAll 4 g

/-- **The honest clause bundle of the level-four pairing** — the coefficient-free form of the
clause list of `OpenPkg.N4Extra'` which the rows consume, with the *second* argument in the
honest class `HQo α 4` instead of the frozen `RegQ α 4` (whose `SmoothQuad` conjunct is not
available along the route).

The clause list is exactly the one used by the row proofs of `Nonlinear.Open`:
`cs`, `add`, `smul`, `neg`, `congr` (algebraic), `dz` (the lossless `D_z`-self-pairing),
`t1` (`D_θ`-transport with an `ℋ⁴`-coefficient), `t2`/`t3` (`D_z`-transport with a flat
resp. `𝒲^{4,∞}`-coefficient) and `t4` (`D_θ`-transport with a `𝒲^{4,∞}`-coefficient). -/
structure N4ExtraH (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  /-- positivity of the two constants. -/
  pos : 0 < Ct ∧ 0 < α₂
  /-- Cauchy–Schwarz against the `ℋ⁴`-norm, on the honest class. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    |IP α f g| ≤ Ct * Xn α f * Xn α g
  /-- additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, HQo α 4 f₁ → HQo α 4 f₂ → HQo α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ), ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- negation in the first argument. -/
  neg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    IP α (fun z θ => -f z θ) g = -IP α f g
  /-- `IP` only depends on the first argument through its values on the open quadrant. -/
  congr : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g : Fn, HQo α 4 f → HQo α 4 f' → HQo α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  /-- the lossless `D_z`-self-pairing (design §5 T5), on the open coercivity class. -/
  dz : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 g →
    |IP α (Dz g) g| ≤ Ct * Xn α g ^ 2
  /-- `T1Q`: transport with `D_θ` and an `ℋ⁴`-coefficient (tex 1119). -/
  t1 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → Work.FTS.EllipticEst.SmoothOpen g →
    HkMem α 4 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dth g z θ) g| ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T2S`: transport with `D_z` and a flat angular coefficient. -/
  t2 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → HkMem α 4 f →
    CoefThMem 1 f → Work.FTS.EllipticEst.SmoothOpen g → HkMem α 4 g → HkMem α 5 g →
    Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Xn α f + CoefTh 1 f) * Xn α g ^ 2
  /-- `T3S`: transport with `D_z` and a `𝒲^{4,∞}`-coefficient. -/
  t3 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.WlInfMem α 4 f → CoefThMem 3 f → Work.FTS.EllipticEst.SmoothOpen g →
    HkMem α 4 g → HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + CoefTh 3 f) * Xn α g ^ 2
  /-- `T3Q` with `D_θ` and a `𝒲^{4,∞}`-coefficient, in the `D`-sup norm. -/
  t4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → WDMem 4 f →
    Work.FTS.EllipticEst.SmoothOpen g →
    HkMem α 4 g → HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * WDp 4 f * Xn α g ^ 2

/-! ## Elementary projections

The two classes of the route: `ClassC α g` (the honest class of the elliptic chapter) and
`CoerAdmO α g` (the open coercivity class). -/

/-- `ClassC` refines the honest `ℋ⁴`-class `HQo α 4`. -/
theorem classC_hqo4 {α : ℝ} {g : Fn} (h : Work.FTS.ClassC.ClassC α g) : HQo α 4 g :=
  ⟨h.reg, Work.FTS.OpenPkg.HkMem_mono_open h.reg 4 (by norm_num) h.mem⟩

/-- `ClassC` refines the honest `ℋ⁵`-class `HQo α 5`. -/
theorem classC_hqo5 {α : ℝ} {g : Fn} (h : Work.FTS.ClassC.ClassC α g) : HQo α 5 g :=
  ⟨h.reg, Work.FTS.OpenPkg.HkMem_mono_open h.reg 5 (by norm_num) h.mem⟩

/-- `ClassC ∧ CoerAdmO` gives the open coercivity class `RegQo α 4`. -/
theorem classC_regQo4 {α : ℝ} {g : Fn} (h : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 4 g := h.regQoFour

/-- `HkMem` of the mixed slots at the level needed by the product rules. -/
theorem classC_hkMem6 {α : ℝ} {g : Fn} (h : Work.FTS.ClassC.ClassC α g) : HkMem α 6 g :=
  Work.FTS.OpenPkg.HkMem_mono_open h.reg 6 (by norm_num) h.mem

/-- **The context of one honest §8 row**: the hypotheses of the target, namely the class-`C`
profile data (`ClassC α g` and the open coercivity class `CoerAdmO α g`), the two open-quadrant
elliptic packages of `Φs` and `Φg`, and the ranges of `α`.

This is the honest (class-`C`) replacement of the frozen row context `NonlinRows.Ctx` /
`Open2.CtxO` (which carry `GalClass α g`, i.e. `SmoothQuad`, not available along the route). -/
def CtxT (Cs Ce α₂ α : ℝ) (g Φs Φg : Fn) : Prop :=
  0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ Work.FTS.ClassC.ClassC α g ∧
    Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g ∧
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs ∧ Work.FTS.VocabO.EllPkgGo α Ce g Φg

theorem CtxT.hα {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) : 0 < α := h.1

theorem CtxT.hα1 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) : α ≤ 1 :=
  h.2.1

theorem CtxT.hαα₂ {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) : α ≤ α₂ :=
  h.2.2.1

theorem CtxT.hg {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.ClassC.ClassC α g := h.2.2.2.1

theorem CtxT.hco {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g := h.2.2.2.2.1

theorem CtxT.hs {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs := h.2.2.2.2.2.1

theorem CtxT.hell {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO.EllPkgGo α Ce g Φg := h.2.2.2.2.2.2

/-- The honest profile bundle `HAdm α g` from the row context, given the decay (which
`ClassC` supplies via `N4C.decayAll_of_classC`). -/
theorem CtxT.hAdm {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    (hdec : Work.Spaces.DecayAll 4 g) : HAdm α g :=
  ⟨h.hg.reg, Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg 4 (by norm_num) h.hg.mem,
    Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg 5 (by norm_num) h.hg.mem,
    Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg 6 (by norm_num) h.hg.mem, hdec⟩

/-- The honest `ℋ⁴`-class of the profile, from the row context. -/
theorem CtxT.hqo4 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    HQo α 4 g := classC_hqo4 h.hg

/-- The honesty of the profile's `D_z`-slot, from the row context. -/
theorem CtxT.hqoDz {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    HQo α 4 (Dz g) :=
  ⟨h.hg.reg.Dz,
    Work.FTS.IPGen.HkMem_Dz_le h.hg.reg
      (Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg 5 (by norm_num) h.hg.mem)⟩

/-! ## The honest row table

The honest (class-`C`) version of the §8 row bundle: the three row groups
(`Nonlinear.Pieces.N0Rows`, `VocabO2.NRows2`, `Nonlinear.Pieces.AuxRows`) and the `ℋ⁴`-honesty
table `OpenPkg.PiecesHk`, all in the context `CtxT` (class-`C` data and the open-quadrant
packages).  The single constant of each group is uniform in `α, g, Φs, Φg`. -/
structure RowsT (IP : ℝ → Fn → Fn → ℝ) (α₂ Ce Cs : ℝ) where
  /-- the constant of rows 1--7. -/
  K₁ : ℝ
  /-- the constant of rows 8--26. -/
  K₂ : ℝ
  /-- the constant of the auxiliary rows. -/
  K₃ : ℝ
  hK₁ : 0 < K₁
  hK₂ : 0 < K₂
  hK₃ : 0 < K₃
  /-- rows 1--7 (the `N₀`-block). -/
  rowsN0 : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.Nonlinear.Pieces.N0Rows IP α K₁ g Φs Φg
  /-- rows 8--26 (the `N`-block). -/
  rowsN : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.VocabO2.NRows2 IP α K₂ g Φs Φg
  /-- the auxiliary rows `rak`, `rl0`--`rl2`. -/
  rowsAux : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.Nonlinear.Pieces.AuxRows IP α K₃ g Φs Φg
  /-- the `ℋ⁴`-honesty of every piece and of the three blocks. -/
  hk : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.OpenPkg.PiecesHk α g Φs Φg
  /-- the two exact splits of `N₀` and `N`, and the collapse of `N_*`. -/
  splits : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.NonlinRows.SplitsData α g Φs Φg

/-- **The clause bundle is monotone in the range `α₂`**: a bundle on `(0, α₂]` restricts to
`(0, α₂']` for `α₂' ≤ α₂`. -/
theorem N4ExtraH.mono {IP : ℝ → Fn → Fn → ℝ} {α₂ α₂' Ct : ℝ} (hα₂' : α₂' ≤ α₂)
    (hα₂'pos : 0 < α₂') (h : N4ExtraH IP α₂ Ct) : N4ExtraH IP α₂' Ct :=
  ⟨⟨h.pos.1, hα₂'pos⟩,
   fun α hα f g hf hg => h.cs α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g hf hg,
   fun α hα f₁ f₂ g h₁ h₂ h₃ => h.add α ⟨hα.1, le_trans hα.2 hα₂'⟩ f₁ f₂ g h₁ h₂ h₃,
   fun α hα c f g h₁ h₂ => h.smul α ⟨hα.1, le_trans hα.2 hα₂'⟩ c f g h₁ h₂,
   fun α hα f g h₁ h₂ => h.neg α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂,
   fun α hα f f' g h₁ h₂ h₃ hh => h.congr α ⟨hα.1, le_trans hα.2 hα₂'⟩ f f' g h₁ h₂ h₃ hh,
   fun α hα f hf => h.dz α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f g h₁ h₂ h₃ h₄ => h.t1 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄,
   fun α hα f g h₁ h₂ h₃ h₄ h₅ h₆ h₇ =>
     h.t2 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄ h₅ h₆ h₇,
   fun α hα f g h₁ h₂ h₃ h₄ h₅ h₆ h₇ =>
     h.t3 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄ h₅ h₆ h₇,
   fun α hα f g h₁ h₂ h₃ h₄ h₅ h₆ =>
     h.t4 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄ h₅ h₆⟩

end Work.FTS.StrongEps.E4R3.N4C
