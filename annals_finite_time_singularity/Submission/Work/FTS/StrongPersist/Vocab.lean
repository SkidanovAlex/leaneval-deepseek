/-
# `Work.FTS.StrongPersist` — the strong-solution route, nodes S2 and S6 of the design

Design: `Submission/Work/FTS/FTS_STRONG_ROUTE.md` §3 (table S1–S6) and §1 (`RegPkgMin`).

The IP₄-Galerkin limit of the Open2/Open3 chain cannot be shown to have the regularity the
downstream nodes need (design §3, obstructions 1–3).  The replacement route is the
*strong-solution* route: local existence in `ℋ⁶` (S1), persistence of `ℋ⁶` from the a-priori
`ℋ⁴` bound (S2), an interior Sobolev embedding (S3), the a-priori bootstrap (S4), continuation
(S5) and the `ℋ³` bound on `∂_τ g` (S6).

**This chapter owns S2 and S6.**  It fixes:

* the level-six norm `Xn6`, the level-six inner product `IP6` (the paper's recursion
  `IP^{k+1} = HkIPStep c₁ c₂ IP^k` applied twice on top of the `ℋ⁴` inner product
  `CoercivityFix.Assembly.IP4` of the coercivity chapter) and the linear part `linPart` of the
  fake-time equation;
* the strong-solution predicate `IsStrongSolOn` on a half-open fake-time interval `[0,T)`,
  with the corrected elliptic law `Open3.IsBslSolPos` of design §1/§4 (the boundary conditions
  only for `z ≥ 0`);
* the regularity packages `RegPkgMin` (copied **verbatim** from design §1) and `RegPkgH6`;
* the **k = 6 restatements of the interface clauses** consumed by the S2 Gronwall argument:
  the `ℋ⁶` product/`L₁₂` clauses (`N6Norm`), the transport clauses T1/T2/T3 of `VocabO` at
  level six (`N6Trans`), the level-six coercivity/comparability package of the paper's inner
  product (`H6Coer`), the level-six pairing bound for the nonlinear right-hand side
  (`H6Pair`) and the level-six energy identity (`H6EnergyDeriv`);
* the level-three operator package `L3Data` of S6.

The clause packages are *interfaces*: they are the level-six analogues of the level-four
clauses `OpenPkg.N4Norm'`, `VocabO.T2Clause`, `VocabO.T3Clause` and
`CoercivityStep.IsHkIP`.  The theorems of `Persist` and `Dbd` are proved *from* them; nothing
in this file is a proof obligation by itself.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.CoercivityFix.Assembly.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice gdot dynLin dynRHS IsDynEqOn IsDynGSolWith IsDynEq
  galFun galFam Slab)
open Work.FTS.Nonlin (Xn RegQ)
open Work.FTS.VocabO (HQo CoefTh CoefThMem WDp WDMem)
open Work.FTS.VocabO2 (StarPkgo2)
open Work.Coercivity (LGammaT HkIPStep H1IP wip)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth mixed pth pzIter DthIter DzIter)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The elliptic law of the strong route

`IsBslSolPos` is the *positivised* elliptic (Biot–Savart) law of the strong-solution route: the
paper's (PolarBSL) problem on the open quadrant, with the Dirichlet data `Ψ z 0 = Ψ z (π/2) = 0`
asserted only for `z ≥ 0` (the frozen `Work.Elliptic.IsBslSol` asks it for every real `z`, which no
solution of the local problem with data on `Iz` satisfies — `FTS_INTEGRATION_AUDIT.md` §3), plus the
decay at infinity.  It is the `Law` argument of `IsDynGSolWith` in this route.

The definition is *character-for-character* the one of the sibling area `FTS/StrongLWP`
(`Work.FTS.StrongLWP.IsBslSolPos`, `StrongLWP/Defs.lean`) and logically the one of
`Work.FTS.Open3.IsBslSolPos`; `StrongPersist/Basic.lean` records the (definitional) bridge to the
former.  It is repeated here — and not imported — so that this chapter's core does not depend on
the `Open3`/`Open2`/`OpenPkg` chain. -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0 ∧ Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

/-! ## The level-six norm and inner product -/

/-- The `ℋ⁶`-norm of a profile: `Xn6 α f = |f|_{ℋ⁶}`.  (`Xn α f` of `FTS/Vocab.lean` is
`|f|_{ℋ⁴}`.) -/
abbrev Xn6 (α : ℝ) (f : Fn) : ℝ := Work.Spaces.HkNorm α 6 f

/-- Membership in `ℋ⁶`. -/
abbrev H6Mem (α : ℝ) (f : Fn) : Prop := Work.Spaces.HkMem α 6 f

/-- **The level-six coercivity class.**  The paper's coercivity of `𝓛_Γ^T` on `ℋ^k` is *not* a
statement about the whole space: the nonlocal term `L₁₂` and the behaviour at the axis and at the
angular ends matter.  The class below is the level-six instance of the class the coercivity
chapter's corrected induction lives on (`Vocab.CoerAdm` with `RegQ α 5` replaced by the honest
`HQo α 6`): the slice is in the honest `ℋ⁶`-class, vanishes on the two angular boundary lines, its
axis values and first radial derivative vanish at `z = 0`, and the zero mode `L₁₂(f)(0)` is zero
(the projector condition of the paper). -/
structure H6Adm (α : ℝ) (f : Fn) : Prop where
  /-- the honest `ℋ⁶`-class. -/
  reg : HQo α 6 f
  /-- vanishing on the angular boundary lines. -/
  vanish : Work.Spaces.VanishTheta f
  /-- vanishing of the values and the first radial derivative at the axis. -/
  axis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0
  /-- the projector condition: the zero mode of `L₁₂` vanishes. -/
  l12 : Work.Construction.L12 f 0 = 0

/-- `HkSq α 6 f`, the square of the `ℋ⁶` norm (a name of its own for readability). -/
abbrev Sq6 (α : ℝ) (f : Fn) : ℝ := Work.Spaces.HkSq α 6 f

/-- The linear part `-𝓛_Γ^T f` of the fake-time equation as a function of the profile: by
`rfl`, `dynLin α g τ = linPart α (slice g τ)`.  (This is a definition, not an abbreviation, so
that `dynLin α g τ = linPart α (slice g τ)` holds by `rfl`.) -/
def linPart (α : ℝ) (f : Fn) : Fn := fun z θ => -(LGammaT α f z θ)

/-- **The `ℋ⁶` inner product.**  `IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α` is the paper's
recursion (tex 686)

`IP^{k+1} = HkIPStep c₁ c₂ IP^k = IP^k + c₁ IP^k(D_θ·, D_θ·) + c₂ IP^k(D_z·, D_z·)`

applied twice on top of the `ℋ⁴` inner product `CoercivityFix.Assembly.IP4` of the coercivity
chapter: `IP6 = HkIPStep e₁ e₂ (HkIPStep f₁ f₂ IP4)`.

All ten coefficients are free: the coercivity of the level-six operator is a property of the
*coefficients*, and the design's small-step choice lives in the lower levels
(`CoercivityFix/Assembly/Defs.lean`).  The package `H6Coer` below asserts the properties of
`IP6` for the coefficients that the coercivity chapter's induction produces. -/
def IP6 (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  HkIPStep e₁ e₂
    (HkIPStep f₁ f₂
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α))

/-- `IP6` unfolded: the outermost step applied to the level-five inner product. -/
theorem IP6_eq (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (u v : Fn) :
    IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α u v
      = HkIPStep f₁ f₂ (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) u v
        + e₁ * HkIPStep f₁ f₂ (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α)
            (Dth u) (Dth v)
        + e₂ * HkIPStep f₁ f₂ (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α)
            (Dz u) (Dz v) := rfl

theorem dynLin_eq_linPart (α : ℝ) (g : Fam) (τ : ℝ) :
    dynLin α g τ = linPart α (slice g τ) := rfl

/-! ## The strong-solution predicate on `[0,T)` -/

/-- **The dynamic modulated equation on the half-open interval `[0,T)`.**  This is
`Galerkin.IsDynEqOn` cut down to `τ < T`; the derivative is taken *within* `[0,T)`, the honest
formulation for a solution whose maximal interval of existence is `[0,T)`. -/
def IsDynEqOnUpTo (α : ℝ) (Φ g : Fam) (T : ℝ) : Prop :=
  ∀ z θ τ, 0 ≤ τ → τ < T → (z, θ) ∈ Work.Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s)
      (dynLin α g τ z θ + dynRHS α Φ g τ z θ) (Set.Ico 0 T) τ

/-- **A strong solution of the dynamic modulated problem on `[0,T)`**, with the corrected
elliptic law `IsBslSolPos` of design §1/§4. -/
def IsStrongSolOn (α : ℝ) (Φ g : Fam) (T : ℝ) : Prop :=
  (∀ τ, 0 ≤ τ → τ < T → IsBslSolPos α (Work.Construction.Ftau α g τ) (slice Φ τ)) ∧
    IsDynEqOnUpTo α Φ g T

/-- A solution of the half-line form is a strong solution on every `[0,T)` with `T > 0`.
This is how the `Open3`-style consumption of this chapter is wired: the existence theorems
produce `IsDynGSolWith` on the half-line, persistence works on `[0,T)`. -/
theorem isStrongSolOn_of_isDynGSolWith {α T : ℝ} {Φ g : Fam}
    (h : IsDynGSolWith (IsBslSolPos α) α Φ g) (hT : 0 < T) : IsStrongSolOn α Φ g T :=
  ⟨fun τ hτ _ => h.1 τ hτ,
    fun z θ τ hτ _ hz => (h.2 z θ τ hτ hz).mono (Set.Ico_subset_Ici_self)⟩

/-- A strong solution on `[0,T)` is a strong solution on every `[0,T')` with `T' ≤ T`. -/
theorem IsStrongSolOn.mono {α T T' : ℝ} {Φ g : Fam} (h : IsStrongSolOn α Φ g T)
    (hT : T' ≤ T) : IsStrongSolOn α Φ g T' :=
  ⟨fun τ hτ hτT => h.1 τ hτ (lt_of_lt_of_le hτT hT),
    fun z θ τ hτ hτT hz =>
      (h.2 z θ τ hτ (lt_of_lt_of_le hτT hT) hz).mono (Set.Ico_subset_Ico_right hT)⟩

/-- **A uniform bound on the `ℋᵏ`-norm of the slices of a family** on `[0,T)`: the family is
in `ℋᵏ` at every fake time `τ < T` and the norms are bounded by `M`.  This is the form in
which the hypothesis `sup Xn₄ < ∞` and the conclusion `sup Xn₆ < ∞` of S2 are stated. -/
def XnBddOn (α : ℝ) (k : ℕ) (g : Fam) (T M : ℝ) : Prop :=
  ∀ τ, 0 ≤ τ → τ < T →
    HkMem α k (slice g τ) ∧ HkNorm α k (slice g τ) ≤ M

/-- A uniform `ℋ⁴` bound on `[0,T)` (`sup Xn₄ < ∞`, the hypothesis of S2). -/
abbrev Xn4BddOn (α : ℝ) (g : Fam) (T M : ℝ) : Prop := XnBddOn α 4 g T M

/-- A uniform `ℋ⁶` bound on `[0,T)` (`sup Xn₆ < ∞`, the conclusion of S2). -/
abbrev Xn6BddOn (α : ℝ) (g : Fam) (T M : ℝ) : Prop := XnBddOn α 6 g T M

/-! ## The regularity packages

`RegPkgMin` is copied **verbatim** from design §1 (`FTS_STRONG_ROUTE.md`); only the names are
qualified. -/
structure RegPkgMin (α : ℝ) (g : Fam) : Prop where
  c1     : ContDiffOn ℝ 1 (fun p : ℝ×ℝ×ℝ => g p.1 p.2.1 p.2.2) (Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Ioi 0)
  c4     : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0
  cont   : ∀ z θ, (z,θ) ∈ Work.Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Ici 0)
  mem4   : ∀ τ, 0 ≤ τ → Work.Spaces.HkMem α 4 (slice g τ)
  dbd : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd
  vanish : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π/2) τ = 0

/-- `RegPkgMin` with the `ℋ⁶`-membership and the uniform `ℋ⁶` bound added: what S1–S2
produce and what S5 hands on to the regularity transfer. -/
structure RegPkgH6 (α C : ℝ) (g : Fam) : Prop where
  min : RegPkgMin α g
  mem6 : ∀ τ, 0 ≤ τ → H6Mem α (slice g τ)
  bd6 : ∀ τ, 0 ≤ τ → Xn6 α (slice g τ) ≤ C

end Work.FTS.StrongPersist
