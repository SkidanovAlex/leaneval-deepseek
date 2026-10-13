/-
# `Work.FTS.Final.Defs` — the vocabulary of the end-to-end assembly

This is the vocabulary module of the **FTS/Final** area: the interfaces through which the
end-to-end wiring `Work.FTS.Final.exists_blowupAt_of_inputs` reads.

## What lives here

* the re-exported names of the physical bridge (`Fam`, `Uax`, `BiotSavartSwirl`,
  `PressureReconstructionOn`, `MeridianEqOn`, `RegPkg'`, `IsBslSolPos`), so that the statements of
  this area read exactly like the design's;
* the two definitions of the *new* strong route (`FTS_HARD_STMTS.lean.txt`, lead 01:30), copied
  verbatim from that statement file because the area that owns them (`FTS/StrongEps`) is still
  being built: the log-coordinate mollifier `Jeps`/`Jfam`, the `ε`-scheme `IsEpsSol`, its uniform
  bound `EpsUniform`, and the *statement* `GlobalStrong2` of `global_strong2` (whose proof is the
  `StrongEps` area's deliverable).  When `Submission/Work/FTS/StrongEps/` lands, a rename of the
  four names `Jeps`, `Jfam`, `IsEpsSol`, `EpsUniform` is all that is needed;
* the elliptic input `Work.FTS.EllSol.ExistsEllSolC` (the lead's class-C linear solution operator,
  already on disk in `Submission/Work/FTS/EllSol/ClassC.lean`) — re-exported, not copied.

## Conventions (do not change without changing every consumer)

* the *challenge* exponent is `α` (a `ℝ≥0` in the final statement); the *profile* exponent is
  `pExp α = 3α`;
* the physical vorticity of the reconstruction is `ω := −physOmega α A B g C` (design correction 1);
* the clock amplitude is `C.A = 2 * A` (design correction 2), with `A = Avort m`, `B = Bdyn m`;
* the stream function of the reconstruction is `merPsi (pExp α) A B Φ C`
  (`Work.FTS.MeridianDyn.merPsi`).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongGlobal.Main
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.FireFix.Firing
import Submission.Work.FTS.FinalClock.PhysClock
import Submission.Work.FTS.Top.Main
import Submission.Work.FTS.LocData6.Main
import Submission.Work.FTS.MeridianDyn.All

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)

set_option autoImplicit false

/-! ## Re-exported vocabulary -/

/-- `ℝ³` (definitionally the `R3` of every other area). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The open set on which the pointwise vorticity equation is available (the complement of the
axis and of the equatorial plane). -/
abbrev Uax : Set R3 := Work.FTS.PressureOn.Uax

/-- **The Biot–Savart law for swirl vorticity** (proved by `BSSwirl`,
`Work.FTS.BSSwirl.biotSavartSwirl`). -/
abbrev BiotSavartSwirl : Prop := Work.FTS.BSSwirl.BiotSavartSwirl

/-- **The pressure reconstruction** (design §1 item 5; owner `PressureOn`,
`Work.FTS.PressureOn.PressureReconstructionOn`). -/
abbrev PressureReconstructionOn (α : ℝ≥0) : Prop := Work.FTS.PressureOn.PressureReconstructionOn α

/-- The meridian scalar equation on the time window `(0,T)` (owner `MeridianDyn`). -/
abbrev MeridianEqOn (W ψ : ℝ → ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  Work.FTS.MeridianDyn.MeridianEqOn W ψ T

/-- The *corrected* regularity package of the profile (owner `RegPkgGal`). -/
abbrev RegPkg' (α : ℝ) (S : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Work.FTS.RegPkgGal.RegPkg' α S A B g

/-- **The elliptic law of the strong route** (owner `StrongGlobal`/`StrongLWP`): the paper's
(PolarBSL) with the Dirichlet data only for `z ≥ 0`. -/
abbrev IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop := Work.FTS.StrongGlobal.IsBslSolPos α F Ψ

/-- The `ℋ⁴` size `Xn α 4` (the frozen `Work.FTS.Nonlin.Xn`). -/
abbrev Xn (α : ℝ) (g : Fn) : ℝ := Work.FTS.Nonlin.Xn α g

/-- The `ℋ⁶` size of the strong route (`Work.FTS.StrongGlobal.Xn6`). -/
abbrev Xn6 (α : ℝ) (g : Fn) : ℝ := Work.FTS.StrongGlobal.Xn6 α g

/-- The profile class `RegPkgMin` of the strong route (owner `StrongGlobal`). -/
abbrev RegPkgMin (α : ℝ) (g : Fam) : Prop := Work.FTS.StrongGlobal.RegPkgMin α g

/-- The class (C) of the elliptic layer (owner `EllSol`, `Work.FTS.EllSol.ClassC`). -/
abbrev ClassC (α : ℝ) (g : Fn) : Prop := Work.FTS.EllSol.ClassC α g

/-- The elliptic package at order `k` of the class-C layer. -/
abbrev EllPkgK (α : ℝ) (k : ℕ) (Ce : ℝ) (g Φg : Fn) : Prop := Work.FTS.EllSol.EllPkgK α k Ce g Φg

/-- `EllPkgGo` (owner `VocabO`). -/
abbrev EllPkgGo (α Ce : ℝ) (g Φg : Fn) : Prop := Work.FTS.VocabO.EllPkgGo α Ce g Φg

/-- The star package `StarPkgo2` (owner `PhiStar`, `Work.FTS.VocabO2.StarPkgo2`). -/
abbrev StarPkgo2 (α Cs : ℝ) (Φs : Fn) : Prop := Work.FTS.VocabO2.StarPkgo2 α Cs Φs

/-- UnifIP (owner `CoercivityFix`/`IPGen`). -/
abbrev UnifIP (IP : ℝ → Fn → Fn → ℝ) (α₂ cc clo Cup Ccs : ℝ) : Prop :=
  Work.FTS.Nonlin.UnifIP IP α₂ cc clo Cup Ccs

/-- The primed norm interface `N4Norm'` (owner `NonlinRows`). -/
abbrev N4Norm' (Ci α₂ : ℝ) : Prop := Work.FTS.OpenPkg.N4Norm' Ci α₂

/-- The primed `IP`-level contract `N4Extra'` (owner `NonlinRows`). -/
abbrev N4Extra' (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop := Work.FTS.OpenPkg.N4Extra' IP α₂ Ct

/-- The elliptic input of the class-C layer: a **linear** solution operator `E` with the two
packages `EllPkgGo` and `EllPkgK 6` (owner `EllSol`, `Work.FTS.EllSol.ExistsEllSolC`, verbatim from
`FTS_HARD_STMTS.lean.txt`). -/
abbrev ExistsEllSolC : Prop := Work.FTS.ClassC.ExistsEllSolC

/-! ## The `ε`-scheme of the strong route (re-exported from `FTS/StrongEps`)

The area `Submission/Work/FTS/StrongEps/` has landed and owns the four definitions of design §B
(its `Basic.lean` defines `Jeps`, `Jfam`, `IsEpsSol`, `EpsUniform` with *the same bodies* as the
statement file).  The names below are therefore **re-exports** of that area's declarations, so that
a consumer of `FTS/Final` and a consumer of `FTS/StrongEps` speak about the same objects.
-/

/-- **(B) the log-coordinate mollifier** `s = log z`, `ζ = log tan θ`
(owner: `Work.FTS.StrongEps`, verbatim from `FTS_HARD_STMTS.lean.txt`). -/
abbrev Jeps : (ℝ × ℝ → ℝ) → ℝ → Fn → Fn := Work.FTS.StrongEps.Jeps

/-- The same, applied slicewise to a family. -/
abbrev Jfam : (ℝ × ℝ → ℝ) → ℝ → Fam → Fam := Work.FTS.StrongEps.Jfam

/-- **The `ε`-scheme on `[0,T]`**: `∂_τ g = J_ε[𝓛 + ℛ](J_ε g)`, `Ψ = Φs + E(J_ε g)`. -/
abbrev IsEpsSol : ℝ → (ℝ × ℝ → ℝ) → ℝ → ℝ → Fn → (Fn → Fn) → Fn → Fam → Prop :=
  Work.FTS.StrongEps.IsEpsSol

/-- **The uniform `ε`-bounds on every `[0,T]`.** -/
abbrev EpsUniform : ℝ → (ℝ × ℝ → ℝ) → Fn → (Fn → Fn) → Fn → ℝ → ℝ → Prop :=
  Work.FTS.StrongEps.EpsUniform

/-- **`GlobalStrong2`** — the *statement* of `Work.FTS.StrongEps.global_strong2` (verbatim from
`FTS_HARD_STMTS.lean.txt`, as a `Prop`): from the uniform `ε`-bounds, the global strong solution of
the dynamic modulated equation, with the positivised law `IsBslSolPos`, the canonical stream
function `PsiCan Φs E g`, the regularity package `RegPkgMin` and the uniform `C₀α²` bound.

This is the *dynamic-solution input* of the assembly (conjunct (4) of `Inputs`); its proof (E1–E6
of the design) is the `StrongEps` area's deliverable.  Until that area's `Assembly.lean` lands, the
statement is recorded here. -/
def GlobalStrong2 : Prop :=
  ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {C₀ K Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongEps.EllLimOK α E → Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
    Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K →
      ∃ g : Fam, IsDynGSolWith (IsBslSolPos α) α (PsiCan Φs E g) g ∧
        (∀ z θ, g z θ 0 = g₀ z θ) ∧ RegPkgMin α g ∧
        ∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2

/-! ## The clock of the dynamic modulation -/

/-- The modulation of the clock, extended to all of `ℝ` by `m s = μ (max s 0)`, where `μ` is the
dynamic modulation `muDyn α Φ g`.  This is the `m` of `Work.FTS.FinalClock.physClock_of_dyn`. -/
def maxMu (α : ℝ) (Φ g : Fam) : ℝ → ℝ := fun s => Work.FTS.Galerkin.muDyn α Φ g (max s 0)

/-- The amplitude `A = Avort m` and the companion `B = Bdyn m` of the clock (§2–§3 of
`FTS_PHYS_BRIDGE.md`).  The clock's own amplitude is `C.A = 2A` (design correction 2). -/
def ampA (m : ℝ → ℝ) : ℝ → ℝ := Work.FTS.FinalClock.Avort m
def ampB (m : ℝ → ℝ) : ℝ → ℝ := Work.FTS.FinalClock.Bdyn m

/-- **The clock data of the reconstruction**: the modulation identity `C.mu = muDyn α Φ g` (on the
fake-time half-line), the amplitude normalisation `C.A = 2A` (design correction 2), the two ODEs
`A' = -(1+μ)A`, `B' = -(1-μ)B` that the *physical* bridge's `MeridianEqOn` consumes, and the
positivity of `B`.  This is exactly the four clock hypotheses of
`Work.FTS.MeridianDyn.meridianEq_of_dynEq` (in `A B C`), with the two `HasDerivAt` clauses of the
meridian bridge. -/
def ClockData (α : ℝ) (Φ g : Fam) (A B : ℝ → ℝ) (C : Work.FTS.Physical.PhysClock) : Prop :=
  (∀ τ : ℝ, 0 ≤ τ → C.mu τ = Work.FTS.Galerkin.muDyn α Φ g τ) ∧
  (∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ) ∧
  (∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + C.mu τ) * A τ) τ) ∧
  (∀ τ : ℝ, 0 ≤ τ → HasDerivAt B (-(1 - C.mu τ) * B τ) τ) ∧
  (∀ τ : ℝ, 0 ≤ τ → 0 < B τ)

/-- **The `A`/`B`-clauses of the corrected package `RegPkg'`** (the ten clock clauses of design
§2, on the fake-time strip `[0,S]`): positivity, two-sided boundedness, differentiability with
`deriv` as derivative, boundedness of `deriv`, and `α`-Hölder continuity of `deriv`.  These are
exactly the hypotheses on the amplitude and the scaling that `RegPkg'` asks for, isolated so that
the *g*-part of the package can be stated as a provider over them (the ten clauses are *false* for
an arbitrary pair `A B`, so they must be a hypothesis of any such provider). -/
def ClockPkg (α S : ℝ) (A B : ℝ → ℝ) : Prop :=
  (∀ τ ∈ Set.Icc (0 : ℝ) S, 0 < A τ) ∧
  (∀ τ ∈ Set.Icc (0 : ℝ) S, 0 < B τ) ∧
  (∃ a₀ a₁ : ℝ, 0 < a₀ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, a₀ ≤ A τ ∧ A τ ≤ a₁) ∧
  (∃ b₀ b₁ : ℝ, 0 < b₀ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, b₀ ≤ B τ ∧ B τ ≤ b₁) ∧
  (∀ τ ∈ Set.Icc (0 : ℝ) S, HasDerivAt A (deriv A τ) τ) ∧
  (∀ τ ∈ Set.Icc (0 : ℝ) S, HasDerivAt B (deriv B τ) τ) ∧
  (∃ a₂ : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) S, |deriv A τ| ≤ a₂) ∧
  (∃ b₂ : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) S, |deriv B τ| ≤ b₂) ∧
  (∃ a₃ : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
    |deriv A τ - deriv A τ'| ≤ a₃ * |τ - τ'| ^ α) ∧
  (∃ b₃ : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
    |deriv B τ - deriv B τ'| ≤ b₃ * |τ - τ'| ^ α)

/-- **The data produced by the strong route for a family `g`**: the regularity package
`RegPkgMin` and the uniform `ℋ⁴`-bound `Xn α (slice g τ) ≤ C₀ α²` on the fake-time half-line.
This is the bundle that the sup bound, the RegPkg conversion, the clock data and the meridian
bridge all take as their hypothesis about `g`. -/
def DynOK (α C₀ : ℝ) (g : Fam) : Prop :=
  RegPkgMin α g ∧ ∀ τ : ℝ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2

theorem DynOK.regPkgMin {α C₀ : ℝ} {g : Fam} (h : DynOK α C₀ g) : RegPkgMin α g := h.1

theorem DynOK.Xn_le {α C₀ : ℝ} {g : Fam} (h : DynOK α C₀ g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2 := h.2

end Work.FTS.Final
