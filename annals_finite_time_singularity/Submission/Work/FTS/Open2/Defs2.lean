/-
# `FTS/Open2/Defs2` — the Open2 vocabulary (design item D, the N5 side)

This module is the vocabulary of the migration of the **open-package assembly (N5 side)** from
the old star package `Work.FTS.VocabO.StarPkgo` to the upgraded one,
`Work.FTS.VocabO2.StarPkgo2` (frozen in `Submission/Work/FTS/VocabO2.lean`), which is the package
the (delivered, `sorry`-free) N4 row bundle
`Work.FTS.Nonlinear.Open.n4Rows2` is stated over.

Nothing in the N5/N6 chain ever *opens* `StarPkgo2` (the package occurs only as a hypothesis that
is passed on to `PairData'.bound`); the migration is therefore a signature change, and the
constructions here are

* `RowInputs2'` — the per-piece table of §8 with **row 16 at the relaxed rate** `X³`, which is
  what `n4Rows2` produces (`VocabO2.NRows2.r16`; `√α·X³` is *not* reachable — the lead's
  `STARPKG_T2_LEAD.md` §1.6 and `Nonlinear/Open/Main.lean`).  Every other field is that of
  `Work.FTS.OpenPkg.RowInputs'`.  The relaxation is harmless for the assembly because row 16 is
  consumed through the comparison `X³ ≤ Pbd α X` (`Work.FTS.Nonlin.cube_le_Pbd`), i.e.
  `X³ ≤ α^{-3/2}X³`, which is inside `Pbd`'s `α^{-3/2}X³` budget;
* `PairData2`, `AprioriFields2`, `DynInputsOpen2` — the copies of `PairData'`, `AprioriFields'`
  and `DynInputsOpen` with `StarPkgo2` in place of `StarPkgo` (the other two have no star-package
  field at all, so their "migration" is literally the same field list; the copies are kept so
  that every name of the new chain is a name of *this* namespace);
* the transfers recorded here are `StarPkgo2.toStarPkgo` (the `extends` projection, used to feed
  the delivered lemmas that *consume* a `StarPkgo`), `AprioriFields2.toPrimed` and
  `DynInputsOpen2.toOpen`, which let the delivered N5/N6 chain (`OpenPkg.Top`,
  `OpenPkg.Galerkin`, `OpenPkg.exists_dynGSol_of_ode_open`) be re-used verbatim once the
  hypotheses are stated over `StarPkgo2`.  The opposite direction for `PairData2` does **not**
  exist and is not needed: `PairData2.bound` is a statement about *more* data than
  `PairData'.bound`, so it is consumed directly (see `Open2/Bridge2`, `Open2/Fields2`), while
  `PairData' → PairData2` is available in `Open2/Compat`.

Everything in this file is a definition or a `rfl`-level projection; the mathematical content of
the migration is in `Open2/Blocks2`, `Open2/Nterm2`, `Open2/N0Block2`, `Open2/Assembly2` and
`Open2/PairingBound2`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.OpenPkg.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField coeffOf IsSolOn IsGalFam
  ConvLocUnif DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau
  profileFam RegPkg prof Slab)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The row table with the relaxed row 16 -/

/-- **The per-piece table of §8, with row 16 at the rate `X³`.**

Field for field this is `Work.FTS.OpenPkg.RowInputs'`, except for `r16`, whose rate is the one
delivered by the row bundle `Work.FTS.Nonlinear.Open.n4Rows2`
(`Work.FTS.VocabO2.NRows2.r16 : |IP α (N3gg α g Φg) g| ≤ K·Xn α g ^ 3`).

The assembly consumes `r16` only through `X³ ≤ Pbd α X`, so nothing is lost: this is exactly the
"row-16 step replaced by `X³ ≤ α^{-3/2}X³`" of the design note. -/
structure RowInputs2' (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the perturbation is in the `ℋ⁴`-class of the frozen vocabulary -/
  reg4 : RegQ α 4 g
  r1 : Work.Spaces.HkMem α 4 (N0fix α) ∧ Xn α (N0fix α) ≤ C * α ^ 2
  r2 : Work.Spaces.HkMem α 4 (N03g α g) ∧
    Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  r3 : Work.Spaces.HkMem α 4 (N04aF α g) ∧
    Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r4 : Work.Spaces.HkMem α 4 (N04bF α g) ∧
    |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  r5 : Work.Spaces.HkMem α 4 (N05aF α g) ∧
    Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r6 : Work.Spaces.HkMem α 4 (N05bF α g) ∧
    |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r7 : Work.Spaces.HkMem α 4 (N06F α g) ∧
    |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r8 : Work.Spaces.HkMem α 4 (N1gg α g Φg) ∧
    Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  r9 : Work.Spaces.HkMem α 4 (N1gs α g Φg) ∧
    Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  r10 : Work.Spaces.HkMem α 4 (N1sg α Φs g) ∧
    Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  r11 : Work.Spaces.HkMem α 4 (N1ss α Φs) ∧ Xn α (N1ss α Φs) ≤ C * α ^ 2
  r12 : Work.Spaces.HkMem α 4 (N2gg α g Φg) ∧
    |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r13 : Work.Spaces.HkMem α 4 (N2gs α g Φg) ∧
    Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r14 : Work.Spaces.HkMem α 4 (N2sg α Φs g) ∧
    |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r15 : Work.Spaces.HkMem α 4 (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ C * α ^ 2
  /-- **row 16, relaxed**: `|(N₃^{gg}, g)| ≤ C·X³` (was `C·√α·X³`) -/
  r16 : Work.Spaces.HkMem α 4 (N3gg α g Φg) ∧
    |IP α (N3gg α g Φg) g| ≤ C * Xn α g ^ 3
  r17 : Work.Spaces.HkMem α 4 (N3gs α g Φg) ∧
    Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r18 : Work.Spaces.HkMem α 4 (N3sg α Φs g) ∧
    |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  r19 : Work.Spaces.HkMem α 4 (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ C * α ^ 3
  r20 : Work.Spaces.HkMem α 4 (N4gg α g) ∧
    |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r21 : Work.Spaces.HkMem α 4 (N4gs α g) ∧
    Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r22 : Work.Spaces.HkMem α 4 (N4sg α g) ∧
    |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r23 : Work.Spaces.HkMem α 4 (N4ss α) ∧ Xn α (N4ss α) ≤ C * α ^ 3
  r24 : Work.Spaces.HkMem α 4 (N5gg g) ∧ Xn α (N5gg g) ≤ C * Xn α g ^ 2
  r25 : Work.Spaces.HkMem α 4 (N5gs α g) ∧ Work.Spaces.HkMem α 4 (N5sg α g) ∧
    Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  r26 : Work.Spaces.HkMem α 4 (N5ss α) ∧ Xn α (N5ss α) ≤ C * α ^ 2
  rak : Work.Spaces.HkMem α 4 (Work.Construction.AK α) ∧ Xn α (Work.Construction.AK α) ≤ C
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ
  hkN0 : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  hkN : Work.Spaces.HkMem α 4
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  hkDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g)

/-! ## The N4 output, the N5 fields and the N6 bundle over `StarPkgo2` -/

/-- **The output of `pairing_bound_open2`** (the `StarPkgo2` analogue of
`Work.FTS.OpenPkg.PairData'`). -/
structure PairData2 (IP : ℝ → Fn → Fn → ℝ) (CcN Ce Cs α₄ : ℝ) : Prop where
  hCcN : 0 < CcN
  hα₄ : 0 < α₄
  bound : ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ g Φs Φg : Fn,
    GalClass α g → Work.FTS.VocabO2.StarPkgo2 α Cs Φs → EllPkgGo α Ce g Φg →
    Xn α g ≤ α ^ (7 / 4 : ℝ) →
    |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * (α + α ^ (-(1 : ℝ)) * Xn α g + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2)
      ∧ |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)| ≤ 1 / 2
      ∧ |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Pbd α (Xn α g)

/-- **The a-priori fields of N6, over `StarPkgo2`.**  This structure carries no star-package
field (only the perturbation `g₀`, the stream functions `Φs`/`EllSol` as *data*, the basis and
the open-quadrant limit bound), so it is field-for-field
`Work.FTS.OpenPkg.AprioriFields'`; the copy exists so that the whole new chain is stated in the
`Open2` vocabulary. -/
structure AprioriFields2 (IP : ℝ → Fn → Fn → ℝ) (α C₀ clo cc CcN Ce Cs : ℝ) (φ : ℕ → Fn)
    (Φs : Fn) (EllSol : Fn → Fn) (g₀ : Fn) : Prop where
  /-- **`hInit`**: the projected datum lies in the a-priori ball. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n,
    (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hCoeffBound`**: every Galerkin solution stays in the a-priori ball. -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hProfileBdd`**: uniform local bounds on the Galerkin profiles. -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.Galerkin.Slab →
      ∃ Cb : ℝ, ∀ n : ℕ, ∀ p ∈ K, |Work.FTS.Galerkin.prof φ c n p| ≤ Cb
  /-- **`hLimBound`**: the limit of a convergent subsequence obeys the a-priori bound. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Xn α (slice g τ) ≤ C₀ * α ^ 2

/-- The downgrade `AprioriFields2 → AprioriFields'` (the two have the same field list). -/
theorem AprioriFields2.toPrimed {IP : ℝ → Fn → Fn → ℝ} {α C₀ clo cc CcN Ce Cs : ℝ}
    {φ : ℕ → Fn} {Φs : Fn} {EllSol : Fn → Fn} {g₀ : Fn}
    (h : AprioriFields2 IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀) :
    Work.FTS.OpenPkg.AprioriFields' IP α C₀ clo cc CcN Ce Cs φ Φs EllSol g₀ :=
  ⟨h.hInit, h.hCoeffBound, h.hProfileBdd, h.hLimBound⟩

/-- **The Galerkin (N6) bundle over `StarPkgo2`** — the `StarPkgo2` analogue of
`Work.FTS.OpenPkg.DynInputsOpen`. -/
structure DynInputsOpen2 (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  /-- the fields shared with `DynCore` -/
  core : Work.FTS.OpenPkg.DynCore Law α g₀ C₀
  Cs : ℝ
  Ce : ℝ
  hΦs : Work.FTS.VocabO2.StarPkgo2 α Cs (core.Φs)
  hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (core.EllSol g)

/-- The downgrade `DynInputsOpen2 → DynInputsOpen`. -/
def DynInputsOpen2.toOpen {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputsOpen2 Law α g₀ C₀) : Work.FTS.OpenPkg.DynInputsOpen Law α g₀ C₀ :=
  ⟨hin.core, hin.Cs, hin.Ce, hin.hΦs.toStarPkgo, hin.hEllSol⟩

end Work.FTS.Open2
