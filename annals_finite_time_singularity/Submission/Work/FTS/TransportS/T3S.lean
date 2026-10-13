/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T3S_Dz`: the `D_z` half of `Transport3` in the true form (design `ELL_H2_LEAD.md` §B3)

The frozen statement (verbatim from `Submission/Work/FTS/ELL_H2_STATEMENTS.lean.txt`):

```
theorem T3S_Dz : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    SmoothOpen f → WlInfMem α 4 f → CoefThMem 3 f →
    RegQ α 4 g → HkMem α 5 g → DecayAll 4 g →
    |H4Pair α (fun z θ => f z θ * Dz g z θ) g|
      ≤ C / √(gam α - 1) * (WlInf α 4 f + CoefTh 3 f) * Xn α g ^ 2
```

## How it is obtained

* the `D_θ` half of the same pairing is **already proved** in the interior class:
  `Work.FTS.H2.T3Q.T3Q_Dth`;
* the `D_z` half splits pointwise as `H4PairInt α (f·D_z g) g = GoodZ + Badz2`, where
  `Badz2 = Badz + Mismatchz` is the "exceptional" part (the order-five "all derivatives on
  `g`" summands together with the "mismatch" summands, in which every `D_θ`-derivative falls
  on `f`); the good part is bounded **pointwise** by `C|f|_{𝒲^{4,∞}}·HkIntegrand α 4 g`
  (`Work.FTS.H2.T3Q.GoodZPt`), so only `Badz2` needs an integration by parts;
* the workspace theorem `Work.FTS.H2.T3Q.T3Q_of_Badz2` performs that assembly in the
  `SmoothQuad` class and in terms of the two inputs `Badz2BoundQ` and `AesmZ`.  The design's
  point (`ELL_H2_LEAD.md` §B3) is that the *old* `Badz2BoundQ` is unprovable because its
  mismatch half fails for `α < 1/30` (`T3Q/NOTES_MismatchMargPt_FALSE.md`,
  `T3Mismatch/NOTES_mismatchz_bad_bound.md`), while with the extra hypothesis `CoefThMem 3 f`
  the mismatch factor `sin(2θ)·sin(2θ)^{(η-γ)/2}` is bounded for **all** `0 < α ≤ 1`, so the
  mismatch half closes termwise.

This module therefore records

* the hypothesis bundles `T3SF`, `T3SG` (the frozen ones);
* `T3Good` — the pointwise bound on the good part (a corollary of the proved
  `Work.FTS.H2.T3Q.GoodZPt`, restated in the frozen class);
* `T3Bad` — the replacement of `Badz2BoundQ`: the same statement with `SmoothOpen f`,
  `WlInfMem α 4 f`, `CoefThMem 3 f` in place of `SmoothQuad f`, `WlInfMem α 4 f`;
* `T3Aesm` — the replacement of `AesmZ` in the frozen class;
* `T3S_of_pieces` — the assembly (the `D_z` half of `T3Q_of_Badz2`), reduced to the above.

The per-slot version of `T3Bad` (which is what the `IP4` rows consume) is in
`Submission/Work/FTS/TransportS/Slots.lean`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.H2.T3Q.T3Q
import Submission.Work.FTS.H2.T3Q.GoodZPt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The hypothesis bundles -/

/-- The frozen `f`-side hypotheses of `T3S_Dz`. -/
def T3SF (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.WlInfMem α 4 f
    ∧ Work.FTS.VocabO.CoefThMem 3 f

/-- The frozen `g`-side hypotheses of `T3S_Dz`. -/
def T3SG (α : ℝ) (g : Fn) : Prop :=
  Work.FTS.Nonlin.RegQ α 4 g ∧ Work.Spaces.HkMem α 5 g ∧ Work.Spaces.DecayAll 4 g

theorem T3SF.smoothOpen {α : ℝ} {f : Fn} (h : T3SF α f) :
    Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem T3SF.wlInf {α : ℝ} {f : Fn} (h : T3SF α f) : Work.Spaces.WlInfMem α 4 f := h.2.1
theorem T3SF.coef {α : ℝ} {f : Fn} (h : T3SF α f) : Work.FTS.VocabO.CoefThMem 3 f := h.2.2
theorem T3SG.reg {α : ℝ} {g : Fn} (h : T3SG α g) : Work.FTS.Nonlin.RegQ α 4 g := h.1
theorem T3SG.hk4 {α : ℝ} {g : Fn} (h : T3SG α g) : Work.Spaces.HkMem α 4 g := h.1.2.1
theorem T3SG.hk5 {α : ℝ} {g : Fn} (h : T3SG α g) : Work.Spaces.HkMem α 5 g := h.2.1

/-- The frozen statement of `T3S_Dz`, as a `Prop`. -/
def T3SProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T3SF α f → T3SG α g →
    |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2

/-! ## The three inputs of the `D_z` half -/

/-- **Input 1**: the pointwise bound on the *good* part of the `D_z` pairing, i.e. on
`H4PairInt α (f·D_z g) g - Badz2 α f g` (the `SmoothOpen`/`WlInfMem` form of the proved
`Work.FTS.H2.T3Q.GoodZPt`, which is stated for `SmoothQuad`). -/
def T3Good : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T3SF α f → T3SG α g →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
          - Work.FTS.H2.Badz2 α f g z θ|
        ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ

/-- **Input 2**: the replacement of `Work.FTS.H2.T3Q.Badz2BoundQ`: the exceptional part of
the `D_z` pairing, with the design's extra hypothesis `CoefThMem 3 f` (which makes the
mismatch half closable for all `0 < α ≤ 1`). -/
def T3Bad : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T3SF α f → T3SG α g →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Badz2 α f g z θ|
      ≤ C * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * Work.Spaces.HkSq α 4 g

/-- **Input 3**: the a.e. strong measurability of the radial marginal of `Badz2` together
with the `θ`-slice integrability of the good part (the `SmoothOpen` form of `AesmZ`). -/
def T3Aesm : Prop :=
  ∀ (α : ℝ) (f g : Fn), 0 < α → T3SF α f → T3SG α g →
    MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Badz2 α f g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
          - Work.FTS.H2.Badz2 α f g z θ) Work.Spaces.Iθ)

/-! ## The frozen statement as a `Prop` (no proof obligations here) -/

/-- The frozen `T3S_Dz`, stated as a `Prop` so that it can be cited without a proof body.
It is `T3SProp` (kept under both names for the consumers' convenience). -/
abbrev T3S_Dz : Prop := T3SProp

end Work.FTS.TransportS
