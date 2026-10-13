/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.FatouG` — the limit vocabulary (its `HasPkgF` half RETIRED, 2026-10-11)

**STATUS.**  The package hypothesis `HasPkgF` defined in this module was **denied** by the lead's
ruling (`sources/ftsV2/fts_ellimok_ruling.md`): `PkgMemSq`/`PkgSlice` are false by homogeneity and
`PkgDecay`/`PkgStrip`/`PkgCorner` are false as well (see the banners in `PkgRepair.lean`); hence
`ExistsEllSolCF` is false and the predicates `FatouDataG`, `SmallFatouDataG`, `ClosedCompact3G`,
`SmallCompact3G` and the theorem `fatouDataG_of_hasPkgF`/`smallFatouDataG` of this module are
vacuous in their hypothesis and are superseded by `FatouH.lean`'s `HasPkgH`-indexed
`LocalBoundH`/`FatouDataH`/`BoxDataH`/`ClosedCompact3H`.

**KEPT (endorsed by the ruling)**: the *minimal limit package* `FatouPkgG`, the limit vocabulary
`IsJetLimit3G`/`JConv3`/`ClosedE3G`, and the package-free uniqueness `ClosedUniq3G`, all of which
the H-chain uses unchanged.  `RulingELF.lean` still imports this module for the refuted definitions
it uses in `pkgMemSq_degenerate`.

## The original header

# `FTS_EllLimOK.FatouG` — the limit vocabulary over the repaired packages

`NOTES.md` §10.5 steps 1–2.  The frozen predicates of `Defs3.lean` are stated in the **naive**
`θ`-normalisation (`pth Ψ = ∂_θΨ`), which the packages cannot supply: they carry the *granulated*
`D_θ = sin(2θ)·∂_θ` and, for the `1/cos θ`-membership, the `PhiTil`-part of the solution only
(`Theta α g = sin(2θ)·L₁₂ g/(4α)` is a *source-only* term, so `HkMem (E g/cos θ)` does not follow
from `HkMem (PhiTil α g (E g)/cos θ)`).  Recovering one naive `θ`-derivative from a granulated
slot costs a factor `sin(2θ)^{-1}`, which the weight `sin(2θ)^{-η}` (`η = 99/100 < 1`) cannot
absorb; and `PkgDecay`/`PkgCorner`/`PkgSlice` are the other three fields that the packages
provably lack (`REPLY_LEAD2.md`).

This module restates the limit vocabulary over the repaired hypothesis `HasPkgF`, so that the
order-`3` closure chain can be re-run and conclude the **frozen** `FinalV2.EllLimOK3` (whose own
body mentions only the law, `C³` and the jet convergence, hence is unaffected by the change).

## The design (and why the package below is *minimal*)

The only consumer of the limit's package is the **uniqueness** half of the closure
(`ClosedUniq3_small`), and the only clauses of the package that the uniqueness proof
(`UniqFatou.eqOn_of_same_law`) reads are

* the law (`IsBslSolPos α f Ψ`),
* `ContDiffOn ℝ 3 (uncurry Ψ) Qd`,
* `HkMem α 0 Ψ` and `HkMem α 0 (Ψ/cos θ)`,
* `BoxReg Ψ` — the closed-box regularity, whose absence made the frozen `FatouPkg` unprovable
  (`NOTES.md` §0bis).

`FatouPkgG` below is exactly that quintuple: it is *provable* from the repaired packages, and it is
*sufficient* for uniqueness.  (The extra clauses of the frozen `FatouPkg` — the naive `∂_θ`- and
`∂_θ²`-memberships, the `L²`-memberships, `ZDecay` — are used by nothing in the closure chain:
`ZDecay` and the decay clause of `FatouData` only served the frozen package, and the `L²`-records
only served `ZDecay`.)

`FatouDataG` is the sequence-level hypothesis the compactness theorem consumes: the uniform
`ℋ⁰`-memberships with their `HkSq` bounds along a `LimSeq4`, and the box data.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Defs
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.PkgJets.boxDataD_uniform
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The repaired hypothesis `HasPkgF`

`HasPkgE` (`PkgRepair`) is the frozen two packages plus the five fields they provably lack
(`PkgCos`, `PkgDecay`, `PkgStrip`, `PkgCorner`, `PkgSlice`).  The last missing piece for the
sequence-level Fatou step is a **quantitative** version of the pinning membership: `HkMem` alone
says that `HkSq α 0 (E g)` is *finite*, not that it is bounded by a constant times the source norm,
and the Fatou step needs one constant working for a whole sequence (`LimSeq4.bound` bounds
`Xn6 α (fn n)` but nothing else).  `PkgMemSq` is exactly that bound, for the two memberships the
uniqueness consumes.  (It is the level-`0` case of the paper's a priori estimate `prop:L2`; the
`∃C`-form of `phiTil_bundle_of_hasPkgD` cannot supply it.) -/

/-- **The quantitative `ℋ⁰`-membership field**, in the form the sequence-level Fatou step
consumes: for the two quantities `E g` and `E g/cos θ`, the `ℋ⁰`-membership, the *quantitative*
`HkSq` bound, and the *uniform-in-`z`* `θ`-slice bound, all relative to the source's `ℋ⁶`-norm.

The third clause is genuinely needed: `HkMem_fatou` bounds the `θ`-slice of the limit's integrand
by the `liminf` of the slices of the members, which is finite only under a bound that is uniform in
the sequence index; `HkMem` alone gives one finite value *per member*.  (The uniform-in-`z`
`θ`-slice form is the shape of the already-assumed `PkgSlice` field, so this is the same kind of
object, now for the solution itself.) -/
def PkgMemSq (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g →
    (Work.Spaces.HkMem α 0 (E g) ∧
        Work.Spaces.HkSq α 0 (E g) ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E g) z θ)
            ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g)) ∧
      (Work.Spaces.HkMem α 0 (fun z θ => E g z θ / Real.cos θ) ∧
        Work.Spaces.HkSq α 0 (fun z θ => E g z θ / Real.cos θ)
          ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => E g z θ / Real.cos θ) z θ)
              ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g))

/-- **The fully repaired hypothesis**: the frozen packages plus `PkgCos`, `PkgDecay`, `PkgStrip`,
`PkgCorner`, `PkgSlice` (the five fields of `HasPkgE`) plus the quantitative membership field
`PkgMemSq`. -/
def HasPkgF (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  HasPkg α Ce E ∧ PkgCos α E ∧ PkgDecay α E ∧ PkgStrip α E ∧
    PkgCorner α Ce E ∧ PkgSlice α Ce E ∧ PkgMemSq α Ce E

theorem HasPkgF.toHasPkg {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgF α Ce E) :
    HasPkg α Ce E := h.1

theorem HasPkgF.toHasPkgD {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgF α Ce E) :
    HasPkgD α Ce E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem HasPkgF.toHasPkgE {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgF α Ce E) :
    HasPkgE α Ce E :=
  ⟨h.toHasPkgD, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem HasPkgF.memSq {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgF α Ce E) :
    PkgMemSq α Ce E := h.2.2.2.2.2.2

theorem hasPkgF_of_parts {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgE α Ce E)
    (hm : PkgMemSq α Ce E) : HasPkgF α Ce E :=
  ⟨h.toHasPkgD.toHasPkg, h.toHasPkgD.cos, h.toHasPkgD.decay, h.toHasPkgD.strip,
    h.corner, h.slice, hm⟩

/-- The defining equation of `HasPkgF`, as an `iff` — the checklist for the EllSol-side supply. -/
theorem hasPkgF_iff {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} :
    HasPkgF α Ce E ↔ HasPkg α Ce E ∧ PkgCos α E ∧ PkgDecay α E ∧ PkgStrip α E ∧
      PkgCorner α Ce E ∧ PkgSlice α Ce E ∧ PkgMemSq α Ce E :=
  Iff.rfl

/-- The same, from the seven fields separately. -/
theorem hasPkgF_of_seven {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h1 : HasPkg α Ce E)
    (h2 : PkgCos α E) (h3 : PkgDecay α E) (h4 : PkgStrip α E) (h5 : PkgCorner α Ce E)
    (h6 : PkgSlice α Ce E) (h7 : PkgMemSq α Ce E) : HasPkgF α Ce E :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **The `ExistsEllSolC` clause with the repaired hypothesis**: the same existence statement as
`ClassC.ExistsEllSolC`, with the packages on the class `C` strengthened by the five fields of
`HasPkgE` and the quantitative membership field `PkgMemSq`.  This is the hypothesis under which
this area proves the lead's conjuncts (1) + (1a′); it is the "EllSol-side supply" item of
`REPLY_LEAD2.md`. -/
def ExistsEllSolCF : Prop :=
  ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ E : Fn →ₗ[ℝ] Fn, HasPkgF α Ce E

/-! ## The limit package and the order-`3` vocabulary -/

/-- **The granulated decay condition** (the honest form of `Defs3`/`EllipticEst.ZDecay`):
the `z²`-weighted sum of squares of `Ψ` and of its *granulated* first and second derivatives tends
to `0` at `z → ∞`.  This is what excludes the homogeneous mode `z^{-5/α} sin 2θ`.  It is **not**
part of `FatouPkgG` (the minimal package): no step of the closure chain consumes it.  It is kept
here for the ledger of the interface change, and for any future consumer that wants the frozen
`FatouPkg`'s decay clause. -/
def ZDecayG (Ψ : Fn) : Prop :=
  ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => z ^ 2
    * ((Ψ z θ) ^ 2 + (Work.Spaces.pz Ψ z θ) ^ 2 + (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
      + (Work.Spaces.mixed 0 1 Ψ z θ) ^ 2 + (Work.Spaces.mixed 0 2 Ψ z θ) ^ 2))
    Filter.atTop (𝓝 0)

/-- **The limit package (minimal form).**  What the closure chain proves of a cluster limit, and
what the uniqueness argument consumes: the law, `C³`-regularity on the open quadrant, the two
`ℋ⁰`-memberships (`Ψ` and `Ψ/cos θ`) and the closed-box regularity. -/
structure FatouPkgG (α : ℝ) (f Ψ : Fn) : Prop where
  sol : Work.FTS.StrongGlobal.IsBslSolPos α f Ψ
  smooth : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd
  mem : Work.Spaces.HkMem α 0 Ψ
  memCos : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ)
  box : BoxReg Ψ

/-- **Order-`3` jet-cluster-limit over the repaired package.** -/
def IsJetLimit3G (α : ℝ) (E : Fn → Fn) (fn : ℕ → Fn) (f Ψ : Fn) : Prop :=
  FatouPkgG α f Ψ ∧
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧ JConv3 (fun n => E (fn (σ n))) Ψ

/-- **Order-`3` jet uniqueness over the repaired package**: two order-`3` jet-cluster-limits of the
same operator along the same sequence have the same `C³`-jets on the open quadrant.  (No package
hypothesis on `E` is needed.) -/
def ClosedUniq3G (α : ℝ) : Prop :=
  ∀ (E : Fn → Fn) (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ Ψ Ψ' : Fn, IsJetLimit3G α E fn f Ψ → IsJetLimit3G α E fn f Ψ' →
      ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.mixed j i Ψ z θ = Work.Spaces.mixed j i Ψ' z θ

/-- **Order-`3` closure over the repaired package**: along every `LimSeq4` the `C³`-jets of
`E (fn n)` converge, without reindexing, to the jets of a limit in `FatouPkgG`. -/
def ClosedE3G (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ Ψ : Fn, FatouPkgG α f Ψ ∧ JConv3 (fun n => E (fn n)) Ψ

/-- **Obligation 1 (compactness) over the repaired hypothesis.** -/
def ClosedCompact3G (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkgF α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ Ψ : Fn, IsJetLimit3G α E fn f Ψ

/-- **The small-`α` shapes over the repaired hypothesis.** -/
def SmallCompact3G : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, ClosedCompact3G α Ce

def SmallUniq3G : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ClosedUniq3G α

/-! ## The sequence-level Fatou data over the repaired hypothesis -/

/-- **The sequence-level Fatou data**: along every `LimSeq4`, for the two quantities `E (fn n)`
and `E (fn n)/cos θ`, the `ℋ⁰`-membership, one common `HkSq` bound and one common
uniform-in-`z` `θ`-slice bound; and the closed-box data.  These are exactly the clauses the
compactness theorem consumes; they are produced from `HasPkgF` by `fatouDataG_of_hasPkgF`. -/
def FatouDataG (α Ce : ℝ) : Prop :=
  (∀ E : Fn →ₗ[ℝ] Fn, HasPkgF α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, Work.Spaces.HkMem α 0 (E (fn n)) ∧
        Work.Spaces.HkSq α 0 (E (fn n)) ≤ C ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E (fn n)) z θ) ≤ C)) ∧
      (∀ n : ℕ, Work.Spaces.HkMem α 0 (fun z θ => E (fn n) z θ / Real.cos θ) ∧
        Work.Spaces.HkSq α 0 (fun z θ => E (fn n) z θ / Real.cos θ) ≤ C ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => E (fn n) z θ / Real.cos θ) z θ) ≤ C))) ∧
  BoxDataD α Ce

/-- The small-`α` Fatou data. -/
def SmallFatouDataG : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ, FatouDataG α Ce

/-! ## The derivation of the sequence-level data from the field

`PkgMemSq` gives the two memberships with `HkSq ≤ Ce·Xn6 α g` *per source* `g`; along a `LimSeq4`
the source norms are bounded by `B` (`LimSeq4.bound`), so one constant works for the whole
sequence.  `BoxDataD` is the box clause (`PkgJets.boxDataD_uniform`). -/

theorem fatouDataG_of_hasPkgF {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    FatouDataG α Ce := by
  refine ⟨?_, Work.FTS_EllLimOK.PkgJets.boxDataD_uniform hα hα1⟩
  intro E hE fn f hL
  obtain ⟨B, hB⟩ := hL.bound
  refine ⟨|Ce| * max B 0 + 1, by positivity, ?_, ?_⟩
  · intro n
    obtain ⟨⟨hmem, hsq, hth⟩, -⟩ := hE.memSq (fn n) (hL.classC n)
    have hBle : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 := le_trans (hB n) (le_max_left _ _)
    have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (fn n) := Work.Spaces.HkNorm_nonneg α 6 (fn n)
    have h1 : Ce * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ |Ce| * max B 0 :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self Ce) hXnn)
        (mul_le_mul_of_nonneg_left hBle (abs_nonneg Ce))
    exact ⟨hmem, by linarith [h1, hsq], fun z hz => by linarith [h1, hth z hz]⟩
  · intro n
    obtain ⟨-, hmem, hsq, hth⟩ := hE.memSq (fn n) (hL.classC n)
    have hBle : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 := le_trans (hB n) (le_max_left _ _)
    have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (fn n) := Work.Spaces.HkNorm_nonneg α 6 (fn n)
    have h1 : Ce * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ |Ce| * max B 0 :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self Ce) hXnn)
        (mul_le_mul_of_nonneg_left hBle (abs_nonneg Ce))
    exact ⟨hmem, by linarith [h1, hsq], fun z hz => by linarith [h1, hth z hz]⟩

/-- **The sequence-level Fatou data holds over the repaired hypothesis.** -/
theorem smallFatouDataG : SmallFatouDataG :=
  ⟨1, one_pos, fun α hα hα1 Ce => fatouDataG_of_hasPkgF hα hα1⟩

end Work.FTS_EllLimOK
