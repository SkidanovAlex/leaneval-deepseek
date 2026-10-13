/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Closed` — the closure obligation, split into the ruling's two lemmas

The area's remaining obligation is `Defs.EllClosed α Ce`: every linear operator `E` carrying the
two elliptic packages on the class `C` must send `LimSeq4`-limits to `C²`-convergent jets of
solutions (`Defs.ClosedE`).  This module *proves* the reduction of the ruling's §A — "compactness
from the package bounds, then uniqueness in the Fatou package class" — to two precisely named
analytic obligations, and nothing else:

* **`ClosedCompact α Ce`** (obligation 1, compactness): along every `LimSeq4`, some cofinal
  reindexing has `C²`-convergent jets (to a `C²` solution of the limit profile).  Route: the
  package `ℋ⁶`-bounds on `ℛ`, `U/sin 2θ`, `V` give local `C⁴`-bounds on `E (fn n)` (through the
  elliptic estimates `FTS.EllipticEst.TT.EllEstUnif`, proved in the tree), and Arzelà–Ascoli on
  the open quadrant gives the convergent reindexing.
* **`ClosedUniq α Ce`** (obligation 2, uniqueness of the limit jets): two jet-cluster-limits of the
  same operator along the same sequence have the same `C²`-jets on `Qd`.  Route: both are limits
  of the *same* solutions; the Fatou-class uniqueness (mode analysis: `r ≥ 0` is killed by decay,
  `r < 0` makes `Uop` or `Vop` non-`L²` near `0`) identifies their jets.  Note that this is *not*
  a uniqueness of functions (which is false — `Obstruction.not_bslSolPos_unique`), only of the
  `C²`-jets on the open quadrant.

## What is proved here

* `limSeq4_comp` — `LimSeq4` is stable under cofinal reindexing;
* `IsJetLimit` — "`Ψ` is a jet-cluster-limit of `E` along `fn`";
* **`EllClosed_of_compact_uniq`** — the reduction: obligations 1 + 2 give `EllClosed`;
* `existsEllSolCLim_of_compact_uniq` — and hence `ExistsEllSolCLim` (via `Glue.existsEllSolCLim_of`),
  i.e. Final's core (1) ∧ (1a) from `ExistsEllSolC` + the two obligations.

The proof of the reduction is the standard subsequence argument, with
`Filter.tendsto_of_subseq_tendsto`: given the compactness witness `Ψ`, every subsequence of a jet
has a further subsequence converging to the jets of *some* jet-cluster-limit, and obligation 2 says
that all of those are `Ψ`; hence the jets converge to `Ψ` on the nose.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.Glue

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

/-! ## Reindexing -/

/-- A `LimSeq4` is stable under composition with any index map tending to infinity. -/
theorem limSeq4_comp {α : ℝ} {fn : ℕ → Fn} {f : Fn} (hL : LimSeq4 α fn f) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) : LimSeq4 α (fun n => fn (σ n)) f where
  classC n := hL.classC (σ n)
  bound := by
    obtain ⟨B, hB⟩ := hL.bound
    exact ⟨B, fun n => hB (σ n)⟩
  c4 := hL.c4
  conv j i hji z θ hz := (hL.conv j i hji z θ hz).comp hσ

/-! ## The two obligations -/

/-- **`Ψ` is a jet-cluster-limit of `E` along the sequence `fn`**: `Ψ` is a `C²` solution of the
limit profile `f`, and the `C²`-jets of `E (fn n)` converge to those of `Ψ` along some cofinal
reindexing. -/
def IsJetLimit (α : ℝ) (E : Fn → Fn) (fn : ℕ → Fn) (f Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
    ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd ∧
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧ JConv (fun n => E (fn (σ n))) Ψ

/-- **Obligation 1 (compactness)**: along every `LimSeq4` some cofinal reindexing of the jets of
`E` converges, to a `C²` solution of the limit profile. -/
def ClosedCompact (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ Ψ : Fn, IsJetLimit α E fn f Ψ

/-- **Obligation 2 (uniqueness of the limit jets)**: two jet-cluster-limits of the same operator
along the same sequence have the same `C²`-jets on the open quadrant. -/
def ClosedUniq (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ Ψ Ψ' : Fn, IsJetLimit α E fn f Ψ → IsJetLimit α E fn f Ψ' →
      ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.mixed j i Ψ z θ = Work.Spaces.mixed j i Ψ' z θ

/-- **The analytic content of obligation 1, isolated**: along every `LimSeq4`, the package
solutions `E (fn n)` have uniform local growth bounds — of order `j + i ≤ 3`, so that the order-`2`
jets are equicontinuous on compacta, and with a decay factor `1/(1+z)` in the far field, so that
the limit decays.  (The `1/z` and `1/(θ(π/2−θ))` factors are the growth allowed near the two
boundaries of `Qd`.)

This is exactly what the elliptic a priori theory has to supply: the package bounds control the
*coefficients* `ℛ`, `U/sin 2θ`, `V` of `PhiTil α g (E g)`, and one has to reconstruct `E g` from
them (`Uop Φ = -3Φ - α z ∂_zΦ`, `Vop Φ = ∂_θΦ - tan θ · Φ`) and then apply the tree's
`TT.EllEstUnif` and the Agmon-type local-bound machinery. -/
def LocalBound (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ|
        ≤ C * (1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z)

/-! ## The reduction -/

/-- **The ruling's §A reduction, proved**: obligations 1 (compactness) and 2 (uniqueness of the
limit jets) give the closure obligation `EllClosed`. -/
theorem EllClosed_of_compact_uniq
    (hcomp : ∀ α Ce : ℝ, 0 < α → ClosedCompact α Ce)
    (huniq : ∀ α Ce : ℝ, 0 < α → ClosedUniq α Ce) :
    ∀ α Ce : ℝ, 0 < α → EllClosed α Ce := by
  intro α Ce hα E hE fn f hL
  obtain ⟨Ψ, hΨsol, hΨsm, hΨ⟩ := hcomp α Ce hα E hE fn f hL
  refine ⟨Ψ, hΨsol, hΨsm, ?_⟩
  intro j i hji z θ hz
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  -- reindex `ns` by a cofinal subsequence and apply compactness to the reindexed sequence
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hL' : LimSeq4 α (fun n => fn (ns (ψ n))) f := limSeq4_comp hL hnsψ.tendsto_atTop
  obtain ⟨Ψ₂, hΨ₂sol, hΨ₂sm, σ, hσ, hJ₂⟩ := hcomp α Ce hα E hE _ f hL'
  have h₂ : IsJetLimit α E fn f Ψ₂ :=
    ⟨hΨ₂sol, hΨ₂sm, ⟨fun n => ns (ψ (σ n)), hnsψ.tendsto_atTop.comp hσ, by
      simpa only [Function.comp_apply] using hJ₂⟩⟩
  have hjet := huniq α Ce hα E hE fn f hL Ψ Ψ₂ ⟨hΨsol, hΨsm, hΨ⟩ h₂ j i hji z θ hz
  refine ⟨fun n => ψ (σ n), ?_⟩
  rw [hjet]
  simpa only [Function.comp_apply] using hJ₂ j i hji z θ hz

/-- **`ExistsEllSolCLim` from `ExistsEllSolC` and the two obligations** — Final's core (1) ∧ (1a)
from the delivered elliptic layer plus compactness and limit-jet uniqueness. -/
theorem existsEllSolCLim_of_compact_uniq (hE : Work.FTS.ClassC.ExistsEllSolC)
    (hcomp : ∀ α Ce : ℝ, 0 < α → ClosedCompact α Ce)
    (huniq : ∀ α Ce : ℝ, 0 < α → ClosedUniq α Ce) : ExistsEllSolCLim :=
  existsEllSolCLim_of hE (EllClosed_of_compact_uniq hcomp huniq)

end Work.FTS_EllLimOK
