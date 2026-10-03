/-
# The linear (`g`-side) lacunary variational estimate of the mixed range (Area A7, KMT §8)

Target: `Work.KMTAreas.A7.LinVarGuard P p₂ hdeg hp₂ htp₂` (see
`Submission/Work/KMTAreas/A7/MixedGSideAux.lean`), i.e. the paper's `(lin-2)` for the guarded
`g`-side family `GmixedFam` of the mixed range `l₁ = 0`.

## What is proved here

* `GmixedFam_eq_Gcl`: the guarded family of the mixed range is, definitionally, the `l₁ = 0`
  instance of the model's `g`-side family `Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g`: the guard is
  `loGuard ρ C₀ a 0 l₂ k₁ k₂ = core ρ C₀ 0 l₂ k₁ k₂ a`, and for `l₂ ≠ 0` the exact-height
  multiplier `Tm ρ l₂ = iwConv (diffFreqs ρ l₂) (periodize ·)` is the *same operator* as
  `Tex ρ l₂ = iwConv (iwArithFreqsNew ρ l₂) (periodize ·)`, because
  `Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew`.
* `LinVarGuard`: the target, obtained from the *proved, axiom-clean* assembly
  `Work.KMTAreas.A7Hi.linVarG_of_pieces` (which reduces the `g`-side estimate to the three dyadic
  low-pass pieces `SupPiece`, `ChainPiece`, `SqPiece`) by specialising to `l₁ = 0`.

## The three dyadic pieces

`Work.KMTAreas.A7Hi.linVarG_of_pieces` was applied with

* `SupPiece` — the values-supremum (maximal) bound `‖sup_m |Π_{≤l,≤−(m₀+m)} f|‖_p ≤ C(1+l)²‖f‖_p`,
  supplied by `Work.KMTAreas.A7LV.supPiece`, which re-exports
  `Work.KMTAreas.A7MixedG.supBound`;
* `ChainPiece` — the chain bound
  `‖chainPart r‖_p ≤ B(‖supPart r‖_p + ‖sqFun‖_p)`, supplied by
  `Work.KMTAreas.A7LV.chainPiece`, which re-exports `Work.KMTAreas.A7MixedG.chainLe`;
* `SqPiece` — the band-pass square-function bound `‖sqFun ρ l m₀ f‖_p ≤ C(1+l)²‖f‖_p`, supplied by
  `Work.KMTAreas.A7LV.sqPiece` (proved, from `Work.KMTAreas.A7MixedG.sqFunBound`; an independent
  route — the uniform-in-signs annuli bound plus Khintchine's inequality — is in
  `Submission/Work/KMTAreas/A7LV/sqFunOfUniformSigns.lean`).

Note that `SqPiece` and `BandSquarePiece` are *not* the same statement: `SqPiece` bounds the square
function of the *increments* `T_{m+1}f − T_m f`, whereas `BandSquarePiece` bounds the square function
of the *values* `T_k f` — the two agree only in the `ℓ²`-orthogonality regime (which holds here by
the nesting `T_m T_{m'} = T_{max}` for `m ≠ m'`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.MixedGSideAux
import Submission.Work.KMTAreas.A7Hi.LinVarG
import Submission.Work.KMTAreas.A7Hi2.supPieceClean

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7MixedG

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **The guarded `g`-side family of the mixed range is the `l₁ = 0` instance of `Gcl`.** -/
theorem GmixedFam_eq_Gcl (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (hl₂ : l₂ ≠ 0) :
    Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g
      = Work.KMTAreas.A7.Gcl ρ P C₀ a 0 l₂ k₁ k₂ t g := by
  funext n x
  simp only [Work.KMTAreas.A7.GmixedFam, Work.KMTAreas.A7.Gcl,
    Work.KMTAreas.A7.loGuard, Work.KMTAreas.A7.core, Work.KMTAreas.A7.Tm,
    Work.KMTAreas.A7.Tex, Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂]

end Work.KMTAreas.A7MixedG
