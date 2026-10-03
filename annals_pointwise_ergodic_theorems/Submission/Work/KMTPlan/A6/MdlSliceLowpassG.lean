/-
# The `g`-side low-pass model slice of the `(2,2,1)` large-scale model estimate (area A6)

Target: `Work.KMTPlan.A6.MdlSliceLowpassG`, i.e. the `k₂ = 0`, `j₂ = 0`, `p = 2` slice of the
`g`-side linear lacunary variational estimate of Krause--Mirek--Tao, *in the model carrier*:

  `‖ V^R_n (1_{mdlCore n} · T^{≤l₂}_{φ̃_{N_n,0,t}}(Π_{l₂,≤-du}g)) ‖_{ℓ²(ℤ)}
      ≤ C(ρ,Λ) · lossWeight A ρ l₁ l₂ k₁ 0 · ‖g‖_{ℓ²(ℤ)}`,  `N_n = ⌊a n⌋`, `u = uScale ρ L`,

for every `Λ`-lacunary `a`, all `l₁,l₂,k₁`, `t ∈ [1/2,1]`, under `ρ ≤ 1/(2C₀)`.

## Status (session 3)

The file now contains the **complete reduction of the target to the two documented deep inputs**:
`Work.KMTPlan.A6.MdlSliceLowpassG_of_sockets` (PROVED, axiom-clean) has the target's statement
verbatim, with `(hSup : Work.KMTAreas.A7Hi2.SupPiece)` and `(hChain : Work.KMTAreas.A7Hi2.ChainPiece)`
as its only hypotheses; the target `MdlSliceLowpassG` itself is therefore one line away:

```lean
theorem MdlSliceLowpassG … := MdlSliceLowpassG_of_sockets P hd C₀ hC₀ R hR <SupPiece> <ChainPiece>
```

(and those two follow from the sharper node `Work.KMTAreas.A7HiRep.chainPartSqFunPos` through the
already-proved `A7HiRep.supPieceOfChainPartSqFun` / `A7HiRep.chainPieceOfChainPartSqFun`).  The
proof splits on the non-aliasing of `(ℚ/ℤ)_{≤l₂}` at the window `-(d·uScale ρ L)`:

* the **bad** regime — `l₂ = 0`, or `¬ NonAliasing` (which forces `lcL l₁ l₂ k₁ 0 ≤ D(ρ)`, hence
  bounded height) — is proved **without any deep input**, using the axiom-clean bounded-height
  packet estimate `Work.KMTPlan.A6.PieceBoundedH.sliceGBound` and the proved height-`0` slice
  `HeightZeroSliceBound`;
* the **good** regime is the collapse `slice_eq_tex` to the `Gcl`-family plus the explicit-`ρ`-range
  bound `GclVarEstimateExplicitLs`, whose only inputs are the two sockets.

See `NOTES_MdlSliceLowpassG_SESSION3.md` at the workspace root for the details, the two workspace
hazards met on the way, and the exact endgame.

## Status (session 4)

The §4c dichotomy is now factored through the abstract predicate `GclBound` (§4b-bis), i.e. through
*"the `Gcl`-carrier bound of §3 at the explicit `ρ`-range"*, so that the target is instantiated from
either carrier-bound package by a one-line wrapper.  The available wrappers are

| wrapper | input |
|---|---|
| `MdlSliceLowpassG_of_cruxOnly` | `A6.ChainPartSqFunPos` **alone** — the shortest route, no maximal socket |
| `MdlSliceLowpassG_of_socketsPos` | `A7Hi2.SupPiece` + `A6.PosChainPiece` (the **safe** endgame) |
| `MdlSliceLowpassG_of_sockets` | `A7Hi2.SupPiece` + `A7Hi2.ChainPiece` |
| `MdlSliceLowpassG_of_cruxPos` | `A6.ChainPartSqFunPos` (the sharp but **unconditioned** crux) |
| `MdlSliceLowpassG_of_chainPartSqFun` | `A6.ChainPartSqFun` (the unrestricted crux) |

All five are sorry-free and axiom-clean, and each of them has the target's statement verbatim.
`MdlSliceLowpassG_of_cruxOnly` uses the tree's own proved reduction
`Work.KMTAreas.A7Hi.lowpassVarGRepOfChainPartSqFunPos` (via the new module
`Submission/Work/KMTPlan/A6/GclVarEstimateExplicitCrux.lean`), which eliminates the values-supremum
by telescoping + `A7.kmtProj_lp_bound_uniform`; hence `SupPiece` is *not* needed on that route.

Two warnings, both relevant to whoever supplies the input (details in §4c-bis and
`NOTES_MdlSliceLowpassG_SESSION4.md`):

* the crux `ChainPartSqFunPos` is stated for **every** `f : ℤ → ℂ` with no integrability
  hypothesis; the owning area (`A7HiRep/chainPartSqFunPosMemLp.lean`) records that the
  unconditioned form is unsafe and that the repaired form carries
  `MeasureTheory.MemLp f p MeasureTheory.Measure.count`.  Prefer the socket routes above;
* the **`r = 2` endpoint** of the chain bound is FALSE (KMT, "Unboundedness of quadratic
  variation"; `NOTES_quadratic_variation_r2_FALSE.md`), so no route may reduce the chain socket to
  its `r = 2` instance — the `r > 2` hypothesis of `ChainPiece`/`PosChainPiece` is essential.

## Status (session 5)

* The **`MemLp`-guarded endgame is wired**: `Work.KMTPlan.A6.ChainPartSqFunPosMemLp`
  (`Submission/Work/KMTPlan/A6/CruxMemLpDefs.lean`, the statement of the owning area's canonical
  obligation `Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp`) plus the proved assembly
  `Work.KMTPlan.A6.lowpassVarGRepMemLp` and the wrapper
  `Work.KMTPlan.A6.gclVarEstimateExplicitMemLp`
  (`Submission/Work/KMTPlan/A6/GclVarEstimateExplicitMemLp.lean`) give
  `MdlSliceLowpassG_of_cruxMemLp : ChainPartSqFunPosMemLp → <the target>`.  So the **safe**
  endgame is now also a one-liner, and it is the one a successor should use:
  `MdlSliceLowpassG_of_cruxMemLp <ChainPartSqFunPosMemLp> P hd C₀ hC₀ R hR`.
* `Work.KMTPlan.A6.gclVarEstimateExplicitCrux`'s ~600-line assembly is now factored as
  `gclVarEstimateExplicitOfLow (P) (hd) (hLowpass)`, with `hLowpass` (the low-pass variational
  estimate) as its only deep input, and `gclVarEstimateExplicitCrux` a one-line wrapper — so any
  further form of the crux costs one line, not another copy.
* **Workspace hazard (fixed on this side only).**  `Submission/Work/KMTAreas/A7Hi2/
  sieveRouteUnconditional.lean` is stale w.r.t. `Submission/Work/A7Hi2/SieveAssembly.lean`
  (changed 2026-10-01 07:28 to a form whose constant is uniform in `l₁, m₀`) and no longer
  elaborates, which breaks `KMTPlan/A6/PieceBoundedH/sliceGBound` and with it this module.  Two
  local, sorry-free modules restore the build:
  `Submission/Work/KMTPlan/A6/PieceBoundedH/SieveUncondLocal.lean` (the same theorems against the
  current `SieveAssembly`) and `Submission/Work/KMTPlan/A6/PieceBoundedH/sliceGBoundLocal.lean`
  (a copy of `sliceGBound.lean` with the broken import swapped and every declaration renamed with a
  `Loc` suffix, so that it cannot clash if the original is repaired).  This module now uses
  `…PieceBoundedH.sliceGBoundLoc`.  The fix at source is two `obtain`/`have` lines — see
  `NOTES_MdlSliceLowpassG_SESSION5.md` §0 — after which both local modules can be deleted.

## Where the statement sits in the workspace

`MdlSliceLowpassG` is the `(k₂,j₂) = (0,0)` case of the `g`-side packet estimate
`Work.KMTPlan.A6.MdlSliceLinGOne`, and the single input of the sibling `MdlSliceLinG`
(`Submission/Work/KMTPlan/A6/MdlSliceLinG.lean`, which imports this module) in its low-pass case.
It is *not* reachable from the arithmetic-free material alone: the `T^{≤l₂}` carrier with `l₂ ≥ 1`
is exactly the low-pass family whose variational estimate is the workspace's documented central
open crux (see `NOTES_A7Hi2_chainPieceClean_SESSION.md`, `NOTES_A7Hi_LowpassMaximal_SESSION*.md`
and `NOTES_KMTPlan_A6_LowpassVarGHi_SESSION1.md`).  The crux appears here in the two *isolated*
sockets

* `Work.KMTAreas.A7Hi2.SupPiece`  (the Ionescu--Wainger lacunary **maximal** bound;
  equivalently `A7Hi2.IwMaximalLac` = Tao's uniform IW lacunary maximal inequality), and
* `Work.KMTAreas.A7Hi2.ChainPieceCanonical`  (the Lepingle/JSW **chain** step in its canonical
  `∃ Cρ` form),

and every other ingredient of the reduction below is *proved and axiom-clean* in the tree
(`A7Hi2.lowpassVarG_of_pieces`/`dyadicLowpass`, `A7Hi.lacunaryBumpLowpassClipBoundG`,
`A7Hi.lacunaryBumpBadPartBoundG`, `A7Hi.lacunaryBumpVarEstimate_assemblyG`,
`A7G.lowpassVarZeroHeight`, `A7Hi.DilVar`, `A7G.plainDevVarG`, `MdlGL2Bound`,
`A7Hi2.sqFunBound`).
## The reduction (verified against the tree's `#print axioms`; every step below is a *proved*
lemma except the two sockets)

Write `u_n = Tle ρ l₂ ψ_n (mdlG ρ P (uScale ρ L) l₂ g)`, `ψ_n = varphitildeNt P d ⌊a n⌋ 0 t`,
`d = P.natDegree`, `L = max (max l₁ l₂) k₁`.

1. `mdlCore ρ C₀ a l₁ l₂ k₁ 0 n ↔ core ρ C₀ l₁ l₂ k₁ 0 a n` (`mdlCore_iff_core`), so the model
   slice is the `k₂ = 0` instance of the A7 large-scale carrier family.
2. `Tle ρ l₂ ψ_n (mdlG ρ P (uScale ρ L) l₂ g) = Tm ρ l₂ ψ_n g`
   (`Work.KMTPlan.A6.Tle_mdlG_eq_Tm`, PROVED): the `≤ l₂` multiplier applied to the *narrow*
   exact-height projection is the exact-height multiplier applied to `g`.  Its hypotheses are
   `NonAliasing (-(d·uScale ρ L)) (iwArithFreqs ρ l₂)` and `SupportedInArc` of the bump in
   `realArc (-(d·uScale ρ L) - 1)`; the second is `supportedInArc_varphitildeNtj` (PROVED, from
   `mainRegime ρ k₁ 0 ⌊a n⌋`: `2·uScale ρ (max k₁ 0) ≤ logN ⌊a n⌋` together with
   `max l₁ l₂ ≤ heightScale C₀ ⌊a n⌋` and `ρ ≤ 1/(2C₀)`), the first is the *non-aliasing
   dichotomy*: for `L ≥ B(ρ)` it holds by `nonAliasing_of_size` /
   `A6.nonAliasingDiffFreqsR`-type size comparisons (`2^{-d·uScale ρ L} ≤ 2^{-2 l₂ - 2}` since
   `uScale ρ L = ⌊2^{2ρL}⌋` dominates `2L/d` once `L ≥ B(ρ)`), while for `L < B(ρ)` the pair
   `(l₂, uScale ρ L)` is *bounded by a constant depending on `ρ` alone*.
3. For `l₂ ≥ 1`, `Tm ρ l₂ = Tex ρ l₂` (`tm_eq_tex`, PROVED, from
   `diffFreqs_eq_iwArithFreqsNew`).  Hence the family is the A7 `Gcl`-family at `(k₂,t) = (0,t)`:
   `Gcl ρ P C₀ a l₁ l₂ k₁ 0 t g n = 1_{core n}·Tex ρ l₂ ψ_n g`.
4. The `Gcl`-bound is
   `Work.KMTAreas.A7Hi.lacunaryBumpVarEstimate_assemblyG P hd hLowpass hLowClip hBadPart C₀ hC₀ R hR`
   (PROVED, axiom-clean) with
   * `hLowClip := lacunaryBumpLowpassClipBoundG …` (PROVED),
   * `hBadPart := lacunaryBumpBadPartBoundG P d hd le_rfl …` (PROVED), and
   * `hLowpass := Work.KMTAreas.A7Hi2.lowpassVarG_of_pieces hSup hChain hSq d (by omega)`, the
     only place where the two sockets enter (`hSq` is the PROVED `A7Hi2.sqFunBound`).  It yields
     the conclusion with `A = 4`, `ρ₀ = min 1 (1/(2C₀))`; since `C₀ ≥ 1` this is exactly the
     range `ρ ≤ 1/(2C₀)` of the target.
5. `l₂ = 0`: the `Gcl`-family vanishes (`Tex ρ 0 = 0`), and the family is the *modulated*
   height-`0` low-pass family `Tle ρ 0 ψ_n (mdlG … ) = Tm ρ 0 ψ_n g = Tle ρ 0 ψ_n g`
   (`tm_zero_eq_tle_zero`, PROVED).  This case is handled by the arithmetic-free machinery
   (`A7Hi.DilVar` for the fixed-shift dilate family `n ↦ E_{N_n}g(· + t^d N_n^d)` and
   `A7G.plainDevVarG`/`A7Hi.TmModulatedLipschitz` for the `O(1/N_n)` deviation of the shift
   `PevalR P (N_n t)/N_n^d` from `t^d`), all PROVED and axiom-clean.
6. the `ℓ²`-bound of the model input `mdlG` at height `0` (the crude `eLpNorm_piExact_le` at the
   single exact-height frequency `(ℚ/ℤ)_{≤0} = {0}`, factor `4`), and the `(1+l₂)²`/`(1+l₂)`
   losses of the A7 assembly are absorbed by
   `lossWeight A ρ l₁ l₂ k₁ 0 = (1+lmaxR)^A·2^{Aρ·lmaxR}` for `A` large (the target's `∃A`
   is quantified *after* `C₀`, so it may depend on `C₀`; note `lmaxR ≥ l₂`).

**The two sockets are the only deep inputs**, and they are the workspace's documented central
open problem (Tao's uniform Ionescu--Wainger lacunary maximal inequality and the
Lepingle/Jones--Seeger--Wright chain step).  See `NOTES_A7Hi2_chainPieceClean_SESSION.md` §4 for
the route to `ChainPieceCanonical`, and `NOTES_A7Hi_LowpassMaximal_SESSION*.md` for the maximal
half, whose arithmetic input `Work.KMTAreas.iwEvenMultiplierGapUniform` (= `AreaA1`, PROVED in
the tree) is now available.

**A cleaner route for step 2 which avoids the non-aliasing dichotomy** (and which is the route a
successor should implement): use the height decomposition of the carrier,
`Tle ρ l₂ ψ = Tle ρ 0 ψ + Σ_{1 ≤ l' ≤ l₂} Tex ρ l' ψ` (proved by telescoping from
`Work.KMTAreas.A7.Tex_eq_Tle_sub_of_bounded` / `iwConv_sdiff_of_bounded` for bounded input, and
from `Work.KMTPlan.A6.Tm_add_of_memLp` for `ℓ²` input), then bound the `l' ≥ 1` terms by the
`Gcl`-bound of §3 applied at level `l'` (legitimate because `mdlCore l₂ ⇒ core l'` for
`l' ≤ l₂`, `mdlCore_imp_core`), and the `l' = 0` term — the *modulated height-`0`* family
`Tle ρ 0 ψ_n` — by the arithmetic-free machinery (`A7Hi.DilVar` for the fixed-shift dilate
`n ↦ E_{N_n}g(· + t^d N_n^d)`, plus `A7G.plainDevVarG`/`A7Hi.TmModulatedLipschitz` for the
`O(1/N_n)` deviation of `PevalR P (N_n t)/N_n^d` from `t^d`).  This removes the constraint
`L ≥ B(ρ)` and with it the bounded-`L` regime, at the cost of the two obligations just named.

## Status of the three obligations (this session)

* the two sockets `SupPiece`, `ChainPiece` are **delegated** (paths
  `Submission/Work/KMTPlan/A6/SupPieceProvable.lean`,
  `Submission/Work/KMTPlan/A6/ChainPieceProvable.lean`); their deep arithmetic input
  (`Work.KMTAreas.iwEvenMultiplierGapUniform` = `AreaA1`) is already PROVED in the tree;
* the height-`0` carrier bound is stated at `Submission/Work/KMTPlan/A6/MdlSliceLowpassGZero.lean`
  (same shape as the target with `Tle ρ l₂` replaced by `Tle ρ 0` and an arbitrary input `h`);
  note that the `t`-frozen modulation `PevalR P (⌊a n⌋ t)` makes this a genuinely non-trivial
  (non-conventional) shift, so it must *not* be assumed to follow from `DilVar` alone when
  `lc P · t^deg > 1`;
* the height decomposition `Tle_eq_Tle_zero_add_sum_tex` is PROVED here (for `ℓ²` input), as is the
  `ℓ²` set-additivity `iwConv_sdiff_of_memLp` and the `Tex`/`Tle` difference
  `tex_eq_tle_sub_of_memLp` it rests on;
* the remaining assembly (the `l'`-sum, the `mdlCore l₂ ⇒ mdlCore l'` monotonicity, the
  `lossWeight`/`(1+l₂)²` absorption and the `eLpNorm` bookkeeping) is mechanical and is the
  immediate follow-up once the three inputs land.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Tle_piExact_eq_convOp
import Submission.Work.KMTAreas.A7.MixedGSideAux
import Submission.Work.KMTAreas.A7Hi.LinVarG
import Submission.Work.KMTPlan.A6.HeightZeroSliceBound
import Submission.Work.KMTPlan.A6.PieceBoundedH.sliceGBoundLocal
import Submission.Work.KMTPlan.A6.eLpNorm_piExact_le
import Submission.Work.KMTPlan.A6.varphitildeNtjPointwise
import Submission.Work.KMTAreas.A7G.lowpassAlphaTransferG

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7 Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## §1.  Structural identifications -/

/-- **At positive height the A6 `Tm`-carrier of the model tuple agrees with the `Tex`-carrier of
the A7 large-scale assembly.**  `diffFreqs ρ l` is the exact-height frequency set
`iwArithFreqsNew ρ l` as soon as `l ≠ 0`. -/
theorem tm_eq_tex {ρ : ℝ} {l : ℕ} (hl : l ≠ 0) (φ : ℝ → ℂ) :
    Tm ρ l φ = Tex ρ l φ := by
  show Work.Analysis.IWMultiplier.iwConv (diffFreqs ρ l) (Work.Analysis.IonescuWainger.periodize φ)
      = Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize φ)
  rw [diffFreqs_eq_iwArithFreqsNew hl]

/-- At height `0` the A6 `Tm`-carrier is the plain (height-`≤ 0`) window multiplier. -/
theorem tm_zero_eq_tle_zero {ρ : ℝ} (φ : ℝ → ℂ) : Tm ρ 0 φ = Tle ρ 0 φ := by
  show Work.Analysis.IWMultiplier.iwConv (diffFreqs ρ 0) (Work.Analysis.IonescuWainger.periodize φ)
      = Work.Analysis.IWMultiplier.iwConv (iwArithFreqs ρ 0) (Work.Analysis.IonescuWainger.periodize φ)
  simp only [diffFreqs]
  norm_num

/-! ## §1b.  The `ℓ²` form of the set-additivity of the Ionescu--Wainger multiplier

`Work.KMTAreas.A7.iwConv_sdiff_of_bounded` states the set-additivity
`iwConv (A \ B) Φ f = iwConv A Φ f - iwConv B Φ f` for *bounded* `f`; the height decomposition of
the `Tle` carrier needed by the reduction (see the module docstring) requires it for `f ∈ ℓ²`,
which is where the summands `κ j * f (n - j)` are `ℓ² * ℓ² ⊆ ℓ¹`
(`Work.KMTPlan.A6.summable_mul_of_summable_normSq`).  The proof is the `ℓ¹` proof with that
substitution. -/

/-- **`ℓ²`-input set-additivity of `iwConv`:** for `B ⊆ A`,
`iwConv (A \ B) Φ f = iwConv A Φ f - iwConv B Φ f` whenever the two symbols are integrable,
their kernels are square-summable and `f ∈ ℓ²(ℤ)`. -/
theorem iwConv_sdiff_of_memLp {A B : Finset Work.Analysis.IonescuWainger.Circle} (hsub : B ⊆ A)
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hA : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Φ)
      Work.Analysis.IonescuWainger.circleMeasure)
    (hB : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet B Φ)
      Work.Analysis.IonescuWainger.circleMeasure)
    {f : ℤ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hκA : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖ ^ 2)
    (hκB : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet B Φ) j‖ ^ 2) :
    Work.Analysis.IWMultiplier.iwConv (A \ B) Φ f
      = Work.Analysis.IWMultiplier.iwConv A Φ f
        - Work.Analysis.IWMultiplier.iwConv B Φ f := by
  have hfmem : Memℓp f (2 : ℝ≥0∞) := memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  have hf2 : Summable fun j : ℤ => ‖f j‖ ^ 2 := by
    have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hfmem
    simpa [Real.rpow_natCast] using h
  funext n
  simp only [Work.Analysis.IWMultiplier.iwConv_apply, Pi.sub_apply]
  have hz : Summable fun j : ℤ => ‖f (n - j)‖ ^ 2 := summable_kernel_translate hf2 n
  have hs1 : Summable fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j • f (n - j) :=
    summable_smul_of_summable_normSq hκA hz
  have hs2 : Summable fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet B Φ) j • f (n - j) :=
    summable_smul_of_summable_normSq hκB hz
  rw [← hs1.tsum_sub hs2]
  refine tsum_congr (fun j => ?_)
  rw [Work.KMTAreas.A7.iwKernel_iwSymbolSet_sdiff hsub hA hB j, sub_smul]

/-- **The exact-height multiplier is a difference of two height-`≤` multipliers, for `ℓ²` input.** -/
theorem tex_eq_tle_sub_of_memLp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} (hl : 1 ≤ l)
    {φ : ℝ → ℂ} (hA : MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) Work.Analysis.IonescuWainger.circleMeasure)
    (hB : MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ (l - 1))
        (Work.Analysis.IonescuWainger.periodize φ)) Work.Analysis.IonescuWainger.circleMeasure)
    {f : ℤ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hκA : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) j‖ ^ 2)
    (hκB : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ (l - 1))
        (Work.Analysis.IonescuWainger.periodize φ)) j‖ ^ 2) :
    Tex ρ l φ f = Tle ρ l φ f - Tle ρ (l - 1) φ f := by
  have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
    iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
  have hmain := iwConv_sdiff_of_memLp hsub hA hB hf hκA hκB
  simpa only [Tex, Tle, Work.Analysis.IonescuWainger.iwArithFreqsNew] using hmain

/-- **The height decomposition of the `Tle` carrier, for `ℓ²` input**: the height-`≤ l` window
multiplier is the height-`0` one plus the exact-height pieces,
`Tle ρ l φ = Tle ρ 0 φ + Σ_{1 ≤ l' ≤ l} Tex ρ l' φ`.  Proved by telescoping
`tex_eq_tle_sub_of_memLp`. -/
theorem Tle_eq_Tle_zero_add_sum_tex {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) {φ : ℝ → ℂ}
    {f : ℤ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hInt : ∀ l' : ℕ, l' ≤ l → MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ l')
        (Work.Analysis.IonescuWainger.periodize φ)) Work.Analysis.IonescuWainger.circleMeasure)
    (hκ : ∀ l' : ℕ, l' ≤ l → Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ l')
        (Work.Analysis.IonescuWainger.periodize φ)) j‖ ^ 2) :
    Tle ρ l φ f = Tle ρ 0 φ f + ∑ l' ∈ Finset.Icc 1 l, Tex ρ l' φ f := by
  induction l with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega : ¬ (1 ≤ 0))]
      simp
  | succ l ih =>
      have hl : 1 ≤ l + 1 := Nat.succ_le_succ (Nat.zero_le l)
      have hkill : l + 1 ∉ Finset.Icc 1 l := by
        simp only [Finset.mem_Icc, not_and, not_le]
        intro _
        omega
      have hsub : ∀ l' : ℕ, l' ≤ l → l' ≤ l + 1 := fun l' h => le_trans h (Nat.le_succ l)
      have hstep : Tex ρ (l + 1) φ f = Tle ρ (l + 1) φ f - Tle ρ l φ f := by
        have h := tex_eq_tle_sub_of_memLp ρ hρ hρ1 hl (hInt (l + 1) le_rfl) (hInt l (Nat.le_succ l))
          hf (hκ (l + 1) le_rfl) (hκ l (Nat.le_succ l))
        rwa [Nat.succ_sub_one] at h
      have hstep' : Tle ρ (l + 1) φ f = Tle ρ l φ f + Tex ρ (l + 1) φ f := by
        rw [hstep]; abel
      have hIcc : Finset.Icc 1 (l + 1) = insert (l + 1) (Finset.Icc 1 l) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hstep', ih (fun l' h => hInt l' (hsub l' h)) (fun l' h => hκ l' (hsub l' h)), hIcc,
        Finset.sum_insert hkill]
      abel

/-- **The `≤ l₂` multiplier applied to the narrow exact-height projection `mdlG` collapses to the
exact-height multiplier `Tm` applied to `g`.**

This is a *copy* (renamed with a prime) of `Work.KMTPlan.A6.Tle_mdlG_eq_Tm` of
`MdlSliceLinGOne.lean`, taken so that this module does not depend on that module: while the
assembly below was being written, `MdlSliceLinGOne.lean` was transiently broken by a duplicate
declaration of `Work.KMTPlan.A6.iwConv_eq_multiplierOf` in two of its own imports
(`ssuCollapse.lean` and `tsum_eLpNorm_sq_iwConv_le.lean`), which made every module importing it
un-buildable.  The proof is the original one-liner. -/
theorem Tle_mdlG_eq_Tm' (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (u l₂ : ℕ)
    (φ : ℝ → ℂ)
    (hc : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) ≤ 1 / 2)
    {g : ℤ → ℂ} (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing
      (-((P.natDegree : ℤ) * (u : ℤ))) (iwArithFreqs ρ l₂))
    (hφmem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (u : ℤ)) - 1) (Work.Analysis.IonescuWainger.periodize φ)) :
    Tle ρ l₂ φ (mdlG ρ P u l₂ g) = Tm ρ l₂ φ g := by
  rw [mdlG, Tle_piExact_eq_convOp ρ hρ hρ1 l₂ (-((P.natDegree : ℤ) * (u : ℤ))) φ hc hg hnA
      hφmem hΦ, mae_Tm_eq_convOp_maeKer]

/-! ## §3.  The target -/

/-! ## §3.  The `Gcl`-carrier bound from the two sockets

`Work.KMTAreas.A7Hi.lacunaryBumpVarEstimate_assemblyG` (PROVED, axiom-clean) reduces the
`Gcl`-carrier estimate to the low-pass estimate `hLowpass`, the clipped low-pass estimate
`hLowClip` and the poor-scales estimate `hBadPart`; the last two are PROVED
(`lacunaryBumpLowpassClipBoundG`, `lacunaryBumpBadPartBoundG`), and `hLowpass` is
`Work.KMTAreas.A7Hi2.lowpassVarG_of_pieces` (PROVED) applied to the two sockets
`SupPiece` and `ChainPiece` together with the PROVED `sqFunBound` (which is `SqPiece`).
Nothing else is used. -/

/-! ## §4.  The model slice is the `Gcl` family (on the core, for `l₂ ≥ 1`)

This is the bridge that converts the A7 large-scale assembly's `Gcl`-carrier bound (§3) into the
model slice of the target.  Its hypotheses are the *narrowness* of the `mdlG` window and the
non-aliasing of the exact-height frequencies, which come from `mdlCore` in the regime
`L = max (max l₁ l₂) k₁ ≥ B(ρ)` (see the module docstring); in the complementary bounded-`L`
regime the pair `(l₂, uScale ρ L)` is bounded by a `ρ`-dependent constant and the functional
calculus identity has to be replaced by the height decomposition
`Tle ρ l₂ = Tle ρ 0 + Σ_{1 ≤ l' ≤ l₂}Tex ρ l'`. -/

/-- **The model slice is the exact-height multiplier at positive height.**  Under the narrowness
of the `mdlG` window (`hc`), the non-aliasing of the exact-height frequencies (`hnA`), the support
(`hΦ`) and integrability (`hφmem`) of the bump, the `≤ l₂` multiplier applied to the narrow
exact-height input `mdlG` is the exact-height multiplier applied to `g` (`Tle_mdlG_eq_Tm`), and at
`l₂ ≠ 0` that is `Tex` (`tm_eq_tex`). -/
theorem slice_eq_tex {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (u l₂ : ℕ)
    (φ : ℝ → ℂ) (hc : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) ≤ 1 / 2)
    {g : ℤ → ℂ} (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing
      (-((P.natDegree : ℤ) * (u : ℤ))) (iwArithFreqs ρ l₂))
    (hφmem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (u : ℤ)) - 1) (Work.Analysis.IonescuWainger.periodize φ))
    (hl₂ : l₂ ≠ 0) :
    Tle ρ l₂ φ (mdlG ρ P u l₂ g) = Tex ρ l₂ φ g := by
  rw [Tle_mdlG_eq_Tm' ρ hρ hρ1 P u l₂ φ hc hg hnA hφmem hΦ, tm_eq_tex hl₂ φ]

/-- The `j₂ = 0` modified bump is the modulated bump of §6. -/
theorem varphitildeNtj_zero_apply (P : Polynomial ℤ) (N : ℕ) (t : ℝ) :
    Work.KMTPlan.A6.varphitildeNtj P N 0 0 t
      = varphitildeNt P P.natDegree N 0 t :=
  Work.KMTPlan.A6.varphitildeNtj_zero P N 0 t

/-- **`mdlCore` implies the `core` of the `Gcl` carrier** (with `k₂ = 0`). -/
theorem mdlCore_imp_core {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ n : ℕ}
    (h : mdlCore ρ C₀ a l₁ l₂ k₁ 0 n) : core ρ C₀ l₁ l₂ k₁ 0 a n :=
  (mdlCore_iff_core ρ C₀ a l₁ l₂ k₁ 0 n).mp h

/-- **Monotonicity of `mdlCore` in the arithmetic height.**  `mdlCore ρ C₀ a l₁ l₂ k₁ 0 n` only
becomes stronger as `l₂` grows: the index set is monotone in the first height, the large-scale cut
`splitCut ρ (max (max l₁ l₂) (max k₁ 0))` is monotone in the same maximum, and the main regime does
not depend on `l₂`.  This is what lets the height decomposition of the carrier be fed into the
`Gcl`-carrier bound at every level `l' ≤ l₂` (the `Gcl` family is clipped at `core ρ C₀ l₁ l' k₁ 0`,
i.e. at the level-`l'` instance of the same predicate). -/
theorem mdlCore_mono_height {ρ : ℝ} (hρ : 0 ≤ ρ) {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ n : ℕ}
    {l' : ℕ} (hl : l' ≤ l₂) (h : mdlCore ρ C₀ a l₁ l₂ k₁ 0 n) :
    mdlCore ρ C₀ a l₁ l' k₁ 0 n := by
  obtain ⟨hin, hcut, hmain⟩ := h
  refine ⟨⟨?_, hin.2.1, hin.2.2⟩, ?_, hmain⟩
  · have hmax : max (l₁ : ℤ) (l' : ℤ) ≤ max (l₁ : ℤ) (l₂ : ℤ) := by
      refine max_le_max le_rfl ?_
      exact_mod_cast hl
    exact le_trans hmax hin.1
  · have hmax : max (max l₁ l') (max k₁ 0) ≤ max (max l₁ l₂) (max k₁ 0) :=
      max_le_max (max_le_max le_rfl hl) le_rfl
    exact lt_of_le_of_lt (Work.KMTAreas.A7.splitCut_mono ρ hρ hmax) hcut

/-! ## §4b.  Elementary helpers for the reduction

The sibling modules in which the following facts are proved (`A6/MdlSliceLinGOne`,
`A7Hi/LossWeightMono`) cannot be imported here: a duplicate declaration
`Work.KMTPlan.A6.iwConv_eq_multiplierOf` in two of their own imports makes them un-importable in
this closure.  The copies below are self-contained. -/

/-- The arcs `ℝ_{≤k}` are monotone in `k`. -/
theorem realArc_mono' {k k' : ℤ} (hk : k ≤ k') :
    Work.Analysis.IonescuWainger.realArc k ⊆ Work.Analysis.IonescuWainger.realArc k' := by
  intro θ hθ
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hθ ⊢
  have h : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k' := zpow_le_zpow_right₀ (by norm_num) hk
  exact ⟨le_trans (neg_le_neg h) hθ.1, le_trans hθ.2 h⟩

/-- **The non-aliasing condition is monotone in the scale.**  Shrinking the window arc `ℝ_{≤k}` can
only make the major arcs `α + ℝ_{≤k}` more separated. -/
theorem nonAliasing_mono_scale' {k k' : ℤ} (hk : k ≤ k')
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    (h : Work.Analysis.IonescuWainger.NonAliasing k' A) :
    Work.Analysis.IonescuWainger.NonAliasing k A :=
  fun α hα β hβ θ hθ θ' hθ' he =>
    h α hα β hβ θ (realArc_mono' hk hθ) θ' (realArc_mono' hk hθ') he

/-- `eLpNorm f 2 count ≠ ⊤` gives `f ∈ ℓ²(ℤ)`. -/
theorem memLp_two_count_of_ne_top'' {f : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count ≠ ⊤) :
    MeasureTheory.MemLp f 2 MeasureTheory.Measure.count :=
  MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr h)

/-- The loss weight is monotone in its exponent (for `ρ ≥ 0`). -/
theorem lossWeight_mono_exp {A A' ρ : ℝ} (hAA' : A ≤ A') (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight A' ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    have h : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]; omega
    exact_mod_cast h
  rw [Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lossWeight]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith) hAA'
  · refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA' hρ) hL

/-- **The modified `g`-bump of the model is supported in the narrow arc of the window of `mdlG`**:
if the main regime `k₂ + 2u ≤ Log N` holds, then `φ̃_{N,k₂,j₂}` is supported in `ℝ_{≤-(d·u)-1}`. -/
theorem supportedInArc_varphitildeNtj' (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (N k₂ : ℕ) (j₂ : ℤ) (t : ℝ) {u : ℕ} (hu : 1 ≤ u)
    (hmain : k₂ + 2 * u ≤ (Work.Analysis.EndVar.logN N).toNat) :
    Work.Analysis.IonescuWainger.SupportedInArc (-((P.natDegree : ℤ) * (u : ℤ)) - 1)
      (Work.Analysis.IonescuWainger.periodize (varphitildeNtj P N k₂ j₂ t)) := by
  refine supportedInArc_periodize_of_arc fun x hx => ?_
  have hvt : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t x ≠ 0 := by
    intro h0
    exact hx (by simp only [varphitildeNtj, h0, mul_zero])
  have hsupp := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k₂ t x hvt
  have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
    have : 1 ≤ P.natDegree := by omega
    exact_mod_cast this
  have hu1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hlogN : (k₂ : ℤ) + 2 * (u : ℤ) ≤ Work.Analysis.EndVar.logN N := by
    have h0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := by
      simp only [Work.Analysis.EndVar.logN]; exact Int.natCast_nonneg _
    have h1 : ((Work.Analysis.EndVar.logN N).toNat : ℤ) = Work.Analysis.EndVar.logN N :=
      Int.toNat_of_nonneg h0
    omega
  have hexp : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤
      (((-((P.natDegree : ℤ) * (u : ℤ)) - 1 : ℤ)) : ℝ) := by
    have h3 : (1 : ℤ) ≤ (P.natDegree : ℤ) * (u : ℤ) :=
      le_trans (by omega) (mul_le_mul hd1 hu1 (by omega) (by omega))
    have h4 : (P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN N) ≤
        -((P.natDegree : ℤ) * (u : ℤ)) - 1 := by
      have h5 : (P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN N)
          ≤ (P.natDegree : ℤ) * (-(2 * (u : ℤ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by omega)
        omega
      nlinarith [h5, h3]
    calc (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
        = (((P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN N) : ℤ) : ℝ) := by
          push_cast; ring
      _ ≤ (((-((P.natDegree : ℤ) * (u : ℤ)) - 1 : ℤ)) : ℝ) := by exact_mod_cast h4
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  have hle : |x| ≤ (2 : ℝ) ^ (((-((P.natDegree : ℤ) * (u : ℤ)) - 1 : ℤ)) : ℝ) :=
    le_trans hsupp (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  rw [Real.rpow_intCast] at hle
  exact ⟨neg_le_of_abs_le hle, le_of_abs_le hle⟩

/-- The periodisation of the modified `g`-bump is essentially bounded. -/
theorem memLp_periodize_varphitildeNtj' (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (N k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (hk : k₂ ≠ 0 ∨ 0 ≤ j₂) (hN : 1 ≤ N)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (hj : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize
      (varphitildeNtj P N k₂ j₂ t)) ⊤ Work.Analysis.IonescuWainger.circleMeasure := by
  obtain ⟨hbd, -⟩ := varphitildeNtjPointwise P hd
  obtain ⟨Cb, hCbpos, hCb⟩ := hbd
  obtain ⟨S, hSpos, hS⟩ := varphitildeNtj_bounds P N k₂ j₂ hk
  obtain ⟨hScd, hScs, -, -⟩ := hS t ht
  obtain ⟨R, hR⟩ := Work.KMTAreas.A7.exists_abs_le_of_hasCompactSupport hScs
  refine Work.Analysis.IonescuWainger.memLp_periodize hScd.continuous.measurable
    (R := max R 0) (C := Cb) (le_max_right R 0) ?_ ?_
  · intro x hx
    exact hR x (le_of_lt (lt_of_le_of_lt (le_max_left R 0) hx))
  · intro x
    have hnot : ¬(k₂ = 0 ∧ j₂ = -1) := by
      rintro ⟨h1, h2⟩
      rcases hk with h | h
      · exact h h1
      · omega
    exact hCb N k₂ j₂ t hj hnot hN x

/-! ## §4b-bis.  The `Gcl`-carrier bound as a hypothesis

The good regime of §4c only needs the `Gcl`-carrier estimate of §3 *at the explicit `ρ`-range*
`ρ ≤ 1`, `ρ ≤ 1/(2C₀)` (which is exactly the range of the target).  That estimate is produced by
two different packages, with identical conclusion shapes:

* `Work.KMTPlan.A6.gclVarEstimateExplicitLs` (from the two sockets `SupPiece`, `ChainPiece`);
* `Work.KMTPlan.A6.gclVarEstimateExplicitLsPos` (from `SupPiece` and the **positively normalised**
  socket `PosChainPiece` — the normalisation `2 ≤ Cρ₀`, which is the only one the tree's inputs
  can supply).

Factoring the §4c proof through the abstract `GclBound` below lets the target be instantiated from
either package by a one-line wrapper, and lets the sharp (`Pos`) route be taken without duplicating
the ~270 lines of the dichotomy. -/

/-- **The `Gcl`-carrier bound** (the conclusion shape of `gclVarEstimateExplicitLs` /
`gclVarEstimateExplicitLsPos`): for every `C₀ ≥ 1`, `2 < r`, there are `A ≥ 0` and, for every
`ρ ∈ (0, 1] ∩ (0, 1/(2C₀)]`, a constant family `C : ℝ≥0 → ℝ≥0` with

`‖V^r_n (Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f)‖_{ℓᵖ} ≤ (C Λ) · ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) · ‖f‖_{ℓᵖ}`

uniformly in the lacunary family `a`, the base `l₁ l₂ k₁ k₂`, `t ∈ [1/2,1]` and `f`. -/
abbrev GclBound (P : Polynomial ℤ) : Prop :=
  ∀ (C₀ : ℕ), 1 ≤ C₀ → ∀ (r : NNReal), 2 < r → ∃ A : ℝ, 0 ≤ A ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ρ ≤ 1 / (2 * (C₀ : ℝ)) →
      ∀ (p : ENNReal), 1 < p → p < ⊤ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x))
            p MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count

/-! ## §4c.  The target modulo the two sockets

At a fixed `ρ` the proof splits on the non-aliasing of the exact-height frequencies of the model
level `l₂` at the window `2^{-d·uScale ρ L}` of the model input `mdlG`,
`L = max (max l₁ l₂) (max k₁ 0) = lcL l₁ l₂ k₁ 0`:

* **good regime** (`l₂ ≠ 0`, `NonAliasing` holds): the functional-calculus collapse `slice_eq_tex`
  turns the masked model family into the `Gcl`-family, whose bound with the *explicit* `ρ`-range
  `ρ ≤ 1`, `ρ ≤ 1/(2C₀)` is `gclVarEstimateExplicitLs`, the two sockets being its only inputs;
* **bad regime** (`l₂ = 0`, or `¬ NonAliasing`, which by `lcL_le_of_not_nonAliasing` forces
  `lcL l₁ l₂ k₁ 0 ≤ D(ρ)`, hence bounded height): the *bounded-height packet estimate*
  `Work.KMTPlan.A6.PieceBoundedH.sliceGBound` (PROVED, axiom-clean) bounds the whole family with a
  constant depending only on `(ρ, Λ)`; the case `l₂ = 0` is the PROVED height-`0` slice
  `Work.KMTPlan.A6.HeightZeroSliceBound` (with the model input replaced by `g` through the
  functional-calculus collapse, and the two-sided `ℓ²`-bound of the input obtained from the crude
  `Work.KMTPlan.A6.eLpNorm_piExact_le_of_two_pow_le_half` at the single frequency `{(0)}`).

The bounded-height route replaces the `ballVarBound` input of the packet `PktMdlSliceLowpassG`
(which cannot be imported here). -/
theorem MdlSliceLowpassG_of_gcl (hgcl : ∀ (P : Polynomial ℤ), 2 ≤ P.natDegree → GclBound P)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ)
    (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))),
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ : ℕ) (t : ℝ) (g : ℤ → ℂ),
            PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            t ∈ Set.Icc (1 / 2 : ℝ) 1 →
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ =>
                  if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
                    Work.KMTAreas.A7.Tle ρ l₂
                      (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t)
                      (Work.KMTPlan.A6.mdlG ρ P
                        (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g) x
                  else 0)) 2 MeasureTheory.Measure.count
              ≤ ENNReal.ofReal C * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ 0) *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨A_G, hA_G0, H_G⟩ := hgcl P hd C₀ hC₀ R hR
  obtain ⟨A_h, hA_h0, H_h⟩ := HeightZeroSliceBound P hd C₀ hC₀ R hR
  have hAGE : A_G ≤ max (max A_G 4) A_h := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA4 : (4 : ℝ) ≤ max (max A_G 4) A_h := le_trans (le_max_right _ _) (le_max_left _ _)
  have hAh : A_h ≤ max (max A_G 4) A_h := le_max_right _ _
  have hAmax0 : (0 : ℝ) ≤ max (max A_G 4) A_h := le_trans hA_G0 hAGE
  refine ⟨max (max A_G 4) A_h, hAmax0, ?_⟩
  intro Λ hΛ ρ hρ hρ1 hρC
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  obtain ⟨C_G, H_Gρ⟩ := H_G ρ hρ hρ1 hρC 2 (by norm_num) (by norm_num)
  obtain ⟨C_h, hC_hpos, H_hρ⟩ := H_h Λ hΛ ρ hρ hρ1 hρC
  -- the non-aliasing threshold of the bad regime
  obtain ⟨Cna, hCnapos, hsize0⟩ := nonAliasing_of_size ρ hρ hρ1
  have hsize : ∀ (l : ℕ) (K : ℤ),
      (K : ℝ) + Cna * (2 : ℝ) ^ (ρ * (l : ℝ)) < 0 →
        Work.Analysis.IonescuWainger.NonAliasing K
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) := by
    intro l K hK
    refine Work.KMTAreas.A7.NonAliasing_of_subset (hsize0 l l K ?_) Finset.subset_union_left
    simpa using hK
  set D : ℕ := ⌈Real.logb 2 Cna / ρ⌉₊ + 1 with hDdef
  -- the bounded-height packet constant
  obtain ⟨K_bad, hK_bad⟩ :=
    Work.KMTPlan.A6.PieceBoundedH.sliceGBoundLoc P hd R hR C₀ hC₀ ρ hρ hρ1 D
  -- the total constant
  have hCG_le : (C_G Λ : ℝ) ≤ max (max (C_G Λ : ℝ) (K_bad Λ : ℝ)) (C_h * 4 + 1) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hKb_le : (K_bad Λ : ℝ) ≤ max (max (C_G Λ : ℝ) (K_bad Λ : ℝ)) (C_h * 4 + 1) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hChCm_le : C_h * 4 ≤ max (max (C_G Λ : ℝ) (K_bad Λ : ℝ)) (C_h * 4 + 1) :=
    le_trans (le_add_of_nonneg_right (by norm_num)) (le_max_right _ _)
  have hCpos : (0 : ℝ) < max (max (C_G Λ : ℝ) (K_bad Λ : ℝ)) (C_h * 4 + 1) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < C_h * 4 + 1) (le_max_right _ _)
  refine ⟨max (max (C_G Λ : ℝ) (K_bad Λ : ℝ)) (C_h * 4 + 1), hCpos, ?_⟩
  intro a l₁ l₂ k₁ t g ha ha1 ht
  have ham : Monotone a := Work.KMTAreas.A7Hi2.monotone_of_lacunary hΛ ha ha1
  -- the narrowness `2^{-d·u} ≤ 1/2` of the window of `mdlG`
  have hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0)) :=
    Work.KMTAreas.A7.one_le_uScale ρ hρ0 _
  have hc : (2 : ℝ) ^ (-((P.natDegree : ℤ) *
      ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ))) ≤ 1 / 2 := by
    have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
      have : 1 ≤ P.natDegree := by omega
      exact_mod_cast this
    have hu1z : (1 : ℤ) ≤
        ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ) := by
      exact_mod_cast hu1
    have hdu : (1 : ℤ) ≤ (P.natDegree : ℤ) *
        ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ) := by
      calc (1 : ℤ) = 1 * 1 := by ring
        _ ≤ _ := mul_le_mul hd1 hu1z (by omega) (by omega)
    calc (2 : ℝ) ^ (-((P.natDegree : ℤ) *
            ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ)))
        ≤ (2 : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  by_cases hgood : l₂ ≠ 0 ∧ Work.Analysis.IonescuWainger.NonAliasing
      (-((P.natDegree : ℤ) *
        ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
  · -- ## good regime: the collapse to the `Gcl`-family and the socket-based `Gcl`-bound
    obtain ⟨hl₂0, hNA⟩ := hgood
    by_cases hgtop : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
    · rw [hgtop, ENNReal.mul_top]
      · exact le_top
      · refine mul_ne_zero ?_ ?_
        · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
        · exact ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one
            (Work.KMTAreas.A7Hi.assembly_one_le_lossWeight (c := max (max A_G 4) A_h) hAmax0 hρ0
              l₁ l₂ k₁ 0))
    · have hgmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count :=
        memLp_two_count_of_ne_top'' hgtop
      -- the pointwise identification with the `Gcl`-family
      have hfam : ∀ x : ℤ, (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
              Work.KMTAreas.A7.Tle ρ l₂
                (fun ξ : ℝ => varphitildeNtj P (Nat.floor (a n)) 0 0 t ξ)
                (Work.KMTPlan.A6.mdlG ρ P
                  (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g) x
            else 0)
          = fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ 0 t g n x := by
        intro x
        funext n
        by_cases hc0 : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
        · have hcore : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ 0 a n :=
            (Work.KMTPlan.A6.mdlCore_iff_core ρ C₀ a l₁ l₂ k₁ 0 n).mp hc0
          simp only [if_pos hc0, Work.KMTAreas.A7.Gcl, if_pos hcore]
          have hsupp : Work.Analysis.IonescuWainger.SupportedInArc
              (-((P.natDegree : ℤ) *
                ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ)) - 1)
              (Work.Analysis.IonescuWainger.periodize
                (varphitildeNtj P (Nat.floor (a n)) 0 0 t)) := by
            refine supportedInArc_varphitildeNtj' P hd (Nat.floor (a n)) 0 0 t hu1 ?_
            obtain ⟨-, hcut, -⟩ := hc0
            have hbig : 2 ^ (2 ^ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))))
                < Nat.floor (a n) := by
              have hsplit : Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ 0))
                  = 2 ^ (2 ^ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0)))) := by
                rw [Work.KMTAreas.A7.splitCut, Work.KMTAreas.A7.uScale]
              rw [← hsplit]
              exact hcut
            have hlog : 2 ^ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0)))
                ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
              have hlogN : Work.Analysis.EndVar.logN (Nat.floor (a n))
                  = ((Nat.log 2 (max (Nat.floor (a n)) 2) : ℕ) : ℤ) := rfl
              rw [hlogN, Int.toNat_natCast]
              calc 2 ^ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0)))
                  = Nat.log 2 (2 ^ (2 ^ (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ 0))))) :=
                    (Nat.log_pow (by norm_num : 1 < 2) _).symm
                _ ≤ Nat.log 2 (max (Nat.floor (a n)) 2) :=
                    Nat.log_mono_right (le_trans (le_of_lt hbig) (le_max_left _ _))
            have h2u : 2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0)))
                ≤ 2 ^ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) :=
              Nat.mul_le_pow (by norm_num : (2 : ℕ) ≠ 1) _
            omega
          have hmem : MeasureTheory.MemLp
              (Work.Analysis.IonescuWainger.periodize
                (varphitildeNtj P (Nat.floor (a n)) 0 0 t)) ⊤
              Work.Analysis.IonescuWainger.circleMeasure :=
            memLp_periodize_varphitildeNtj' P hd (Nat.floor (a n)) 0 0 t
              (Or.inr (by norm_num : (0 : ℤ) ≤ 0))
              ((Nat.one_le_floor_iff (a n)).mpr (ha1 n)) ht (by simp)
          have hsl := slice_eq_tex hρ hρ1 P
            (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂
            (varphitildeNtj P (Nat.floor (a n)) 0 0 t)
            hc hgmem hNA hmem hsupp hl₂0
          rw [Work.KMTPlan.A6.varphitildeNtj_zero] at hsl
          simp only [Work.KMTPlan.A6.varphitildeNtj_zero]
          exact congrFun hsl x
        · rw [if_neg hc0, Work.KMTAreas.A7.Gcl,
            if_neg (fun hh => hc0
              ((Work.KMTPlan.A6.mdlCore_iff_core ρ C₀ a l₁ l₂ k₁ 0 n).mpr hh))]
          simp
      have hfamL : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
                Work.KMTAreas.A7.Tle ρ l₂
                  (fun ξ : ℝ => varphitildeNtj P (Nat.floor (a n)) 0 0 t ξ)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g) x
              else 0))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ 0 t g n x)) := by
        funext x
        congr 1
        exact hfam x
      rw [hfamL]
      refine (H_Gρ a Λ l₁ l₂ k₁ 0 t g hΛ ha ha1 ht).trans ?_
      refine mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl
      · rw [← ENNReal.ofReal_coe_nnreal (p := C_G Λ)]
        exact ENNReal.ofReal_le_ofReal hCG_le
      · exact ENNReal.ofReal_le_ofReal (lossWeight_mono_exp hAGE hρ0 l₁ l₂ k₁ 0)
  · -- ## bad regime
    rcases Nat.eq_zero_or_pos l₂ with h0 | hpos
    · -- ## `l₂ = 0`: the height-`0` slice bound `HeightZeroSliceBound`
      subst h0
      have h1 := H_hρ a l₁ 0 k₁ t (Work.KMTPlan.A6.mdlG ρ P
        (Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) (max k₁ 0))) 0 g) ha ha1 ht
      have h2' : MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlG ρ P
            (Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) (max k₁ 0))) 0 g)
            2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal 4 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        have hpi := eLpNorm_piExact_le_of_two_pow_le_half ρ hρ hρ1 0
          (-((P.natDegree : ℤ) *
            ((Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) (max k₁ 0))) : ℤ))) hc g
        have hcard : (Work.KMTAreas.A7.diffFreqs ρ 0).card = 1 := by
          rw [show Work.KMTAreas.A7.diffFreqs ρ 0
              = Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 from rfl,
            Work.KMTAreas.A7.iwArithFreqs_zero]
          simp
        refine hpi.trans (le_of_eq ?_)
        rw [hcard, Nat.mul_one]
        norm_num
      refine (h1.trans (mul_le_mul' le_rfl h2')).trans ?_
      rw [show ENNReal.ofReal C_h
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A_h ρ l₁ 0 k₁ 0)
            * (ENNReal.ofReal 4 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
          = (ENNReal.ofReal C_h * ENNReal.ofReal 4)
            * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A_h ρ l₁ 0 k₁ 0)
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) from by ring,
        ← ENNReal.ofReal_mul hC_hpos.le, ← mul_assoc]
      exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hChCm_le)
        (ENNReal.ofReal_le_ofReal (lossWeight_mono_exp hAh hρ0 l₁ 0 k₁ 0))) le_rfl
    · -- ## `l₂ > 0` and `¬ NonAliasing`: bounded height, `sliceGBound`
      have hna' : ¬ Work.Analysis.IonescuWainger.NonAliasing
          (-((P.natDegree : ℤ) *
            ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := fun h => hgood ⟨by omega, h⟩
      have hna2 : ¬ Work.Analysis.IonescuWainger.NonAliasing
          (-(2 * ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
            ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
        intro hcon
        refine hna' (nonAliasing_mono_scale' (A := Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
          (k := -((P.natDegree : ℤ) *
            ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ)))
          (k' := -(2 * ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ))) ?_
          (Work.KMTAreas.A7.NonAliasing_of_subset hcon Finset.subset_union_right))
        have hd2 : (2 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
        have hu0 : (0 : ℤ) ≤
            ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) : ℤ) :=
          Int.natCast_nonneg _
        nlinarith
      have hD : Work.KMTPlan.A6.lcL l₁ l₂ k₁ 0 ≤ D :=
        lcL_le_of_not_nonAliasing ρ hρ hρ1 Cna hCnapos hsize l₁ l₂ k₁ 0 (by
          rw [show Work.KMTPlan.A6.lcL l₁ l₂ k₁ 0 = max (max l₁ l₂) (max k₁ 0) from rfl]
          exact hna2)
      have hbad := hK_bad a Λ l₁ l₂ k₁ 0 t g hΛ ha ha1 ht hD
      have hfamB : ∀ x : ℤ, (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
              Work.KMTAreas.A7.Tle ρ l₂
                (fun ξ : ℝ => varphitildeNtj P (Nat.floor (a n)) 0 0 t ξ)
                (Work.KMTPlan.A6.mdlG ρ P
                  (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g) x
            else 0)
          = fun n : ℕ => Work.KMTPlan.A6.PieceBoundedH.sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x := by
        intro x
        funext n
        by_cases hc0 : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
        · simp only [if_pos hc0, Work.KMTPlan.A6.PieceBoundedH.sliceG, if_pos hc0,
            Work.KMTPlan.A6.varphitildeNtj_zero, Work.KMTPlan.A6.lcL, Pi.zero_apply]
        · simp only [if_neg hc0, Work.KMTPlan.A6.PieceBoundedH.sliceG, if_neg hc0, Pi.zero_apply]
      have hfamBL : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
                Work.KMTAreas.A7.Tle ρ l₂
                  (fun ξ : ℝ => varphitildeNtj P (Nat.floor (a n)) 0 0 t ξ)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g) x
              else 0))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTPlan.A6.PieceBoundedH.sliceG ρ P C₀ a l₁ l₂ k₁ 0 t g n x)) := by
        funext x
        congr 1
        exact hfamB x
      rw [hfamBL]
      refine hbad.trans ?_
      refine mul_le_mul' ?_ le_rfl
      have hKne : (K_bad Λ : ENNReal) = ENNReal.ofReal ((K_bad Λ : ℝ)) :=
        (ENNReal.ofReal_coe_nnreal (p := K_bad Λ)).symm
      have hmul1 : ENNReal.ofReal ((K_bad Λ : ℝ)) * 1 = ENNReal.ofReal ((K_bad Λ : ℝ)) :=
        mul_one _
      rw [hKne, ← hmul1]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hKb_le) (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Work.KMTAreas.A7Hi.assembly_one_le_lossWeight
          hAmax0 hρ0 l₁ l₂ k₁ 0))

/-! ## §4c-bis.  The instantiations of §4c (the target from the sockets, and from the sharp crux)

`MdlSliceLowpassG_of_gcl` above is the whole dichotomy; the wrappers below differ only in which
package supplies the `Gcl`-carrier bound of §3.  **The target follows from any of them in one
line** the moment its input lands.

Two warnings, both recorded in `NOTES_MdlSliceLowpassG_SESSION4.md`:

* the sharp crux `ChainPartSqFunPos` is an **unconditioned** statement (`∀ f : ℤ → ℂ`, no
  integrability), and the area that owns it states
  (`A7HiRep/chainPartSqFunPosMemLp.lean`) that the unconditioned form is *unsafe* there and that the
  repaired form carries `MeasureTheory.MemLp f p MeasureTheory.Measure.count`.  The routes through
  `supPiece_of_cruxPos` / `posChainPiece_of_cruxPos` are therefore only usable if the unconditioned
  crux is true; the **safe** endgames are the two socket routes below (`SupPiece` and `ChainPiece`
  resp. `PosChainPiece` are ordinary inequalities that are `⊤` on both sides whenever `‖f‖_p = ⊤`,
  so the degeneracy cannot arise);
* the `r = 2` endpoint of the chain bound is **FALSE** (KMT, "Unboundedness of quadratic variation";
  see `NOTES_quadratic_variation_r2_FALSE.md`), so the chain socket must be taken with its genuine
  `r > 2` hypothesis — which is what `ChainPiece` / `PosChainPiece` do. -/

/-! ## §4c-ter.  The target from the crux **alone** (no maximal socket)

`Work.KMTPlan.A6.GclVarEstimateExplicitCrux` supplies the `Gcl`-carrier bound from the crux
`ChainPartSqFunPos` alone, via the tree's proved reduction
`Work.KMTAreas.A7Hi.lowpassVarGRepOfChainPartSqFunPos` (which eliminates the values-supremum by the
telescoping `V^r(walk) ≤ ‖T_0 f‖ + 2 chainPart r (walk)` plus the proved height-free single-scale
bound `A7.kmtProj_lp_bound_uniform`).  So the target closes from **one** input — the crux — with the
Ionescu–Wainger lacunary maximal socket `A7Hi2.SupPiece` not needed at all. -/

/-! ## §4c-quater.  The target from the **`MemLp`-guarded** crux (the safe route)

The crux `ChainPartSqFunPos` above quantifies over every `f : ℤ → ℂ` with no integrability
assumption, and the area that owns it states verbatim
(`Submission/Work/KMTAreas/A7HiRep/chainPartSqFunPosMemLp.lean`) that this unconditioned form is
*unsafe* — the repaired canonical obligation adds `MeasureTheory.MemLp f p MeasureTheory.Measure.count`
— and that no sixth copy of the unrepaired statement should be produced.

The repair is invisible at the level of this target: `Work.KMTPlan.A6.gclVarEstimateExplicitOfLow`
consumes its low-pass input at the *same* `∀ f : ℤ → ℂ` shape, and the input is applied to the very
`f` that appears on the right-hand side, so the dichotomy `eLpNorm f p = ⊤` (trivial) versus
`f ∈ ℓᵖ` (feed the guarded crux) leaves the conclusion untouched.  That is the content of the
proved assembly `Work.KMTPlan.A6.lowpassVarGRepMemLp`. -/

/-! ## §4d.  The two sockets from the canonical chain/square-function crux

The workspace's canonical open node is the chain/square-function crux

  `‖chainPart r (m ↦ lpf ρ l₁ m₀ m f)‖_{ℓᵖ} ≤ C ‖sqFun ρ l₁ m₀ f‖_{ℓᵖ}`

on the good major arcs, with `C` independent of `l₁, m₀` (statement: `Work.KMTAreas.A7HiRep.chainPartSqFun`;
sharp form carrying the hypothesis `2 ≤ Cρ₀`: `Work.KMTAreas.A7HiRep.chainPartSqFunPos`).  From it
both sockets of §3 follow through *proved* lemmas — the maximum via
`Work.KMTAreas.A7HiRep.supBoundOfLacunaryMax` (the Men'shov/lacunary-maximal piece from
`partMaxD ≤ chainPart`), the chain piece by the one-line comparison with `supPart + sqFun`.  The
derivations below are copies of `Work.KMTAreas.A7HiRep.lowpassVarGRepCrux`'s with the crux taken as
a *hypothesis*, so that this module's endgame does not depend on that (currently `sorry`-carrying)
module.

**Normalisation.**  The hypothesis `ChainPartSqFun` below quantifies over an *arbitrary* real
`Cρ₀` — the form the tree's assembly consumes (`Work.KMTAreas.A7Hi2.ChainPiece` also has an
arbitrary `Cρ₀`); it therefore contains the fully aliased corner `Cρ₀ ≤ 0`, which the paper's
`(lin-2)` does not need.  See `NOTES_MdlSliceLowpassG_SESSION3.md` §8 for the relation with the
sharp form `2 ≤ Cρ₀` and for the corner's status. -/

/-- **The canonical crux as a hypothesis** (the statement of
`Work.KMTAreas.A7HiRep.chainPartSqFun`): the chain part of the low-pass Ionescu--Wainger walk is
dominated by the band square function of its increments. -/
abbrev ChainPartSqFun : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Cρ₀ : ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count

/-- Two points of a sequence give a chain, so the jump `a K - a 0` is at most the chain part. -/
private lemma two_point_le_chainPart' {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) (K : ℕ) :
    ‖a K - a 0‖ₑ ≤ Work.KMTAreas.A7Hi.chainPart r a := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (r : ℝ) := by
      have h1 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    exact this.ne'
  refine le_iSup_of_le 1 ?_
  refine le_iSup_of_le (fun i : ℕ => if i = 0 then 0 else K) ?_
  refine le_iSup_of_le ?_ ?_
  · refine monotone_nat_of_le_succ fun i => ?_
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · have h1 : i ≠ 0 := h.ne'
      have h2 : i + 1 ≠ 0 := by omega
      simp only [h1, h2, if_false]
      exact le_rfl
  · have hval : (fun i : Fin 1 =>
          a ((fun i : ℕ => if i = 0 then 0 else K) (i + 1))
            - a ((fun i : ℕ => if i = 0 then 0 else K) i))
        = fun _ : Fin 1 => a K - a 0 := by
      funext i
      have hi : (i : ℕ) = 0 := by omega
      rw [hi]
      simp
    rw [hval]
    have h1' := Work.KMTAreas.A7.ofReal_norm_toLp r hr 1 (fun _ : Fin 1 => a K - a 0)
    rw [Fin.sum_univ_one] at h1'
    rw [h1', one_div]
    exact le_of_eq (ENNReal.rpow_rpow_inv hr0 _).symm

/-- The partial sums of the annuli are dominated by the chain part. -/
private lemma partialSum_le_chainPart' (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (K : ℕ) (x : ℤ) :
    ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ
      ≤ Work.KMTAreas.A7Hi.chainPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
  rw [Finset.sum_range_sub (fun i : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x) K]
  exact two_point_le_chainPart' (r := 3) (by norm_num)
    (fun i : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x) K

/-- **The Men'shov/lacunary maximal piece, from the crux.** -/
theorem lacunaryMaxOfChainPartSqFun' (h : ChainPartSqFun) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (Work.KMTAreas.A7HiRep.partMaxD ρ l₁ m₀ f)
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
                p MeasureTheory.Measure.count
            + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop
  obtain ⟨C, hC, hcrux⟩ := h ρ hρ hρ1 3 (by norm_num) p hp hptop 1
  refine ⟨1, by norm_num, C, hC, ?_⟩
  intro l₁ m₀ hgood f
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  have hpt : ∀ x : ℤ, Work.KMTAreas.A7HiRep.partMaxD ρ l₁ m₀ f x
      ≤ Work.KMTAreas.A7Hi.chainPart 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) :=
    fun x => iSup_le fun K => partialSum_le_chainPart' ρ l₁ m₀ f K x
  have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := Work.KMTAreas.A7HiRep.partMaxD ρ l₁ m₀ f)
    (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 3
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
    hpt hp0 hpT (μ := MeasureTheory.Measure.count)
  refine (hmono.trans (hcrux l₁ m₀ hgood f)).trans ?_
  exact le_add_of_nonneg_right bot_le

/-- **The chain socket, from the crux.** -/
theorem chainPieceOfChainPartSqFun' (h : ChainPartSqFun) :
    Work.KMTAreas.A7Hi2.ChainPiece := by
  intro ρ hρ hρ1 r hr p hp hptop Cρ₀
  obtain ⟨C, hC, hcrux⟩ := h ρ hρ hρ1 r hr p hp hptop Cρ₀
  refine ⟨C, hC, ?_⟩
  intro l₁ m₀ hgood f
  refine (hcrux l₁ m₀ hgood f).trans ?_
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left bot_le) bot_le

/-! ## §5.  The target -/

theorem MdlSliceLowpassG (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (R : NNReal) (hR : 2 < R) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))),
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ : ℕ) (t : ℝ) (g : ℤ → ℂ),
            PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            t ∈ Set.Icc (1 / 2 : ℝ) 1 →
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ =>
                  if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
                    Work.KMTAreas.A7.Tle ρ l₂
                      (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t)
                      (Work.KMTPlan.A6.mdlG ρ P
                        (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g) x
                  else 0)) 2 MeasureTheory.Measure.count
              ≤ ENNReal.ofReal C * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ 0) *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by sorry

end

end Work.KMTPlan.A6
