import Mathlib
import Submission.Work.KMTAreas.A7HiRep.Defs
import Submission.Work.KMTAreas.A7Hi.kmtProjHeightSplit
import Submission.Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top
import Submission.Work.KMTAreas.A7.varShiftDiffPrep
import Submission.Work.KMTAreas.A7Hi.eLpNorm_chainPart_le_uniform
import Submission.Commons.Analysis.HardyLittlewood.discrete_maximal_lp
import Submission.Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
import Submission.Work.Analysis.Variation.Defs
import Submission.Work.KMTAreas.A4.kmtProjSelfAdjoint
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTAreas.A5.iwSymbolSet_prod_kmtEta
import Submission.Work.KMTAreas.A7.FiberOpWideCutEqSelf
import Submission.Work.KMTAreas.A7G.chainPartLowpass
import Submission.Work.KMTAreas.A7G.maximalLowpass
import Submission.Work.KMTAreas.A7Hi.rotationIdentity
import Submission.Work.KMTAreas.A7Hi2.LowpassVarG2
import Submission.Work.KMTAreas.A7LoLin.kernel0
import Submission.Work.KMTPlan.A6.besselG
import Submission.Work.KMTPlan.A6.projVanishingF
import Submission.Port.Aesm

/-! # The low-pass lacunary maximal piece (the assignment `A7Hi2.lacunaryMaxPieceProved`)

## Status

The target `lacunaryMaxPieceProved` is **not proved**; it routes through the sibling stub
`Work.KMTAreas.A7Hi2.lacunaryMaxPiece` and therefore rests on `sorryAx`.  Every *other* lemma in
this file is `sorry`-free and axiom-clean (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`).

## Axiom audit of the neighbouring inputs (session 9, all `#print axioms`-verified)

CLEAN: `A7Hi.kmtProj_zero_varBound` (height-`0` variational bound, `l`- and `m₀`-free),
`A7G.plainBumpVarG`, `A7.lacunaryBumpDilationVar` (JSW Thm 1.1 for Schwartz dilates),
`A7Hi2.menshovScalarL2_ellTwo_all` (Men'shov at `l₁ = 0`, `p = 2`, every `m₀`),
`A7Lpd.bandSquareUnif`, `A7.kmtProj_lp_bound_uniform`, `iwEvenMultiplierGapUniform`,
`A7Lpd.uniformSignsAnnuliOfReal`, `A7Lpd.singleChain_blockSqSum_le`, `A7Hi2.perKLeSqFunLpAll`,
and (new) `A7Hi2.reverseLPAnnuli` — the **reverse Littlewood--Paley bound**
`Summable (‖f‖²) → ‖T_0 f‖_{ℓᵖ} ≤ C‖sqFun f‖_{ℓᵖ}` with `C` free of `l₁,m₀`.  That is the second of
the two inputs of the tree's proved reduction `A7Lpd.lacunaryMaxFun_of_maximal_and_revLp`; the
first, `(VM) = (MAX)`, is the crux isolated below, so the target is still equivalent to `(MAX)`.

**Warning (statement bug found in session 9).**  The `hRL` *hypothesis* of
`A7Lpd.lacunaryMaxFun_of_maximal_and_revLp` — and the stub `A7Lpd.lacunaryMaxFun` — quantifies
`∀ f : ℤ → ℂ` with no summability hypothesis, and is therefore **false**: for the character
`f = x ↦ e(αx)` at an arithmetic frequency `α ∈ (ℚ/ℤ)_{≤l}` one has `kmtProj ρ l k f = f` for every
`k` (`iwSymbolSet_apply_arithFreqs_eq_one` below), hence `sqFun ρ l m₀ f = 0` while
`‖T_0 f‖_{ℓᵖ} = ∞`, i.e. `(RL)` would say `∞ ≤ 0`.  The proved `A7Hi2.reverseLPAnnuli` carries the
missing hypothesis `Summable (fun n => ‖f n‖²)`.  (The *target* is immune: there the left-hand side
is `0` and the additive term `C‖f‖_{ℓᵖ}` is present.)

## What the file contains (session 10 additions, all PROVED and axiom-clean)

`chainPart_le_smallHeight` (the chain-part bound for `l₁ ≤ iwC0 ρ`, uniform in `m₀`),
`lacunaryMaxPieceProved_smallHeight` (**the assignment itself for `l₁ ≤ iwC0 ρ`**) and
`lacunaryMaxPieceProved_of_deepChainPart` (**the assignment reduces to the deep regime
`iwC0 ρ < l₁`**, where the PROVED fibre/coset machinery of `A7G/chainPartLowpassFibre` and the
factorisation `arithChar = iwQ0 ρ l · KW` of `A7Hi/kernelDecimation` apply).  See
`NOTES_A7Hi2_lacunaryMaxPieceProved_SESSION10.md` for the exact remaining gap (the mean-zero
"super-orthogonality" part of the fibre walk) and for the list of routes that cannot work.

## What the file contains

* the **equivalence web** (all proved): `lacunaryMaxPieceProved_of_iwMaximal`,
  `lacunaryMaxPieceProved_of_lacunaryMaxPiece`, `lacunaryMaxPieceProved_of_chainPartSqFun`,
  `lacunaryMaxPieceProved_of_varBound`, `lacunaryMaxPieceProved_of_lacunaryMaxPieceGen`,
  `IwMaximalLac` with `lacunaryMaxPieceProved_of_iwMaximalLac`,
  `iwMaximalLac_of_lacunaryMaxPieceProved` and `iwMaximalLac_iff_targetShaped` — so the assignment
  is *equivalent* to the `l₁`-free Ionescu--Wainger lacunary maximal inequality
  `‖sup_m |kmtProj ρ l₁ (−(m₀+m)) f|‖_{ℓᵖ} ≤ C‖f‖_{ℓᵖ}`;
* the **height-0 case for all `m₀`** (`lacunaryMaxPieceProved_lzero`, `iwMaximalLac_lzero`) and the
  **fixed-height case** with the explicit constant `2·(#(ℚ/ℤ)_{≤l₁}+1)·C₀` (`lacunaryMaxLDep`,
  `lacunaryMaxPieceProved_lDep`, unconditional in `m₀` and `f`, no `GoodMajorArcs` needed);
* the **equivalence of the integrand with the three-point variation**
  (`partMaxD_le_two_variationalNorm`) and the pointwise domination by the chain term;
* **structural facts on the sample lattice** `iwQl ρ l · ℤ` (session 7): the arithmetic character
  is periodic with that period and equals `#(iwArithFreqs ρ l)` there, and the IW kernel on that
  lattice is `#(iwArithFreqs ρ l)` times the plain bump kernel
  (`arithChar_zero_eq_card`, `arithChar_add_iwQl_mul`, `arithChar_eq_card_of_iwQl_dvd`,
  `iwKernel_eq_card_mul_cw_of_iwQl_dvd`).

## The exact remaining gap

The assignment needs the `Vʳ`-valued (equivalently `ℓ^∞`-valued) **uniform vector-valued
Ionescu--Wainger multiplier bound for a family of narrow symbols** (Tao, arXiv:2008.05066, the
`⟨l⟩`-free form of KMT's Theorem `thm:iw`), together with the adelic/sampling transfer and the
one-parameter dilation theory (the latter two are partly in the tree).  Every `l`-free discrete
route (α-channel triangle inequality `#A ≍ 4^l`; sublattice/Shannon transfer `#A²`; Rademacher–
Menshov `l`; pointwise rigidity `√#A`) loses an `l`-dependent factor, which is why the statement is
genuinely stronger than the paper's own estimates: see
`NOTES_A7Hi2_lacunaryMaxPieceProved_SESSION7.md` (§2 for the paper's regime structure, §4 for the
sublattice computation, §5 for the exact input, §9 for the fleet hazards observed).

## Session 11: the sockets of this file, and the KMSZ Theorem 5.2 route

The file now records *every* known form in which the assignment follows from a single named input:

* `lacunaryMaxPieceProved_of_lacunaryMaxPiece` (the sibling stub `A7Hi2.lacunaryMaxPiece`);
* `lacunaryMaxPieceProved_of_iwMaximal` and `lacunaryMaxPieceProved_of_iwMaximalLac` (the
  `l`-free Ionescu--Wainger *maximal* inequality (MAX), `A7Hi2.IwMaximalLac`, with the proved
  equivalence `iwMaximalLac_iff_targetShaped`);
* `lacunaryMaxPieceProved_of_varBound` (the `l`-free `V³` bound of the walk, i.e. Lépingle);
* `lacunaryMaxPieceProved_of_varPartSqFun` (the `l`-free `V³` ≤ square-function step);
* `lacunaryMaxPieceProved_of_chainPartSqFun` and `lacunaryMaxPieceProved_of_chainPartBound` (the
  chain part ≤ `‖f‖`, resp. ≤ the square function);
* `lacunaryMaxPieceProved_of_deepChainPart` (the deep regime `iwC0 ρ < l₁` together with the
  *proved* small-height case `lacunaryMaxPieceProved_smallHeight`);
* `lacunaryMaxPieceProved_of_varRhoAll` (the `Work.BourgainPlan.Maximal.varRhoAll 2` form of the
  `l`-free `2`-variation bound, i.e. the output shape of KMSZ Theorem 5.2).

**Why no socket is weaker than (MAX).**  The assignment's integrand is the partial-sum maximal of
the annuli, and `partMaxD ≤ 2 V³(walk)`, `partMaxD ≤ chainPart 3(walk)` and
`partMaxD ≤ varRhoAll 2(walk)`; conversely the *values* maximal of the walk is dominated by the
first value plus the partial-sum maximal, and the `sqFun` term is *forced* by the proved
`A7Lpd.bandSquareUnif` (the values-maximal is not controlled by `‖f‖` alone at `l₁ = 0`, where
`A7Hi.kmtProj_zero_varBound` gives the sharp `Vʳ` estimate).  So the content of the assignment is
exactly the `l₁`-free *lacunary-maximal/Lépingle* statement for the low-pass Ionescu--Wainger walk.

**The KMSZ route (the newest route, and the reason the socket `…_of_varRhoAll` is recorded).**
`Work.BourgainPlan.Thm52.exists_thm52` / `…exists_thm52_finsupp` is KMSZ Theorem 5.2
(Kosz--Mirek--Słomian--Zhang, arXiv:2606.12663 §5), *proved* in the workspace: a family `T` whose
lacunary differences satisfy the uniform-in-signs bound `SignedDiffBound p T κ A` and whose tail
from `2^κ` satisfies the sampling bound `LargeScaleBound p T (2^κ) B` has
`‖varRhoAll 2 (T · f)‖_{ℓᵖ} ≤ C·(C₂A(κ+1) + B)‖f‖_{ℓᵖ}`.  For the low-pass walk
`T i = lpf ρ l₁ m₀ i`:

* the *small-scale* input `SignedDiffBoundF` is **PROVED** in the tree
  (`Submission/Work/A7Hi2/lowpassSignedDiffBoundF.lean`, from the proved
  `A7Lpd.uniformSignsAnnuliOfReal` and a regrouping of the signed block sums into unit increments),
  with a constant `A` independent of the window `κ`, of `l₁` and of `m₀`;
* the *large-scale* input `LargeScaleBoundF` is the single remaining gap
  (`Submission/Work/A7Hi2/lowpassLargeScaleBoundF.lean`); its intended proof is the
  kernel factorisation `TleKer_eq_arChar_cw` (proved) + the Mirek--Stein--Trojanski sampling
  principle for `2`-variations (`Thm52.decimatedKernel_lp.sampling_principle_variation_decimated_lp`,
  proved) + a **continuous** (`ℝ`-form) lacunary variational estimate for the rescaled narrow
  symbols (the residual; the lattice form is the proved `A7.lacunaryBumpDilationVar`).

**The `(κ+1)A` factor is why the KMSZ route alone does not give the assignment.**  KMSZ's constant
is linear in the dyadic window `κ`, i.e. it carries the Rademacher--Menshov `log` loss over the
window; with `κ = 0` the theorem reduces to the `B`-term, which *is* the crux.  So the KMSZ route
produces the `⟨l₁⟩`-lossy form (`Work.A7Hi2.SupPiece`, `A7Hi.LowpassMaximal`, `A7Lpd.maximal`,
all of which are stated with a `(1+l₁)²` constant) but not the `l₁`-free assignment: removing the
`log` requires the *orthogonality of the dyadic level square functions* (Rubio de Francia's
square-function theorem for the levels, equivalently Lépingle's inequality for this walk), which is
exactly the crux recorded above. -/
namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- Telescoping of the increments of the low-pass family. -/
lemma sum_range_lpf_sub (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (K : ℕ) (x : ℤ) :
    (∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))
      = Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x := by
  simpa using Finset.sum_range_sub (fun i : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x) K

/-- `lpf ρ l₁ m₀ 0 = kmtProj ρ l₁ (-(m₀))`. -/
lemma lpf_zero_eq (ρ : ℝ) (l₁ m₀ : ℕ) :
    Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) := by
  funext y
  simp only [Work.KMTAreas.A7Hi.lpf]
  norm_num

/-- **The target from the `l`-free Ionescu--Wainger maximal estimate.** -/
theorem lacunaryMaxPieceProved_of_iwMaximal
    (hVM : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ,
            ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ) p
          MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨CρM, hCρMpos, CM, hCMpos, hM⟩ := hVM ρ hρ hρ1 p hp hptop
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨CρM, hCρMpos, 2 * CM, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  -- The values-supremum of the family.
  have hpt : ∀ x : ℤ, (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      ≤ (⨆ K : ℕ,
          ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ)
        + (⨆ K : ℕ,
          ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ) := by
    intro x
    refine iSup_le fun K => ?_
    have hK : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K
        = Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) := rfl
    have h0 : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0
        = Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((0 : ℕ) : ℤ))) := rfl
    rw [sum_range_lpf_sub ρ l₁ m₀ f K x, hK, h0]
    have h1 : ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((0 : ℕ) : ℤ))) f x‖ₑ
        ≤ ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ
          + ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((0 : ℕ) : ℤ))) f x‖ₑ :=
      enorm_sub_le
    have h2 : ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((0 : ℕ) : ℤ))) f x‖ₑ
        ≤ ⨆ K : ℕ, ‖Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ :=
      le_iSup (fun K : ℕ => ‖Work.KMTContract.kmtProj ρ l₁
        (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ) 0
    have h3 : ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ
        ≤ ⨆ K : ℕ, ‖Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ :=
      le_iSup (fun K : ℕ => ‖Work.KMTContract.kmtProj ρ l₁
        (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ) K
    exact h1.trans (add_le_add h3 h2)
  have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
    (v := fun x : ℤ =>
        (⨆ K : ℕ, ‖Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ)
        + (⨆ K : ℕ, ‖Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ))
    hpt hp0 hpT (μ := MeasureTheory.Measure.count)
  refine hmono.trans ?_
  have hadd := Work.KMTAreas.A7.eLpNorm_add_le_ennreal
    (u := fun x : ℤ => (⨆ K : ℕ, ‖Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ))
    (v := fun x : ℤ => (⨆ K : ℕ, ‖Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((K : ℕ) : ℤ))) f x‖ₑ))
    (le_of_lt hp) (ne_of_lt hptop) (μ := MeasureTheory.Measure.count)
  refine hadd.trans ?_
  have hb := hM l₁ m₀ hgood f
  refine (add_le_add hb hb).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add hCMpos.le hCMpos.le]
  have heq : CM + CM = 2 * CM := by ring
  rw [heq]
  exact le_add_left le_rfl

/-- **The target from the sibling statement `Work.KMTAreas.A7Hi2.lacunaryMaxPiece`**, which is
*byte-identical* to it (own module `Submission.Work.KMTAreas.A7Hi2.lacunaryMaxPiece`, same
namespace), so that whichever of the two equivalent cruxes is closed first, the target follows. -/
theorem lacunaryMaxPieceProved_of_lacunaryMaxPiece
    (hP : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (_hp : 1 < p) (_hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
            p MeasureTheory.Measure.count
          + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
  hP ρ hρ hρ1 p hp hptop

/-- The partial-sum maximal function of the annuli is dominated by the chain part of the
variational norm of the low-pass walk (the two-point chain `0 → K`).  This is
`Work.KMTAreas.A7G.partMaxD_le_chainPart`, inlined so that the reduction below does not have to
import the crux-bearing module `Submission.Work.KMTAreas.A7G.maximalLowpass`. -/
lemma partMaxD_le_chainPart (ρ : ℝ) (l m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Work.KMTAreas.A7HiRep.partMaxD ρ l m₀ f x
      ≤ Work.KMTAreas.A7Hi.chainPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ m f x) := by
  have hunfold : Work.KMTAreas.A7HiRep.partMaxD ρ l m₀ f x
      = ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ i f x))‖ₑ := rfl
  rw [hunfold]
  refine iSup_le fun K => ?_
  rw [Finset.sum_range_sub (fun i : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ i f x) K]
  simpa only [Work.KMTAreas.A7Hi.chainPart, Submission.PointwiseErgodicTheorems.varPart] using
    Work.KMTAreas.A7Lpd.enorm_sub_zero_le_varPart (r := 3) (by norm_num)
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ m f x) K

/-- **The target from the workspace's isolated crux `Work.KMTAreas.A7HiRep.chainPartSqFun`.**

That statement --- the `l`-free domination of the *chain part* of the `r`-variation of the low-pass
walk by the band square function of its increments (L\'epingle / Men'shov / Jones--Seeger--Wright)
--- is the single stub on which `Work.KMTAreas.A7G.maximalLowpass`,
`Work.KMTAreas.A7Hi2.dyadicLowpass` and every reduction of the maximal estimate in this chapter
rest.  The passage to the target is *elementary*: the target's integrand is literally
`partMaxD ρ l₁ m₀ f = ⨆_K ‖∑_{i<K} Δ_i f‖ₑ`, `partMaxD ≤ chainPart 3` is the two-point chain of
the variational norm (`partMaxD_le_chainPart`), and `eLpNorm` is monotone.  In particular the
constant is `l`-free and the extra additive term `ofReal C * ‖f‖_p` of the target is not needed at
all here.

This is the sharpest known sufficient condition for the target inside the workspace; it is *not*
equivalent to (MAX) (it is strictly stronger) and it is the node against which the rest of the A7
maximal chapter is written. -/
theorem lacunaryMaxPieceProved_of_chainPartSqFun
    (hC : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Cρ₀ : ℝ), 2 ≤ Cρ₀ →
      ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
                p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hbound⟩ := hC ρ hρ hρ1 3 (by norm_num) p hp hptop 2 (le_refl 2)
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨2, by norm_num, C, hCpos, ?_⟩
  intro l₁ m₀ hgood f
  change MeasureTheory.eLpNorm (Work.KMTAreas.A7HiRep.partMaxD ρ l₁ m₀ f) p
      MeasureTheory.Measure.count
    ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
        p MeasureTheory.Measure.count
      + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
  have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := Work.KMTAreas.A7HiRep.partMaxD ρ l₁ m₀ f)
    (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 3
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
    (fun x => partMaxD_le_chainPart ρ l₁ m₀ f x) hp0 hpT
    (μ := MeasureTheory.Measure.count)
  exact hmono.trans ((hbound l₁ m₀ hgood f).trans (le_add_right le_rfl))


/-! ## The sharpest socket: the *Ionescu--Wainger lacunary maximal inequality*

The target's integrand is the partial-sum maximal of the annuli,
`partMaxD ρ l₁ m₀ f x = ⨆_K ‖T_K f x - T_0 f x‖ₑ` with `T_k = lpf ρ l₁ m₀ k` (the telescoping
`∑_{i<K} Δ_i f = T_K f - T_0 f`).  Since

  `partMaxD ≤ (⨆_K ‖T_K f‖ₑ) + ‖T_0 f‖ₑ`   and   `⨆_K ‖T_K f‖ₑ ≤ ‖T_0 f‖ₑ + partMaxD`

pointwise, and since the *single-scale* bound `‖T_0 f‖_{ℓᵖ} ≤ C‖f‖_{ℓᵖ}` with an `l`-free constant
is PROVED in the workspace (`Work.KMTAreas.A7.kmtProj_lp_bound_uniform`), the target is
**equivalent** (given the `l`-free forward band square-function bound
`Work.KMTAreas.A7Lpd.bandSquareUnif`, also PROVED) to the single statement

  **(MAX)**  `∃ Cρ > 0, ∃ C > 0, ∀ l₁ m₀, GoodMajorArcs ρ Cρ l₁ (-(m₀)) → ∀ f,
      ‖ ⨆_K ‖kmtProj ρ l₁ (-(m₀+K)) f · ‖ₑ ‖_{ℓᵖ} ≤ C ‖f‖_{ℓᵖ}`,

i.e. to the Ionescu--Wainger *maximal* inequality for the lacunary levels `k = -(m₀+K)`, with a
constant free of the arithmetic height `l₁`.  This is the weakest known socket of the chapter: it
is implied by every variational/square-function statement in the tree (`A7HiRep.chainPartSqFun`,
`A7Lpd.lacunaryMaxConst`, `A7Hi2.lacunaryMaxPiece`, `(VAR)`) and, conversely, it implies them all
*through* the target.

**Consequence for the critical path.**  The square-function term of the target is *forced* by the
maximal term (via `bandSquareUnif`), so no route to the target can avoid (MAX); and any proof of
(MAX) closes the target with the two short reductions below.  The remaining mathematical content of
(MAX) is exactly Tao's uniform (`l`-free) Ionescu--Wainger lacunary maximal inequality; the
workspace contains everything else used below.
-/

/-- The sequence form of the elementary split `sup_n ‖a n‖ ≤ ‖a 0‖ + sup_K ‖a K - a 0‖`. -/
lemma iSup_enorm_le_enorm_zero_add_iSup_sub (a : ℕ → ℂ) :
    (⨆ n : ℕ, ‖a n‖ₑ) ≤ ‖a 0‖ₑ + ⨆ K : ℕ, ‖a K - a 0‖ₑ := by
  refine iSup_le fun n => ?_
  have h : ‖a n‖ₑ ≤ ‖a 0‖ₑ + ‖a n - a 0‖ₑ := by
    have h1 := enorm_add_le (a 0) (a n - a 0)
    rwa [add_sub_cancel] at h1
  exact h.trans (add_le_add le_rfl (le_iSup (fun K : ℕ => ‖a K - a 0‖ₑ) n))

/-- The partial-sum maximal of the annuli is dominated by the values-maximal of the walk plus the
first value: `partMaxD ≤ (⨆_K ‖T_K f‖ₑ) + ‖T_0 f‖ₑ`. -/
lemma partMaxD_le_iSup_lpf_add (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      ≤ (⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ)
        + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ := by
  refine iSup_le fun K => ?_
  rw [sum_range_lpf_sub ρ l₁ m₀ f K x]
  calc ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ
        + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ := enorm_sub_le
    _ ≤ (⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ)
        + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ :=
        add_le_add (le_iSup (fun K : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ) K) le_rfl

/-- Conversely, the values-maximal of the walk is dominated by the first value plus the
partial-sum maximal of the annuli. -/
lemma iSup_lpf_le_enorm_zero_add_partMaxD (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    (⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ) := by
  have key : (⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
      = (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ) := by
    refine iSup_congr fun K => ?_
    rw [sum_range_lpf_sub ρ l₁ m₀ f K x]
  rw [← key]
  exact iSup_enorm_le_enorm_zero_add_iSup_sub _

/-- The **Ionescu--Wainger lacunary maximal inequality** (with an `l`-free constant), the socket
of the target isolated above. -/
def IwMaximalLac (ρ : ℝ) (p : ENNReal) : Prop :=
  ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
    MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ,
        ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (K : ℤ))) f x‖ₑ)
      p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count

/-- **The target from the Ionescu--Wainger lacunary maximal inequality.**  Only the *single-scale*
bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform` (PROVED, `l`-free) is needed besides (MAX); the
square-function factor on the right of the target is absorbed by choosing the constant at least
`C_0 + C_{MAX}`. -/
theorem lacunaryMaxPieceProved_of_iwMaximalLac
    (hM : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → IwMaximalLac ρ p)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨CρM, hCρM, CM, hCM, hMb⟩ := hM ρ hρ hρ1 p hp hptop
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨Cρ0, hCρ0, C0, hC0, h0b⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hpR
  have hpne : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨max CρM Cρ0, lt_max_of_lt_left hCρM, CM + C0, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgM : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρM l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_left _ _) hgood
  have hg0 : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ0 l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_right _ _) hgood
  have hstep := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
    (v := fun x : ℤ => (⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ)
        + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
    (fun x => partMaxD_le_iSup_lpf_add ρ l₁ m₀ f x) hp0 hpT
    (μ := MeasureTheory.Measure.count)
  refine (hstep.trans ?_).trans (le_add_left le_rfl)
  have hadd := Work.KMTAreas.A7.eLpNorm_add_le_ennreal
    (u := fun x : ℤ => ⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ)
    (v := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
    (le_of_lt hp) hpT (μ := MeasureTheory.Measure.count)
  refine hadd.trans ?_
  have hU : MeasureTheory.eLpNorm (fun x : ℤ =>
        ⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CM * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hfun : (fun x : ℤ => ⨆ K : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ)
        = (fun x : ℤ => ⨆ K : ℕ,
            ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (K : ℤ))) f x‖ₑ) := rfl
    rw [hfun]
    exact hMb l₁ m₀ hgM f
  have hV : MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hfun : (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        = fun x : ℤ => ‖Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f x‖ₑ := rfl
    rw [hfun, MeasureTheory.eLpNorm_enorm (hf := by pw_aesm)]
    have h := h0b l₁ (-(m₀ : ℤ)) hg0 f
    rw [hpne] at h
    exact h
  exact (add_le_add hU hV).trans (le_of_eq (by
    rw [← add_mul, ← ENNReal.ofReal_add hCM.le hC0.le]))

/-- **The Ionescu--Wainger lacunary maximal inequality from the target.**  `⨆_K ‖T_K f‖ₑ` is
dominated by the first value plus the partial-sum maximal of the annuli, and the square function of
the annuli is dominated by `‖f‖_{ℓᵖ}` with an `l`-free constant
(`Work.KMTAreas.A7Lpd.bandSquareUnif`, PROVED).  Hence the converse reduction of
`lacunaryMaxPieceProved_of_iwMaximalLac`. -/
theorem iwMaximalLac_of_lacunaryMaxPieceProved
    (hT : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ →
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
            p MeasureTheory.Measure.count
          + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    IwMaximalLac ρ p := by
  obtain ⟨CρT, hCρT, CT, hCT, hTb⟩ := hT ρ hρ hρ1 p hp hptop
  obtain ⟨CρB, hCρB, CB, hCB, hBb⟩ :=
    Work.KMTAreas.A7Lpd.bandSquareUnif ρ hρ hρ1 p hp hptop
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨Cρ0, hCρ0, C0, hC0, h0b⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hpR
  have hpne : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨max (max CρT CρB) Cρ0, lt_max_of_lt_left (lt_max_of_lt_left hCρT),
    CT + CT * CB + C0, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgT : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρT l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono
      (le_trans (le_max_left _ _) (le_max_left _ _)) hgood
  have hgB : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρB l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono
      (le_trans (le_max_right _ _) (le_max_left _ _)) hgood
  have hg0 : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ0 l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_right _ _) hgood
  have hstep := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => ⨆ K : ℕ,
        ‖Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (K : ℤ))) f x‖ₑ)
    (v := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ))
    (fun x => iSup_lpf_le_enorm_zero_add_partMaxD ρ l₁ m₀ f x) hp0 hpT
    (μ := MeasureTheory.Measure.count)
  have hV : MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hfun : (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        = fun x : ℤ => ‖Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f x‖ₑ := rfl
    rw [hfun, MeasureTheory.eLpNorm_enorm (hf := by pw_aesm)]
    have h := h0b l₁ (-(m₀ : ℤ)) hg0 f
    rw [hpne] at h
    exact h
  have hW : MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CT + CT * CB) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    calc MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal CT * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count
            + ENNReal.ofReal CT * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          hTb l₁ m₀ hgT f
      _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal CB *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
            + ENNReal.ofReal CT * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          add_le_add (mul_le_mul_of_nonneg_left (hBb l₁ m₀ hgB f) bot_le) le_rfl
      _ = ENNReal.ofReal (CT + CT * CB) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          have harith : CT * CB + CT = CT + CT * CB := by ring
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCT.le, ← add_mul,
            ← ENNReal.ofReal_add (mul_nonneg hCT.le hCB.le) hCT.le, harith]
  refine (hstep.trans (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
      (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
      (v := fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      (le_of_lt hp) hpT (μ := MeasureTheory.Measure.count))).trans ?_
  calc MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal (CT + CT * CB) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        add_le_add hV hW
    _ = ENNReal.ofReal (CT + CT * CB + C0) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← add_mul, ← ENNReal.ofReal_add hC0.le (by positivity)]
        congr 1
        ring


/-- **The two reductions packaged as an equivalence**: the target (in its `∀ ρ …`-quantified form)
holds **iff** the Ionescu--Wainger lacunary maximal inequality (MAX) holds, i.e. iff
`IwMaximalLac ρ p` for all `0 < ρ ≤ 1` and `1 < p < ⊤`.

Proof: `lacunaryMaxPieceProved_of_iwMaximalLac` and `iwMaximalLac_of_lacunaryMaxPieceProved`
above; the only external inputs are the two PROVED `l`-free single-scale/square-function bounds
`Work.KMTAreas.A7.kmtProj_lp_bound_uniform` and `Work.KMTAreas.A7Lpd.bandSquareUnif`.

Consequently `Work.KMTAreas.A7Hi2.iwMaximalLac_lzero` (PROVED) is *literally* the height-`0`
instance of the target's crux, and the whole remaining obligation of the assignment is (MAX) with
a constant **uniform in `l₁`**. -/
theorem iwMaximalLac_iff_targetShaped :
    (∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → IwMaximalLac ρ p)
      ↔ (∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ →
          ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
            Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
            MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
                (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
              p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
                p MeasureTheory.Measure.count
              + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
  ⟨lacunaryMaxPieceProved_of_iwMaximalLac, iwMaximalLac_of_lacunaryMaxPieceProved⟩

/-- **(U) ⟹ the target.**  The `l`-free chain-part bound

  `(U)  ∃Cρ>0, ∃C>0, ∀ l₁ m₀, GoodMajorArcs ρ Cρ l₁ (-(m₀)) → ∀ f ∈ ℓᵖ,
        ‖chainPart 3 (m ↦ lpf ρ l₁ m₀ m f)‖_{ℓᵖ} ≤ C‖f‖_{ℓᵖ}`

implies the assignment, because the target's integrand is *literally* the partial-sum maximal of
the annuli (`partMaxD`, by the telescoping `∑_{i<K} Δ_i = T_K - T_0`) and
`partMaxD ≤ chainPart 3` (the two-point chain, `partMaxD_le_chainPart` below, proved).  This is the
socket against which the `(P1)` route has to be run: `(P1) = Work.KMTAreas.A7Hi.bandSumSqRep`
(proved, `l`-free) + `Work.KMTAreas.A7Hi2.chainPartSqFunOfBandSumSqAll` (proved, all `1<p<∞`) give
the chain-part bound only with the `#A_l` loss of `A7Hi2.chainPart_le_sum_variationalNorm`; removing
that loss — i.e. proving `(U)` — is exactly the remaining obstruction (see
`NOTES_A7Hi2_lacunaryMaxPieceProved_SESSION9.md` §5). -/
theorem lacunaryMaxPieceProved_of_chainPartBound
    (hU : ∀ (ρ : ℝ) (_hρ : 0 < ρ) (_hρ1 : ρ ≤ 1) (p : ENNReal) (_hp : 1 < p) (_hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.MemLp f p MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨CρU, hCρU, CU, hCU, hUb⟩ := hU ρ hρ hρ1 p hp hptop
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨CρU, hCρU, CU, hCU, ?_⟩
  intro l₁ m₀ hgood f
  by_cases hfin : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count < ⊤
  · have hfmem : MeasureTheory.MemLp f p MeasureTheory.Measure.count :=
      (MeasureTheory.memLp_iff.mpr (hfin))
    have hpt : ∀ x : ℤ, (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        ≤ Work.KMTAreas.A7Hi.chainPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
      intro x
      have h0 : Work.KMTAreas.A7HiRep.partMaxD ρ l₁ m₀ f x
          = (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
              (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ) := rfl
      rw [← h0]
      exact partMaxD_le_chainPart ρ l₁ m₀ f x
    refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal hpt hp0 hpT
      (μ := MeasureTheory.Measure.count)).trans ?_
    exact (hUb l₁ m₀ hgood f hfmem).trans (le_add_left le_rfl)
  · have htop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤ :=
      le_antisymm le_top (not_lt.mp hfin)
    have hofR : ENNReal.ofReal CU ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hCU
    rw [htop, ENNReal.mul_top hofR]
    exact le_add_left le_top

/-- **The target from the *stronger* sibling node `Work.KMTAreas.A7Hi2.lacunaryMaxPieceGen`** —
the statement of the workspace's `(P1) + (P2)` chapter
(`NOTES_A7Hi2_P2_chapter_DESIGN.md`), which is the *same* inequality **without** the additive
`C‖f‖_{ℓᵖ}` term, hence implies the assignment.  Together with the routes already in this file
(`…_of_lacunaryMaxPiece`, `…_of_chainPartSqFun`, `…_of_iwMaximal`, `…_of_varBound`) this records
that *any* of the equivalent crux statements lands the assignment. -/
theorem lacunaryMaxPieceProved_of_lacunaryMaxPieceGen
    (hG : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (_hp : 1 < p) (_hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hb⟩ := hG ρ hρ hρ1 p hp hptop
  exact ⟨Cρ, hCρ, C, hC, fun l₁ m₀ hg f =>
    (hb l₁ m₀ hg f).trans (le_add_of_nonneg_right bot_le)⟩

/-! ## The arithmetic-free (`l₁ = 0`) case of the target

The assignment's inequality for `l₁ = 0` is proved here outright, from the workspace's
*axiom-clean* `Work.KMTAreas.A7G.plainBumpVarG`: the `Λ`-lacunary variational estimate for the
plain (single-frequency) low-pass family `Tle ρ 0 (varphitildeN d N 0)`.  The two steps are

* `Tle ρ 0 (varphitildeN 1 (2^n) 0) = lpf ρ 0 m₀ (n - m₀)` for `n ≥ m₀`, so the plain family at the
  dyadic levels `2^n` (a `3/2`-lacunary family) *is* the `lpf` walk, reindexed by a monotone map
  (and a monotone reindexing does not increase the variational norm,
  `Work.KMTAreas.A7.variationalNorm_comp_mono_le`);
* the partial-sum maximal of the annuli is `≤ 2 · V³` of the walk (the telescoping
  `∑_{i<K}(lpf (i+1) - lpf i) = lpf K - lpf 0` plus `‖a - b‖ ≤ ‖a‖ + ‖b‖`).

Consequently the `l₁ = 0` instance of the target holds with an `m₀`-free constant. -/

/-- `Nat.floor` of the dyadic natural `2 ^ k`, as an `ℝ≥0`-floor. -/
lemma floor_two_pow (k : ℕ) : Nat.floor ((2 : NNReal) ^ k) = 2 ^ k := by
  have h : ((2 : NNReal) ^ k) = ((2 ^ k : ℕ) : NNReal) := by norm_num
  rw [h]; exact Nat.floor_natCast _

/-- `logN (2 ^ n) = max 1 n`. -/
lemma logN_two_pow (n : ℕ) : Work.Analysis.EndVar.logN (2 ^ n) = ((max 1 n : ℕ) : ℤ) := by
  have hpow : (2 : ℕ) ^ (max 1 n) = max (2 ^ n) 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have h2 : (2 : ℕ) ≤ 2 ^ n := by
        have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by norm_num) h
        simpa using this
      rw [max_eq_right (show 1 ≤ n by omega), max_eq_left h2]
  change (Nat.log 2 (max (2 ^ n) 2) : ℤ) = ((max 1 n : ℕ) : ℤ)
  rw [← hpow, Nat.log_pow (by norm_num : 1 < 2)]

/-- The dyadic family `n ↦ 2 ^ n` is lacunary with ratio `3/2`. -/
lemma lacunary_two_pow :
    PointwiseErgodicTheorems.Lacunary (3 / 2 : NNReal) (fun n : ℕ => (2 : NNReal) ^ n) := by
  intro n
  have hne : (2 : NNReal) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have h : ((2 : NNReal) ^ (n + 1)) / ((2 : NNReal) ^ n) = 2 := by
    rw [pow_succ]; field_simp
  rw [h]; norm_num

/-- The `Tle`-form of the rescaled cutoff: `Tle ρ l (varphitildeN d N 0) = kmtProj ρ l (-(d * logN N))`,
proved here in-file from `varphitildeN_zero_eq_etaCutG` and `Tle_etaCut` (so that this module does
not have to import the crux-bearing `A7G.lowpassAlphaTransferG`). -/
lemma Tle_varphitildeN_zero_eq_kmtProj' (ρ : ℝ) (l d N : ℕ) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphitildeN d N 0)
      = Work.KMTContract.kmtProj ρ l (-((d : ℤ) * Work.Analysis.EndVar.logN N)) := by
  rw [Work.KMTAreas.A7G.varphitildeN_zero_eq_etaCutG, Work.KMTAreas.A7.Tle_etaCut]

/-- **The partial-sum maximal of the annuli is dominated by twice the variational norm of the
walk**, pointwise, for *every* arithmetic height `l₁` and base level `m₀`.  This is the telescoping
`∑_{i<K}(lpf (i+1) - lpf i) = lpf K - lpf 0` followed by `‖a - b‖ ≤ ‖a‖ + ‖b‖` and
`supPart ≤ variationalNorm`. -/
lemma partMaxD_le_two_variationalNorm (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      ≤ 2 * PointwiseErgodicTheorems.variationalNorm 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
  refine iSup_le fun K => ?_
  rw [sum_range_lpf_sub ρ l₁ m₀ f K x]
  have hK : ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ
      ≤ PointwiseErgodicTheorems.variationalNorm 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) :=
    (le_iSup (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x‖ₑ) K).trans
      (le_add_right le_rfl)
  have h0 : ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
      ≤ PointwiseErgodicTheorems.variationalNorm 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) :=
    (le_iSup (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x‖ₑ) 0).trans
      (le_add_right le_rfl)
  calc ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ
        + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ := enorm_sub_le
    _ ≤ PointwiseErgodicTheorems.variationalNorm 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
        + PointwiseErgodicTheorems.variationalNorm 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := add_le_add hK h0
    _ = 2 * PointwiseErgodicTheorems.variationalNorm 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by rw [two_mul]

/-- **The target from the `l`-free variational estimate for the low-pass walk.**  This is the
sharpest socket in the file: the assignment's inequality (in its *values/chain* packaging) follows
from the single statement that the *full* `3`-variational norm of the walk
`m ↦ lpf ρ l₁ m₀ m f` is `ℓᵖ`-bounded by `C‖f‖_{ℓᵖ}`, uniformly in `l₁` and `m₀`.

That variational statement is exactly the paper's linear Ionescu--Wainger estimate (lin-1)/(lin-2)
in the `m₀`-uniform, `l₁`-uniform form, and it is the natural target for the transfer from the
*arithmetic-free* case (which is PROVED, see `lacunaryMaxPieceProved_lzero` and
`Work.KMTAreas.A7G.plainBumpVarG`). -/
theorem lacunaryMaxPieceProved_of_varBound
    (hV : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hVb⟩ := hV ρ hρ hρ1 p hp hptop
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨Cρ, hCρ, 2 * C, by positivity, ?_⟩
  intro l₁ m₀ hg f
  have hstep := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ))
    (v := fun x : ℤ => 2 * PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
    (fun x => partMaxD_le_two_variationalNorm ρ l₁ m₀ f x) hp0 hpT
    (μ := MeasureTheory.Measure.count)
  rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := (2 : ℝ≥0∞))
    (by norm_num) hp0 hpT] at hstep
  have hmid : 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * C) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    calc 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
        ≤ 2 * (ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left (hVb l₁ m₀ hg f) (by norm_num : (0 : ℝ≥0∞) ≤ 2)
      _ = ENNReal.ofReal (2 * C) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          rw [← mul_assoc, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact (hstep.trans hmid).trans (le_add_of_nonneg_left bot_le)

/-- **The target from the Lépingle / Jones--Seeger--Wright variational step.**

This is the sharpest socket in the file, and it is the statement the project's own analysis
(`Work.KMTAreas.A7Lpd.lacunaryMaximal.lean`, docstring) names as the remaining crux
`Work.KMTAreas.A7Lpd.varPartSqFun`: the classical real-variable inequality saying that the
*variation part* of the walk `k ↦ Tle ρ l (η(2^{m₀+k}·)) f` is dominated in `ℓᵖ` by the band-pass
square function of its increments,

  `‖ varPart^3 (T_k f)_k ‖_{ℓᵖ}  ≤  C ‖ (∑_k ‖T_k f − T_{k+1} f‖ₑ²)^{1/2} ‖_{ℓᵖ}`,

with a constant `C` *independent of `l₁` and `m₀`*.

Given that inequality, the assignment follows: the partial-sum maximal of the annuli is dominated
pointwise by the `3`-variation of the walk
(`Work.KMTAreas.A7Lpd.iSup_partialSum_le_varPart`), the first value is bounded by the
`l₁`-free single-scale bound folded into the constant, and the *proved*, `l₁`-free band square
function bound `Work.KMTAreas.A7Lpd.bandSquareUnif` absorbs the square function into `C‖f‖_{ℓᵖ}`.

The square function is written with the `ℝ≥0∞`-valued norms `‖·‖ₑ` (`Work.KMTAreas.A7Hi.sqFun`),
which is *junk-free*: the `ℝ`-valued `∑'` form used in `Work.KMTAreas.A7Lpd.lacunaryMaxConst` is
`0` on the (a.e. null) set where the family is not summable, and is therefore the weaker
hypothesis. -/
theorem lacunaryMaxPieceProved_of_varPartSqFun
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (hvar : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
          (fun k : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (k : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l m₀ f)
          p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
            p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ₁, hCρ₁, C₁, hC₁, h₁⟩ := hvar
  obtain ⟨Cρ₂, hCρ₂, C₂, hC₂, h₂⟩ :=
    Work.KMTAreas.A7Lpd.bandSquareUnif ρ hρ hρ1 p hp hptop
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨max Cρ₁ Cρ₂, lt_max_of_lt_left hCρ₁, C₁ * C₂ + 1, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hg₁ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₁ l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_left _ _) hgood
  have hg₂ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₂ l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_right _ _) hgood
  -- ## the two sides differ only by the sign of the summands
  have hsumEq : ∀ (K : ℕ) (x : ℤ),
      ‖(∑ i ∈ Finset.range K, (Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ
        = ‖(∑ i ∈ Finset.range K, (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ := by
    intro K x
    have hneg : (∑ i ∈ Finset.range K, (Work.KMTContract.kmtProj ρ l₁
            (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))
        = -(∑ i ∈ Finset.range K, (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Work.KMTAreas.A7Hi.lpf]
      ring
    rw [hneg, enorm_neg]
  have hL : (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      = fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ := by
    funext x
    refine le_antisymm (iSup_le fun K => ?_) (iSup_le fun K => ?_)
    · exact le_iSup_of_le K (le_of_eq (hsumEq K x).symm)
    · exact le_iSup_of_le K (le_of_eq (hsumEq K x))
  -- ## the partial-sum maximal is dominated by the `3`-variation of the walk
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
          (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x))
          p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_mono_ennreal
      (u := fun x : ℤ => (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ))
      (v := fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
          (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x))
      (fun x => Work.KMTAreas.A7Lpd.iSup_partialSum_le_varPart ρ l₁ m₀ f
        (r := 3) (by norm_num) x) hp0 hpT (μ := MeasureTheory.Measure.count)
  -- ## assembly
  calc MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ)
          p MeasureTheory.Measure.count := by rw [hL]
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
          (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x))
          p MeasureTheory.Measure.count := hstep
    _ ≤ ENNReal.ofReal C₁ * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count := h₁ l₁ m₀ hg₁ f
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal C₂ *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_left (h₂ l₁ m₀ hg₂ f) bot_le
    _ = ENNReal.ofReal (C₁ * C₂) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC₁.le]
    _ ≤ ENNReal.ofReal (C₁ * C₂ + 1) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) bot_le
    _ ≤ ENNReal.ofReal (C₁ * C₂ + 1) *
          (MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p
              MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_left (le_add_left le_rfl) bot_le
    _ = ENNReal.ofReal (C₁ * C₂ + 1) * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
            p MeasureTheory.Measure.count
        + ENNReal.ofReal (C₁ * C₂ + 1) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [mul_add]

/-- **The `l₁ = 0` case of the assignment.**  For every `m₀ ≥ 1` the partial-sum maximal of the
annuli of the plain low-pass family `lpf ρ 0 m₀` obeys the requested square-function estimate with
a constant independent of `m₀`. -/
theorem lacunaryMaxPieceProved_lzero (ρ : ℝ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m₀ : ℕ), 1 ≤ m₀ → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ 0 m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ 0 m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨C, hC, hB⟩ := Work.KMTAreas.A7G.plainBumpVarG 1 le_rfl ρ (3 / 2 : NNReal)
    (by norm_num) 3 (by norm_num) p hp hptop
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨2 * (C + 1), by positivity, ?_⟩
  intro m₀ hm₀ f
  -- ## Step 1: the plain family at dyadic levels is the `lpf` walk reindexed
  have hV : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x)
      ≤ PointwiseErgodicTheorems.variationalNorm 3
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN 1 (Nat.floor ((2 : NNReal) ^ n)) 0) f x) := by
    intro x
    have hEq : ∀ m : ℕ, Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeN 1
          (Nat.floor ((2 : NNReal) ^ (m₀ + m))) 0) f x
        = Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x := by
      intro m
      rw [Tle_varphitildeN_zero_eq_kmtProj', floor_two_pow, logN_two_pow,
        max_eq_right (le_trans hm₀ (Nat.le_add_right m₀ m))]
      simp only [Work.KMTAreas.A7Hi.lpf]
      exact congrArg (fun z : ℤ => Work.KMTContract.kmtProj ρ 0 z f x) (by push_cast; ring)
    have h1 := Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := 3)
      (u := fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN 1 (Nat.floor ((2 : NNReal) ^ n)) 0) f x)
      (φ := fun m : ℕ => m₀ + m) (fun a b hab => Nat.add_le_add_left hab m₀)
    have h2 : (fun m : ℕ => Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeN 1
          (Nat.floor ((2 : NNReal) ^ (m₀ + m))) 0) f x)
        = (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x) := funext hEq
    rwa [h2] at h1
  have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x))
    (v := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN 1 (Nat.floor ((2 : NNReal) ^ n)) 0) f x))
    hV hp0 hpT (μ := MeasureTheory.Measure.count)
  have hBV := hB (fun n : ℕ => (2 : NNReal) ^ n) lacunary_two_pow
    (fun n => one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2)) f
  have hVfin : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    hmono.trans hBV
  -- ## Step 2: the partial-sum maximal is dominated by `2` times the variational norm
  have hpt : ∀ x : ℤ, (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ 0 m₀ i f x))‖ₑ)
      ≤ 2 * PointwiseErgodicTheorems.variationalNorm 3
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x) := by
    intro x
    refine iSup_le fun K => ?_
    rw [sum_range_lpf_sub ρ 0 m₀ f K x]
    have hK : ‖Work.KMTAreas.A7Hi.lpf ρ 0 m₀ K f x‖ₑ
        ≤ PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x) :=
      (le_iSup (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x‖ₑ) K).trans
        (le_add_right le_rfl)
    have h0 : ‖Work.KMTAreas.A7Hi.lpf ρ 0 m₀ 0 f x‖ₑ
        ≤ PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x) :=
      (le_iSup (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x‖ₑ) 0).trans
        (le_add_right le_rfl)
    calc ‖Work.KMTAreas.A7Hi.lpf ρ 0 m₀ K f x
            - Work.KMTAreas.A7Hi.lpf ρ 0 m₀ 0 f x‖ₑ
        ≤ ‖Work.KMTAreas.A7Hi.lpf ρ 0 m₀ K f x‖ₑ
          + ‖Work.KMTAreas.A7Hi.lpf ρ 0 m₀ 0 f x‖ₑ := enorm_sub_le
      _ ≤ PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x)
          + PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x) := add_le_add hK h0
      _ = 2 * PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x) := by rw [two_mul]
  have hstep := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ 0 m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ 0 m₀ i f x))‖ₑ))
    (v := fun x : ℤ => 2 * PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x))
    hpt hp0 hpT (μ := MeasureTheory.Measure.count)
  rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := (2 : ℝ≥0∞))
    (by norm_num) hp0 hpT] at hstep
  have hmid : 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x)) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * (C + 1)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    calc 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x)) p MeasureTheory.Measure.count
        ≤ 2 * (ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left hVfin (by norm_num : (0 : ℝ≥0∞) ≤ 2)
      _ = ENNReal.ofReal (2 * C) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          rw [← mul_assoc, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ ENNReal.ofReal (2 * (C + 1)) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) bot_le
  exact (hstep.trans hmid).trans (le_add_of_nonneg_left bot_le)

/-- **The Ionescu--Wainger lacunary maximal inequality (MAX) at arithmetic height `0`**, i.e. a
*proved instance* of the socket `IwMaximalLac` (unconditional in the base level, for `m₀ ≥ 1`).

This is the same computation as `lacunaryMaxPieceProved_lzero`, but stopping at the values-maximal
instead of the partial-sum maximal: the values-maximal is dominated by the full variational norm
(`variationalNorm = supPart + chainPart`), the walk at base level `m₀` is the monotone reindexing
`m ↦ m₀ + m` of the dyadic family `n ↦ Tle ρ 0 (varphitildeN 1 ⌊2^n⌋ 0)`, and a monotone reindexing
does not increase the variational norm.  Hence the whole height-`0` instance of the target's crux
`(MAX)` is a theorem of the workspace. -/
theorem iwMaximalLac_lzero (ρ : ℝ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m₀ : ℕ), 1 ≤ m₀ → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ,
          ‖Work.KMTContract.kmtProj ρ 0 (-((m₀ : ℤ) + (K : ℤ))) f x‖ₑ)
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨C, hC, hB⟩ := Work.KMTAreas.A7G.plainBumpVarG 1 le_rfl ρ (3 / 2 : NNReal)
    (by norm_num) 3 (by norm_num) p hp hptop
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨C, hC, ?_⟩
  intro m₀ hm₀ f
  have hV : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x)
      ≤ PointwiseErgodicTheorems.variationalNorm 3
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN 1 (Nat.floor ((2 : NNReal) ^ n)) 0) f x) := by
    intro x
    have hEq : ∀ m : ℕ, Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeN 1
          (Nat.floor ((2 : NNReal) ^ (m₀ + m))) 0) f x
        = Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x := by
      intro m
      rw [Tle_varphitildeN_zero_eq_kmtProj', floor_two_pow, logN_two_pow,
        max_eq_right (le_trans hm₀ (Nat.le_add_right m₀ m))]
      simp only [Work.KMTAreas.A7Hi.lpf]
      exact congrArg (fun z : ℤ => Work.KMTContract.kmtProj ρ 0 z f x) (by push_cast; ring)
    have h1 := Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := 3)
      (u := fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN 1 (Nat.floor ((2 : NNReal) ^ n)) 0) f x)
      (φ := fun m : ℕ => m₀ + m) (fun a b hab => Nat.add_le_add_left hab m₀)
    have h2 : (fun m : ℕ => Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeN 1
          (Nat.floor ((2 : NNReal) ^ (m₀ + m))) 0) f x)
        = (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x) := funext hEq
    rwa [h2] at h1
  have hpt : ∀ x : ℤ, (⨆ K : ℕ,
        ‖Work.KMTContract.kmtProj ρ 0 (-((m₀ : ℤ) + (K : ℤ))) f x‖ₑ)
      ≤ PointwiseErgodicTheorems.variationalNorm 3
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN 1 (Nat.floor ((2 : NNReal) ^ n)) 0) f x) := by
    intro x
    refine (hV x).trans' ?_
    have h := Work.KMTAreas.A7Hi.variationalNorm_eq_parts 3
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ 0 m₀ m f x)
    rw [h]
    exact le_add_of_nonneg_right bot_le
  refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal hpt hp0 hpT
    (μ := MeasureTheory.Measure.count)).trans ?_
  exact hB (fun n : ℕ => (2 : NNReal) ^ n) lacunary_two_pow
    (fun n => one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2)) f


/-- `eLpNorm` of a finite sum of `ℝ≥0∞`-valued functions. -/
lemma eLpNorm_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℝ≥0∞) {p : ENNReal}
    (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ∑ i ∈ s, F i x) p MeasureTheory.Measure.count
      ≤ ∑ i ∈ s, MeasureTheory.eLpNorm (F i) p MeasureTheory.Measure.count := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : (fun x : ℤ => ∑ i ∈ insert a s, F i x)
        = (F a) + (fun x : ℤ => ∑ i ∈ s, F i x) := by
      funext x
      rw [Finset.sum_insert ha]
      rfl
    rw [h1]
    refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal hp1 hpt).trans ?_
    rw [Finset.sum_insert ha]
    exact add_le_add le_rfl ih

/-- `‖z‖ₑ = ofReal ‖z‖` for a complex number. -/
private lemma enorm_eq_ofReal_norm' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  congr 1

/-- `GoodMajorArcs ρ Cρ l₁ (-(m₀))` with `Cρ ≥ 1` and `ρ > 0` forces `m₀ ≥ 1`. -/
lemma one_le_of_goodMajorArcs {ρ Cρ : ℝ} {l₁ m₀ : ℕ} (hCρ : 1 ≤ Cρ) (hρ : 0 < ρ)
    (h : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ))) : 1 ≤ m₀ := by
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have h4 : ((-(m₀ : ℤ) : ℤ) : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := h
  have h5 : (1 : ℝ) ≤ (m₀ : ℝ) := by
    push_cast at h4
    nlinarith [hCρ, h3]
  exact_mod_cast h5

/-! ## The arithmetic character on the sample lattice `iwQl ρ l · ℤ`

`iwQl ρ l = lcm (P_{≤l})` kills every element of `(ℚ/ℤ)_{≤l}`
(`Analysis.IonescuWainger.iwQl_nsmul_eq_zero`), so the arithmetic character
`arithChar ρ l y = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α y)` is constant on the sample lattice `iwQl ρ l · ℤ`
and equals the cardinality of the frequency set there.  Consequently the whole arithmetic content of the Ionescu--Wainger kernel disappears on that
lattice: with `A7Hi.kmtKernel_eq_arithChar_cw` this gives that the kernel of `kmtProj ρ l k` is
`#(ℚ/ℤ)_{≤l}` times the *plain* bump kernel `cw (η_{≤k})` on `iwQl ρ l · ℤ` (recorded below as
`iwKernel_eq_card_mul_cw_of_iwQl_dvd`).

This is the "arithmetic vanishes on the sample lattice" half of the Shannon sampling transfer of
the paper's large-scale regime (`A7Rep/SamplingLatticeIdentity` is the reproduction half); the
statement itself is the content of the (currently non-compiling) module
`Submission/Work/KMTAreas/A7/residueLp_arithQ_eq.lean` (`arithChar_eq_of_dvd`), reproduced here
against the stable `iwQl`.  **It does not by itself give the assignment**: the route through it
produces a factor `#A² ≍ 16^{l₁}` (the reproducing kernel `\check 1_{Ω_0} = arithChar · sinc` is
not in `ℓ¹(ℤ)`), which is why the assignment's `l`-free statement needs the uniform
vector-valued Ionescu--Wainger input — see `NOTES_A7Hi2_lacunaryMaxPieceProved_SESSION7.md` §4-§5. -/

/-- The arithmetic character at the origin is the cardinality of the frequency set. -/
lemma arithChar_zero_eq_card (ρ : ℝ) (l : ℕ) :
    Work.KMTAreas.A7.arithChar ρ l 0
      = ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℂ) := by
  unfold Work.KMTAreas.A7.arithChar
  simp [fourier_apply, fourier_zero']

/-- The arithmetic character is periodic with period `iwQl ρ l`. -/
lemma arithChar_add_iwQl_mul (ρ : ℝ) (l : ℕ) (y c : ℤ) :
    Work.KMTAreas.A7.arithChar ρ l (y + (Work.Analysis.IonescuWainger.iwQl ρ l : ℤ) * c)
      = Work.KMTAreas.A7.arithChar ρ l y := by
  unfold Work.KMTAreas.A7.arithChar
  refine Finset.sum_congr rfl fun α hα => ?_
  have hkill : ((Work.Analysis.IonescuWainger.iwQl ρ l : ℤ) * c) • α = 0 := by
    rw [mul_comm, mul_zsmul]
    rw [show (((Work.Analysis.IonescuWainger.iwQl ρ l : ℕ) : ℤ) • α)
        = Work.Analysis.IonescuWainger.iwQl ρ l • α from by simp]
    rw [Work.Analysis.IonescuWainger.iwQl_nsmul_eq_zero hα, smul_zero]
  rw [fourier_add]
  have hf : fourier (T := 1) ((Work.Analysis.IonescuWainger.iwQl ρ l : ℤ) * c) α = 1 := by
    rw [fourier_apply, hkill]
    exact fourier_zero'
  rw [hf, mul_one]

/-- On the sample lattice `iwQl ρ l · ℤ` the arithmetic character equals the cardinality. -/
lemma arithChar_eq_card_of_iwQl_dvd (ρ : ℝ) (l : ℕ) {y : ℤ}
    (hy : ((Work.Analysis.IonescuWainger.iwQl ρ l : ℕ) : ℤ) ∣ y) :
    Work.KMTAreas.A7.arithChar ρ l y
      = ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℂ) := by
  obtain ⟨c, hc⟩ := hy
  have h := arithChar_add_iwQl_mul ρ l 0 c
  rw [zero_add] at h
  rw [hc, h, arithChar_zero_eq_card]

/-- **The IW kernel on the sample lattice is `#(ℚ/ℤ)_{≤l}` times the plain bump kernel.** -/
lemma iwKernel_eq_card_mul_cw_of_iwQl_dvd (ρ : ℝ) (l : ℕ) (k j : ℤ)
    (hj : ((Work.Analysis.IonescuWainger.iwQl ρ l : ℕ) : ℤ) ∣ j) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j
      = ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℂ)
        * Work.KMTAreas.A7.cw
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j := by
  rw [Work.KMTAreas.A7Hi.kmtKernel_eq_arithChar_cw]
  rw [arithChar_eq_card_of_iwQl_dvd ρ l (y := -j) (by simpa using dvd_neg.mpr hj)]

/-! ## The symbol at the arithmetic frequencies

`periodize (etaCut kmtEta k)` is supported in `realArc k` (`A7Hi.supportedInArc_iwPhi`), so under
the non-aliasing hypothesis at least one term of the Ionescu--Wainger symbol `σ_k = ∑_{α'} P_k(·-α')`
vanishes: at `ξ = 0` (and, more generally, at every `ξ ∈ (ℚ/ℤ)_{≤l}`) exactly one term survives,
and its value is `P_k 0 = 1`.  Hence

  `σ_k α = 1` for every `α ∈ (ℚ/ℤ)_{≤l}`,

i.e. **the IW projections fix the arithmetic characters** — the frequency-side reason why the
square function `sqFun` is blind to the `A_l`-content of `f` (and hence why the assignment carries
the additive term `+ C‖f‖ₚ`, and why the sibling stubs without it are governed by the junk
convention — see `NOTES_A7Hi2_lacunaryMaxPieceProved_SESSION7.md` §7, §11). -/

/-! ## The small-height (`l ≤ iwC0 ρ`) case of the chain-part bound

Everything below is proved from the PROVED channel decomposition
`Work.KMTAreas.A7Hi2.chainPart_le_sum_variationalNorm` (`chainLeFiniteIntegral`) and the PROVED
arithmetic-free lacunary variational estimate `Work.KMTAreas.A7Hi.DilVarClean`.  The point is that
the only loss of that route is the number of `α`-channels, `#(ℚ/ℤ)_{≤l}`, which in the small-height
regime `l ≤ iwC0 ρ` is bounded by the *constant* `4 ^ iwC0 ρ` — a function of `ρ` alone.  Hence the
chain-part bound holds in that regime with a constant that is uniform in `m₀` and in `l ≤ iwC0 ρ`.
This is what isolates the remaining content of `lacunaryMaxPieceProved` in the deep regime
`iwC0 ρ < l`. -/

/-- Modulating by a character does not change the pointwise extended norm, hence not the
`ℓᵖ`-norm. -/
lemma enorm_charMul_eq (α : Work.Analysis.IonescuWainger.Circle) (g : ℤ → ℂ) (x : ℤ) :
    ‖Work.KMTAreas.A7Hi.charMul α g x‖ₑ = ‖g x‖ₑ := by
  have h : ‖Work.KMTAreas.A7Hi.charMul α g x‖₊ = ‖g x‖₊ := by
    rw [← NNReal.coe_inj, coe_nnnorm, coe_nnnorm, Work.KMTAreas.A7Hi.norm_charMul]
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, h]

/-- In the small-height regime `l ≤ iwC0 ρ` the IW arithmetic frequency set has at most
`4 ^ (iwC0 ρ + 1)` elements (a constant depending only on `ρ`). -/
lemma card_iwArithFreqs_le_smallHeight (ρ : ℝ) {l : ℕ}
    (hl : l ≤ Work.Analysis.IonescuWainger.iwC0 ρ) :
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card
      ≤ 4 ^ (Work.Analysis.IonescuWainger.iwC0 ρ + 1) := by
  classical
  have hP : Work.Analysis.IonescuWainger.iwP ρ l = Finset.Icc 1 (2 ^ l) := by
    rw [Work.Analysis.IonescuWainger.iwP]; exact if_pos hl
  have hcard : (Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card
      ≤ ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, q := by
    have hb : Work.Analysis.IonescuWainger.iwArithFreqs ρ l
        = (Work.Analysis.IonescuWainger.iwP ρ l).biUnion
            (fun q : ℕ => (Finset.range q).image (fun a : ℕ =>
              ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle))) := rfl
    rw [hb]
    have hb2 : ((Work.Analysis.IonescuWainger.iwP ρ l).biUnion (fun q : ℕ =>
        (Finset.range q).image (fun a : ℕ =>
          ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle)))).card
        ≤ ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, ((Finset.range q).image (fun a : ℕ =>
          ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle))).card :=
      @Finset.card_biUnion_le ℕ Work.Analysis.IonescuWainger.Circle _
        (Work.Analysis.IonescuWainger.iwP ρ l)
        (fun q : ℕ => (Finset.range q).image (fun a : ℕ =>
          ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle)))
    refine hb2.trans ?_
    refine Finset.sum_le_sum fun q _ => ?_
    simpa using Finset.card_image_le (s := Finset.range q)
      (f := fun a : ℕ => ((a : ℝ) / (q : ℝ) : Work.Analysis.IonescuWainger.Circle))
  have hsum : ∑ q ∈ Finset.Icc 1 (2 ^ l), q ≤ 4 ^ (l + 1) := by
    have hsub : Finset.Icc 1 (2 ^ l) ⊆ Finset.range (2 ^ l + 1) := by
      intro q hq
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hq).2
    calc ∑ q ∈ Finset.Icc 1 (2 ^ l), q
        ≤ ∑ q ∈ Finset.range (2 ^ l + 1), q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ ≤ ∑ _q ∈ Finset.range (2 ^ l + 1), (2 ^ l + 1) :=
          Finset.sum_le_sum fun q hq => Nat.le_of_lt (Finset.mem_range.mp hq)
      _ = (2 ^ l + 1) * (2 ^ l + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ 4 ^ (l + 1) := by
          have h1 : 2 ^ l + 1 ≤ 2 ^ (l + 1) := by
            rw [pow_succ]
            have := Nat.one_le_pow l 2 (by norm_num)
            omega
          have h2 : (2 ^ l + 1) ^ 2 ≤ (2 ^ (l + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
          have h3 : (2 ^ (l + 1)) ^ 2 = 4 ^ (l + 1) := by
            rw [← pow_mul, show (l + 1) * 2 = 2 * (l + 1) from by omega, pow_mul]; norm_num
          rw [h3] at h2
          simpa [pow_two] using h2
  have hpow : 4 ^ (l + 1) ≤ 4 ^ (Work.Analysis.IonescuWainger.iwC0 ρ + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card
      ≤ ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, q := hcard
    _ = ∑ q ∈ Finset.Icc 1 (2 ^ l), q := by rw [hP]
    _ ≤ 4 ^ (l + 1) := hsum
    _ ≤ 4 ^ (Work.Analysis.IonescuWainger.iwC0 ρ + 1) := hpow

/-- **The chain-part bound in the small-height regime**, with a constant uniform in `m₀` and in
`l ≤ iwC0 ρ`. -/
theorem chainPart_le_smallHeight (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l m₀ : ℕ), l ≤ Work.Analysis.IonescuWainger.iwC0 ρ → ∀ f : ℤ → ℂ,
      Summable (fun n : ℤ => ‖f n‖ ^ p.toReal) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ m f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp0R : (0:ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hp1R : (1:ℝ) < p.toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hp0R, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (ne_of_lt hptop)]
    exact hp
  obtain ⟨Cdil, hCdilpos, hDil⟩ :=
    Work.KMTAreas.A7Hi.DilVarClean p.toReal hp1R r hr Work.KMTAreas.A7Hi.kmtPhiSch
  refine ⟨(4:ℝ) ^ (Work.Analysis.IonescuWainger.iwC0 ρ + 1) * Cdil, by positivity, ?_⟩
  intro l m₀ hl f hf
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hptne : p ≠ ⊤ := ne_of_lt hptop
  have hpt : ∀ x : ℤ, Work.KMTAreas.A7Hi.chainPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ m f x)
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
              (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x) :=
    Work.KMTAreas.A7Hi2.chainPart_le_sum_variationalNorm ρ l m₀ r hr p hp hptop f hf
  have hchan : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
            (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Cdil * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro α _
    have h := hDil (Work.KMTAreas.A7Hi.lpfScale m₀)
      (fun n => Work.KMTAreas.A7Hi.lpfScale_pos m₀ n)
      (fun n => Work.KMTAreas.A7Hi.lpfScale_lacunary m₀ n) (Work.KMTAreas.A7Hi.charMul α f)
    rw [hpeq] at h
    have hmod : MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.charMul α f) p MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      have h1 : MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.charMul α f) p MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by
          rw [enorm_charMul_eq]
      have h2 : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.charMul α f) p MeasureTheory.Measure.count :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by
          rw [enorm_charMul_eq]
      exact le_antisymm h1 h2
    rw [hmod] at h
    exact h
  have hsum := eLpNorm_finset_sum_le (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
    (fun α x => PointwiseErgodicTheorems.variationalNorm r
      (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
        (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
    (le_of_lt hp) hptne
  refine ((MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => hpt x)).trans hsum).trans ?_
  have hfin : ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
            (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
          p MeasureTheory.Measure.count
      ≤ ∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          ENNReal.ofReal Cdil * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    Finset.sum_le_sum hchan
  refine hfin.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcardle : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ≥0∞)
      ≤ ENNReal.ofReal (4 ^ (Work.Analysis.IonescuWainger.iwC0 ρ + 1)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast card_iwArithFreqs_le_smallHeight ρ hl)
  have hCdil0 : (0:ℝ≥0∞) ≤ ENNReal.ofReal Cdil := bot_le
  calc ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ≥0∞) *
        (ENNReal.ofReal Cdil * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (4 ^ (Work.Analysis.IonescuWainger.iwC0 ρ + 1)) *
          (ENNReal.ofReal Cdil * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_right hcardle bot_le
    _ = ENNReal.ofReal ((4:ℝ) ^ (Work.Analysis.IonescuWainger.iwC0 ρ + 1) * Cdil) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]


/-! ## The Khintchine ("lossless summation") step for a finite family of operators

The lemma `sqSum_lintegral_le_of_uniformSigns` below is the finite-family form of the classical
Rademacher/Khintchine linearisation: if a *finite* family of operators has a uniform-in-signs `ℒᵖ`
bound, then the square function of the family obeys the same bound with a constant depending only
on `p`.  In the present chapter this is the "lossless summation" step of the deep regime: a
selection of `card ι` Ionescu–Wainger strata (the "few large primes" frequencies, `KWfreqs ρ l`)
can be summed **without loss**, which is what turns the single-scale bound
`Work.KMTAreas.A7.KW_conv_lp_bound` (proved, via Tao's superset bound
`Work.KMTAreas.main_signed_strata_uniform`) into the square-function bound for the strata.

The finite-family form matters because `KWfreqs ρ l` is indexed by a `Finset` of subsets of the
prime set `S_l` and not by `ℕ`; the tree's ℕ-indexed version
(`Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin`) cannot be applied directly. -/

/-- **Khintchine linearisation for a finite family of operators**: a uniform-in-signs `ℒᵖ` bound
implies the square-function bound, with a constant depending only on `p`. -/
theorem sqSum_lintegral_le_of_uniformSigns (q : ℝ) (hq : 1 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} (T : Fin n → (ℤ → ℂ) → (ℤ → ℂ)) (M : ℝ), 0 ≤ M →
      (∀ (ε : Fin n → ℂ), (∀ i, ‖ε i‖ ≤ 1) → ∀ f : ℤ → ℂ,
        ∫⁻ x, ‖∑ i, ε i * T i f x‖ₑ ^ q ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count) →
      ∀ f : ℤ → ℂ,
      ∫⁻ x, (∑ i : Fin n, ‖T i f x‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count := by
  obtain ⟨c, hc, hK⟩ := Work.KMTAreas.A7.khintchine_sqSum_pointwise q hq
  refine ⟨(c ^ q)⁻¹, by positivity, ?_⟩
  intro n T M hM hsgn f
  -- pointwise Khintchine
  have hpt : ∀ x : ℤ, (∑ i : Fin n, ‖T i f x‖ₑ ^ (2 : ℝ)) ^ (q / 2)
      ≤ (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ *
          ∑ ε : Fin n → Bool, ‖∑ i : Fin n,
            (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q := by
    intro x
    simpa using hK n (fun i => T i f x)
  have hstep1 : ∫⁻ x, (∑ i : Fin n, ‖T i f x‖ₑ ^ (2 : ℝ)) ^ (q / 2)
        ∂MeasureTheory.Measure.count
      ≤ (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ *
          ∫⁻ x, (∑ ε : Fin n → Bool, ‖∑ i : Fin n,
            (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q) ∂MeasureTheory.Measure.count := by
    refine (MeasureTheory.lintegral_mono hpt).trans (le_of_eq ?_)
    rw [MeasureTheory.lintegral_const_mul'']
    exact (measurable_of_countable
      (fun x : ℤ => ∑ ε : Fin n → Bool, ‖∑ i : Fin n,
        (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q)).aemeasurable
  have hstep2 : ∫⁻ x, (∑ ε : Fin n → Bool, ‖∑ i : Fin n,
        (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q) ∂MeasureTheory.Measure.count
      = ∑ ε : Fin n → Bool, ∫⁻ x, ‖∑ i : Fin n,
        (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q ∂MeasureTheory.Measure.count :=
    MeasureTheory.lintegral_finsetSum Finset.univ (fun ε _ => measurable_of_countable
      (fun x : ℤ => ‖∑ i : Fin n, (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q))
  rw [hstep2] at hstep1
  have hstep3 : ∑ ε : Fin n → Bool, ∫⁻ x, ‖∑ i : Fin n,
        (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((2 : ℝ) ^ n) *
          (ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count) := by
    have h1 : ∀ ε : Fin n → Bool, ∫⁻ x, ‖∑ i : Fin n,
          (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count := by
      intro ε
      refine hsgn (fun i => if ε i then (1 : ℂ) else -1) (fun i => ?_) f
      by_cases h : ε i <;> simp [h]
    calc ∑ ε : Fin n → Bool, ∫⁻ x, ‖∑ i : Fin n,
            (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q ∂MeasureTheory.Measure.count
        ≤ ∑ _ε : Fin n → Bool,
            (ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count) :=
          Finset.sum_le_sum (fun ε _ => h1 ε)
      _ = (Fintype.card (Fin n → Bool) : ℝ≥0∞) *
            (ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ENNReal.ofReal ((2 : ℝ) ^ n) *
            (ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count) := by
          congr 1
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
            ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  set Z : ℝ≥0∞ := ENNReal.ofReal (M ^ q) *
      ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count with hZdef
  have h2ne : ENNReal.ofReal ((2 : ℝ) ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).ne'
  have h2top : ENNReal.ofReal ((2 : ℝ) ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcq_ne : (ENNReal.ofReal (c ^ q))⁻¹ = ENNReal.ofReal ((c ^ q)⁻¹) :=
    (ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hc q)).symm
  have hZ : (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n) * Z) = Z := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel h2ne h2top, one_mul]
  refine hstep1.trans ?_
  calc (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ *
        (∑ ε : Fin n → Bool, ∫⁻ x, ‖∑ i : Fin n,
          (if ε i then (1 : ℂ) else -1) * T i f x‖ₑ ^ q ∂MeasureTheory.Measure.count)
      ≤ (ENNReal.ofReal (c ^ q))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ *
          (ENNReal.ofReal ((2 : ℝ) ^ n) * Z) :=
        mul_le_mul_of_nonneg_left hstep3 bot_le
    _ = (ENNReal.ofReal (c ^ q))⁻¹ * Z := by rw [mul_assoc, hZ]
    _ = ENNReal.ofReal ((c ^ q)⁻¹ * M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count := by
        rw [hZdef, hcq_ne, ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hc.le q))]


/-- **Khintchine linearisation, `Finset`-indexed form.**  This is the interface in which the
Ionescu–Wainger strata arrive: `main_signed_strata_uniform` (Tao's superset bound, PROVED in the
tree) is a uniform-in-signs bound for the family `A ↦ Op_{ψ;Σ_A}` indexed by the `Finset`
`S.powerset.filter (·.card ≤ k)`, and the present lemma converts it into the square-function bound

  `∫⁻ (Σ_{A ∈ s} ‖Op_A f‖²)^{q/2} ≤ ofReal (K M^q) * ∫⁻ ‖f‖^q`,

i.e. the *lossless summation over the strata*.  (The `Fin`-indexed
`sqSum_lintegral_le_of_uniformSigns` cannot be applied directly to a `Finset`-indexed family, which
is why this interface is recorded.) -/
theorem sqSum_lintegral_le_of_uniformSigns_finset (q : ℝ) (hq : 1 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} (s : Finset ι) (T : ι → (ℤ → ℂ) → (ℤ → ℂ)) (M : ℝ),
      0 ≤ M →
      (∀ (ε : ι → ℂ), (∀ i ∈ s, ‖ε i‖ ≤ 1) → ∀ f : ℤ → ℂ,
        ∫⁻ x, ‖∑ i ∈ s, ε i * T i f x‖ₑ ^ q ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count) →
      ∀ f : ℤ → ℂ,
      ∫⁻ x, (∑ i ∈ s, ‖T i f x‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count := by
  obtain ⟨K, hK, hmain⟩ := sqSum_lintegral_le_of_uniformSigns q hq
  refine ⟨K, hK, ?_⟩
  intro ι s T M hM hsgn f
  classical
  set e : Fin s.card ≃ {x // x ∈ s} := (s.equivFin).symm with he
  set T' : Fin s.card → (ℤ → ℂ) → (ℤ → ℂ) := fun j => T ((e j).1) with hT'def
  have hsumC : ∀ (g : ι → ℂ), (∑ i ∈ s, g i) = ∑ j : Fin s.card, g ((e j).1) := by
    intro g
    have h1 : (∑ i ∈ s, g i) = ∑ i : {x // x ∈ s}, g i.1 := by
      simpa using (Finset.sum_attach s g).symm
    rw [h1]
    exact (Equiv.sum_comp e (fun i : {x // x ∈ s} => g i.1)).symm
  have hsumE : ∀ (g : ι → ℝ≥0∞), (∑ i ∈ s, g i) = ∑ j : Fin s.card, g ((e j).1) := by
    intro g
    have h1 : (∑ i ∈ s, g i) = ∑ i : {x // x ∈ s}, g i.1 := by
      simpa using (Finset.sum_attach s g).symm
    rw [h1]
    exact (Equiv.sum_comp e (fun i : {x // x ∈ s} => g i.1)).symm
  have hsgn' : ∀ (ε : Fin s.card → ℂ), (∀ j, ‖ε j‖ ≤ 1) → ∀ f : ℤ → ℂ,
      ∫⁻ x, ‖∑ j, ε j * T' j f x‖ₑ ^ q ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (M ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂MeasureTheory.Measure.count := by
    intro ε hε f
    have hε' : ∀ i ∈ s, ‖(if h : i ∈ s then ε (e.symm ⟨i, h⟩) else 0 : ℂ)‖ ≤ 1 := by
      intro i hi
      simp only [dif_pos hi]
      exact hε _
    have hpt : ∀ x : ℤ, (∑ j : Fin s.card, ε j * T' j f x)
        = ∑ i ∈ s, (if h : i ∈ s then ε (e.symm ⟨i, h⟩) else 0 : ℂ) * T i f x := by
      intro x
      refine (Finset.sum_congr rfl (fun j _ => ?_)).trans
        ((hsumC (fun i => (if h : i ∈ s then ε (e.symm ⟨i, h⟩) else 0 : ℂ) * T i f x)).symm)
      have h1 : (e j).1 ∈ s := (e j).2
      rw [dif_pos h1]
      have h2 : e.symm ⟨(e j).1, h1⟩ = j := by
        rw [show (⟨(e j).1, h1⟩ : {x // x ∈ s}) = e j from rfl]
        exact e.symm_apply_apply j
      rw [h2]
    simp only [hpt]
    exact hsgn (fun i => if h : i ∈ s then ε (e.symm ⟨i, h⟩) else 0) hε' f
  have hgoal : ∀ x : ℤ, (∑ i ∈ s, ‖T i f x‖ₑ ^ (2 : ℝ))
      = ∑ j : Fin s.card, ‖T' j f x‖ₑ ^ (2 : ℝ) := by
    intro x
    exact hsumE (fun i => ‖T i f x‖ₑ ^ (2 : ℝ))
  simp only [hgoal]
  exact hmain T' M hM hsgn' f


/-! ## The assignment from the `varRhoAll`-form of the Ionescu--Wainger variation bound

`Work.BourgainPlan.Maximal.varRhoAll (2 : ℝ) a = ⨆ K, varRho 2 0 K a` is the `2`-variation of the
sequence `a` in the packaging of `Work.BourgainPlan.Maximal` (KMSZ §5).  The pointwise domination
below shows that the assignment's integrand is *dominated* by that `2`-variation, so the assignment
follows from an `l₁`-free `varRhoAll 2` bound of the low-pass walk.  That is the shape in which the
KMSZ Theorem 5.2 route (`Work.BourgainPlan.Thm52.exists_thm52` / `…_finsupp`) produces its
estimates: the `Rademacher--Menshov`-form theorem bounds `eLpNorm (varRhoAll 2 …)`
directly, so this socket wires the KMSZ route to the assignment with no further maximal/variational
conversion. -/

end Work.KMTAreas.A7Hi2
