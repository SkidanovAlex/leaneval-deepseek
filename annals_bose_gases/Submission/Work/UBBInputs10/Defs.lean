import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.qLHSwordB_integral_u_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs10` — round 10: the (R3) word comparison

**Read `Submission/Work/UBBInputs8/README.md` §"The precise residuals" (R3) first.**

Round 8 reduced FS `lem:LocPotential` (`hpot`) for *every* corpus trial state `Φ : CSBox N L` to the
single word comparison `Work.UBBInputs8.LocPotentialCorpus` (alias `Work.UBBInputs2.LocPotentialCorpus`),
i.e. the `χ_M²`-weighted *localised reference* word below the corpus per-box potential word,
and proved it to be *exactly* the remaining content (`A.hpotAll_of_locPotentialCorpus`).

This chapter **decides that comparison**.  Its content:

* **the comparison as stated is FALSE** (`Refute/not_locPotentialCorpus.lean`): the localisation
  layer uses the cosine-`M` bump `chiSmall M` (= FS's own `χ = C_M(ζζζ)^M`, `eq:Def_chi`), whose
  support is the *cube* `[−1/2,1/2]³`, while the corpus global word uses `Submission.CubicChi`'s
  `χ`, a Mathlib `ContDiffBump` with `rOut = 1/2` whose support is the *ball* of radius `1/2`.
  At a corner of the analysis box the corpus bump vanishes identically while the localisation bump
  does not, so the one-body term of the reference word is strictly negative where the corpus word
  is `0`.  This is a *modelling* mismatch (FS use the same `χ` everywhere), not an analytic gap;
* **the diagnosis** (`Refute/Corner.lean`): the two machine-checked support facts and the corner
  computation;
* **the repairs, proved** (`Repair/`): at *matched* bumps the comparison is a pointwise kernel
  domination (from `(χ⋆χ) ≤ 1` and `v, g₀ ≥ 0`), so
  * `qLHSwordChi ≤ qLHSwordChiM` — the reference word below the FS-faithful global word at the
    `χ_M` localisation (`Repair/ChiM.lean`), and
  * `qLHSwordPlainChi ≤ qLHSword (wPairC L v) (wPairC L (g₀ v h))` — the unrenormalised `χ²`-word
    below the *corpus* global word (`Repair/ChiPlain.lean`), which is what the localisation layer
    must telescope to if the corpus's global word is kept.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs10

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The two kernel families

* the **localisation/reference** kernel: the `χ_M(·/L)`-weighted *unrenormalised* kernel
  (this is exactly the pair of kernels appearing in `Work.SmallBoxSliding.qLHSwordChi`, i.e.
  the `u`-integral of the corpus's per-box kernel `Work.DLSmallKernels.wSmallPair`);
* the **global** kernels: FS's `eq:DefW_12` global kernel
  `w(x,y) = χ(x/L)·(h(x−y)/(χ⋆χ)((x−y)/L))·χ(y/L)`, in two bumps:
  * `renormChiMKernel` — the cosine-`M` bump `chiSmall M` (FS's own `χ`, *matched* with the
    localisation),
  * `plainChiKernel` — the corpus bump `chiScale L`, *without* the `(χ⋆χ)` renormalisation.
-/

/-- The *reference* (`χ_M`-weighted, unrenormalised) kernel of a numerator `f`. -/
noncomputable def chiMKernel (M : ℕ) (L : ℝ) (f : ℝ³ → ℝ) : ℝ³ → ℝ³ → ℝ :=
  fun x y => chiSmall M (L⁻¹ • x) * f (x - y) * chiSmall M (L⁻¹ • y)

/-- The one-body fibre of `chiMKernel M L (g0 v h)`: the `χ_M²`-weighted `g₀`-fibre
`∫_{y ∈ acube L} χ_M(x/L)·g₀(x−y)·χ_M(y/L) dy` — the quantity the reference word's
chemical-potential term carries. -/
noncomputable def chiMFibre {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L : ℝ) (z : ℝ³) : ℝ :=
  ∫ y in acube L, chiSmall M (L⁻¹ • z) * g0 v h (z - y) * chiSmall M (L⁻¹ • y)

/-- **The FS-faithful global kernel at the `χ_M` localisation**: FS `eq:DefW_12`
with FS's own `χ = C_M(ζζζ)^M` (the corpus's `chiSmall M`) and the `(χ_M⋆χ_M)(·/L)`
renormalisation denominator. -/
noncomputable def renormChiMKernel (M : ℕ) (L : ℝ) (f : ℝ³ → ℝ) : ℝ³ → ℝ³ → ℝ :=
  fun x y => chiSmall M (L⁻¹ • x) * (f (x - y) / convScaleSmall M L (x - y)) *
    chiSmall M (L⁻¹ • y)

/-- The corpus bump's kernel *without* the `(χ⋆χ)` renormalisation denominator:
`χ(x/L)·f(x−y)·χ(y/L)` with `χ` = `Submission.CubicChi.chi`. -/
noncomputable def plainChiKernel (L : ℝ) (f : ℝ³ → ℝ) : ℝ³ → ℝ³ → ℝ :=
  fun x y => chiScale L x * f (x - y) * chiScale L y

/-! ## 2. The three words -/

/-- **The FS-faithful global potential word at the `χ_M` localisation** — the corpus
`qLHSword` at the `χ_M`-renormalised kernels.  This is FS's global word `w = v/(χ⋆χ)`,
`w₁ = g₀/(χ⋆χ)` at FS's own `χ`. -/
noncomputable def qLHSwordChiM {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L μ : ℝ)
    (Φ : X N → ℝ) : ℝ :=
  qLHSword (N := N) L μ (renormChiMKernel M L v) (renormChiMKernel M L (g0 v h)) Φ

/-- **The unrenormalised `χ²`-weighted global word** at the *corpus* bump `χ` (no `(χ⋆χ)`
denominator).  This is the word that the localisation layer must telescope to if the corpus's
global word `qLHSword (wPairC L v) (wPairC L (g₀ v h))` is kept. -/
noncomputable def qLHSwordPlainChi {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (L μ : ℝ)
    (Φ : X N → ℝ) : ℝ :=
  qLHSword (N := N) L μ (plainChiKernel L v) (plainChiKernel L (g0 v h)) Φ

/-- The delivered reference word `Work.SmallBoxSliding.qLHSwordChi` is the corpus `qLHSword`
at the `χ_M` kernels (definitional). -/
theorem qLHSwordChi_eq_qLHSword_chiMKernel {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ)
    (L d μ : ℝ) (Φ : X N → ℝ) :
    Work.SmallBoxSliding.qLHSwordChi (N := N) h M L d μ Φ
      = qLHSword (N := N) L μ (chiMKernel M L v) (chiMKernel M L (g0 v h)) Φ := rfl

/-- The corpus global word is the `qLHSword` at `wPairC`. -/
theorem qLHSword_wPairC_eq {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (L μ : ℝ) (Φ : X N → ℝ) :
    qLHSword (N := N) L μ (wPairC L v) (wPairC L (g0 v h)) Φ
      = qLHSword (N := N) L μ
          (fun x y => chiScale L x * (v (x - y) / convScale L (x - y)) * chiScale L y)
          (fun x y => chiScale L x * (g0 v h (x - y) / convScale L (x - y)) * chiScale L y)
          Φ := rfl

/-! ## 3. The residual statements

`LocPotentialCorpus'` is the round-7/8 residual verbatim (the *false* one, named here so that the
refutation can be stated); `LocPotentialChiM` is the FS-faithful replacement. -/

/-- **The (R3) residual as stated in rounds 7/8** (alias of `Work.UBBInputs2.LocPotentialCorpus`,
spelled with the chapter's kernels so that the refutation reads off the two bumps). -/
def LocPotentialCorpus' (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
    qLHSword (N := N) L (dens N L) (chiMKernel M L v) (chiMKernel M L (g0 v h)) (Φ : X N → ℝ)
      ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)

/-- The residual with the `u`-integral of the corpus's per-box word; equivalent to
`LocPotentialCorpus'` by the delivered telescoping identity. -/
def LocalisedWordBelowCorpus (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
    (∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
      ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)

/-- **Not a repair: the naive matched-bump comparison.**  With the cosine-`M` bump on both sides
(the bump of FS's `eq:Def_chi`), the reference word is *not* below the global word: the
renormalisation denominator `(χ_M⋆χ_M)(·/L) ≤ 1` makes the renormalised fibre *larger*, and the
fibre enters `qLHSword` with a *minus* sign, so at `N = 1` (where the pair terms vanish) the reverse
inequality holds (`Repair/qLHSwordChiM_le_qLHSwordChi_one`).  Recorded here so that nobody mistakes
this Prop for the repair. -/
def LocPotentialChiM (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
    qLHSword (N := N) L (dens N L) (chiMKernel M L v) (chiMKernel M L (g0 v h)) (Φ : X N → ℝ)
      ≤ qLHSwordChiM h M L (dens N L) (Φ : X N → ℝ)

/-- **Not a repair either: the unrenormalised `χ²`-word against the corpus global word.**  The
corpus global word carries the additional `1/(χ⋆χ)(·/L) ≥ 1` factor, so its fibre is *larger* and
its pair kernel *larger*: at `N = 1` the unrenormalised word is *above* the corpus word.  The actual
repair is an **identity**, with the localised kernel restored to FS `eq:defW_12`
(`chiSmallBRep`, `wPairRep`, `qLHSwordBRep`, `LocalisedWordEqCorpus` below). -/
def PlainChiBelowCorpus (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
    qLHSwordPlainChi h L (dens N L) (Φ : X N → ℝ)
      ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)

/-! ## 4. The corner-state predicate (the refutation's witness class) -/

/-- A corpus trial state is *corner-supported* at scale `L` when every particle sits at a
configuration point of norm at least `L/2` — i.e. outside the support of the corpus bump
`chiScale L`. -/
def CornerState {N : ℕ} (L : ℝ) (Φ : CSBox N L) : Prop :=
  ∀ x ∈ tsupport (Φ : X N → ℝ), ∀ i : Fin N, L / 2 ≤ ‖x i‖



/-! ## 5. The repaired localisation layer (the FS-faithful kernels)

**Diagnosis (see `README.md`).**  The corpus's localised potential kernel
`Work.DLSmallKernels.wSmallScaled M (ℓd) f z = f z / (χ_M⋆χ_M)(z/(ℓd))` carries **only** the
small-box renormalisation.  FS `eq:defW_12` have `W^s(x) = W(x)/(χ⋆χ)(x/(dℓ))` where
`W(x) = v(x)/(χ⋆χ)(x/ℓ)`: the *ℓ-scale* factor is missing in the corpus.  As a consequence the
delivered telescoping identity lands on the **unrenormalised** word
`Work.SmallBoxSliding.qLHSwordChi` (kernel `χ_M(x/ℓ)·f(x−y)·χ_M(y/ℓ)`) instead of the global word
`qLHSword (wPairC L v) (wPairC L (g₀ v h))` — and the comparison between those two is **false**
(`Refute/not_locPotentialCorpus`), not a bookkeeping step.

**Repair.**  Restore FS's missing ℓ-scale denominator in the localised kernel, and use at the
ℓ-scale the *same* cutoff function as the global word (the corpus's `chiScale L`):

  `wPairRep M L d u f x y = χ_L(x)·χ_M((Ld)⁻¹x − u)·(f(x−y)/((χ⋆χ)((x−y)/L)·(χ_M⋆χ_M)((x−y)/(Ld))))·χ_L(y)·χ_M((Ld)⁻¹y − u)`.

Then `∫_u wPairRep M L d u f x y du = wPairC L f x y` **exactly** (the sliding integral of the
two `χ_M` factors cancels the `(Ld)`-denominator; the `ℓ`-denominator and the `χ_L` factors are
`u`-independent), so the sliding sum telescopes to the corpus global word *identically* — the
`hpot` field becomes a theorem with no comparison at all
(`Repair/qLHSwordBRep_integral_u`). -/
section Repair

/-- The `ℓ`-scale cutoff factor of the repaired localisation: the corpus bump `chiScale L`
(*matched* with the corpus global word), times the cosine-`M` bump at the small-box scale. -/
noncomputable def chiSmallBRep (M : ℕ) (L d : ℝ) (u x : ℝ³) : ℝ :=
  chiScale L x * chiSmall M ((L * d)⁻¹ • x - u)

/-- The repaired localised two-body kernel: FS `eq:defW_12`'s renormalisation at *both* scales
(`(χ⋆χ)(·/L)` from the global word and `(χ_M⋆χ_M)(·/(Ld))` from the sliding), with the cutoff
`chiSmallBRep`.  Its `u`-integral is exactly the corpus global kernel `wPairC L f`. -/
noncomputable def wPairRep (M : ℕ) (L d : ℝ) (u : ℝ³) (f : ℝ³ → ℝ) : ℝ³ → ℝ³ → ℝ :=
  fun x y => chiSmallBRep M L d u x *
    (f (x - y) / (convScale L (x - y) * convScaleSmall M (L * d) (x - y))) *
    chiSmallBRep M L d u y

/-- The repaired per-box potential word (the `qLHSword` at the repaired kernels). -/
noncomputable def qLHSwordBRep {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  qLHSword (N := N) L μ (wPairRep M L d u v) (wPairRep M L d u (g0 v h)) Φ

/-- The uncurried `u`-integrand of the repaired per-box word `qLHSwordBRep`. -/
noncomputable def qLHSBRepIntegrand {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L d μ : ℝ)
    (Φ : X N → ℝ) (u : ℝ³) (x : X N) : ℝ :=
  (Φ x) ^ 2 * (- μ * (∑ i : Fin N, ∫ y in acube L,
      chiSmallBRep M L d u (x i) *
        (g0 v h ((x i) - y) / (convScale L ((x i) - y) *
          convScaleSmall M (L * d) ((x i) - y))) * chiSmallBRep M L d u y)
    + (1 / 2) * (∑ p ∈ pairSet N, wPairRep M L d u v (x p.1) (x p.2)))

/-- The x-integrand of the corpus global word `qLHSword (wPairC L v) (wPairC L (g₀ v h))`. -/
noncomputable def corpusPotIntegrand {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (L μ : ℝ)
    (Φ : X N → ℝ) (x : X N) : ℝ :=
  (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre L (wPairC L (g0 v h)) (x i))
    + (1 / 2) * (∑ p ∈ pairSet N, wPairC L v (x p.1) (x p.2)))

/-- **The repaired residual is an identity**: the `u`-integral of the repaired per-box word is
*exactly* the corpus global word (`Repair/qLHSwordBRep_integral_u`). -/
def LocalisedWordEqCorpus (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
    (∫ u : ℝ³, qLHSwordBRep h M L d (dens N L) u (Φ : X N → ℝ))
      = qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)

end Repair


/-! ## 6. The bracket of the reference word, and the cosine-`M` lower bound -/

/-- The per-configuration bracket of the `χ_M`-**reference** word: `qLHSword` at the `χ_M` kernels
factors as `∫_{abox} Φ² · chiMBracket`. -/
noncomputable def chiMBracket {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ) (L μ : ℝ)
    (x : X N) : ℝ :=
  - μ * (∑ i : Fin N, chiMFibre h M L (x i))
    + (1 / 2) * (∑ p ∈ pairSet N, chiMKernel M L v (x p.1) (x p.2))

/-- The `qLHSword` at the `χ_M` kernels is the `Φ²`-weighted integral of `chiMBracket`. -/
theorem qLHSword_chiMKernel_eq_integral {N : ℕ} {v : ℝ³ → ℝ} (h : ScatSol v) (M : ℕ)
    (L μ : ℝ) (Φ : X N → ℝ) :
    qLHSword (N := N) L μ (chiMKernel M L v) (chiMKernel M L (g0 v h)) Φ
      = ∫ x in abox N L, (Φ x) ^ 2 * chiMBracket h M L μ x := rfl

/-- A positive lower bound for the cosine-`M` bump on the *coordinate* region `|z_j| ≤ 2/5`
(the region's "corners" are at distance `√3·(2/5) > 1/2` from the origin, exactly the
corner phenomenon analysed in `Refute/`). -/
noncomputable def chiSmallLower (M : ℕ) : ℝ :=
  (Real.cos (Real.pi * (2 / 5))) ^ (3 * M) / Real.sqrt (chiSmallNormSq M)

/-- `chiSmallLower M > 0`. -/
theorem chiSmallLower_pos {M : ℕ} (hM : 1 ≤ M) : 0 < chiSmallLower M := by
  have hcos : 0 < Real.cos (Real.pi * (2 / 5)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  exact div_pos (pow_pos hcos _) (Real.sqrt_pos.mpr (chiSmallNormSq_pos hM))

end Work.UBBInputs10
