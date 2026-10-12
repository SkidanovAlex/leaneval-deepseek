import ChallengeDeps
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_eq_of_mem_farSet
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_farSet_le_tBwordB
import Submission.Work.UBBInputs8.A.exists_hlow_localised_of_bounded
import Submission.Work.UBBInputs8.A.qLHSwordB_integral_u_box
import Submission.Work.UBBInputs8.A.tBLocalisationInd_const
import Submission.Work.UBBInputs8.A.tBwordBInd_const_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs9.Defs` — round 9: the kinetic localisation (R1)

Round 8 (`Submission/Work/UBBInputs8/README.md` §"The precise residuals" (R1)) left the
kinetic localisation as the one external input of the a-priori side, in the FS-faithful
(`boxQInd`-carrying) form

    `KineticLocalisationInd d b  :=  ∀ N ℓ ε c Φ, tBLocalisationInd N ℓ d b ε c Φ`

with

    `tBLocalisationInd N ℓ d b ε c Φ  :=  (b/2ℓ²)·cnPlus ℓ Φ + ∫_u 𝒯_{B(u)}(Φ) du ≤ kinWord N ℓ Φ`

(`𝒯_{B(u)} = tBwordBInd`, FS `eq:HBU`/`eq:appTB`).

This chapter does three things.

## 1. It **refutes** the clause as stated

`A.not_KineticLocalisationInd` : for `0 < b` the round-8 clause is **false**, with an explicit
witness state — the *slot-indicator* state `slotInd N i S` (`x ↦ 1_S(x i)`).  For such a state the
right-hand side `kinWord` — the corpus's word `ΣᵢΣ_k ∫ (∂_{ik}Φ)²`, i.e. the integral of the
*square of the pointwise Fréchet derivative* — vanishes identically (`fderiv` of a slot indicator
is `0` **everywhere**: off the differentiability set by definition, and at a differentiability
point the function is locally constant), while the left-hand side is `≥ (b/2ℓ²)·cnPlus ℓ Φ > 0`
for a non-trivial box indicator.  So the clause is not the operator localisation it is meant to
express: it quantifies over a state class on which `kinWord` is *not* the Dirichlet form.

The same witness refutes the corpus's indicator-free rendering
(`Work.SmallBoxTBWord.tBLocalisation`, `Work.UBBInputs2.KineticLocalisation`), and hence shows
that the `hloc` field makes `Work.UBBInputs8.AprioriClauses8` (and round 7's `AprioriClauses`)
**uninhabited**.  See `A/not_KineticLocalisationInd.lean` (proved).

## 2. It **repairs** the clause: the right-hand side is the `χ`-weighted word

FS's sliding localisation does not telescope to the plain word `kinWord`: the sliding window
`χ_{B(u)}(x) = χ(x/ℓ)·χ(x/(dℓ) − u)` satisfies `∫_u χ_{B(u)}(x)² du = χ(x/ℓ)²` (the per-`x`
partition `DLInfra.chiB_partition_u`), so the `u`-integral of a `χ_B`-weighted Dirichlet word is
the `χ(x/ℓ)²`-weighted *global* word — and `χ(x/ℓ)²` has supremum `chiSup² > 1`
(`B/chiSup_sq_ge.lean`), with value `chiSup²` on the whole ball `‖x‖ ≤ ℓ/4`
(`B/chiScale_plateau.lean`).  The corpus's `SmallBoxSliding/NOTES.md` §7(b) records exactly this
(`kinWordChi ≈ 132·kinWord` for the `chiSmallB` normalisation); this chapter proves it for the
corpus's own `chi` (`B/not_kinWord_le_kinWordW.lean`) and *quantitatively* for the sliding family
(`A/not_tBLocalisationInd_smooth.lean`).

So the repaired clause carries the weighted word `kinWordW` (and a smoothness/support condition
on the state, since the plain word is only a Dirichlet form on `H¹`-states):

    `tBLocalisationW N ℓ d b ε c Φ  :=  (b/2ℓ²)·cnPlus ℓ Φ + ∫_u 𝒯_{B(u)}(Φ) du ≤ kinWordW N ℓ Φ`

with `kinWordW N ℓ Φ = ΣᵢΣ_k∫_{abox N ℓ} χ(x_i/ℓ)²(∂_{ik}Φ)²`.  The consumer's chain can absorb
the constant: `B/kinWordW_le_sup` gives `kinWordW ≤ chiSup²·kinWord`.  **The word alone is not enough:**
`A/not_KineticLocalisationW` shows that the `χ`-weighted clause is *also* false on the
unrestricted state class (the same slot-indicator witness), so a usable clause must restrict the
state class as well — that is `KineticLocalisationWSm` below.

## 3. It names the honest residual and its roadmap

`BSslidingKin` (FS `eq:BSsliding2` = Bratteli–Solovej Thm 3.10, the *kinetic* content at the
small-box family) and `LocKinEnWord` (FS `lem:LocKinEn`, the *big-box* family `Λ(u)` with the
Neumann term of `eq:DefT`) are stated here at the corpus's own objects, with the roadmap in
`README.md`.  Neither is a word-level consequence of the corpus pieces: FS's two lemmas are
*operator* inequalities, and the corpus's `tBwordBInd` keeps the gap term
`½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q_B` of `eq:appTB` but **drops** the two Neumann-gap terms
`½ε_T(dℓ)⁻²(−Δ^N_u)/(−Δ^N_u+(dℓ)⁻²)` and `bℓ⁻²Q_u` of `eq:DefT` which pay for it.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2
open Work.UBBInputs8
open Work.SmallBoxTBWord
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The witness states

The slot-indicator state is the cheapest state on which the two sides of the clause disagree
qualitatively: its `kinWord` (an integral of squares of *pointwise* derivatives) is `0`, while its
excited count `cnPlus` is strictly positive inside a non-trivial box. -/

/-- **The slot-`i` indicator state** `x ↦ 1_S(x i)` of the slot-`i` coordinate.  No measurability
or smoothness hypothesis on `S` is needed to *state* it; for the `cnPlus`-positivity lemma `S` is
taken measurable and inside the centred box. -/
noncomputable def slotInd (N : ℕ) (i : Fin N) (S : Set ℝ³) : X N → ℝ :=
  fun x => S.indicator (fun _ => (1 : ℝ)) (x i)

/-- The **witness set** of the refutation: a sub-box of `acube ℓ` of measure strictly between
`0` and `ℓ³` (a cube of side `ℓ/2`). -/
def halfCube (ℓ : ℝ) : Set ℝ³ := acube (ℓ / 2)

/-- The **witness state** of the refutation (single particle, slot `0`). -/
noncomputable def indWitness (ℓ : ℝ) : X 1 → ℝ :=
  slotInd 1 0 (halfCube ℓ)

/-! ## 2. The `χ`-weighted global Dirichlet word

This is the word that the sliding family *does* telescope to (`Work.SmallBoxSliding.Telescope`,
`Work.SmallBoxTBWord.Free.kinWordB_projection_free`): the corpus's `kinWordB` `u`-integral.  It is
the honest right-hand side of the localisation clause, because FS's small-box window is the
*product* `χ(x/ℓ)χ(x/(dℓ) − u)`, whose `u`-partition is `χ(x/ℓ)²` — not the indicator `1_{B(u)}`
(whose `u`-integral is `1` and for which the plain word is exactly right,
`Work.SmallBoxSliding.kinWordBoxInd_integral_u`). -/

/-- **The `χ`-weighted word**: `ΣᵢΣ_k ∫_{abox N ℓ} χ(x_i/ℓ)²(∂_{ik}Φ)²`.  For `χ = chiScale ℓ`
this is the corpus's `Words.kinWordChi` shape. -/
noncomputable def kinWordW (N : ℕ) (ℓ : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N ℓ, (chiScale ℓ (x i)) ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-! ## 3. The repaired clause -/

/-- **The repaired (R1) clause** — the `χ`-weighted-word form.  Compared with
`tBLocalisationInd` the right-hand side is the weighted word `kinWordW` (the word the sliding
family telescopes to) instead of the plain `kinWord`; a caller keeps the plain-word shape by
multiplying the right-hand side by the constant `chiSup²` (`B/kinWordW_le_sup`). -/
def tBLocalisationW (N : ℕ) (ℓ d b ε c : ℝ) (Φ : X N → ℝ) : Prop :=
  (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
      (∫ u : ℝ³, tBwordBInd N ℓ d ε c u Φ) ≤ kinWordW N ℓ Φ

/-- The `χ`-weighted-word localisation, quantified as in round 1/2. -/
def KineticLocalisationW (d b : ℝ) : Prop :=
  ∀ (N : ℕ) (ℓ ε c : ℝ) (Φ : X N → ℝ), tBLocalisationW N ℓ d b ε c Φ

/-! ## 4. The honest residuals (FS's two operator lemmas, at the corpus's objects)

FS prove (their Lemma `lem:LocKinEn`, from Bratteli–Solovej Lemma 3.7) that the `u`-integral of
the **big-box** kinetic

    `𝒯_u = ½ε_T(dℓ)⁻²(−Δ_u^N)/(−Δ_u^N+(dℓ)⁻²) + bℓ⁻²Q_u
            + bε_T(dℓ)⁻²Q_u1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_u + 𝒯'_u`,

    `𝒯'_u = Q_uχ_u{(1−ε_T)[√−Δ−½(sℓ)⁻¹]_+² + ε_T[√−Δ−½(dsℓ)⁻¹]_+²}χ_uQ_u`

is dominated by `−Δ` (the plain Dirichlet word — here the `u`-family is the *big*-box family
`χ_u(x) = χ(x/ℓ − u)`, an exact `L²`-partition, `∫_uχ_u(x)²du = 1`), and (their `eq:BSsliding2`,
cited from Bratteli–Solovej Thm 3.10) that the *anchored* box Hamiltonian dominates
`Σᵢ(b/2)Q_{Λ,i}ℓ⁻² + ∫_uH_{B(u)}(μ)du`.  The corpus's `tBwordKinInd`/`tBwordBInd` are the
`eq:appTB`-shaped parts of these objects; the two named residuals below record the missing
content in the corpus's vocabulary. -/

/-- The **big-box family** `Λ(u) = ℓu + acube ℓ` of FS's `lem:LocKinEn`. -/
def bigBox (ℓ : ℝ) (u : ℝ³) : Set ℝ³ := {x : ℝ³ | x - ℓ • u ∈ acube ℓ}

/-- FS's big-box window `χ_u(x) = χ(x/ℓ − u) = chiScale ℓ (x − ℓu)`. -/
noncomputable def chiBig (ℓ : ℝ) (u : ℝ³) (x : ℝ³) : ℝ := chiScale ℓ (x - ℓ • u)

/-- **FS `eq:DefT`'s main kinetic term at the *big* box** (`u = 0`): the corpus's `tBwordKinInd`
at `A = acube ℓ`, `volA = ℓ³`, `χ = chiScale ℓ`.  (FS's full `𝒯_{u=0}` is this plus the
Neumann-gap term `½ε_T(dℓ)⁻²(−Δ_Λ^N)/(−Δ_Λ^N+(dℓ)⁻²)`, the large-box gap `bℓ⁻²Q_Λ` and the
large-momentum term `bε_T(dℓ)⁻²Q_Λ1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_Λ` — all of which only *increase* the
left-hand side of `BSslidingKin`.) -/
noncomputable def tBwordKinBig (N : ℕ) (ℓ c : ℝ) (Φ : X N → ℝ) : ℝ :=
  tBwordKinInd ℓ (acube ℓ) (ℓ ^ 3) (chiScale ℓ) c Φ

/-- The **big-box family** kinetic term of FS's `lem:LocKinEn`: `tBwordKinInd` at `A = Λ(u)`,
`volA = ℓ³`, `χ = χ_u`. -/
noncomputable def tBwordKinBigU (N : ℕ) (ℓ c : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  tBwordKinInd ℓ (bigBox ℓ u) (ℓ ^ 3) (chiBig ℓ u) c Φ

/-- **FS `lem:LocKinEn` (the `𝒯'` term), word form**: the `u`-integral of the big-box family's
main kinetic term is dominated by the plain Dirichlet word.  This is the part of FS's cited
lem:LocKinEn that corresponds to their `∫_u𝒯'_u du ≤ −Δ` (the other terms of their `𝒯_u` only
*increase* the left-hand side, so this is implied by their statement).

⚠ **Instantiate it at FS's cutoff `c = ½(sℓ)⁻¹`, not at `c = 0`.**  The *unprojected* version of
the big-box family at `c = 0` is refuted by the exact telescoping `B.integral_dirichlet_chiBig_eq`
(`= kinWord + (Σ_k∫(∂_kχ_ℓ)²)/ℓ³·∫Φ²`, a *positive* excess over `kinWord`), i.e. FS's cutoff is
load-bearing in `lem:LocKinEn` as well; the projected statement above differs from the unprojected
one only by the box mean (`|c_Λ| ≤ ‖Φ‖₁/ℓ³`). -/
def LocKinEnWord (N : ℕ) (ℓ c : ℝ) (Φ : X N → ℝ) : Prop :=
  (∫ u : ℝ³, tBwordKinBigU N ℓ c u Φ) ≤ kinWord N ℓ Φ

/-- **Bratteli–Solovej Thm 3.10 / FS `eq:BSsliding2`, kinetic content**, in the corpus's word
vocabulary: the gap `(b/2ℓ²)cnPlus` plus the small-box average of `𝒯_B` is dominated by the
*anchored* big-box kinetic term. -/
def BSslidingKin (N : ℕ) (ℓ d b ε c : ℝ) (Φ : X N → ℝ) : Prop :=
  (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
      (∫ u : ℝ³, tBwordBInd N ℓ d ε c u Φ) ≤ tBwordKinBig N ℓ c Φ

/-! ## 5. The state class of the residual: integrability of the sliding integrand

The corpus's own consumer (`Work.SmallBoxTBWord.sliding_sum_bound_of_tBLocalisation`) takes the
integrability of the sliding integrand as an *explicit field*; the smooth-state refutation of
`A/not_tBLocalisationInd_smooth.lean` is proved under exactly that field, so it applies inside the
consumer's own hypotheses. -/

/-- **The integrability field** of the residual at a state `Φ`: the `u`-integrand of the
small-box kinetic is `Integrable` (in particular the clause's `∫_u` is the mathematical integral
and not the `integral_undef` convention). -/
def KinIntegrable (N : ℕ) (ℓ d ε c : ℝ) (Φ : X N → ℝ) : Prop :=
  Integrable (fun u : ℝ³ => tBwordBInd N ℓ d ε c u Φ)

/-! ## 6. The repaired clause and the repaired (A) list

The two halves of the repair: the `χ`-weighted word (`tBLocalisationW`) **and** a state-class
restriction.  `A/not_KineticLocalisationW` refutes the word repair alone (the slot-indicator
witness has `kinWordW = 0`), so the clause a caller should wire is `KineticLocalisationWSm`. -/

/-- **The repaired kinetic clause**: the `χ`-weighted-word clause (`tBLocalisationW`) restricted to
*even* states — here: to `ContDiff ℝ ∞` states, on which the corpus word `ΣᵢΣ_k∫(∂_{ik}Φ)²` is the
honest Dirichlet form of `Φ` (and on which the box words are not decided by `integral_undef`). -/
def KineticLocalisationWSm (d b : ℝ) : Prop :=
  ∀ (N : ℕ) (ℓ ε c : ℝ) (Φ : X N → ℝ), ContDiff ℝ (⊤ : ENat) Φ →
    tBLocalisationW N ℓ d b ε c Φ

/-- **The repaired round-8 (A) list**: `AprioriClauses8` with its `hloc` field replaced by the
repaired kinetic clause `KineticLocalisationWSm`.  It is the list a caller should instantiate once
the a-priori chain is re-derived with the `χ`-weighted word (the constants are free in FS's
scheme: `B/kinWordW_le_sup` converts the weighted word back to `chiSup²` times the plain one). -/
structure AprioriClauses8W (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (d M : ℕ)
    (R0 : ℝ) : Prop where
  hb : 0 < b
  ha : 0 ≤ a v
  hR' : 0 ≤ R'
  hM : 1 ≤ M
  hd : (0 : ℝ) < (d : ℝ)
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hR0 : 0 < R0
  hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16
  hv1 : MemLp v 1
  hloc : KineticLocalisationWSm (d : ℝ) b
  hcore : BoxSumBoundCore v h b K_B R' J ε₀ d M
  hLP : LocPotentialCorpus v h d M

end Work.UBBInputs9
