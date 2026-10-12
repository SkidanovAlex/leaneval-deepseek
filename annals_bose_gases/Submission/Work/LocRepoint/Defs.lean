import ChallengeDeps
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.UBBInputs10.Defs
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_eq_of_mem_farSet
import Submission.Work.UBBInputs8.A.cnPlusBoxB_const_farSet_le_tBwordB
import Submission.Work.UBBInputs8.A.exists_hlow_localised_of_bounded
import Submission.Work.UBBInputs8.A.tBLocalisationInd_const
import Submission.Work.UBBInputs8.A.tBwordBInd_const_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.LocRepoint` — the localisation repoint (round 11)

**Read `Submission/Work/UBBInputs10/README.md` first.**  Round 10 decided the (R3) word
comparison `LocPotentialCorpus` (`= Work.UBBInputs2.LocPotentialCorpus`): it is **FALSE**
(`Work.UBBInputs10.not_locPotentialCorpus`), so the `hLP` field of `Work.UBBInputs8.AprioriClauses8`
and the `hpot` field of every a-priori bundle of rounds 1/2/7 cannot be closed as stated.  Round 10
also delivered the FS-faithful **repair**: at the repaired localised kernels
(`Work.UBBInputs10.chiSmallBRep` / `wPairRep`) the sliding sum telescopes *identically* to the
corpus global word `qLHSword (wPairC L v) (wPairC L (g₀ v h))`
(`Work.UBBInputs10.Repair.qLHSwordBRep_integral_u`), so there is nothing to compare.

This chapter **lands the repoint**: it carries the *whole localisation layer at the repaired
definitions*, under the corpus's own names, together with the repaired downstream a-priori chain,
so that

* `Work.LocRepoint.HpotEqAll_holds` — the potential-localisation field is a **THEOREM** (an
  equality, no comparison, no integrability hypothesis beyond continuity of the state);
* `Work.LocRepoint.AprioriClauses8Rep` — the round-8 (A) list **without** the `hLP` field:
  `R' + (b/2L²)·n₊/‖Φ‖² − 4πρ²(a v)L³(1 + K_B³√(ρ(a v)³)) ≤ EnergyWord` with no word comparison;
* `Work.LocRepoint.aprioriNPlusCov_of_aprioriClauses8Rep` — FS `eq:apriorinn+` from that list.

## The two edits (this is the whole semantic change)

| corpus (`Submission.BoseGases`) | repointed (`Work.LocRepoint`) |
|---|---|
| `chiSmallB M ℓ d u x = χ_M(x/ℓ)·χ_M(x/(ℓd) − u)` | `chiSmallB M ℓ d u x = χ(x/ℓ)·χ_M(x/(ℓd) − u)` |
| `wSmallPair M ℓ d u h x y = χ_B(x)·(h(x−y)/(χ_M⋆χ_M)((x−y)/(ℓd)))·χ_B(y)` | `wSmallPair M ℓ d u h x y = χ_B(x)·(h(x−y)/((χ⋆χ)((x−y)/ℓ)·(χ_M⋆χ_M)((x−y)/(ℓd))))·χ_B(y)` |

with `χ = Submission.CubicChi.chi` (the bump of the corpus *global* word `wPairC ℓ`), i.e. FS
`eq:Def_chi`'s `χ = C_M(ζζζ)^M` is **replaced at the ℓ-scale** by the same bump the global word
uses, and FS `eq:defW_12`'s **missing ℓ-scale renormalisation** `1/(χ⋆χ)(·/ℓ)` is restored.  Both
edits are *confined to the localisation layer*: `conv3Small`, `convScaleSmall`, `wSmallScaled`,
`wPairC`, `qLHSword`, the kinetic word `tBwordB` and the whole a-priori arithmetic
(`DLSlideCov`, `AprioriNPlusCov`) are untouched.

The repointed `chiSmallB`/`wSmallPair` are *definitionally* `Work.UBBInputs10.chiSmallBRep` /
`Work.UBBInputs10.wPairRep` (`rfl`), so round 10's delivered kernel and telescope identities apply
verbatim; everything else below is the corpus's own file with the two lines changed.

## Interface (what to import)

    import Submission.Work.LocRepoint.All     -- namespace `Work.LocRepoint`

* the repointed layer: `chiSmallB`, `wSmallScaled`, `wSmallPair`, `wSmall1Pair`, `chiMass`,
  `kinWordB`, `qLHSwordB`, `sboxEBWord`, `qLHSBIntegrand`, `qLHSwordChi`, `kinWordChi`;
* the delivered telescoping at the repointed layer: `qLHSwordB_integral_u_box`,
  `integrable_qLHSBIntegrand_box`, `integrable_qLHSwordB_u`, `HpotEqAll_holds`;
* the repaired a-priori chain: `BoxSumBoundCoreRep`, `BoxSumBoundCanonRep`, `BoxSumBoundRep`,
  `SlidingSumDataRep`, `slidingRawNormRep_of_data`, `slidingSumDataRep_of`,
  `AprioriClauses8Rep`, `aprioriNPlusCov_of_aprioriClauses8Rep`.

**Repointing in place.**  `Work.LocRepoint.X` is written to be *textually* the corpus's `X`; to
land the repoint in the shared layer, replace the two definitions of
`Submission.BoseGases.chiSmallB` and `Submission.BoseGases.wSmallPair` by the two lines in
`PATCH.md` (in this directory) and re-run the delivered proofs, which is what this chapter does at
a copy of the namespace.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.LocRepoint

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The repointed localisation kernels -/

/-- **The repointed small-box cutoff** — edit (i): the ℓ-scale factor is the *corpus global word's*
bump `χ(·/ℓ)` (`chiScale ℓ`), the same function used by `wPairC ℓ`, instead of the cosine bump
`χ_M(·/ℓ)`.  (FS use one and the same `χ` at every scale; the corpus used two.) -/
noncomputable def chiSmallB (M : ℕ) (ℓ d : ℝ) (u x : ℝ³) : ℝ :=
  chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u)

/-- The repointed cutoff is round 10's repaired cutoff (definitional). -/
theorem chiSmallB_eq_rep (M : ℕ) (ℓ d : ℝ) (u x : ℝ³) :
    chiSmallB M ℓ d u x = Work.UBBInputs10.chiSmallBRep M ℓ d u x := rfl

/-- **The repointed renormalised localised kernel numerator** — FS `eq:defW_12`'s `W^s`: *both*
denominators, `(χ⋆χ)(·/ℓ)` from the global word and `(χ_M⋆χ_M)(·/(ℓd))` from the sliding. -/
noncomputable def wSmallScaled (M : ℕ) (ℓ d : ℝ) (h : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  h x / (convScale ℓ x * convScaleSmall M (ℓ * d) x)

/-- **The repointed localised two-body kernel** — edit (ii): the numerator carries both
renormalisation denominators.  This is *definitionally* `Work.UBBInputs10.wPairRep`. -/
noncomputable def wSmallPair (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (h : ℝ³ → ℝ) (x y : ℝ³) : ℝ :=
  chiSmallB M ℓ d u x * wSmallScaled M ℓ d h (x - y) * chiSmallB M ℓ d u y

/-- The repointed localised pair kernel is round 10's repaired pair kernel (definitional). -/
theorem wSmallPair_eq_wPairRep (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (h : ℝ³ → ℝ) (x y : ℝ³) :
    wSmallPair M ℓ d u h x y = Work.UBBInputs10.wPairRep M ℓ d u h x y := rfl

/-- The repointed localised one-body kernel (numerator `g₀ = v(1−ω)`). -/
noncomputable def wSmall1Pair {v : ℝ³ → ℝ}
    (h : ScatSol v) (M : ℕ) (ℓ d : ℝ)
    (u : ℝ³) (x y : ℝ³) : ℝ :=
  wSmallPair M ℓ d u (g0 v h) x y

/-! ## 2. The repointed sliding geometry (unchanged objects) -/

/-- The good set `G` of the sliding localisation (unchanged by the repoint: it is defined from
`(ℓd)•u` alone).  Alias of `Work.SmallBoxSliding.goodSet`. -/
abbrev goodSet (ℓ d μ : ℝ) : Set ℝ³ := Work.SmallBoxSliding.goodSet ℓ d μ

/-- The nominal small-box volume (unchanged). -/
abbrev boxVol (ℓ d : ℝ) : ℝ := Work.SmallBoxSliding.boxVol ℓ d

/-! ## 3. The repointed masses and words -/

/-- The repointed `χ_{B(u)}²`-mass `∫_x χ_{B(u)}(x)² dx`. -/
noncomputable def chiMass (M : ℕ) (ℓ d : ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2

/-- The repointed localised kinetic word: the `χ_{B(u)}²`-weighted Dirichlet energy. -/
noncomputable def kinWordB (N : ℕ) (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N ℓ, (chiSmallB M ℓ d u (x i)) ^ 2 *
      (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-- **The repointed localised potential word**: the corpus `qLHSword` at the repointed localised
kernels.  This is round 10's `Work.UBBInputs10.qLHSwordBRep` (definitional). -/
noncomputable def qLHSwordB {N : ℕ} {v : ℝ³ → ℝ}
    (h : ScatSol v) (M : ℕ) (ℓ d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  qLHSword (N := N) ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) Φ

/-- The repointed localised potential word is round 10's repaired per-box word (definitional). -/
theorem qLHSwordB_eq_rep {N : ℕ} {v : ℝ³ → ℝ}
    (h : ScatSol v) (M : ℕ) (ℓ d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) :
    qLHSwordB (N := N) h M ℓ d μ u Φ
      = Work.UBBInputs10.qLHSwordBRep h M ℓ d μ u Φ := rfl

/-- The repointed per-box energy word `E_{B(u)} = kinWordB + qLHSwordB`. -/
noncomputable def sboxEBWord {N : ℕ} {v : ℝ³ → ℝ}
    (h : ScatSol v) (M : ℕ) (ℓ d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  kinWordB N M ℓ d u Φ + qLHSwordB h M ℓ d μ u Φ

/-- **The reference kinetic word at the repointed layer**: the `χ(·/L)²`-weighted Dirichlet energy
— the `u`-integral of the repointed localised kinetic word (`kinWordB_integral_u`).  Note the
weight is the *corpus global* bump `chiScale L`, i.e. `kinWordChi` is the kinetic half of the word
that the repointed potential word telescopes to. -/
noncomputable def kinWordChi (N : ℕ) (M : ℕ) (L : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N L, (chiScale L (x i)) ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-- The uncurried `u`-integrand of the repointed localised potential word (this is round 10's
`Work.UBBInputs10.qLHSBRepIntegrand`, definitionally). -/
noncomputable def qLHSBIntegrand {N : ℕ} {v : ℝ³ → ℝ}
    (h : ScatSol v) (M : ℕ) (ℓ d μ : ℝ)
    (Φ : X N → ℝ) (u : ℝ³) (x : X N) : ℝ :=
  Φ x ^ 2 * (- μ * (∑ i : Fin N, ∫ y in acube ℓ, wSmall1Pair h M ℓ d u (x i) y)
    + (1 / 2) * (∑ q ∈ pairSet N, wSmallPair M ℓ d u v (x q.1) (x q.2)))

/-- The `x`-integrand of the corpus global word `qLHSword (wPairC ℓ v) (wPairC ℓ (g₀ v h))`. -/
noncomputable def corpusPotIntegrand {N : ℕ} {v : ℝ³ → ℝ}
    (h : ScatSol v) (ℓ μ : ℝ)
    (Φ : X N → ℝ) (x : X N) : ℝ :=
  Φ x ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
    + (1 / 2) * (∑ q ∈ pairSet N, wPairC ℓ v (x q.1) (x q.2)))

/-- The telescoping identity at the repointed layer (this is round 10's
`Work.UBBInputs10.LocalisedWordEqCorpus`, definitionally). -/
def LocalisedWordEqCorpus (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
    (∫ u : ℝ³, qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
      = qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)

/-- **The potential-localisation field at the repointed layer** — FS `lem:LocPotential`
*as an equality* (round 10: the comparison-shaped `HpotAt`/`HpotAll` of `Work.UBBInputs7` is
false; at the repointed kernels the telescoping is exact). -/
def HpotEqAt (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) (L : ℝ) (N : ℕ) (Φ : CSBox N L) : Prop :=
  (∫ u : ℝ³, qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
    = qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)

/-- The potential-localisation field at the repointed layer, over the whole corpus trial space. -/
def HpotEqAll (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L, HpotEqAt v h d M L N Φ

/-! ## 4. The repointed a-priori residual bundles

These are `Work.UBBInputs8.BoxSumBoundCore` / `Work.UBBInputs2.BoxSumBoundCanon` /
`Work.UBBInputs.BoxSumBound` / `Work.UBBInputs.SlidingSumData` verbatim, with the *only* change
being `Work.SmallBoxSliding.qLHSwordB ↦ Work.LocRepoint.qLHSwordB` and
`Work.SmallBoxSliding.chiMass ↦ Work.LocRepoint.chiMass`. -/

/-- **The repointed core bundle** — the mathematical content of FS `thm:smallbox` at the sliding
geometry, at the repointed localisation.  Its four fields are the genuine per-state residuals
(all of them at *unchanged* objects except `qLHSwordB`/`chiMass`):

* `Integrable (fun u => tBwordB … u Φ)` — the witness-dependent integrability of the kinetic
  word (at the `ε = 0` witness; see `Work.UBBInputs8.A.not_integrable_tBwordB_const`);
* `hlow` — the per-box lower bound on the discarded boxes;
* `hmass` — the discarded `χ`-mass bound;
* `hsum` — the per-box bound integrated over the good set (the count ↔ localised-density bridge).

The fields that round 8 *proved* (`hpot`, and the `qLHSwordB`-integrability) are **not** members:
here they are `HpotEqAll_holds` and `integrable_qLHSwordB_u`. -/
def BoxSumBoundCoreRep (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ),
      0 ≤ C ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      (∀ u : ℝ³, - C * chiMass M L d u
        ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
          + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u in (goodSet L d (dens N L))ᶜ, chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in goodSet L d (dens N L),
            (Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
              + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)))

/-- **The repointed canonical bundle** — `Work.UBBInputs2.BoxSumBoundCanon` at the repointed
layer, i.e. the per-box energy word `eBf` fixed to `tBwordB + qLHSwordB` and three of its fields
discharged (`hpot` by the telescoping equality, the `qLHSwordB`-integrability by the box-restricted
integrability of the integrand, the `χ`-mass integrability by `integrable_chiMass`).  Only
`hintt`, `hlowu`, `hmass`, `hsum` remain as per-state data. -/
def BoxSumBoundCanonRep (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ),
      0 ≤ C ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      (∀ u : ℝ³, - C * chiMass M L d u
        ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
          + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u in (goodSet L d (dens N L))ᶜ, chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in goodSet L d (dens N L),
            (Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
              + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)))

/-- **The repointed round-1 bundle** — `Work.UBBInputs.BoxSumBound` at the repointed layer. -/
def BoxSumBoundRep (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ) (eBf : ℝ³ → ℝ),
      0 ≤ C ∧
      (∀ u : ℝ³, eBf u ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
        + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u : ℝ³, qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
        ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
            (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      Integrable eBf ∧
      Integrable (fun u : ℝ³ => chiMass M L d u) ∧
      (∀ u : ℝ³, - C * chiMass M L d u ≤ eBf u) ∧
      ((∫ u in (goodSet L d (dens N L))ᶜ, chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in goodSet L d (dens N L), eBf u)

/-- **The repointed residual bundle of the sliding localisation** —
`Work.UBBInputs.SlidingSumData` at the repointed layer. -/
def SlidingSumDataRep (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ) (eBf : ℝ³ → ℝ),
      0 ≤ C ∧
      Work.SmallBoxTBWord.tBLocalisation N L d b ε c (Φ : X N → ℝ) ∧
      (∀ u : ℝ³, eBf u ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
        + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u : ℝ³, qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
        ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
            (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      Integrable eBf ∧
      Integrable (fun u : ℝ³ => chiMass M L d u) ∧
      (∀ u : ℝ³, - C * chiMass M L d u ≤ eBf u) ∧
      ((∫ u in (goodSet L d (dens N L))ᶜ, chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in goodSet L d (dens N L), eBf u)


/-! ## 7. The honest kinetic clause, and the `χ`-weighted carrier (round 9's repair)

Round 9 (`Submission/Work/UBBInputs9/README.md`) proved that the *plain-word* kinetic clause
`tBLocalisation` — the `hloc` field of every a-priori list of rounds 2/7/8 — is **false**: its
witnesses are the slot-indicator state (non-smooth; `A/not_KineticLocalisation*`) and, decisively,
a *smooth* `L²`-normalised state (`B/proj_defect`, `B/unproj_defect`: at the `ε = c = 0` witness
`kinWord + (b/2ℓ²)cnPlus < ∫_u 𝒯_{B(u)}`), because the sliding family's `u`-partition is
`∫_u χ_{B(u)}(x)² du = χ(x/ℓ)²` with `chiSup² > 4/3`, not `1`.  Hence **every** a-priori list that
carries `hloc : KineticLocalisation` is uninhabited and its headline vacuous, *independently of the
repoint*.

Round 9's honest clause therefore changes **the word** (to the `χ`-weighted Dirichlet word — at this
chapter's layer the repointed `kinWordChi`, whose formula is round 9's `kinWordW`) and restricts
**the state class** (to smooth states, on which the word is the honest Dirichlet form).  That is
`tBLocalisationWRep`/`KineticLocalisationWSmRep` below; it is a *residual* (FS's `eq:BSsliding2`
cited from Bratteli–Solovej Thm 3.10, i.e. round 9's `BSslidingKin`), and no witness is known
against it.

Consequently the a-priori chain's conclusion is at the `χ`-weighted carrier:
`EnergyWordW`/`WordDensW` are the corpus's `EnergyWord`/`WordDens` with `kinWord ↦ kinWordChi` (the
potential word, being localisation-independent, is the *same* corpus global word).  The window
arithmetic (`Work.SmallBoxSliding.cnPlus_and_R_le`, the core of `aprioriNPlusCov_of_dlSlideCov`) is
generic in the energy word, so the re-run is mechanical — see `Clauses.lean`.
-/

/-- **The honest kinetic clause at the repointed layer** (round 9's `tBLocalisationW`, with the
corpus box word `tBwordB` that the delivered sliding assembly and the per-box bundle both use):
`(b/2ℓ²)·n₊ + ∫_u 𝒯_{B(u)} ≤ kinWordChi`, i.e. the right-hand side is the `χ(·/ℓ)²`-weighted
Dirichlet word — the word the sliding family actually telescopes to
(`Work.LocRepoint.sboxEBWord_integral_u`). -/
def tBLocalisationWRep (M : ℕ) (L d b ε c : ℝ) {N : ℕ} (Φ : X N → ℝ) : Prop :=
  (b / (2 * L ^ 2)) * cnPlus L Φ
    + (∫ u : ℝ³, Work.SmallBoxTBWord.tBwordB N L d ε c u Φ) ≤ kinWordChi N M L Φ

/-- The honest kinetic clause, restricted to the smooth state class (round 9's
`KineticLocalisationWSm`). -/
def KineticLocalisationWSmRep (M : ℕ) (d b : ℝ) : Prop :=
  ∀ (N : ℕ) (L ε c : ℝ) (Φ : X N → ℝ), ContDiff ℝ (⊤ : ENat) Φ → tBLocalisationWRep M L d b ε c Φ

/-- **The `χ`-weighted energy word**: the corpus `EnergyWord` with `kinWord ↦ kinWordChi`
(the potential word is the corpus global word `qLHSword (wPairC …)`, unchanged by the repoint). -/
noncomputable def EnergyWordW (N : ℕ) (M : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (Φ : CSBox N L) : ℝ :=
  (kinWordChi N M L (Φ : X N → ℝ)
      + qLHSword (N := N) L μ (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ))
    / (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)

/-- The `χ`-weighted energy *density* (the corpus `WordDens` at `kinWordChi`). -/
noncomputable def WordDensW (N : ℕ) (M : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (Φ : X N → ℝ) : ℝ :=
  (kinWordChi N M L Φ + qLHSword (N := N) L μ (wPairC L v) (wPairC L (g0 v h)) Φ)
    / (L ^ 3 * ∫ x in abox N L, (Φ x) ^ 2)

/-- **FS `eq:BSsliding2` at the `χ`-weighted carrier, norm-one form** (the analogue of
`Work.UBBInputs.SlidingRawNorm`). -/
def SlidingRawNormW (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDensW N M L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
      - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
      ≤ kinWordChi N M L (Φ : X N → ℝ)
        + qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)

/-- The norm-one form of the `χ`-weighted sliding inequality (the analogue of
`Work.UBBInputs.DLSlideNorm`). -/
def DLSlideNormW (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDensW N M L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    R' + (b / (2 * L ^ 2)) * cnPlus L (Φ : X N → ℝ)
      - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
      ≤ (kinWordChi N M L (Φ : X N → ℝ)
        + qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ))
        / sqNormN N L (Φ : X N → ℝ)

/-- The covariant form of the `χ`-weighted sliding inequality (the analogue of
`Work.UBBInputs.DLSlideCov`; the low-state condition is at the `χ`-weighted density). -/
def DLSlideCovW (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    WordDensW N M L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    R' + (b / (2 * L ^ 2)) * (cnPlus L (Φ : X N → ℝ) / sqNormN N L (Φ : X N → ℝ))
      - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ))
      ≤ EnergyWordW N M L (dens N L) v h Φ

/-- **The covariant a-priori `n₊` window at the `χ`-weighted carrier** — the analogue of
`Work.UBBInputs.AprioriNPlusCov`; the window `W` is *the same* FS window (it does not involve the
kinetic word). -/
def AprioriNPlusCovW (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ : ℝ) (M : ℕ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    WordDensW N M L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    cnPlus L (Φ : X N → ℝ) ≤ W N L * sqNormN N L (Φ : X N → ℝ)

/-- **The repointed core bundle at the `χ`-weighted carrier**: `BoxSumBoundCoreRep` with the
low-state hypothesis read at `WordDensW`. -/
def BoxSumBoundCoreRepW (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDensW N M L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ),
      0 ≤ C ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      (∀ u : ℝ³, - C * chiMass M L d u
        ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
          + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u in (goodSet L d (dens N L))ᶜ, chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in goodSet L d (dens N L),
            (Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
              + qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)))

/-- **The repointed (A) list, at the honest kinetic clause** — the list a caller can actually
instantiate:

* `hloc` is the **honest** kinetic clause `tBLocalisationWRep` restricted to smooth states
  (round 9's repair: the plain-word `tBLocalisation` is *false*, both at an indicator witness and
  at a smooth L²-normalised witness `B/proj_defect`, so keeping it would make this list
  uninhabited and every headline from it vacuous);
* `hcore : BoxSumBoundCoreRepW` is the per-state bundle with its low-state hypothesis read at the
  `χ`-weighted density `WordDensW` — the carrier the sliding sum actually telescopes to;
* the potential-localisation field is **absent**: at the repointed kernels FS `lem:LocPotential` is
  the equality `Work.LocRepoint.HpotEqAll_holds` (`hLP` is deleted, not restated).

What remains of the paper's a-priori side is then exactly: the honest kinetic residual (FS
`eq:BSsliding2`/BS Thm 3.10 = round 9's `BSslidingKin`) and the per-state fields of FS
`thm:smallbox`. -/
structure AprioriClauses8Rep (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ) (d M : ℕ)
    (R0 : ℝ) : Prop where
  hb : 0 < b
  ha : 0 ≤ a v
  hR' : 0 ≤ R'
  hM : 1 ≤ M
  hd : (0 : ℝ) < (d : ℝ)
  hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0
  hR0 : 0 < R0
  hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16
  hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0
  hv1 : MemLp v 1
  hloc : KineticLocalisationWSmRep M (d : ℝ) b
  hcore : BoxSumBoundCoreRepW v h b K_B R' J ε₀ d M

end Work.LocRepoint
