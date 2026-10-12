import ChallengeDeps
import Submission.Work.SmallBoxA0.KinPDefs
import Submission.Work.SmallBoxBridge.Cauchy.pModeForm_le_pDiagForm
import Submission.Work.SmallBoxBridge.ModeIdent.kinPWord_eq_pModeForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `KinPSuperadd` — the mode-level superadditivity of the small-box kinetic words

## Why this chapter exists

The FS `thm:smallbox` argument, and the corpus chain that consumes it
(`SboxEB.eB_superadd_chosen`, `SboxEBGroup.eB_group_superadd_chosen`,
`SmallBoxTwoArm`, `EBPerState`, the `n″`-arm of `SmallBoxDLBound`), rests on the
*grouping trick*: at a fixed chemical potential `μ` and box side `s`, the
`n`-particle small-box ground energy is **superadditive** in the particle
number,

    e(N₁ + N₂) ≥ e(N₁) + e(N₂)      (and hence n = m·n′ + n″),

because an `(N₁+N₂)`-particle state can be split into two *groups of labels*,
the (nonnegative) cross-group pair interaction dropped, and each group bounded
by its own ground energy.  The mechanism that makes this work is that the
**kinetic word of the energy is a SUM of ONE-PARTICLE forms over the
particles**: then the two groups decouple, each group's contribution is a slice
integral of the other's, and the infimum can be taken group by group.

`Work.SmallBoxA0`'s SESSION-290 report (README §30) names the ONE open
obligation of the re-pointed (`𝒯_B`, `kinPWord`) energy: the corpus's
`kinPWord` is built from `modeP`, a **SQUARE OF A SUM** over the particles
(`modeP s g Φ = (s³)⁻¹∫(boxOp s 1 g Φ)²`, `boxOp s 1 g Φ = Σ_i ∫g·Φ(x_{i↦z})`),
and a square of a sum does **not** decompose over particle groups — its
cross-group term `2(Σ_{i∈G₁}A_i)(Σ_{j∈G₂}A_j)` has no sign.  This chapter
settles that obligation *as mathematics*:

* `SlotSplit s K` (`Defs.lean`) is the **exact structural property** an energy
  word `K` must have for the grouping trick — the block decomposition
  `K(N₁+N₂)Φ = ∫_w K N₁(slice_w Φ) + ∫_u K N₂(slice'_u Φ)` (plus the
  slice-integrability that makes the two integrals meaningful).
* `Engine.lean` proves the **grouping theorem** `slotEB_superadd`: `SlotSplit`
  plus the elementary Rayleigh inequality for `K` *imply* the superadditivity
  of the corresponding small-box ground energy.  This is the whole mechanism of
  the FS group trick, isolated and reusable.
* `KinWord.lean`, `CnPlus.lean`, `DiagSplit.lean` prove `SlotSplit` for
  `kinWord` (the corpus's delivered word — recovering `eB_superadd_chosen`),
  for `cnPlus`, and for the **faithful one-particle-sum transcription** of FS's
  `𝒯_B` (`pDiagForm s F = Σ_i (one-particle form of slot i)`, the corpus's
  `Σ_i Q_iχ_iF(√−Δ_i)χ_iQ_i`).
* `Obstruction.lean` proves the **negative result**: `modeP`-based words do
  **not** satisfy `SlotSplit`; the failure is exactly the cross-group pair
  count, with the deficiency `2N₁N₂(∫g)²(s³)^{N−1}` made explicit, and it is
  exhibited for the corpus's own modes `qModeRe s p` as well.

See `README.md` for the ledger, and `Residual.lean` for the precise residual of
the delivered `Submission.BoseGases.smallbox_block_bound` /
`smallbox_state_block_bound` and the roadmap.

## Conventions

* `X N = Fin N → ℝ³`, `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `abox N s` the centred
  box of side `s` in `N` slots, `acube s = abox 1 s`.
* `mergeBlock N₁ N₂ (u,w) : X (N₁+N₂)` is the block concatenation
  (`Submission.SubaddVol`); `Fin.castAdd N₂` is the first-block embedding and
  `Fin.natAdd N₁` the second-block embedding.
* A **word** is a family `K : ∀ N, (X N → ℝ) → ℝ`.  `K N Φ` is the `K`-energy
  of the state `Φ`.
* A slice: for `Φ : X (N₁+N₂) → ℝ` and `w : X N₂`, the first-block slice is
  `fun u => Φ (mergeBlock N₁ N₂ (u,w))`; for `u : X N₁` the second-block slice
  is `fun w => Φ (mergeBlock N₁ N₂ (u,w))`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  The structural property: block-splittability of a word -/

/-- **Block-splittability (`SlotSplit`)** — the exact structural property of a
kinetic word `K` that the FS grouping trick needs.

A word `K : ∀ N, (X N → ℝ) → ℝ` is `SlotSplit` at box side `s` when, for every
block decomposition `N₁ + N₂` of the particle number, the `(N₁+N₂)`-particle
word evaluated at a smooth `Φ` equals the `w`-slice integral of the
`N₁`-particle word on the first group plus the `u`-slice integral of the
`N₂`-particle word on the second group:

    K (N₁+N₂) Φ
      = ∫_{w ∈ abox N₂ s} K N₁ (fun u ↦ Φ (merge(u,w)))
        + ∫_{u ∈ abox N₁ s} K N₂ (fun w ↦ Φ (merge(u,w))) ,

together with the slice-integrability of each of the two summands as a function
of the frozen variable (which is what makes the two integrals meaningful and
the infimum step of the grouping argument legal).

This is the slice form of "`K` is a sum of one-particle forms over the
particles": a sum `Σ_i T_i` of one-slot operators commutes with the block
decomposition, and the slot integrals over the *other* group's coordinates are
exactly the slice integrals.  `DiagSplit.slotSplit_pDiagForm` proves it for
FS's faithful one-particle-sum transcription of `𝒯_B`;
`Obstruction.not_slotSplit_modeP` *refutes* it for the `modeP`-based
(square-of-a-sum) transcription. -/
structure SlotSplit (s : ℝ) (K : ∀ N : ℕ, (X N → ℝ) → ℝ) : Prop where
  /-- the block decomposition of the word, on smooth states -/
  split : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
    K (N1 + N2) Φ =
      (∫ w in abox N2 s, K N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
      + (∫ u in abox N1 s, K N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))
  /-- first-block slice integrability -/
  int₁ : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
    IntegrableOn (fun w : X N2 => K N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
      (abox N2 s) volume
  /-- second-block slice integrability -/
  int₂ : ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
    IntegrableOn (fun u : X N1 => K N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))
      (abox N1 s) volume

/-- **Block-superadditivity (`BlockSuperadd`)** — the ONE-SIDED form of
`SlotSplit`, and *exactly* what the FS grouping trick consumes.

The grouping argument compares the `(N₁+N₂)`-particle word with the two slice
integrals of the block words; it never needs the identity, only the inequality

    ∫_w K N₁ (slice_w Φ) + ∫_u K N₂ (slice'_u Φ)  ≤  K (N₁+N₂) Φ .

`SlotSplit.blockSuperadd` shows `SlotSplit ⟹ BlockSuperadd`, so every positive
instance of the chapter gives this.  Its value is the SHARP form of the
obstruction: the `modeP` words FAIL `BlockSuperadd`
(`Obstruction.not_blockSuperadd_modePGen`,
`Obstruction.not_blockSuperadd_pModeContent`) — i.e. the superadditivity the
grouping needs is genuinely false for the square-of-a-sum word, not merely
undischarged. -/
def BlockSuperadd (s : ℝ) (K : ∀ N : ℕ, (X N → ℝ) → ℝ) : Prop :=
  ∀ ⦃N1 N2 : ℕ⦄ (Φ : X (N1 + N2) → ℝ), ContDiff ℝ ∞ Φ →
    (∫ w in abox N2 s, K N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
      + (∫ u in abox N1 s, K N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))
    ≤ K (N1 + N2) Φ

/-- `SlotSplit` implies the one-sided form `BlockSuperadd` (the grouping trick's
requirement). -/
lemma SlotSplit.blockSuperadd {s : ℝ} {K : ∀ N : ℕ, (X N → ℝ) → ℝ}
    (hK : SlotSplit s K) : BlockSuperadd s K := by
  intro N1 N2 Φ hΦ
  rw [hK.split Φ hΦ]

lemma SlotSplit.split_apply {s : ℝ} {K : ∀ N : ℕ, (X N → ℝ) → ℝ} (hK : SlotSplit s K)
    {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    K (N1 + N2) Φ =
      (∫ w in abox N2 s, K N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
      + (∫ u in abox N1 s, K N2 (fun w => Φ (mergeBlock N1 N2 (u, w)))) :=
  hK.split Φ hΦ

/-- The sum of two `SlotSplit` words is `SlotSplit`. -/
lemma SlotSplit.add {s : ℝ} {K L : ∀ N : ℕ, (X N → ℝ) → ℝ}
    (hK : SlotSplit s K) (hL : SlotSplit s L) : SlotSplit s (fun N Φ => K N Φ + L N Φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N1 N2 Φ hΦ
    have h1 := hK.split Φ hΦ
    have h2 := hL.split Φ hΦ
    have hA : (∫ w in abox N2 s, ((K N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
        + (L N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))))
        = (∫ w in abox N2 s, K N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
          + (∫ w in abox N2 s, L N1 (fun u => Φ (mergeBlock N1 N2 (u, w)))) :=
      integral_add (hK.int₁ Φ hΦ) (hL.int₁ Φ hΦ)
    have hB : (∫ u in abox N1 s, ((K N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))
        + (L N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))))
        = (∫ u in abox N1 s, K N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))
          + (∫ u in abox N1 s, L N2 (fun w => Φ (mergeBlock N1 N2 (u, w)))) :=
      integral_add (hK.int₂ Φ hΦ) (hL.int₂ Φ hΦ)
    rw [h1, h2, hA, hB]
    ring
  · intro N1 N2 Φ hΦ
    exact (hK.int₁ Φ hΦ).add (hL.int₁ Φ hΦ)
  · intro N1 N2 Φ hΦ
    exact (hK.int₂ Φ hΦ).add (hL.int₂ Φ hΦ)

/-- A constant multiple of a `SlotSplit` word is `SlotSplit`. -/
lemma SlotSplit.const_mul {s : ℝ} {K : ∀ N : ℕ, (X N → ℝ) → ℝ} (c : ℝ)
    (hK : SlotSplit s K) : SlotSplit s (fun N Φ => c * K N Φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N1 N2 Φ hΦ
    rw [hK.split Φ hΦ]
    have hA : (∫ w in abox N2 s, c * K N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
        = c * (∫ w in abox N2 s, K N1 (fun u => Φ (mergeBlock N1 N2 (u, w)))) :=
      integral_const_mul c _
    have hB : (∫ u in abox N1 s, c * K N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))
        = c * (∫ u in abox N1 s, K N2 (fun w => Φ (mergeBlock N1 N2 (u, w)))) :=
      integral_const_mul c _
    rw [hA, hB]
    ring
  · intro N1 N2 Φ hΦ
    exact (hK.int₁ Φ hΦ).const_mul c
  · intro N1 N2 Φ hΦ
    exact (hK.int₂ Φ hΦ).const_mul c

/-! ## 2  The block energy and its infimum

The small-box energy of a word `K` at scale `s`, chemical potential `μ` and
kernels `(w, w₁)` is `K N Φ` plus the `qLHSword` potential word; the
`eB`-level object is its infimum over the corpus's trial space `CSBox N s`. -/

/-- The **block energy** of the word `K`: the kinetic word plus the
`qLHSword` potential word (written as the integral of `Φ²` against the
diagonal density `qLHSden`). -/
noncomputable def blockE (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (K : ∀ N : ℕ, (X N → ℝ) → ℝ) (N : ℕ) (Φ : X N → ℝ) : ℝ :=
  K N Φ + ∫ x in abox N s, (Φ x) ^ 2 * qLHSden N s μ w w1 x

/-- The **block energy as the corpus's `sboxE` with `kinWord` replaced by the
word `K`**. -/
lemma blockE_eq (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (K : ∀ N : ℕ, (X N → ℝ) → ℝ)
    (N : ℕ) (Φ : X N → ℝ) :
    blockE s μ w w1 K N Φ = K N Φ + qLHSword (N := N) s μ w w1 Φ := by
  rw [blockE, qLHSword_eq_integral_qLHSden]

/-- The **`eB`-level ground energy** of the word `K`: the infimum of the
`blockE`-quotients over the corpus's smooth trial states `CSBox N s`.  With
`K := fun N Φ => kinWord N s Φ` this is exactly `SboxEB.eB`. -/
noncomputable def slotEB (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (K : ∀ N : ℕ, (X N → ℝ) → ℝ) (N : ℕ) : ℝ :=
  ⨅ Φ : CSBox N s,
    blockE s μ w w1 K N (Φ : X N → ℝ) / (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2)

/-- `slotEB` at `K := kinWord` is the corpus's `eB` (definitionally, after
unfolding `blockE` and `sboxE`). -/
lemma slotEB_kinWord_eq_eB (N : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    slotEB s μ (wPairC s v) (wPairC s (g0 v h)) (fun N Φ => kinWord N s Φ) N
      = eB N s μ v h := by
  rfl

end Work.KinPSuperadd

namespace Work.KinPSuperadd

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 3  The `modeP` word at general particle number, and the two candidate
transcriptions of FS's `𝒯_B`

The corpus's `modeP s g Ψ` is indexed by `X (n+1) → ℝ` (D1's convention, `n+1`
particles).  For the block/superadditivity analysis it is convenient to have the
same object at a general particle number; the two agree definitionally at
`N = n+1`. -/

/-- The per-mode content `modeP` at general particle number `N` — the corpus's
`modeP` (`X (n+1) → ℝ`) transported to `X N → ℝ`. -/
noncomputable def modePGen (s : ℝ) (g : ℝ³ → ℝ) (N : ℕ) (Ψ : X N → ℝ) : ℝ :=
  (s ^ 3)⁻¹ * ∫ x in abox N s, (boxOp s (fun _ => (1 : ℝ)) g Ψ x) ^ 2

/-- `modePGen` at `N = n+1` is the corpus's `modeP` (definitional). -/
lemma modePGen_eq_modeP {s : ℝ} {n : ℕ} (g : ℝ³ → ℝ) (Ψ : X (n + 1) → ℝ) :
    modePGen s g (n + 1) Ψ = modeP s g Ψ := rfl

/-- **The `modeP` word as a word in the `SlotSplit` sense** — the transcription
of FS's `𝒯_B` spectral half that the corpus's D1 chain actually uses, i.e. the
SQUARE OF A SUM `Σ_i A_i` of the occupation of a single mode.  It is this word
whose block-splittability is refuted by `Obstruction.not_slotSplit_modePGen`. -/
noncomputable def modePWord (s : ℝ) (g : ℝ³ → ℝ) : ∀ N : ℕ, (X N → ℝ) → ℝ :=
  fun N Ψ => modePGen s g N Ψ

/-- **The DIAGONAL (one-particle-sum) transcription** of the same per-mode
content: `Σ_i ‖A_i‖²` instead of `‖Σ_i A_i‖²`.  This is the quadratic form of
the one-body operator `Q_Bχ_B|qMode⟩⟨qMode|χ_BQ_B` summed over slots — the
faithful transcription of FS's one-particle `𝒯_B`. -/
noncomputable def pModeDiagonalWord (s : ℝ) (p : ℝ³) : ∀ N : ℕ, (X N → ℝ) → ℝ :=
  fun N Ψ => pModeDiagonal s p Ψ

/-! ## 4  The faithful (`pDiagForm`, one-particle-sum) small-box energy

`kinPEnergy` (`Work.SmallBoxA0.KinPDefs`) is `cgap·cnPlus + kinPWord + qLHSword`
with `kinPWord = pModeForm s (fsKinCoeff c₀)` a SQUARE OF A SUM.  The faithful
transcription replaces `pModeForm` (square of a sum over slots) by `pDiagForm`
(sum of the slot diagonal), which is the quadratic form of FS's one-particle
`𝒯_B = Q_Bχ_B[√−Δ−c]₊²χ_BQ_B` summed over the particles.  Everything else —
the `ε_T`-gap term, the potential word, the trial space, the bundles — is
unchanged. -/

/-- The **faithful (`pDiagForm`) slot word**: `cgap·cnPlus + pDiagForm s F`. -/
noncomputable def diagSlotWord (s : ℝ) (c₀ cgap : ℝ) : ∀ N : ℕ, (X N → ℝ) → ℝ :=
  fun N Φ => cgap * cnPlus s Φ + pDiagForm s (fsKinCoeff c₀) Φ

/-- The **faithful (`pDiagForm`) small-box energy** at particle count `n+1`,
mirroring `Work.SmallBoxA0.kinPEnergy` verbatim with `kinPWord s c₀` replaced by
`pDiagForm s (fsKinCoeff c₀)`. -/
noncomputable def diagKinPEnergy (n : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (c₀ cgap : ℝ) (Φ : X (n + 1) → ℝ) : ℝ :=
  diagSlotWord s c₀ cgap (n + 1) Φ + qLHSword (N := n + 1) s μ w w1 Φ

/-- `diagKinPEnergy` is `kinPEnergy` with the square-of-a-sum word `kinPWord`
replaced by the sum-of-squares word `pDiagForm`. -/
lemma diagKinPEnergy_eq_slotEB (n : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (c₀ cgap : ℝ) (Φ : X (n + 1) → ℝ) :
    diagKinPEnergy n s μ w w1 c₀ cgap Φ
      = blockE s μ w w1 (diagSlotWord s c₀ cgap) (n + 1) Φ :=
  rfl

/-- The **`eB`-level faithful small-box ground energy** (mirror of
`Work.SmallBoxA0.kinPeB` with the faithful word). -/
noncomputable def diagKinPeB (n : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : ℝ :=
  ⨅ Φ : CSBox (n + 1) s,
    diagKinPEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c₀ cgap (Φ : X (n + 1) → ℝ) /
      (∫ x in abox (n + 1) s, ((Φ : X (n + 1) → ℝ) x) ^ 2)

/-- `diagKinPeB` is the `slotEB`-level object of the faithful word. -/
lemma diagKinPeB_eq_slotEB (n : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) :
    diagKinPeB n s μ v h c₀ cgap
      = slotEB s μ (wPairC s v) (wPairC s (g0 v h)) (diagSlotWord s c₀ cgap) (n + 1) :=
  rfl

end Work.KinPSuperadd
