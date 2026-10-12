import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.boxMarginDefs
import Submission.Work.BoseFixB1B.fibreWord_smul
import Submission.Work.BoseFixB1B.permInvariant_slotFibreState
import Submission.Work.FibreWord.SliceAE
import Submission.Work.FibreWord.fibPiece_ae_eq_zero_of_fibMass_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sectorCountBoxAux` — the vocabulary and the assembly of the
# arity/count reduction at FS's box normaliser

Holder: `Work.BoseFixB1B.repairedPerSectorBoundG_of_sectorCountBox`.

## What this module is for

The target `Work.BoseFixB1B.RepairedPerSectorBoundG v h R` follows from the count-indexed core
`Work.BoseFixB1B.SectorCountSmallboxBox v h` by

1. **opening the core** — `SectorCountBodyBox` (the inequality at fixed `(ε₀, c, C)`),
   `CountCoreAt` (the same inequality read at an arbitrary count `k` and an arbitrary threshold
   `T`, for **smooth** symmetric normalised in-box states);
2. **the sharp extension** — the core is stated for `ContDiff` states, while the fibre of a slot
   piece is `1_{B(u)^{S.card}}·(smooth fibre)`; `SharpCountCoreAt` is the same inequality for the
   sharp state, and `sharpCountCoreAt_of_countCoreAt` (delegated) is the passage.  This is the only
   analytic content of the reduction;
3. **the fibre assembly** — for each slot set `S` of the sector `k`, the word of the slot piece is
   the `y`-integral of the word of its fibre (`Work.SlotWord.WordFibreFactorisation`, PROVED), the
   slot mass is the `y`-integral of the fibre masses
   (`Work.SlotWord.integral_slotFibreMassReal_piece_eq_slotMass`, PROVED), so the per-slot bound
   `slotMass_S·T ≤ word(slotPiece_S)` follows from the per-fibre sharp bound (`slotBound_of_sharp`),
   and summing over `S` of cardinality `k` with the sector additivity
   (`sectorPiece_word_eq_sum_slot_piece`, delegated) gives
   `sectorMass_k·T ≤ word(sectorPiece_k Φ)`.

## Files and obligations

| name | content | status |
|---|---|---|
| `SectorCountBodyBox` | the core at fixed `(ε₀, c, C)` | definition |
| `countCoreAt_of_bodyBox` | the core ⟹ `CountCoreAt` at the threshold `PBThresh` | proved here |
| `SharpCountCoreAt` | the sharp (indicator-times-smooth) form of the core | definition |
| `sharpCountCoreAt_of_countCoreAt` | **the sharp extension** | delegated |
| `slotBound_of_sharp` | per-slot set: `slotMass·T ≤ word(slotPiece)` | proved here |
| `sectorPiece_word_eq_sum_slot_piece` | the sector additivity of the word | delegated |
| `repairedPerSectorBoundG_of_slotBounds` | per-sector assembly | proved here |

The geometric inputs of the sharp extension (`SmoothCutoffFamily`, `CollarVolumeLe`,
`ChiMarginLe`) are named here so that the sharp extension is a statement about analysis only.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open Classical

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The count-indexed core, opened -/

/-- **The body of the count-indexed core at fixed `(ε₀, c, C)`** — `SectorCountSmallboxBox` with
the existential quantifiers opened.  For every admissible `μ`, every particle number `n`, every
smooth symmetric `n`-particle state all of whose particles lie in the sliding box `B(u)` and which
is normalised, the count-indexed inequality of FS `thm:smallbox` holds. -/
def SectorCountBodyBox (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ε₀ c C : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
      u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n (PBℓ v μ))),
        (Φ : X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ PBB v μ u) →
      (∫ x in abox n (PBℓ v μ), ((Φ : X n → ℝ) x) ^ 2) = 1 →
      (c * psiWeight 1 μ ((n : ℝ) / PBBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
        - C * (μ ^ 2 * (a v) * PBΓ v μ * PBW h μ u + μ * (a v))
      ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
            (Work.BoseFixB1.sbCut μ (a v)) u (Φ : X n → ℝ)
        + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u (Φ : X n → ℝ)

/-- **Opening the core.** -/
theorem exists_bodyBox_of_sectorCountSmallboxBox {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    (hS : SectorCountSmallboxBox v h) :
    ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧ SectorCountBodyBox v h ε₀ c C := by
  obtain ⟨ε₀, c, C, hε₀, hc0, hc14, hC0, hbody⟩ := hS
  exact ⟨ε₀, c, C, hε₀, hc0, hc14, hC0, hbody⟩

/-- **The count-core threshold** — the left-hand side of the core at the count `k`, the box `u` and
the constants `c, C`.  (No `ε₀`: the threshold itself does not see the admissibility.) -/
noncomputable def PBThresh {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (c C μ : ℝ) (u : E3)
    (k : ℕ) : ℝ :=
  (c * psiWeight 1 μ ((k : ℝ) / PBBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
    - C * (μ ^ 2 * (a v) * PBΓ v μ * PBW h μ u + μ * (a v))

/-- **The count core at an arbitrary count `k` and threshold `T`.**  This is the hypothesis of the
sharp extension: for every smooth symmetric normalised in-box `k`-particle state, the threshold `T`
is dominated by the sliding word.  (The core's own instantiation of `T` is `PBThresh h c C μ u k`.) -/
def CountCoreAt {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (L d ε c μ : ℝ) (u : E3)
    (k : ℕ) (T : ℝ) : Prop :=
  ∀ Ψ : X k → ℝ, ContDiff ℝ (⊤ : ENat) Ψ → PermInvariant k Ψ → Ψ ≠ 0 →
    (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox k L)),
      Ψ x ≠ 0 → ∀ i : Fin k, x i ∈ dlBox L d u) →
    (∫ x in abox k L, (Ψ x) ^ 2) = 1 →
    T ≤ Work.SlotWord.fibreWord h M k L d ε c μ u Ψ

/-- **The core gives the count core at the count `k`.** -/
theorem countCoreAt_of_bodyBox {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ε₀ c C : ℝ}
    (hB : SectorCountBodyBox v h ε₀ c C) {μ : ℝ} (hμ : Work.BoseBoxFix.Adm v ε₀ μ)
    {u : E3} (hu : u ∈ goodSet (PBℓ v μ) (PBd v μ) μ) (k : ℕ) :
    CountCoreAt h (PBM v μ) (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (a v)) μ u k (PBThresh h c C μ u k) := by
  intro Ψ hΨcd hΨperm hΨne hsupp hnorm
  have h := hB μ hμ k ⟨Ψ, hΨcd, hΨperm, hΨne⟩ u hu hsupp hnorm
  simpa only [PBThresh, Work.SlotWord.fibreWord] using h

/-! ## 2. The sharp state and the sharp core -/

/-- **The sharp in-box state** `1_{B^k}·ψ`: the smooth fibre `ψ` truncated to the box `B^k`. -/
def sharpBoxState {k : ℕ} (B : Set E3) (ψ : X k → ℝ) : X k → ℝ :=
  (Work.PerSector.slotBox (ι := Fin k) B).indicator ψ

theorem sharpState_apply {k : ℕ} (B : Set E3) (ψ : X k → ℝ) (x : X k) :
    sharpBoxState B ψ x = if ∀ i : Fin k, x i ∈ B then ψ x else 0 := by
  classical
  by_cases h : ∀ i : Fin k, x i ∈ B
  · rw [sharpBoxState, Set.indicator_of_mem (by simpa [Work.PerSector.slotBox] using h), if_pos h]
  · rw [sharpBoxState, Set.indicator_of_notMem (by simpa [Work.PerSector.slotBox] using h), if_neg h]

theorem sharpState_eq_self_of_mem {k : ℕ} {B : Set E3} {ψ : X k → ℝ} {x : X k}
    (h : ∀ i : Fin k, x i ∈ B) : sharpBoxState B ψ x = ψ x := by
  rw [sharpState_apply, if_pos h]

theorem sharpState_eq_zero_of_notMem {k : ℕ} {B : Set E3} {ψ : X k → ℝ} {x : X k}
    (h : ¬ ∀ i : Fin k, x i ∈ B) : sharpBoxState B ψ x = 0 := by
  rw [sharpState_apply, if_neg h]

theorem sharpState_zero {k : ℕ} (B : Set E3) : sharpBoxState B (0 : X k → ℝ) = 0 := by
  funext x; rw [sharpBoxState]; simp

/-- **The sharp count core**: the count inequality for the sharp (indicator-times-smooth) in-box
states.  This is the form in which the core is consumed by the fibre assembly; it is *not* an
instance of `CountCoreAt`, whose states must be `ContDiff`. -/
def SharpCountCoreAt {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (L d ε c μ : ℝ) (u : E3)
    (k : ℕ) (T : ℝ) : Prop :=
  ∀ ψ : X k → ℝ, ContDiff ℝ (⊤ : ENat) ψ → PermInvariant k ψ →
    (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) * T
      ≤ Work.SlotWord.fibreWord h M k L d ε c μ u (sharpBoxState (dlBox L d u) ψ)

/-! ## 3. The geometric inputs of the sharp extension -/

/-- **A specified smooth cutoff family for the sliding box**: `γ δ` is smooth, takes values in
`[0,1]`, is supported in `B(u)`, equals `1` on the inner box `{boxMargin ≥ δ}` and has
`‖fderiv (γ δ)‖ ≤ K/δ`. -/
def IsCutFamily (L d : ℝ) (u : E3) (K : ℝ) (γ : ℝ → E3 → ℝ) : Prop :=
  0 ≤ K ∧ ∀ δ : ℝ, 0 < δ →
    ContDiff ℝ (⊤ : ENat) (γ δ) ∧ tsupport (γ δ) ⊆ dlBox L d u ∧
    (∀ x, 0 ≤ γ δ x ∧ γ δ x ≤ 1) ∧
    (∀ x, boxMargin L d u x ≥ δ → γ δ x = 1) ∧
    (∀ x, ‖fderiv ℝ (γ δ) x‖ ≤ K / δ)

/-- **The existence form of the smooth cutoff family** (the geometric input (F1')). -/
def SmoothCutoffFamily (L d : ℝ) (u : E3) (K : ℝ) : Prop :=
  ∃ γ : ℝ → E3 → ℝ, IsCutFamily L d u K γ

/-- **The product approximation** `(∏_i γ(x_i))·ψ` of the sharp state `1_{B^k}ψ`: for `γ = γ_δ`
the in-box smooth approximant of the sharp fibre. -/
def cutProd {k : ℕ} (γ : E3 → ℝ) (ψ : X k → ℝ) : X k → ℝ :=
  fun x => (∏ i : Fin k, γ (x i)) * ψ x

theorem cutProd_apply {k : ℕ} (γ : E3 → ℝ) (ψ : X k → ℝ) (x : X k) :
    cutProd γ ψ x = (∏ i : Fin k, γ (x i)) * ψ x := rfl

/-- The product approximation is dominated by the sharp state: for `0 ≤ γ ≤ 1` with
`tsupport γ ⊆ B` and `x` in the box, `|cutProd γ ψ x| ≤ ψ x`, and off the box both are
`0`.  In particular the square of the approximant is dominated by the square of the sharp state. -/
theorem cutProd_sq_le_sharp {k : ℕ} {B : Set E3} {γ : E3 → ℝ} {ψ : X k → ℝ}
    (hγ01 : ∀ x, 0 ≤ γ x ∧ γ x ≤ 1) (hγsupp : tsupport γ ⊆ B) (x : X k) :
    (cutProd γ ψ x) ^ 2 ≤ (sharpBoxState B ψ x) ^ 2 := by
  classical
  have hzero_of_notMem : ∀ z : E3, z ∉ B → γ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (hγsupp (subset_tsupport γ (Function.mem_support.mpr hne)))
  by_cases hx : ∀ i : Fin k, x i ∈ B
  · have hnn : 0 ≤ ∏ i : Fin k, γ (x i) := Finset.prod_nonneg (fun i _ => (hγ01 (x i)).1)
    have hle1 : (∏ i : Fin k, γ (x i)) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => (hγ01 (x i)).1) (fun i _ => (hγ01 (x i)).2)
    have hsq : (∏ i : Fin k, γ (x i)) ^ 2 ≤ 1 := by nlinarith
    rw [sharpState_eq_self_of_mem hx]
    calc (cutProd γ ψ x) ^ 2
        = (∏ i : Fin k, γ (x i)) ^ 2 * (ψ x) ^ 2 := by rw [cutProd_apply]; ring
      _ ≤ 1 * (ψ x) ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (ψ x) ^ 2 := by ring
  · rw [sharpState_eq_zero_of_notMem hx]
    push_neg at hx
    obtain ⟨i, hi⟩ := hx
    rw [cutProd_apply, Finset.prod_eq_zero (Finset.mem_univ i) (hzero_of_notMem (x i) hi)]
    simp

/-- **The linear collar bound**: the volume of the part of the support of the sliding window whose
box margin is `< δ` is `O(δ)`. -/
def CollarVolumeLe (L d : ℝ) (u : E3) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
    volume ({x : E3 | boxMargin L d u x < δ} ∩ Function.support (chiB L d u))
      ≤ ENNReal.ofReal (C * δ)

/-- **The window vanishes linearly on the boundary of the box**: `|χ_{B(u)}| ≤ C·boxMargin`. -/
def ChiMarginLe (L d : ℝ) (u : E3) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ x ∈ dlBox L d u, |chiB L d u x| ≤ C * boxMargin L d u x

/-! ## 4. The per-slot-set fibre assembly -/

/-- **The per-slot-set bound from the sharp core.**  For a slot set `S`, the slot-piece word (the
`y`-integral of the words of the fibres, `WordFibreFactorisation`) dominates the slot mass times
the threshold, once the sharp core holds at the fibre and the fibre mass of the piece is the mass
of the sharp state.

The two `∀ᵐ`-identifications are the elementary bridge between the corpus vocabulary (`pieceFibre`,
`slotFibreMassReal`) and the sharp vocabulary of the core. -/
theorem slotBound_of_sharp {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ} {L d ε c μ : ℝ}
    {u : E3} {n : ℕ} {T : ℝ} {Φ : X n → ℝ} (S : Finset (Fin n))
    (e : SlotIn n S ≃ Fin S.card)
    (hcore : SharpCountCoreAt h M L d ε c μ u (S.card) T)
    (hcd : ContDiff ℝ (⊤ : ENat) Φ)
    (hperm : ∀ y : SlotOut n S → E3, PermInvariant S.card (slotFibreState S e Φ y))
    (hfac : Work.UBBInputs8.tBwordBInd n L d ε c u (slotPiece (dlBox L d u) S Φ)
        + Work.SmallBoxSliding.qLHSwordB h M L d μ u (slotPiece (dlBox L d u) S Φ)
      = ∫ y in slotOutside L (dlBox L d u) S,
          Work.SlotWord.fibreWord h M S.card L d ε c μ u (pieceFibre (dlBox L d u) S e Φ y))
    (hmassreal : slotMass L (dlBox L d u) S Φ
      = ∫ y in slotOutside L (dlBox L d u) S,
          slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Φ) y)
    (hmassI : Integrable (fun y : SlotOut n S → E3 =>
        slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Φ) y)
      (volume.restrict (slotOutside L (dlBox L d u) S)))
    (hwordI : Integrable (fun y : SlotOut n S → E3 =>
        Work.SlotWord.fibreWord h M S.card L d ε c μ u (pieceFibre (dlBox L d u) S e Φ y))
      (volume.restrict (slotOutside L (dlBox L d u) S)))
    (hid : ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
      pieceFibre (dlBox L d u) S e Φ y = sharpBoxState (dlBox L d u) (slotFibreState S e Φ y))
    (hidm : ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
      slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Φ) y
        = ∫ x in abox S.card L, (sharpBoxState (dlBox L d u) (slotFibreState S e Φ y) x) ^ 2) :
    slotMass L (dlBox L d u) S Φ * T
      ≤ Work.UBBInputs8.tBwordBInd n L d ε c u (slotPiece (dlBox L d u) S Φ)
        + Work.SmallBoxSliding.qLHSwordB h M L d μ u (slotPiece (dlBox L d u) S Φ) := by
  rw [hmassreal, hfac]
  have hle : ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
      slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Φ) y * T
        ≤ Work.SlotWord.fibreWord h M S.card L d ε c μ u
            (pieceFibre (dlBox L d u) S e Φ y) := by
    filter_upwards [hid, hidm] with y hy hy_m
    rw [hy_m, hy]
    exact hcore (slotFibreState S e Φ y)
      (Work.PerSector.contDiff_slotFibreState S e hcd y) (hperm y)
  rw [← MeasureTheory.integral_mul_const]
  exact MeasureTheory.integral_mono_ae (hmassI.mul_const T) hwordI hle

/-! ## 5. The per-sector assembly -/

/-- **The zero state's sliding word vanishes.** -/
theorem fibreWord_zero {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (k : ℕ) (L d ε c μ : ℝ)
    (u : E3) :
    Work.SlotWord.fibreWord h M k L d ε c μ u (0 : X k → ℝ) = 0 := by
  rw [Work.SlotWord.fibreWord, Work.PerSector.tBwordBInd_zero, Work.PerSector.qLHSwordB_zero,
    add_zero]

/-- **The `k = 0` sector of the per-sector bound is free**: the word of the zero-occupancy sector
piece vanishes (`Work.FockBridge.sectorPiece_zero_word_eq_zero`), so the inequality reduces to
`sectorMass·T ≤ 0`, which is `sectorMass ≥ 0` together with `T ≤ 0`. -/
theorem sectorBound_zero {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ} {L d ε c μ : ℝ}
    {u : E3} {n : ℕ} {T : ℝ} {Φ : X n → ℝ} (hL : 0 < L) (hd : 0 < d) (hT : T ≤ 0) :
    Work.FockBridge.sectorMass L (dlBox L d u) Φ 0 * T
      ≤ Work.UBBInputs8.tBwordBInd n L d ε c u (Work.FockBridge.sectorPiece (dlBox L d u) 0 Φ)
        + Work.SmallBoxSliding.qLHSwordB h M L d μ u
          (Work.FockBridge.sectorPiece (dlBox L d u) 0 Φ) := by
  rw [Work.FockBridge.sectorPiece_zero_word_eq_zero (N := n) h M L d μ ε c hL hd u Φ]
  exact mul_nonpos_of_nonneg_of_nonpos (Work.FockBridge.sectorMass_nonneg L (dlBox L d u) Φ 0) hT

/-- **The per-sector assembly.**  Given the mass identity `sectorMass_k = Σ_{|S|=k} slotMass_S`, the
sector additivity of the word (`sectorPiece_word_eq_sum_slot_piece`, i.e. the state-level identity
`word(Φ_k) = Σ_{|S|=k} word(Φ_S)`) and the per-slot-set bounds, the per-sector inequality holds. -/
theorem sectorBound_of_slotBounds {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ} {L d ε c μ : ℝ}
    {u : E3} {n k : ℕ} {T : ℝ} {Φ : X n → ℝ}
    (hmass : Work.FockBridge.sectorMass L (dlBox L d u) Φ k
      = ∑ S ∈ Finset.powersetCard k Finset.univ,
          slotMass L (dlBox L d u) S Φ)
    (hadd : Work.UBBInputs8.tBwordBInd n L d ε c u
          (Work.FockBridge.sectorPiece (dlBox L d u) k Φ)
        + Work.SmallBoxSliding.qLHSwordB h M L d μ u
          (Work.FockBridge.sectorPiece (dlBox L d u) k Φ)
      = ∑ S ∈ Finset.powersetCard k Finset.univ,
          (Work.UBBInputs8.tBwordBInd n L d ε c u (slotPiece (dlBox L d u) S Φ)
            + Work.SmallBoxSliding.qLHSwordB h M L d μ u (slotPiece (dlBox L d u) S Φ)))
    (hslot : ∀ S ∈ Finset.powersetCard k Finset.univ,
      slotMass L (dlBox L d u) S Φ * T
        ≤ Work.UBBInputs8.tBwordBInd n L d ε c u (slotPiece (dlBox L d u) S Φ)
          + Work.SmallBoxSliding.qLHSwordB h M L d μ u (slotPiece (dlBox L d u) S Φ)) :
    Work.FockBridge.sectorMass L (dlBox L d u) Φ k * T
      ≤ Work.UBBInputs8.tBwordBInd n L d ε c u
          (Work.FockBridge.sectorPiece (dlBox L d u) k Φ)
        + Work.SmallBoxSliding.qLHSwordB h M L d μ u
          (Work.FockBridge.sectorPiece (dlBox L d u) k Φ) := by
  rw [hadd, hmass, Finset.sum_mul]
  exact Finset.sum_le_sum hslot

/-! ## 6. The sharp extension: from the count core to the sharp core -/

/-- **The mass form of the count core.**  `CountCoreAt` is the inequality at *normalised* in-box
states; homogenising with `Work.BoseFixB1B.fibreWord_smul` (`fibreWord (a•Ψ) = a²·fibreWord Ψ`)
gives the mass-weighted form used at the fibres. -/
theorem countCoreAt_mass_form {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ} {L d ε c μ : ℝ}
    {u : E3} {k : ℕ} {T : ℝ} (hcore : CountCoreAt h M L d ε c μ u k T) :
    ∀ Ψ : X k → ℝ, ContDiff ℝ (⊤ : ENat) Ψ → PermInvariant k Ψ → Ψ ≠ 0 →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox k L)),
        Ψ x ≠ 0 → ∀ i : Fin k, x i ∈ dlBox L d u) →
      0 < ∫ x in abox k L, (Ψ x) ^ 2 →
      (∫ x in abox k L, (Ψ x) ^ 2) * T
        ≤ Work.SlotWord.fibreWord h M k L d ε c μ u Ψ := by
  intro Ψ hcd hperm hne hsupp hpos
  set m : ℝ := ∫ x in abox k L, (Ψ x) ^ 2 with hmdef
  have hmpos : 0 < m := hpos
  set a : ℝ := (Real.sqrt m)⁻¹ with hadef
  have ha : a ≠ 0 := by
    rw [hadef]
    exact inv_ne_zero (Real.sqrt_pos_of_pos hmpos).ne'
  -- the normalised state
  have hscale : ∀ x : X k, (fun y => a * Ψ y) x = a * Ψ x := fun _ => rfl
  have hcd' : ContDiff ℝ (⊤ : ENat) (fun x : X k => a * Ψ x) := contDiff_const.mul hcd
  have hperm' : PermInvariant k (fun x : X k => a * Ψ x) := by
    intro σ x
    simp only [Pi.mul_apply]
    rw [hperm σ x]
  have hne' : (fun x : X k => a * Ψ x) ≠ 0 := by
    intro hzero
    apply hne
    funext x
    have h := congrFun hzero x
    simp only [Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left ha
  have hsupp' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox k L)),
      (fun y : X k => a * Ψ y) x ≠ 0 → ∀ i : Fin k, x i ∈ dlBox L d u := by
    filter_upwards [hsupp] with x hx hne2
    exact hx (fun hzero => hne2 (by simp [hzero]))
  have hnorm : (∫ x in abox k L, ((fun y : X k => a * Ψ y) x) ^ 2) = 1 := by
    have : ∀ x : X k, ((fun y : X k => a * Ψ y) x) ^ 2 = a ^ 2 * (Ψ x) ^ 2 := by
      intro x; simp only [Pi.mul_apply]; ring
    rw [show (∫ x in abox k L, ((fun y : X k => a * Ψ y) x) ^ 2)
        = ∫ x in abox k L, a ^ 2 * (Ψ x) ^ 2 from by
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall this)]
    rw [MeasureTheory.integral_const_mul]
    have ha2 : a ^ 2 = m⁻¹ := by
      rw [hadef, inv_pow, Real.sq_sqrt (le_of_lt hmpos)]
    rw [ha2, hmdef, inv_mul_cancel₀ (ne_of_gt hmpos)]
  have hcore' := hcore (fun x : X k => a * Ψ x) hcd' hperm' hne' hsupp' hnorm
  have hsmul : Work.SlotWord.fibreWord h M k L d ε c μ u (fun x : X k => a * Ψ x)
      = a ^ 2 * Work.SlotWord.fibreWord h M k L d ε c μ u Ψ :=
    fibreWord_smul h M k L d ε c μ u a Ψ
  rw [hsmul] at hcore'
  have ha2 : a ^ 2 = m⁻¹ := by
    rw [hadef, inv_pow, Real.sq_sqrt (le_of_lt hmpos)]
  rw [ha2] at hcore'
  have h1 : m * (m⁻¹ * Work.SlotWord.fibreWord h M k L d ε c μ u Ψ)
      = Work.SlotWord.fibreWord h M k L d ε c μ u Ψ := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmpos), one_mul]
  have := mul_le_mul_of_nonneg_left hcore' (le_of_lt hmpos)
  rwa [h1] at this

/-- **The sharp extension, given the convergence of the word and of the mass along the approximating
family.**  This is the assembly of the analytic input: the count core at the normalised approximants
(`countCoreAt_mass_form`), the two convergence statements, and `le_of_tendsto_of_tendsto'. -/
theorem sharpCountCoreAt_of_tendsto {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    {L d ε c μ : ℝ} {u : E3} {k : ℕ} {T K : ℝ} {γ : ℝ → E3 → ℝ} {ψ : X k → ℝ}
    (hL : 0 < L) (hd : 0 < d)
    (hcut : IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hψsymm : PermInvariant k ψ)
    (hcore : CountCoreAt h M L d ε c μ u k T)
    (hconv : Filter.Tendsto
      (fun δ : ℝ => Work.SlotWord.fibreWord h M k L d ε c μ u (cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.SlotWord.fibreWord h M k L d ε c μ u (sharpBoxState (dlBox L d u) ψ))))
    (hconvM : Filter.Tendsto
      (fun δ : ℝ => ∫ x in abox k L, (cutProd (γ δ) ψ x) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2)))
    (hmpos : 0 < ∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) :
    (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) * T
      ≤ Work.SlotWord.fibreWord h M k L d ε c μ u (sharpBoxState (dlBox L d u) ψ) := by
  have hcut' := hcut
  obtain ⟨hK, hcutδ⟩ := hcut'
  -- the approximants are smooth, symmetric and supported in the box, with positive mass eventually
  have hcdδ : ∀ δ : ℝ, 0 < δ → ContDiff ℝ (⊤ : ENat) (cutProd (γ δ) ψ) := by
    intro δ hδ
    have hprod : ContDiff ℝ (⊤ : ENat)
        (∏ i : Fin k, fun x : X k => γ δ (x i)) := by
      classical
      refine Finset.prod_induction (s := (Finset.univ : Finset (Fin k)))
        (f := fun i : Fin k => fun x : X k => γ δ (x i))
        (p := fun g : X k → ℝ => ContDiff ℝ (⊤ : ENat) g)
        (fun f g hf hg => hf.mul hg) contDiff_const ?_
      intro i _
      exact (hcutδ δ hδ).1.comp ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin k => E3) i).contDiff)
    have hprod' : ContDiff ℝ (⊤ : ENat) (fun x : X k => ∏ i : Fin k, γ δ (x i)) := by
      have hfun : (∏ i : Fin k, fun x : X k => γ δ (x i))
          = fun x : X k => ∏ i : Fin k, γ δ (x i) := by
        funext x
        rw [Finset.prod_apply]
      rwa [hfun] at hprod
    exact hprod'.mul hψ
  have hsuppδ : ∀ δ : ℝ, 0 < δ → ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox k L)),
      cutProd (γ δ) ψ x ≠ 0 → ∀ i : Fin k, x i ∈ dlBox L d u := by
    intro δ hδ
    refine Filter.Eventually.of_forall (fun x hx i => ?_)
    have hz : γ δ (x i) ≠ 0 := by
      intro hz0
      exact hx (by rw [cutProd_apply, Finset.prod_eq_zero (Finset.mem_univ i) hz0, zero_mul])
    exact (hcutδ δ hδ).2.1 (subset_tsupport _ (Function.mem_support.mpr hz))
  have hpermδ : ∀ δ : ℝ, PermInvariant k (cutProd (γ δ) ψ) := by
    intro δ σ x
    simp only [cutProd_apply]
    rw [hψsymm σ x]
    congr 1
    exact Equiv.prod_comp σ (fun j : Fin k => γ δ (x j))
  -- eventually the approximants have positive mass
  have hev : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < ∫ x in abox k L, (cutProd (γ δ) ψ x) ^ 2 := by
    have hhalf : (0 : ℝ) < (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) / 2 := by
      linarith
    filter_upwards [hconvM.eventually (Ioi_mem_nhds (by linarith :
      (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) / 2
        < ∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2))] with δ hδ
    linarith
  -- the mass-weighted count core at the approximants
  have hkey : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ x in abox k L, (cutProd (γ δ) ψ x) ^ 2) * T
        ≤ Work.SlotWord.fibreWord h M k L d ε c μ u (cutProd (γ δ) ψ) := by
    filter_upwards [hev, self_mem_nhdsWithin] with δ hδm hδpos
    refine countCoreAt_mass_form hcore (cutProd (γ δ) ψ) (hcdδ δ hδpos) (hpermδ δ) ?_ ?_ hδm
    · intro hzero
      have : cutProd (γ δ) ψ = 0 := hzero
      have h0 : (∫ x in abox k L, (cutProd (γ δ) ψ x) ^ 2) = ∫ x in abox k L, (0 : ℝ) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        rw [this]; simp
      rw [h0] at hδm
      simp at hδm
    · exact hsuppδ δ hδpos
  -- pass to the limit
  have hlim : Filter.Tendsto (fun δ : ℝ =>
      (∫ x in abox k L, (cutProd (γ δ) ψ x) ^ 2) * T)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2) * T)) :=
    hconvM.mul tendsto_const_nhds
  exact le_of_tendsto_of_tendsto hlim hconv hkey

end Work.BoseFixB1B
