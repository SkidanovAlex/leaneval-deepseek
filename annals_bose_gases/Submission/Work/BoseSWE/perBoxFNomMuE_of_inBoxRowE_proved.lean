import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSWE.nomCoeffE_slot_le_word
import Submission.Work.BoseSWE.nomSharpRowE_body
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.perBoxFNomMuE_of_inBoxRowE_proved` — F3b of the `BoseSWE` route

Piece B of the nominal per-box chapter with the vanishing slack `ErrE` carried: from the in-box
`E`-row at fixed constants to the `E`-row for **every** `BoxState`, with fresh constants.

The whole arity passage of `Submission/Work/BoseB1Cube/nomArbAux.lean` + `nomArbAssembly.lean` is
"coefficient times `abox`-mass", so the slack — itself `n`-linear and multiplying the same
`abox`-mass — is absorbed into the coefficient `nomCoeffE = nomCoeff − ErrE(·)` (see
`Submission/Work/BoseSWE/DefsE.lean`).  The two transcription lemmas
(`Work.BoseSWE.nomSharpRowE_body`, `Work.BoseSWE.nomCoeffE_slot_le_word`) supply the smooth-to-sharp
step and the per-slot fibre step; the assembly below is the `E`-twin of §3 of `nomArbAssembly.lean`,
with the slack aggregated by `Σ_S ErrE(|S|)·m_S ≤ ErrE(n)·‖Φ‖²` (`|S| ≤ n`, `ErrE` monotone).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-! ## 0. The slot masses of the passage -/

/-- The `abox`-`L²`-mass of the slot piece of the occupant set `S`. -/
noncomputable def slotMassB (v : E3 → ℝ) (μ : ℝ) (u : E3) (n : ℕ) (Φ : X n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S Φ x) ^ 2

/-- The matched word of the slot piece of the occupant set `S`. -/
noncomputable def slotWordB (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3) (n : ℕ)
    (Φ : X n → ℝ) (S : Finset (Fin n)) : ℝ :=
  Work.BoseFixB1B.sbWordCube v h μ u
    (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S Φ)

/-- The slot mass is nonnegative. -/
theorem slotMassB_nonneg (v : E3 → ℝ) (μ : ℝ) (u : E3) (n : ℕ) (Φ : X n → ℝ)
    (S : Finset (Fin n)) : 0 ≤ slotMassB v μ u n Φ S :=
  integral_nonneg (fun x => sq_nonneg _)

/-- The frozen nominal demand is the sum of its per-sector demands (`perBoxRow_eq_sum_slots` in the
`slotMassB` spelling). -/
theorem perBoxRow_eq_sum_slotMassB {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    {u : E3} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    Work.BoseB1Cube.perBoxRow v h R c₁ C μ μ n Φ u
      = ∑ S : Finset (Fin n),
          Work.BoseB1Cube.nomCoeff v h R c₁ C μ u S.card
            * slotMassB v μ u n (Φ : X n → ℝ) S := by
  rw [perBoxRow_eq_sum_slots (v := v) (h := h) (R := R) (c₁ := c₁) (C := C) (μ := μ) (n := n)
    (u := u) (Φ := Φ) hℓ]
  exact Finset.sum_congr rfl (fun S _ => by simp only [slotMassB])

/-- The `abox`-mass splits over the occupant sectors (`normB_eq_sum_slots` in the `slotMassB`
spelling). -/
theorem normB_eq_sum_slotMassB {v : E3 → ℝ} {μ : ℝ} {n : ℕ} {u : E3}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
      = ∑ S : Finset (Fin n), slotMassB v μ u n (Φ : X n → ℝ) S := by
  rw [normB_eq_sum_slots (v := v) (μ := μ) (n := n) (u := u) (Φ := Φ) hℓ]
  exact Finset.sum_congr rfl (fun S _ => by simp only [slotMassB])

/-! ## 1. The target -/

/-- **F3b of the `BoseSWE` route**: piece B with the slack — from the in-box row at the *fixed*
constants `(ε₀, 1/40, C, CE)` (F3a's output) to the row for **every** `BoxState`.  The constants
`ε₀ C CE` are binders of this declaration (not universally quantified inside it), so a caller
holding F3a's `∃ ε₁ …` instantiates them.  (Identical statement to `Work.BoseSWE.perBoxFNomMuE_of_inBoxRowE`,
which two reviewers approved; the name is changed only because a reviewer probe file occupies that
path.)
Recipe (`Submission/Work/BoseSWE/BRIEF.md` §7): copy `Work.BoseB1Cube.nomRowArbState` /
`nomArbAssembly` / `nomArbAux` (the demand splits over the slot sets `nomDemand_split`, the word is
slot-additive `sbWordCube_slotAdditive`, the norm is slot additive `normB_slotFibre`, the empty slot
set is paid by `c₁' ≤ 1/4`); the slack survives with the *same* coefficient because
`Σ_S ErrE v CE μ (S.card)·N_S ≤ ErrE v CE μ n·normB` (`|S| ≤ n`, `ErrE` is `n`-linear and
nonnegative).  The conclusion uses fresh constants (as `NomRowArbState` does). -/
theorem perBoxFNomMuE_of_inBoxRowE_proved {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ C CE : ℝ} (hε₀ : 0 < ε₀) (hC : 0 ≤ C) (hCE : 0 ≤ CE)
    (hIn : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ)
          (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
            (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
              ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          Work.BoseSWE.PerBoxFNomE v h R (1 / 40) C CE μ μ n Φ u) :
    Work.BoseSWE.PerBoxFNomMuE v h R := by
  classical
  -- ## the diluteness thresholds of the three proved inputs
  obtain ⟨εc, hεc, hconvB⟩ :=
    Work.BoseB1Cube.tendsto_sbWordCube_cutProd h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εw, hεw, hwordB⟩ :=
    Work.BoseB1Cube.sbWordCube_slotFibre h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εa, hεa, haddB⟩ :=
    Work.BoseB1Cube.sbWordCube_slotAdditive h hv hv1 hvrad hR hv_supp hav
  set ε₂ : ℝ := min ε₀ (min εc (min εw εa)) with hε₂def
  have hε₂ : 0 < ε₂ := by
    rw [hε₂def]; exact lt_min hε₀ (lt_min hεc (lt_min hεw hεa))
  have h2ε₀ : ε₂ ≤ ε₀ := by rw [hε₂def]; exact min_le_left _ _
  have h2εc : ε₂ ≤ εc := by
    rw [hε₂def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have h2εw : ε₂ ≤ εw := by
    rw [hε₂def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h2εa : ε₂ ≤ εa := by
    rw [hε₂def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨ε₂, 1 / 40, C, CE, hε₂, by norm_num, hC, hCE, ?_⟩
  intro μ hAdm n Φ u hu
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  -- ## the in-box `E`-row in the state-level spelling, and the sharp row
  have hinB : NomInBoxRowBodyE v h R (1 / 40) C CE ε₂ := by
    intro μ' hAdm' m Ψ w hw hloc
    exact (PerBoxFNomE_iff_nomRowE (v := v) (h := h) (R := R) (c₁ := 1 / 40) (C := C) (CE := CE)
        (μ := μ') (n := m) (u := w) (Φ := Ψ) hloc).mp
      (hIn μ' (Work.BoseFixB1.Adm.mono hAdm' h2ε₀) m Ψ w hw hloc)
  have hsharp : NomSharpRowBodyE v h R (1 / 40) C CE ε₂ :=
    nomSharpRowE_body (v := v) (h := h) (R := R) (c₁ := 1 / 40) (C := C) (CE := CE) (ε₀ := ε₂)
      hv hv1 hvrad hR hv_supp hav hε₂ hinB
      (fun μ' hμ' => hconvB μ' (Work.BoseFixB1.Adm.mono hμ' h2εc))
  -- ## the finiteness of the state's `abox`-mass
  have hfinΦ : (∫⁻ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ENNReal.ofReal (((Φ : X n → ℝ) x) ^ 2)) ≠ ⊤ := by
    obtain ⟨Cb, hCb⟩ :=
      (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
        Φ.contDiff.continuous.continuousOn
    set Cc : ℝ := max Cb 0 with hCcdef
    have hbound : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : X n → ℝ) x) ^ 2 ≤ Cc ^ 2 := by
      intro x hx
      have h1 : |(Φ : X n → ℝ) x| ≤ Cc := by
        rw [← Real.norm_eq_abs]
        exact le_trans (hCb x hx) (le_max_left _ _)
      have habs : ((Φ : X n → ℝ) x) ^ 2 = |(Φ : X n → ℝ) x| ^ 2 := by rw [sq_abs]
      rw [habs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h2 : (∫⁻ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ENNReal.ofReal (((Φ : X n → ℝ) x) ^ 2))
        ≤ ENNReal.ofReal (Cc ^ 2) * volume (Submission.BoseGases.abox n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
      calc (∫⁻ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ENNReal.ofReal (((Φ : X n → ℝ) x) ^ 2))
          ≤ ∫⁻ _x in Submission.BoseGases.abox n
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), ENNReal.ofReal (Cc ^ 2) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem
              (Submission.BoseGases.abox_isClosed n
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))).measurableSet] with x hx
            exact ENNReal.ofReal_le_ofReal (hbound x hx)
        _ = ENNReal.ofReal (Cc ^ 2) * volume (Submission.BoseGases.abox n
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
            rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
    exact ne_of_lt (lt_of_le_of_lt h2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Submission.BoseGases.abox_lt_top n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hℓ.le)))
  -- ## the two fibre factorisations
  have massData : ∀ (S : Finset (Fin n)) (e : Work.PerSector.SlotIn n S ≃ Fin S.card), 0 < S.card →
      MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut n S → E3 =>
          ∫ x in Submission.BoseGases.abox S.card (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.PerSector.slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2)
        ((volume : Measure (Work.PerSector.SlotOut n S → E3)).restrict
          (Work.PerSector.slotOutside (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S))
      ∧ (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S (Φ : X n → ℝ) x) ^ 2)
        = ∫ y in Work.PerSector.slotOutside (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S,
            ∫ x in Submission.BoseGases.abox S.card (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.PerSector.slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2 :=
    fun S e _ => Work.BoseB1Cube.normB_slotFibre (N := n)
      (L := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd u
      (Φ := (Φ : X n → ℝ)) Φ.contDiff.continuous.measurable hfinΦ S e
  have wordData : ∀ (S : Finset (Fin n)) (e : Work.PerSector.SlotIn n S ≃ Fin S.card),
      0 < S.card →
      MeasureTheory.Integrable
        (fun y : Work.PerSector.SlotOut n S → E3 => Work.BoseFixB1B.sbWordCube v h μ u
          (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.PerSector.slotFibreState S e (Φ : X n → ℝ) y)))
        ((volume : Measure (Work.PerSector.SlotOut n S → E3)).restrict
          (Work.PerSector.slotOutside (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S))
      ∧ Work.BoseFixB1B.sbWordCube v h μ u
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S (Φ : X n → ℝ))
        = ∫ y in Work.PerSector.slotOutside (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S,
            Work.BoseFixB1B.sbWordCube v h μ u
              (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.PerSector.slotFibreState S e (Φ : X n → ℝ) y)) :=
    fun S e hS => hwordB μ (Work.BoseFixB1.Adm.mono hAdm h2εw) u hu n Φ S hS e
  -- ## the elementary nonnegativities
  have hW0 : 0 ≤ Work.BoseB1Cube.nomW v h μ u := by
    rw [Work.BoseB1Cube.nomW]
    exact Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hE0 : 0 ≤ Work.BoseB1Cube.nomESlot v R C μ μ u := by
    rw [Work.BoseB1Cube.nomESlot, Work.BoseB1Cube.nomChi]
    refine mul_nonneg hC (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le)
      ?_) (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)) (mul_nonneg hμ.le hav.le))
    rw [Work.BoseB1Cube.nomGamma]
    have h2 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := by
      rw [Work.BoseFixB1.KB3_half_eq (A := _root_.BoseGases.a v) (μ := μ) hav hμ,
        Work.BoseBox.fsXp]
      exact Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hav.le 3)) _
    linarith [sq_nonneg (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d))]
  -- ## the per-slot rows
  have hslot : ∀ S : Finset (Fin n),
      nomCoeffE v h R (1 / 40) C CE μ u S.card * slotMassB v μ u n (Φ : X n → ℝ) S
        ≤ slotWordB v h μ u n (Φ : X n → ℝ) S := by
    intro S
    by_cases hS : S = ∅
    · subst hS
      rw [Finset.card_empty]
      have hcoef : nomCoeffE v h R (1 / 40) C CE μ u 0 ≤ 0 :=
        nomCoeffE_zero_nonpos hW0 hE0 (by norm_num)
      have hm0 : 0 ≤ slotMassB v μ u n (Φ : X n → ℝ) (∅ : Finset (Fin n)) :=
        slotMassB_nonneg v μ u n (Φ : X n → ℝ) _
      calc nomCoeffE v h R (1 / 40) C CE μ u 0
            * slotMassB v μ u n (Φ : X n → ℝ) (∅ : Finset (Fin n))
          ≤ 0 * slotMassB v μ u n (Φ : X n → ℝ) (∅ : Finset (Fin n)) :=
            mul_le_mul_of_nonneg_right hcoef hm0
        _ = 0 := by ring
        _ ≤ slotWordB v h μ u n (Φ : X n → ℝ) (∅ : Finset (Fin n)) := by
            rw [slotWordB]
            exact Work.BoseB1Cube.sbWordCube_slotPiece_empty_nonneg (v := v) (h := h) hAdm Φ u
    · have hSp : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      have hrow := nomCoeffE_slot_le_word (v := v) (h := h) (R := R) (c₁ := 1 / 40) (C := C)
        (CE := CE) (ε₀ := ε₂) (μ := μ) hAdm u hu Φ hsharp massData wordData S hSp
        (Work.BoseKinLoc.Sector.slotIso S)
      simpa only [slotMassB, slotWordB, Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd,
        Work.BoseFixB1B.PBB] using hrow
  -- ## the slot sum
  have hsum : (∑ S : Finset (Fin n), nomCoeffE v h R (1 / 40) C CE μ u S.card
        * slotMassB v μ u n (Φ : X n → ℝ) S)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    calc (∑ S : Finset (Fin n), nomCoeffE v h R (1 / 40) C CE μ u S.card
          * slotMassB v μ u n (Φ : X n → ℝ) S)
        ≤ ∑ S : Finset (Fin n), slotWordB v h μ u n (Φ : X n → ℝ) S :=
          Finset.sum_le_sum (fun S _ => hslot S)
      _ = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
          rw [haddB μ (Work.BoseFixB1.Adm.mono hAdm h2εa) n Φ u]
          exact Finset.sum_congr rfl (fun S _ => by simp only [slotWordB])
  -- ## the slack aggregation and the conclusion
  rw [PerBoxFNomE_iff_row, perBoxRow_eq_sum_slotMassB (μ := μ) (n := n) (u := u) (Φ := Φ) hℓ,
    normB_eq_sum_slotMassB (μ := μ) (n := n) (u := u) (Φ := Φ) hℓ]
  have hkey : (∑ S : Finset (Fin n), Work.BoseB1Cube.nomCoeff v h R (1 / 40) C μ u S.card
          * slotMassB v μ u n (Φ : X n → ℝ) S)
        - ErrE v CE μ n * (∑ S : Finset (Fin n), slotMassB v μ u n (Φ : X n → ℝ) S)
      = (∑ S : Finset (Fin n), nomCoeffE v h R (1 / 40) C CE μ u S.card
          * slotMassB v μ u n (Φ : X n → ℝ) S)
        + ∑ S : Finset (Fin n), (ErrE v CE μ S.card - ErrE v CE μ n)
            * slotMassB v μ u n (Φ : X n → ℝ) S := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => by rw [nomCoeffE]; ring)
  rw [hkey]
  have hnonpos : (∑ S : Finset (Fin n), (ErrE v CE μ S.card - ErrE v CE μ n)
        * slotMassB v μ u n (Φ : X n → ℝ) S) ≤ 0 := by
    refine Finset.sum_nonpos (fun S _ => ?_)
    have hcard : S.card ≤ n := by
      have h := Finset.card_le_univ S
      simpa using h
    have hle : ErrE v CE μ S.card ≤ ErrE v CE μ n :=
      ErrE_mono (v := v) (CE := CE) (μ := μ) hCE hav.le hμ.le hcard
    have hm0 : 0 ≤ slotMassB v μ u n (Φ : X n → ℝ) S := slotMassB_nonneg v μ u n (Φ : X n → ℝ) S
    have hneg : ErrE v CE μ S.card - ErrE v CE μ n ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hneg hm0
  linarith [hsum, hnonpos]

end Work.BoseSWE
