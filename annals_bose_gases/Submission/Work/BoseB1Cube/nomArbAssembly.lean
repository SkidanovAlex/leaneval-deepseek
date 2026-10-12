import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.nomArbAux
import Submission.Work.BoseB1Cube.nomDemand_split
import Submission.Work.BoseB1Cube.nomRowPieces
import Submission.Work.BoseB1Cube.normB_slotFibre
import Submission.Work.BoseB1Cube.sbWordCube_slotFibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomArbAssembly` — the **nominal** arity passage, assembled

Piece B of `nominalPerBoxRow`, in the nominal (indicator-count) spelling:

    in-box row (nominal) ⟹ all-states row (nominal),

with fresh constants.  This is the transcript of
`Work.BoseB1Cube.cubePerBox_of_inBoxCubeRow` / `cubeArityAssembly.cubePerBox_of_pieces` at the
demand `Work.BoseB1Cube.nomRow`:

* the smooth in-box row collapses to `nomRow ≤ sbWordCube` (`perBoxFNom_le_iff_nomRow`);
* the sharp in-box row follows from it (`nomSharpRow_body`, with the PROVED word convergence
  `tendsto_sbWordCube_cutProd`);
* the per-slot rows follow from the sharp row, the **mass** fibre factorisation
  (`normB_slotFibre`) and the **word** fibre factorisation (`sbWordCube_slotFibre`), through
  `nomCoeff_slot_le_word`;
* the demand splits over the slot sets (`nomDemand_split`) and the word is slot-additive
  (`sbWordCube_slotAdditive`);
* the empty slot set is the one degenerate term, paid by `c₁' ≤ 1/4`
  (`sbWordCube_slotPiece_empty_nonneg`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseKinLoc Work.PerSector Work.SlotWord Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-! ## 1. Elementary nonnegativity facts -/

/-- `ψ(1,μ,t) ≥ 0` on the physical range `t ≥ 0`. -/
theorem psiWeight_one_nonneg {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight 1 μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  refine div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_
  have h : 0 ≤ t * μ⁻¹ := mul_nonneg ht (inv_nonneg.mpr hμ.le)
  linarith

/-- The nominal coefficient at the count `0` is nonpositive as soon as `c₁ ≤ 1/2`: the `F`-weight
saturates at `ψ(1,μ,0) = μ²` and the two remaining terms are nonpositive. -/
theorem nomCoeff_zero_nonpos {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {u : E3}
    (hW : 0 ≤ nomW v h μ u) (hE : 0 ≤ nomESlot v R C μ μ u) (hc₁ : c₁ ≤ 1 / 2) :
    nomCoeff v h R c₁ C μ u 0 ≤ 0 := by
  have hψ0 : Work.SmallBoxSliding.psiWeight 1 μ ((0 : ℝ) / nomV v μ u) = μ ^ 2 := by
    rw [Work.SmallBoxSliding.psiWeight]
    simp
  rw [nomCoeff]
  simp only [Nat.cast_zero, zero_div] at hψ0 ⊢
  rw [hψ0]
  have hu : 0 ≤ nomW v h μ u * μ ^ 2 := mul_nonneg hW (sq_nonneg μ)
  have h1 : c₁ * (nomW v h μ u * μ ^ 2) ≤ (1 / 2) * (nomW v h μ u * μ ^ 2) :=
    mul_le_mul_of_nonneg_right hc₁ hu
  nlinarith [h1, hE, hu]

/-! ## 2. The nominal `PerBoxFNom` is the slot-sum row -/

/-- **The nominal per-box row splits exactly over the slot sets.**  The configuration-level
`F`-weight `ψ(1,μ, boxIndCount/|B|)` is the constant `ψ(1,μ,|S|/|B|)` on the slot set of `S`, so the
nominal row at any state is exactly the sum of the per-slot rows of the coefficients `nomCoeff |S|`. -/
theorem perBoxFNom_iff_sum_slots {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    {u : E3} {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))} (hℓ : 0 < sideAt μ (a v)) :
    PerBoxFNom v h R c₁ C μ μ n Φ u ↔
      (∑ S : Finset (Fin n),
          nomCoeff v h R c₁ C μ u S.card
            * (∫ x in abox n (sideAt μ (a v)),
                (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) S
                  (Φ : X n → ℝ) x) ^ 2))
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
  classical
  have hsplit := nomDemand_split (N := n) (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d)
    (μ := μ)
    (W := c₁ * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u)
    (E := (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u
      + C * (μ ^ 2 * (a v)
          * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u
        + μ * (a v)))
    hℓ u (Φ := (Φ : X n → ℝ)) (hΦ := Φ.contDiff.continuous)
  have hL : (c₁ * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u)
      * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
          * Work.SmallBoxSliding.psiWeight 1 μ
              (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))
      - ((1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u
          + C * (μ ^ 2 * (a v)
              * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                  + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u
            + μ * (a v)))
        * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2)
      = ∑ S : Finset (Fin n),
          nomCoeff v h R c₁ C μ u S.card
            * (∫ x in abox n (sideAt μ (a v)),
                (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) S
                  (Φ : X n → ℝ) x) ^ 2) := by
    rw [hsplit]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    simp only [nomCoeff, nomW, nomV, nomESlot, nomChi, nomGamma]
    ring
  have key := hL
  clear key
  constructor
  · intro hper
    rw [PerBoxFNom] at hper
    have h1 : (c₁ * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u)
        * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2
            * Work.SmallBoxSliding.psiWeight 1 μ
                (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                  / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))
        - ((1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u
            + C * (μ ^ 2 * (a v)
                * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                    + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                    (paramsAt μ (a v)).d u
              + μ * (a v)))
          * (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) :=
      le_of_eq_of_le (by
        simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
        ring) hper
    rw [hL] at h1
    exact h1
  · intro hsum
    rw [PerBoxFNom]
    rw [← hL] at hsum
    exact le_of_eq_of_le (by
      simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      ring) hsum

/-! ## 3. The nominal arity passage -/

/-- **Piece B of `nominalPerBoxRow`, in the nominal spelling.**  From the in-box nominal row (at a
fixed diluteness `ε₀` and constants `(c₁, C)`) the row holds for *every* `BoxState`, at the fresh
constants `(min ε₀ (min εconv εword εadd), min c₁ 1/4, C)`.

The constant `ε₀'` dilutes the target diluteness to the (state-free) thresholds of the three proved
inputs; `c₁' = min c₁ 1/4` is needed *only* for the empty slot set, where the `F`-weight saturates at
`μ²` and the row must absorb the error bracket. -/
theorem nomRowArbState_holds {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) :
    NomRowArbState v h R := by
  classical
  intro ε₀ c₁ C hε₀ hc₁ hC hIn
  obtain ⟨εc, hεc, hconvB⟩ := tendsto_sbWordCube_cutProd h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εw, hεw, hwordB⟩ := sbWordCube_slotFibre h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εa, hεa, haddB⟩ := sbWordCube_slotAdditive h hv hv1 hvrad hR hv_supp hav
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
  refine ⟨ε₂, min c₁ (1 / 4), C, hε₂, lt_min hc₁ (by norm_num), hC, ?_⟩
  intro μ hAdm n Φ u hu
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  -- ## the in-box row at `c₁`, and the sharp row
  have hinB : NomInBoxRowBody v h R c₁ C ε₂ := fun μ' hμ' n' Φ' u' hu' hloc' =>
    (perBoxFNom_le_iff_nomRow (v := v) (h := h) (R := R) (c₁ := c₁) (C := C) (μ := μ')
      (n := n') (u := u') (Φ := Φ') hloc').mp
      (hIn μ' (Work.BoseFixB1.Adm.mono hμ' h2ε₀) n' Φ' u' hu' hloc')
  have hsharp : NomSharpRowBody v h R c₁ C ε₂ :=
    nomSharpRow_body hv hv1 hvrad hR hv_supp hav hε₂ hinB
      (fun μ' hμ' => hconvB μ' (Work.BoseFixB1.Adm.mono hμ' h2εc))
  -- ## the finiteness of the state's `abox`-mass
  have hfinΦ : (∫⁻ x in abox n (sideAt μ (a v)),
      ENNReal.ofReal (((Φ : X n → ℝ) x) ^ 2)) ≠ ⊤ := by
    obtain ⟨Cb, hCb⟩ :=
      (abox_compact n hℓ).exists_bound_of_continuousOn Φ.contDiff.continuous.continuousOn
    set Cc : ℝ := max Cb 0 with hCcdef
    have hbound : ∀ x ∈ abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 ≤ Cc ^ 2 := by
      intro x hx
      have h1 : |(Φ : X n → ℝ) x| ≤ Cc := by
        rw [← Real.norm_eq_abs]
        exact le_trans (hCb x hx) (le_max_left _ _)
      have habs : ((Φ : X n → ℝ) x) ^ 2 = |(Φ : X n → ℝ) x| ^ 2 := by rw [sq_abs]
      rw [habs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h2 : (∫⁻ x in abox n (sideAt μ (a v)), ENNReal.ofReal (((Φ : X n → ℝ) x) ^ 2))
        ≤ ENNReal.ofReal (Cc ^ 2) * volume (abox n (sideAt μ (a v))) := by
      calc (∫⁻ x in abox n (sideAt μ (a v)), ENNReal.ofReal (((Φ : X n → ℝ) x) ^ 2))
          ≤ ∫⁻ _x in abox n (sideAt μ (a v)), ENNReal.ofReal (Cc ^ 2) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem
              (abox_isClosed n (sideAt μ (a v))).measurableSet] with x hx
            exact ENNReal.ofReal_le_ofReal (hbound x hx)
        _ = ENNReal.ofReal (Cc ^ 2) * volume (abox n (sideAt μ (a v))) := by
            rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
    exact ne_of_lt (lt_of_le_of_lt h2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Submission.BoseGases.abox_lt_top n (sideAt μ (a v)) hℓ.le)))
  -- ## the two fibre factorisations
  have massData : ∀ (S : Finset (Fin n)) (e : SlotIn n S ≃ Fin S.card), 0 < S.card →
      MeasureTheory.Integrable
        (fun y : SlotOut n S → E3 => ∫ x in abox S.card (PBℓ v μ),
          (sharpBoxState (PBB v μ u) (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2)
        ((volume : Measure (SlotOut n S → E3)).restrict (slotOutside (PBℓ v μ) (PBB v μ u) S))
      ∧ (∫ x in abox n (PBℓ v μ), (slotPiece (PBB v μ u) S (Φ : X n → ℝ) x) ^ 2)
        = ∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S,
            ∫ x in abox S.card (PBℓ v μ),
              (sharpBoxState (PBB v μ u) (slotFibreState S e (Φ : X n → ℝ) y) x) ^ 2 :=
    fun S e _ => normB_slotFibre (N := n) (L := PBℓ v μ) (d := PBd v μ) hℓ hd u
      (Φ := (Φ : X n → ℝ)) Φ.contDiff.continuous.measurable hfinΦ S e
  have wordData : ∀ (S : Finset (Fin n)) (e : SlotIn n S ≃ Fin S.card), 0 < S.card →
      MeasureTheory.Integrable
        (fun y : SlotOut n S → E3 => sbWordCube v h μ u
          (sharpBoxState (PBB v μ u) (slotFibreState S e (Φ : X n → ℝ) y)))
        ((volume : Measure (SlotOut n S → E3)).restrict (slotOutside (PBℓ v μ) (PBB v μ u) S))
      ∧ sbWordCube v h μ u (slotPiece (PBB v μ u) S (Φ : X n → ℝ))
        = ∫ y in slotOutside (PBℓ v μ) (PBB v μ u) S, sbWordCube v h μ u
            (sharpBoxState (PBB v μ u) (slotFibreState S e (Φ : X n → ℝ) y)) :=
    fun S e hS => hwordB μ (Work.BoseFixB1.Adm.mono hAdm h2εw) u hu n Φ S hS e
  -- ## the elementary nonnegativities
  have hW0 : 0 ≤ nomW v h μ u := by
    rw [nomW]
    exact Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hV0 : 0 ≤ nomV v μ u := by
    rw [nomV]
    exact Work.BoseFixB1S.boxMass_nonneg (sideAt μ (a v)) (paramsAt μ (a v)).d u
  have hΓ : 0 ≤ nomGamma v R μ := by
    rw [nomGamma]
    have h2 : 0 ≤ (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
      rw [Work.BoseFixB1.KB3_half_eq (A := a v) (μ := μ) hav hμ, Work.BoseBox.fsXp]
      exact Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hav.le 3)) _
    linarith [sq_nonneg (R / (sideAt μ (a v) * (paramsAt μ (a v)).d))]
  have hE0 : 0 ≤ nomESlot v R C μ μ u := by
    rw [nomESlot, nomChi]
    refine mul_nonneg hC (add_nonneg ?_ (mul_nonneg hμ.le hav.le))
    refine mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) hΓ) ?_
    exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  -- ## the per-slot rows
  have hslot : ∀ S : Finset (Fin n),
      nomCoeff v h R (min c₁ (1 / 4)) C μ u S.card
        * (∫ x in abox n (sideAt μ (a v)),
            (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) S
              (Φ : X n → ℝ) x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) S (Φ : X n → ℝ)) := by
    intro S
    by_cases hS : S = ∅
    · subst hS
      rw [Finset.card_empty]
      have hcoef : nomCoeff v h R (min c₁ (1 / 4)) C μ u 0 ≤ 0 :=
        nomCoeff_zero_nonpos hW0 hE0 (le_trans (min_le_right _ _) (by norm_num))
      have hm0 : 0 ≤ ∫ x in abox n (sideAt μ (a v)),
          (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            (∅ : Finset (Fin n)) (Φ : X n → ℝ) x) ^ 2 :=
        integral_nonneg (fun x => sq_nonneg _)
      calc nomCoeff v h R (min c₁ (1 / 4)) C μ u 0
            * (∫ x in abox n (sideAt μ (a v)),
                (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
                  (∅ : Finset (Fin n)) (Φ : X n → ℝ) x) ^ 2)
          ≤ 0 * (∫ x in abox n (sideAt μ (a v)),
                (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
                  (∅ : Finset (Fin n)) (Φ : X n → ℝ) x) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hm0
        _ = 0 := by ring
        _ ≤ sbWordCube v h μ u (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
              (∅ : Finset (Fin n)) (Φ : X n → ℝ)) :=
            sbWordCube_slotPiece_empty_nonneg (v := v) (h := h) hAdm Φ u
    · have hSp : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      have hmS : 0 ≤ ∫ x in abox n (PBℓ v μ),
          (slotPiece (PBB v μ u) S (Φ : X n → ℝ) x) ^ 2 :=
        integral_nonneg (fun x => sq_nonneg _)
      have hrow := nomCoeff_slot_le_word (v := v) (h := h) (R := R) (c₁ := c₁) (C := C)
        (ε₀ := ε₂) (μ := μ) hAdm u hu Φ hsharp massData wordData S hSp
        (Work.BoseKinLoc.Sector.slotIso S)
      have hmono : nomCoeff v h R (min c₁ (1 / 4)) C μ u S.card
          ≤ nomCoeff v h R c₁ C μ u S.card :=
        nomCoeff_mono_c₁ (v := v) (h := h) (R := R) (C := C) (μ := μ)
          (c₁ := c₁) (c₁' := min c₁ (1 / 4)) (u := u) S.card (min_le_left _ _) hW0
          (psiWeight_one_nonneg hμ (div_nonneg (Nat.cast_nonneg _) hV0))
      exact le_trans (mul_le_mul_of_nonneg_right hmono hmS) hrow
  -- ## the demand split and the slot summation
  have hsum : (∑ S : Finset (Fin n),
        nomCoeff v h R (min c₁ (1 / 4)) C μ u S.card
          * (∫ x in abox n (sideAt μ (a v)),
              (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) S
                (Φ : X n → ℝ) x) ^ 2))
      ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    calc (∑ S : Finset (Fin n), nomCoeff v h R (min c₁ (1 / 4)) C μ u S.card
          * (∫ x in abox n (sideAt μ (a v)),
              (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) S
                (Φ : X n → ℝ) x) ^ 2))
        ≤ ∑ S : Finset (Fin n), Work.BoseFixB1B.sbWordCube v h μ u
            (slotPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) S
              (Φ : X n → ℝ)) := Finset.sum_le_sum (fun S _ => hslot S)
      _ = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) :=
          (haddB μ (Work.BoseFixB1.Adm.mono hAdm h2εa) n Φ u).symm
  exact (perBoxFNom_iff_sum_slots (v := v) (h := h) (R := R) (c₁ := min c₁ (1 / 4)) (C := C)
    (μ := μ) (n := n) (u := u) (Φ := Φ) hℓ).mpr hsum

end Work.BoseB1Cube
