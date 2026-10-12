import ChallengeDeps
import Submission.Work.BoseB1Cube.cubeAmpEnergyJoint
import Submission.Work.BoseB1Cube.kinSlotAdditive_of_jointIntegrable
import Submission.Work.BoseB1Cube.sbWordCube_sectorAdditive
import Submission.Work.BoseFixB1B.integrableOn_slotPiece_sq_qLHSden_sliding
import Submission.Work.BoseFixB1B.sectorPieceWordAdditive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.sbWordCube_slotAdditive`

**The slot additivity of the matched-window (single cube cutoff) sliding word `sbWordCube`.**

For the sliding word `sbWordCube v h μ u = sbKinCube v μ u + sbPot h μ u` of the matched-window
cube chapter, and every smooth symmetric box state `Φ`, the word of the state is the sum of the
words of its `B(u)`-**slot pieces** `slotPiece (B(u)) S Φ = 1_{x ∈ slotSet B S}·Φ`:

    sbWordCube v h μ u Φ = Σ_{S : Finset (Fin n)} sbWordCube v h μ u (slotPiece B(u) S Φ) .

This is the matched-window twin of the PROVED `Work.BoseFixB1B.sbWord_eq_sum_slotWord` (the same
statement at the *ball* window `chiB`) and the companion of the PROVED
`Work.BoseB1Cube.sbWordCube_sectorAdditive` (the same word at the *sector* pieces).

## Why it holds (and why the state must be a box state)

Both halves of the word are *diagonal* in the slot decomposition of the configuration space — the
sets `slotSet B S` (the configurations whose in-box particles are exactly the slots of `S`)
partition `X n`:

* **kinetic half**: `sbKinCube v μ u` is *definitionally* FS's `𝒯_{B(u)}` at the cube cutoff
  `chiSmallB` (`Work.BoseB1Cube.sbKinCube_eq_tBwordInd`).  Its two rows decompose slot by slot:
  - the excited count `cnPlusBoxInd` via the pointwise identity
    `Work.PerSector.sq_boxQInd_eq_sum_sq_boxQInd_slotPiece`, integrated with the `L∞`-integrability
    `Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn`;
  - the windowed `p`-diagonal form `tBdiagFormInd` via the pointwise Parseval identity
    `Work.PerSector.sum_tBamp_normSq_slotPiece` (Fubini + `integral_finsetSum`, i.e. the child
    lemma `Work.BoseB1Cube.kinSlotAdditive_of_jointIntegrable`, fed the joint `(p,x)`-integrability
    `Work.BoseB1Cube.cubeAmpEnergyJoint`).
  These are exactly the two inputs of the corpus's rearrangement
  `Work.PerSector.tBwordInd_eq_sum_slotPiece`.

* **potential half**: `sbPot h μ u` is the *multiplication form*
  `qLHSword ℓ μ w_{B(u)} w_{1,B(u)} = ∫_{abox} qLHSden·Φ²`
  (`Work.FockBridge.qLHSword_eq_mul_integral`), so it only sees the state through its density: the
  slot pieces are disjointly supported, whence `Φ² = Σ_S (slotPiece_S Φ)²` pointwise, and the
  finite sum comes out of the integral (`Work.PerSector.qLHSword_eq_sum_slotPiece`).

The only place the diluteness structure enters is the `abox`-integrability of the sliding potential
summands (`Work.BoseFixB1B.integrableOn_slotPiece_sq_qLHSden_sliding`), which is what forces the
threshold `ε₀` of the statement through `Work.BoseFixB1.exists_adm_regime`.  The kinetic
integrability inputs hold for *every* smooth state and every centre `u`.
-/

namespace Work.BoseB1Cube

open MeasureTheory
open scoped Topology Real BigOperators ENNReal ContDiff

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

theorem sbWordCube_slotAdditive {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) (u : EuclideanSpace ℝ (Fin 3)),
        Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)
          = ∑ S : Finset (Fin n),
              Work.BoseFixB1B.sbWordCube v h μ u
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u) S (Φ : Submission.BoseGases.X n → ℝ)) := by
  classical
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Work.BoseFixB1.exists_adm_regime (v := v) hav hR
  refine ⟨ε₀, hε₀pos, fun μ hAdm n Φ u => ?_⟩
  obtain ⟨hreg1, hreg2⟩ := hε₀ μ hAdm
  have hμ : 0 < μ := hAdm.1
  -- recast the goal in the `b*` vocabulary (definitionally equal to the statement's form)
  show Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
      = ∑ S : Finset (Fin n),
          Work.BoseFixB1B.sbWordCube v h μ u
            (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ))
  -- basic facts about the admissible parameters
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM4 : 4 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1B.bM_eq_mValue]; exact Work.BoseFixB1B.four_le_mValue
  have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by omega
  have hc : (0 : ℝ) ≤ Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
    le_of_lt (Work.BoseFixB1S.sbCut_pos hμ hav)
  have hAmeas : MeasurableSet (Work.BoseFixB1.bA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hAa : Work.BoseFixB1.bA v μ u ⊆ Submission.BoseGases.acube (Work.BoseFixB1.bSide v μ) :=
    Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  have hvol : Work.BoseFixB1.bV v μ u
      = (MeasureTheory.volume : MeasureTheory.Measure E3).real (Work.BoseFixB1.bA v μ u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _
  have hχc : Continuous (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) :=
    (Work.BoseFixB1S.win.contDiff_three_chiSmallB hM4 hℓ hd u).continuous
  have hχsupp : ∀ z : E3, Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u z ≠ 0 → z ∈ Work.BoseFixB1.bA v μ u := by
    intro z hz
    by_contra hnot
    exact hz (Work.BoseFixB1S.win.chiSmallB_eq_zero_of_not_mem_dlBox hM1 hℓ hd u z hnot)
  obtain ⟨Cψ, hCψ0, hCψ⟩ := Work.BoseFixB1.exists_bound_abox_pos (N := n)
    (ℓ := Work.BoseFixB1.bSide v μ) hℓ Φ.contDiff.continuous
  have hpiece : ∀ S : Finset (Fin n), ∀ x ∈ Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
      |Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ) x| ≤ Cψ := by
    intro S x hx
    have h1 : |Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ) x|
        ≤ |(Φ : X n → ℝ) x| := by
      simpa only [Real.norm_eq_abs, Work.PerSector.slotPiece] using
        (norm_indicator_le_norm_self (s := Work.PerSector.slotSet (Work.BoseFixB1.bA v μ u) S)
          (f := (Φ : X n → ℝ)) (a := x))
    exact le_trans h1 (hCψ x hx)
  -- (1) the excited count is slot-additive, slot by slot
  have hcn : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
        (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i
          (Φ : X n → ℝ) x) ^ 2)
      = ∑ S : Finset (Fin n),
          ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
            (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i
              (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ)) x) ^ 2 := by
    intro i
    exact Work.PerSector.cnPlusBoxInd_eq_sum_slotPiece hAmeas i
      (fun S => Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn hAmeas hAa hvol
        (Work.PerSector.slotPiece_measurable _ hAmeas S Φ.contDiff.continuous.measurable)
        hCψ0 (hpiece S) i)
      (Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn hAmeas hAa hvol
        Φ.contDiff.continuous.measurable hCψ0 hCψ i)
  -- (2) the windowed `p`-diagonal form is slot-additive, slot by slot
  have hdkin : ∀ i : Fin n,
      (∫ p : E3, Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖ *
        (((Work.BoseFixB1.bSide v μ) ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
                (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) p
              (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i
                (Φ : X n → ℝ)) i x‖ ^ 2))
      = ∑ S : Finset (Fin n),
          ∫ p : E3, Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖ *
            (((Work.BoseFixB1.bSide v μ) ^ 3)⁻¹ *
              ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
                    (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u) p
                  (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i
                    (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ))) i x‖ ^ 2) := by
    intro i
    exact kinSlotAdditive_of_jointIntegrable (A := Work.BoseFixB1.bA v μ u) hAmeas hχc hχsupp hℓ i
      (cubeAmpEnergyJoint (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
        (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd hM4 u hc Φ.contDiff i)
      (fun S => Work.PerSector.slotPiece_measurable _ hAmeas S Φ.contDiff.continuous.measurable)
  -- (3) the kinetic half: the corpus rearrangement of the two slot-by-slot identities
  have hT := Work.PerSector.tBwordInd_eq_sum_slotPiece (N := n) (A := Work.BoseFixB1.bA v μ u)
    (volA := Work.BoseFixB1.bV v μ u) (a := Work.BoseFixB1.bSide v μ)
    (s := Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
    (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
    (χ := Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u) (Φ := (Φ : X n → ℝ)) hcn hdkin
  have hkin : Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
      = ∑ S : Finset (Fin n),
          Work.BoseFixB1B.sbKinCube v μ u
            (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ)) := by
    -- `sbKinCube` is FS's `𝒯_{B(u)}` at the cube cutoff, definitionally
    have hfun : ∀ Ψ : X n → ℝ, Work.UBBInputs8.tBwordInd (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u)
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u) (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
        ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Ψ = Work.BoseFixB1B.sbKinCube v μ u Ψ :=
      fun Ψ => (Work.BoseB1Cube.sbKinCube_eq_tBwordInd v μ u Ψ).symm
    calc Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
        = Work.UBBInputs8.tBwordInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
            (Work.BoseFixB1.bV v μ u) (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
              (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
            (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
            ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (Φ : X n → ℝ) := (hfun _).symm
      _ = ∑ S : Finset (Fin n), Work.UBBInputs8.tBwordInd (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u)
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
            ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
            (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ)) := hT
      _ = ∑ S : Finset (Fin n), Work.BoseFixB1B.sbKinCube v μ u
            (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ)) :=
          Finset.sum_congr rfl (fun S _ => hfun _)
  -- (4) the potential half (a multiplication form: `Φ² = Σ_S (slotPiece_S Φ)²`)
  have hpot : Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ)
      = ∑ S : Finset (Fin n),
          Work.BoseFixB1.sbPot h μ u
            (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ)) := by
    show Submission.BoseGases.qLHSword (Work.BoseFixB1.bSide v μ) μ
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u v)
        (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u) (Φ : X n → ℝ)
      = ∑ S : Finset (Fin n), Submission.BoseGases.qLHSword (Work.BoseFixB1.bSide v μ) μ
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u)
          (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ))
    refine Work.PerSector.qLHSword_eq_sum_slotPiece _ _ (fun S => ?_)
    -- the summand integrability: the sliding regime, at the slot piece of the *state*
    have h0 := Work.BoseFixB1B.integrableOn_slotPiece_sq_qLHSden_sliding (h := h)
      (M := Work.BoseFixB1.bM v μ) (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
      (μ := μ) (R0 := R) hM1 hℓ hd hv1 hR hv_supp hreg1 hreg2 u (k := S.card)
      (Φ := (Φ : X n → ℝ)) Φ.contDiff.continuous hCψ0 hCψ S
    have h0' : (fun x : X n =>
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) S
            (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) S.card (Φ : X n → ℝ)) x) ^ 2
          * Submission.BoseGases.qLHSden n (Work.BoseFixB1.bSide v μ) μ
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) x)
        = fun x : X n =>
            Submission.BoseGases.qLHSden n (Work.BoseFixB1.bSide v μ) μ
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u) x
            * (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u) S (Φ : X n → ℝ) x) ^ 2 := by
      funext x
      rw [Work.PerSector.slotPiece_sectorPiece_eq_of_card_eq (k := S.card) rfl (Φ : X n → ℝ),
        mul_comm]
    rw [h0'] at h0
    exact h0
  -- (5) assemble the two halves
  show Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ) + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ)
      = ∑ S : Finset (Fin n),
          (Work.BoseFixB1B.sbKinCube v μ u
              (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ))
            + Work.BoseFixB1.sbPot h μ u
              (Work.PerSector.slotPiece (Work.BoseFixB1.bA v μ u) S (Φ : X n → ℝ)))
  rw [hkin, hpot, Finset.sum_add_distrib]

end

end Work.BoseB1Cube
