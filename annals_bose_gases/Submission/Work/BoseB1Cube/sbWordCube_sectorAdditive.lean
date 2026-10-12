import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseB1Cube.tBdiagFormInd_cube_eq_sum_sectorPiece
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.sbWordCube_sectorAdditive`

**The sector additivity of the matched-window (single cube cutoff) sliding word `sbWordCube`.**

`sbWordCube v h μ u Φ = sbKinCube v μ u Φ + sbPot h μ u Φ` splits over the
`B(u)`-occupancy sectors `Φ_k = 1_{n_{B(u)} = k}·Φ` of the state: for every admissible `μ`,
every `n`, every box state `Φ` and every sliding centre `u`,

    sbWordCube v h μ u Φ = Σ_{k ≤ n} ( sbKinCube v μ u Φ_k + sbPot h μ u Φ_k ) .

This is the matched-window twin of the PROVED `Work.BoseFixB1.sbWordSectorAdditiveAdm` (the same
statement at the *ball* window `chiB`), and it is what lets the cube chapter push a per-`u`
inequality through the sector decomposition (`Work.BoseFixB1.nodeB1B_holds_of_cubePieces` consumes
`SlidingBCube` and `SmallBoxCollectedCube`, and the latter's per-box ledger is applied sector by
sector).

## The two halves

* **kinetic half** `sbKinCube v μ u Φ = Σ_k sbKinCube v μ u Φ_k`.  `sbKinCube` is
  *definitionally* FS's small-box kinetic word `𝒯_{B(u)} = tBwordInd` at the **cube** cutoff
  `chiSmallB M ℓ d u` (`sbKinCube_eq_tBwordInd`), so this is
  `Work.FockBridge.tBwordInd_eq_sum_sectorPiece` fed the two per-slot additivities
  (`cnPlusBoxInd_eq_sum_sectorPiece_sliding` for the gap row — it is window-free — and the cube
  twin `Work.BoseB1Cube.tBdiagFormInd_cube_eq_sum_sectorPiece` of the spectral row);
* **potential half** `sbPot h μ u Φ = Σ_k sbPot h μ u Φ_k` — `sbPot` is `qLHSwordB` at the
  localized kernels, whose sector additivity is
  `Work.BoseFixB1.qLHSwordB_eq_sum_sectorPiece_regime` (`Work.FockBridge.qLHSword_eq_sum_sectorPiece`
  with the `IntegrableOn` side condition discharged by the dilute regime).  As in the ball-window
  twin, this is the reason the `Adm`-threshold `ε₀` is needed at all: the potential half splits a
  *signed* Bochner integral.

The threshold `ε₀` below is the one supplied by `Work.BoseFixB1.exists_adm_regime` (the regime
`R ≤ ℓd/16`, `R ≤ ℓ·chiR0` of every supplier of the localised-kernel bounds).
-/

namespace Work.BoseB1Cube

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`sbKinCube` is FS's `𝒯_{B(u)}` at the cube cutoff**: the definitional identity exhibiting the
matched kinetic word as `tBwordInd` at the window `chiSmallB M ℓ d u`, the box `B(u) = dlBox ℓ d u`
(volume `boxMass ℓ d u`), the gap parameter `ℓd` and the spectral cutoff `sbCut μ (a v)`. -/
theorem sbKinCube_eq_tBwordInd (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixB1B.sbKinCube v μ u Φ
      = Work.UBBInputs8.tBwordInd (Work.BoseFixB1.bSide v μ)
          (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
          (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
          ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ := rfl

/-- **The cube-cutoff small-box kinetic word is sector-additive** at the raw box parameters:
`tBwordInd = tbGapCoeff·n₊ + Q_Bχ_B[√−Δ−c]₊²χ_BQ_B` splits over the `B(u)`-occupancy sectors.
This is `Work.FockBridge.tBwordInd_eq_sum_sectorPiece` with the gap additivity
`Work.BoseFixB1.cnPlusBoxInd_eq_sum_sectorPiece_sliding` (window-free) and the cube spectral
additivity `Work.BoseB1Cube.tBdiagFormInd_cube_eq_sum_sectorPiece`. -/
theorem tBwordInd_cube_eq_sum_sectorPiece {n : ℕ} {ℓ d c ε : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {M : ℕ} (hM : 4 ≤ M) (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u)
        (ℓ * d) ε c Φ
      = ∑ k ∈ Finset.range (n + 1),
          Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u)
            (ℓ * d) ε c (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) :=
  Work.FockBridge.tBwordInd_eq_sum_sectorPiece
    (fun i => Work.BoseFixB1.cnPlusBoxInd_eq_sum_sectorPiece_sliding hℓ hd u hΦ.continuous i)
    (fun i => tBdiagFormInd_cube_eq_sum_sectorPiece hℓ hd hM u hΦ i)

/-- **The matched kinetic word `sbKinCube` is sector-additive** at FS's per-box parameters
`ℓ = bSide v μ`, `d = bD v μ`, `M = bM v μ` and the sliding box `bA v μ u = dlBox ℓ d u`. -/
theorem sbKinCube_eq_sum_sectorPiece {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hℓ : 0 < Work.BoseFixB1.bSide v μ) (hd : 0 < Work.BoseFixB1.bD v μ)
    (hM4 : 4 ≤ Work.BoseFixB1.bM v μ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.BoseFixB1B.sbKinCube v μ u Φ
      = ∑ k ∈ Finset.range (n + 1),
          Work.BoseFixB1B.sbKinCube v μ u
            (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k Φ) := by
  have h := tBwordInd_cube_eq_sum_sectorPiece (ℓ := Work.BoseFixB1.bSide v μ)
    (d := Work.BoseFixB1.bD v μ) (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
    (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (M := Work.BoseFixB1.bM v μ) hℓ hd hM4 u hΦ
  have hdef : ∀ Ψ : Submission.BoseGases.X n → ℝ, Work.BoseFixB1B.sbKinCube v μ u Ψ
      = Work.UBBInputs8.tBwordInd (Work.BoseFixB1.bSide v μ)
          (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
          (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ)
          ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Ψ := fun Ψ => rfl
  rw [hdef, h]
  exact Finset.sum_congr rfl (fun k _ => (hdef _).symm)

/-- **The matched potential word `sbPot` is sector-additive** at FS's per-box parameters, under the
regime hypotheses `R ≤ ℓd/16` and `R ≤ ℓ·chiR0` (which make every sector summand of the localized
pairing word `qLHSwordB` Bochner-integrable).  This is
`Work.BoseFixB1.qLHSwordB_eq_sum_sectorPiece_regime`, i.e.
`Work.FockBridge.qLHSword_eq_sum_sectorPiece` with the `IntegrableOn` side condition discharged by
`Work.BoseFixB1.integrableOn_sectorPiece_sq_qLHSden_regime`. -/
theorem sbPot_eq_sum_sectorPiece {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} (hℓ : 0 < Work.BoseFixB1.bSide v μ) (hd : 0 < Work.BoseFixB1.bD v μ)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hreg1 : R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16)
    (hreg2 : R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1.sbPot h μ u Φ
      = ∑ k ∈ Finset.range (n + 1),
          Work.BoseFixB1.sbPot h μ u
            (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k Φ) := by
  have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  exact Work.BoseFixB1.qLHSwordB_eq_sum_sectorPiece_regime (h := h)
    (M := Work.BoseFixB1.bM v μ) (μ := μ) (ℓ := Work.BoseFixB1.bSide v μ)
    (d := Work.BoseFixB1.bD v μ) hM1 hℓ hd hv1 hR hv_supp hreg1 hreg2 u hΦc

theorem sbWordCube_sectorAdditive {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)
          = ∑ k ∈ Finset.range (n + 1),
              (Work.BoseFixB1B.sbKinCube v μ u
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k
                    (Φ : Submission.BoseGases.X n → ℝ))
                + Work.BoseFixB1.sbPot h μ u
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k
                    (Φ : Submission.BoseGases.X n → ℝ))) := by
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Work.BoseFixB1.exists_adm_regime hav hR
  refine ⟨ε₀, hε₀pos, fun μ hAdm n Φ u => ?_⟩
  obtain ⟨hreg1, hreg2⟩ := hε₀ μ hAdm
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM4 : 4 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hkin := sbKinCube_eq_sum_sectorPiece (v := v) (μ := μ) hℓ hd hM4 u Φ.contDiff
  have hpot := sbPot_eq_sum_sectorPiece (v := v) (h := h) (μ := μ) hℓ hd hv1 hR hv_supp
    hreg1 hreg2 u Φ.contDiff.continuous
  rw [Work.BoseFixB1B.sbWordCube, hkin, hpot, Finset.sum_add_distrib]

end Work.BoseB1Cube
