import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Cube.Loc.fibreSplitAux
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Cube.Loc.fsKinPGen_chiSmallB_integrable`

`p`-integrability of the `fsKinCoeff`-weighted slot content

    p ↦ [‖p‖ − c]₊² · (ℓ³)⁻¹ · ∫_{abox N ℓ} ‖tBamp χ_B p (Q_{B,i}Ψ) i x‖²

at the **sliding** geometry `ℓ = bSide v μ`, `d = bD v μ`, `M = bM v μ = 48`,
`B = bA v μ u = dlBox ℓ d u`, `|B| = bV v μ u = boxMass ℓ d u`, `c = sbCut μ (a v)` and the
sliding window `χ_B = chiSmallB M ℓ d u`.  This is the `hint`-hypothesis of the Step-Loc fibre
split (`Submission/Work/BoseFixB1/Cube/Loc/FINDING_sbWordCube_fibreSplit.md` §6).

## Route

The three cases are decided by the **degeneracy of the box**, and only one of them is analytic:

* `ℓ ≤ 0`: the ambient box `abox N ℓ` is null (`N ≥ 1`), so the inner integral — and hence the
  whole integrand — vanishes identically;
* `0 < ℓ`, `|B| ≤ 0`: then `|B| = 0`, i.e. `B` is a null set.  The box projection degenerates
  (`boxPInd = (1/0)·… = 0`) so `Q_{B,i}Ψ = 1_B(x_i)Ψ`, and the amplitude is the integral of a
  function vanishing a.e. — again `0`;
* `0 < ℓ`, `0 < |B|`: the honest case.  Here `ℓ > 0` forces `μ·(a v) > 0` (the `(−1/2)`-power
  in `sideAt` is identically `0` on the non-positive half-line), hence `d > 0`, `M = 48` and
  `c > 0`, and `Work.BoseFixB1S.win.slotContentIntegrableC2` (the `C²`-regularity slot
  integrability of the sliding window) applies verbatim.

⚠ Scratch files in this directory written by this session and **not** part of the development
(no declaration of the target depends on them): `_probe_fsKinPGen.lean`, `_probe2.lean`
(environment/file-search probes, `#check`-only) and `_ax_fsk.lean` (`#print axioms` probe).
They are kept in place, per the project convention.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseFixB1.Cube.Loc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The `rpow` convention on the non-positive half-line -/

/-- `x ^ (-(1/2)) = 0` for `x ≤ 0` (the `Real.rpow` convention: for `x < 0` the definition is
`exp (log x * y) * cos (yπ)`, which vanishes at `y = -1/2`; for `x = 0` it is `Real.zero_rpow`). -/
lemma rpow_negHalf_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : x ^ (-(1 / 2) : ℝ) = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.rpow_def_of_neg h]
    have hc : Real.cos ((-(1 / 2) : ℝ) * Real.pi) = 0 := by
      rw [show (-(1 / 2) : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg,
        Real.cos_pi_div_two]
    rw [hc, mul_zero]
  · subst h
    rw [Real.zero_rpow (by norm_num : (-(1 / 2) : ℝ) ≠ 0)]

/-! ## 2. The parameters at FS's choice -/

lemma bSide_eq (v : E3 → ℝ) (μ : ℝ) :
    Work.BoseFixB1.bSide v μ
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(3 / 2 : ℝ) / 323)
          * (μ * _root_.BoseGases.a v) ^ (-(1 / 2) : ℝ) := by
  simp [Work.BoseFixB1.bSide, Work.BoseBox.sideAt, Work.BoseBox.boxSide,
    Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]

lemma bM_eq (v : E3 → ℝ) (μ : ℝ) : Work.BoseFixB1.bM v μ = 48 := by
  simp [Work.BoseFixB1.bM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
    Work.BoseBox.mValue]

lemma bD_eq (v : E3 → ℝ) (μ : ℝ) :
    Work.BoseFixB1.bD v μ = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((6 : ℝ) / 323) := by
  simp [Work.BoseFixB1.bD, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
    Work.BoseBox.fsXp]

lemma bS_eq (v : E3 → ℝ) (μ : ℝ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323) := by
  simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]

/-- **A positive sliding side forces `μ·(a v) > 0`**: `bSide v μ` is the product of
`(μ(a v)³)^{−3/646}` with `(μ a v)^{−1/2}`, and the second factor vanishes identically on
`μ a v ≤ 0`. -/
lemma mul_a_pos_of_bSide_pos {v : E3 → ℝ} {μ : ℝ} (h : 0 < Work.BoseFixB1.bSide v μ) :
    0 < μ * _root_.BoseGases.a v := by
  by_contra hc
  have hc' : μ * _root_.BoseGases.a v ≤ 0 := le_of_not_gt hc
  have h0 : Work.BoseFixB1.bSide v μ = 0 := by
    rw [bSide_eq v μ, rpow_negHalf_eq_zero_of_nonpos hc', mul_zero]
  linarith

/-- `0 < bSide v μ` forces the diluteness parameter `μ(a v)³` to be positive. -/
lemma cube_mul_pos_of_bSide_pos {v : E3 → ℝ} {μ : ℝ} (h : 0 < Work.BoseFixB1.bSide v μ) :
    0 < μ * (_root_.BoseGases.a v) ^ 3 := by
  have ha := mul_a_pos_of_bSide_pos h
  have ha0 : _root_.BoseGases.a v ≠ 0 := fun hz => by simp [hz] at ha
  have h2 : 0 < (_root_.BoseGases.a v) ^ 2 := by
    rw [pow_two]; exact mul_self_pos.mpr ha0
  have heq : μ * (_root_.BoseGases.a v) ^ 3
      = (μ * _root_.BoseGases.a v) * (_root_.BoseGases.a v) ^ 2 := by ring
  rw [heq]
  exact mul_pos ha h2

lemma bD_pos_of_bSide_pos {v : E3 → ℝ} {μ : ℝ} (h : 0 < Work.BoseFixB1.bSide v μ) :
    0 < Work.BoseFixB1.bD v μ := by
  rw [bD_eq]
  exact Real.rpow_pos_of_pos (cube_mul_pos_of_bSide_pos h) _

lemma sbCut_pos_of_bSide_pos {v : E3 → ℝ} {μ : ℝ} (h : 0 < Work.BoseFixB1.bSide v μ) :
    0 < Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) := by
  have ht := cube_mul_pos_of_bSide_pos h
  have hd : 0 < Work.BoseFixB1.bD v μ := bD_pos_of_bSide_pos h
  have hs : 0 < (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323) :=
    Real.rpow_pos_of_pos ht _
  rw [Work.BoseFixB1.sbCut, bS_eq v μ]
  exact inv_pos.mpr (mul_pos (mul_pos hd hs) h)

/-! ## 3. The degeneracy lemmas for the box -/

/-- `boxMass` is nonnegative (it is the `toReal` of a measure of a set). -/
lemma boxMass_nonneg (ℓ d : ℝ) (u : E3) : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  exact ENNReal.toReal_nonneg

/-- **The ambient box is null when `ℓ ≤ 0`** (and `N ≥ 1`): it is contained in `abox N 0`, whose
volume is `(0³)^N = 0`. -/
lemma abox_measure_zero_of_nonpos {N : ℕ} (hN : 0 < N) {ℓ : ℝ} (hℓ : ℓ ≤ 0) :
    (volume : Measure (Submission.BoseGases.X N)) (Submission.BoseGases.abox N ℓ) = 0 := by
  have hsub : Submission.BoseGases.abox N ℓ ⊆ Submission.BoseGases.abox N 0 := by
    intro x hx
    rw [Submission.BoseGases.mem_abox_iff_coord] at hx ⊢
    intro i m
    have h1 := hx i m
    simp only [Set.mem_Icc, neg_zero, zero_div] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  refine MeasureTheory.measure_mono_null hsub ?_
  rw [Submission.BoseGases.abox_volume N 0 le_rfl]
  rw [show ((0 : ℝ) ^ 3) ^ N = 0 by
    rw [show (0 : ℝ) ^ 3 = 0 by norm_num, zero_pow hN.ne']]
  exact ENNReal.ofReal_zero

/-- **A vanishing box mass makes the box null**: `boxMass ℓ d u = 0` means
`volume (dlBox ℓ d u) = 0` (the box is contained in the finite-measure cube `acube ℓ`,
`ℓ > 0`). -/
lemma volume_dlBox_eq_zero_of_boxMass_eq_zero {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : E3}
    (h : Work.SmallBoxSliding.boxMass ℓ d u = 0) :
    (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) = 0 := by
  have h1 : ((volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u)).toReal = 0 := by
    rw [← MeasureTheory.Measure.real_def, ← Work.SmallBoxSliding.boxMass_eq_measureReal]
    exact h
  rcases (ENNReal.toReal_eq_zero_iff _).mp h1 with hh | hh
  · exact hh
  · exact absurd hh (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))

/-- Almost every point avoids a null box. -/
lemma ae_notMem_dlBox_of_boxMass_eq_zero {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : E3}
    (h : Work.SmallBoxSliding.boxMass ℓ d u = 0) :
    ∀ᵐ z ∂(volume : Measure ℝ³), z ∉ Submission.BoseGases.dlBox ℓ d u := by
  have hvol := volume_dlBox_eq_zero_of_boxMass_eq_zero hℓ h
  have hset : {z : ℝ³ | ¬ z ∉ Submission.BoseGases.dlBox ℓ d u}
      = Submission.BoseGases.dlBox ℓ d u := by
    ext z; simp
  rw [MeasureTheory.ae_iff, hset]
  exact hvol

/-! ## 4. The target -/

theorem fsKinPGen_chiSmallB_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ (N : ℕ) (Ψ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ENat) Ψ → ∀ i : Fin N,
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖ *
          ((((Work.BoseFixB1.bSide v μ) ^ 3)⁻¹) *
            ∫ x in Submission.BoseGases.abox N (Work.BoseFixB1.bSide v μ),
              ‖Work.SmallBoxTBWord.tBamp
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u) p
                (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i Ψ)
                i x‖ ^ 2)) := by
  intro N Ψ hΨ i
  by_cases hN : N = 0
  · subst hN
    exact i.elim0
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  by_cases hℓ : 0 < Work.BoseFixB1.bSide v μ
  · by_cases hV : 0 < Work.BoseFixB1.bV v μ u
    · -- ### the honest case: the `C²`-slot integrability of the sliding window
      have hd : 0 < Work.BoseFixB1.bD v μ := bD_pos_of_bSide_pos hℓ
      have hc : 0 < Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) :=
        sbCut_pos_of_bSide_pos hℓ
      have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by rw [bM_eq v μ]; norm_num
      have hM3 : 2 + 1 ≤ Work.BoseFixB1.bM v μ := by rw [bM_eq v μ]; norm_num
      have hvol : Work.BoseFixB1.bV v μ u = (volume (Work.BoseFixB1.bA v μ u)).toReal :=
        (Work.SmallBoxSliding.boxMass_eq_measureReal (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u).trans
          (MeasureTheory.Measure.real_def (volume : Measure ℝ³)
            (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u))
      exact Work.BoseFixB1S.win.slotContentIntegrableC2 (n := N)
        (a := Work.BoseFixB1.bSide v μ) (volA := Work.BoseFixB1.bV v μ u)
        (Ac := Work.BoseFixB1.bA v μ u) hℓ
        (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
        (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
        hvol hV
        (Work.BoseFixB1S.win.contDiff_chiSmallB 2 (Work.BoseFixB1.bM v μ) hM3
          (ne_of_gt hℓ) (ne_of_gt hd) u)
        (Submission.BoseGases.chiSmallB_hasCompactSupport hM1 hℓ u)
        (fun z hz => Work.BoseFixB1S.win.chiSmallB_eq_zero_of_not_mem_dlBox hM1 hℓ hd u z hz)
        (fun z => Work.BoseFixB1S.win.chiSmallB_nonneg (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u z)
        hc hΨ i
    · -- ### `|B| ≤ 0`: the box is null
      have hV0 : Work.BoseFixB1.bV v μ u = 0 :=
        le_antisymm (le_of_not_gt hV) (boxMass_nonneg (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
      have hAae : ∀ᵐ z ∂(volume : Measure ℝ³),
          z ∉ Work.BoseFixB1.bA v μ u :=
        ae_notMem_dlBox_of_boxMass_eq_zero hℓ hV0
      have hQ : ∀ y : Submission.BoseGases.X N,
          Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i Ψ y
            = (Work.BoseFixB1.bA v μ u).indicator (fun _ => (1 : ℝ)) (y i) * Ψ y := by
        intro y
        simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
        rw [hV0]
        simp
      have htb : ∀ (p : E3) (x : Submission.BoseGases.X N),
          Work.SmallBoxTBWord.tBamp
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) p
            (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i Ψ)
            i x = 0 := by
        intro p x
        rw [Work.SmallBoxTBWord.tBamp]
        refine MeasureTheory.integral_eq_zero_of_ae ?_
        filter_upwards [hAae] with z hz
        rw [hQ]
        simp only [Function.update_self]
        rw [Set.indicator_of_notMem hz]
        simp
      have hI : ∀ p : E3, (∫ x in Submission.BoseGases.abox N (Work.BoseFixB1.bSide v μ),
          ‖Work.SmallBoxTBWord.tBamp
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) p
            (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i Ψ)
            i x‖ ^ 2) = 0 := by
        intro p
        simp only [htb p]
        simp
      have hzero : (fun p : E3 =>
          Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖ *
            ((((Work.BoseFixB1.bSide v μ) ^ 3)⁻¹) *
              ∫ x in Submission.BoseGases.abox N (Work.BoseFixB1.bSide v μ),
                ‖Work.SmallBoxTBWord.tBamp
                  (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
                    (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u) p
                  (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                    i Ψ) i x‖ ^ 2)) = fun _ => 0 := by
        funext p
        simp only [hI p]
        ring
      rw [hzero]
      exact integrable_zero E3 ℝ (volume : Measure E3)
  · -- ### `ℓ ≤ 0`: the ambient box is null
    have hℓ0 : Work.BoseFixB1.bSide v μ ≤ 0 := le_of_not_gt hℓ
    have hvol : (volume : Measure (Submission.BoseGases.X N))
        (Submission.BoseGases.abox N (Work.BoseFixB1.bSide v μ)) = 0 :=
      abox_measure_zero_of_nonpos hNpos hℓ0
    have hI : ∀ p : E3, (∫ x in Submission.BoseGases.abox N (Work.BoseFixB1.bSide v μ),
        ‖Work.SmallBoxTBWord.tBamp
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) p
          (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u) i Ψ)
          i x‖ ^ 2) = 0 := fun p => MeasureTheory.setIntegral_measure_zero _ hvol
    have hzero : (fun p : E3 =>
        Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖ *
          ((((Work.BoseFixB1.bSide v μ) ^ 3)⁻¹) *
            ∫ x in Submission.BoseGases.abox N (Work.BoseFixB1.bSide v μ),
              ‖Work.SmallBoxTBWord.tBamp
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u) p
                (Work.UBBInputs8.boxQInd (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                  i Ψ) i x‖ ^ 2)) = fun _ => 0 := by
      funext p
      simp only [hI p]
      ring
    rw [hzero]
    exact integrable_zero E3 ℝ (volume : Measure E3)

end Work.BoseFixB1.Cube.Loc
