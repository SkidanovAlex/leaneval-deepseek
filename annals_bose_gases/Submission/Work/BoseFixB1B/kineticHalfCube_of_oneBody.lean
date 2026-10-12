import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.chiSmallB_tBamp_decay_uniform
import Submission.Work.BoseFixB1B.jointMeasurable_chiSmallB_slotWord
import Submission.Work.BoseFixB1B.tBwordInd_eq_slotSum_three
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.kineticHalfCube_of_oneBody`

The matched-window (single cube cutoff) analogue of `Work.BoseFixB1.kineticHalf_of_oneBody`: the
**slot decomposition** of the cube-windowed sliding word `Work.BoseFixB1B.sbKinCube` reduces the
`N`-body kinetic half `KineticHalfCube` to its `N = 1` instance `OneBodyKineticHalfCube` plus the
`u`-marginal integrability `SbKinCubeMarginalIntegrable`.

The word is `cubeWord M ℓ d ε c u Φ = Work.UBBInputs8.tBwordInd ℓ (dlBox ℓ d u) (boxMass ℓ d u)
(chiSmallB M ℓ d u) (ℓd) ε c Φ` (`cubeWordDefs.lean`), and `sbKinCube` is its instantiation at
FS's parameters (`sbKinCube_eq_cubeWord`, which is `rfl`).  Everything is the frozen bookkeeping of
`Work.BoseFixB1.kineticHalf_of_oneBody` with the window `chiB ↦ chiSmallB`:

* `tBwordInd_eq_slotSum_three` — the pointwise slot decomposition at a `C³` window;
* `chiSmallB_tBamp_decay_uniform` — the `u`-uniform `(1+‖p‖)⁻³` decay of the windowed amplitude;
* `jointMeasurable_chiSmallB_slotWord` — joint measurability of the slot word;
* `cubeWord_uniform_bound` — the `u`-uniform bound and far vanishing (this file);
* `cubeWord_slotSwap` — the `u ↔ r` Fubini exchange (this file);
* `cubeWord_kineticSplit_slotSum` / `kineticHalfCube_of_oneBody` — the reduction and the target.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- The norm of a real number inside `ℂ` is its absolute value. -/
private lemma norm_ofReal_abs' (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-! ## 1. The `C³`-window facts of `chiSmallB` at FS's regularity `M ≥ 4` -/

section WindowFacts

variable {M : ℕ} {ℓ d : ℝ}

theorem chiSmallB_contDiff3 (hM : 4 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M ℓ d u) :=
  Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u

theorem chiSmallB_hasCompactSupport' (hM : 1 ≤ M) (hℓ : 0 < ℓ) (u : E3) :
    HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
  Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u

theorem chiSmallB_eq_zero_of_notMem_dlBox' (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    ∀ z, z ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  intro z hz
  by_contra h
  exact hz (Work.BoseFixB1S.win.support_chiSmallB_subset_dlBox hM hℓ hd u
    (Function.mem_support.mpr h))

end WindowFacts

/-! ## 2. The slot fibre: the one-slot amplitude is the amplitude of the ambient configuration -/

/-- The slot-`0` amplitude of the slot-`i` fibre of an `(n+1)`-particle state is the slot-`i`
amplitude of the state at the inserted configuration `kcInsN n i (0, r)`. -/
theorem tBamp_slotState1_eq (M : ℕ) {ℓ d : ℝ} {n : ℕ} (Φ : X (n + 1) → ℝ) (i : Fin (n + 1))
    (r : X n) (u p : E3) (x : X 1) :
    Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
        (Work.BSKinetic.slotState1 i Φ r) 0 x
      = Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p Φ i
          (Submission.BoseGases.kcInsN n i (0, r)) := by
  have hstate : ∀ z : E3, Work.BSKinetic.slotState1 i Φ r
        (Function.update x (0 : Fin 1) z) = Φ (Submission.BoseGases.kcInsN n i (z, r)) := by
    intro z
    have hupd : Function.update x (0 : Fin 1) z = fun _ : Fin 1 => z := by
      funext j; fin_cases j; simp
    rw [hupd, Work.BSKinetic.slotState1]
  simp only [Work.SmallBoxTBWord.tBamp]
  apply integral_congr_ae
  filter_upwards with z
  rw [Work.SmallBoxBridge.Fourier.update_kcInsN]
  simp only [hstate z]

/-! ## 3. The uniform bound and far vanishing of the cube word on slot fibres -/

/-- `fsKinCoeff c r ≤ 2(1+|c|)²(1+r)²`. -/
theorem fsKinCoeff_le_lin (c r : ℝ) (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ 2 * (1 + |c|) ^ 2 * (1 + r) ^ 2 := by
  have h1 := Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul c r
  have hK1 : r ^ 2 + c ^ 2 ≤ (1 + |c|) ^ 2 * (1 + r) ^ 2 := by
    have hcc : c ^ 2 ≤ (1 + |c|) ^ 2 := by nlinarith [abs_nonneg c, sq_abs c]
    have h1 : (1 : ℝ) ≤ (1 + |c|) ^ 2 := by nlinarith [abs_nonneg c]
    have hrr : r ^ 2 ≤ (1 + |c|) ^ 2 * r ^ 2 := by nlinarith [h1, sq_nonneg r]
    have hmid : (1 + |c|) ^ 2 + (1 + |c|) ^ 2 * r ^ 2
        ≤ (1 + |c|) ^ 2 * (1 + r) ^ 2 := by
      nlinarith [sq_nonneg (1 + |c|), sq_nonneg r, hr]
    linarith
  linarith

/-- **The `u`-uniform bound and far vanishing of the cube word on the slot fibres.** -/
theorem cubeWord_uniform_bound {M : ℕ} (hM : 4 ≤ M) {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (n : ℕ) (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 ≤ R ∧
      (∀ u : E3, R < ‖u‖ → ∀ (i : Fin (n + 1)) (r : X n),
          cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r) = 0) ∧
      (∀ (i : Fin (n + 1)) (r : X n), r ∈ Submission.BoseGases.abox n ℓ →
          ∀ u : E3, |cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)| ≤ K) := by
  classical
  have hM1 : 1 ≤ M := by omega
  obtain ⟨S, S1, hS, hS1, hfib⟩ := Work.BSKinetic.exists_fibre_bound hℓ n hΦ
  obtain ⟨C0, hC00, hC0⟩ := chiSmallB_tBamp_decay_uniform hM hℓ hd Φ hΦ
  obtain ⟨C1, hC10, hC1⟩ := chiSmallB_tBamp_decay_uniform hM hℓ hd
      (fun _ : X 1 => (1 : ℝ)) contDiff_const
  set D : ℝ := C0 + S * C1 with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set G : ℝ := (2 * (1 + |c|) ^ 2 * D ^ 2) * ∫ p : E3, (1 + ‖p‖) ^ (-(4 : ℝ)) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    refine mul_nonneg (by positivity) (integral_nonneg fun p => ?_)
    exact Real.rpow_nonneg (by positivity) _
  set K : ℝ := |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε| * (4 * S ^ 2 * ℓ ^ 3)
      + ((2 * Real.pi) ^ 3)⁻¹ * G with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact add_nonneg (mul_nonneg (abs_nonneg _) (by positivity))
      (mul_nonneg (by positivity) hG0)
  refine ⟨K, Real.sqrt 3 * (1 + d) / (2 * d), hK0,
    by positivity, ?_, ?_⟩
  · -- far vanishing
    intro u hu i r
    simp only [cubeWord]
    rw [Work.BSKinetic.dlBox_eq_empty_of_far hℓ hd hu]
    exact Work.BSKinetic.tBwordInd_empty_eq_zero ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.chiSmallB M ℓ d u) (ℓ * d) ε c _
  · -- the bound
    intro i r hr u
    have h0mem : (0 : E3) ∈ Submission.BoseGases.acube ℓ :=
      Submission.BoseGases.mem_acube_of_norm_le (le_of_lt hℓ) (by rw [norm_zero]; positivity)
    have hxmem : Submission.BoseGases.kcInsN n i (0, r) ∈ Submission.BoseGases.abox (n + 1) ℓ := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [Submission.BoseGases.kc_insN_apply_same]; exact h0mem
      · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
        rw [Submission.BoseGases.kc_insN_apply_succ]; exact hr j'
    have hχ3 : ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M ℓ d u) :=
      chiSmallB_contDiff3 hM hℓ hd u
    have hχcs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
      chiSmallB_hasCompactSupport' hM1 hℓ u
    have hχsupp : ∀ z, z ∉ Submission.BoseGases.dlBox ℓ d u →
        Submission.BoseGases.chiSmallB M ℓ d u z = 0 :=
      chiSmallB_eq_zero_of_notMem_dlBox' hM1 hℓ hd u
    have hψc : Continuous (Work.BSKinetic.slotState1 i Φ r) :=
      hΦ.continuous.comp
        ((Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r).continuous.comp
          (continuous_apply 0))
    -- the uniform pointwise amplitude bound
    have hAmpl : ∀ (p : E3) (x : X 1), x ∈ Submission.BoseGases.abox 1 ℓ →
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) 0
              (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ≤ D / (1 + ‖p‖) ^ 3 := by
      intro p x hx
      rw [Work.BoseBox.tBamp_boxQInd_eq_sub (Work.BSKinetic.slotState1 i Φ r) 0 p x 0
        hχsupp hχ3.continuous hχcs hψc]
      have h1 : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.BSKinetic.slotState1 i Φ r) 0 x‖ ≤ C0 / (1 + ‖p‖) ^ 3 := by
        rw [tBamp_slotState1_eq M Φ i r u p x]
        exact hC0 u i _ hxmem p
      have h2 : |Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) 0 (Work.BSKinetic.slotState1 i Φ r)
            (Function.update x 0 0)| ≤ S := by
        rw [Work.SmallBoxTBWord.boxP]
        have hcongr : (∫ z in Submission.BoseGases.dlBox ℓ d u,
              Work.BSKinetic.slotState1 i Φ r (Function.update (Function.update x 0 0) 0 z))
            = ∫ z in Submission.BoseGases.dlBox ℓ d u,
              Φ (Submission.BoseGases.kcInsN n i (z, r)) := by
          apply integral_congr_ae
          filter_upwards with z
          have hupd : Function.update (Function.update x (0 : Fin 1) (0 : E3)) (0 : Fin 1) z
              = fun _ : Fin 1 => z := by funext j; fin_cases j; simp
          rw [hupd, Work.BSKinetic.slotState1_apply_one]
        rw [hcongr]
        exact Work.BSKinetic.abs_mean_dlBox_le hℓ (hfib i r hr).1
      have h3 : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (fun _ : X 1 => (1 : ℝ)) 0 x‖ ≤ C1 / (1 + ‖p‖) ^ 3 :=
        hC1 u 0 x hx p
      calc ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.BSKinetic.slotState1 i Φ r) 0 x
            - ((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) 0 (Work.BSKinetic.slotState1 i Φ r)
                (Function.update x 0 0) : ℝ) : ℂ)
              * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                (fun _ : X 1 => (1 : ℝ)) 0 x‖
          ≤ ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.BSKinetic.slotState1 i Φ r) 0 x‖
            + ‖((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) 0 (Work.BSKinetic.slotState1 i Φ r)
                (Function.update x 0 0) : ℝ) : ℂ)
              * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                (fun _ : X 1 => (1 : ℝ)) 0 x‖ := norm_sub_le _ _
        _ = ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.BSKinetic.slotState1 i Φ r) 0 x‖
            + |Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) 0 (Work.BSKinetic.slotState1 i Φ r)
                (Function.update x 0 0)|
              * ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                (fun _ : X 1 => (1 : ℝ)) 0 x‖ := by
            rw [norm_mul, norm_ofReal_abs']
        _ ≤ C0 / (1 + ‖p‖) ^ 3 + S * (C1 / (1 + ‖p‖) ^ 3) :=
            add_le_add h1 (mul_le_mul h2 h3 (norm_nonneg _) hS)
        _ = D / (1 + ‖p‖) ^ 3 := by rw [hDdef]; ring
    -- the inner (`x`-)integral
    have haboxlt : (MeasureTheory.volume : Measure (X 1)) (Submission.BoseGases.abox 1 ℓ) < ⊤ :=
      Submission.BoseGases.abox_lt_top 1 ℓ hℓ.le
    have hinner : ∀ p : E3, (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) 0
              (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2
        ≤ (D / (1 + ‖p‖) ^ 3) ^ 2 := by
      intro p
      haveI : IsFiniteMeasure
          ((MeasureTheory.volume : Measure (X 1)).restrict (Submission.BoseGases.abox 1 ℓ)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact haboxlt⟩
      have hInt : (∫ x in Submission.BoseGases.abox 1 ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) 0
                (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)
          ≤ ∫ _x in Submission.BoseGases.abox 1 ℓ, (D / (1 + ‖p‖) ^ 3) ^ 2 := by
        refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          (integrable_const _) ?_
        refine (ae_restrict_iff' (Submission.BoseGases.abox_measurable 1 ℓ)).mpr
          (Eventually.of_forall fun x hx => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hAmpl p x hx) 2
      have hconst : (∫ _x in Submission.BoseGases.abox 1 ℓ, (D / (1 + ‖p‖) ^ 3) ^ 2)
          = (D / (1 + ‖p‖) ^ 3) ^ 2 * ℓ ^ 3 := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Submission.BoseGases.abox_volume 1 ℓ hℓ.le,
          ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (ℓ ^ 3) ^ 1), pow_one,
          smul_eq_mul, mul_comm]
      have h2 : (∫ x in Submission.BoseGases.abox 1 ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) 0
                (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)
          ≤ (D / (1 + ‖p‖) ^ 3) ^ 2 * ℓ ^ 3 := hInt.trans (le_of_eq hconst)
      calc (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) 0
                  (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2
          ≤ (ℓ ^ 3)⁻¹ * ((D / (1 + ‖p‖) ^ 3) ^ 2 * ℓ ^ 3) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (D / (1 + ‖p‖) ^ 3) ^ 2 := by
            rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 3 (ne_of_gt hℓ))]
            ring
    -- the outer (`p`-)integral
    have hGint : MeasureTheory.Integrable
        (fun p : E3 => (2 * (1 + |c|) ^ 2 * D ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ))) :=
      (integrable_one_add_norm (E := E3) (μ := (MeasureTheory.volume : Measure E3)) (r := 4)
        (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num)).const_mul _
    have houter : (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) 0
                  (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2))
        ≤ G := by
      have hpt : ∀ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) 0
                    (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)
          ≤ (2 * (1 + |c|) ^ 2 * D ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
        intro p
        have hbase : (0 : ℝ) < 1 + ‖p‖ := by positivity
        have hstep1 : Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) 0
                      (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)
            ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ * (D / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_left (hinner p) (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
        have hstep2 : Submission.BoseGases.fsKinCoeff c ‖p‖ * (D / (1 + ‖p‖) ^ 3) ^ 2
            ≤ (2 * (1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2) * (D / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_right (fsKinCoeff_le_lin c ‖p‖ (norm_nonneg p)) (sq_nonneg _)
        have hcollapse : (2 * (1 + |c|) ^ 2 * (1 + ‖p‖) ^ 2) * (D / (1 + ‖p‖) ^ 3) ^ 2
            = (2 * (1 + |c|) ^ 2 * D ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
          rw [Real.rpow_neg hbase.le, Real.rpow_ofNat, div_pow]
          field_simp
        linarith [hstep1, hstep2, hcollapse.le]
      calc (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
              ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) 0
                    (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2))
          ≤ ∫ p : E3, (2 * (1 + |c|) ^ 2 * D ^ 2) * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
            refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun p =>
              mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) ?_) hGint
              (Eventually.of_forall hpt)
            exact mul_nonneg (inv_nonneg.mpr (by positivity))
              (integral_nonneg fun x => sq_nonneg _)
        _ = G := by
          rw [hGdef, MeasureTheory.integral_const_mul]
    -- gap term
    have hgap : |Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Work.BSKinetic.slotState1 i Φ r)|
        ≤ 4 * S ^ 2 * ℓ ^ 3 := by
      refine Work.BSKinetic.cnPlusBoxInd_one_le hℓ ?_ ?_
      · intro z hz
        rw [Work.BSKinetic.slotState1_apply_one]
        exact (hfib i r hr).1 z hz.1
      · rw [show (∫ z in Submission.BoseGases.dlBox ℓ d u,
              Work.BSKinetic.slotState1 i Φ r (fun _ : Fin 1 => z))
            = ∫ z in Submission.BoseGases.dlBox ℓ d u,
              Φ (Submission.BoseGases.kcInsN n i (z, r)) from
            integral_congr_ae (Eventually.of_forall fun z =>
              Work.BSKinetic.slotState1_apply_one i Φ r z)]
        exact Work.BSKinetic.abs_mean_dlBox_le hℓ (hfib i r hr).1
    -- assemble
    have hword : cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)
        = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
            * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (Work.BSKinetic.slotState1 i Φ r)
          + ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) 0
                      (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2) := by
      simp only [cubeWord, Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
        Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.cnPlusBoxInd, Fin.sum_univ_one]
    rw [hword, hKdef]
    have hSpecnn : (0 : ℝ) ≤ ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) 0
                (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2) :=
      integral_nonneg fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg fun x => sq_nonneg _))
    calc |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
            * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (Work.BSKinetic.slotState1 i Φ r)
          + ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) 0
                      (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)|
        ≤ |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
            * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (Work.BSKinetic.slotState1 i Φ r)|
          + |((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) 0
                      (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2)| := abs_add_le _ _
      _ = |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε|
            * |Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (Work.BSKinetic.slotState1 i Φ r)|
          + ((2 * Real.pi) ^ 3)⁻¹ * |(∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) 0
                      (Work.BSKinetic.slotState1 i Φ r)) 0 x‖ ^ 2))| := by
          congr 1
          · rw [abs_mul]
          · rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹)]
      _ ≤ |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε| * (4 * S ^ 2 * ℓ ^ 3)
          + ((2 * Real.pi) ^ 3)⁻¹ * G := by
          refine add_le_add (mul_le_mul_of_nonneg_left hgap (abs_nonneg _)) ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [abs_of_nonneg hSpecnn]
          exact houter

/-! ## 4. The `u ↔ r` Fubini exchange at the cube window -/

/-- **The slot decomposition of the cube word, integrated in `u`.**  This is
`Work.BSKinetic.tBwordBInd_slotSwap_nosupp` with the ball window replaced by the cube window
`chiSmallB M ℓ d u`; the pointwise identity is `tBwordInd_eq_slotSum_three`, the uniform bound and
far vanishing are `cubeWord_uniform_bound`, and the measurability is
`jointMeasurable_chiSmallB_slotWord`. -/
theorem cubeWord_slotSwap {M : ℕ} (hM : 4 ≤ M) {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    (∫ u : E3, cubeWord M ℓ d ε c u Φ)
        = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ, ∫ u : E3,
            cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)
    ∧ (∀ i : Fin (n + 1), MeasureTheory.Integrable
        (fun r : X n => ∫ u : E3,
            cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
        (Work.BSKinetic.boxMu n ℓ)) := by
  classical
  have hM1 : 1 ≤ M := by omega
  haveI hfin : IsFiniteMeasure (Work.BSKinetic.boxMu n ℓ) :=
    Work.BSKinetic.isFiniteMeasure_boxMu n ℓ hℓ.le
  obtain ⟨K, R, hK0, hR0, hfar, hsmall⟩ := cubeWord_uniform_bound hM hℓ hd n Φ hΦ
  have hin : ∀ i : Fin (n + 1), MeasureTheory.Integrable
      (Function.uncurry (fun (u : E3) (r : X n) =>
        cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)))
      ((MeasureTheory.volume : Measure E3).prod (Work.BSKinetic.boxMu n ℓ)) := by
    intro i
    refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
      (μ := (MeasureTheory.volume : Measure E3)) (ν := Work.BSKinetic.boxMu n ℓ)
      (f := fun (u : E3) (r : X n) =>
        cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
      (g := fun _ : X n => ENNReal.ofReal K
        * (MeasureTheory.volume : Measure E3) (Metric.closedBall (0 : E3) R))
      (jointMeasurable_chiSmallB_slotWord hM hℓ hd n Φ hΦ i) ?_ ?_
    · rw [MeasureTheory.lintegral_const, Work.BSKinetic.boxMu, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (MeasureTheory.measure_closedBall_lt_top (x := (0 : E3)) (r := R)).ne)
        (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
    · rw [Work.BSKinetic.boxMu,
        MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
      filter_upwards with r hr
      calc ∫⁻ u, ENNReal.ofReal ‖cubeWord M ℓ d ε c u
              (Work.BSKinetic.slotState1 i Φ r)‖
          ≤ ∫⁻ u, ENNReal.ofReal K
              * (Metric.closedBall (0 : E3) R).indicator (fun _ => (1 : ENNReal)) u := by
            apply lintegral_mono; intro u
            show ENNReal.ofReal ‖cubeWord M ℓ d ε c u
                (Work.BSKinetic.slotState1 i Φ r)‖
                ≤ ENNReal.ofReal K
                  * (Metric.closedBall (0 : E3) R).indicator (fun _ => (1 : ENNReal)) u
            by_cases hu : u ∈ Metric.closedBall (0 : E3) R
            · rw [Set.indicator_of_mem hu, mul_one]
              exact ENNReal.ofReal_le_ofReal (by
                rw [Real.norm_eq_abs]; exact hsmall i r hr u)
            · rw [Set.indicator_of_notMem hu, mul_zero]
              have hu' : R < ‖u‖ := by
                have h := hu
                rw [Metric.mem_closedBall, dist_zero_right] at h
                exact not_le.mp h
              rw [hfar u hu' i r]
              simp
        _ = ENNReal.ofReal K * (MeasureTheory.volume : Measure E3)
              (Metric.closedBall (0 : E3) R) := by
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            rw [MeasureTheory.lintegral_indicator (Metric.isClosed_closedBall.measurableSet),
              MeasureTheory.setLIntegral_one]
  refine ⟨?_, ?_⟩
  · rw [show (∫ u : E3, cubeWord M ℓ d ε c u Φ)
        = ∫ u : E3, ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
            cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r) from by
      apply integral_congr_ae
      filter_upwards with u
      exact tBwordInd_eq_slotSum_three hℓ hd n u (Submission.BoseGases.chiSmallB M ℓ d u)
        (chiSmallB_contDiff3 hM hℓ hd u) (chiSmallB_hasCompactSupport' hM1 hℓ u)
        (chiSmallB_eq_zero_of_notMem_dlBox' hM1 hℓ hd u) Φ hΦ]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (n + 1)) (u : E3) => ∫ r in Submission.BoseGases.abox n ℓ,
        cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
      (fun i _ => ((hin i).integral_prod_left))]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ∫ a : E3, ∫ r, cubeWord M ℓ d ε c a (Work.BSKinetic.slotState1 i Φ r)
          ∂(Work.BSKinetic.boxMu n ℓ)
        = ∫ r, ∫ u : E3, cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)
          ∂(MeasureTheory.volume : Measure E3) ∂(Work.BSKinetic.boxMu n ℓ)
    rw [MeasureTheory.integral_integral_swap (μ := (MeasureTheory.volume : Measure E3))
      (ν := Work.BSKinetic.boxMu n ℓ) (hin i)]
  · intro i
    exact (hin i).integral_prod_right

/-! ## 5. The `N`-body ⟸ `N = 1` slot reduction at the cube window -/

/-- **The cube-windowed kinetic split.**  The `N`-body kinetic half of FS `eq:BSsliding2` at the
single cube cutoff follows from its `N = 1` instance, by the index shift, the slot decomposition of
`kinFormB` (`kinHalf_kinFormB_succ`), of `cnPlus` (`kinHalf_cnPlus_slotSum`) and of the cube word
(`cubeWord_slotSwap`). -/
theorem cubeWord_kineticSplit_slotSum {M : ℕ} (hM : 4 ≤ M) {ℓ d s εT b c : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d)
    (h1 : ∀ φ : X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ φ
          + (∫ u : E3, cubeWord M ℓ d εT c u φ)
        ≤ Work.BoseKinLoc.kinFormB 1 ℓ d s εT b φ) :
    ∀ (n : ℕ) (Φ : X n → ℝ), ContDiff ℝ (⊤ : ENat) Φ →
      (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ Φ
        + (∫ u : E3, cubeWord M ℓ d εT c u Φ)
      ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b Φ := by
  intro n
  rcases n with _ | m
  · intro Φ hΦ
    have hzero : ∀ u : E3, cubeWord M ℓ d εT c u (Φ : X 0 → ℝ) = 0 := by
      intro u
      simp only [cubeWord, Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
        Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.cnPlusBoxInd, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, add_zero]
    rw [show Submission.BoseGases.cnPlus ℓ Φ = 0 by simp [Submission.BoseGases.cnPlus],
      show (∫ u : E3, cubeWord M ℓ d εT c u Φ) = 0 by
        rw [show (fun u : E3 => cubeWord M ℓ d εT c u Φ) = fun _ => (0 : ℝ) from
          funext hzero, MeasureTheory.integral_zero],
      show Work.BoseKinLoc.kinFormB 0 ℓ d s εT b Φ = 0 by simp [Work.BoseKinLoc.kinFormB]]
    norm_num
  · intro Φ hΦ
    obtain ⟨hK, hKi⟩ := cubeWord_slotSwap hM hℓ hd m Φ hΦ
    have hF := Work.BoseFixB1.kinHalf_kinFormB_succ (d := d) (s := s) (εT := εT) (b := b)
      hℓ m Φ hΦ
    have hCn : ∀ i : Fin (m + 1), MeasureTheory.IntegrableOn
        (fun r : X m => (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ
            (Work.BSKinetic.slotState1 i Φ r)) (Submission.BoseGases.abox m ℓ) :=
      fun i => (Work.BSKinetic.integrable_cnPlus_slotState1 hℓ m Φ hΦ i).const_mul _
    have hB : ∀ i : Fin (m + 1), MeasureTheory.IntegrableOn
        (fun r : X m => ∫ u : E3,
            cubeWord M ℓ d εT c u (Work.BSKinetic.slotState1 i Φ r))
        (Submission.BoseGases.abox m ℓ) := fun i => hKi i
    have hC : ∀ i : Fin (m + 1), MeasureTheory.IntegrableOn
        (fun r : X m => Work.BoseKinLoc.kinFormB 1 ℓ d s εT b
            (Work.BSKinetic.slotState1 i Φ r))
        (Submission.BoseGases.abox m ℓ) :=
      fun i => Work.BoseFixB1.kinHalf_integrable_kinFormB_slotState1 (d := d) (s := s)
        (εT := εT) (b := b) hℓ m Φ hΦ i
    have hLHS : (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ Φ
        + (∫ u : E3, cubeWord M ℓ d εT c u Φ)
        = ∑ i : Fin (m + 1),
            ((∫ r in Submission.BoseGases.abox m ℓ,
                (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ
                  (Work.BSKinetic.slotState1 i Φ r))
              + ∫ r in Submission.BoseGases.abox m ℓ,
                  ∫ u : E3, cubeWord M ℓ d εT c u (Work.BSKinetic.slotState1 i Φ r)) := by
      rw [Work.BoseFixB1.kinHalf_cnPlus_slotSum hℓ m Φ hΦ, hK, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    have hper : ∀ i : Fin (m + 1),
        ((∫ r in Submission.BoseGases.abox m ℓ,
            (b / (2 * ℓ ^ 2)) * Submission.BoseGases.cnPlus ℓ
              (Work.BSKinetic.slotState1 i Φ r))
          + ∫ r in Submission.BoseGases.abox m ℓ,
              ∫ u : E3, cubeWord M ℓ d εT c u (Work.BSKinetic.slotState1 i Φ r))
        ≤ ∫ r in Submission.BoseGases.abox m ℓ,
            Work.BoseKinLoc.kinFormB 1 ℓ d s εT b (Work.BSKinetic.slotState1 i Φ r) := by
      intro i
      rw [← MeasureTheory.integral_add (hCn i) (hB i)]
      refine MeasureTheory.integral_mono ((hCn i).add (hB i)) (hC i) fun r => ?_
      exact h1 (Work.BSKinetic.slotState1 i Φ r)
        (Work.BSKinetic.contDiff_slotState1 hΦ i r)
    rw [hLHS, hF]
    exact Finset.sum_le_sum fun i _ => hper i

/-! ## 6. The target -/

theorem kineticHalfCube_of_oneBody {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (h1 : Work.BoseFixB1B.OneBodyKineticHalfCube v h)
    (hI : Work.BoseFixB1B.SbKinCubeMarginalIntegrable v) :
    Work.BoseFixB1B.KineticHalfCube v h := by
  obtain ⟨ε₁, hε₁, H1⟩ := h1
  obtain ⟨ε₂, hε₂, HI⟩ := hI
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun μ hAdm n Φ => ⟨?_, ?_⟩⟩
  · exact HI μ (Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)) n Φ
  · have hAdm1 : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm1
    have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm1
    have hM4 : 4 ≤ Work.BoseFixB1.bM v μ := by rw [bM_eq_mValue]; exact four_le_mValue
    have h1' : ∀ φ : X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
        ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
            / (2 * Work.BoseFixB1.bSide v μ ^ 2))
          * Submission.BoseGases.cnPlus (Work.BoseFixB1.bSide v μ) φ
          + (∫ u : E3, cubeWord (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u φ)
        ≤ Work.BoseKinLoc.kinFormB 1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b φ := by
      intro φ hφ
      exact H1 μ hAdm1 φ hφ
    have hmain := cubeWord_kineticSplit_slotSum (M := Work.BoseFixB1.bM v μ) hM4
      (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
      (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
      (εT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
      (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) hℓ hd h1'
      n (Φ : X n → ℝ) Φ.contDiff
    exact hmain

end Work.BoseFixB1B

