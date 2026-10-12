import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.cubeWindowPort
import Submission.Work.BoseB1Cube.rhs_slot_peel_low
import Submission.Work.BoseB1Cube.windowPlancherel_low
import Submission.Work.BoseFixB1B.tBwordInd_eq_slotSum_three
import Submission.Work.BoseFixB1S.mfBoxAbbrev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.cubeKinPeel`

The **cube-window Dirichlet identity**: the `‖p‖²`-weighted `p`-diagonal kinetic slot of the
FS small-box word at the *cosine-`M`-th-power* cube cutoff `chiSmallB M ℓ d u` equals the sum of
the slot Dirichlet energies of the windowed, `Q_B`-projected fibres:

    tBdiagFormInd ℓ (B(u)) V (chiSmallB M ℓ d u) (·)² Φ
      = Σ_i ∫_{abox N ℓ} Σ_{k∈Fin 3} (∂_{kcDir N i k}(χ_B(x_i)·(Q_{B,i}Ind Φ)))² .

This is the cube twin of the PROVED ball-window identity
`Work.BoseFixB1S.mfKinEqDirichletB1`; the only obstruction to copying its proof is that the
corpus's `Work.SmallBoxTBWord.tBdiagForm_sq_eq_dirichlet` (and its whole chain) is stated for
`ContDiff ℝ ⊤` windows, while `chiSmallB M ℓ d u` is only `ContDiff ℝ 3` (`M = 48` is hard-wired
by `fsParams`, see `Submission/Work/BoseFixB1S/win/chiSmallB_windowIntegrable.lean` §5 and the
`cubeWindowPort` docstring).  The `C³`-layer this needs is supplied by two companion modules of
this directory (both proved, `sorry`-free, axiom-clean):

* `Work.BoseB1Cube.windowPlancherel_low`
  (`Submission/Work/BoseB1Cube/windowPlancherel_low.lean`) — the windowed Plancherel identity
  `(2π)⁻³∫_p ‖p‖²‖kinFT(Wψ) p‖² = ∫_{acube a} Σ_k (∂_k(Wψ))²` at a `C¹` compactly supported
  window, from the PROVED `C¹` gradient Plancherel
  `Work.BoseFixB1S.gradient_plancherel_of_contDiff_one`;
* `Work.BoseB1Cube.rhs_slot_peel_low` (`.../rhs_slot_peel_low.lean`, with its chain-rule core
  `Work.BoseB1Cube.fderiv_slot_eq_fibre_low_aux`) — the `kcInsN` slot peel at a `C¹` weight
  (the `C^∞` version is `Work.SmallBoxTBWord.rhs_slot_peel`).

On top of them this module proves

* `tBdiagForm_slot_gen_low` — the per-slot identity, using the PROVED `C³` Fubini
  `Work.BoseFixB1B.swap_p_abox_tBamp_gen_three` (at `c = 0`, where `fsKinCoeff 0 ‖p‖ = ‖p‖²`)
  and the amplitude peel `Work.SmallBoxTBWord.tBamp_peel` (which needs only continuity);
* `tBdiagForm_sq_eq_dirichlet_low` — the resulting `C³` Dirichlet identity for `tBdiagForm`
  (the `C³` relaxation of `Work.SmallBoxTBWord.tBdiagForm_sq_eq_dirichlet`).

The target `cubeKinPeel` is the `chiSmallB` instance: the FS-faithful projection `boxQInd` is
reduced to the corpus's `boxQ` by `Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm` (the cutoff
vanishes off `dlBox ℓ d u`, `Work.SlotWord.chiSmallB_support_mem_dlBox`) together with
`chiSmallB_mul_boxQInd_eq`, exactly as in `Work.BoseFixB1S.mfKinEqDirichletB1`.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff
open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The per-slot Plancherel/Dirichlet identity at a `C³` window -/

/-- **Per-slot Dirichlet identity at a `C³` window.**  For a `C³` window `χ` with compact support
in the one-particle cube `acube a` and a smooth fibre `Φ`, the `i`-th `‖p‖²`-mode energy of the
windowed slot is the Dirichlet energy of the windowed many-particle slot,

`(2π)⁻³∫_p ‖p‖² (a³)⁻¹∫_{abox (n+1) a} ‖tBamp χ p Φ i x‖² = ∫_{abox (n+1) a} Σ_k (∂_{ik}(χ (· i) Φ))²`.

This is `Work.SmallBoxTBWord.tBdiagForm_slot_gen` with the window regularity relaxed from `C^∞`
to `C³`: step 1 (`tBamp_peel`) needs only continuity, the Fubini step uses the PROVED `C³`
`Work.BoseFixB1B.swap_p_abox_tBamp_gen_three`, the fibre Plancherel is
`Work.BoseB1Cube.windowPlancherel_low`, and the final peel is
`Work.BoseB1Cube.rhs_slot_peel_low`. -/
theorem tBdiagForm_slot_gen_low {a : ℝ} {χ : E3 → ℝ} {n : ℕ} (ha : 0 < a)
    (hχ : ContDiff ℝ 3 χ) (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ acube a)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin (n + 1)) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖p‖ ^ 2 *
        ((a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫ x in abox (n + 1) a, ∑ k : Fin 3,
          (fderiv ℝ (fun y : X (n + 1) => χ (y i) * Φ y) x (kcDir (n + 1) i k)) ^ 2 := by
  have hχsupp : ∀ z : E3, z ∉ acube a → χ z = 0 := Work.SmallBoxTBWord.chi_tsupp_vanishes htsupp
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  have hfs : ∀ p : E3, fsKinCoeff 0 ‖p‖ = ‖p‖ ^ 2 := by
    intro p
    rw [Submission.BoseGases.fsKinCoeff, sub_zero, max_eq_left (norm_nonneg p)]
  -- step 1: peel the slot and identify the fibre amplitude
  have hstep1 : (∫ p : E3, ‖p‖ ^ 2 *
        ((a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫ p : E3, fsKinCoeff 0 ‖p‖ *
          (∫ r in abox n a, ‖Work.SmallBoxTBWord.tBamp χ p Φ i (kcInsN n i (0, r))‖ ^ 2) := by
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    simp only []
    have hp : (a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2
        = ∫ r in abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i (kcInsN n i (0, r))‖ ^ 2 := by
      rw [Work.SmallBoxTBWord.tBamp_peel ha hχ.continuous hχsupp hΦ.continuous i p]
      refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
      simp only []
      rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT i p r 0]
    rw [hp, hfs p]
  -- step 2: Fubini in `(p, r)` (the PROVED `C³` exchange, at `c = 0`)
  rw [hstep1,
    (Work.BoseFixB1B.swap_p_abox_tBamp_gen_three (ℓ := a) (c := 0) ha χ hχ hcs Φ hΦ i).2]
  -- step 3: fibre-by-fibre windowed Plancherel
  have hper : ∀ r : X n, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, fsKinCoeff 0 ‖p‖ *
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i (kcInsN n i (0, r))‖ ^ 2
      = ∫ y in acube a, ∑ k : Fin 3,
          (fderiv ℝ (fun w : E3 => χ w * Φ (kcInsN n i (w, r))) y (kcStdBasis k)) ^ 2 := by
    intro r
    have hψ : ContDiff ℝ 1 (fun w : E3 => Φ (kcInsN n i (w, r))) :=
      (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)).of_le (by norm_num)
    have hw := windowPlancherel_low (a := a) (W := χ) (ψ := fun w : E3 => Φ (kcInsN n i (w, r)))
      ha hχ1 hcs htsupp hψ
    rw [← hw]
    congr 1
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    simp only []
    rw [hfs p, Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT i p r 0]
  rw [show (∫ r in abox n a, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, fsKinCoeff 0 ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i (kcInsN n i (0, r))‖ ^ 2)
      = ∫ r in abox n a, ∫ y in acube a, ∑ k : Fin 3,
          (fderiv ℝ (fun w : E3 => χ w * Φ (kcInsN n i (w, r))) y (kcStdBasis k)) ^ 2 from
    integral_congr_ae (Eventually.of_forall hper)]
  -- step 4: peel the Dirichlet energy back onto the many-particle box
  exact (rhs_slot_peel_low ha hχ1 hΦ i).symm

/-- **The Dirichlet identity for `tBdiagForm` at a `C³` window** — the `C³` relaxation of
`Work.SmallBoxTBWord.tBdiagForm_sq_eq_dirichlet`. -/
theorem tBdiagForm_sq_eq_dirichlet_low {a : ℝ} {A : Set E3} {volA : ℝ} {χ : E3 → ℝ} {n : ℕ}
    (ha : 0 < a) (hχ : ContDiff ℝ 3 χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ acube a) (hA : IsCompact A)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.SmallBoxTBWord.tBdiagForm a A volA χ (fun r => r ^ 2) Ψ
      = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) a, ∑ k : Fin 3,
          (fderiv ℝ (fun y : X (n + 1) => χ (y i) * Work.SmallBoxTBWord.boxQ volA A i Ψ y) x
            (kcDir (n + 1) i k)) ^ 2 := by
  unfold Work.SmallBoxTBWord.tBdiagForm
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact tBdiagForm_slot_gen_low ha hχ hcs htsupp
    (Work.SmallBoxTBWord.boxQ_contDiff_of_compact hA volA i hΨ) i

/-! ## 2. The target -/

/-- The box indicator carried by FS's `Q_{B,i}` is invisible to the cube cutoff
`chiSmallB M ℓ d u`, which vanishes off `dlBox ℓ d u` (the `chiSmallB` twin of the PROVED
`Work.BoseFixB1S.chiB_mul_boxQInd_eq`). -/
lemma chiSmallB_mul_boxQInd_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 1 ≤ M)
    (u : E3) {V : ℝ} {N : ℕ} (i : Fin N) (Φ : X N → ℝ) :
    (fun y : X N => chiSmallB M ℓ d u (y i) * Work.UBBInputs8.boxQInd V (dlBox ℓ d u) i Φ y)
      = fun y : X N => chiSmallB M ℓ d u (y i)
          * Work.SmallBoxTBWord.boxQ V (dlBox ℓ d u) i Φ y := by
  funext y
  rw [Work.UBBInputs9.A.boxQInd_eq_indicator_mul_boxQ]
  simp only []
  by_cases hy : y i ∈ dlBox ℓ d u
  · rw [Set.indicator_of_mem hy, one_mul]
  · have h0 : chiSmallB M ℓ d u (y i) = 0 := by
      by_contra h
      exact hy (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd h)
    rw [Set.indicator_of_notMem hy, zero_mul, h0, zero_mul, zero_mul]

/-- **The cube-window kinetic peel.**  At the cosine-`M`-th-power cube cutoff
`chiSmallB M ℓ d u` (`M ≥ 4`), the `‖p‖²`-weighted `p`-diagonal kinetic slot of the FS
small-box word is the sum over slots of the Dirichlet energy of the windowed, `Q_B`-projected
fibres.  This is the cube twin of `Work.BoseFixB1S.mfKinEqDirichletB1` at the regularities the
corpus can supply (`chiSmallB` is `C³`, not `C^∞`). -/
theorem cubeKinPeel {N : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : EuclideanSpace ℝ (Fin 3)}
    {V : ℝ} {M : ℕ} (hM : 4 ≤ M) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u) V
        (Submission.BoseGases.chiSmallB M ℓ d u) (fun r : ℝ => r ^ 2) Φ
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Submission.BoseGases.X N =>
              Submission.BoseGases.chiSmallB M ℓ d u (y i)
                * Work.UBBInputs8.boxQInd V (Submission.BoseGases.dlBox ℓ d u) i Φ y) x)
            (Submission.BoseGases.kcDir N i k) ^ 2 := by
  have hM1 : 1 ≤ M := by omega
  rcases N with _ | m
  · simp [Work.UBBInputs8.tBdiagFormInd]
  · have hχ3 : ContDiff ℝ 3 (chiSmallB M ℓ d u) :=
      Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u
    have hcs : HasCompactSupport (chiSmallB M ℓ d u) :=
      chiSmallB_hasCompactSupport hM1 hℓ u
    have htsupp : tsupport (chiSmallB M ℓ d u) ⊆ acube ℓ :=
      tsupport_chiSmallB_subset_acube hM1 hℓ u
    have hA : IsCompact (dlBox ℓ d u) := Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u
    have hzero : ∀ z : E3, z ∉ dlBox ℓ d u → chiSmallB M ℓ d u z = 0 := by
      intro z hz
      by_contra h
      exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hℓ hd h)
    rw [Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (fun r : ℝ => r ^ 2) Φ hzero]
    rw [tBdiagForm_sq_eq_dirichlet_low (n := m) hℓ hχ3 hcs htsupp hA hΦ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact congrArg (fun t : ℝ => t ^ 2)
      (congrArg (fun f : X (m + 1) → ℝ => fderiv ℝ f x (kcDir (m + 1) i k))
        (chiSmallB_mul_boxQInd_eq (V := V) hℓ hd hM1 u i Φ).symm)

end

end Work.BoseB1Cube
