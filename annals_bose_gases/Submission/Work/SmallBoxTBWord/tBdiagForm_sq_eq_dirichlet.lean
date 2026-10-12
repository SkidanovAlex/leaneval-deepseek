import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.swap_p_slot
import Submission.Work.SmallBoxTBWord.tBamp_peel
import Submission.Work.SmallBoxTBWord.windowPlancherel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The diagonal `p`-form of `𝒯_B` with the squared symbol equals the Dirichlet form

`tBdiagForm a A volA χ (·)² Ψ` is the `p`-space diagonal form of the one-body operator
`Σ_i Q_{B,i}χ_i(−Δ_i)χ_iQ_{B,i}`.  This module proves that it is *exactly* the sum of the
slot Dirichlet energies of the windowed, `Q_B`-projected fibres:

    `tBdiagForm a A volA χ (·)² Ψ
        = Σ_i ∫_{abox (n+1) a} Σ_k (∂_{kcDir (n+1) i k}(χ(x_i)·Q_{B,i}Ψ))²`.

The proof is per slot (`tBdiagForm_slot_gen`, for an arbitrary smooth `Φ` in place of
`Q_{B,i}Ψ`): rewrite `(a³)⁻¹∫_{abox}‖tBamp χ p Φ i x‖²` as the fibre `p`-mode energy
(`tBamp_peel`), Fubini-swap the `p`- and fibre integrals (`swap_p_slot`), apply the
one-particle windowed Plancherel identity fibre by fibre (`windowPlancherel`), and peel the
Dirichlet energy back onto the box (`rhs_slot_peel`).  The box-projection is then plugged in
(`tBdiagForm_slot_gen` takes an arbitrary smooth `Φ`; `boxQ` is smooth by `boxQ_contDiff_tbdiag`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0  The `boxQ`-projection is smooth -/

/-- The insertion map `(p, z) ↦ p_{i←z}` is smooth (pair form). -/
lemma contDiff_update_pair_tbdiag {N : ℕ} (i : Fin N) : ContDiff ℝ (⊤ : ENat)
    (fun q : X N × ℝ³ => Function.update q.1 i q.2) := by
  rw [contDiff_pi]
  intro j
  by_cases h : j = i
  · subst h
    have hf : (fun q : X N × ℝ³ => Function.update q.1 j q.2 j) = (fun q => q.2) := by
      funext q; simp
    rw [hf]
    simpa using contDiff_snd (𝕜 := ℝ) (n := (⊤ : ENat)) (E := X N) (F := ℝ³)
  · have hf : (fun q : X N × ℝ³ => Function.update q.1 i q.2 j) = (fun q => q.1 j) := by
      funext q; simp [h]
    rw [hf]
    have h1 : (fun q : X N × ℝ³ => q.1 j)
        = ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (X N) ℝ³)) := by
      ext q; rfl
    rw [h1]
    exact (ContinuousLinearMap.proj (R := ℝ) j |>.comp
      (ContinuousLinearMap.fst ℝ (X N) ℝ³)).contDiff

/-- The box mean `boxP volA A i Φ` is smooth (`Φ` smooth and `A` compact). -/
lemma boxP_contDiff_tbdiag {N : ℕ} {A : Set ℝ³} (hA : IsCompact A) (volA : ℝ) (i : Fin N)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ContDiff ℝ (⊤ : ENat) (boxP volA A i Φ) := by
  have hU : ContDiff ℝ (⊤ : ENat) (fun q : X N × ℝ³ => Function.update q.1 i q.2) :=
    contDiff_update_pair_tbdiag i
  have hF : ContDiff ℝ (⊤ : ENat)
      (Function.uncurry (fun (p : X N) (z : ℝ³) => Φ (Function.update p i z))) :=
    hΦ.comp hU
  have hmain : ContDiff ℝ (⊤ : ENat)
      (fun p : X N => ∫ z in A, Φ (Function.update p i z)) :=
    Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (k := A) hA hF
  have hmain2 : ContDiff ℝ (⊤ : ENat)
      (fun p : X N => (1 / volA) * ∫ z in A, Φ (Function.update p i z)) :=
    (contDiff_const (c := (1 / volA))).mul hmain
  unfold boxP
  exact hmain2

/-- The box mean-free projection `boxQ volA A i Φ = Φ − boxP volA A i Φ` is smooth. -/
lemma boxQ_contDiff_tbdiag {N : ℕ} {A : Set ℝ³} (hA : IsCompact A) (volA : ℝ) (i : Fin N)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ContDiff ℝ (⊤ : ENat) (boxQ volA A i Φ) := by
  unfold boxQ
  exact hΦ.sub (boxP_contDiff_tbdiag hA volA i hΦ)

/-- A window supported in `acube a` vanishes off it. -/
lemma chi_tsupp_vanishes {a : ℝ} {χ : ℝ³ → ℝ} (htsupp : tsupport χ ⊆ acube a) :
    ∀ z : ℝ³, z ∉ acube a → χ z = 0 := by
  intro z hz
  by_contra h
  exact hz (htsupp (subset_tsupport χ (Function.mem_support.mpr h)))

/-! ## 1  The per-slot identity for an arbitrary smooth fibre `Φ` -/

/-- **Per-slot Plancherel identity.**  For a smooth window `χ` supported in `acube a` and an
arbitrary smooth fibre `Φ : X (n+1) → ℝ`, the `i`-th `p`-mode energy of the slot-`i` fibre is
the Dirichlet energy of the windowed fibre over the box. -/
lemma tBdiagForm_slot_gen {a : ℝ} {χ : ℝ³ → ℝ} {n : ℕ} (ha : 0 < a)
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ acube a)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : ℝ³, ‖p‖ ^ 2 *
          ((a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2)
      = ∫ x in abox (n + 1) a, ∑ k : Fin 3,
          (fderiv ℝ (fun y : X (n + 1) => χ (y i) * Φ y) x (kcDir (n + 1) i k)) ^ 2 := by
  have hχsupp : ∀ z : ℝ³, z ∉ acube a → χ z = 0 := chi_tsupp_vanishes htsupp
  -- (1) peel the slot-`i` coordinate out of the amplitude integral, pointwise in `p`
  rw [show (∫ p : ℝ³, ‖p‖ ^ 2 *
        ((a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2))
      = ∫ p : ℝ³, ‖p‖ ^ 2 * (∫ r in abox n a, ‖kinFT (fun z : ℝ³ =>
          (χ z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2) from by
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    show ‖p‖ ^ 2 * ((a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖tBamp χ p Φ i x‖ ^ 2)
        = ‖p‖ ^ 2 * (∫ r in abox n a, ‖kinFT (fun z : ℝ³ =>
            (χ z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)
    rw [tBamp_peel ha hχ.continuous hχsupp hΦ.continuous i p]]
  -- (2) Fubini: swap the `p`- and fibre-integrals
  rw [swap_p_slot ha hχ hcs htsupp hΦ i]
  -- (3) pull the `(2π)⁻³` prefactor inside the fibre integral
  rw [← MeasureTheory.integral_const_mul]
  -- (4) one-particle windowed Plancherel, fibre by fibre
  rw [show (∫ r in abox n a, ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, ‖p‖ ^ 2 *
        ‖kinFT (fun z : ℝ³ => (χ z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2))
      = ∫ r in abox n a, (∫ y in acube a, ∑ k : Fin 3,
          (fderiv ℝ (fun w : ℝ³ => χ w * Φ (kcInsN n i (w, r))) y (kcStdBasis k)) ^ 2) from by
    refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
    exact windowPlancherel (a := a) (W := χ) (ψ := fun y : ℝ³ => Φ (kcInsN n i (y, r)))
      ha hχ hcs htsupp (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r))]
  -- (5) peel the Dirichlet energy back onto the box
  rw [← rhs_slot_peel ha hχ hΦ i]

/-! ## 2  The theorem -/

theorem tBdiagForm_sq_eq_dirichlet {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ} (ha : 0 < a) (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ Submission.BoseGases.acube a) (hA : IsCompact A) {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) : Work.SmallBoxTBWord.tBdiagForm a A volA χ (fun r => r ^ 2) Ψ = ∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) a, ∑ k : Fin 3, (fderiv ℝ (fun y : Submission.BoseGases.X (n + 1) => χ (y i) * Work.SmallBoxTBWord.boxQ volA A i Ψ y) x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
  unfold tBdiagForm
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact tBdiagForm_slot_gen ha hχ hcs htsupp (boxQ_contDiff_tbdiag hA volA i hΨ) i

end Work.SmallBoxTBWord
