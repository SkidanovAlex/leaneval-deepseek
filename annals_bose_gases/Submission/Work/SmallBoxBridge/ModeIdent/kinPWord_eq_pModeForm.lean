import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.ModeIdent

open MeasureTheory
open scoped Topology BigOperators

open Submission.BoseGases

set_option maxHeartbeats 800000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Helpers

`kinPWord` and `pModeForm` differ only in how the per-`p` mode content is written: the D1 word
uses `modeP` at the real and imaginary parts of the complex mode `qMode s p`, while `pModeContent`
uses the complex slot amplitudes.  The identity is the elementary `Re² + Im² = ‖·‖²` at the level
of the complexified `boxOp`. -/

/-- Integrability of the slot amplitude integrand on the box (the complex mode times a real
shifted test function). -/
private lemma integrable_pSlot_pt (s : ℝ) (hs : 0 < s) (p : ℝ³) {N : ℕ}
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (i : Fin N) (x : X N) :
    Integrable (fun z : ℝ³ => qMode s p z * (Ψ (Function.update x i z) : ℂ))
      ((volume : Measure ℝ³).restrict (acube s)) := by
  refine ContinuousOn.integrableOn_compact (acube_compact hs) ?_
  refine ((continuous_qMode (ℓ := s) p).mul ?_).continuousOn
  exact Complex.continuous_ofReal.comp (hΨ.comp
    (((continuous_const : Continuous (fun _ : ℝ³ => x)).update i continuous_id)))

/-- The `i`-th summand of `boxOp 1 (qModeRe s p)` is the real part of the slot amplitude. -/
private lemma integral_qModeRe_slot (s : ℝ) (hs : 0 < s) (p : ℝ³) {N : ℕ}
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (i : Fin N) (x : X N) :
    ∫ z in acube s, qModeRe s p z * Ψ (Function.update x i z)
      = (pSlotAmp s p Ψ i x).re := by
  have hint := integrable_pSlot_pt s hs p hΨ i x
  have hcongr : (fun z : ℝ³ => qModeRe s p z * Ψ (Function.update x i z))
      = fun z : ℝ³ => (qMode s p z * (Ψ (Function.update x i z) : ℂ)).re := by
    funext z
    simp only [qModeRe, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hcongr]
  exact Complex.reCLM.integral_comp_comm
    (φ := fun z : ℝ³ => qMode s p z * (Ψ (Function.update x i z) : ℂ)) (φ_int := hint)

/-- The `i`-th summand of `boxOp 1 (qModeIm s p)` is the imaginary part of the slot amplitude. -/
private lemma integral_qModeIm_slot (s : ℝ) (hs : 0 < s) (p : ℝ³) {N : ℕ}
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (i : Fin N) (x : X N) :
    ∫ z in acube s, qModeIm s p z * Ψ (Function.update x i z)
      = (pSlotAmp s p Ψ i x).im := by
  have hint := integrable_pSlot_pt s hs p hΨ i x
  have hcongr : (fun z : ℝ³ => qModeIm s p z * Ψ (Function.update x i z))
      = fun z : ℝ³ => (qMode s p z * (Ψ (Function.update x i z) : ℂ)).im := by
    funext z
    simp only [qModeIm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [hcongr]
  exact Complex.imCLM.integral_comp_comm
    (φ := fun z : ℝ³ => qMode s p z * (Ψ (Function.update x i z) : ℂ)) (φ_int := hint)

/-- `boxOp 1 (qModeRe s p) Φ x` is the real part of the complexified box operator at the mode
`qMode s p`. -/
private lemma boxOp_one_qModeRe (s : ℝ) (hs : 0 < s) (p : ℝ³) {N : ℕ}
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (x : X N) :
    boxOp s (fun _ => (1 : ℝ)) (qModeRe s p) Ψ x
      = (∑ i : Fin N, pSlotAmp s p Ψ i x).re := by
  rw [show boxOp s (fun _ => (1 : ℝ)) (qModeRe s p) Ψ x
      = ∑ i : Fin N, ∫ z in acube s, qModeRe s p z * Ψ (Function.update x i z) from by
    simp only [boxOp, one_mul]]
  rw [Finset.sum_congr rfl (fun i _ => integral_qModeRe_slot s hs p hΨ i x)]
  exact (Complex.re_sum Finset.univ (fun i : Fin N => pSlotAmp s p Ψ i x)).symm

/-- `boxOp 1 (qModeIm s p) Φ x` is the imaginary part of the complexified box operator at the mode
`qMode s p`. -/
private lemma boxOp_one_qModeIm (s : ℝ) (hs : 0 < s) (p : ℝ³) {N : ℕ}
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) (x : X N) :
    boxOp s (fun _ => (1 : ℝ)) (qModeIm s p) Ψ x
      = (∑ i : Fin N, pSlotAmp s p Ψ i x).im := by
  rw [show boxOp s (fun _ => (1 : ℝ)) (qModeIm s p) Ψ x
      = ∑ i : Fin N, ∫ z in acube s, qModeIm s p z * Ψ (Function.update x i z) from by
    simp only [boxOp, one_mul]]
  rw [Finset.sum_congr rfl (fun i _ => integral_qModeIm_slot s hs p hΨ i x)]
  exact (Complex.im_sum Finset.univ (fun i : Fin N => pSlotAmp s p Ψ i x)).symm

/-- **The per-`p` mode identity**: the D1 per-mode content `P_{u_p} + P_{v_p}` equals the corpus
mode content written as the norm-square of the complexified box operator. -/
private lemma modeP_add_eq_pModeContent (s : ℝ) (hs : 0 < s) (p : ℝ³) {n : ℕ}
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) :
    modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ = pModeContent s p Φ := by
  have hRe_int : Integrable
      (fun x : X (n + 1) => (boxOp s (fun _ => (1 : ℝ)) (qModeRe s p) Φ x) ^ 2)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      (((continuous_boxOp (s := s) hs (N := n + 1) (f := fun _ => (1 : ℝ))
        (h := qModeRe s p) continuous_const (continuous_qModeRe p) (Ψ := Φ) hΦ).pow 2).continuousOn)
  have hIm_int : Integrable
      (fun x : X (n + 1) => (boxOp s (fun _ => (1 : ℝ)) (qModeIm s p) Φ x) ^ 2)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) s)) :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
      (((continuous_boxOp (s := s) hs (N := n + 1) (f := fun _ => (1 : ℝ))
        (h := qModeIm s p) continuous_const (continuous_qModeIm p) (Ψ := Φ) hΦ).pow 2).continuousOn)
  rw [modeP, modeP, pModeContent, ← mul_add, ← integral_add hRe_int hIm_int]
  have hpoint : ∀ x : X (n + 1),
      (boxOp s (fun _ => (1 : ℝ)) (qModeRe s p) Φ x) ^ 2
        + (boxOp s (fun _ => (1 : ℝ)) (qModeIm s p) Φ x) ^ 2
      = ‖∑ i : Fin (n + 1), pSlotAmp s p Φ i x‖ ^ 2 := by
    intro x
    rw [boxOp_one_qModeRe s hs p hΦ x, boxOp_one_qModeIm s hs p hΦ x]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  exact congrArg (fun t : ℝ => (s ^ 3)⁻¹ * t)
    (integral_congr_ae (Filter.Eventually.of_forall hpoint))

theorem kinPWord_eq_pModeForm {n : ℕ} {s c : ℝ} (hs : 0 < s)
    {Φ : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΦ : Continuous Φ) :
    Submission.BoseGases.kinPWord s c Φ
      = Submission.BoseGases.pModeForm s (Submission.BoseGases.fsKinCoeff c) Φ := by
  rw [kinPWord, pModeForm, inv_pow]
  congr 1
  have hpoint : ∀ p : ℝ³,
      fsKinCoeff c ‖p‖ * (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)
        = fsKinCoeff c ‖p‖ * pModeContent s p Φ := by
    intro p
    rw [modeP_add_eq_pModeContent s hs p hΦ]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

end Work.SmallBoxBridge.ModeIdent
