import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
import Submission.Work.SmallBoxD1KinDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Cauchy–Schwarz step of the kinetic bridge: `pModeForm ≤ (N+1)·pDiagForm`

The mode content `pModeContent s p Ψ` is the norm-square of the sum of the `N` slot
amplitudes `Σ_i pSlotAmp s p Ψ i x`; Cauchy–Schwarz bounds it by `(N+1)` times the
sum of the squared norms, i.e. the *diagonal* content `pModeDiagonal`.  Integrating
over `p`, the exchange of the finite slot sum with the `p`-integral requires the
individual slot integrands to be measurable; measurability comes from the continuity
of `p ↦ ∫_x ‖pSlotAmp s p Ψ i x‖²`, which `continuous_parametric_integral_of_continuous`
supplies from the joint continuity of the slot amplitude.
-/

namespace Work.SmallBoxBridge.Cauchy

open MeasureTheory Metric
open scoped Topology Real BigOperators
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Joint continuity of the slot amplitude** `(p,x) ↦ pSlotAmp s p Ψ i x`
(for continuous `Ψ`). -/
theorem continuous_pSlotAmp_pair {N : ℕ} {s : ℝ} (hs : 0 < s) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) (i : Fin N) :
    Continuous (fun q : ℝ³ × X N => pSlotAmp s q.1 Ψ i q.2) := by
  rw [show (fun q : ℝ³ × X N => pSlotAmp s q.1 Ψ i q.2)
      = fun q => ∫ z in acube s, qMode s q.1 z * (Ψ (Function.update q.2 i z) : ℂ) from by
    funext q; simp only [pSlotAmp]]
  refine continuous_parametric_integral_of_continuous
    (f := fun (q : ℝ³ × X N) (z : ℝ³) =>
      qMode s q.1 z * (Ψ (Function.update q.2 i z) : ℂ)) ?_ (acube_compact hs)
  rw [show Function.uncurry (fun (q : ℝ³ × X N) (z : ℝ³) =>
        qMode s q.1 z * (Ψ (Function.update q.2 i z) : ℂ))
      = fun r : (ℝ³ × X N) × ℝ³ =>
          qMode s r.1.1 r.2 * (Ψ (Function.update r.1.2 i r.2) : ℂ) from rfl]
  have h1 : Continuous fun r : (ℝ³ × X N) × ℝ³ => (r.1.1, r.2) :=
    continuous_fst.fst.prodMk continuous_snd
  have h2 : Continuous fun r : (ℝ³ × X N) × ℝ³ => r.1.2 := continuous_fst.snd
  exact ((continuous_qMode_pair (ℓ := s) hs).comp h1).mul
    (Complex.continuous_ofReal.comp (hΨ.comp (h2.update i continuous_snd)))

/-- **Continuity in `p` of the `i`-th slot mode form** `p ↦ ∫_x ‖pSlotAmp s p Ψ i x‖²`. -/
theorem continuous_integral_pSlotAmp_sq {N : ℕ} {s : ℝ} (hs : 0 < s) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) (i : Fin N) :
    Continuous (fun p : ℝ³ => ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2) := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (p : ℝ³) (x : X N) => ‖pSlotAmp s p Ψ i x‖ ^ 2) ?_ (abox_compact N hs)
  rw [show Function.uncurry (fun (p : ℝ³) (x : X N) => ‖pSlotAmp s p Ψ i x‖ ^ 2)
      = fun r : ℝ³ × X N => ‖pSlotAmp s r.1 Ψ i r.2‖ ^ 2 from rfl]
  exact (continuous_norm.comp (continuous_pSlotAmp_pair hs hΨ i)).pow 2

/-- **Cauchy–Schwarz on the slot sum**: the mode content is dominated by `(N+1)` times the
diagonal (one-body) content, pointwise in `p`. -/
theorem pModeContent_le_pModeDiagonal {N : ℕ} {s : ℝ} (hs : 0 < s) (p : ℝ³) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) :
    pModeContent s p Ψ ≤ ((N : ℝ) + 1) * pModeDiagonal s p Ψ := by
  have hcont : ∀ i : Fin N, Continuous (fun x : X N => ‖pSlotAmp s p Ψ i x‖ ^ 2) := fun i =>
    (continuous_norm.comp ((continuous_pSlotAmp_pair hs hΨ i).comp
      (continuous_const.prodMk continuous_id))).pow 2
  have hBint : ∀ i : Fin N, Integrable (fun x : X N => ‖pSlotAmp s p Ψ i x‖ ^ 2)
      ((volume : Measure (X N)).restrict (abox N s)) := fun i =>
    ContinuousOn.integrableOn_compact (abox_compact N hs) (hcont i).continuousOn
  have hpt : ∀ x : X N, ‖∑ i : Fin N, pSlotAmp s p Ψ i x‖ ^ 2
      ≤ ((N : ℝ) + 1) * ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ ^ 2 := by
    intro x
    have h1 : ‖∑ i : Fin N, pSlotAmp s p Ψ i x‖ ≤ ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ :=
      norm_sum_le _ _
    have h2 : (∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖) ^ 2
        ≤ (N : ℝ) * ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin N => ‖pSlotAmp s p Ψ i x‖)
    have h3 : ‖∑ i : Fin N, pSlotAmp s p Ψ i x‖ ^ 2
        ≤ (∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h4 : (N : ℝ) * ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ ^ 2
        ≤ ((N : ℝ) + 1) * ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ ^ 2 := by
      have h5 : 0 ≤ ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      nlinarith
    linarith
  have hmain : ∫ x in abox N s, ‖∑ i : Fin N, pSlotAmp s p Ψ i x‖ ^ 2
      ≤ ((N : ℝ) + 1) * ∑ i : Fin N, ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2 := by
    have hgint : Integrable (fun x : X N => ((N : ℝ) + 1) *
        ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ ^ 2) ((volume : Measure (X N)).restrict (abox N s)) :=
      (integrable_finsetSum _ (fun i _ => hBint i)).const_mul _
    have h1 := integral_mono_of_nonneg
      (f := fun x : X N => ‖∑ i : Fin N, pSlotAmp s p Ψ i x‖ ^ 2)
      (g := fun x : X N => ((N : ℝ) + 1) * ∑ i : Fin N, ‖pSlotAmp s p Ψ i x‖ ^ 2)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hgint (Filter.Eventually.of_forall hpt)
    rwa [MeasureTheory.integral_const_mul,
        integral_finsetSum _ (fun i _ => hBint i)] at h1
  rw [pModeContent, pModeDiagonal]
  have hs3 : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
  calc (s ^ 3)⁻¹ * ∫ x in abox N s, ‖∑ i : Fin N, pSlotAmp s p Ψ i x‖ ^ 2
      ≤ (s ^ 3)⁻¹ * (((N : ℝ) + 1) * ∑ i : Fin N, ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmain hs3
    _ = ((N : ℝ) + 1) * ((s ^ 3)⁻¹ * ∑ i : Fin N, ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2) := by
        ring

/-- **The `(n+1)` Cauchy–Schwarz bookkeeping of the kinetic bridge.**  The corpus mode form
`pModeForm s F Ψ = (2π)⁻³∫_p F(‖p‖)·pModeContent s p Ψ` is dominated by `(N+1)` times the
diagonal (one-body) mode form `pDiagForm s F Ψ`. -/
theorem pModeForm_le_pDiagForm {N : ℕ} {s : ℝ} (hs : 0 < s) {F : ℝ → ℝ}
    (hF : ∀ r, 0 ≤ F r) {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΨ : Continuous Ψ)
    (hint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖ * (∑ i : Fin N,
      (s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N s,
        ‖Submission.BoseGases.pSlotAmp s p Ψ i x‖ ^ 2))) :
    Submission.BoseGases.pModeForm s F Ψ ≤ ((N : ℝ) + 1) * Submission.BoseGases.pDiagForm s F Ψ := by
  let c : Fin N → ℝ³ → ℝ := fun i p => (s^3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖^2
  have hDc : ∀ p, pModeDiagonal s p Ψ = ∑ i : Fin N, c i p := by
    intro p
    simp only [pModeDiagonal, c, Finset.mul_sum]
  have hc_nonneg : ∀ i p, 0 ≤ c i p := by
    intro i p
    simp only [c]
    exact mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))
  have hpc_nonneg : ∀ p, 0 ≤ pModeContent s p Ψ := by
    intro p; simp only [pModeContent]
    exact mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))
  have hci_meas : ∀ i : Fin N, AEMeasurable (c i) := by
    intro i
    have h : AEMeasurable (fun p : ℝ³ => (s^3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖^2) :=
      ((continuous_integral_pSlotAmp_sq hs hΨ i).const_mul ((s^3)⁻¹)).aestronglyMeasurable.aemeasurable
    simpa only [c] using h
  have hD_meas : AEMeasurable (fun p : ℝ³ => pModeDiagonal s p Ψ) := by
    have h0 : AEMeasurable (∑ i : Fin N, c i) volume :=
      Finset.aemeasurable_sum _ (fun i _ => hci_meas i)
    have h : AEMeasurable (fun p : ℝ³ => ∑ i : Fin N, c i p) volume :=
      h0.congr (Filter.Eventually.of_forall fun p => (Finset.sum_apply p Finset.univ c))
    exact h.congr (Filter.Eventually.of_forall fun p => (hDc p).symm)
  have hΦ_int : Integrable (fun p : ℝ³ => F ‖p‖ * pModeDiagonal s p Ψ) := by
    have hfun : (fun p : ℝ³ => F ‖p‖ * pModeDiagonal s p Ψ)
        = fun p => F ‖p‖ * (∑ i : Fin N,
            (s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Ψ i x‖ ^ 2) := by
      funext p; rw [hDc p]
    rw [hfun]; exact hint
  have hg_int : ∀ i : Fin N, Integrable (fun p : ℝ³ => F ‖p‖ * c i p) := by
    intro i
    have hbound : ∀ᵐ p ∂(volume : Measure ℝ³), ‖F ‖p‖ * c i p‖ ≤ F ‖p‖ * pModeDiagonal s p Ψ :=
      Filter.Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (hF _) (hc_nonneg i p))]
        exact mul_le_mul_of_nonneg_left
          (by rw [hDc p]
              exact Finset.single_le_sum (fun j _ => hc_nonneg j p) (Finset.mem_univ i)) (hF _)
    apply Integrable.mono' hΦ_int _ hbound
    have hEq : (fun p : ℝ³ => F ‖p‖ * c i p)
        = fun p => F ‖p‖ * pModeDiagonal s p Ψ * (pModeDiagonal s p Ψ)⁻¹ * c i p := by
      funext p
      by_cases h : pModeDiagonal s p Ψ = 0
      · have hc0 : c i p = 0 := by
          have hsum : ∑ j : Fin N, c j p = 0 := by rw [← hDc p, h]
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc_nonneg j p)).mp hsum i
            (Finset.mem_univ i)
        rw [h, hc0]; ring
      · have hD0 : pModeDiagonal s p Ψ * (pModeDiagonal s p Ψ)⁻¹ = 1 := mul_inv_cancel₀ h
        rw [show F ‖p‖ * pModeDiagonal s p Ψ * (pModeDiagonal s p Ψ)⁻¹ * c i p
            = F ‖p‖ * (pModeDiagonal s p Ψ * (pModeDiagonal s p Ψ)⁻¹) * c i p by ring, hD0]
        ring
    rw [hEq]
    exact ((hΦ_int.aestronglyMeasurable.aemeasurable.mul hD_meas.inv).mul
      (hci_meas i)).aestronglyMeasurable
  have hsum : ∫ p, F ‖p‖ * pModeDiagonal s p Ψ = ∑ i : Fin N, ∫ p, F ‖p‖ * c i p := by
    rw [show (fun p : ℝ³ => F ‖p‖ * pModeDiagonal s p Ψ)
        = fun p => ∑ i : Fin N, F ‖p‖ * c i p from by
      funext p; rw [hDc p, Finset.mul_sum]]
    exact integral_finsetSum _ (fun i _ => hg_int i)
  have hI : ∫ p, F ‖p‖ * pModeContent s p Ψ
      ≤ ((N : ℝ) + 1) * ∫ p, F ‖p‖ * pModeDiagonal s p Ψ := by
    have hgi : Integrable (fun p : ℝ³ => ((N : ℝ) + 1) * (F ‖p‖ * pModeDiagonal s p Ψ)) :=
      hΦ_int.const_mul _
    have hmono := integral_mono_of_nonneg
      (f := fun p : ℝ³ => F ‖p‖ * pModeContent s p Ψ)
      (g := fun p : ℝ³ => ((N : ℝ) + 1) * (F ‖p‖ * pModeDiagonal s p Ψ))
      (Filter.Eventually.of_forall fun p => mul_nonneg (hF _) (hpc_nonneg p)) hgi
      (Filter.Eventually.of_forall fun p => by
        have hcs := pModeContent_le_pModeDiagonal hs p hΨ
        have hFn : 0 ≤ F ‖p‖ := hF _
        nlinarith [hcs, hFn])
    rwa [MeasureTheory.integral_const_mul] at hmono
  unfold pModeForm pDiagForm
  have hA : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  calc ((2 * π) ^ 3)⁻¹ * ∫ p, F ‖p‖ * pModeContent s p Ψ
      ≤ ((2 * π) ^ 3)⁻¹ * (((N : ℝ) + 1) * ∫ p, F ‖p‖ * pModeDiagonal s p Ψ) :=
        mul_le_mul_of_nonneg_left hI hA
    _ = ((2 * π) ^ 3)⁻¹ * (((N : ℝ) + 1) * ∑ i : Fin N, ∫ p, F ‖p‖ * c i p) := by rw [hsum]
    _ = ((N : ℝ) + 1) * ∑ i : Fin N, ((2 * π) ^ 3)⁻¹ * (∫ p, F ‖p‖ * c i p) := by
        have h2 : ∑ i : Fin N, ((2 * π) ^ 3)⁻¹ * (∫ p, F ‖p‖ * c i p)
            = ((2 * π) ^ 3)⁻¹ * ∑ i : Fin N, (∫ p, F ‖p‖ * c i p) := by
          rw [Finset.mul_sum]
        rw [h2]; ring

end Work.SmallBoxBridge.Cauchy
