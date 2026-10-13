import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdzSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## Integrability and bounds of the slots -/

/-- The bound and integrability of a slot with `(i,j) ≠ (0,0)`: the pointwise domination by the
level-six integrand integrates to `K·HkSq α 6 f`. -/
theorem rowA_slot_bound {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b i j : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (hm6 : Work.Spaces.HkMem α 6 f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) (hia : i ≤ a) (hjb : j ≤ b) (hij : 1 ≤ i + j) :
    MeasureTheory.Integrable (rowA_piece f A ρ a b i j) pqm ∧
      |∫ p, rowA_piece f A ρ a b i j p ∂pqm| ≤ K * Work.Spaces.HkSq α 6 f := by
  obtain ⟨hHkInt, hHkEq⟩ := rowA_HkIntegrand_prodIntegrable (k := 6) hso hm6
  have hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.continuousOn_leaf_Q0 hρ
  have hdom : ∀ᵐ p ∂pqm,
      |rowA_piece f A ρ a b i j p| ≤ K * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
    Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
      (fun θ hθ z hz => rowA_slot_dom hα hα1 hK hρ hAbd hab hia hjb hij hz hθ)
  have hInt : MeasureTheory.Integrable (rowA_piece f A ρ a b i j) pqm :=
    (hHkInt.const_mul K).mono'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (rowA_piece_continuousOn hso hAso hρc))
      (by simpa only [Real.norm_eq_abs] using hdom)
  refine ⟨hInt, ?_⟩
  calc |∫ p, rowA_piece f A ρ a b i j p ∂pqm|
      ≤ ∫ p, |rowA_piece f A ρ a b i j p| ∂pqm := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ p, K * Work.Spaces.HkIntegrand α 6 f p.1 p.2 ∂pqm :=
        MeasureTheory.integral_mono_ae hInt.abs (hHkInt.const_mul K) hdom
    _ = K * ∫ p, Work.Spaces.HkIntegrand α 6 f p.1 p.2 ∂pqm :=
        MeasureTheory.integral_const_mul K _
    _ = K * Work.Spaces.HkSq α 6 f := by rw [hHkEq]

/-- The bound and integrability of the leading `(0,0)`-slot: the exact radial self-pairing
(`dzSelfA2d`) gives `5K·HkSq α 6 f` without ever using the level-seven norm. -/
theorem rowA_slot00 {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {f A : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ)))
    (hab : a + b ≤ 6) :
    MeasureTheory.Integrable (rowA_piece f A ρ a b 0 0) pqm ∧
      |∫ p, rowA_piece f A ρ a b 0 0 p ∂pqm| ≤ 5 * K * Work.Spaces.HkSq α 6 f := by
  have hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.continuousOn_leaf_Q0 hρ
  have hInt : MeasureTheory.Integrable (rowA_piece f A ρ a b 0 0) pqm := by
    obtain ⟨hHk7Int, -⟩ := rowA_HkIntegrand_prodIntegrable (k := 7) hso hm7
    refine (hHk7Int.const_mul K).mono'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (rowA_piece_continuousOn hso hAso hρc)) ?_
    filter_upwards [Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
      (fun θ hθ z hz => rowA_slot_dom_00 hα hK hρ hAbd hab hz hθ)] with p hp
    simpa only [Real.norm_eq_abs] using hp
  refine ⟨hInt, ?_⟩
  obtain ⟨σ, hσeq, hσpos, hσm, hσle⟩ := rowA_leaf_decomp hα hα1 hρ
  have hAb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K := by
    intro z θ hz h1 h2
    have h := hAbd z θ hz h1 h2 0 0 (by norm_num)
    simpa using h
  obtain ⟨hVae, hFρ, hD2ρ, hcrossρ⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.leadPiece α hα hα1 hso hAso hm6 hm7 hK hρ hab hAb
  have hF : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) pqm :=
    hFρ.congr (Filter.Eventually.of_forall fun p => by
      show ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
        = (Work.Spaces.w p.1) ^ 2 * σ p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
      rw [hσeq p.1 p.2])
  have hD2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
      * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2) pqm :=
    hD2ρ.congr (Filter.Eventually.of_forall fun p => by
      show ρ p.1 p.2 * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2
        = (Work.Spaces.w p.1) ^ 2 * σ p.2
          * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2
      rw [hσeq p.1 p.2])
  have hcross : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
      * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
        * Work.Spaces.mixed b a f p.1 p.2))) pqm :=
    hcrossρ.congr (Filter.Eventually.of_forall fun p => by
      show ρ p.1 p.2 * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
          * Work.Spaces.mixed b a f p.1 p.2))
        = (Work.Spaces.w p.1) ^ 2 * σ p.2
          * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
            * Work.Spaces.mixed b a f p.1 p.2))
      rw [hσeq p.1 p.2])
  have hdz := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.dzSelfA2d (σ := σ) (A := A)
    (V := Work.Spaces.mixed b a f) (K := K) hK hσm hσpos
    (fun θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.SmoothOpen.slice hAso hθ 1)
    hAb
    (fun z θ hz h1 h2 => by
      have h := hAbd z θ hz h1 h2 1 0 (by norm_num)
      have hrz : Work.Spaces.mixed 1 0 A z θ = z * deriv (fun z' => A z' θ) z := rfl
      rw [hrz] at h
      simpa using h)
    (fun θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.SmoothOpen.slice (hso.mixed b a) hθ 1)
    hVae hF hD2 hcross
  have hS : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * σ θ * (Work.Spaces.mixed b a f z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 6 f := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).1 b (by omega) σ
        (fun θ hθ => le_of_lt (hσpos θ hθ)) (fun θ hθ => by simpa using hσle θ hθ)
      simpa using h
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).2 b a ha1 (by omega) σ
        (fun θ hθ => le_of_lt (hσpos θ hθ)) (fun θ hθ => by simpa [if_neg ha0] using hσle θ hθ)
      simpa using h
  have hcongr : (∫ p, rowA_piece f A ρ a b 0 0 p ∂pqm)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ
            * (A z θ * ((z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
              * Work.Spaces.mixed b a f z θ)) := by
    rw [MeasureTheory.integral_prod _ hInt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [rowA_piece, Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero, Nat.sub_zero]
    rw [hσeq z θ]
    rw [show Work.Spaces.mixed (b + 1) a f z θ
        = z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ from rfl]
    ring
  calc |∫ p, rowA_piece f A ρ a b 0 0 p ∂pqm|
      = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * σ θ
          * (A z θ * ((z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
            * Work.Spaces.mixed b a f z θ))| := by rw [hcongr]
    _ ≤ 5 * K * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ * (Work.Spaces.mixed b a f z θ) ^ 2) := hdz
    _ ≤ 5 * K * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_left hS (by linarith)

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
