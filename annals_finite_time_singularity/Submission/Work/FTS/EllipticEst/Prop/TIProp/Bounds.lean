import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Helpers
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamLeftW
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamRightW
import Submission.Work.EllipticEst.Core.i0Aux.setIntegral_Ioo_split3
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypAux
import Submission.Work.FTS.EllipticEst.Prop.TIProp.Helpers
import Submission.Work.FTS.EllipticEst.Prop.TIProp.SurrEnergy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted bounds for the surrogate decomposition

For `f` with finite weighted energies `P = ∫ f²σ` and `E = ∫ (f'')²σ`, whose endpoint traces are
`F₀`, `F₁`, and a surrogate `ℓ = surrFun ψ F₀ F₁ L` at a scale `L` with `L⁴ = P/(16(P+E))`, this
module records:

* the weighted `L²` mass of the difference `f - ℓ` (at most `10^6 P`);
* the weighted `L²` mass of the second derivative of `f - ℓ` (at most `10^8 (Cb+1)² (P+E)`);
* the weighted `L²` mass of the first derivative of `ℓ`;
* the integrability of `(f-ℓ)²σ`, `((f-ℓ)')²σ` and `((f-ℓ)'')²σ`.
-/

namespace Work.FTS.EllipticEst.Prop.TIProp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "σ" => Work.FTS.EllipticEst.thEta

theorem bounds {ψ : ℝ → ℝ} {Cb F₀ F₁ P E L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ Cb)
    (hLpos : 0 < L) (hLp : L ≤ Real.pi / 4) (hPpos : 0 < P) (hEnn : 0 ≤ E)
    (hL4 : L ^ 4 = P / (16 * (P + E)))
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hF0tr : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀))
    (hF1tr : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁))
    (hPint : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hAint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ)
    (hPdef : P = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
    (hEdef : E = ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * σ θ) :
    ((∫ θ in Work.Spaces.Iθ,
        (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2
          * σ θ) ≤ 10 ^ 6 * P)
    ∧ ((∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2
          * σ θ) ≤ (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E))
    ∧ ((∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          ≤ 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)))
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2
          * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2
          * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          Work.Spaces.Iθ) := by
  have hLnn : (0 : ℝ) ≤ L := hLpos.le
  have hLlt : L < Real.pi / 2 := by linarith [hLp, Real.pi_pos]
  have hPnn : 0 ≤ P := hPpos.le
  have hsubPO : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hIooP : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * σ θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hPint.mono_set hsubPO
  have hIooE : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * σ θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hEint.mono_set hsubPO
  have hPbound : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 * σ θ) ≤ P := by
    rw [hPdef]
    refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · filter_upwards with θ hθ; exact hsubPO hθ
  have hEbound : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv f) θ) ^ 2 * σ θ) ≤ E := by
    rw [hEdef]
    refine MeasureTheory.setIntegral_mono_set hEint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · filter_upwards with θ hθ; exact hsubPO hθ
  have hF0b : F₀ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P := by
    have h := Work.EllipticEst.Core.i0Aux.TVRed.endpointParamLeftW f F₀ L hLpos hLlt hf hF0tr
      hIooE hIooP
    have h1 : 0 ≤ L ^ (3 + Work.Spaces.eta) := Real.rpow_nonneg hLnn _
    have h2 : 0 ≤ L ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg hLnn _
    have h3 := mul_le_mul_of_nonneg_left hEbound h1
    have h4 := mul_le_mul_of_nonneg_left hPbound h2
    linarith
  have hF1b : F₁ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P := by
    have h := Work.EllipticEst.Core.i0Aux.TVRed.endpointParamRightW f F₁ L hLpos hLlt hf hF1tr
      hIooE hIooP
    have h1 : 0 ≤ L ^ (3 + Work.Spaces.eta) := Real.rpow_nonneg hLnn _
    have h2 : 0 ≤ L ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg hLnn _
    have h3 := mul_le_mul_of_nonneg_left hEbound h1
    have h4 := mul_le_mul_of_nonneg_left hPbound h2
    linarith
  have hF0sc : F₀ ^ 2 * L ^ (1 - Work.Spaces.eta) ≤ 200 * P :=
    endpoint_scale hLpos hPpos hPnn hEnn hL4 hF0b
  have hF1sc : F₁ ^ 2 * L ^ (1 - Work.Spaces.eta) ≤ 200 * P :=
    endpoint_scale hLpos hPpos hPnn hEnn hL4 hF1b
  -- ## the surrogate and its weighted energies
  let ℓ : ℝ → ℝ := Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L
  let g : ℝ → ℝ := fun θ : ℝ => f θ - ℓ θ
  obtain ⟨hAℓ, hEℓ, hintℓ0, hintℓ1, hintℓ2⟩ :=
    Work.FTS.EllipticEst.Prop.TIProp.surr_energy hψ hLpos hLp hPpos hEnn hL4 hF0b hF1b
  -- ## the weighted mass of `f - ℓ`
  have hL2pos : (0 : ℝ) < L / 2 := by linarith
  have hcmp : L / 2 < Real.pi / 2 - L / 2 := by linarith [hLp, Real.pi_pos]
  have hcmp2 : Real.pi / 2 - L / 2 < Real.pi / 2 := by linarith
  have hsubL : Set.Ioo (0 : ℝ) (L / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt (by linarith [hθ.2, hLp, Real.pi_pos])⟩
  have hsubR : Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt (by linarith [hθ.1, hLp, Real.pi_pos]), le_of_lt hθ.2⟩
  have hmid0 : ∀ θ ∈ Set.Ioo (L / 2) (Real.pi / 2 - L / 2), ℓ θ = 0 := by
    intro θ hθ
    have h1 : ψ (θ / L) = 0 :=
      hψ.eq_zero _ (by rw [le_div_iff₀ hLpos]; linarith [hθ.1])
    have h2 : ψ ((Real.pi / 2 - θ) / L) = 0 :=
      hψ.eq_zero _ (by rw [le_div_iff₀ hLpos]; linarith [hθ.2])
    show Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ = 0
    simp only [Work.EllipticEst.Core.i0Aux.surrFun, h1, h2, mul_zero, add_zero]
  have hsurrb : ∀ θ : ℝ, (ℓ θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ θ
    calc (ℓ θ) ^ 2 = |ℓ θ| ^ 2 := (sq_abs _).symm
      _ ≤ (|F₀| + |F₁|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  -- the left piece
  have hleft : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (g θ) ^ 2 * σ θ) ≤ 400000 * P := by
    have h1 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (g θ) ^ 2 * σ θ)
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (L / 2),
            2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩)
      · exact ((hPint.mono_set hsubL).const_mul 2).add ((hintℓ0.mono_set hsubL).const_mul 2)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        have hσ : 0 ≤ σ θ :=
          thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩
        have h2 : (g θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2 := by
          show (f θ - ℓ θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2
          nlinarith [sq_nonneg (f θ + ℓ θ)]
        calc (g θ) ^ 2 * σ θ ≤ (2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2) * σ θ :=
              mul_le_mul_of_nonneg_right h2 hσ
          _ = 2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by ring
    have h2 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2),
          2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ))
        ≤ 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta))) := by
      rw [MeasureTheory.integral_add ((hPint.mono_set hsubL).const_mul 2)
          ((hintℓ0.mono_set hsubL).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have h3 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (f θ) ^ 2 * σ θ) ≤ P := by
        rw [hPdef]
        refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
        · filter_upwards with θ hθ; exact hsubL hθ
      have h4 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (ℓ θ) ^ 2 * σ θ)
          ≤ (|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)) := by
        have h5 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (ℓ θ) ^ 2 * σ θ)
            ≤ ∫ θ in Set.Ioo (0 : ℝ) (L / 2), ((|F₀| + |F₁|) ^ 2) * σ θ := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_nonneg (sq_nonneg _)
              (thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩)
          · exact ((Work.FTS.EllipticEst.integrableOn_thEta.1).mono_set hsubL).const_mul _
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_le_mul_of_nonneg_right (hsurrb θ)
              (thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩)
        rw [MeasureTheory.integral_const_mul] at h5
        exact h5.trans
          (mul_le_mul_of_nonneg_left (thEta_tail_left_Ioo hLpos hLp) (by positivity))
      linarith [h3, h4]
    have h6 : 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
        ≤ 400000 * P := by
      have h7 : (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
          ≤ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by
        have h7a : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
          nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
        calc (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
            ≤ (2 * (F₀ ^ 2 + F₁ ^ 2)) * L ^ (1 - Work.Spaces.eta) :=
              mul_le_mul_of_nonneg_right h7a (Real.rpow_nonneg hLnn _)
          _ = 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by ring
      have h8 : 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) ≤ 800 * P := by
        have h8a : (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) ≤ 400 * P := by
          linarith [hF0sc, hF1sc]
        linarith
      calc 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
          = 2 * P + 400 * ((|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)) := by ring
        _ ≤ 2 * P + 400 * (800 * P) := by linarith [h7, h8]
        _ ≤ 400000 * P := by linarith [hPnn]
    linarith [h1, h2, h6]
  -- the middle piece
  have hmid : (∫ θ in Set.Ioo (L / 2) (Real.pi / 2 - L / 2), (g θ) ^ 2 * σ θ) ≤ P := by
    have h1 : (∫ θ in Set.Ioo (L / 2) (Real.pi / 2 - L / 2), (g θ) ^ 2 * σ θ)
        = ∫ θ in Set.Ioo (L / 2) (Real.pi / 2 - L / 2), (f θ) ^ 2 * σ θ := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
        (Filter.Eventually.of_forall ?_)
      intro θ hθ
      show (f θ - ℓ θ) ^ 2 * σ θ = (f θ) ^ 2 * σ θ
      rw [hmid0 θ hθ]; ring
    rw [h1, hPdef]
    refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · filter_upwards with θ hθ
      exact ⟨le_of_lt (by linarith [hθ.1, hL2pos]), le_of_lt (by linarith [hθ.2, hcmp2])⟩
  -- the right piece
  have hright : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (g θ) ^ 2 * σ θ)
      ≤ 400000 * P := by
    have h1 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (g θ) ^ 2 * σ θ)
        ≤ ∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
            2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩)
      · exact ((hPint.mono_set hsubR).const_mul 2).add ((hintℓ0.mono_set hsubR).const_mul 2)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        have hσ : 0 ≤ σ θ :=
          thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩
        have h2 : (g θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2 := by
          show (f θ - ℓ θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2
          nlinarith [sq_nonneg (f θ + ℓ θ)]
        calc (g θ) ^ 2 * σ θ ≤ (2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2) * σ θ :=
              mul_le_mul_of_nonneg_right h2 hσ
          _ = 2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by ring
    have h2 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
          2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ))
        ≤ 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta))) := by
      rw [MeasureTheory.integral_add ((hPint.mono_set hsubR).const_mul 2)
          ((hintℓ0.mono_set hsubR).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have h3 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
          (f θ) ^ 2 * σ θ) ≤ P := by
        rw [hPdef]
        refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
        · filter_upwards with θ hθ; exact hsubR hθ
      have h4 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (ℓ θ) ^ 2 * σ θ)
          ≤ (|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)) := by
        have h5 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (ℓ θ) ^ 2 * σ θ)
            ≤ ∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
                ((|F₀| + |F₁|) ^ 2) * σ θ := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_nonneg (sq_nonneg _)
              (thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩)
          · exact ((Work.FTS.EllipticEst.integrableOn_thEta.1).mono_set hsubR).const_mul _
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_le_mul_of_nonneg_right (hsurrb θ)
              (thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩)
        rw [MeasureTheory.integral_const_mul] at h5
        exact h5.trans
          (mul_le_mul_of_nonneg_left (thEta_tail_right_Ioo hLpos hLp) (by positivity))
      linarith [h3, h4]
    have h6 : 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
        ≤ 400000 * P := by
      have h7 : (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
          ≤ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by
        have h7a : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
          nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
        calc (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
            ≤ (2 * (F₀ ^ 2 + F₁ ^ 2)) * L ^ (1 - Work.Spaces.eta) :=
              mul_le_mul_of_nonneg_right h7a (Real.rpow_nonneg hLnn _)
          _ = 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by ring
      have h8 : 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) ≤ 800 * P := by
        have h8a : (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) ≤ 400 * P := by
          linarith [hF0sc, hF1sc]
        linarith
      calc 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
          = 2 * P + 400 * ((|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)) := by ring
        _ ≤ 2 * P + 400 * (800 * P) := by linarith [h7, h8]
        _ ≤ 400000 * P := by linarith [hPnn]
    linarith [h1, h2, h6]
  -- ## the total mass and the integrability of `(f - ℓ)²σ`
  have hgIθ : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * σ θ) Work.Spaces.Iθ :=
    Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_sq_sub hPint hintℓ0
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn hf.continuousOn)
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        ((Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hLpos)).continuous.continuousOn))
  have hIfg : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * σ θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hgIθ.mono_set hsubPO
  have hsplit3 := Work.EllipticEst.Core.i0Aux.setIntegral_Ioo_split3
    (f := fun θ : ℝ => (g θ) ^ 2 * σ θ) (a := (0 : ℝ)) (b := L / 2)
    (c := Real.pi / 2 - L / 2) (d := Real.pi / 2) hL2pos hcmp hcmp2 hIfg
  have hIθIoo : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σ θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g θ) ^ 2 * σ θ := by
    rw [Measure.restrict_congr_set (Work.EllipticEst.Core.i0Aux.tvc_ae_eq_Iθ_Ioo)]
  have hPg : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σ θ) ≤ 10 ^ 6 * P := by
    rw [hIθIoo, hsplit3]
    linarith [hleft, hmid, hright]
  -- ## the integrability of `((f - ℓ)'')²σ` and the bound for `((f-ℓ)'')²σ`
  have hg_int2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have hae : (fun θ : ℝ => (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * σ θ) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Work.EllipticEst.Core.i0Aux.TVRed.tvh_deriv2_sub hf
        (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hLpos)) θ hθ]
    refine (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_sq_sub hEint hintℓ2
      ?_ ?_).congr hae
    · have h0 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (contDiffOn_zero.1 (h0.deriv_of_isOpen isOpen_Ioo (by norm_num)))
    · have h1 : ContDiff ℝ 1 (deriv ℓ) := by
        simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hLpos)).deriv' (n := 1)
      exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (contDiffOn_zero.1 ((h1.contDiffOn).deriv_of_isOpen isOpen_Ioo (by norm_num)))
  have hEg : (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * σ θ)
      ≤ (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E) := by
    have hae : (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * σ θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Work.EllipticEst.Core.i0Aux.TVRed.tvh_deriv2_sub hf
        (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hLpos)) θ hθ]
    rw [MeasureTheory.integral_congr_ae hae]
    have h2 : (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            2 * ((deriv (deriv f) θ) ^ 2 * σ θ) + 2 * ((deriv (deriv ℓ) θ) ^ 2 * σ θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · exact (hEint.const_mul 2).add (hintℓ2.const_mul 2)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        have h3 : (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2
            ≤ 2 * (deriv (deriv f) θ) ^ 2 + 2 * (deriv (deriv ℓ) θ) ^ 2 := by
          nlinarith [sq_nonneg (deriv (deriv f) θ + deriv (deriv ℓ) θ)]
        calc (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ
            ≤ (2 * (deriv (deriv f) θ) ^ 2 + 2 * (deriv (deriv ℓ) θ) ^ 2) * σ θ :=
              mul_le_mul_of_nonneg_right h3 hσ
          _ = 2 * ((deriv (deriv f) θ) ^ 2 * σ θ)
              + 2 * ((deriv (deriv ℓ) θ) ^ 2 * σ θ) := by ring
    rw [MeasureTheory.integral_add (hEint.const_mul 2) (hintℓ2.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h2
    rw [← hEdef] at h2
    have h5 : 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv ℓ) θ) ^ 2 * σ θ)
        ≤ 2 * (10 ^ 8 * (Cb + 1) ^ 2 * (P + E)) :=
      mul_le_mul_of_nonneg_left hEℓ (by norm_num)
    have h6 : 2 * E + 2 * (10 ^ 8 * (Cb + 1) ^ 2 * (P + E))
        ≤ (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E) := by
      have h7 : 2 * E ≤ 2 * (P + E) := by linarith [hEnn, hPpos.le]
      linarith [h7]
    linarith [h2, h5, h6]
  -- ## the integrability of `((f - ℓ)')²σ`
  have hg_int1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have hae : (fun θ : ℝ => (deriv f θ - deriv ℓ θ) ^ 2 * σ θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Work.EllipticEst.Core.i0Aux.TVRed.tvh_deriv_sub hf
        (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hLpos)) θ hθ]
    refine (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_sq_sub hAint hintℓ1
      ?_ ?_).congr hae
    · exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num))
    · have h1 : ContDiff ℝ 1 (deriv ℓ) := by
        simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hLpos)).deriv' (n := 1)
      exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (h1.continuous.continuousOn)
  exact ⟨hPg, hEg, hAℓ, hgIθ, hg_int1, hg_int2, hintℓ0, hintℓ1⟩

end Work.FTS.EllipticEst.Prop.TIProp
