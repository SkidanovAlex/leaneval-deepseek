import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts
import Submission.Work.FTS.EllipticEst.Deleg.psiDSecondDeriv
import Submission.Work.FTS.EllipticEst.Deleg.psiD_deriv2_zero_mid

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false

/-!
## The `(1)`-D collar bound for the angular cut-off `psiD δ`

We prove `mixedCollarBound`: there is a universal constant `Cw > 0` such that for every
`K > 0`, `δ > 0` with `4δ ≤ π/2`, and every `f` whose slices satisfy the two endpoint *rates*

`f(θ)² ≤ K θ^{1+η} ∫_0^θ σ (f')²`,  `f(θ)² ≤ K (π/2-θ)^{1+η} ∫_θ^{π/2} σ (f')²`

(with `σ = sin(2θ)^{-η}`, `η = 99/100`) one has

`|∫_0^{π/2} σ ψ_δ'' f²| ≤ Cw K (∫_0^δ σ (f')² + ∫_{π/2-δ}^{π/2} σ (f')²)`.

The proof is pointwise: `ψ_δ''` vanishes on `(δ/2, π/2-δ/2)` and is `O(1/δ²)` everywhere, so

`|σ ψ_δ'' f²| ≤ (Cψ/δ²) σ f² · 1_{collar}`,

and on the collars the rates give `σ f² ≤ K A_i C₀ · (distance to the endpoint)`, whose integral
over the collar of width `δ` is `≤ K A_i C₀ δ²`; this cancels the `1/δ²`.

(The pointwise bounds `σ θ θ^{1+η} ≤ (π/4)^η θ` and its reflected twin follow from
`sin(2θ) ≥ 4θ/π`.)
-/

/-- On `(0,π/4]` we have `θ^{1+η} σ(θ) ≤ (π/4)^η θ`. -/
theorem sigTheta_mul_rpow_le_left {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 4) :
    θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * θ := by
  have hη := Work.Spaces.eta_pos
  have hπ := Real.pi_pos
  have hsin_pos : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsin_le : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin_pos
  have hsin : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
    have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith)
    calc (4 / Real.pi) * θ = 2 / Real.pi * (2 * θ) := by ring
      _ ≤ Real.sin (2 * θ) := h
  have hratio : θ / Real.sin (2 * θ) ≤ Real.pi / 4 := by
    rw [div_le_iff₀ hsin_pos]
    calc θ = (Real.pi / 4) * ((4 / Real.pi) * θ) := by field_simp
      _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin (by positivity)
  have hpow : (θ / Real.sin (2 * θ)) ^ Work.Spaces.eta
      ≤ (Real.pi / 4) ^ Work.Spaces.eta :=
    Real.rpow_le_rpow (by positivity) hratio (le_of_lt hη)
  have hident : θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ
      = θ * (θ / Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [Work.FTS.EllipticEst.AngSecond.sig, Real.rpow_neg hsin_le, Real.rpow_add hθ0,
      Real.rpow_one, Real.div_rpow (le_of_lt hθ0) hsin_le, div_eq_mul_inv]
    ring
  rw [hident]
  calc θ * (θ / Real.sin (2 * θ)) ^ Work.Spaces.eta
      ≤ θ * (Real.pi / 4) ^ Work.Spaces.eta := mul_le_mul_of_nonneg_left hpow (le_of_lt hθ0)
    _ = (Real.pi / 4) ^ Work.Spaces.eta * θ := by ring

/-- The angular weight is invariant under `θ ↦ π/2 - θ`. -/
theorem sigTheta_reflect (θ : ℝ) :
    Work.FTS.EllipticEst.AngSecond.sig (Real.pi / 2 - θ)
      = Work.FTS.EllipticEst.AngSecond.sig θ := by
  rw [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.AngSecond.sig,
    show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-- On `[π/4, π/2)` we have `(π/2-θ)^{1+η} σ(θ) ≤ (π/4)^η (π/2-θ)`. -/
theorem sigTheta_mul_rpow_le_right {θ : ℝ} (hθ : Real.pi / 4 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2 - θ) := by
  have h1 : 0 < Real.pi / 2 - θ := by linarith
  have h2 : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
  have h := sigTheta_mul_rpow_le_left h1 h2
  rwa [sigTheta_reflect] at h


/-- **The mixed collar bound.**  A single constant `Cw` works in `CollarBound`. -/
theorem mixedCollarBound : ∃ Cw : ℝ, 0 < Cw ∧ Work.FTS.EllipticEst.Deleg.CollarBound Cw := by
  obtain ⟨C1, hC1pos, hC1⟩ := psiD_deriv2_bound_alt
  have hmid0 := psiD_deriv2_zero_mid
  have hC0pos : 0 < (Real.pi / 4) ^ Work.Spaces.eta :=
    Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _
  have hCwpos : 0 < C1 * (2 * (Real.pi / 4) ^ Work.Spaces.eta) + 1 := by
    nlinarith [hC1pos, hC0pos]
  refine ⟨C1 * (2 * (Real.pi / 4) ^ Work.Spaces.eta) + 1, hCwpos, ?_⟩
  intro K hK δ hδ hδ2 f hf1 hfint hrateL hrateR
  have hπ : 0 < Real.pi := Real.pi_pos
  have hδπ : δ < Real.pi / 2 := by linarith
  have hδ8 : δ ≤ Real.pi / 8 := by linarith
  have hδ4 : δ ≤ Real.pi / 4 := by linarith
  -- ### order of the two factors of the integrand
  have hd_eq : (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      = fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    funext θ; ring
  have hfint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) volume := by
    rw [hd_eq]; exact hfint
  -- ### the two collars
  have hc1I : Set.Ioo (0 : ℝ) δ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Ioo_right (le_of_lt hδπ)
  have hc2I : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Set.Ioo_subset_Ioo_left (by linarith)
  have hsig_nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ := fun θ hθ =>
    Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hd_nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2 :=
    fun θ hθ => mul_nonneg (hsig_nn θ hθ) (sq_nonneg _)
  have hc1intd : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      (Set.Ioo (0 : ℝ) δ) volume := hfint'.mono_set hc1I
  have hc2intd : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ * (deriv f θ) ^ 2)
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) volume := hfint'.mono_set hc2I
  -- ### the two collar energies, and `C0`
  let A1 : ℝ := ∫ t in Set.Ioo (0 : ℝ) δ,
    Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2
  let A2 : ℝ := ∫ t in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
    Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2
  let C0 : ℝ := (Real.pi / 4) ^ Work.Spaces.eta
  have hA1nn : 0 ≤ A1 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => hd_nn θ (hc1I hθ))
  have hA2nn : 0 ≤ A2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => hd_nn θ (hc2I hθ))
  -- ### the pointwise bounds on the two collars
  have hpt1 : ∀ θ ∈ Set.Ioo (0 : ℝ) δ,
      Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2 ≤ K * A1 * (C0 * θ) := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hc1I hθ
    have hθ0 : 0 < θ := hθ.1
    have hθ4 : θ ≤ Real.pi / 4 := by linarith [hθ.2, hδ4]
    have hE : (∫ t in Set.Ioo (0 : ℝ) θ,
        Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ A1 := by
      refine MeasureTheory.setIntegral_mono_set hc1intd ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hd_nn t (hc1I ht)
      · exact Eventually.of_forall
          (fun t ht => Set.Ioo_subset_Ioo_right (le_of_lt hθ.2) ht)
    have hrate := hrateL θ hθI
    have hrate' : (f θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo (0 : ℝ) θ,
            Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) := by
      simpa only [← hd_eq] using hrate
    have hYnn : 0 ≤ θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hθ0) _) (hsig_nn θ hθI)
    have h2 : θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ ≤ C0 * θ :=
      sigTheta_mul_rpow_le_left hθ0 hθ4
    calc Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2
        ≤ Work.FTS.EllipticEst.AngSecond.sig θ
            * (K * θ ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo (0 : ℝ) θ,
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hrate' (hsig_nn θ hθI)
      _ = K * (∫ t in Set.Ioo (0 : ℝ) θ,
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
            * (θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
      _ ≤ K * A1 * (C0 * θ) := by
          have h1 : K * (∫ t in Set.Ioo (0 : ℝ) θ,
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ K * A1 :=
            mul_le_mul_of_nonneg_left hE (le_of_lt hK)
          calc K * (∫ t in Set.Ioo (0 : ℝ) θ,
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
                * (θ ^ (1 + Work.Spaces.eta) * Work.FTS.EllipticEst.AngSecond.sig θ)
              ≤ K * A1 * (θ ^ (1 + Work.Spaces.eta)
                  * Work.FTS.EllipticEst.AngSecond.sig θ) :=
                mul_le_mul_of_nonneg_right h1 hYnn
            _ ≤ K * A1 * (C0 * θ) :=
                mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_of_lt hK) hA1nn)
  have hpt2 : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
      Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2
        ≤ K * A2 * (C0 * (Real.pi / 2 - θ)) := by
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hc2I hθ
    have hθ4 : Real.pi / 4 ≤ θ := by linarith [hθ.1, hδ4]
    have hE : (∫ t in Set.Ioo θ (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ A2 := by
      refine MeasureTheory.setIntegral_mono_set hc2intd ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hd_nn t (hc2I ht)
      · exact Eventually.of_forall
          (fun t ht => Set.Ioo_subset_Ioo_left (le_of_lt hθ.1) ht)
    have hrate := hrateR θ hθI
    have hrate' : (f θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo θ (Real.pi / 2),
            Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) := by
      simpa only [← hd_eq] using hrate
    have hYnn : 0 ≤ (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * Work.FTS.EllipticEst.AngSecond.sig θ :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hθ.2]) _) (hsig_nn θ hθI)
    have h2 : (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
        * Work.FTS.EllipticEst.AngSecond.sig θ ≤ C0 * (Real.pi / 2 - θ) :=
      sigTheta_mul_rpow_le_right hθ4 hθI.2
    calc Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2
        ≤ Work.FTS.EllipticEst.AngSecond.sig θ
            * (K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo θ (Real.pi / 2),
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hrate' (hsig_nn θ hθI)
      _ = K * (∫ t in Set.Ioo θ (Real.pi / 2),
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
            * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
      _ ≤ K * A2 * (C0 * (Real.pi / 2 - θ)) := by
          have h1 : K * (∫ t in Set.Ioo θ (Real.pi / 2),
              Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2) ≤ K * A2 :=
            mul_le_mul_of_nonneg_left hE (le_of_lt hK)
          calc K * (∫ t in Set.Ioo θ (Real.pi / 2),
                  Work.FTS.EllipticEst.AngSecond.sig t * (deriv f t) ^ 2)
                * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                    * Work.FTS.EllipticEst.AngSecond.sig θ)
              ≤ K * A2 * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                  * Work.FTS.EllipticEst.AngSecond.sig θ) :=
                mul_le_mul_of_nonneg_right h1 hYnn
            _ ≤ K * A2 * (C0 * (Real.pi / 2 - θ)) :=
                mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_of_lt hK) hA2nn)
  -- ### the dominating function
  let g1 : ℝ → ℝ := fun θ => (C1 / δ ^ 2) * K * A1 * C0
      * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ
  let g2 : ℝ → ℝ := fun θ => (C1 / δ ^ 2) * K * A2 * C0
      * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator (fun θ : ℝ => Real.pi / 2 - θ) θ
  have hg1eq : ∀ θ : ℝ, g1 θ = (C1 / δ ^ 2) * K * A1 * C0
      * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ := fun θ => rfl
  have hg2eq : ∀ θ : ℝ, g2 θ = (C1 / δ ^ 2) * K * A2 * C0
      * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
          (fun θ : ℝ => Real.pi / 2 - θ) θ := fun θ => rfl
  -- ### integrability of the dominating function
  have hvol1 : volume (Set.Ioo (0 : ℝ) δ) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hvol2 : volume (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hlin1 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ) (Set.Ioo (0 : ℝ) δ) volume := by
    refine MeasureTheory.IntegrableOn.of_bound hvol1 continuous_id.aestronglyMeasurable δ ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_pos ht.1]
    exact le_of_lt ht.2
  have hlin2 : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.pi / 2 - θ)
      (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) volume := by
    refine MeasureTheory.IntegrableOn.of_bound hvol2
      ((continuous_const.sub continuous_id)).aestronglyMeasurable δ ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [ht.2])]
    linarith [ht.1]
  have hint1 : Integrable ((Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => θ) (Set.Ioo (0 : ℝ) δ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hlin1.restrict
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2 h
  have hint2 : Integrable ((Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
      (fun θ : ℝ => Real.pi / 2 - θ))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.pi / 2 - θ)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hlin2.restrict
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).2 h
  have hg1int : Integrable g1 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    change Integrable (fun θ => (C1 / δ ^ 2) * K * A1 * C0
      * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ) _
    exact hint1.const_mul _
  have hg2int : Integrable g2 (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    change Integrable (fun θ => (C1 / δ ^ 2) * K * A2 * C0
      * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
          (fun θ : ℝ => Real.pi / 2 - θ) θ) _
    exact hint2.const_mul _
  have hsumint : Integrable (fun θ => g1 θ + g2 θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hg1int.add hg2int
  -- ### the pointwise domination
  have hpt : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ‖(Work.FTS.EllipticEst.AngSecond.sig θ
          * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2)‖
        ≤ g1 θ + g2 θ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθI
    by_cases h1 : θ ∈ Set.Ioo (0 : ℝ) δ
    · have h2not : θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) := by
        intro hc
        linarith [h1.2, hc.1, hδ8]
      rw [hg1eq θ, hg2eq θ, Set.indicator_of_mem h1, Set.indicator_of_notMem h2not,
        mul_zero, add_zero, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (hsig_nn θ hθI), abs_of_nonneg (sq_nonneg (f θ))]
      have hψ : |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| ≤ C1 / δ ^ 2 :=
        hC1 δ hδ θ
      calc Work.FTS.EllipticEst.AngSecond.sig θ
            * |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| * (f θ) ^ 2
          ≤ Work.FTS.EllipticEst.AngSecond.sig θ * (C1 / δ ^ 2) * (f θ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hψ (hsig_nn θ hθI)) (sq_nonneg _)
        _ = (C1 / δ ^ 2) * (Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2) := by ring
        _ ≤ (C1 / δ ^ 2) * (K * A1 * (C0 * θ)) :=
            mul_le_mul_of_nonneg_left (hpt1 θ h1)
              (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
        _ = (C1 / δ ^ 2) * K * A1 * C0 * θ := by ring
    · by_cases h2 : θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)
      · rw [hg1eq θ, hg2eq θ, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
          mul_zero, zero_add, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (hsig_nn θ hθI), abs_of_nonneg (sq_nonneg (f θ))]
        have hψ : |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| ≤ C1 / δ ^ 2 :=
          hC1 δ hδ θ
        calc Work.FTS.EllipticEst.AngSecond.sig θ
              * |deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ| * (f θ) ^ 2
            ≤ Work.FTS.EllipticEst.AngSecond.sig θ * (C1 / δ ^ 2) * (f θ) ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hψ (hsig_nn θ hθI)) (sq_nonneg _)
          _ = (C1 / δ ^ 2) * (Work.FTS.EllipticEst.AngSecond.sig θ * (f θ) ^ 2) := by ring
          _ ≤ (C1 / δ ^ 2) * (K * A2 * (C0 * (Real.pi / 2 - θ))) :=
              mul_le_mul_of_nonneg_left (hpt2 θ h2)
                (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
          _ = (C1 / δ ^ 2) * K * A2 * C0 * (Real.pi / 2 - θ) := by ring
      · have hθge : δ ≤ θ := by
          rcases lt_or_ge θ δ with hlt | hge
          · exact absurd ⟨hθI.1, hlt⟩ h1
          · exact hge
        have hθle : θ ≤ Real.pi / 2 - δ := by
          rcases lt_or_ge (Real.pi / 2 - δ) θ with hlt | hge
          · exact absurd ⟨hlt, hθI.2⟩ h2
          · exact hge
        have hmid : deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ = 0 :=
          hmid0 δ hδ θ (by linarith) (by linarith)
        have hGz : Work.FTS.EllipticEst.AngSecond.sig θ
            * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2 = 0 := by
          rw [hmid, mul_zero, zero_mul]
        have hg1z : g1 θ = 0 := by
          rw [hg1eq θ, Set.indicator_of_notMem h1, mul_zero]
        have hg2z : g2 θ = 0 := by
          rw [hg2eq θ, Set.indicator_of_notMem h2, mul_zero]
        rw [hGz, hg1z, hg2z, norm_zero, add_zero]
  -- ### the integral of the dominating function
  have hstep1 : |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig θ
          * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g1 θ + g2 θ) := by
    have h := MeasureTheory.norm_integral_le_of_norm_le hsumint hpt
    simpa only [Real.norm_eq_abs] using h
  have hstep2 : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g1 θ + g2 θ)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ)
        + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ) :=
    MeasureTheory.integral_add hg1int hg2int
  have hg1val : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ
      = (C1 / δ ^ 2) * K * A1 * C0 * (∫ θ in Set.Ioo (0 : ℝ) δ, θ) := by
    change ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (C1 / δ ^ 2) * K * A1 * C0
        * (Set.Ioo (0 : ℝ) δ).indicator (fun θ : ℝ => θ) θ
      = (C1 / δ ^ 2) * K * A1 * C0 * (∫ θ in Set.Ioo (0 : ℝ) δ, θ)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo, Set.inter_comm,
      Set.inter_eq_left.2 hc1I]
  have hg2val : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ
      = (C1 / δ ^ 2) * K * A2 * C0
        * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.pi / 2 - θ)) := by
    change ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (C1 / δ ^ 2) * K * A2 * C0
        * (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)).indicator
            (fun θ : ℝ => Real.pi / 2 - θ) θ
      = (C1 / δ ^ 2) * K * A2 * C0
        * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.pi / 2 - θ))
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo, Set.inter_comm,
      Set.inter_eq_left.2 hc2I]
  have hvolc1 : ∫ θ in Set.Ioo (0 : ℝ) δ, θ = δ ^ 2 / 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (le_of_lt hδ), integral_id]
    ring
  have hvolc2 : ∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.pi / 2 - θ)
      = δ ^ 2 / 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith)]
    rw [intervalIntegral.integral_comp_sub_left (f := fun y : ℝ => y) (d := Real.pi / 2),
      integral_id]
    ring
  have hg1le : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ ≤ C1 * K * A1 * C0 := by
    rw [hg1val, hvolc1]
    have hnn : 0 ≤ (C1 / δ ^ 2) * K * A1 * C0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
        (le_of_lt hK)) hA1nn) (le_of_lt hC0pos)
    calc (C1 / δ ^ 2) * K * A1 * C0 * (δ ^ 2 / 2)
        ≤ (C1 / δ ^ 2) * K * A1 * C0 * δ ^ 2 :=
          mul_le_mul_of_nonneg_left (by linarith [sq_nonneg δ]) hnn
      _ = C1 * K * A1 * C0 := by
          rw [show (C1 / δ ^ 2) * K * A1 * C0 * δ ^ 2
              = ((C1 / δ ^ 2) * δ ^ 2) * K * A1 * C0 by ring,
            div_mul_cancel₀ C1 (pow_ne_zero 2 (ne_of_gt hδ))]
  have hg2le : ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ ≤ C1 * K * A2 * C0 := by
    rw [hg2val, hvolc2]
    have hnn : 0 ≤ (C1 / δ ^ 2) * K * A2 * C0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (le_of_lt hC1pos) (sq_nonneg δ))
        (le_of_lt hK)) hA2nn) (le_of_lt hC0pos)
    calc (C1 / δ ^ 2) * K * A2 * C0 * (δ ^ 2 / 2)
        ≤ (C1 / δ ^ 2) * K * A2 * C0 * δ ^ 2 :=
          mul_le_mul_of_nonneg_left (by linarith [sq_nonneg δ]) hnn
      _ = C1 * K * A2 * C0 := by
          rw [show (C1 / δ ^ 2) * K * A2 * C0 * δ ^ 2
              = ((C1 / δ ^ 2) * δ ^ 2) * K * A2 * C0 by ring,
            div_mul_cancel₀ C1 (pow_ne_zero 2 (ne_of_gt hδ))]
  have hfinal : |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig θ
          * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
      ≤ (C1 * (2 * C0) + 1) * K * (A1 + A2) := by
    calc |∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.FTS.EllipticEst.AngSecond.sig θ
            * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ * (f θ) ^ 2|
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g1 θ + g2 θ) := hstep1
      _ = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g1 θ)
            + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g2 θ) := hstep2
      _ ≤ C1 * K * A1 * C0 + C1 * K * A2 * C0 := add_le_add hg1le hg2le
      _ = C1 * K * C0 * (A1 + A2) := by ring
      _ ≤ (C1 * (2 * C0) + 1) * K * (A1 + A2) := by
          have hx : 0 ≤ C1 * K * C0 * (A1 + A2) :=
            mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1pos) (le_of_lt hK))
              (le_of_lt hC0pos)) (add_nonneg hA1nn hA2nn)
          have hy : 0 ≤ K * (A1 + A2) :=
            mul_nonneg (le_of_lt hK) (add_nonneg hA1nn hA2nn)
          nlinarith [hx, hy]
  exact hfinal

end Work.FTS.EllipticEst.Deleg
