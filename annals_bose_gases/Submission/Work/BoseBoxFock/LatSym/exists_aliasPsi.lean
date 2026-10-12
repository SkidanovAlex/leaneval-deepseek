import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.GreenAux
import Submission.Work.BoseBoxFock.LatSym.contDiff_kinFT
import Submission.Work.BoseBoxFock.LatSym.contDiff_mul_inv_innerSq3
import Submission.Work.BoseBoxFock.LatSym.dIter_kinFT_decay
import Submission.Work.BoseBoxFock.heatImage_t_rpow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators

namespace Work.BoseBoxFock.LatSym

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable def aliasWeight (g : E3 → ℂ) (s : ℝ) (η : E3) : E3 → ℂ :=
  fun u => autocorr g (u - s • η) * ((((inner ℝ u u : ℝ) ^ 3 : ℝ)) : ℂ)⁻¹

/-! ## The general specification -/

theorem aliasPsi_spec {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) {η : E3} (hη : ℓ < ‖η‖)
    (s : ℝ) (hs : ‖s • η‖ = ‖η‖) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => Submission.BoseGases.kinFT (aliasWeight g s η) p) ∧
      (∀ p : E3,
        Work.BoseBoxFock.lap3 (fun p : E3 => Submission.BoseGases.kinFT (aliasWeight g s η) p) p
          = -(Submission.BoseGases.kinFT (autocorr g) p) *
              Complex.exp (-((s : ℂ) * Complex.I * (inner ℝ η p : ℂ)))) ∧
      (∀ p : E3, ‖Submission.BoseGases.kinFT (aliasWeight g s η) p‖
          ≤ (∫ u : E3, ‖autocorr g u‖) / (‖η‖ - ℓ) ^ 6) ∧
      (∀ L : List E3, L.length ≤ 6 → ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3,
        ‖Work.BoseBoxFock.dIter (fun p : E3 => Submission.BoseGases.kinFT (aliasWeight g s η) p) L p‖
          ≤ C * (1 + ‖p‖) ^ (-7 : ℝ)) := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_closedBall hgs
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (autocorr g) := Green.autocorr_contDiff hg hgc
  have hcs : HasCompactSupport (autocorr g) := Green.hasCompactSupport_autocorr hgc
  -- the shifted autocorrelation is smooth
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun u : E3 => autocorr g (u - s • η)) :=
    hcd.comp (contDiff_id.sub contDiff_const)
  -- vanishing near the origin
  have hvan : ∀ u : E3, ℓ < ‖u - s • η‖ → autocorr g (u - s • η) = 0 :=
    fun u hu => autocorr_eq_zero_of_lt_norm_closed hℓ hgs hu
  have h0 : ∃ δ : ℝ, 0 < δ ∧ ∀ u : E3, ‖u‖ < δ → autocorr g (u - s • η) = 0 := by
    refine ⟨(‖η‖ - ℓ) / 2, by linarith, fun u hu => ?_⟩
    refine hvan u ?_
    have h1 : ‖s • η‖ - ‖u‖ ≤ ‖u - s • η‖ := by
      have h := abs_norm_sub_norm_le (s • η) u
      rw [norm_sub_rev (s • η) u] at h
      have h2 : (‖s • η‖ - ‖u‖) ≤ |‖s • η‖ - ‖u‖| := le_abs_self _
      linarith
    rw [hs] at h1
    linarith
  -- smoothness of the weight
  have hβd : ContDiff ℝ (⊤ : ℕ∞) (aliasWeight g s η) :=
    contDiff_mul_inv_innerSq3 hshift h0
  -- compact support of the weight
  have hβc : HasCompactSupport (aliasWeight g s η) := by
    have hcc : HasCompactSupport (fun u : E3 => autocorr g (u - s • η)) := by
      have h := hcs.comp_homeomorph (Homeomorph.addRight (-(s • η)))
      simpa [Function.comp_def, Homeomorph.addRight, sub_eq_add_neg] using h
    exact hcc.mul_right (f' := fun u : E3 => ((((inner ℝ u u : ℝ) ^ 3 : ℝ)) : ℂ)⁻¹)
  -- the pointwise cancellation `‖u‖⁶ · wgt u = A g (u - s•η)`
  have hβmul : ∀ u : E3, (((‖u‖ ^ 6 : ℝ)) : ℂ) * aliasWeight g s η u
      = autocorr g (u - s • η) := by
    intro u
    have hK : (inner ℝ u u : ℝ) ^ 3 = ‖u‖ ^ 6 := by
      rw [real_inner_self_eq_norm_sq]; ring
    rw [aliasWeight, hK]
    by_cases hu : (‖u‖ : ℝ) = 0
    · have huz : u = 0 := norm_eq_zero.mp hu
      subst huz
      have hz : (((‖(0 : E3)‖ ^ 6 : ℝ)) : ℂ) = 0 := by simp
      rw [hz, zero_mul]
      exact (autocorr_eq_zero_of_lt_norm_closed hℓ hgs
        (by rw [zero_sub, norm_neg, hs]; exact hη)).symm
    · have h6 : (((‖u‖ ^ 6 : ℝ)) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact pow_ne_zero 6 hu
      rw [← mul_assoc, mul_comm (((‖u‖ ^ 6 : ℝ)) : ℂ) (autocorr g (u - s • η)), mul_assoc,
        mul_inv_cancel₀ h6, mul_one]
  -- the pointwise norm bound
  have hβbound : ∀ u : E3, ‖aliasWeight g s η u‖ ≤
      ((‖η‖ - ℓ) ^ 6)⁻¹ * ‖autocorr g (u - s • η)‖ := by
    intro u
    by_cases hc0 : autocorr g (u - s • η) = 0
    · rw [aliasWeight, hc0, zero_mul, norm_zero, mul_zero]
    · have hlt : ‖u - s • η‖ < ℓ := by
        by_contra hle
        exact hc0 (autocorr_eq_zero_of_le_norm_closed hℓ hg hgs (le_of_not_gt hle))
      have hnorm : ‖η‖ - ℓ < ‖u‖ := by
        have h1 : ‖u‖ + ‖u - s • η‖ ≥ ‖s • η‖ := by
          have h := norm_sub_le u (u - s • η)
          simpa [sub_sub_cancel] using h
        rw [hs] at h1
        linarith
      have hK : (inner ℝ u u : ℝ) ^ 3 = ‖u‖ ^ 6 := by
        rw [real_inner_self_eq_norm_sq]; ring
      have hpos : 0 < ‖u‖ := by linarith
      have hle : (‖η‖ - ℓ) ^ 6 ≤ ‖u‖ ^ 6 :=
        pow_le_pow_left₀ (by linarith) hnorm.le 6
      rw [aliasWeight, hK, norm_mul, mul_comm (((‖η‖ - ℓ) ^ 6)⁻¹) (‖autocorr g (u - s • η)‖)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hnorm6 : ‖(((‖u‖ ^ 6 : ℝ)) : ℂ)‖ = ‖u‖ ^ 6 := by simp
      rw [norm_inv, hnorm6]
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hle
  -- integrability
  have hβInt : Integrable (fun u : E3 => ‖aliasWeight g s η u‖) :=
    hβd.continuous.norm.integrable_of_hasCompactSupport hβc.norm
  have hautonorm : Integrable (fun u : E3 => ‖autocorr g u‖) :=
    (autocorr_integrable hg hgc).norm
  have hnormInt : Integrable (fun u : E3 => ‖autocorr g (u - s • η)‖) :=
    hautonorm.comp_sub_right (s • η)
  -- the sup bound
  have hbound : ∀ p : E3, ‖Submission.BoseGases.kinFT (aliasWeight g s η) p‖
      ≤ (∫ u : E3, ‖autocorr g u‖) / (‖η‖ - ℓ) ^ 6 := by
    intro p
    have h1 : ‖Submission.BoseGases.kinFT (aliasWeight g s η) p‖
        ≤ ∫ u : E3, ‖aliasWeight g s η u‖ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show ‖Complex.exp (-(Complex.I * (inner ℝ p u : ℂ))) * aliasWeight g s η u‖
        = ‖aliasWeight g s η u‖
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(Complex.I * (inner ℝ p u : ℂ))).re = 0 := by simp
      rw [hre, Real.exp_zero, one_mul]
    have h2 : (∫ u : E3, ‖aliasWeight g s η u‖) ≤
        ∫ u : E3, ((‖η‖ - ℓ) ^ 6)⁻¹ * ‖autocorr g (u - s • η)‖ :=
      integral_mono_ae hβInt (hnormInt.const_mul _) (Eventually.of_forall hβbound)
    have h3 : (∫ u : E3, ((‖η‖ - ℓ) ^ 6)⁻¹ * ‖autocorr g (u - s • η)‖)
        = ((‖η‖ - ℓ) ^ 6)⁻¹ * (∫ u : E3, ‖autocorr g u‖) := by
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (fun u : E3 => ‖autocorr g u‖) (s • η)
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [h3, div_eq_mul_inv, mul_comm]
  -- the `Δ³` identity
  have hLap : ∀ p : E3,
      Work.BoseBoxFock.lap3 (fun p : E3 => Submission.BoseGases.kinFT (aliasWeight g s η) p) p
        = -(Submission.BoseGases.kinFT (autocorr g) p) *
            Complex.exp (-((s : ℂ) * Complex.I * (inner ℝ η p : ℂ))) := by
    have hfun : (fun z : E3 => (((‖z‖ ^ 6 : ℝ)) : ℂ) * aliasWeight g s η z)
        = fun z : E3 => autocorr g (z - s • η) := funext hβmul
    intro p
    have hlap := congrFun (lap3_kinFT hβd hβc) p
    rw [hlap, hfun, kinFT_sub_right (autocorr g) (s • η) p]
    have harg : -(Complex.I * ((inner ℝ (s • η) p : ℝ) : ℂ))
        = -((s : ℂ) * Complex.I * (inner ℝ η p : ℂ)) := by
      rw [real_inner_smul_left]; push_cast; ring
    rw [harg]
    ring
  -- the decay
  have hDec : ∀ L : List E3, L.length ≤ 6 → ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3,
      ‖Work.BoseBoxFock.dIter (fun p : E3 => Submission.BoseGases.kinFT (aliasWeight g s η) p) L p‖
        ≤ C * (1 + ‖p‖) ^ (-7 : ℝ) :=
    fun L _ => dIter_kinFT_decay hβd hβc L
  exact ⟨contDiff_kinFT hβd hβc, hLap, hbound, hDec⟩

/-!
# `Work.BoseBoxFock.LatSym.exists_aliasPsi`

For `g` smooth with `tsupport g ⊆ closedBall 0 (ℓ/2)`, `ℓ > 0` and `η` with `ℓ < ‖η‖`, we need two
`C^∞` functions `Ψ_±` with

    lap3 Ψ_± = -(kinFT (autocorr g)) * exp (∓ I ⟪η,·⟫)

(`lap3 = Δ³`, `autocorr g u = ∫ x, g x * conj (g (x-u))`, `kinFT` is the corpus's `p`-convention
Fourier transform), together with an `L^∞` bound `‖Ψ_±‖ ≤ (∫ ‖autocorr g‖) / (‖η‖-ℓ)^6` and the
superpolynomial decay of all `dIter Ψ_± L`, `|L| ≤ 6`.

## Explicit construction

`a := autocorr g` is `C^∞` with `tsupport a ⊆ closedBall 0 ℓ`, hence integrable
(`GreenAux.autocorr_contDiff`, `GreenAux.hasCompactSupport_autocorr`, `AliasAux.autocorr_integrable`,
and for the support `AliasClosedAux.autocorr_eq_zero_of_le_norm_closed`), and
`kinFT a p = ∫ u, a u * exp (-(I ⟪p,u⟫)) du`.

For `s = ±1` put

    Ψ_s(p) = ∫ u, a u * ((‖u + s•η‖ ^ 2) ^ 3)⁻¹ * exp (-(I * ⟪p, u + s•η⟫)) .

(On `tsupport a` one has `‖u + s•η‖ ≥ ‖η‖ - ℓ > 0`, so the weight is smooth.)

Then:
* `dIter Ψ_s L p = ∫ u, a u * ((‖u+s•η‖^2)^3)⁻¹ * dIter (fun q => exp (-(I ⟪q, u+s•η⟫))) L p du`
  by induction on `L`, differentiating under the integral sign (dominated convergence; the
  `u`-integral is effectively over the compact `tsupport a`, where each derivative brings a bounded
  factor `‖u+s•η‖`);
* `dIter (fun q => exp (-(I ⟪q,z⟫))) L p = (∏_{w ∈ L} (-I ⟪w,z⟫)) * exp (-(I ⟪p,z⟫))`, and summing
  over the 27 triples `(a,b,c)` gives `lap3 (fun q => exp (-(I ⟪q,z⟫))) p = -‖z‖^6 * exp (-(I ⟪p,z⟫))`
  because `(-I)^6 = -1`, `Σ_{a,b,c} z_a²z_b²z_c² = ‖z‖^6` and `lap3 = Δ³`; hence
  `lap3 Ψ_s(p) = -∫ u, a u * exp (-(I ⟪p, u+s•η⟫)) du = -kinFT a p * exp (-(s*I) ⟪p,η⟫)`
  (factor out the constant phase `exp (-(s*I)⟪p,η⟫)` → conjunct 1 is `s = +1`, conjunct 2 is
  `s = -1`, using `inner ℝ η p = inner ℝ p η`);
* the bound: `‖Ψ_s p‖ ≤ ∫ u, ‖a u‖ * (‖η‖-ℓ)^{-6} du = (∫ u, ‖a u‖) / (‖η‖ - ℓ)^6`;
* the decay of `dIter Ψ_s L` (order ≤ 6): the `u`-integral equals
  `exp (-(s*I)⟪p,η⟫) * kinFT b_L p` with the compactly supported smooth
  `b_L u = a u * ((‖u+s•η‖^2)^3)⁻¹ * ∏_{w∈L}(-(I ⟪w,u+s•η⟫))`, so
  `‖kinFT b_L p‖ ≤ C_L (1+‖p‖)^{-N}` for every `N` by `SqrtKin.kinFT_decay_gen`
  (or `OneBodyKin.kinFT_decay_le`).

The result is used as `v` in `BoseBoxFock/LatSym/integral_mul_lap3_eq_of_quad`, which is where the
decay hypothesis comes from.
-/
theorem exists_aliasPsi {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    {η : EuclideanSpace ℝ (Fin 3)} (hη : ℓ < ‖η‖) :
    (∃ Ψ : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        (∀ p : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.lap3 Ψ p = -(Submission.BoseGases.kinFT (Work.BoseBoxFock.autocorr g) p) *
            Complex.exp (-(Complex.I * (inner ℝ η p : ℂ)))) ∧
        (∀ p : EuclideanSpace ℝ (Fin 3),
          ‖Ψ p‖ ≤ (∫ u : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.autocorr g u‖) / (‖η‖ - ℓ) ^ 6) ∧
        (∀ L : List (EuclideanSpace ℝ (Fin 3)), L.length ≤ 6 → ∃ C : ℝ, 0 ≤ C ∧
          ∀ p : EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseBoxFock.dIter Ψ L p‖ ≤ C * (1 + ‖p‖) ^ (-7 : ℝ))) ∧
      (∃ Ψ : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        (∀ p : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.lap3 Ψ p = -(Submission.BoseGases.kinFT (Work.BoseBoxFock.autocorr g) p) *
            Complex.exp (Complex.I * (inner ℝ η p : ℂ))) ∧
        (∀ p : EuclideanSpace ℝ (Fin 3),
          ‖Ψ p‖ ≤ (∫ u : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.autocorr g u‖) / (‖η‖ - ℓ) ^ 6) ∧
        (∀ L : List (EuclideanSpace ℝ (Fin 3)), L.length ≤ 6 → ∃ C : ℝ, 0 ≤ C ∧
          ∀ p : EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseBoxFock.dIter Ψ L p‖ ≤ C * (1 + ‖p‖) ^ (-7 : ℝ))) := by

  have hplus := aliasPsi_spec hℓ hg hgs hη (1 : ℝ) (by simp)
  have hminus := aliasPsi_spec hℓ hg hgs hη (-1 : ℝ) (by simp)
  constructor
  · refine ⟨fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinFT (aliasWeight g 1 η) p,
      hplus.1, ?_, hplus.2.2.1, hplus.2.2.2⟩
    intro p
    have h := hplus.2.1 p
    have harg : -((((1 : ℝ)) : ℂ) * Complex.I * (inner ℝ η p : ℂ))
        = -(Complex.I * (inner ℝ η p : ℂ)) := by
      rw [Complex.ofReal_one]; ring
    rw [harg] at h
    exact h
  · refine ⟨fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinFT (aliasWeight g (-1) η) p,
      hminus.1, ?_, hminus.2.2.1, hminus.2.2.2⟩
    intro p
    have h := hminus.2.1 p
    have harg : -((((↑(-1 : ℝ))) : ℂ) * Complex.I * (inner ℝ η p : ℂ))
        = Complex.I * (inner ℝ η p : ℂ) := by
      rw [Complex.ofReal_neg, Complex.ofReal_one]; ring
    rw [harg] at h
    exact h

end Work.BoseBoxFock.LatSym
