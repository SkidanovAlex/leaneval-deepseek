import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.OneBodyKin.kinFT_chiScale
import Submission.Work.OneBodyKin.kinFT_comp_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsPair_eq_cos` — the cross form `bsPair` as a cosine integral

The cross form of the projected moving-box family (FS's `⟨χ_u, F(√−Δ)(χ_u ψ)⟩`) is defined in
`Submission.Work.OneBodyKin.Defs` as

  `bsPair ℓ F u ψ = (2π)⁻³ ∫_p F(‖p‖) · Re[kinFT χ_u(p) · conj(kinFT (χ_u ψ)(p))]`.

This file computes it: with `χ_u(x) = χ(x/ℓ − u)` the moving-box window, the two Fourier
transforms contribute the phase factors `e^{−i⟪ℓp,u⟫}` (which cancel against each other) and the
dilations `ℓ³` (`ℓ⁶` in the product), leaving

  `bsPair ℓ F u ψ = (2π)⁻³ ℓ⁶ ∫_p F(‖p‖) · profHat(ℓp) ·
      (∫_v χ(v) ψ(ℓ(v+u)) cos⟪ℓp,v⟫ dv)`.

## Structure

* `kinFT_bsWin` — `kinFT χ_u(p) = e^{−i⟪ℓp,u⟫} ℓ³ profHat(ℓp)`;
* `kinFT_bsWin_mul` — the same for the product `χ_u·ψ`, where the dilation substitution
  `z = ℓ(v+u)` produces the inner `v`-integral;
* `integrable_bsPairExp` — the `v`-integrand is continuous with compact support, hence integrable;
* `starRingEnd_cexp_neg_I_mul` — `conj(e^{−i t}) = e^{i t}` for real `t`;
* `bsPair_integrand_re` — the pointwise identity `Re[𝓕χ_u · conj(𝓕(χ_uψ))] = ℓ⁶ profHat(ℓp) ∫_v …`;
* `bsPair_eq_cos` — the pointwise identity integrated against `F(‖p‖)`.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The Fourier transform of the moving-box window -/

/-- The moving-box window `χ_u = χ(·/ℓ − u)` has `p`-convention Fourier transform
`e^{−i⟪ℓp,u⟫} · ℓ³ · profHat(ℓp)`: translation by `ℓu` (`kinFT_comp_sub`) contributes the phase,
the dilation `χ(·/ℓ)` (`kinFT_chiScale`) the factor `ℓ³`. -/
theorem kinFT_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u p : ℝ³) :
    Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p
      = Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) u : ℝ) : ℂ))) *
          ((ℓ : ℂ) ^ 3 * (Work.OneBodyKin.profHat (ℓ • p) : ℂ)) := by
  rw [show (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ))
      = (fun z : ℝ³ => (Submission.BoseGases.chiScale ℓ (z - ℓ • u) : ℂ)) from rfl]
  rw [Work.OneBodyKin.kinFT_comp_sub (fun w : ℝ³ => (Submission.BoseGases.chiScale ℓ w : ℂ))
      (ℓ • u) p, Work.OneBodyKin.kinFT_chiScale (ℓ := ℓ) hℓ p]
  congr 1
  congr 1
  rw [inner_smul_right, inner_smul_left]
  simp

/-! ## 2. The Fourier transform of `χ_u · ψ` -/

/-- The `p`-convention Fourier transform of `χ_u · ψ`: the dilation substitution `z = ℓ(v+u)`
(volume factor `ℓ³`) turns it into `e^{−i⟪ℓp,u⟫} ℓ³ ∫_v e^{−i⟪ℓp,v⟫} χ(v) ψ(ℓ(v+u)) dv`. -/
theorem kinFT_bsWin_mul {ℓ : ℝ} (hℓ : 0 < ℓ) (u p : ℝ³) (ψ : ℝ³ → ℝ) :
    Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p
      = Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) u : ℝ) : ℂ))) *
          ((ℓ : ℂ) ^ 3 * ∫ v : ℝ³,
            Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))) *
              ((Submission.BoseGases.chi v * ψ (ℓ • (v + u)) : ℝ) : ℂ)) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  rw [Submission.BoseGases.kinFT]
  rw [Work.OneBodyKin.integral_eq_smul_integral_comp_smul
      (g := fun z : ℝ³ => Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ))) *
          ((Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ))) hℓ]
  rw [show (∫ s : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p (ℓ • s) : ℝ) : ℂ))) *
          ((Work.BSKinetic.bsWin ℓ u (ℓ • s) : ℂ) * (ψ (ℓ • s) : ℂ)))
        = ∫ s : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) s : ℝ) : ℂ))) *
            ((Submission.BoseGases.chi (s - u) : ℂ) * (ψ (ℓ • s) : ℂ)) from by
    apply integral_congr_ae; filter_upwards with s
    have hcs : Work.BSKinetic.bsWin ℓ u (ℓ • s) = Submission.BoseGases.chi (s - u) := by
      rw [Work.BSKinetic.bsWin]
      rw [show ℓ • s - ℓ • u = ℓ • (s - u) from by module]
      exact Submission.BoseGases.chiScale_apply_smul hℓne (s - u)
    have hin : inner ℝ p (ℓ • s) = inner ℝ (ℓ • p) s := by
      simp [inner_smul_left, inner_smul_right]
    rw [hcs, hin]]
  rw [show (∫ s : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) s : ℝ) : ℂ))) *
          ((Submission.BoseGases.chi (s - u) : ℂ) * (ψ (ℓ • s) : ℂ)))
        = ∫ v : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) (v + u) : ℝ) : ℂ))) *
            ((Submission.BoseGases.chi ((v + u) - u) : ℂ) * (ψ (ℓ • (v + u)) : ℂ)) from by
    rw [← integral_add_right_eq_self
      (f := fun s : ℝ³ => Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) s : ℝ) : ℂ))) *
          ((Submission.BoseGases.chi (s - u) : ℂ) * (ψ (ℓ • s) : ℂ))) u]]
  rw [show (∫ v : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) (v + u) : ℝ) : ℂ))) *
          ((Submission.BoseGases.chi ((v + u) - u) : ℂ) * (ψ (ℓ • (v + u)) : ℂ)))
        = ∫ v : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) u : ℝ) : ℂ))) *
            (Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))) *
              ((Submission.BoseGases.chi v * ψ (ℓ • (v + u)) : ℝ) : ℂ)) from by
    apply integral_congr_ae; filter_upwards with v
    have hvu : (v + u) - u = v := by abel
    rw [hvu, inner_add_right]
    rw [show -(Complex.I * (((inner ℝ (ℓ • p) v + inner ℝ (ℓ • p) u : ℝ)) : ℂ))
        = -(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ)) +
          -(Complex.I * ((inner ℝ (ℓ • p) u : ℝ) : ℂ)) from by push_cast; ring]
    rw [Complex.exp_add, Complex.ofReal_mul]
    ring]
  rw [integral_const_mul, Complex.real_smul, Complex.ofReal_pow]
  ring

/-! ## 3. Integrability of the inner `v`-integrand -/

/-- The `v`-integrand `e^{−i⟪ℓp,v⟫} χ(v) ψ(ℓ(v+u))` is continuous (as a complex-valued function)
and compactly supported (its support lies in `supp χ`), hence integrable. -/
theorem integrable_bsPairExp {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (u p : ℝ³) :
    MeasureTheory.Integrable (fun v : ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))) *
        ((Submission.BoseGases.chi v * ψ (ℓ • (v + u)) : ℝ) : ℂ)) := by
  have hcont1 : Continuous (fun v : ℝ³ => Submission.BoseGases.chi v * ψ (ℓ • (v + u))) :=
    Submission.BoseGases.chi_continuous.mul (hψ.continuous.comp (by fun_prop))
  have hcs1 : HasCompactSupport (fun v : ℝ³ => Submission.BoseGases.chi v * ψ (ℓ • (v + u))) :=
    Submission.BoseGases.chi_hasCompactSupport.mul_right
  have hG : MeasureTheory.Integrable (fun v : ℝ³ =>
      ((Submission.BoseGases.chi v * ψ (ℓ • (v + u)) : ℝ) : ℂ)) :=
    (hcont1.integrable_of_hasCompactSupport hcs1).ofReal
  refine hG.bdd_mul (c := 1) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Complex.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.const_mul
    exact Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_const.prodMk continuous_id))
  · filter_upwards with v
    rw [Complex.norm_exp]
    have h0 : (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))).re = 0 := by simp
    rw [h0, Real.exp_zero]

/-! ## 4. The star of the phase factor -/

/-- For real `t`, `conj(e^{−i t}) = e^{i t}`. -/
lemma starRingEnd_cexp_neg_I_mul (t : ℝ) :
    starRingEnd ℂ (Complex.exp (-(Complex.I * (t : ℂ)))) = Complex.exp (Complex.I * (t : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-! ## 5. The pointwise real-part identity -/

/-- The pointwise identity underlying `bsPair_eq_cos`: the real part of
`𝓕χ_u(p) · conj(𝓕(χ_u ψ)(p))` is `ℓ⁶ profHat(ℓp) ∫_v χ(v) ψ(ℓ(v+u)) cos⟪ℓp,v⟫ dv`.

The two phase factors `e^{∓i⟪ℓp,u⟫}` (from the translations in the two Fourier transforms)
cancel, leaving `ℓ⁶ profHat(ℓp)` times the (real) integral of `e^{i⟪ℓp,v⟫} χ(v)ψ(ℓ(v+u))`. -/
theorem bsPair_integrand_re {ℓ : ℝ} (hℓ : 0 < ℓ) (u p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ((Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p) *
      star (Submission.BoseGases.kinFT
        (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p)).re
      = ℓ ^ 6 * Work.OneBodyKin.profHat (ℓ • p) *
          ∫ v : ℝ³, Submission.BoseGases.chi v * ψ (ℓ • (v + u)) *
            Real.cos (inner ℝ (ℓ • p) v) := by
  rw [kinFT_bsWin hℓ u p, kinFT_bsWin_mul hℓ u p ψ]
  set K : ℂ := ∫ v : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))) *
        ((Submission.BoseGases.chi v * ψ (ℓ • (v + u)) : ℝ) : ℂ) with hK
  set th : ℂ := ((inner ℝ (ℓ • p) u : ℝ) : ℂ) with hth
  rw [show star (Complex.exp (-(Complex.I * th)) * ((ℓ : ℂ) ^ 3 * K))
      = starRingEnd ℂ (Complex.exp (-(Complex.I * th)) * ((ℓ : ℂ) ^ 3 * K)) from
        (starRingEnd_apply _).symm]
  have hstar : starRingEnd ℂ (Complex.exp (-(Complex.I * th)) * ((ℓ : ℂ) ^ 3 * K))
      = Complex.exp (Complex.I * th) * ((ℓ : ℂ) ^ 3 * (starRingEnd ℂ K)) := by
    rw [map_mul, map_mul, starRingEnd_cexp_neg_I_mul, map_pow, Complex.conj_ofReal]
  rw [hstar]
  have hexp1 : Complex.exp (-(Complex.I * th)) * Complex.exp (Complex.I * th) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hprod : Complex.exp (-(Complex.I * th)) *
        ((ℓ : ℂ) ^ 3 * (Work.OneBodyKin.profHat (ℓ • p) : ℂ)) *
        (Complex.exp (Complex.I * th) * ((ℓ : ℂ) ^ 3 * (starRingEnd ℂ K)))
      = (((ℓ ^ 6 * Work.OneBodyKin.profHat (ℓ • p) : ℝ)) : ℂ) * (starRingEnd ℂ K) := by
    rw [show Complex.exp (-(Complex.I * th)) *
          ((ℓ : ℂ) ^ 3 * (Work.OneBodyKin.profHat (ℓ • p) : ℂ)) *
          (Complex.exp (Complex.I * th) * ((ℓ : ℂ) ^ 3 * (starRingEnd ℂ K)))
        = (Complex.exp (-(Complex.I * th)) * Complex.exp (Complex.I * th)) *
          (((ℓ : ℂ) ^ 3 * (ℓ : ℂ) ^ 3) * (Work.OneBodyKin.profHat (ℓ • p) : ℂ) *
            (starRingEnd ℂ K)) from by ring]
    rw [hexp1, one_mul, ← pow_add, ← Complex.ofReal_pow ℓ 6, ← Complex.ofReal_mul]
  rw [hprod]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.conj_re]
  congr 1
  rw [hK]
  change RCLike.re (∫ v : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))) *
        ((Submission.BoseGases.chi v * ψ (ℓ • (v + u)) : ℝ) : ℂ)) =
      ∫ v : ℝ³, Submission.BoseGases.chi v * ψ (ℓ • (v + u)) *
        Real.cos (inner ℝ (ℓ • p) v)
  rw [← integral_re (integrable_bsPairExp hℓ hψ hcs u p)]
  apply integral_congr_ae
  filter_upwards with v
  change (Complex.exp (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))) *
      ((Submission.BoseGases.chi v * ψ (ℓ • (v + u)) : ℝ) : ℂ)).re =
    Submission.BoseGases.chi v * ψ (ℓ • (v + u)) * Real.cos (inner ℝ (ℓ • p) v)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Complex.exp_re]
  have h1 : (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))).re = 0 := by simp
  have h2 : (-(Complex.I * ((inner ℝ (ℓ • p) v : ℝ) : ℂ))).im = -(inner ℝ (ℓ • p) v) := by simp
  rw [h1, h2, Real.exp_zero, one_mul, Real.cos_neg]
  ring

/-! ## 6. The main identity -/

theorem bsPair_eq_cos {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.OneBodyKin.bsPair ℓ F u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 6 *
          ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ * Work.OneBodyKin.profHat (ℓ • p) *
            (∫ v : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chi v * ψ (ℓ • (v + u)) *
              Real.cos (inner ℝ (ℓ • p) v)) := by
  unfold Work.OneBodyKin.bsPair
  rw [mul_assoc]
  congr 1
  rw [show (∫ p : ℝ³, F ‖p‖ *
        (Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ)) p *
          star (Submission.BoseGases.kinFT
            (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ u z : ℂ) * (ψ z : ℂ)) p)).re)
      = ∫ p : ℝ³, F ‖p‖ * (ℓ ^ 6 * Work.OneBodyKin.profHat (ℓ • p) *
          ∫ v : ℝ³, Submission.BoseGases.chi v * ψ (ℓ • (v + u)) *
            Real.cos (inner ℝ (ℓ • p) v)) from by
    apply integral_congr_ae; filter_upwards with p
    rw [bsPair_integrand_re hℓ u p ψ hψ hcs]]
  rw [show (∫ p : ℝ³, F ‖p‖ * (ℓ ^ 6 * Work.OneBodyKin.profHat (ℓ • p) *
          ∫ v : ℝ³, Submission.BoseGases.chi v * ψ (ℓ • (v + u)) *
            Real.cos (inner ℝ (ℓ • p) v)))
      = ∫ p : ℝ³, ℓ ^ 6 * (F ‖p‖ * Work.OneBodyKin.profHat (ℓ • p) *
          ∫ v : ℝ³, Submission.BoseGases.chi v * ψ (ℓ • (v + u)) *
            Real.cos (inner ℝ (ℓ • p) v)) from by
    apply integral_congr_ae; filter_upwards with p; ring]
  rw [integral_const_mul]

end Work.OneBodyKin
