import Mathlib
import Submission.Work.BoseBoxFock.memLp_modes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.e0_prop_theta` — the Cauchy–Schwarz equality case for `θ = 1_Λ`

Let `θ_Λ = 1_{Λ(ℓ)}` be the sharp characteristic function of the box `Λ(ℓ) = ℓ • cell`
of volume `ℓ³` (`Work.BoseB4.BoxData.thetaFun`).  The Gram data of the box model
(`Work.BoseB4.realIP_thetaFun_thetaFun`) give `‖θ_Λ‖²_{L²} = ℓ³`, so by Cauchy–Schwarz

  `|∫ conj(e) θ_Λ| ≤ ‖e‖_{L²} · ℓ^{3/2}`

with equality **iff** `e` is a multiple of `θ_Λ`.  The statement below is exactly the
equality case: from `‖e‖² = 1` and `∫ conj(e) θ_Λ = ℓ^{3/2}` (the maximal possible value)
it concludes `e = c·θ_Λ` a.e. with `|c|² = ℓ⁻³`.

The proof avoids the abstract Cauchy–Schwarz equality case and computes the defect
directly: with `c = (ℓ^{3/2})⁻¹` and `f = e − c θ_Λ`, the two identities

  `∫ conj(f) e = ∫ conj(f) θ_Λ = 0`

hold by expanding `conj(f)` and using the two hypotheses plus `‖θ_Λ‖² = ℓ³`; hence
`∫ conj(f) f = 0`, and `conj(f) f = ↑(‖f‖²)` is a non-negative real integrand, so
`f = 0` a.e.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- `conj z * z` is the (real) number `‖z‖²`, viewed in `ℂ`. -/
private lemma conj_mul_self_eq_ofReal_normSq (z : ℂ) :
    (starRingEnd ℂ) z * z = (((‖z‖ ^ 2 : ℝ)) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- The real part of `conj z * z` is `‖z‖²`. -/
private lemma re_conj_mul_self (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
  rw [conj_mul_self_eq_ofReal_normSq, Complex.ofReal_re]

/-- Conjugation fixes the real numbers (in the `starRingEnd` spelling used for integrands). -/
private lemma starRingEnd_ofReal (r : ℝ) :
    (starRingEnd ℂ) ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) :=
  Complex.conj_ofReal r

theorem e0_prop_theta {ℓ : ℝ} (hℓ : 0 < ℓ) {e : EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : MeasureTheory.MemLp e 2 MeasureTheory.volume)
    (horth : ∫ x, (starRingEnd ℂ) (e x) * e x = 1)
    (hpair : ∫ x, (starRingEnd ℂ) (e x) * Work.BoseK15.corpusBox.thetaFun ℓ x
      = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ)) :
    ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      ∀ᵐ x, e x = c * Work.BoseK15.corpusBox.thetaFun ℓ x := by
  classical
  set θ : EuclideanSpace ℝ (Fin 3) → ℂ := Work.BoseK15.corpusBox.thetaFun ℓ with hθdef
  set c : ℂ := (((ℓ ^ (3 / 2 : ℝ))⁻¹ : ℝ) : ℂ) with hcdef
  set f : EuclideanSpace ℝ (Fin 3) → ℂ := fun x => e x - c * θ x with hfdef
  -- ## scalar facts about `ℓ^{3/2}` and `c`
  have ha_ne : ℓ ^ (3 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hℓ _)
  have hsq : ℓ ^ (3 / 2 : ℝ) * ℓ ^ (3 / 2 : ℝ) = ℓ ^ 3 := by
    rw [← Real.rpow_add hℓ, show (3 : ℝ) / 2 + 3 / 2 = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hc_conj : (starRingEnd ℂ) c = c := by
    rw [hcdef]
    exact starRingEnd_ofReal _
  have hc_mul_a : c * (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ) = 1 := by
    rw [hcdef, ← Complex.ofReal_mul, inv_mul_cancel₀ ha_ne, Complex.ofReal_one]
  have hreal_l3 : (ℓ ^ (3 / 2 : ℝ))⁻¹ * ℓ ^ 3 = ℓ ^ (3 / 2 : ℝ) := by
    rw [← hsq, ← mul_assoc, inv_mul_cancel₀ ha_ne, one_mul]
  have hc_mul_l3 : c * ((ℓ ^ 3 : ℝ) : ℂ) = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ) := by
    rw [hcdef, ← Complex.ofReal_mul, hreal_l3]
  have hc_scalar : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ := by
    have hreal2 : (ℓ ^ (3 / 2 : ℝ))⁻¹ * (ℓ ^ (3 / 2 : ℝ))⁻¹ = (ℓ ^ 3)⁻¹ := by
      rw [← mul_inv, hsq]
    rw [hc_conj, hcdef, ← Complex.ofReal_mul, hreal2]
  -- ## the `L²` data of the two vectors
  have hθm : MemLp θ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
    have h := (memLp_modes ℓ hℓ).2.2
    simpa [hθdef] using h
  have hpair' : ∫ x, (starRingEnd ℂ) (e x) * θ x = (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ) := by
    simpa [hθdef] using hpair
  have hint_e2 : Integrable (fun x => ‖e x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
  have hint_θ2 : Integrable (fun x => ‖θ x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hθm.aestronglyMeasurable).mp hθm
  have hint_ee : Integrable (fun x => (starRingEnd ℂ) (e x) * e x) volume := by
    have h1 : Integrable (fun x => (((‖e x‖ ^ 2 : ℝ)) : ℂ)) volume := hint_e2.ofReal
    exact h1.congr
      (Filter.Eventually.of_forall fun x => (conj_mul_self_eq_ofReal_normSq (e x)).symm)
  have hint_θθ : Integrable (fun x => (starRingEnd ℂ) (θ x) * θ x) volume := by
    have h1 : Integrable (fun x => (((‖θ x‖ ^ 2 : ℝ)) : ℂ)) volume := hint_θ2.ofReal
    exact h1.congr
      (Filter.Eventually.of_forall fun x => (conj_mul_self_eq_ofReal_normSq (θ x)).symm)
  have hint_eθ : Integrable (fun x => (starRingEnd ℂ) (e x) * θ x) volume := by
    have h : Integrable (fun x => (star e) x * θ x) volume := he.star.integrable_mul hθm
    exact h.congr (Filter.Eventually.of_forall fun x => by
      show (star e) x * θ x = (starRingEnd ℂ) (e x) * θ x
      rw [Pi.star_apply]
      rfl)
  have hint_θe : Integrable (fun x => (starRingEnd ℂ) (θ x) * e x) volume := by
    have h : Integrable (fun x => (star θ) x * e x) volume := hθm.star.integrable_mul he
    exact h.congr (Filter.Eventually.of_forall fun x => by
      show (star θ) x * e x = (starRingEnd ℂ) (θ x) * e x
      rw [Pi.star_apply]
      rfl)
  have he_sq : ∫ x, ‖e x‖ ^ 2 = 1 := by
    have h1 : ∫ x, (((‖e x‖ ^ 2 : ℝ)) : ℂ) = 1 :=
      (integral_congr_ae
          (Filter.Eventually.of_forall fun x => (conj_mul_self_eq_ofReal_normSq (e x)).symm)).trans horth
    have h3 : ((∫ x, ‖e x‖ ^ 2 : ℝ) : ℂ) = ∫ x, (((‖e x‖ ^ 2 : ℝ)) : ℂ) :=
      (Complex.ofRealCLM.integral_comp_comm hint_e2).symm
    have h2 : ((∫ x, ‖e x‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [h3, h1]
      exact Complex.ofReal_one.symm
    exact Complex.ofReal_injective h2
  have hθ_sq : ∫ x, ‖θ x‖ ^ 2 = ℓ ^ 3 := by
    have h := Work.BoseB4.realIP_thetaFun_thetaFun Work.BoseK15.corpusBox hℓ
    rw [Work.BoseB4.BoxData.realIP_apply] at h
    rw [← hθdef] at h
    simpa only [re_conj_mul_self] using h
  have hθc : ∫ x, (starRingEnd ℂ) (θ x) * θ x = ((ℓ ^ 3 : ℝ) : ℂ) := by
    have h1 : ∫ x, (starRingEnd ℂ) (θ x) * θ x = ∫ x, (((‖θ x‖ ^ 2 : ℝ)) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => conj_mul_self_eq_ofReal_normSq (θ x))
    have h2 : ∫ x, (((‖θ x‖ ^ 2 : ℝ)) : ℂ) = ((∫ x, ‖θ x‖ ^ 2 : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hint_θ2
    rw [h1, h2, hθ_sq]
  have hfm : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
    have h : MemLp (fun x => e x - c * θ x) 2 volume := he.sub (hθm.const_mul c)
    simpa [hfdef] using h
  have hint_fe : Integrable (fun x => (starRingEnd ℂ) (f x) * e x) volume := by
    have h : Integrable (fun x => (star f) x * e x) volume := hfm.star.integrable_mul he
    exact h.congr (Filter.Eventually.of_forall fun x => by
      show (star f) x * e x = (starRingEnd ℂ) (f x) * e x
      rw [Pi.star_apply]
      rfl)
  have hint_fθ : Integrable (fun x => (starRingEnd ℂ) (f x) * θ x) volume := by
    have h : Integrable (fun x => (star f) x * θ x) volume := hfm.star.integrable_mul hθm
    exact h.congr (Filter.Eventually.of_forall fun x => by
      show (star f) x * θ x = (starRingEnd ℂ) (f x) * θ x
      rw [Pi.star_apply]
      rfl)
  have hint_ff : Integrable (fun x => (starRingEnd ℂ) (f x) * f x) volume := by
    have h : Integrable (fun x => (star f) x * f x) volume := hfm.star.integrable_mul hfm
    exact h.congr (Filter.Eventually.of_forall fun x => by
      show (star f) x * f x = (starRingEnd ℂ) (f x) * f x
      rw [Pi.star_apply]
      rfl)
  -- ## the two vanishing pairings of `f`
  have hA : ∫ x, (starRingEnd ℂ) (f x) * e x = 0 := by
    have hpt : ∀ x, (starRingEnd ℂ) (f x) * e x
        = (starRingEnd ℂ) (e x) * e x - (starRingEnd ℂ) c * ((starRingEnd ℂ) (θ x) * e x) := by
      intro x
      simp only [hfdef]
      rw [map_sub, map_mul]
      ring
    have hconjθe : ∫ x, (starRingEnd ℂ) (θ x) * e x
        = (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (e x) * θ x) := by
      have h := integral_conj (μ := volume) (f := fun x => (starRingEnd ℂ) (e x) * θ x)
      simpa [mul_comm] using h
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub hint_ee (hint_θe.const_mul ((starRingEnd ℂ) c)), integral_const_mul,
      horth, hconjθe, hpair', ← map_mul, hc_mul_a, map_one]
    ring
  have hB : ∫ x, (starRingEnd ℂ) (f x) * θ x = 0 := by
    have hpt : ∀ x, (starRingEnd ℂ) (f x) * θ x
        = (starRingEnd ℂ) (e x) * θ x - (starRingEnd ℂ) c * ((starRingEnd ℂ) (θ x) * θ x) := by
      intro x
      simp only [hfdef]
      rw [map_sub, map_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub hint_eθ (hint_θθ.const_mul ((starRingEnd ℂ) c)), integral_const_mul,
      hpair', hθc, hc_conj, hc_mul_l3]
    ring
  have hC : ∫ x, (starRingEnd ℂ) (f x) * f x = 0 := by
    have hpt : ∀ x, (starRingEnd ℂ) (f x) * f x
        = (starRingEnd ℂ) (f x) * e x - c * ((starRingEnd ℂ) (f x) * θ x) := by
      intro x
      simp only [hfdef]
      rw [map_sub, map_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub hint_fe (hint_fθ.const_mul c), integral_const_mul, hA, hB]
    ring
  -- ## `f` vanishes a.e.
  have hnorm : ∫ x, ‖f x‖ ^ 2 = 0 := by
    have hre1 : (∫ x, (starRingEnd ℂ) (f x) * f x).re
        = ∫ x, ((starRingEnd ℂ) (f x) * f x).re :=
      (Complex.reCLM.integral_comp_comm hint_ff).symm
    have hre2 : ∫ x, ((starRingEnd ℂ) (f x) * f x).re = ∫ x, ‖f x‖ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => re_conj_mul_self (f x))
    rw [← hre2, ← hre1, hC]
    simp
  refine ⟨c, hc_scalar, ?_⟩
  have hf0 : f =ᵐ[volume] 0 := by
    have hzero : (fun x => ‖f x‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        ((memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable).mp hfm)).mp hnorm
    filter_upwards [hzero] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  filter_upwards [hf0] with x hx
  simpa [hfdef, hθdef, sub_eq_zero] using hx

end Work.BoseBoxFock
