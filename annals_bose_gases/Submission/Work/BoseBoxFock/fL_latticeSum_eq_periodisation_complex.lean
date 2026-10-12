import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.fL_latticeSum_eq_periodisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.fL_latticeSum_eq_periodisation_complex`

The **complex (phasor) form** of the periodisation (Poisson summation) identity for the
low-momentum symbol `fc.f(‖·‖/κ)`: for `κ, ℓ > 0` and every shift `w ∈ ℝ³`,

    Σ'_m f(‖k_m‖/κ)·e^{i⟪k_m, w⟫}
      = ℓ³ · Σ'_d (2π)⁻³ ∫_p e^{i⟪p, w + ℓ·v_d⟫}·f(‖p‖/κ) dp ,

where `k_m = (2π/ℓ)·latVec m` is the sampling (dual) lattice of `(2π/ℓ)ℤ³` and `v_d = latVec d`.

This is the sibling `Work.BoseBoxFock.fL_latticeSum_eq_periodisation` with the cosine replaced by
the full phasor `e^{iθ}`: it is the *complex* (not merely real-part) form of Poisson summation,
which the real statement cannot supply (the real statement loses the sine part).

## Proof

The argument is the one already carried out inside the sibling proof, stopped one step earlier:
the complex identity `key` of that file — obtained from Poisson summation on `ℤ³`
(`Work.BoseBoxFock.poissonEuclid3Summable`) applied to the position-space test function

    h x = symb fc κ (c·x)·e^{i⟪c·x, w⟫},      c = 2π/ℓ ,

with the sample computation `Work.BoseBoxFock.sample_scaled_lowCut` — *is* the wanted statement,
up to reading `symb fc κ p = ((fc.f (‖p‖/κ) : ℝ) : ℂ)` and `c⁻³ = ℓ³(2π)⁻³`.  The real part of
`key` is what the sibling file uses; here we keep the whole complex identity.

The auxiliary lemmas `symb`, `symb_apply`, `contDiff_symb`, `hasCompactSupport_symb`,
`norm_symb_le_one`, `fl_norm_exp_I`, `invT`, `norm_invT_le` are reused from the imported sibling
module.
-/

open MeasureTheory

namespace Work.BoseBoxFock

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem fL_latticeSum_eq_periodisation_complex (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (w : EuclideanSpace ℝ (Fin 3)) :
    (∑' m : Fin 3 → ℤ,
        ((fc.f (‖(2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m‖ / κ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) w : ℂ)))
      = (ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : EuclideanSpace ℝ (Fin 3),
              Complex.exp (Complex.I * (inner ℝ p (w + ℓ • Work.BoseBoxFock.latVec d) : ℂ)) *
                ((fc.f (‖p‖ / κ) : ℝ) : ℂ)) := by
  classical
  set c : ℝ := 2 * Real.pi / ℓ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hF0d : ContDiff ℝ (⊤ : ℕ∞) (symb fc κ) := contDiff_symb fc hκ
  have hF0s : HasCompactSupport (symb fc κ) := hasCompactSupport_symb fc hκ
  -- the position-space test function
  set h : E3 → ℂ := fun x => symb fc κ (c • x) *
    Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ)) with hhdef
  -- ## continuity
  have h_cont : Continuous h := by
    rw [hhdef]
    refine (hF0d.continuous.comp (continuous_const_smul c)).mul ?_
    fun_prop
  -- ## vanishing beyond the support of the symbol
  have h_zero_of_gt : ∀ x : E3, 2 * κ / c < ‖x‖ → h x = 0 := by
    intro x hx
    rw [hhdef]
    have h2 : 2 * κ < ‖c • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hcpos.le]
      rw [div_lt_iff₀ hcpos] at hx
      linarith
    have h3 : (2 : ℝ) ≤ ‖c • x‖ / κ := by rw [le_div_iff₀ hκ]; linarith
    show symb fc κ (c • x) * Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ)) = 0
    rw [symb_apply, fc.zero _ h3, Complex.ofReal_zero, zero_mul]
  -- ## compact support
  have h_cs : HasCompactSupport h := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * κ / c))
      (isCompact_closedBall 0 (2 * κ / c)) ?_
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    rw [not_le] at hlt
    exact hx (h_zero_of_gt x hlt)
  -- ## norm bound
  have h_le_one : ∀ x : E3, ‖h x‖ ≤ 1 := by
    intro x
    rw [hhdef]
    calc ‖symb fc κ (c • x) * Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ))‖
        = ‖symb fc κ (c • x)‖ *
            ‖Complex.exp (Complex.I * (inner ℝ (c • x) w : ℂ))‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_symb_le_one fc κ (c • x))
          (le_of_eq (fl_norm_exp_I (inner ℝ (c • x) w))) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, ‖h x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℤ)) := by
    refine ⟨(1 + 2 * κ / c) ^ 4, by positivity, fun x => ?_⟩
    rcases le_or_gt ‖x‖ (2 * κ / c) with hx | hx
    · have h1 : ‖h x‖ ≤ 1 := h_le_one x
      have h2 : (1 : ℝ) ≤ (1 + 2 * κ / c) ^ 4 * (1 + ‖x‖) ^ (-(4 : ℤ)) := by
        rw [zpow_neg]
        have hb : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
        have h4 : (1 + ‖x‖) ^ 4 ≤ (1 + 2 * κ / c) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 4
        calc (1 : ℝ) = (1 + ‖x‖) ^ 4 * ((1 + ‖x‖) ^ 4)⁻¹ := by
              rw [mul_inv_cancel₀ (ne_of_gt hb)]
          _ ≤ (1 + 2 * κ / c) ^ 4 * ((1 + ‖x‖) ^ 4)⁻¹ :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
    · rw [h_zero_of_gt x hx, norm_zero]
      positivity
  have h_dec : ∃ C : ℝ, ∀ x : E3, (1 + ‖x‖) ^ 4 * ‖h x‖ ≤ C := by
    obtain ⟨C, hC0, hC⟩ := h_bound
    refine ⟨C, fun x => ?_⟩
    have h2 : (1 + ‖x‖) ^ 4 * (C * (1 + ‖x‖) ^ (-(4 : ℤ))) = C := by
      rw [zpow_neg]
      field_simp
    calc (1 + ‖x‖) ^ 4 * ‖h x‖
        ≤ (1 + ‖x‖) ^ 4 * (C * (1 + ‖x‖) ^ (-(4 : ℤ))) :=
          mul_le_mul_of_nonneg_left (hC x) (by positivity)
      _ = C := h2
  -- ## the sample computation
  have hsample : ∀ m : Fin 3 → ℤ,
      (∫ x : E3, h x * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))))
        = ((c ^ 3 : ℝ) : ℂ)⁻¹ * invT (symb fc κ) (w - ℓ • latVec m) := by
    intro m
    have hstep := sample_scaled_lowCut fc hκ hℓ w m
    have h1 : (∫ x : E3, h x *
          Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))))
        = ∫ x : E3, ((fc.f (‖(2 * Real.pi / ℓ) • x‖ / κ) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • x) w : ℂ))
            * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hhdef, symb_apply, hcdef]
    have h2 : ((((2 * Real.pi / ℓ) ^ 3 : ℝ) : ℂ))⁻¹ * (∫ p : E3, ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ p (w - ℓ • latVec m) : ℂ)))
        = ((c ^ 3 : ℝ) : ℂ)⁻¹ * invT (symb fc κ) (w - ℓ • latVec m) := by
      rw [hcdef]
      rfl
    rw [h1, hstep, h2]
  -- ## summability of the shifted inverse transforms
  obtain ⟨C₀, hC₀0, hC₀⟩ := norm_invT_le (symb fc κ) hF0d hF0s
  have hsum_pos : Summable (fun d : Fin 3 → ℤ => invT (symb fc κ) (w + ℓ • latVec d)) :=
    summable_shift_latVec hC₀0 hC₀ hℓ w
  have hsum_neg : Summable (fun m : Fin 3 → ℤ => invT (symb fc κ) (w - ℓ • latVec m)) := by
    refine ((Equiv.summable_iff (Equiv.neg (Fin 3 → ℤ))).mpr hsum_pos).congr fun m => ?_
    simp only [Function.comp_apply, Equiv.neg_apply, latVec_neg, smul_neg]
    abel
  have hsum_samples : Summable (fun m : Fin 3 → ℤ =>
      ∫ x : E3, h x * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ)))) :=
    (hsum_neg.mul_left (((c ^ 3 : ℝ)) : ℂ)⁻¹).congr fun m => (hsample m).symm
  -- ## Poisson summation
  have hpois0 := poissonEuclid3Summable h h_cont h_dec hsum_samples
  have hpois : (∑' m : Fin 3 → ℤ, h (latVec m))
      = ∑' m : Fin 3 → ℤ, ∫ x : E3,
          h x * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x (latVec m) : ℂ))) :=
    hpois0
  -- ## reindexing
  have hreindex : (∑' m : Fin 3 → ℤ, invT (symb fc κ) (w - ℓ • latVec m))
      = ∑' d : Fin 3 → ℤ, invT (symb fc κ) (w + ℓ • latVec d) := by
    rw [← (Equiv.neg (Fin 3 → ℤ)).tsum_eq
      (fun m : Fin 3 → ℤ => invT (symb fc κ) (w - ℓ • latVec m))]
    refine tsum_congr fun m => ?_
    simp only [Equiv.neg_apply, latVec_neg, smul_neg]
    abel
  -- ## the complex identity
  have key : (∑' m : Fin 3 → ℤ, h (latVec m))
      = ((c ^ 3 : ℝ) : ℂ)⁻¹ * ∑' d : Fin 3 → ℤ, invT (symb fc κ) (w + ℓ • latVec d) := by
    rw [hpois, tsum_congr hsample, tsum_mul_left, hreindex]
  -- ## the target's left-hand side is the lattice sum of `h`
  have hLHS : (∑' m : Fin 3 → ℤ,
        ((fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) w : ℂ)))
      = ∑' m : Fin 3 → ℤ, h (latVec m) :=
    tsum_congr (fun m => by simp only [hhdef, symb_apply, hcdef])
  -- ## the target's right-hand side is the shifted inverse transform
  have hRHS : (∑' d : Fin 3 → ℤ,
          ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : E3,
              Complex.exp (Complex.I * (inner ℝ p (w + ℓ • latVec d) : ℂ)) *
                ((fc.f (‖p‖ / κ) : ℝ) : ℂ))
      = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ)
          * ∑' d : Fin 3 → ℤ, invT (symb fc κ) (w + ℓ • latVec d) := by
    rw [tsum_mul_left]
    congr 1
    refine tsum_congr fun d => ?_
    rw [invT_apply]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [symb_apply]
      rw [mul_comm])
  -- ## the algebra of the prefactors: `c⁻³ = ℓ³(2π)⁻³`
  have hcinv3 : ((c ^ 3 : ℝ))⁻¹ = ℓ ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ := by
    rw [hcdef]
    field_simp
  have hcoef : ((((c ^ 3 : ℝ)) : ℂ))⁻¹
      = (ℓ : ℂ) ^ 3 * ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, hcinv3]
    push_cast
    ring
  rw [hLHS, hRHS, key, hcoef]
  ring

end

end Work.BoseBoxFock
