import Mathlib
import Submission.Work.FIArea7.angTrunc_le
import Submission.Work.FITop4.Defs4
import Submission.Work.FIArea7.theta_sum_Icc_int_le

namespace Work.FIArea7

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-! ### Complexification of a real `C²` mollifier

The Fourier-coefficient bound `angFourierCoeff_le` (*FI* (16.26)) is stated for a complex-valued
weight `w` with the complex derivative bound `‖w^{(j)}‖ ≤ Cθ^{-j}`.  Here we transport the real
bounds of the angular mollifier `q` (with `|q^{(j)}| ≤ c_j θ^{-j}`, `j ≤ 2`) to its
complexification `t ↦ ((q t : ℝ) : ℂ)`. -/

private lemma deriv_ofReal_comp_c (q : ℝ → ℝ) (hq : Differentiable ℝ q) :
    deriv (fun t => ((q t : ℝ) : ℂ)) = fun t => ((deriv q t : ℝ) : ℂ) := by
  funext t
  exact ((hq t).hasDerivAt.ofReal_comp).deriv

private lemma iteratedDeriv_one_ofReal_c (q : ℝ → ℝ) (hq : Differentiable ℝ q) :
    iteratedDeriv 1 (fun t => ((q t : ℝ) : ℂ)) = fun t => ((deriv q t : ℝ) : ℂ) := by
  rw [iteratedDeriv_one]
  exact deriv_ofReal_comp_c q hq

private lemma iteratedDeriv_two_ofReal_c (q : ℝ → ℝ) (hq : Differentiable ℝ q)
    (hd : Differentiable ℝ (deriv q)) :
    iteratedDeriv 2 (fun t => ((q t : ℝ) : ℂ)) = fun t => ((iteratedDeriv 2 q t : ℝ) : ℂ) := by
  have h : iteratedDeriv 2 (fun t => ((q t : ℝ) : ℂ))
      = deriv (fun t => ((deriv q t : ℝ) : ℂ)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one_ofReal_c q hq]
  rw [h, deriv_ofReal_comp_c (deriv q) hd]
  have h2 : iteratedDeriv 2 q = deriv (deriv q) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]

/-- **The `L¹`-bound on the Fourier coefficients of the angular mollifier** (the "`Σ_ℓ |ĉ(ℓ)| ≤ C`"
step of `AREA7_ROUTE_LEAD.md` §2.2, used in the §17 character transport): the sum of the absolute
values of the Fourier coefficients `Work.FIArea7.angFourierCoeff` of the complexification of a
mollifier `q` of width `≍ θ`, over the frequencies `|ℓ| ≤ L`, is bounded by an absolute constant,
uniformly in `q`, `θ ≤ 1` and `L`.

This is `Σ_{|ℓ|≤L} |q̂(ℓ)| ≪ Σ_{|ℓ|≤L} θ/(1+θ²ℓ²) ≤ 1 + π`, the first inequality being the
pointwise bound (16.26) `angFourierCoeff_le` and the second the elementary estimate
`theta_sum_Icc_int_le`. -/
theorem angFourierCoeff_l1_le :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (q : ℝ → ℝ) (θ : ℝ) (L : ℕ),
      0 < θ → θ ≤ 1 → ContDiff ℝ 2 q →
      (∀ α, 0 ≤ q α ∧ q α ≤ 1) →
      (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
      (∀ j : ℕ, j ≤ 2 → ∀ α : ℝ,
        |iteratedDeriv j q α| ≤ Work.FITop4.cMoll j * θ ^ (-(j : ℝ))) →
      ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
        ‖Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ‖ ≤ C1 := by
  obtain ⟨C', hC'pos, hC'⟩ := angFourierCoeff_le (Work.FITop4.cMoll 2) (Work.FITop4.cMoll_pos 2)
  refine ⟨C' * (1 + Real.pi), mul_pos hC'pos (by linarith [Real.pi_pos]), ?_⟩
  intro q θ L hθ hθ1 hq hbdd hsupp hder
  have hdiff : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hdiff1 : Differentiable ℝ (deriv q) := by
    simpa [iteratedDeriv_one] using ContDiff.differentiable_iteratedDeriv' 1 hq
  have hw_cont : ContDiff ℝ 2 (fun t : ℝ => ((q t : ℝ) : ℂ)) := by
    have h := (ContinuousLinearMap.contDiff Complex.ofRealCLM (n := 2)).comp hq
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using h
  have hw_bd : ∀ t : ℝ, ‖((q t : ℝ) : ℂ)‖ ≤ 1 := by
    intro t
    rw [Complex.norm_real, Real.norm_of_nonneg (hbdd t).1]
    exact (hbdd t).2
  have hw_supp : ∀ t : ℝ, ((q t : ℝ) : ℂ) ≠ 0 → 0 ≤ t ∧ t ≤ 2 * Real.pi * θ := by
    intro t ht
    exact hsupp t (fun h0 => ht (by simp [h0]))
  have hder2 : ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
      |iteratedDeriv j q t| ≤ Work.FITop4.cMoll 2 * θ ^ (-(j : ℝ)) := by
    intro j hj t
    have h := hder j hj t
    have hc : Work.FITop4.cMoll j ≤ Work.FITop4.cMoll 2 := by
      unfold Work.FITop4.cMoll
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      omega
    have hp : (0 : ℝ) ≤ θ ^ (-(j : ℝ)) := Real.rpow_nonneg hθ.le _
    exact le_trans h (mul_le_mul_of_nonneg_right hc hp)
  have hw_der : ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => ((q t : ℝ) : ℂ)) t‖
        ≤ Work.FITop4.cMoll 2 * θ ^ (-(j : ℝ)) := by
    intro j hj t
    have hid : ‖iteratedDeriv j (fun t : ℝ => ((q t : ℝ) : ℂ)) t‖ = |iteratedDeriv j q t| := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rw [iteratedDeriv_zero, iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs]
      · rw [iteratedDeriv_one_ofReal_c q hdiff, iteratedDeriv_one, Complex.norm_real,
          Real.norm_eq_abs]
      · rw [iteratedDeriv_two_ofReal_c q hdiff hdiff1, Complex.norm_real, Real.norm_eq_abs]
    rw [hid]
    exact hder2 j hj t
  have hcoeff : ∀ ℓ : ℤ, ‖angFourierCoeff (fun t : ℝ => ((q t : ℝ) : ℂ)) ℓ‖
      ≤ C' * (θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2)) := by
    intro ℓ
    have h := hC' (fun t : ℝ => ((q t : ℝ) : ℂ)) θ ℓ hθ hθ1 hw_cont hw_bd hw_supp hw_der
    refine h.trans (le_of_eq ?_)
    ring
  calc ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L, ‖angFourierCoeff (fun t : ℝ => ((q t : ℝ) : ℂ)) ℓ‖
      ≤ ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L, C' * (θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2)) :=
        Finset.sum_le_sum (fun ℓ _ => hcoeff ℓ)
    _ = C' * ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L, θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ C' * (1 + Real.pi) :=
        mul_le_mul_of_nonneg_left (theta_sum_Icc_int_le θ hθ hθ1 L) hC'pos.le

end

end Work.FIArea7
