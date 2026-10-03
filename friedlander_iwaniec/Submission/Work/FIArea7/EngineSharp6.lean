/-
# `Submission.Work.FIArea7.EngineSharp6` — the sharpened (17.10) engine error

The landed child `Work.FIArea7.WUniOmega6Pull6_sub_Moll_le` gives

  `‖WUniOmega6Pull6 − WUniOmega6Pull6Moll‖ ≤ C·(N³/K + N)·(log N)⁶`,

which is **too large** to close the contract's target `X⁻¹N²log N` for any admissible `K`: the
term `N³/K` is `≫ N²/X` unless `K ≳ NX`, and that choice destroys the (17.13) split
(`NOTES.md` §58.3).  The loss is *not* in the pointwise mollification error — `norm_term_le`
already carries the sharp `4(1+θ)N/(K|Δ|)` — but in the final step, where the `(b,e)`-weight is
replaced by the uniform bound `pairW ≤ 2` (`quadruple_le`, `pairW_le_two`) and then `(Σ‖βz‖)²` is
estimated by `#supp · Σ‖βz‖²`.

This file keeps the `1/|Δ|` to the end: after the `(b,e)`-sums are interchanged with the pair sums
the error reads

  `8(1+θ)N/K · Σ_{z₁,z₂} pairW(uniB Pa, X, |Δ(z₁,z₂)|)·‖β z₁‖·‖β z₂‖`,

and the sharp input `pairW_pair_sum_le` bounds that double sum by `O((X+1)·log³N)·Σ_z‖β z‖²` —
*no* factor `#supp` and *no* factor `N`.  Hence

  `‖WUniOmega6Pull6 − WUniOmega6Pull6Moll‖ ≤ C·(X+1)·(N+1)·(log N)^4·(Σ_z‖β z‖²)/K`,

which with `K = X³(log N)²⁰` and `Σ_z‖β z‖² ≤ 1000(θN+√N+1)(log N)³` is `≪ θN²log^{-10}/X²`, far
below the target `X⁻¹N²log N`.

`WUniOmega6Pull6_sub_Moll_le_sharp_aux` is stated with the pair-sum bound as an explicit
hypothesis so that this file builds before that child lands; the instantiation is the one-liner
`WUniOmega6Pull6_sub_Moll_le_sharp` (in `EngineSharp6b.lean`).
-/
import Mathlib
import Submission.Work.FIArea7.WUniOmega6Pull6_sub_Moll_le
import Submission.Work.FIArea7.quadruple_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Two elementary norms -/

/-- `‖(μ(b)/b : ℂ)‖ ≤ 1/b`. -/
private lemma norm_moebius_weight_le' (b : ℕ) :
    ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖ ≤ 1 / (b : ℝ) := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ))]
  rcases eq_or_lt_of_le (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ)) with h | h
  · rw [← h]; simp
  · rw [div_le_div_iff₀ h h, one_mul]
    have h1 : |((ArithmeticFunction.moebius b : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
    nlinarith [h1, h]

/-- The pair sum at fixed `(b,e)`: the `(z₁,z₂)`-sum of the mollifier error with its sharp
pointwise bound. -/
private lemma moll_termsum_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {K : ℕ} (hK : 1 ≤ K)
    {b e : ℕ} (hb : 1 ≤ b) (he : 1 ≤ e) :
    ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          Pull6Base β b e z1 z2
            * (((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
      ≤ (4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
          * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
                  * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun z1 _ => norm_sum_le _ _)) ?_
  refine le_trans (Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ =>
    norm_term_le hβ hK hb he z1 z2))) ?_
  apply le_of_eq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z2 _ => ?_)
  rw [div_eq_mul_inv, mul_inv]
  ring


/-! ## 1. The engine error with the `1/|Δ|` kept -/

/-- **The sharpened mollifier error.**  Takes the sharp pair-sum bound as a hypothesis. -/
theorem WUniOmega6Pull6_sub_Moll_le_sharp_aux
    (hpw : ∃ C : ℝ, 0 < C ∧ ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
        {β : GaussianInt → ℂ} (X : ℕ), Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X →
        (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            pairW (uniB Pa) X (Work.FIPlan.absDelta z1 z2) * ‖β z1‖ * ‖β z2‖)
          ≤ C * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3
              * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {z0 : GaussianInt}
        {β : GaussianInt → ℂ}, Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X →
        ∀ K : ℕ, 1 ≤ K →
        ‖WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Moll Pa X β K‖
          ≤ C * ((X : ℝ) + 1) * (Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 4
              * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) / (K : ℝ) := by
  obtain ⟨Cp, hCppos, hpw⟩ := hpw
  refine ⟨16 * Cp, by positivity, ?_⟩
  intro Pa X φ z0 β hβ hX K hK
  set E2 : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2 with hE2def
  have hE2nn : (0 : ℝ) ≤ E2 := by rw [hE2def]; positivity
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.N + 2) := one_le_log_add_two hN1
  have hnum : (0 : ℝ) ≤ 4 * ((1 + Pa.θ) * Pa.N) := by nlinarith [Pa.hθ0, hNpos]
  have hfac : (0 : ℝ) ≤ 4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ) := div_nonneg hnum hKpos.le
  -- auxiliary: the `(b,e)`-sum with the Möbius weight and the divisibility indicator
  -- step 1: pull out the Möbius weights and the per-`(b,e)` pair bound
  have hA : ‖∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
        (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
          * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Pull6Base β b e z1 z2
                  * (((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
      ≤ (4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
          * (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
              ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (1 / (b : ℝ))
                    * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
                    * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun b _ => norm_sum_le _ _)) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun b hb => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun e he => ?_)
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    rw [norm_mul]
    have hstep := mul_le_mul (norm_moebius_weight_le' b) (moll_termsum_le hβ hK hb1 he1)
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (b : ℝ))
    calc ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖
          * ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Pull6Base β b e z1 z2
                  * (((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
        ≤ (1 / (b : ℝ)) * ((4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
            * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
                    * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)) := hstep
      _ = (4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
            * ((1 / (b : ℝ)) * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
                    * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)) := by ring
      _ = (4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
            * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (1 / (b : ℝ))
                    * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
                    * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro z1 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro z2 _
          ring
  -- step 2: interchange the `(b,e)`-sums with the pair sums, giving `pairW`
  have hsw : (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
              ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (1 / (b : ℝ))
                    * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
                    * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)
      = ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            pairW (uniB Pa) X (Work.FIPlan.absDelta z1 z2) * ‖β z1‖ * ‖β z2‖ := by
    rw [sum_comm_four (Finset.Icc 1 (uniB Pa)) (Finset.Icc 1 X)
      (Work.FIPlan.gBox (Work.FITop.radN Pa))
      (fun b e z1 z2 => (1 / (b : ℝ))
        * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
        * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)]
    apply Finset.sum_congr rfl; intro z1 _
    apply Finset.sum_congr rfl; intro z2 _
    simp only [pairW, ← Finset.sum_mul]
  have hpw' := hpw (Pa := Pa) (φ := φ) (z0 := z0) (β := β) X hβ hX
  rw [Pull6_sub_Moll_eq Pa X β K, norm_mul]
  rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
  have hbig : ‖∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
        (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
          * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Pull6Base β b e z1 z2
                  * (((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
      ≤ (4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
          * (Cp * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 * E2) := by
    refine le_trans hA ?_
    rw [hsw, hE2def]
    exact mul_le_mul_of_nonneg_left hpw' hfac
  have hlead : (0 : ℝ) ≤ Cp * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 * E2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hCppos.le (by positivity)) (by positivity)) hE2nn
  calc 2 * ‖∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
        (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
          * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Pull6Base β b e z1 z2
                  * (((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) - logFac6Series z1 z2 K)‖
      ≤ 2 * ((4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
          * (Cp * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 * E2)) :=
        mul_le_mul_of_nonneg_left hbig (by norm_num)
    _ ≤ 16 * Cp * ((X : ℝ) + 1) * (Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 4 * E2
          / (K : ℝ) := by
        have h1θ : 1 + Pa.θ ≤ 2 := by linarith
        have hlog3 : (Real.log (Pa.N + 2)) ^ 3 ≤ (Real.log (Pa.N + 2)) ^ 4 :=
          pow_le_pow_right₀ hlog1 (by norm_num : (3:ℕ) ≤ 4)
        have h2 : 2 * (4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
            ≤ 16 * (Pa.N + 1) / (K : ℝ) := by
          have hnum2 : 2 * (4 * ((1 + Pa.θ) * Pa.N)) ≤ 16 * (Pa.N + 1) := by nlinarith
          rw [show 2 * (4 * ((1 + Pa.θ) * Pa.N) / (K:ℝ))
              = (2 * (4 * ((1 + Pa.θ) * Pa.N))) / (K:ℝ) from by ring]
          exact div_le_div_of_nonneg_right hnum2 hKpos.le
        have h3 : (Real.log (Pa.N + 2)) ^ 3 * E2 ≤ (Real.log (Pa.N + 2)) ^ 4 * E2 :=
          mul_le_mul_of_nonneg_right hlog3 hE2nn
        have hCX : (0 : ℝ) ≤ Cp * ((X : ℝ) + 1) :=
          mul_nonneg hCppos.le (by positivity)
        calc 2 * ((4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ))
              * (Cp * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 * E2))
            = (2 * (4 * ((1 + Pa.θ) * Pa.N) / (K : ℝ)))
                * (Cp * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 * E2) := by ring
          _ ≤ (16 * (Pa.N + 1) / (K : ℝ))
                * (Cp * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 3 * E2) :=
              mul_le_mul_of_nonneg_right h2 hlead
          _ ≤ (16 * (Pa.N + 1) / (K : ℝ))
                * (Cp * ((X : ℝ) + 1) * (Real.log (Pa.N + 2)) ^ 4 * E2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [h3, hCX]
          _ = 16 * Cp * ((X : ℝ) + 1) * (Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 4 * E2
                / (K : ℝ) := by ring
    _ = 16 * Cp * ((X : ℝ) + 1) * (Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 4
          * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) / (K : ℝ) := by
        rw [hE2def]

end

end Work.FIArea7
