import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetSeriesDefs
import Submission.Work.LinnikAreas.BGTZ.DetSeriesAux
import Submission.Work.LinnikAreas.BGTZ.DetectorSeries

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

variable {q : ℕ} [NeZero q]

/-- **The detector series is the `multSer`-sum over the lcm's of the sieve weights.**
Writing `(Σ_{d|n}θ_d)² = Σ_{d,e ≤ R}θ_dθ_e[gcd(d,e) | n]` and interchanging the (finite) sum
over `(d,e)` with the series turns the detector series into `Σ_{d,e}θ_dθ_e · multSer (lcm d e)`. -/
theorem detSeries_eq_sum_multSer (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {R : ℕ} {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, detCoeff χ₁ χ θw n / (n : ℂ) ^ s)
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          (θw d : ℂ) * (θw e : ℂ) * multSer χ₁ χ (Nat.lcm d e) s := by
  have hterm : ∀ n : ℕ, detCoeff χ₁ χ θw n / (n : ℂ) ^ s
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
          * ((if Nat.lcm d e ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [detCoeff_eq_mul_sq]
      simp [cfun_zero]
    · have hexp := divisors_sum_sq_eq_lcm_sum hθ hn
      have hSq : (((∑ d ∈ n.divisors, θw d : ℝ)) : ℂ) ^ 2
          = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
              (θw d : ℂ) * (θw e : ℂ) * (if Nat.lcm d e ∣ n then (1 : ℂ) else 0) := by
        rw [← Complex.ofReal_pow, hexp, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases h : Nat.lcm d e ∣ n <;> simp [h]
      rw [detCoeff_eq_mul_sq, hSq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun (d : ℕ) _ => ?_
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun (e : ℕ) _ => ?_
      by_cases h : Nat.lcm d e ∣ n <;> simp [h, div_eq_mul_inv] <;> ring
  rw [tsum_congr hterm]
  rw [tsum_sum_finset (Finset.Icc 1 R)
    (fun d n => ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
      * ((if Nat.lcm d e ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s))
    (fun d _ => summable_sum fun e _ => (summable_indicator_cfun_div χ₁ χ hχ₁ (Nat.lcm d e) hs).mul_left _)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [tsum_sum_finset (Finset.Icc 1 R)
    (fun e n => (θw d : ℂ) * (θw e : ℂ)
      * ((if Nat.lcm d e ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s))
    (fun e _ => (summable_indicator_cfun_div χ₁ χ hχ₁ (Nat.lcm d e) hs).mul_left _)]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [tsum_mul_left]
  rfl

theorem DetSeriesIdentity {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {R : ℕ} {θw : ℕ → ℝ} (hθ : Work.LinnikAreas.BGTZ.IsSieveWeight R θw) {s : ℂ}
    (hs : 1 < s.re) :
    (∑' n : ℕ, Work.LinnikAreas.BGTZ.detCoeff χ₁ χ θw n / (n : ℂ) ^ s)
      = DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s
          * Work.LinnikAreas.BGTZ.sieveG χ₁ R θw s χ := by
  rw [detSeries_eq_sum_multSer χ₁ χ hχ₁ hθ hs]
  have hstep : ∀ d ∈ Finset.Icc 1 R, ∀ e ∈ Finset.Icc 1 R,
      (θw d : ℂ) * (θw e : ℂ) * multSer χ₁ χ (Nat.lcm d e) s
        = (θw d : ℂ) * (θw e : ℂ) * (DirichletCharacter.LFunction χ s
            * DirichletCharacter.LFunction (χ * χ₁) s
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p) := by
    intro d _ e _
    by_cases hde : θw d * θw e = 0
    · have hdeC : (θw d : ℂ) * (θw e : ℂ) = 0 := by
        rw [← Complex.ofReal_mul, hde, Complex.ofReal_zero]
      rw [hdeC, zero_mul, zero_mul]
    · have hd0 : θw d ≠ 0 := fun h => hde (by rw [h, zero_mul])
      have he0 : θw e ≠ 0 := fun h => hde (by rw [h, mul_zero])
      have hsd : Squarefree d := by
        by_contra h
        exact hd0 (hθ.2.1 d (Or.inl h))
      have hse : Squarefree e := by
        by_contra h
        exact he0 (hθ.2.1 e (Or.inl h))
      rw [multSer_squarefree χ₁ χ hχ₁ hs (Nat.lcm d e) (squarefree_lcm hsd hse)]
  rw [Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => hstep d hd e he]
  rw [sieveG]
  rw [show (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
        * (DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p))
      = DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s
        * (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring]

end

end Work.LinnikAreas.BGTZ
