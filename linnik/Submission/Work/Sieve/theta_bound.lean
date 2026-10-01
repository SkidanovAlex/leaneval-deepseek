import Mathlib
import Submission.Work.LinnikAreas.Sieve.Defs
import Submission.Work.Sieve.gFun_theory
import Submission.Work.Sieve.sieve_weight_ineq

namespace Work.Sieve

open scoped BigOperators

/-- **Graham's Lemma 9.6, first part: the Selberg weights are bounded by one.**

For a real character `χ₁` mod `q` (`χ₁ ^ 2 = 1`), `R` and `d` arbitrary, the Selberg weights
`Work.LinnikAreas.Sieve.thetaFun χ₁ R d` (BGTZ arXiv:2410.06082 (2.6) = Graham's thesis §9,
`θ_d = μ(d)h(d)/(V(R)g(d)) Σ_{r ≤ R/d, (r,d)=1} μ²(r)/g(r)`, with `V(R) = Σ_{ℓ ≤ R} μ²(ℓ)/g(ℓ)`)
satisfy `|θ_d| ≤ 1`.

Route: for squarefree `d`, `h(d)/g(d) = ∏_{p|d}(1 + 1/g(p)) = Σ_{m|d} μ²(m)/g(m)`, so
`h(d) V_d(R/d)/g(d) = Σ_{r ≤ R/d, (r,d)=1} Σ_{m|d} μ²(rm)/g(rm)` is a sub-sum of
`V(R) = Σ_{n ≤ R} μ²(n)/g(n)` (the map `(r,m) ↦ rm` is injective into squarefree `n ≤ R`); hence
`|θ_d| ≤ 1`.  For `μ(d) = 0` (i.e. `d` not squarefree) `θ_d = 0`, and `R = 0` or `d > R` give
`θ_d = 0` by the empty `Icc`.  The only side conditions are `g(n) > 0` and `1/g(n) ≥ 0`, both from
`a(n) ≥ 0`. -/
theorem theta_bound {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (R d : ℕ) :
    |Work.LinnikAreas.Sieve.thetaFun χ₁ R d| ≤ 1 := by
  obtain ⟨hchar, hgpos, hhfun, hgfun, hgfunpos, hgmul, hVpos⟩ := gFun_theory χ₁ hreal
  by_cases hsq : Squarefree d
  · by_cases hbig : R / d = 0
    · have : Work.LinnikAreas.Sieve.thetaFun χ₁ R d = 0 := by
        rw [Work.LinnikAreas.Sieve.thetaFun, hbig]
        simp
      rw [this]; norm_num
    · have hd0 : d ≠ 0 := hsq.ne_zero
      have hdpos : 0 < R / d := Nat.pos_of_ne_zero hbig
      have hR1 : 1 ≤ R := le_trans hdpos (Nat.div_le_self R d)
      have hV : 0 < Work.LinnikAreas.Sieve.VFun χ₁ R := hVpos R hR1
      set y : ℕ → ℝ := fun n => (Work.LinnikAreas.Sieve.gFun χ₁ n)⁻¹ with hy
      have hyapp : ∀ n, y n = (Work.LinnikAreas.Sieve.gFun χ₁ n)⁻¹ := fun n => by rw [hy]
      set Sd : ℝ := ∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
          (if Squarefree r then (1:ℝ) else 0) / Work.LinnikAreas.Sieve.gFun χ₁ r with hSd
      have hy_p : ∀ p, p.Prime → y p = (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ := by
        intro p hp
        rw [hyapp]
        have hgp : Work.LinnikAreas.Sieve.gFun χ₁ p = Work.LinnikAreas.Sieve.gPrime χ₁ p := by
          rw [hgfun p hp.squarefree, hp.primeFactors]
          simp
        rw [hgp]
      have hprod : (∏ p ∈ d.primeFactors, (1 + y p))
          = Work.LinnikAreas.Sieve.hFun χ₁ d / Work.LinnikAreas.Sieve.gFun χ₁ d := by
        have h1 : ∀ p ∈ d.primeFactors, (1 + y p)
            = Work.LinnikAreas.Sieve.hPrime χ₁ p / Work.LinnikAreas.Sieve.gPrime χ₁ p := by
          intro p hp
          have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
          rw [hy_p p hpp, Work.LinnikAreas.Sieve.hPrime]
          have hne : Work.LinnikAreas.Sieve.gPrime χ₁ p ≠ 0 := ne_of_gt (hgpos p hpp)
          field_simp
        rw [hhfun d hsq, hgfun d hsq]
        rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib]
      have hBnn : 0 ≤ Work.LinnikAreas.Sieve.hFun χ₁ d / Work.LinnikAreas.Sieve.gFun χ₁ d := by
        rw [← hprod]
        exact Finset.prod_nonneg (fun p hp => by
          have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
          have hy0 : 0 ≤ y p := by
            rw [hyapp]
            exact le_of_lt (inv_pos.mpr (hgfunpos p hpp.squarefree))
          linarith)
      have hSnn : 0 ≤ Sd := by
        rw [hSd]
        refine Finset.sum_nonneg (fun r _ => ?_)
        by_cases hrs : Squarefree r
        · simp only [hrs, if_true]
          exact div_nonneg zero_le_one (le_of_lt (hgfunpos r hrs))
        · simp [hrs]
      have hSdeq : Sd = ∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
          (if Squarefree r then (1:ℝ) else 0) * y r := by
        rw [hSd]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [div_eq_mul_inv, hyapp]
      have hVeq : Work.LinnikAreas.Sieve.VFun χ₁ R
          = ∑ n ∈ Finset.Icc 1 R, (if Squarefree n then (1:ℝ) else 0) * y n := by
        rw [Work.LinnikAreas.Sieve.VFun]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [div_eq_mul_inv, hyapp]
      have hy_nonneg : ∀ n, Squarefree n → 0 ≤ y n := by
        intro n hn
        rw [hyapp]
        exact le_of_lt (inv_pos.mpr (hgfunpos n hn))
      have hy_mul : ∀ m n, Squarefree m → Squarefree n → Nat.Coprime m n →
          y (m * n) = y m * y n := by
        intro m n hm hn hmn
        rw [hyapp, hyapp, hyapp, hgmul m n hm hn hmn, mul_inv, mul_comm]
      have hBS : (Work.LinnikAreas.Sieve.hFun χ₁ d / Work.LinnikAreas.Sieve.gFun χ₁ d) * Sd
          ≤ Work.LinnikAreas.Sieve.VFun χ₁ R := by
        calc (Work.LinnikAreas.Sieve.hFun χ₁ d / Work.LinnikAreas.Sieve.gFun χ₁ d) * Sd
            = (∏ p ∈ d.primeFactors, (1 + y p)) * Sd := by rw [hprod]
          _ = (∑ r ∈ (Finset.Icc 1 (R / d)).filter (fun r => Nat.Coprime r d),
                  (if Squarefree r then (1:ℝ) else 0) * y r)
                * (∏ p ∈ d.primeFactors, (1 + y p)) := by
                rw [hSdeq]; exact mul_comm _ _
          _ ≤ ∑ n ∈ Finset.Icc 1 R, (if Squarefree n then (1:ℝ) else 0) * y n :=
                sieve_weight_ineq y hy_mul hy_nonneg R d hd0 hsq
          _ = Work.LinnikAreas.Sieve.VFun χ₁ R := hVeq.symm
      have hid : Work.LinnikAreas.Sieve.thetaFun χ₁ R d
          = (ArithmeticFunction.moebius d : ℝ)
              * (Work.LinnikAreas.Sieve.hFun χ₁ d / Work.LinnikAreas.Sieve.gFun χ₁ d) * Sd
              / Work.LinnikAreas.Sieve.VFun χ₁ R := by
        rw [Work.LinnikAreas.Sieve.thetaFun, hSd]
        ring_nf
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
        push_cast
        rw [abs_pow]
        simp
      rw [hid]
      rw [abs_div, abs_mul, abs_mul, hmu, abs_of_nonneg hBnn, abs_of_nonneg hSnn,
          abs_of_pos hV, one_mul, div_le_one hV]
      exact hBS
  · have hμ0 : (ArithmeticFunction.moebius d : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      norm_num
    rw [Work.LinnikAreas.Sieve.thetaFun, hμ0]
    simp

end Work.Sieve
