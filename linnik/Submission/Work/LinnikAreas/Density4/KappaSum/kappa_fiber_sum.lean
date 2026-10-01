import Mathlib
import Submission.Work.LinnikAreas.Density4.KappaDefs
import Submission.Work.LinnikAreas.Density4.KappaSum.kappa_divisors_identity

namespace Work.LinnikAreas.Density4.KappaSum

/-! ## The fibre/convolution identity for `κ`

This is the elementary rearrangement behind An's Lemmas 11/12: the sum over the
`d | n` with `(d, n/d) = 1` of `μ(d)²/(d κ(d)) · μ(n/d)/(n/d)` collapses to `μ(n)/κ(n)`.

The proof factors the summand as `(μ(n)/n) · (μ(d)/κ(d))`.  Indeed on a fibre the
two factors `d` and `n/d` are coprime, so `μ(d)² μ(n/d) = μ(d) μ(n)` (multiplicativity
of `μ`), and `d · (n/d) = n`.  It then remains to identify the resulting sum:
* if `n` is squarefree, `(d, n/d) = 1` holds for *every* divisor `d`, and the sum is the
  already proved `kappa_divisors_identity`;
* if not, `μ n = 0` kills the whole expression. -/

/-- Pure field rearrangement: `x²/(a k) · y/b = (x y/(a b)) · (x/k)`. -/
lemma kappa_fiber_term_id (a b k x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hk : k ≠ 0) :
    x^2 / (a * k) * y / b = (x * y / (a * b)) * (x / k) := by
  field_simp

/-- `κ` is positive (hence nonzero) on positive integers. -/
lemma kappaR_pos_of_one_le {n : ℕ} (hn : 1 ≤ n) : 0 < kappaR n := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hprod : 1 ≤ ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ)) := by
    apply Finset.one_le_prod₀
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have h2 := (Nat.mem_primeFactors.mp hp).1
      exact_mod_cast h2.two_le
    have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  calc (0 : ℝ) < (n : ℝ) := hn'
    _ = (n : ℝ) * 1 := (mul_one _).symm
    _ ≤ (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod hn'.le
    _ = kappaR n := rfl

theorem kappa_fiber_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)),
        ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
          ((ArithmeticFunction.moebius (n / d) : ℝ)) / ((n / d : ℕ) : ℝ))
      = (ArithmeticFunction.moebius n : ℝ) / kappaR n := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hkn : kappaR n ≠ 0 := ne_of_gt (kappaR_pos_of_one_le hn)
  -- Factor the fibred summand as `(μ n / n) * (μ d / κ d)`.
  have hsum : (∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)),
        ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
          ((ArithmeticFunction.moebius (n / d) : ℝ)) / ((n / d : ℕ) : ℝ))
      = ((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) *
        (∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)),
          (ArithmeticFunction.moebius d : ℝ) / kappaR d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hdmem, hcop⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
    have hde : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    have hcast : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by exact_mod_cast hde.symm
    -- multiplicativity of `μ` on the coprime fibre
    have hmu : (ArithmeticFunction.moebius n : ℝ) =
        (ArithmeticFunction.moebius d : ℝ) *
          (ArithmeticFunction.moebius (n / d) : ℝ) := by
      have h := (ArithmeticFunction.isMultiplicative_moebius.intCast (R := ℝ)).map_mul_of_coprime
        hcop
      rw [hde] at h
      exact h
    have ha : (d : ℝ) ≠ 0 := by positivity
    have hb : ((n / d : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
      positivity
    have hk : kappaR d ≠ 0 := ne_of_gt (kappaR_pos_of_one_le (by omega : 1 ≤ d))
    rw [kappa_fiber_term_id (a := (d : ℝ)) (b := ((n / d : ℕ) : ℝ)) (k := kappaR d)
          (x := (ArithmeticFunction.moebius d : ℝ))
          (y := (ArithmeticFunction.moebius (n / d) : ℝ)) ha hb hk]
    rw [← hmu, ← hcast]
  rw [hsum]
  by_cases hsf : Squarefree n
  · -- Squarefree `n`: every divisor is coprime to its cofactor.
    have hFeq : n.divisors.filter (fun d => Nat.Coprime d (n / d)) = n.divisors := by
      apply Finset.filter_true_of_mem
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hde : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have : Squarefree (d * (n / d)) := by rw [hde]; exact hsf
      exact Nat.coprime_of_squarefree_mul this
    rw [hFeq, kappa_divisors_identity n hn]
    field_simp
  · -- Non-squarefree `n`: `μ n = 0`.
    have hmu0 : (ArithmeticFunction.moebius n : ℝ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
    rw [hmu0]
    simp

end Work.LinnikAreas.Density4.KappaSum
