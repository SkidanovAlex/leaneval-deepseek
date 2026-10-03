import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

/-!
# `Work.KMTAreas.A4.invWeyl_one`

A "degree-one inverse Weyl" statement: for a *linear* integer polynomial `Q` (`Q.natDegree = 1`)
and a frequency `ξ`, if the exponential sum

  `∑_{n ∈ [a,b]} c · e^{2πi ξ Q(n)}`

is as large as `ε · #([a,b])`, then the frequency `ξ · (leading coefficient of Q)` is within
`C ε^{-K} / #([a,b])` of a rational with denominator `q ≤ C ε^{-K}`.

For a linear `Q` the sum is a geometric progression, so the classical first-derivative test
(a Dirichlet kernel bound) applies and the statement is true with the *strong* conclusion
`q = 1`: the distance of `ξ · lc(Q)` to the nearest integer is at most `1/(2 ε L)`, hence
`≤ C ε^{-1}/L`.  The constants `C = 4`, `K = 1` work.

The Dirichlet-kernel input is the already-formalised `Submission.UnitCircle.geom_sum_bound_of_intDist_pos`
(with `Submission.VanDerCorput.intDist` the distance to the nearest integer).
-/

namespace Work.KMTAreas.A4

/-- Evaluation of a degree-one integer polynomial: `Q(n) = Q.coeff 1 * n + Q.coeff 0`. -/
private lemma eval_eq_of_natDegree_one (Q : Polynomial ℤ) (hQ : Q.natDegree = 1) (n : ℤ) :
    Q.eval n = Q.coeff 1 * n + Q.coeff 0 := by
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hQ.le]
  simp [Polynomial.eval_add, Polynomial.eval_mul]

theorem invWeyl_one :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (Q : Polynomial ℤ) (hQ : Q.natDegree = 1) (ξ : ℝ) (c : ℂ) (hc : ‖c‖ = 1)
        (a b : ℤ) (ε : ℝ),
        a ≤ b → 0 < ε → ε ≤ 1 →
        ε * (((b - a : ℤ) : ℝ) + 1) ≤
          ‖∑ n ∈ Finset.Icc a b, c * Complex.exp (2 * Real.pi * Complex.I * (ξ * ((Q.eval n : ℤ) : ℝ)))‖ →
        ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * ε ^ (-K) ∧
          ∃ m : ℤ, |(q : ℝ) * ξ * ((Q.coeff 1 : ℤ) : ℝ) - (m : ℝ)|
            ≤ C * ε ^ (-K) / (((b - a : ℤ) : ℝ) + 1) ^ 1 := by
  refine ⟨4, 1, by norm_num, by norm_num, ?_⟩
  intro Q hQ ξ c hc a b ε hab hε0 hε1 hmain
  -- ## Notation
  set A : ℝ := ((Q.coeff 1 : ℤ) : ℝ) with hA
  set B : ℝ := ((Q.coeff 0 : ℤ) : ℝ) with hB
  set θ : ℝ := ξ * A with hθ
  set ζ : ℂ := Complex.exp (↑(2 * Real.pi * θ) * Complex.I) with hζ
  set N : ℕ := (b + 1 - a).toNat with hN
  -- ## The length of the interval
  have hN1 : 1 ≤ N := by rw [hN]; omega
  have hNL : (N : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by
    rw [hN]
    have hNz : (((b + 1 - a).toNat : ℤ)) = b + 1 - a := Int.toNat_of_nonneg (by omega)
    have h1 : (((b + 1 - a).toNat : ℝ)) = ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast hNz
    have h2 : ((b + 1 - a : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by push_cast; ring
    exact h1.trans h2
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  -- ## The linear phase sum identity
  have hlin : ∀ n : ℤ, Q.eval n = Q.coeff 1 * n + Q.coeff 0 := fun n =>
    eval_eq_of_natDegree_one Q hQ n
  have hC0norm : ‖c * Complex.exp (↑(2 * Real.pi * (ξ * B)) * Complex.I)‖ = 1 := by
    rw [norm_mul, hc, one_mul]
    exact Complex.norm_exp_ofReal_mul_I _
  have hterm : ∀ n : ℤ, c * Complex.exp (2 * Real.pi * Complex.I * (ξ * ((Q.eval n : ℤ) : ℝ)))
      = (c * Complex.exp (↑(2 * Real.pi * (ξ * B)) * Complex.I)) * ζ ^ n := by
    intro n
    have hreal : 2 * Real.pi * (ξ * ((Q.eval n : ℤ) : ℝ))
        = 2 * Real.pi * (ξ * B) + (n : ℝ) * (2 * Real.pi * θ) := by
      rw [hlin n]
      push_cast
      rw [hθ, ← hA, ← hB]
      ring
    have hL : 2 * Real.pi * Complex.I * (ξ * ((Q.eval n : ℤ) : ℝ))
        = (↑(2 * Real.pi * (ξ * ((Q.eval n : ℤ) : ℝ))) : ℂ) * Complex.I := by
      push_cast
      ring
    have hcx : (↑(2 * Real.pi * (ξ * ((Q.eval n : ℤ) : ℝ))) : ℂ) * Complex.I
        = ↑(2 * Real.pi * (ξ * B)) * Complex.I + (n : ℂ) * (↑(2 * Real.pi * θ) * Complex.I) := by
      rw [hreal]
      push_cast
      ring
    rw [hL, hcx, Complex.exp_add, Complex.exp_int_mul, ← hζ]
    ring
  have hζnorm : ‖ζ‖ = 1 := by
    rw [hζ]
    exact Complex.norm_exp_ofReal_mul_I _
  have hζa : ‖ζ ^ a‖ = 1 := by
    rw [norm_zpow, hζnorm, one_zpow]
  have hS1 : (∑ n ∈ Finset.Icc a b,
        c * Complex.exp (2 * Real.pi * Complex.I * (ξ * ((Q.eval n : ℤ) : ℝ))))
      = (c * Complex.exp (↑(2 * Real.pi * (ξ * B)) * Complex.I))
        * (∑ n ∈ Finset.Icc a b, ζ ^ n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hterm n
  have hS2 : (∑ n ∈ Finset.Icc a b, ζ ^ n) = ζ ^ a * ∑ k ∈ Finset.range N, ζ ^ (k : ℤ) := by
    rw [hN, Int.Icc_eq_finset_map, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hemb : (Nat.castEmbedding.trans (addLeftEmbedding a)) k = a + (k : ℤ) := rfl
    rw [hemb, zpow_add₀ (Complex.exp_ne_zero _)]
  have hS3 : (∑ k ∈ Finset.range N, ζ ^ (k : ℤ))
      = ∑ k ∈ Finset.range N, Submission.VanDerCorput.linPhase θ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [zpow_natCast, hζ]
    exact (Submission.VanDerCorput.linPhase_eq_pow θ k).symm
  have hnorm : ‖∑ n ∈ Finset.Icc a b,
        c * Complex.exp (2 * Real.pi * Complex.I * (ξ * ((Q.eval n : ℤ) : ℝ)))‖
      = ‖∑ k ∈ Finset.range N, Submission.VanDerCorput.linPhase θ k‖ := by
    rw [hS1, norm_mul, hC0norm, one_mul, hS2, norm_mul, hζa, one_mul, hS3]
  -- ## The distance to the nearest integer
  have hd0 : 0 ≤ Submission.VanDerCorput.intDist θ := Submission.VanDerCorput.intDist_nonneg θ
  have hlt : Submission.VanDerCorput.intDist θ < (4 * ε ^ ((-1 : ℝ))) / (N : ℝ) := by
    rcases eq_or_lt_of_le hd0 with hz | hpos
    · rw [← hz, Real.rpow_neg_one]
      positivity
    · -- here the exponential sum is large, hence `θ` is close to an integer
      have hγ : ε * (N : ℝ) ≤ (1 / 2) / Submission.VanDerCorput.intDist θ := by
        have h1 : ε * (N : ℝ)
            ≤ ‖∑ k ∈ Finset.range N, Submission.VanDerCorput.linPhase θ k‖ := by
          rw [hNL, ← hnorm]
          exact hmain
        exact h1.trans (Submission.UnitCircle.geom_sum_bound_of_intDist_pos (α := θ) hpos)
      have hdN : 0 < ε * (N : ℝ) := mul_pos hε0 hNpos
      have hstrict : Submission.VanDerCorput.intDist θ < 4 / (ε * (N : ℝ)) := by
        rw [lt_div_iff₀ hdN]
        have h2 := hγ
        rw [le_div_iff₀ hpos] at h2
        nlinarith [h2]
      have hconv : 4 / (ε * (N : ℝ)) = (4 * ε ^ ((-1 : ℝ))) / (N : ℝ) := by
        rw [Real.rpow_neg_one]
        field_simp
      rwa [hconv] at hstrict
  -- ## Conclusion
  have hδ0 : 0 ≤ (4 * ε ^ ((-1 : ℝ))) / (N : ℝ) := by
    rw [Real.rpow_neg_one]
    positivity
  obtain ⟨m, hm⟩ :=
    (Submission.IntDistRegion.intDist_lt_iff_exists_int (x := θ)
      (δ := (4 * ε ^ ((-1 : ℝ))) / (N : ℝ)) hδ0).mp hlt
  refine ⟨1, le_rfl, ?_, m, ?_⟩
  · rw [Real.rpow_neg_one]
    have hεinv : 1 ≤ ε⁻¹ := by rw [one_le_inv₀ hε0]; exact hε1
    push_cast
    linarith
  · have hm' : |ξ * A - (m : ℝ)| ≤ (4 * ε ^ ((-1 : ℝ))) / (N : ℝ) := by
      simpa [hθ] using hm.le
    have hq : ((1 : ℕ) : ℝ) * ξ * A = ξ * A := by norm_num
    have hL2 : ((((b - a : ℤ) : ℝ) + 1) ^ (1 : ℕ)) = (N : ℝ) := by
      rw [hNL, pow_one]
    rw [hq, hL2]
    exact hm'

end Work.KMTAreas.A4
