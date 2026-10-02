import Mathlib
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le

namespace Work.LinnikAreas

/-- **Zero sum at a real point `β ∈ (0,1)`.**

For a non-trivial primitive Dirichlet character `χ mod N`, a real point `σ` with `1 < σ` at which
the logarithmic derivative of the completed `L`-function `Λ = Λ(·,χ)` satisfies
`Re (Λ'/Λ)(σ) ≤ B`, and a real zero `β ∈ (0,1)` of `Λ`, the multiplicity of `β` satisfies

`ord(Λ,β)/(σ - β) ≤ B + log N + ½log 2 + 3/2`.

This is the Hadamard partial-fraction identity

`Λ'/Λ(s) = Σ_ρ (1/(s-ρ) + 1/ρ) + Const`

evaluated on the two vertical lines `Re = σ` and `Re = -1` (both zero-free), together with the
one-sided estimate `-Re (Λ'/Λ)(-1) ≤ log N + 3/2` (`completedLogDeriv_neg_one_re_tight`) and the
fact that every non-real zero of `Λ` lies in the critical strip `0 < Re < 1`
(`zerosInStrip`), so that each kernel term is non-negative and the single term at `β` may be
retained. -/
theorem siegelZeroSimple_zeroSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) (β σ B : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hz : DirichletCharacter.completedLFunction χ (β : ℂ) = 0) (hσ1 : 1 < σ) (hσ2 : σ ≤ 5 / 4)
    (hB : (logDeriv (DirichletCharacter.completedLFunction χ) (σ : ℂ)).re ≤ B) :
    (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β : ℂ) : ℝ) / (σ - β)
      ≤ B + Real.log N + Real.log 2 / 2 + 3 / 2 := by
  classical
  set R : ℝ := 1 with hR
  set K : ℂ → ℝ := fun u => (σ - u.re) / ((σ - u.re) ^ 2 + u.im ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + u.im ^ 2) with hK
  set D : ℂ → ℝ := fun u =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u with hD
  set m : ℕ := analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β : ℂ) with hm
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) := fun z _ => hdiff.analyticAt z
  -- `β` lies in the ball of radius `1`
  have hβnorm : ‖(β : ℂ)‖ = β := by
    have h2 : ‖(β : ℂ)‖ ^ 2 = β ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    nlinarith [norm_nonneg (β : ℂ), hβ0]
  have hβmem : (β : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hR]
    rw [hβnorm]
    linarith
  -- the hypothesis rewritten in the shape expected by the partial-fraction bound
  have hB' : (logDeriv (DirichletCharacter.completedLFunction χ)
      ((σ : ℂ) + Complex.I * ((0 : ℝ) : ℂ))).re ≤ B := by
    simpa using hB
  have hbase := Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le
    χ hχ hχprim 0 σ B (le_of_lt hσ1) hB' R
  -- the kernel of the partial-fraction bound is `K`
  have heq : (∑ᶠ u : ℂ, D u)
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
          ((σ - u.re) / ((σ - u.re) ^ 2 + (0 - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (0 - u.im) ^ 2)) := by
    refine finsum_congr (fun u => ?_)
    simp only [hD, hK]
    ring
  have hsumbound : (∑ᶠ u : ℂ, D u) ≤ B + Real.log N + Real.log 2 / 2 + 3 / 2 := by
    rw [heq]
    have hrhs : B + Real.log (N : ℝ) + 1 / 2 * Real.log (2 + |(0 : ℝ)|) + 3 / 2
        = B + Real.log (N : ℝ) + Real.log 2 / 2 + 3 / 2 := by
      rw [abs_zero, add_zero]
      ring
    rw [hrhs] at hbase
    exact hbase
  -- finiteness of the support of `D`
  have hsuppfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R) u)).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall 0 R) (V := Metric.closedBall 0 R) han.meromorphicOn
      (by rw [hR]; exact isCompact_closedBall (0 : ℂ) 1) (le_refl _)
  have hfin : Function.HasFiniteSupport D := by
    refine hsuppfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [hD]; simp [h0])
  -- non-negativity of every summand
  have hnn : ∀ u : ℂ, 0 ≤ D u := by
    intro u
    by_cases hz0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R) u = 0
    · rw [hD]; simp [hz0]
    · have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
        by_contra h
        exact hz0 (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
      have hcast : (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) ≠ 0 := by
        rw [← Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han huB]
        exact hz0
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 :=
        fun h0 => hcast (by simp [h0])
      have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
      have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
      have hdnn : (0 : ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R) u : ℤ) : ℝ) := by
        rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han huB]
        exact_mod_cast Nat.cast_nonneg
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u)
      have hKnn : 0 ≤ K u := by
        rw [hK]
        have h1 : 0 < σ - u.re := by linarith [hstrip.2, hσ1]
        have h2 : 0 < 1 + u.re := by linarith [hstrip.1]
        have hd1 : 0 < (σ - u.re) ^ 2 + u.im ^ 2 := by
          nlinarith [sq_nonneg u.im, mul_pos h1 h1]
        have hd2 : 0 < (1 + u.re) ^ 2 + u.im ^ 2 := by
          nlinarith [sq_nonneg u.im, mul_pos h2 h2]
        exact add_nonneg (div_nonneg h1.le hd1.le) (div_nonneg h2.le hd2.le)
      rw [hD]
      exact mul_nonneg hdnn hKnn
  have key : D (β : ℂ) ≤ ∑ᶠ u : ℂ, D u := single_le_finsum (β : ℂ) hfin hnn
  -- the value of `D` at `β`
  have hDβ : D (β : ℂ) = (m : ℝ) * (1 / (σ - β) + 1 / (1 + β)) := by
    have hd : ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R) (β : ℂ) : ℤ) : ℝ) = (m : ℝ) := by
      rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hβmem]
      simp [hm]
    have hKβ : K (β : ℂ) = 1 / (σ - β) + 1 / (1 + β) := by
      rw [hK]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      have hσβ : (σ - β) ≠ 0 := by linarith
      have h1β : (1 + β) ≠ 0 := by linarith
      field_simp
      ring
    simp only [hD]
    rw [hd, hKβ]
  have hle : (m : ℝ) / (σ - β) ≤ D (β : ℂ) := by
    rw [hDβ, div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    have h1β : (0 : ℝ) < 1 + β := by linarith
    have hpos : (0 : ℝ) ≤ 1 / (1 + β) := by positivity
    linarith
  calc (m : ℝ) / (σ - β) ≤ D (β : ℂ) := hle
    _ ≤ ∑ᶠ u : ℂ, D u := key
    _ ≤ B + Real.log N + Real.log 2 / 2 + 3 / 2 := hsumbound

end Work.LinnikAreas
