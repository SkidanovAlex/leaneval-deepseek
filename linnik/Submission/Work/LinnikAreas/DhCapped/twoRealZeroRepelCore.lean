import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.siegelZeroSimple_ldUpper
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le

open scoped BigOperators

namespace Work.LinnikAreas.DhCapped

/-- Summing a nonnegative, finitely supported `D : ℂ → ℝ` over two distinct points never exceeds
the full `finsum` of `D` over `ℂ`. -/
private lemma finsum_pair_le {D : ℂ → ℝ} (hfin : Function.HasFiniteSupport D)
    (hnn : ∀ u, 0 ≤ D u) {a b : ℂ} (hab : a ≠ b) :
    D a + D b ≤ ∑ᶠ u : ℂ, D u := by
  classical
  have hsub : ({a, b} : Finset ℂ) ⊆ insert a (insert b hfin.toFinset) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
    tauto
  have hstep : D a + D b ≤ ∑ u ∈ insert a (insert b hfin.toFinset), D u := by
    rw [← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i)
  refine le_trans hstep ?_
  rw [finsum_eq_sum_of_support_subset D (s := insert a (insert b hfin.toFinset)) ?_]
  intro u hu
  have hu' : u ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 hu
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu')

/-- **Two real zeros of `Λ = completedLFunction χ`, Hadamard/partial-fraction form.**

For a non-principal primitive character `χ mod N`, two *distinct* real zeros `β₀ ≠ β₂` of `Λ` in
`(0,1)`, and a real `σ` with `1 < σ ≤ 5/4` at which `Re (Λ'/Λ)(σ) ≤ B`, the Hadamard partial
fraction bound `Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le` (at `T = 0`,
radius `R = 1`) applied to the two points `β₀`, `β₂` gives

`1/(σ-β₀) + 1/(σ-β₂) ≤ B + log N + log 2/2 + 1/2`.

The `+3/2` of the Hadamard bound loses `1` because each of the two second kernel terms
`Re(1/(1+β_i)) = 1/(1+β_i)` is at least `1/2`. -/
private lemma twoRealZeroSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) (β₀ β₂ σ B : ℝ) (hβ₀ : 0 < β₀) (hβ₀1 : β₀ < 1)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hβne : β₂ ≠ β₀)
    (hz₀ : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β₀ : ℂ) ≠ 0)
    (hz₂ : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β₂ : ℂ) ≠ 0)
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 5 / 4)
    (hB : (logDeriv (DirichletCharacter.completedLFunction χ) (σ : ℂ)).re ≤ B) :
    1 / (σ - β₀) + 1 / (σ - β₂) ≤ B + Real.log (N : ℝ) + Real.log 2 / 2 + 1 / 2 := by
  classical
  set R : ℝ := 1 with hR
  set K : ℂ → ℝ := fun u => (σ - u.re) / ((σ - u.re) ^ 2 + u.im ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + u.im ^ 2) with hK
  set D : ℂ → ℝ := fun u =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u with hD
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) := fun z _ => hdiff.analyticAt z
  have hnorm : ∀ β : ℝ, 0 ≤ β → ‖(β : ℂ)‖ = β := by
    intro β hβ
    have h2 : ‖(β : ℂ)‖ ^ 2 = β ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg (β : ℂ), hβ]
  have hmem0 : (β₀ : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hR, hnorm β₀ hβ₀.le]
    linarith
  have hmem2 : (β₂ : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hR, hnorm β₂ hβ₂.le]
    linarith
  have hB' : (logDeriv (DirichletCharacter.completedLFunction χ)
      ((σ : ℂ) + Complex.I * ((0 : ℝ) : ℂ))).re ≤ B := by
    simpa using hB
  have hbase := Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le
    χ hχ hχprim 0 σ B (le_of_lt hσ1) hB' R
  have heq : (∑ᶠ u : ℂ, D u)
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
          ((σ - u.re) / ((σ - u.re) ^ 2 + (0 - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (0 - u.im) ^ 2)) := by
    refine finsum_congr (fun u => ?_)
    simp only [hD, hK]
    ring
  have hsumbound : (∑ᶠ u : ℂ, D u) ≤ B + Real.log (N : ℝ) + Real.log 2 / 2 + 3 / 2 := by
    rw [heq]
    have hrhs : B + Real.log (N : ℝ) + 1 / 2 * Real.log (2 + |(0 : ℝ)|) + 3 / 2
        = B + Real.log (N : ℝ) + Real.log 2 / 2 + 3 / 2 := by
      rw [abs_zero, add_zero]; ring
    rw [hrhs] at hbase
    exact hbase
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
  have hpair : D (β₀ : ℂ) + D (β₂ : ℂ) ≤ ∑ᶠ u : ℂ, D u :=
    finsum_pair_le hfin hnn (by intro h; exact hβne (by exact_mod_cast h.symm))
  have hDval : ∀ β : ℝ, 0 < β → β < 1 →
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β : ℂ) ≠ 0 →
      1 / (σ - β) + 1 / 2 ≤ D (β : ℂ) := by
    intro β hβ0 hβ1 hzβ
    have hmemβ : (β : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hR, hnorm β hβ0.le]
      linarith
    have hd : ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R) (β : ℂ) : ℤ) : ℝ) =
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β : ℂ) : ℝ) := by
      rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmemβ]
      simp
    have hKβ : K (β : ℂ) = 1 / (σ - β) + 1 / (1 + β) := by
      rw [hK]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      have hσβ : (σ - β) ≠ 0 := by linarith
      have h1β : (1 + β) ≠ 0 := by linarith
      field_simp
      ring
    have hDav : D (β : ℂ) =
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β : ℂ) : ℝ)
        * (1 / (σ - β) + 1 / (1 + β)) := by
      simp only [hD]
      rw [hd, hKβ]
    rw [hDav]
    have hm1 : (1 : ℝ) ≤
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β : ℂ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzβ
    have hb : (0 : ℝ) < 1 + β := by linarith
    have hhalf : (1 : ℝ) / 2 ≤ 1 / (1 + β) := one_div_le_one_div_of_le hb (by linarith)
    have hAB : 0 ≤ 1 / (σ - β) + 1 / (1 + β) := by
      have h1 : 0 < 1 / (σ - β) := div_pos one_pos (by linarith)
      have h2 : 0 < 1 / (1 + β) := div_pos one_pos hb
      linarith
    calc 1 / (σ - β) + 1 / 2 ≤ 1 / (σ - β) + 1 / (1 + β) := by linarith
      _ = 1 * (1 / (σ - β) + 1 / (1 + β)) := by ring
      _ ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) (β : ℂ) : ℝ)
            * (1 / (σ - β) + 1 / (1 + β)) := by
        apply mul_le_mul_of_nonneg_right hm1 hAB
  have h0 := hDval β₀ hβ₀ hβ₀1 hz₀
  have h2v := hDval β₂ hβ₂ hβ₂1 hz₂
  have hsum : 1 / (σ - β₀) + 1 / (σ - β₂) + 1 ≤ ∑ᶠ u : ℂ, D u := by
    linarith [h0, h2v, hpair]
  linarith [hsum, hsumbound]

/-- **Two real zeros of the same `L`-function repel each other** (Hadamard partial fraction form).

For a non-principal Dirichlet character `χ` mod `q` (`q ≥ 3`) with two *distinct* real zeros
`β₀ ≠ β₂`, the Hadamard partial-fraction bound
`Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le` evaluated at `T = 0`,
`σ₁ = 1 + √λ₀/log q` and `R = 2`, together with the log-derivative bound
`Work.LinnikAreas.siegelZeroSimple_ldUpper`, gives
`1/(σ₁-β₀) + 1/(σ₁-β₂) ≤ 1/(σ₁-1) + C + log N + log 2/2 + 1/2`, where `N = χ.conductor` and `C`
is an absolute constant.  The `+1/2` on the right is the `+3/2` of the Hadamard bound minus the
two `≥ 1/2` contributions of the second kernel term `Re(1/(1+ū))` at the two real zeros.

Proof notes.  `zeroMult χ · ≠ 0` makes `β₀, β₂` zeros of `Λ = completedLFunction χ.primitiveCharacter`
in `(0,1)` (`Commons…Linnik.completedL_zero_strip`), and `L(βᵢ,χ*) = 0`; the divisor of `Λ` is
non-negative and `K(u) = Re(1/(σ₁-u)) + Re(1/(1+ū)) ≥ 0` at zeros, so
`K(β₀) + K(β₂) ≤ ∑ᶠ u, divisor u * K u` (`single_le_finsum` / `Finset.sum_le_sum_of_subset_of_nonneg`
on the finite support).  Take `C := max C_ld 8` and split on `σ₁ ≤ 5/4`: in that case
`(logDeriv Λ σ₁).re ≤ 1/(σ₁-1) + C_ld` (`siegelZeroSimple_ldUpper`) and the Hadamard bound
`finsum_divisor_re_inv_sub_le χ* … 0 σ₁ (1/(σ₁-1)+C_ld) … 2` gives the claim after dropping
`1/(1+βᵢ) ≥ 1/2`; the `3/2` and the two `1/2` give the stated `+1/2`.  If `σ₁ > 5/4` then
`σ₁ - βᵢ > 1/4` and the conclusion is trivial for `C ≥ 8`. -/
theorem twoRealZeroRepelCore : ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 3 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
    ∀ β₀ β₂ : ℝ, Work.LinnikContract.zeroMult χ (β₀ : ℂ) ≠ 0 →
      Work.LinnikContract.zeroMult χ (β₂ : ℂ) ≠ 0 → β₂ ≠ β₀ →
      0 < Work.LinnikContract.lamOf q (β₀ : ℂ) →
      1 / ((1 + Real.sqrt (Work.LinnikContract.lamOf q (β₀ : ℂ)) / Real.log (q : ℝ)) - β₀)
        + 1 / ((1 + Real.sqrt (Work.LinnikContract.lamOf q (β₀ : ℂ)) / Real.log (q : ℝ)) - β₂)
        ≤ (Real.sqrt (Work.LinnikContract.lamOf q (β₀ : ℂ)) / Real.log (q : ℝ))⁻¹
          + C + Real.log ((χ.conductor : ℕ) : ℝ) + Real.log 2 / 2 + 1 / 2 := by
  obtain ⟨Cld, hCld⟩ := siegelZeroSimple_ldUpper
  refine ⟨max Cld 8, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (le_max_right _ _)
  · intro q hq hqne χ hcondne hχ β₀ β₂ hz₀ hz₂ hβne hlam0
    classical
    -- abbreviate `L = log q`, `lam0 = lamOf q β₀`, `σ = 1 + √lam0/L`
    set L : ℝ := Real.log (q : ℝ) with hL
    have hLpos : 0 < L := by
      rw [hL]
      exact Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    set lam0 : ℝ := Work.LinnikContract.lamOf q (β₀ : ℂ) with hlam0def
    have hlam0pos : 0 < lam0 := hlam0
    -- the primitive character inducing `χ`
    have hchine : χ.primitiveCharacter ≠ 1 := by
      intro h1
      refine hχ ?_
      rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
      exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
    have hchprim : χ.primitiveCharacter.IsPrimitive :=
      DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hz0p : analyticOrderNatAt
        (DirichletCharacter.completedLFunction χ.primitiveCharacter) (β₀ : ℂ) ≠ 0 := by
      simpa only [Work.LinnikContract.zeroMult] using hz₀
    have hz2p : analyticOrderNatAt
        (DirichletCharacter.completedLFunction χ.primitiveCharacter) (β₂ : ℂ) ≠ 0 := by
      simpa only [Work.LinnikContract.zeroMult] using hz₂
    have hL0 : DirichletCharacter.completedLFunction χ.primitiveCharacter (β₀ : ℂ) = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hz0p
    have hL2 : DirichletCharacter.completedLFunction χ.primitiveCharacter (β₂ : ℂ) = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hz2p
    have hstrip₀ : (0 : ℝ) < β₀ ∧ β₀ < 1 := by
      have h := Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter
        hchine hchprim hL0
      simpa using h
    have hstrip₂ : (0 : ℝ) < β₂ ∧ β₂ < 1 := by
      have h := Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter
        hchine hchprim hL2
      simpa using h
    set σ : ℝ := 1 + Real.sqrt lam0 / L with hσdef
    have hσgt1 : 1 < σ := by
      rw [hσdef]
      have h1 : 0 < Real.sqrt lam0 := Real.sqrt_pos.mpr hlam0pos
      have h2 : 0 < Real.sqrt lam0 / L := div_pos h1 hLpos
      linarith
    by_cases hσle : σ ≤ 5 / 4
    · -- main case: apply the Hadamard partial-fraction bound
      have hB : (logDeriv (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (σ : ℂ)).re ≤ 1 / (σ - 1) + Cld :=
        hCld χ.conductor χ.primitiveCharacter hchine σ hσgt1 hσle
      have hcore := twoRealZeroSum χ.primitiveCharacter hchine hchprim β₀ β₂ σ
        (1 / (σ - 1) + Cld) hstrip₀.1 hstrip₀.2 hstrip₂.1 hstrip₂.2 hβne hz0p hz2p hσgt1 hσle hB
      have hσ1eq : 1 / (σ - 1) = (Real.sqrt lam0 / L)⁻¹ := by
        rw [hσdef, add_sub_cancel_left, one_div]
      rw [← hσ1eq]
      linarith [hcore, le_max_left Cld 8]
    · -- σ > 5/4: both terms are < 4 and the right-hand side is ≥ 8
      push Not at hσle
      have hb₀ : 1 / (σ - β₀) ≤ 4 := by
        rw [div_le_iff₀ (by linarith [hstrip₀.2] : (0 : ℝ) < σ - β₀)]
        linarith [hstrip₀.2]
      have hb₂ : 1 / (σ - β₂) ≤ 4 := by
        rw [div_le_iff₀ (by linarith [hstrip₂.2] : (0 : ℝ) < σ - β₂)]
        linarith [hstrip₂.2]
      have hbig : (8 : ℝ) ≤ (Real.sqrt lam0 / L)⁻¹ + max Cld 8
          + Real.log ((χ.conductor : ℕ) : ℝ) + Real.log 2 / 2 + 1 / 2 := by
        have hlogN : 0 ≤ Real.log ((χ.conductor : ℕ) : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
        have hlamInv : 0 ≤ (Real.sqrt lam0 / L)⁻¹ :=
          inv_nonneg.mpr (div_nonneg (Real.sqrt_nonneg _) hLpos.le)
        have hlog2 : 0 ≤ Real.log 2 / 2 := by
          have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
        linarith [le_max_right Cld 8]
      linarith [hb₀, hb₂, hbig]

end Work.LinnikAreas.DhCapped
