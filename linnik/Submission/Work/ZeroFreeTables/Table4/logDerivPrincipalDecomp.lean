import Mathlib

namespace Work.ZeroFreeTables.Table4

open Filter
open scoped Topology

/-- For a natural number `p > 1` and `1 < Re z`, the Euler factor `1 - p ^ (-z)` is nonzero. -/
private lemma one_sub_cpow_neg_ne_zero {p : ℕ} (hp : 1 < p) {z : ℂ} (hz : 1 < z.re) :
    (1 : ℂ) - (p : ℂ) ^ (-z) ≠ 0 := by
  have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp)
  have hpR1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlt : (p : ℝ) ^ (-(z.re)) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos hpR0]
    exact Or.inl ⟨hpR1, by linarith⟩
  have hnorm : ‖(p : ℂ) ^ (-z)‖ = (p : ℝ) ^ (-(z.re)) := by
    rw [← Complex.ofReal_natCast p, Complex.norm_cpow_eq_rpow_re_of_pos hpR0 (-z), Complex.neg_re]
  intro h
  have hx : (p : ℂ) ^ (-z) = 1 := (sub_eq_zero.mp h).symm
  have h1 : ‖(p : ℂ) ^ (-z)‖ = 1 := by rw [hx]; simp
  rw [hnorm] at h1
  linarith

/-- For a natural number `p > 1` and `1 < Re z`, we have `p ^ z ≠ 1`. -/
private lemma cpow_nat_ne_one {p : ℕ} (hp : 1 < p) {z : ℂ} (hz : 1 < z.re) :
    (p : ℂ) ^ z ≠ 1 := by
  have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp)
  have hpR1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hgt : 1 < (p : ℝ) ^ (z.re) := by
    rw [Real.one_lt_rpow_iff_of_pos hpR0]
    exact Or.inl ⟨hpR1, by linarith⟩
  have hnorm : ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ (z.re) := by
    rw [← Complex.ofReal_natCast p, Complex.norm_cpow_eq_rpow_re_of_pos hpR0 z]
  intro h
  have h1 : ‖(p : ℂ) ^ z‖ = 1 := by rw [h]; simp
  rw [hnorm] at h1
  linarith

/-- The logarithmic derivative of the Euler factor `1 - p ^ (-z)` is `log p / (p ^ z - 1)` on
the half plane `1 < Re z`. -/
private lemma logDeriv_one_sub_cpow_neg {p : ℕ} (hp : 1 < p) {z : ℂ} (hz : 1 < z.re) :
    logDeriv (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) z
      = (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1) := by
  have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpR0)
  have hx0 : (1 : ℂ) - (p : ℂ) ^ (-z) ≠ 0 := one_sub_cpow_neg_ne_zero hp hz
  have hy0 : (p : ℂ) ^ z - 1 ≠ 0 := sub_ne_zero.mpr (cpow_nat_ne_one hp hz)
  have hd : HasDerivAt (fun w : ℂ => 1 - (p : ℂ) ^ (-w))
      (0 - ((p : ℂ) ^ (-z) * Complex.log (p : ℂ) * (-1))) z :=
    (hasDerivAt_const (x := z) (c := (1 : ℂ))).sub
      ((hasDerivAt_neg z).const_cpow (Or.inl hp0))
  rw [logDeriv_apply, hd.deriv, ← Complex.natCast_log (n := p)]
  have key : (p : ℂ) ^ (-z) * (p : ℂ) ^ z = 1 := by
    rw [mul_comm, ← Complex.cpow_add z (-z) hp0, add_neg_cancel, Complex.cpow_zero]
  rw [div_eq_div_iff hx0 hy0]
  linear_combination (Real.log (p : ℝ) : ℂ) * key

/-- The function `z ↦ p ^ z` is analytic in the whole plane. -/
private lemma analyticAt_cpow_const (p : ℕ) (hp : 1 < p) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (p : ℂ) ^ w) z := by
  have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpR0)
  have h : AnalyticAt ℂ (fun w : ℂ => Complex.exp (Complex.log (p : ℂ) * w)) z :=
    analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)
  simpa only [Complex.cpow_def_of_ne_zero hp0] using h

theorem logDerivPrincipalDecomp (q : ℕ) [NeZero q] (j : ℕ) (hj : j ≤ 2) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv j (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
      = iteratedDeriv j (logDeriv riemannZeta) s
        + iteratedDeriv j (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s := by
  have hmain : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      =ᶠ[𝓝 s] (fun z : ℂ => logDeriv riemannZeta z
        + ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) := by
    have hU : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    have hAB : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        =ᶠ[𝓝 z] (fun w : ℂ =>
          (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))) * riemannZeta w) := by
      have hUz : {w : ℂ | 1 < w.re} ∈ 𝓝 z :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
      filter_upwards [hUz] with w hw
      have hw1 : w ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
      exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hw1
    rw [(logDeriv_congr_nhds hAB).eq_of_nhds]
    have hPne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      exact one_sub_cpow_neg_ne_zero (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)) hz
    have hζne : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
    have hPdiff : DifferentiableAt ℂ
        (fun w : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))) z := by
      refine DifferentiableAt.fun_finsetProd (fun p hp => ?_)
      have hp1 : 1 < p := Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)
      have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp1)
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpR0)
      exact (differentiableAt_const (c := (1 : ℂ))).sub
        ((differentiableAt_id.neg).const_cpow (Or.inl hp0))
    have hζdiff : DifferentiableAt ℂ riemannZeta z := differentiableAt_riemannZeta hz1
    erw [logDeriv_mul z hPne hζne hPdiff hζdiff]
    have hprod : logDeriv (fun w : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))) z
        = ∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) z :=
      by
        have h :=
          logDeriv_prod (s := q.primeFactors) (f := fun (p : ℕ) (w : ℂ) => 1 - (p : ℂ) ^ (-w))
            (fun p hp =>
              one_sub_cpow_neg_ne_zero (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)) hz)
            (fun p hp => by
              have hp1 : 1 < p := Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)
              have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp1)
              have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpR0)
              exact (differentiableAt_const (c := (1 : ℂ))).sub
                ((differentiableAt_id.neg).const_cpow (Or.inl hp0)))
        simp only [Finset.prod_fn] at h
        exact h
    rw [hprod]
    rw [Finset.sum_congr rfl (fun p hp =>
      logDeriv_one_sub_cpow_neg (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)) hz)]
    ring
  have hζcd : ContDiffAt ℂ (↑j) (logDeriv riemannZeta) s := by
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hzan : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs1)
    have hA : AnalyticAt ℂ (logDeriv riemannZeta) s := by
      simpa only [logDeriv] using hzan.deriv.div hzan (riemannZeta_ne_zero_of_one_lt_re hs)
    exact hA.contDiffAt
  have hTcd : ContDiffAt ℂ (↑j) (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s := by
    refine AnalyticAt.contDiffAt ?_
    refine Finset.analyticAt_fun_sum (f := fun (p : ℕ) (z : ℂ) =>
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) q.primeFactors (fun p hp => ?_)
    have hp1 : 1 < p := Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)
    have hden : AnalyticAt ℂ (fun z : ℂ => (p : ℂ) ^ z - 1) s :=
      (analyticAt_cpow_const p hp1 s).sub analyticAt_const
    have hne : ((p : ℂ) ^ s - 1) ≠ 0 := sub_ne_zero.mpr (cpow_nat_ne_one hp1 hs)
    exact analyticAt_const.div hden hne
  rw [← iteratedDeriv_add hζcd hTcd]
  exact (hmain.iteratedDeriv j).eq_of_nhds

end Work.ZeroFreeTables.Table4
