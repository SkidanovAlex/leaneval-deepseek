import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.sumLogPrimesNotDvdLe
import Submission.Work.LinnikAreas.OtherCharRepel.localFactorLogDerivHalf

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

/-!
# The imprimitivity correction for the sharp off-axis bounds

For `N ∣ q` and a character `ψ` mod `N`, the level-`q` character
`χ = changeLevel hdvd ψ` satisfies the Euler-product factorisation

`L(s,χ) = L(s,ψ) · ∏_{p ∣ q} (1 - ψ(p) p^{-s})`  (`DirichletCharacter.LFunction_changeLevel`),

the factors indexed by the primes `p ∣ N` being equal to `1` because `ψ` vanishes at the
non-unit `p ∈ ZMod N`.  Taking logarithmic derivatives and real parts, and bounding each
remaining local factor by `Re (logDeriv (1 - c p^{-·})) ≥ -(1/2) log p`
(`localFactorLogDerivHalf`), the correction is at most

`(1/2) · ∑_{p ∈ q.primeFactors, p ∤ N} log p ≤ (1/2) · (log q - log N)`
(`sumLogPrimesNotDvdLe`).

Hence `-Re L'/L(·,χ) ≤ -Re L'/L(·,ψ) + (1/2)(log q - log N) + log 2`: raising the level from the
conductor to `q` does **not** destroy the sharp constant `1/2` in front of `log q`.  This is the
missing brick that lets the level-`q` sharp bound (`sharpLevelOffAxis`) be obtained from the
primitive one (`sharpPrimitiveOffAxis`).
-/

set_option maxHeartbeats 800000

/-- A local Euler factor `1 - c p^{-s}` with `‖c‖ ≤ 1` does not vanish for `Re s > 1`. -/
private lemma localFactor_ne_zero {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {z : ℂ} (hz : 1 < z.re) : 1 - c * (p : ℂ) ^ (-z) ≠ 0 := by
  intro hzero
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : c * (p : ℂ) ^ (-z) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm : ‖(p : ℂ) ^ (-z)‖ = (p : ℝ) ^ (-z.re) := by
    have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := by simp
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    simp
  have hlt : (p : ℝ) ^ (-z.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hbound : ‖c * (p : ℂ) ^ (-z)‖ < 1 := by
    rw [norm_mul, hnorm]
    calc ‖c‖ * (p : ℝ) ^ (-z.re) ≤ 1 * (p : ℝ) ^ (-z.re) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hppos.le _)
      _ = (p : ℝ) ^ (-z.re) := one_mul _
      _ < 1 := hlt
  rw [h1, norm_one] at hbound
  exact lt_irrefl 1 hbound

/-- The imprimitivity correction for the logarithmic derivative when the level is raised from
`N` to a multiple `q`. -/
theorem changeLevelSharpCorrection {N q : ℕ} [NeZero N] [NeZero q] (hdvd : N ∣ q)
    (ψ : DirichletCharacter ℂ N) (s : ℂ) (hs : 1 < s.re) :
    (-logDeriv (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd ψ)) s).re ≤
      (-logDeriv (DirichletCharacter.LFunction ψ) s).re
        + (1 / 2) * (Real.log (q : ℝ) - Real.log (N : ℝ)) + Real.log 2 := by
  have hsne : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set F : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors,
      (1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)) with hF
  have hfact : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd ψ) s
      = DirichletCharacter.LFunction ψ s * F s := by
    rw [hF]
    exact DirichletCharacter.LFunction_changeLevel hdvd ψ (Or.inr hsne)
  have hev : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd ψ)
      =ᶠ[nhds s] fun z => DirichletCharacter.LFunction ψ z * F z := by
    filter_upwards [compl_singleton_mem_nhds hsne] with z hz
    simp only [Set.mem_compl_singleton_iff] at hz
    rw [hF]
    exact DirichletCharacter.LFunction_changeLevel hdvd ψ (Or.inr hz)
  have hLne : DirichletCharacter.LFunction ψ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inr hsne) hs.le
  have hLdiff : DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) s :=
    DirichletCharacter.differentiableAt_LFunction ψ s (Or.inl hsne)
  have hFne : F s ≠ 0 := by
    rw [hF, Finset.prod_ne_zero_iff]
    intro p hp
    exact localFactor_ne_zero (Nat.prime_of_mem_primeFactors hp)
      (DirichletCharacter.norm_le_one ψ ((p : ZMod N))) hs
  have hFlocdiff : ∀ p ∈ q.primeFactors,
      DifferentiableAt ℂ (fun z : ℂ => 1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)) s := by
    intro p hp
    have hpne : (p : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hbase : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
      (differentiable_neg.differentiableAt).const_cpow (Or.inl hpne)
    exact (differentiableAt_const (c := (1 : ℂ))).sub
      (hbase.const_mul (ψ ((p : ZMod N))))
  have hFdiff : DifferentiableAt ℂ F s := by
    rw [hF]
    have hfun : (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)))
        = (∏ p ∈ q.primeFactors, fun z : ℂ => (1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z))) := by
      funext z
      rw [Finset.prod_apply]
    rw [hfun]
    exact DifferentiableAt.finsetProd hFlocdiff
  have hldeq : logDeriv (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd ψ)) s
      = logDeriv (fun z => DirichletCharacter.LFunction ψ z * F z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hfact]
  have hmul : logDeriv (fun z => DirichletCharacter.LFunction ψ z * F z) s
      = logDeriv (DirichletCharacter.LFunction ψ) s + logDeriv F s :=
    logDeriv_mul s hLne hFne hLdiff hFdiff
  have hFld : (logDeriv F s).re = ∑ p ∈ q.primeFactors,
      (logDeriv (fun z : ℂ => 1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)) s).re := by
    rw [hF, show (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)))
        = (∏ p ∈ q.primeFactors, fun z : ℂ => (1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z))) from by
          funext z; rw [Finset.prod_apply], logDeriv_prod]
    · rw [Complex.re_sum]
    · intro p hp
      exact localFactor_ne_zero (Nat.prime_of_mem_primeFactors hp)
        (DirichletCharacter.norm_le_one ψ ((p : ZMod N))) hs
    · intro p hp
      exact hFlocdiff p hp
  set a : ℕ → ℝ := fun p =>
    (logDeriv (fun z : ℂ => 1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)) s).re with ha
  set S : Finset ℕ := q.primeFactors.filter (fun p => ¬ p ∣ N) with hS
  have hzero_term : ∀ p ∈ q.primeFactors, p ∣ N → a p = 0 := by
    intro p hp hpdvd
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hnotunit : ¬ IsUnit ((p : ZMod N)) := by
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      have hg : Nat.gcd p N = p := Nat.gcd_eq_left hpdvd
      rw [Nat.Coprime, hg] at hcop
      exact hpp.ne_one hcop
    have hpsi : ψ ((p : ZMod N)) = 0 := ψ.map_nonunit hnotunit
    have hconst : (fun z : ℂ => 1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)) = fun _ => (1 : ℂ) := by
      funext z
      rw [hpsi]
      ring
    have h1 : a p = (logDeriv (fun z : ℂ => 1 - ψ ((p : ZMod N)) * (p : ℂ) ^ (-z)) s).re := rfl
    rw [h1, hconst]
    simp [logDeriv_apply]
  have hS_le : ∑ p ∈ S, a p ≤ ∑ p ∈ q.primeFactors, a p := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_le_sum (fun p hp => ?_)
    by_cases h : p ∣ N
    · simp [h, hzero_term p hp h]
    · simp [h]
  have hS_bound : ∑ p ∈ S, (-(1 / 2) * Real.log (p : ℝ)) ≤ ∑ p ∈ S, a p := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpmem : p ∈ q.primeFactors := by
      rw [hS] at hp; exact Finset.mem_of_mem_filter p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    exact localFactorLogDerivHalf p hpp (ψ ((p : ZMod N)))
      (DirichletCharacter.norm_le_one ψ _) s hs
  have hsum_eq : ∑ p ∈ S, (-(1 / 2) * Real.log (p : ℝ)) = -(1 / 2) * ∑ p ∈ S, Real.log (p : ℝ) := by
    rw [Finset.mul_sum]
  have hlogS : ∑ p ∈ S, Real.log (p : ℝ) ≤ Real.log (q : ℝ) - Real.log (N : ℝ) := by
    rw [hS]
    exact sumLogPrimesNotDvdLe N q hdvd
  have hmain : -(1 / 2) * (Real.log (q : ℝ) - Real.log (N : ℝ)) ≤ (logDeriv F s).re := by
    rw [hFld]
    calc -(1 / 2) * (Real.log (q : ℝ) - Real.log (N : ℝ))
        ≤ -(1 / 2) * ∑ p ∈ S, Real.log (p : ℝ) :=
          mul_le_mul_of_nonpos_left hlogS (by norm_num)
      _ = ∑ p ∈ S, (-(1 / 2) * Real.log (p : ℝ)) := hsum_eq.symm
      _ ≤ ∑ p ∈ S, a p := hS_bound
      _ ≤ ∑ p ∈ q.primeFactors, a p := hS_le
  have hldeq2 : logDeriv (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd ψ)) s
      = logDeriv (DirichletCharacter.LFunction ψ) s + logDeriv F s := by
    rw [hldeq, hmul]
  have hFbound : (-logDeriv F s).re ≤ (1 / 2) * (Real.log (q : ℝ) - Real.log (N : ℝ)) + Real.log 2 := by
    rw [Complex.neg_re]
    linarith [hmain, hlog2]
  calc (-logDeriv (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd ψ)) s).re
      = (-(logDeriv (DirichletCharacter.LFunction ψ) s + logDeriv F s)).re := by rw [hldeq2]
    _ = (-logDeriv (DirichletCharacter.LFunction ψ) s).re + (-logDeriv F s).re := by
          rw [neg_add_rev, Complex.add_re, add_comm]
    _ ≤ (-logDeriv (DirichletCharacter.LFunction ψ) s).re
          + ((1 / 2) * (Real.log (q : ℝ) - Real.log (N : ℝ)) + Real.log 2) := by
          linarith [hFbound]
    _ = (-logDeriv (DirichletCharacter.LFunction ψ) s).re
          + (1 / 2) * (Real.log (q : ℝ) - Real.log (N : ℝ)) + Real.log 2 := by ring

end

end Work.LinnikAreas.OtherCharRepel

