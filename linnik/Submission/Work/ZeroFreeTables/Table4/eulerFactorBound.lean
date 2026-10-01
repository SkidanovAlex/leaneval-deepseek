import Mathlib
import Submission.Work.ZeroFreeTables.Table4.primeTermNormLe
import Submission.Work.ZeroFreeTables.Table4.primeTermDerivNormLe
import Submission.Work.ZeroFreeTables.Table4.primeTermDeriv2NormLe

/-!
# Euler-factor derivative bounds (Heath-Brown, Table 4)

For a modulus `q` and a point `s` with `Re s ≥ 1`, the sum over the primes `p | q`
of the logarithmic Euler factors `log p / (p^s - 1)`, together with its first two
`z`-derivatives, is bounded by

* `∑_{p|q} 2 log p / p`,
* `∑_{p|q} 4 (log p)^2 / p`,
* `∑_{p|q} 16 (log p)^3 / p`.

The pointwise estimates are supplied by the lemmas `primeTermNormLe`,
`primeTermDerivNormLe` and `primeTermDeriv2NormLe`; here we differentiate the
finite sum term-by-term and combine them with the triangle inequality.
-/

namespace Work.ZeroFreeTables.Table4

open scoped BigOperators Topology

/-- The first `z`-derivative of the Euler factor `log p / (p^z - 1)`:
`-(log p)^2 p^z / (p^z - 1)^2` (denominator written multiplicatively). -/
private noncomputable def eulerD1 (p : ℕ) (z : ℂ) : ℂ :=
  -((Real.log (p : ℝ) : ℂ) ^ 2 * (p : ℂ) ^ z / (((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1)))

/-- The second `z`-derivative of the Euler factor `log p / (p^z - 1)`:
`(log p)^3 p^z (p^z + 1) / (p^z - 1)^3` (denominator written multiplicatively). -/
private noncomputable def eulerD2 (p : ℕ) (z : ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) ^ 3 * (p : ℂ) ^ z * ((p : ℂ) ^ z + 1)
    / (((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1))

/-- `‖p^z‖ = p^{Re z}` for a positive natural number `p`. -/
private lemma cpow_norm_eq (p : ℕ) (hp : 0 < p) (z : ℂ) :
    ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < (p : ℝ) by exact_mod_cast hp) z
  simpa using h

/-- The half-plane `{w | 1/2 ≤ Re w}` is a neighbourhood of every `z` with `Re z ≥ 1`. -/
private lemma eventually_half_le_re (z : ℂ) (hz : 1 ≤ z.re) :
    ∀ᶠ w : ℂ in 𝓝 z, (1 / 2 : ℝ) ≤ w.re := by
  have hball : ∀ᶠ w : ℂ in 𝓝 z, dist w z < (1 / 2 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < 1 / 2 by norm_num)] with w hw
    rwa [Metric.mem_ball] at hw
  filter_upwards [hball] with w hw
  have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
    have h := Complex.abs_re_le_norm (w - z)
    simpa using h
  rw [dist_eq_norm] at hw
  have h2 : -((1 / 2 : ℝ)) < w.re - z.re := (abs_lt.mp (lt_of_le_of_lt h1 hw)).1
  linarith

/-- For a prime `p` and `Re w ≥ 1/2` the denominator `p^w - 1` is non-zero. -/
private lemma cpow_sub_one_ne_zero_of_half (p : ℕ) (hp : p.Prime) (w : ℂ)
    (hw : (1 / 2 : ℝ) ≤ w.re) : (p : ℂ) ^ w - 1 ≠ 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hnorm : ‖(p : ℂ) ^ w‖ = (p : ℝ) ^ w.re := cpow_norm_eq p hp.pos w
  have hone : (1 : ℝ) < (p : ℝ) ^ w.re := by
    have hpos : (0 : ℝ) < w.re := by linarith
    have h := (Real.rpow_lt_rpow_left_iff hp1).mpr hpos
    rwa [Real.rpow_zero] at h
  intro h
  have h1 : ‖(p : ℂ) ^ w‖ = 1 := by rw [sub_eq_zero.mp h]; simp
  rw [hnorm] at h1
  linarith

/-- The derivative of `w ↦ log p / (p^w - 1)` at a point where the denominator is non-zero. -/
private lemma term_hasDerivAt (p : ℕ) (hp : p.Prime) (z : ℂ)
    (hne : (p : ℂ) ^ z - 1 ≠ 0) :
    HasDerivAt (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) (eulerD1 p z) z := by
  have hpc : (p : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_ne_zero]
    exact_mod_cast hp.pos.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast p]
    exact (Complex.ofReal_log (x := (p : ℝ)) (by positivity)).symm
  have hA : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := by
    have h : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * Complex.log (p : ℂ) * 1) z :=
      (hasDerivAt_id z).const_cpow (Or.inl hpc)
    rwa [hlog, mul_one] at h
  have hden : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w - 1)
      ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := hA.sub_const 1
  have h := (hasDerivAt_const z ((Real.log (p : ℝ) : ℂ))).div hden hne
  have hd : deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) z = eulerD1 p z := by
    rw [show (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1))
        = ((fun _ : ℂ => (Real.log (p : ℝ) : ℂ)) / (fun w : ℂ => (p : ℂ) ^ w - 1)) from rfl]
    rw [h.deriv]
    simp only [eulerD1]
    have h2 : ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) ≠ 0 := mul_ne_zero hne hne
    have h3 : ((p : ℂ) ^ z - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hne
    field_simp
    ring
  rw [← hd]
  exact h.differentiableAt.hasDerivAt

/-- The derivative of `eulerD1 p` at a point where the denominator is non-zero. -/
private lemma derivTerm_hasDerivAt (p : ℕ) (hp : p.Prime) (z : ℂ)
    (hne : (p : ℂ) ^ z - 1 ≠ 0) :
    HasDerivAt (eulerD1 p) (eulerD2 p z) z := by
  have hpc : (p : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_ne_zero]
    exact_mod_cast hp.pos.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast p]
    exact (Complex.ofReal_log (x := (p : ℝ)) (by positivity)).symm
  have hA : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := by
    have h : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * Complex.log (p : ℂ) * 1) z :=
      (hasDerivAt_id z).const_cpow (Or.inl hpc)
    rwa [hlog, mul_one] at h
  have hnum : HasDerivAt (fun w : ℂ => (Real.log (p : ℝ) : ℂ) ^ 2 * (p : ℂ) ^ w)
      ((Real.log (p : ℝ) : ℂ) ^ 2 * ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ))) z :=
    hA.const_mul _
  have hg : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w - 1)
      ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := hA.sub_const 1
  have hden : HasDerivAt (fun w : ℂ => ((p : ℂ) ^ w - 1) * ((p : ℂ) ^ w - 1))
      (((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) * ((p : ℂ) ^ z - 1)
        + ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ))) z :=
    hg.mul hg
  have hne2 : ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) ≠ 0 := mul_ne_zero hne hne
  have hdiv := hnum.div hden hne2
  have h := hdiv.neg
  have hd : deriv (eulerD1 p) z = eulerD2 p z := by
    rw [show eulerD1 p
        = -(((fun w : ℂ => (Real.log (p : ℝ) : ℂ) ^ 2 * (p : ℂ) ^ w)
            / (fun w : ℂ => ((p : ℂ) ^ w - 1) * ((p : ℂ) ^ w - 1)))) from rfl]
    rw [h.deriv]
    simp only [eulerD2]
    have h3 : ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) ≠ 0 :=
      mul_ne_zero hne2 hne
    have h4 : (((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1)) ^ 2 ≠ 0 := pow_ne_zero 2 hne2
    field_simp
    ring
  rw [← hd]
  exact h.differentiableAt.hasDerivAt

theorem eulerFactorBound (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1)‖
        ≤ ∑ p ∈ q.primeFactors, 2 * Real.log (p : ℝ) / (p : ℝ) ∧
    ‖iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖
        ≤ ∑ p ∈ q.primeFactors, 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ∧
    ‖iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖
        ≤ ∑ p ∈ q.primeFactors, 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
  classical
  have hne_s : ∀ p ∈ q.primeFactors, (p : ℂ) ^ s - 1 ≠ 0 := fun p hp =>
    cpow_sub_one_ne_zero_of_half p (Nat.prime_of_mem_primeFactors hp) s (by linarith)
  have hhalf : ∀ᶠ z : ℂ in 𝓝 s, (1 / 2 : ℝ) ≤ z.re := eventually_half_le_re s hs
  have hsumfun : (fun z : ℂ => ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1))
      = (∑ p ∈ q.primeFactors, fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) := by
    funext z; rw [Finset.sum_apply]
  refine ⟨?_, ?_, ?_⟩
  · calc ‖∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1)‖
        ≤ ∑ p ∈ q.primeFactors, ‖(Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, 2 * Real.log (p : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum fun p hp =>
            primeTermNormLe p (Nat.prime_of_mem_primeFactors hp) s hs
  · have h1 : iteratedDeriv 1
          (fun z : ℂ => ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s
        = ∑ p ∈ q.primeFactors, eulerD1 p s := by
      rw [iteratedDeriv_one, hsumfun]
      have hsum : deriv (∑ p ∈ q.primeFactors,
            fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s
          = ∑ p ∈ q.primeFactors,
            deriv (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s :=
        deriv_sum (fun p hp =>
          (term_hasDerivAt p (Nat.prime_of_mem_primeFactors hp) s (hne_s p hp)).differentiableAt)
      rw [hsum]
      exact Finset.sum_congr rfl fun p hp =>
        (term_hasDerivAt p (Nat.prime_of_mem_primeFactors hp) s (hne_s p hp)).deriv
    rw [h1]
    calc ‖∑ p ∈ q.primeFactors, eulerD1 p s‖
        ≤ ∑ p ∈ q.primeFactors, ‖eulerD1 p s‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' : deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) s
              = eulerD1 p s :=
            (term_hasDerivAt p (Nat.prime_of_mem_primeFactors hp) s (hne_s p hp)).deriv
          rw [← hp']
          exact primeTermDerivNormLe p (Nat.prime_of_mem_primeFactors hp) s hs
  · have h2eq : iteratedDeriv 2
          (fun z : ℂ => ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s
        = deriv (deriv (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1))) s := by
      have htwo : (2 : ℕ) = 1 + 1 := by norm_num
      simp only [htwo, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [h2eq]
    have heq : deriv (fun z : ℂ => ∑ p ∈ q.primeFactors,
            (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1))
        =ᶠ[𝓝 s] (∑ p ∈ q.primeFactors, eulerD1 p) := by
      filter_upwards [hhalf] with z hz
      rw [hsumfun]
      have hsum : deriv (∑ p ∈ q.primeFactors,
            fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) z
          = ∑ p ∈ q.primeFactors,
            deriv (fun z : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) z :=
        deriv_sum (fun p hp =>
          (term_hasDerivAt p (Nat.prime_of_mem_primeFactors hp) z
            (cpow_sub_one_ne_zero_of_half p (Nat.prime_of_mem_primeFactors hp) z hz)).differentiableAt)
      rw [hsum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun p hp =>
        (term_hasDerivAt p (Nat.prime_of_mem_primeFactors hp) z
          (cpow_sub_one_ne_zero_of_half p (Nat.prime_of_mem_primeFactors hp) z hz)).deriv
    rw [heq.deriv_eq]
    have hL2 : deriv (∑ p ∈ q.primeFactors, eulerD1 p) s
        = ∑ p ∈ q.primeFactors, deriv (eulerD1 p) s :=
      deriv_sum (fun p hp =>
        (derivTerm_hasDerivAt p (Nat.prime_of_mem_primeFactors hp) s (hne_s p hp)).differentiableAt)
    rw [hL2]
    calc ‖∑ p ∈ q.primeFactors, deriv (eulerD1 p) s‖
        ≤ ∑ p ∈ q.primeFactors, ‖deriv (eulerD1 p) s‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hd : deriv (eulerD1 p) s = deriv (deriv (fun w : ℂ =>
              (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1))) s := by
            have heqp : deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1))
                =ᶠ[𝓝 s] eulerD1 p := by
              filter_upwards [hhalf] with z hz
              exact (term_hasDerivAt p (Nat.prime_of_mem_primeFactors hp) z
                (cpow_sub_one_ne_zero_of_half p (Nat.prime_of_mem_primeFactors hp) z hz)).deriv
            exact heqp.deriv_eq.symm
          rw [hd]
          exact primeTermDeriv2NormLe p (Nat.prime_of_mem_primeFactors hp) s hs

end Work.ZeroFreeTables.Table4
