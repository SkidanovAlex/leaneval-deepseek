/-
# `Work.ZeroFreeTables.P9.zetaDiffExplicit_gen` — the differentiated explicit formula for `ζ`

For every `k ≥ 1` and every `s` with `1 < Re s`,

`∑'_u ord_u(Λ)·(1/(s-u))^{k+1} + ∑'_n (1/(s+2n+2))^{k+1}
   = (-1)^k/(k!) · ((logDeriv ζ)^{(k)})(s) + 1/(s-1)^{k+1}`,

where `Λ = completedRiemannZeta` and `ord_u(Λ) = analyticOrderNatAt Λ u` is the multiplicity of
`u` as a non-trivial zero of `ζ` (in particular the first family is summable).  This is the
Lagarias–Montgomery–Odlyzko / Kadiri–Ng–Wong (2.5) identity for the Riemann zeta factor.

The case of odd `k` is already in the workspace as `Work.LinnikAreas.FarRepel.zetaDiffExplicit`;
the point here is that the same identity holds for *every* `k ≥ 1`, so the parity reduction
(`(-1)^k = -1`) is unnecessary.  The assembly is the same one:

* `Work.LinnikAreas.FarRepel.xiDerivPF` (Hadamard partial fraction at order `k` for the entire
  completion `Ξ = DhK.Xi`) together with the convergence of the ball divisor sums
  (`Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero`) gives
  `∑'_u ord_u(Ξ)·(1/(s-u))^{k+1} = (-1)^k · (1/k!) · ((logDeriv Ξ)^{(k)})(s)`
  (using `ord_u(Ξ) = ord_u(Λ)`, proved here as `ordNatXi_eq`);
* `Work.LinnikAreas.FarRepel.iteratedDeriv_logDeriv_Xi` splits
  `logDeriv Ξ = 1/z + 1/(z-1) + logDeriv Γℝ + logDeriv ζ` (on `Re z > 1`);
* `Work.ZeroFreeTables.P9.logDeriv_GammaR_iteratedDeriv_series` evaluates the `Γℝ`-derivative as
  `(-1)^{k+1} k! ∑'_n (1/(s+2n))^{k+1}`;
* `Work.ZeroFreeTables.P9.tsum_inv_add_two_shift` splits off the `n = 0` term `(1/s)^{k+1}` of that
  series, which cancels the `(1/s)^{k+1}` coming from `1/z`; the remaining elementary algebra is
  `alg_gen` below, using `(-1)^k·(-1)^k = 1` and `(-1)^{k+1} = (-1)^k·(-1)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.CompletedDerivPF
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.ZeroFreeTables.P9.XiChain
import Submission.Work.LinnikAreas.FarRepel.iteratedDeriv_logDeriv_Xi
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Work.ZeroFreeTables.P9.zetaZeroSum_summable_gen
import Submission.Work.ZeroFreeTables.P9.logDeriv_GammaR_iteratedDeriv_series
import Submission.Work.ZeroFreeTables.P9.tsum_inv_add_two_shift

open scoped Classical BigOperators Topology
open Filter

namespace Work.ZeroFreeTables.P9

noncomputable section

/-! ## The vanishing orders of `Ξ` and of `Λ` agree -/

/-- The vanishing multiplicities of the entire completion `Ξ = DhK.Xi` and of
`Λ = completedRiemannZeta` agree everywhere. -/
private lemma ordNatXi_eq (u : ℂ) :
    analyticOrderNatAt Work.LinnikAreas.DhK.Xi u = analyticOrderNatAt completedRiemannZeta u := by
  by_cases h0 : u = 0
  · subst h0
    have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by rw [Work.LinnikAreas.DhK.Xi_zero]; norm_num))
    rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 0 = 0 from by
          simp [analyticOrderNatAt, hx],
      analyticOrderNatAt_of_not_analyticAt Work.LinnikAreas.not_analyticAt_completedZeta_zero]
  · by_cases h1 : u = 1
    · subst h1
      have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 1 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (by
          rw [show Work.LinnikAreas.DhK.Xi 1 = 1 / 2 by simp [Work.LinnikAreas.DhK.Xi]]
          norm_num))
      rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 1 = 0 from by
            simp [analyticOrderNatAt, hx],
        analyticOrderNatAt_of_not_analyticAt Work.LinnikAreas.not_analyticAt_completedZeta_one]
    · exact Work.LinnikAreas.analyticOrderNatAt_xiC_eq u h0 h1

/-! ## The elementary algebra of the final cancellation -/

/-- The algebraic rearrangement closing the proof: with `X = (-1)^k`, `c = k!`, `X² = 1`,
`P = (1/s)^{k+1}`, `Q = (1/(s-1))^{k+1}` and `T` the trivial-zero series,

`X·(1/c)·(X·c·P + X·c·Q + (X·(-1))·c·(P+T) + D) + T = X·(1/c)·D + Q`. -/
private lemma alg_gen (X c P Q T D : ℂ) (hc : c ≠ 0) (hX : X * X = 1) :
    X * (1 / c) * (X * c * P + X * c * Q + (X * (-1)) * c * (P + T) + D) + T
      = X * (1 / c) * D + Q := by
  field_simp
  linear_combination c * (Q - T) * hX

/-! ## The differentiated explicit formula -/

theorem zetaDiffExplicit_gen (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)) ∧
    (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1))
      + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (k + 1))
      = (-1 : ℂ) ^ k * (1 / (k.factorial : ℂ)) * iteratedDeriv k (logDeriv riemannZeta) s
        + 1 / (s - 1) ^ (k + 1) := by
  classical
  -- summability of the zero family (general `k`)
  have hsumZeta : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)) :=
    zetaZeroSum_summable_gen k hk hs
  -- transfer to the entire completion `Ξ = DhK.Xi`
  have hsumXi : Summable (fun u : ℂ =>
      (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)) :=
    hsumZeta.congr fun u => by rw [ordNatXi_eq u]
  -- the divisor of `Ξ` on `Set.univ` is the vanishing order
  have hdivuniv : ∀ u : ℂ, MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ u
      = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℤ) := fun u =>
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (Work.LinnikAreas.DhK.Xi_analyticOnNhd Set.univ) (Set.mem_univ u)
  have hsumDiv : Summable (fun u : ℂ =>
      (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1)) := by
    rw [show (fun u : ℂ => (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        = (fun u : ℂ => (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        from funext fun u => by rw [hdivuniv u]; simp]
    exact hsumXi
  -- the ball sums converge to the full divisor sum
  have htend := Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
    (Work.LinnikAreas.DhK.Xi_meromorphicOn Set.univ) hsumDiv
  -- Hadamard partial fraction at order `k` for `Ξ`
  have hPF := Work.LinnikAreas.FarRepel.xiDerivPF k hk s
    (Work.LinnikAreas.DhK.Xi_ne_zero_of_one_lt_re hs)
  have huniq : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
      (∑' u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s :=
    tendsto_nhds_unique (htend.const_mul _) hPF
  have htsumDiv : (∑' u : ℂ,
        (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = ∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1) :=
    tsum_congr fun u => by rw [hdivuniv u]; simp
  have hfact : ((k.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hXne : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hX2 : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← pow_add, show k + k = 2 * k by ring, pow_mul]
    norm_num
  -- solve the partial-fraction identity for the zero sum
  have hscalar : (1 / ((-1 : ℂ) ^ k * (k.factorial : ℂ)))
      = (-1 : ℂ) ^ k * (1 / (k.factorial : ℂ)) := by
    rw [one_div, mul_inv_rev, inv_eq_of_mul_eq_one_right hX2, one_div]
    ring
  have hSXi : (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = (-1 : ℂ) ^ k * (1 / (k.factorial : ℂ))
          * iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s := by
    rw [htsumDiv] at huniq
    have h := congrArg
      (fun z : ℂ => (1 / ((-1 : ℂ) ^ k * (k.factorial : ℂ))) * z) huniq
    have h2 : (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        = (1 / ((-1 : ℂ) ^ k * (k.factorial : ℂ)))
            * iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s := by
      rw [← mul_assoc, one_div, inv_mul_cancel₀ (mul_ne_zero hXne hfact), one_mul] at h
      simpa only [one_div] using h
    rw [h2, hscalar]
  -- assemble
  refine ⟨hsumZeta, ?_⟩
  have htsumZeta : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = ∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1) :=
    tsum_congr fun u => by rw [ordNatXi_eq u]
  rw [htsumZeta, hSXi]
  rw [Work.LinnikAreas.FarRepel.iteratedDeriv_logDeriv_Xi k hk hs]
  rw [logDeriv_GammaR_iteratedDeriv_series k hk hs]
  rw [(tsum_inv_add_two_shift k hk hs).2]
  rw [show (-1 : ℂ) ^ (k + 1) = (-1 : ℂ) ^ k * (-1) by rw [pow_succ]]
  simp only [← one_div_pow]
  set X : ℂ := (-1 : ℂ) ^ k with hX
  set c : ℂ := (k.factorial : ℂ) with hcdef
  set P : ℂ := (1 / s) ^ (k + 1) with hP
  set Q : ℂ := (1 / (s - 1)) ^ (k + 1) with hQ
  set T : ℂ := ∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (k + 1) with hT
  set Dv : ℂ := iteratedDeriv k (logDeriv riemannZeta) s with hD
  have hcne : c ≠ 0 := by rw [hcdef]; exact_mod_cast Nat.factorial_ne_zero k
  have hX2' : X * X = 1 := by
    rw [hX, ← pow_add, show k + k = 2 * k by ring, pow_mul]
    norm_num
  exact alg_gen X c P Q T Dv hcne hX2'

end

end Work.ZeroFreeTables.P9
