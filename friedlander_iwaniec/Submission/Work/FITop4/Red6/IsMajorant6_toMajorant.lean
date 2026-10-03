import Mathlib
import Submission.Work.FITop4.Defs6

namespace Work.FITop4.Red6

/-- **ROUND 6.3**: `Work.FITop4.IsMajorant6` implies the round-3 `Work.FITop3.IsMajorant`.
`Defs6.IsMajorant6 Pa f` asserts a `C⁴` interpolant `F` with `F n = f n` and
`|iteratedDeriv j F u| ≤ cMaj j · Pa.M^{-(j:ℝ)}` for `j ≤ 4`, with the absolute constants
`cMaj 1 = 8`, `cMaj 2 = 64` (`Defs6.cMaj`); the first and second difference bounds `|Δf| ≤ 8/M`,
`|Δ²f| ≤ 64/M²` of the round-3 predicate then follow from the MVT, and the support/size/annulus
conjuncts of `IsMajorant6` are conjuncts of the round-3 predicate verbatim.

Hint for the second difference (the constants are tight; do not apply the MVT twice to `F` itself,
which would give `128/M²`): for `h(t) = F(u+1+t) - F(u+t)` on `[0,1]` the MVT gives
`f (u+2) - 2 * f (u+1) + f u = iteratedDeriv 1 F (u+1+c) - iteratedDeriv 1 F (u+c)` with `c ∈ (0,1)`,
and a second MVT on `iteratedDeriv 1 F` between `u+c` and `u+1+c` (differing by exactly `1`) gives
`cMaj 2 · M^{-2} = 64/M²`.  (The callers want the name `Work.FITop4.IsMajorant6.toMajorant`; an
alias with that name is added in `Areas6.lean`, which imports this module.) -/
theorem IsMajorant6_toMajorant {Pa : Work.FITop.Params} {f : ℤ → ℝ}
    (h : Work.FITop4.IsMajorant6 Pa f) : Work.FITop3.IsMajorant Pa f := by
  obtain ⟨⟨F, hFc, hFint, hFb⟩, h0, h1, h2, h3⟩ := h
  have hMpos : (0:ℝ) < Pa.M := lt_of_lt_of_le zero_lt_one Pa.hM1
  have hdF : Differentiable ℝ F := hFc.differentiable (by norm_num)
  refine ⟨h0, h1, h2, h3, ?_, ?_⟩
  · -- first difference: the mean value theorem on `[u, u+1]`
    intro u
    have hcont : ContinuousOn F (Set.Icc (u:ℝ) ((u:ℝ)+1)) := hFc.continuous.continuousOn
    have hdiff : DifferentiableOn ℝ F (Set.Ioo (u:ℝ) ((u:ℝ)+1)) := hdF.differentiableOn
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope F (by linarith) hcont hdiff
    have hF1 : F ((u:ℝ)+1) = f (u+1) := by
      have hh : ((u+1:ℤ):ℝ) = (u:ℝ)+1 := by push_cast; ring
      rw [← hh]; exact hFint (u+1)
    have hF0 : F ((u:ℝ)) = f u := hFint u
    have hval : f (u+1) - f u = deriv F c := by
      rw [← hF1, ← hF0, hcd]; ring_nf
    rw [hval]
    calc |deriv F c| = |iteratedDeriv 1 F c| := by rw [iteratedDeriv_one]
      _ ≤ cMaj 1 * Pa.M ^ (-(1:ℝ)) := by simpa using hFb 1 (by norm_num) c
      _ = 8 / Pa.M := by
          rw [show cMaj 1 = 8 by norm_num [cMaj], Real.rpow_neg_one, div_eq_mul_inv]
  · -- second difference: the mean value theorem on `h(t) = F(u+1+t) - F(u+t)`, then on `deriv F`
    intro u
    have hF0 : F ((u:ℝ)) = f u := hFint u
    have hF1 : F ((u:ℝ)+1) = f (u+1) := by
      have hh : ((u+1:ℤ):ℝ) = (u:ℝ)+1 := by push_cast; ring
      rw [← hh]; exact hFint (u+1)
    have hF2 : F ((u:ℝ)+2) = f (u+2) := by
      have hh : ((u+2:ℤ):ℝ) = (u:ℝ)+2 := by push_cast; ring
      rw [← hh]; exact hFint (u+2)
    have hval : f (u+2) - 2 * f (u+1) + f u
        = F ((u:ℝ)+2) - 2 * F ((u:ℝ)+1) + F ((u:ℝ)) := by
      rw [hF0, hF1, hF2]
    set r : ℝ := (u:ℝ) with hr
    rw [hval]
    set A : ℝ → ℝ := fun t => F (t + (r+1)) - F (t + r) with hA
    have hAdiff : Differentiable ℝ A := by rw [hA]; fun_prop
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope A (by norm_num : (0:ℝ) < 1)
      hAdiff.continuous.continuousOn hAdiff.differentiableOn
    have hderivA : deriv A c = deriv F (c + (r+1)) - deriv F (c + r) := by
      rw [hA]
      have hfun : (fun t => F (t + (r+1)) - F (t + r))
          = (fun t => F (t + (r+1))) - (fun t => F (t+r)) := by
        funext t; simp
      rw [hfun]
      have h1 : HasDerivAt (fun t => F (t + (r+1))) (deriv F (c + (r+1))) c :=
        (hdF (c+(r+1))).hasDerivAt.comp_add_const c (r+1)
      have h2 : HasDerivAt (fun t => F (t + r)) (deriv F (c + r)) c :=
        (hdF (c+r)).hasDerivAt.comp_add_const c r
      exact (h1.sub h2).deriv
    have hA1 : A 1 = F (r+2) - F (r+1) := by rw [hA]; ring_nf
    have hA0 : A 0 = F (r+1) - F r := by rw [hA]; ring_nf
    have hAA : A 1 - A 0 = deriv A c := by rw [hcd]; ring_nf
    have hcont2 : ContinuousOn (deriv F) (Set.Icc (c + r) (c + r + 1)) :=
      (hFc.continuous_deriv (by norm_num)).continuousOn
    have hdd : Differentiable ℝ (deriv F) :=
      ContDiff.differentiable_deriv_two (hFc.of_le (by norm_num))
    obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope (deriv F) (by linarith) hcont2
      hdd.differentiableOn
    have hstep : deriv F (c + r + 1) - deriv F (c + r) = deriv (deriv F) ξ := by
      rw [hξd]; ring_nf
    have hkey : F (r+2) - 2 * F (r+1) + F r = iteratedDeriv 2 F ξ := by
      calc F (r+2) - 2 * F (r+1) + F r
          = A 1 - A 0 := by rw [hA1, hA0]; ring
        _ = deriv A c := hAA
        _ = deriv F (c + (r+1)) - deriv F (c + r) := hderivA
        _ = deriv F (c + r + 1) - deriv F (c + r) := by ring_nf
        _ = deriv (deriv F) ξ := hstep
        _ = iteratedDeriv 2 F ξ := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    calc |F (r+2) - 2 * F (r+1) + F r| = |iteratedDeriv 2 F ξ| := by rw [hkey]
      _ ≤ cMaj 2 * Pa.M ^ (-(2:ℝ)) := by simpa using hFb 2 (by norm_num) ξ
      _ = 64 / Pa.M^2 := by
          rw [show cMaj 2 = 64 by norm_num [cMaj], Real.rpow_neg hMpos.le, Real.rpow_two,
            div_eq_mul_inv]

end Work.FITop4.Red6
