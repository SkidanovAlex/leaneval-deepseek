import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2

namespace Work.BourgainPlan.Maximal

/-- **Uniqueness of the major-arc representation (non-monic, `c`-scaled).**  For `N ≥ 3`,
`d = P.natDegree ≥ 2` and two triples with `|c θ − a/q − l| ≤ N^{-(d−1/4)}`, `a < q`, `gcd a q = 1`,
`l ∈ [-1, c]`, `q ≤ N^{1/4}`, the triples coincide.

Proof route: verbatim adaptation of `Commons.Analysis.ExponentialSums.pow_majorArc_single_unique`
(Submission/Commons/Analysis/ExponentialSums/pure_power_kernel_maximal_l2.lean, lines ~157–249),
which is the same statement with `l ∈ Icc (-2) 2` instead of `Icc (-1) c` at the same radius
`N^{-(d−1/4)}`.  The numeric separation input is
`Commons.Analysis.ExponentialSums.majorArc_shift_sep`
(`|(a/q + l) − (a'/q' + l')| ≥ 1/(q q')` when nonzero), and the final step is
`Commons.Analysis.ExponentialSums.majorArc_term_unique` (both in
Submission/Commons/Analysis/ExponentialSums/quadratic_kernel_model_maximal_l2.lean, which must be
imported).  Note that the bounds on `l`, `l'` are not used by the argument. -/
theorem poly_arc_witness_unique (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {N : ℕ} (hN : 3 ≤ N) (θ : ℝ) {q q' : ℕ} {a a' : ℕ} {l l' : ℤ}
    (hq : (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4)) (ha : a < q) (hg : Nat.gcd a q = 1)
    (hq' : (q' : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4)) (ha' : a' < q') (hg' : Nat.gcd a' q' = 1)
    (hl : l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff)
    (hl' : l' ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff)
    (h₁ : |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
        ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4)))
    (h₂ : |(P.leadingCoeff : ℝ) * θ - (a' : ℝ) / (q' : ℝ) - (l' : ℝ)|
        ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4))) :
    q = q' ∧ a = a' ∧ l = l' := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hqpos : 0 < q := by omega
  have hqpos' : 0 < q' := by omega
  have hd' : (2:ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hsep : 2 * (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4)) < ((q:ℝ)*(q':ℝ))⁻¹ := by
    have hprod : (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^(1/2:ℝ) := by
      calc (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^(1/4:ℝ) * (N:ℝ)^(1/4:ℝ) :=
            mul_le_mul hq hq' (by positivity) (by positivity)
        _ = (N:ℝ)^(1/2:ℝ) := by
            rw [← Real.rpow_add hNpos]
            norm_num
    have hpos : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
    have h1 : (N:ℝ)^(-((1:ℝ)/2)) ≤ ((q:ℝ)*(q':ℝ))⁻¹ := by
      have h1' : ((N:ℝ)^((1:ℝ)/2))⁻¹ ≤ ((q:ℝ)*(q':ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) hpos).mpr hprod
      rwa [← Real.rpow_neg hNpos.le ((1:ℝ)/2)] at h1'
    have h2 : 2 * (N:ℝ)^(-((P.natDegree : ℝ)-(1:ℝ)/4)) ≤ 2 * (N:ℝ)^(-(7/4:ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      linarith
    have h3 : 2 * (N:ℝ)^(-((7:ℝ)/4)) < (N:ℝ)^(-((1:ℝ)/2)) := by
      have hN54 : (2:ℝ) < (N:ℝ)^((5:ℝ)/4) := by
        have h3' : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        have h5' : (3:ℝ) < (N:ℝ)^((5:ℝ)/4) :=
          calc (3:ℝ) = (3:ℝ)^(1:ℝ) := (Real.rpow_one 3).symm
            _ < (3:ℝ)^((5:ℝ)/4) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
            _ ≤ (N:ℝ)^((5:ℝ)/4) := Real.rpow_le_rpow (by norm_num) h3' (by norm_num)
        linarith
      have h4 : (N:ℝ)^(-((7:ℝ)/4)) = (N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      have h5 : (N:ℝ)^(-((5:ℝ)/4)) = ((N:ℝ)^((5:ℝ)/4))⁻¹ :=
        Real.rpow_neg hNpos.le ((5:ℝ)/4)
      have h1' : 2 * (N:ℝ)^(-((5:ℝ)/4)) < 1 := by
        rw [h5, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hNpos _)]
        exact hN54
      have h2' : (0:ℝ) < (N:ℝ)^(-((1:ℝ)/2)) := Real.rpow_pos_of_pos hNpos _
      rw [h4]
      calc 2 * ((N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)))
          = (N:ℝ)^(-((1:ℝ)/2)) * (2 * (N:ℝ)^(-((5:ℝ)/4))) := by ring
        _ < (N:ℝ)^(-((1:ℝ)/2)) * 1 := mul_lt_mul_of_pos_left h1' h2'
        _ = (N:ℝ)^(-((1:ℝ)/2)) := by ring
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le h3 h1)
  exact Commons.Analysis.ExponentialSums.majorArc_term_unique (q₁ := q) (q₂ := q') (a₁ := a) (a₂ := a') (l₁ := l) (l₂ := l')
    hqpos hqpos' ha ha' hg hg' h₁ h₂ hsep

end Work.BourgainPlan.Maximal
