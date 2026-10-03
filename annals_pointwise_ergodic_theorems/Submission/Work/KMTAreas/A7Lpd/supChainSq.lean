import Mathlib
import Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum

namespace Work.KMTAreas.A7Lpd

open scoped ENNReal NNReal BigOperators

/-- **The `ℓ^q`-norm of a finite vector is at most its `ℓ^p`-norm when `p ≤ q`** (both of these
being the *unnormalised* norms `(∑ i, x i ^ p) ^ (1/p)`).  Writing `S = ∑ i, x i ^ p` and
`α = q / p ≥ 1`, the claim is `∑ i, (x i ^ p) ^ α ≤ S ^ α`, which follows from the pointwise
inequality `(x i ^ p) ^ α = (x i ^ p) · (x i ^ p) ^ (α - 1) ≤ (x i ^ p) · S ^ (α - 1)` and
`∑ i, x i ^ p = S`. -/
lemma sum_rpow_le_sum_rpow' {ι : Type*} [Fintype ι] (x : ι → ENNReal) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i, x i ^ q) ^ (1 / q) ≤ (∑ i, x i ^ p) ^ (1 / p) := by
  set S : ENNReal := ∑ i, x i ^ p with hS
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hα0 : (0 : ℝ) ≤ q / p - 1 := by
    have : (1 : ℝ) ≤ q / p := (one_le_div hp).mpr hpq
    linarith
  have hmul : S * S ^ (q / p - 1) = S ^ (q / p) := by
    calc S * S ^ (q / p - 1) = S ^ (1 : ℝ) * S ^ (q / p - 1) := by rw [ENNReal.rpow_one]
      _ = S ^ (1 + (q / p - 1)) :=
          (ENNReal.rpow_add_of_nonneg (x := S) 1 (q / p - 1) zero_le_one hα0).symm
      _ = S ^ (q / p) := by
          congr 1
          ring
  have step1 : ∑ i, x i ^ q ≤ S ^ (q / p) := by
    calc ∑ i, x i ^ q
        = ∑ i, (x i ^ p) ^ (q / p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ENNReal.rpow_mul]
          rw [show p * (q / p) = q by field_simp]
        _ = ∑ i, (x i ^ p) * (x i ^ p) ^ (q / p - 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc (x i ^ p) ^ (q / p) = (x i ^ p) ^ (1 + (q / p - 1)) := by
                rw [show (1 : ℝ) + (q / p - 1) = q / p by ring]
            _ = (x i ^ p) ^ (1 : ℝ) * (x i ^ p) ^ (q / p - 1) :=
                ENNReal.rpow_add_of_nonneg (x := x i ^ p) 1 (q / p - 1) zero_le_one hα0
            _ = (x i ^ p) * (x i ^ p) ^ (q / p - 1) := by rw [ENNReal.rpow_one]
        _ ≤ ∑ i, (x i ^ p) * S ^ (q / p - 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_right ?_ _
          exact ENNReal.rpow_le_rpow
            (Finset.single_le_sum (f := fun j => x j ^ p) (fun j _ => (bot_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)) hα0
        _ = (∑ i, x i ^ p) * S ^ (q / p - 1) := (Finset.sum_mul _ _ _).symm
        _ = S * S ^ (q / p - 1) := by rw [hS]
        _ = S ^ (q / p) := hmul
  calc (∑ i, x i ^ q) ^ (1 / q)
      ≤ (S ^ (q / p)) ^ (1 / q) := ENNReal.rpow_le_rpow step1 (by positivity)
    _ = S ^ ((q / p) * (1 / q)) := (ENNReal.rpow_mul S (q / p) (1 / q)).symm
    _ = S ^ (1 / p) := by
        congr 1
        field_simp

/-
# The elementary `r → 2` reduction of the chain half of the variational norm

`V^r(a) = sup_k ‖a_k‖ + sup over monotone chains (Σ_i |a(t_{i+1}) − a(t_i)|^r)^{1/r}` is the
`r`-variational norm (`PointwiseErgodicTheorems.variationalNorm`).  For `2 ≤ r` the *chain* half with
exponent `r` is at most the chain half with exponent `2`, because on a finite vector
`‖x‖_{ℓ^r} ≤ ‖x‖_{ℓ²}` for `r ≥ 2`.

The statement below writes both halves out explicitly, with the same `⨆ (J : ℕ) (N : ℕ → ℕ)
(_ : Monotone N)` and `Fin J` shape as the definition, so that the conclusion is exactly
"`V^r(a) ≤ sup_k ‖a_k‖ + (chain part of V^2)`".

This replaces the *false* lemma `V^r(a) ≤ C (sup_k‖a_k‖ + V^r(Δa))` (refuted by the triangular wave
with `J` legs of length `L`: `V^r(a) ≥ L J^{1/r}` while `sup|a| + V^r(Δa) ≈ L + 2J^{1/r}`).  The
present statement is the only correct elementary handle; it is elementary and true.  Useful route:
the chain term of `variationalNorm` is `ENNReal.ofReal ‖WithLp.toLp r v‖` (`Work.KMTAreas.A7.ofReal_norm_toLp`
in `variationalNorm_le_sqSum.lean`), and `‖v‖_{WithLp r} ≤ ‖v‖_{WithLp 2}` for `r ≥ 2`
(`PiLp.norm_eq_sum` plus the `ℓ^r ⊆ ℓ²` comparison), then pass through the shared `⨆`.
-/
theorem supChainSq {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a ≤
      (⨆ k : ℕ, ‖a k‖ₑ) + ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
        (∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  refine add_le_add le_rfl ?_
  simp only [Submission.PointwiseErgodicTheorems.varPart]
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  rw [Work.KMTAreas.A7.ofReal_norm_toLp r hr J (fun i : Fin J => a (N (i + 1)) - a (N i))]
  refine le_trans (sum_rpow_le_sum_rpow'
    (fun i : Fin J => ‖a (N (i + 1)) - a (N i)‖ₑ) (p := 2) (q := (r : ℝ))
    (by norm_num) h2r) ?_
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))

end Work.KMTAreas.A7Lpd
