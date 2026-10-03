/-
# The variational norm is submultiplicative for the pointwise product

This module proves `Work.KMTAreas.A7.variationalNorm_mul_le`: there is a constant `C > 0` with

  `‖n ↦ u n * v n‖_{𝕍^r} ≤ C · ‖u‖_{𝕍^r} · ‖v‖_{𝕍^r}`   for every `r ≥ 1`

and every pair of sequences `u v : ℕ → ℂ`.  In fact the constant `C = 1` works; the argument is
elementary and is exactly the "product rule" for the two pieces of the variational norm
`variationalNorm r a = (⨆ n, ‖a n‖ₑ) + varPart r a`:

* the supremum part is submultiplicative (`iSup_enorm_mul_le`):
  `⨆ n ‖u n * v n‖ₑ ≤ (⨆ n ‖u n‖ₑ) · (⨆ n ‖v n‖ₑ)`;
* the variation part satisfies (`varPart_mul_le`)
  `varPart r (u·v) ≤ (⨆ n ‖v n‖ₑ) · varPart r u + (⨆ n ‖u n‖ₑ) · varPart r v`,
  which is the pointwise Leibniz rule `Δ(uv) = (Δu)·v + u·(Δv)` combined with the triangle
  inequality for the `ℓ^r` norm (`r ≥ 1`) and the fact that multiplying the entries of a vector
  by bounded scalars is a contraction of `ℓ^r` (`ofReal_norm_toLp_mul_le`).

Adding the two and expanding `(S_u + P_u)(S_v + P_v)` gives the claim with `C = 1`.

The two analytic ingredients are the following.  First, the `ℓ^r` norm of `WithLp.toLp r` is the
usual `r`-sum for `1 ≤ r` (`ofReal_norm_toLp_eq_sum`, the form in which the variational norm's
second term is written).  Second, componentwise scaling by the entries of a vector is bounded by
the `ℓ^∞` norm of the scalars (`ofReal_norm_toLp_mul_le`), which is the `ℓ^r` statement
`(∑ i ‖c i · x i‖^r)^(1/r) ≤ (⨆ i ‖c i‖) (∑ i ‖x i‖^r)^(1/r)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems

/-- The `ℓ^r` norm (`r ≥ 1`) of a finite vector, written as the `r`-sum: the form in which the
second term of `PointwiseErgodicTheorems.variationalNorm` is stated. -/
theorem ofReal_norm_toLp_eq_sum (r : ℝ≥0) (hr : 1 ≤ r) {ι : Type*} [Fintype ι] (F : ι → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r F‖ = (∑ i : ι, ‖F i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hrt : ((r : ℝ≥0∞)).toReal = (r : ℝ) := ENNReal.coe_toReal r
  have hp : 0 < ((r : ℝ≥0∞)).toReal := by rw [hrt]; linarith
  rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) hp]
  rw [hrt]
  rw [← ENNReal.ofReal_rpow_of_nonneg
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hr0), ofReal_norm])

/-- **Componentwise scaling is a contraction of `ℓ^r` (`r ≥ 1`).**  For scalars `c` and a vector
`x` over a finite index type, `ℓ^r(c ·ₓ x) ≤ (⨆ i ‖c i‖) · ℓ^r(x)`; equivalently, for extended
norms,
`‖WithLp.toLp r (i ↦ c i * x i)‖ₑ ≤ (⨆ i, ‖c i‖ₑ) * ‖WithLp.toLp r x‖ₑ`. -/
theorem ofReal_norm_toLp_mul_le (r : ℝ≥0) (hr : 1 ≤ r) {ι : Type*} [Fintype ι]
    (c x : ι → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r (fun i => c i * x i)‖
      ≤ (⨆ i, ‖c i‖ₑ) * ENNReal.ofReal ‖WithLp.toLp r x‖ := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hrp0 : (0 : ℝ) ≤ (r : ℝ) := le_of_lt hr0
  have hdiv : (0 : ℝ) ≤ 1 / (r : ℝ) := by positivity
  rw [ofReal_norm_toLp_eq_sum r hr (fun i => c i * x i), ofReal_norm_toLp_eq_sum r hr x]
  set C : ℝ≥0∞ := ⨆ i, ‖c i‖ₑ with hC
  have hle : ∀ i : ι, ‖c i‖ₑ ≤ C := fun i => le_iSup (fun i => ‖c i‖ₑ) i
  have key : (∑ i : ι, ‖c i * x i‖ₑ ^ (r : ℝ))
      ≤ C ^ (r : ℝ) * ∑ i : ι, ‖x i‖ₑ ^ (r : ℝ) := by
    calc (∑ i : ι, ‖c i * x i‖ₑ ^ (r : ℝ))
        = ∑ i : ι, (‖c i‖ₑ * ‖x i‖ₑ) ^ (r : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [enorm_mul]
      _ = ∑ i : ι, ‖c i‖ₑ ^ (r : ℝ) * ‖x i‖ₑ ^ (r : ℝ) :=
          Finset.sum_congr rfl fun i _ => ENNReal.mul_rpow_of_nonneg _ _ hrp0
      _ ≤ ∑ i : ι, C ^ (r : ℝ) * ‖x i‖ₑ ^ (r : ℝ) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul' (ENNReal.rpow_le_rpow (hle i) hrp0) le_rfl
      _ = C ^ (r : ℝ) * ∑ i : ι, ‖x i‖ₑ ^ (r : ℝ) := (Finset.mul_sum _ _ _).symm
  have h1 : (∑ i : ι, ‖c i * x i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))
      ≤ (C ^ (r : ℝ) * ∑ i : ι, ‖x i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
    ENNReal.rpow_le_rpow key hdiv
  have h2 : (C ^ (r : ℝ) * ∑ i : ι, ‖x i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))
      = C * (∑ i : ι, ‖x i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hdiv, ← ENNReal.rpow_mul]
    rw [show (r : ℝ) * (1 / (r : ℝ)) = 1 by field_simp]
    rw [ENNReal.rpow_one]
  exact h1.trans h2.le

/-- The supremum part of the variational norm is submultiplicative for the pointwise product. -/
theorem iSup_enorm_mul_le (u v : ℕ → ℂ) :
    (⨆ n, ‖u n * v n‖ₑ) ≤ (⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ) := by
  refine iSup_le fun n => ?_
  rw [enorm_mul]
  exact mul_le_mul' (le_iSup (fun n => ‖u n‖ₑ) n) (le_iSup (fun n => ‖v n‖ₑ) n)

/-- **The variation part of the variational norm is submultiplicative for the pointwise product.**
For `r ≥ 1`,
`varPart r (u·v) ≤ (⨆ n ‖v n‖ₑ) · varPart r u + (⨆ n ‖u n‖ₑ) · varPart r v`. -/
theorem varPart_mul_le {r : ℝ≥0} (hr : 1 ≤ r) (u v : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r (fun n => u n * v n)
      ≤ (⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
        + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  show ENNReal.ofReal ‖WithLp.toLp r
      (fun i : Fin J => u (N (i + 1)) * v (N (i + 1)) - u (N i) * v (N i))‖ ≤ _
  set A : Fin J → ℂ := fun i => (u (N (i + 1)) - u (N i)) * v (N (i + 1)) with hA
  set B : Fin J → ℂ := fun i => u (N i) * (v (N (i + 1)) - v (N i)) with hB
  have hWAB : (fun i : Fin J => u (N (i + 1)) * v (N (i + 1)) - u (N i) * v (N i))
      = A + B := by
    funext i; simp only [hA, hB, Pi.add_apply]; ring
  have hA' : A = fun i : Fin J => v (N (i + 1)) * (u (N (i + 1)) - u (N i)) := by
    funext i; simp only [hA]; ring
  have hkeyA : ENNReal.ofReal ‖WithLp.toLp r A‖
      ≤ (⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u := by
    rw [hA']
    refine (ofReal_norm_toLp_mul_le r hr (fun i : Fin J => v (N (i + 1)))
      (fun i : Fin J => u (N (i + 1)) - u (N i))).trans ?_
    refine mul_le_mul' (iSup_le fun i => ?_) ?_
    · exact le_iSup (fun n => ‖v n‖ₑ) (N (i + 1))
    · exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  have hkeyB : ENNReal.ofReal ‖WithLp.toLp r B‖
      ≤ (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v := by
    refine (ofReal_norm_toLp_mul_le r hr (fun i : Fin J => u (N i))
      (fun i : Fin J => v (N (i + 1)) - v (N i))).trans ?_
    refine mul_le_mul' (iSup_le fun i => ?_) ?_
    · exact le_iSup (fun n => ‖u n‖ₑ) (N i)
    · exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  calc ENNReal.ofReal ‖WithLp.toLp r
        (fun i : Fin J => u (N (i + 1)) * v (N (i + 1)) - u (N i) * v (N i))‖
      = ENNReal.ofReal ‖WithLp.toLp r A + WithLp.toLp r B‖ := by rw [hWAB, WithLp.toLp_add]
    _ ≤ ENNReal.ofReal (‖WithLp.toLp r A‖ + ‖WithLp.toLp r B‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖WithLp.toLp r A‖ + ENNReal.ofReal ‖WithLp.toLp r B‖ :=
        ENNReal.ofReal_add (norm_nonneg (WithLp.toLp r A)) (norm_nonneg (WithLp.toLp r B))
    _ ≤ (⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
        + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v :=
        add_le_add hkeyA hkeyB

/-- **The variational norm is submultiplicative for the pointwise product**, with constant `1`. -/
theorem variationalNorm_mul_le :
    ∃ C : NNReal, 0 < C ∧ ∀ (r : NNReal) (hr : 1 ≤ r) (u v : ℕ → ℂ),
      PointwiseErgodicTheorems.variationalNorm r (fun n => u n * v n) ≤
        (C : ENNReal) * (PointwiseErgodicTheorems.variationalNorm r u *
          PointwiseErgodicTheorems.variationalNorm r v) := by
  refine ⟨1, one_pos, fun r hr u v => ?_⟩
  have hvar := varPart_mul_le hr u v
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r (fun n => u n * v n),
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r u,
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r v,
      ENNReal.coe_one, one_mul]
  calc (⨆ n, ‖u n * v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r (fun n => u n * v n)
      ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
          + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
              + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v) :=
        add_le_add (iSup_enorm_mul_le u v) hvar
    _ ≤ ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
          * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by
        calc ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
            ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
              + (Submission.PointwiseErgodicTheorems.varPart r u
                  * Submission.PointwiseErgodicTheorems.varPart r v) := le_add_right le_rfl
          _ = ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
                * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by ring

end Work.KMTAreas.A7
