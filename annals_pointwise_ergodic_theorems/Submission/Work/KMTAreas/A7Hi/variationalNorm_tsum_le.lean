import Mathlib
import Submission.Work.KMTAreas.A7.fiberVarSamplingCoreG

namespace Work.KMTAreas.A7Hi

open scoped ENNReal NNReal BigOperators

/-! ## Auxiliary facts (local copies of the standard toolkit)

The following three facts are the standard "Young inequality for the variational norm" toolkit
(they occur, as `private` lemmas, in `A7/fiberOpVarYoung.lean`, `A7/fiberVarSamplingCoreG.lean`
and `A7Hi/FiberVarSamplingGOfSmallLnat.lean`).  We restate them here in the `A7Hi` namespace. -/

/-- Summability is transported by `WithLp.toLp` on a finite coordinate set (the topology of
`PiLp r (fun _ : Fin J => ℂ)` is the product topology, so `WithLp.toLp r` is a linear
homeomorphism). -/
private theorem summable_toLp_pi_aux {ι : Type*} (r : NNReal) (J : ℕ)
    (v : ι → Fin J → ℂ) :
    Summable (fun j => WithLp.toLp r (v j)) ↔ Summable v := by
  constructor
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv r ℂ (fun _ : Fin J => ℂ)).toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv r ℂ (fun _ : Fin J => ℂ)).symm.toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)

/-- A single scaled term of the variational `ℓ^r`-sum. -/
private theorem enorm_toLp_smul_sub_le {r : NNReal} (hr : 1 ≤ r)
    [Fact (1 ≤ (r : ℝ≥0∞))] {J : ℕ} (a : ℕ → ℂ) (N : ℕ → ℕ) (hN : Monotone N) (c : ℂ) :
    ‖WithLp.toLp r (fun i : Fin J => c * (a (N (i + 1)) - a (N i)))‖ₑ
      ≤ ‖c‖ₑ * Submission.PointwiseErgodicTheorems.varPart r a := by
  rw [← ofReal_norm]
  refine (Work.KMTAreas.A7.ofReal_norm_toLp_mul_le r hr (fun _ : Fin J => c)
    (fun i : Fin J => a (N (i + 1)) - a (N i))).trans ?_
  refine mul_le_mul' (iSup_le fun i => le_rfl) ?_
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))

/-- **Young's inequality for the variational norm.**  If every column `j ↦ k j * w j n` is
summable, then the variational norm of the family `n ↦ ∑'_j k j * w j n` is at most the
`ℓ¹`-weighted sum `∑_j ‖k j‖ * V^r(w_j)` of the variational norms of the columns, i.e. the
variational norm is subadditive and positively homogeneous with respect to a countable family of
sequences.

The supremum part of the variational norm is bounded through the unconditional inequality
`‖∑'_j b_j‖ₑ ≤ ∑'_j ‖b_j‖ₑ`; the variation part through writing the vector of `N`-differences of
the sum as the `tsum` of the vectors of the `N`-differences of the columns, for which summability
in the `ℓ^r`-topology is obtained from the finiteness of the right-hand side. -/
private theorem variationalNorm_tsum_mul_le {ι : Type*} (r : NNReal) (hr : 1 ≤ r)
    (k : ι → ℂ) (w : ι → ℕ → ℂ) (hsum : ∀ n, Summable (fun j => k j * w j n)) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => ∑' j, k j * w j n)
      ≤ ∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
  letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  by_cases htop : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j)) = ⊤
  · rw [htop]
    exact le_top
  · have hfin : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j)) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hsup : (⨆ n, ‖∑' j, k j * w j n‖ₑ) ≤ ∑' j, ‖k j‖ₑ * (⨆ n, ‖w j n‖ₑ) := by
      refine iSup_le fun n => ?_
      refine (enorm_tsum_le_tsum_enorm).trans ?_
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [enorm_mul]
      exact mul_le_mul' le_rfl (le_iSup (fun n => ‖w j n‖ₑ) n)
    have hvar : Submission.PointwiseErgodicTheorems.varPart r (fun n => ∑' j, k j * w j n)
        ≤ ∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
      refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
      set v : ι → Fin J → ℂ := fun j i => k j * w j (N (i + 1)) - k j * w j (N i) with hv
      have hpoint : ∀ i : Fin J,
          (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)) = ∑' j, v j i := by
        intro i
        refine (Summable.tsum_sub (hsum (N (i + 1))) (hsum (N i))).symm.trans
          (tsum_congr fun j => ?_)
        simp only [hv]
      have hbdd : ∀ j, ‖WithLp.toLp r (v j)‖ₑ
          ≤ ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
        intro j
        have hvj : v j = fun i : Fin J => k j * (w j (N (i + 1)) - w j (N i)) := by
          funext i
          simp only [hv]
          ring
        rw [hvj]
        exact enorm_toLp_smul_sub_le hr (w j) N hN (k j)
      have hsu : (∑' j, ‖WithLp.toLp r (v j)‖ₑ) < ⊤ := by
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hbdd) ?_
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) hfin
        calc ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)
            ≤ ‖k j‖ₑ * ((⨆ n, ‖w j n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r (w j)) :=
              mul_le_mul' le_rfl le_add_self
          _ = ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
              rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
      have hvS : Summable v :=
        (summable_toLp_pi_aux r J v).mp
          (Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.mp (ne_of_lt hsu)))
      have hF : (fun i : Fin J => (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)))
          = ∑' j, v j := by
        funext i
        rw [Pi.tsum_apply hvS]
        exact hpoint i
      calc ENNReal.ofReal ‖WithLp.toLp r
            (fun i : Fin J => (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)))‖
          = ‖∑' j, WithLp.toLp r (v j)‖ₑ := by
              rw [hF, Work.KMTAreas.A7.toLp_tsum_pi r J v hvS, ofReal_norm]
        _ ≤ ∑' j, ‖WithLp.toLp r (v j)‖ₑ := enorm_tsum_le_tsum_enorm
        _ ≤ ∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) :=
            ENNReal.tsum_le_tsum hbdd
    have hR : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j))
        = (∑' j, ‖k j‖ₑ * (⨆ n, ‖w j n‖ₑ))
          + (∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun j => by
        simp only [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add, mul_add]
    rw [hR, Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    exact add_le_add hsup hvar

/-- The `r`-variational norm (over `n`) is subadditive across an arbitrary (infinite) `ℤ`-indexed
linear combination with complex weights:

  `V^r_n (∑'_j c j * g j n) ≤ ∑'_j ‖c j‖ * V^r_n (g j n)`.

The finite-sum case is `variationalNorm_add_le` + homogeneity; the infinite case follows by
approximating with finite partial sums (no summability hypothesis is needed: if the right-hand side
is `⊤` the claim is trivial, otherwise summability follows from `‖g j n‖ ≤ V^r(g j)`). -/
theorem variationalNorm_tsum_le (r : NNReal) (hr : 1 ≤ r) (c : ℤ → ℂ) (g : ℤ → ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ, c j * g j n)
      ≤ ∑' j : ℤ, ‖c j‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => g j n) := by
  by_cases htop : (∑' j : ℤ, ‖c j‖ₑ *
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => g j n)) = ⊤
  · rw [htop]
    exact le_top
  · refine variationalNorm_tsum_mul_le r hr c g ?_
    intro n
    refine Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.mp (ne_of_lt ?_))
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) (lt_top_iff_ne_top.mpr htop)
    rw [enorm_mul]
    exact mul_le_mul' le_rfl
      (Work.KMTAreas.A7.enorm_apply_le_variationalNorm (r := r) (fun n : ℕ => g j n) n)

end Work.KMTAreas.A7Hi
