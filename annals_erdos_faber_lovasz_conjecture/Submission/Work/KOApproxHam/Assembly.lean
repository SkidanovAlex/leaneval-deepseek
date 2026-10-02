import Submission.Work.KOApproxHam.Convert

/-!
# The assembly: the two named steps imply the approximate Hamilton decomposition

This module proves the reduction that the chapter is built on:

```
Work.KOApproxHam.approxHamPackingStatement_of_clustering_and_blowUp :
    ClusteringStatement → BlowUpPackingStatement → ApproxHamPackingStatement
Work.KOApproxHam.approxHamDecompStatement_of_clustering_and_blowUp :
    ClusteringStatement → BlowUpPackingStatement → ApproxHamDecompStatement
```

The proof is the parameter bookkeeping of the two steps, with no mathematical content beyond the
choice of the numerical hierarchy:

* the range parameter of the theorem is `τ := min (1/8) (α/4)`, which is a function of `α` alone,
  so it can be fixed before `ν` and `η` are known (a robust `(ν,τ')`-expander with `τ' ≤ τ` is also
  a robust `(ν,τ)`-expander, so fixing `τ` in advance loses nothing);
* for given `ν`, the clustering parameters are `c := min (1/8) (ν/8)`,
  `dp := min (c/2) (ν/8000)`, `εp := min (dp/2) (ν/800000)` and the loss parameter is
  `γ := η/8 ≤ η/4`;
* the blow-up packing step is invoked *first* to learn its cluster-count threshold `K`, which is
  then handed to the clustering step (which can produce arbitrarily many clusters);
* for `n` above both thresholds the clustering certificate is fed to the packing step.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KOApproxHam

open Work.Deep.GKO

noncomputable section

theorem approxHamPackingStatement_of_clustering_and_blowUp
    (hA : ClusteringStatement) (hB : BlowUpPackingStatement) : ApproxHamPackingStatement := by
  intro α hα
  set τ : ℝ := min (1 / 8) (α / 8) with hτdef
  have hτpos : 0 < τ := lt_min (by norm_num) (by linarith)
  have hτ8 : τ ≤ 1 / 8 := min_le_left _ _
  have hτα8 : τ ≤ α / 8 := min_le_right _ _
  refine ⟨τ, hτpos, ?_⟩
  intro ν η hν hη hντ
  -- the clustering and packing parameters, chosen from `α`, `ν` and `η`
  have hνα8 : ν ≤ α / 8 := le_trans hντ hτα8
  have hνα : ν ≤ α := by linarith
  set γ : ℝ := min (η * α / 8) (η / 4) with hγdef
  have hγpos : 0 < γ := lt_min (by positivity) (by linarith)
  set c : ℝ := min (min (ν / 64) (α / 64)) (min (1 / 8) (γ / 4)) with hcdef
  have hcpos : 0 < c :=
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by norm_num) (by linarith))
  have hcν64 : c ≤ ν / 64 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcα64 : c ≤ α / 64 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc8 : c ≤ 1 / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcγ4 : c ≤ γ / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcν8 : c ≤ ν / 8 := by linarith
  have hcα8 : c ≤ α / 8 := by linarith
  have hc4 : c ≤ 1 / 4 := by linarith
  have hcα4 : c ≤ α / 4 := by linarith
  have h2τc : 2 * τ + c ≤ α / 2 := by linarith
  have hγη : γ ≤ η / 4 := min_le_right _ _
  have hγα : γ ≤ η * α / 8 := min_le_left _ _
  set dp : ℝ := c with hdpdef
  have hdppos : 0 < dp := by rw [hdpdef]; exact hcpos
  have hdpc : dp ≤ c := by rw [hdpdef]
  have hc2dp : c ≤ 2 * dp := by rw [hdpdef]; linarith
  have hdpα : dp ≤ α / 64 := by rw [hdpdef]; exact hcα64
  have hdpν : dp ≤ ν / 64 := by rw [hdpdef]; exact hcν64
  have hdpγ : dp ≤ γ / 4 := by rw [hdpdef]; exact hcγ4
  set εp : ℝ := min (dp / 4) (dp ^ 2 / 1000) with hεpdef
  have hεppos : 0 < εp := lt_min (by linarith) (by positivity)
  have hεpdp : εp ≤ dp := by
    have h := min_le_left (dp / 4) (dp ^ 2 / 1000 : ℝ); linarith
  have hεpdp4 : εp ≤ dp / 4 := min_le_left _ _
  have hεpsq : εp ≤ dp * dp / 100 := by
    have h := min_le_right (dp / 4) (dp ^ 2 / 1000 : ℝ)
    nlinarith [h, hdppos]
  -- the three loss hierarchies for the clustering certificate
  have hlossc : dp + εp ≤ γ := by linarith
  have hlossν : dp + εp ≤ ν / 8 := by linarith
  have hlossα : dp + εp ≤ α / 4 := by linarith
  -- the blow-up packing step is invoked first, to learn its cluster threshold
  obtain ⟨K, n₀B, hK, hn₀B, hB'⟩ :=
    hB εp dp c γ η hεppos hεpdp hεpsq hdpc hc2dp hc4 hγpos hγη hη
  -- the clustering step, with `K` clusters
  obtain ⟨n₀A, hn₀A, hA'⟩ :=
    hA α γ εp dp c ν τ hα hγpos hεppos hεpdp hdpc hc4 hlossc hlossν hlossα hν hνα hντ hτ8 h2τc
      hcν8 hcα4 K hK
  refine ⟨max n₀A n₀B, ?_⟩
  intro n hn G hG r hr hrn
  obtain ⟨k, m, hKle, hm1, hmlarge, hcert⟩ :=
    hA' n (le_trans (le_max_left _ _) hn) G hG r hr hrn
  obtain ⟨Cert⟩ := hcert
  have hγn : 4 * γ * (n : ℝ) ≤ η * (r : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : 4 * γ * (n : ℝ) ≤ 4 * (η * α / 8) * (n : ℝ) := by nlinarith [hγα, hn0]
    have h2 : 4 * (η * α / 8) * (n : ℝ) = η * (α * (n : ℝ)) / 2 := by ring
    rw [h2] at h1
    nlinarith [h1, hη.le, hrn]
  exact hB' k hKle n (le_trans (le_max_right _ _) hn) m hm1 hmlarge r G Cert hγn

/-- The two named steps imply `Work.Deep.GKO.ApproxHamDecompStatement`, the second input of the
Kühn–Osthus assembly `Work.Deep.GKO.koStatement_of_approx_and_absorption`. -/
theorem approxHamDecompStatement_of_clustering_and_blowUp
    (hA : ClusteringStatement) (hB : BlowUpPackingStatement) : ApproxHamDecompStatement :=
  approxHamDecompStatement_of_packing (approxHamPackingStatement_of_clustering_and_blowUp hA hB)

end

end Work.KOApproxHam
