import Mathlib
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.backward_puiseux

namespace Work.EQ

/-- **The F3 branch families are meromorphic at `0`.**

`Work.EQ.backward_puiseux` produces, for an analytic end `c` on `ball u₀ R` and a length `N`, the
families `branchPt a c u₀ R σ t j` of backward `EqRelC`-chains of length `N` ending at
`c (u₀ + t ^ (2^N))`, indexed by the sign sequence `σ` and the parameter `t` in a punctured disc.
`branchPt a c u₀ R σ t j` is *defined* as `Xf a c u₀ R (sigmaExtN σ) (N - j) (t ^ (2^j))`, and
`Work.EQ.XProps_of_good` already provides meromorphicity at `0` of every `Xf` level; composing with
the monomial `t ↦ t ^ (2^j)` (`MeromorphicAt.comp_analyticAt` with `Work.EQ.analyticAt_pow_id`)
gives the claim.

This is used by `Work.EQ.H0_path_limit` to take limits of the branch families in the Riemann
sphere. -/
theorem branchPt_meromorphic {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R)) {σ : Fin N → Bool} (hσ : Work.EQ.Adm a c u₀ R σ)
    (j : Fin (N + 1)) :
    MeromorphicAt (fun t : ℂ => (Work.EQ.branchPt a c u₀ R σ t j).1) 0 ∧
    MeromorphicAt (fun t : ℂ => (Work.EQ.branchPt a c u₀ R σ t j).2) 0 := by
  have hP := XProps_of_good hR hc (sigmaExtN σ) (N - (j : ℕ))
    (hasGood_of_adm hσ (N - (j : ℕ)) (Nat.sub_le _ _))
  have hfst : (fun t : ℂ => (branchPt a c u₀ R σ t j).1)
      = (fun v : ℂ => (Xf a c u₀ R (sigmaExtN σ) (N - (j : ℕ)) v).1)
        ∘ (fun z : ℂ => z ^ (2 ^ (j : ℕ))) := by
    funext t
    simp only [Function.comp_apply, branchPt]
  have hsnd : (fun t : ℂ => (branchPt a c u₀ R σ t j).2)
      = (fun v : ℂ => (Xf a c u₀ R (sigmaExtN σ) (N - (j : ℕ)) v).2)
        ∘ (fun z : ℂ => z ^ (2 ^ (j : ℕ))) := by
    funext t
    simp only [Function.comp_apply, branchPt]
  rw [hfst, hsnd]
  exact ⟨MeromorphicAt.comp_analyticAt (x := (0 : ℂ))
      (g := fun z : ℂ => z ^ (2 ^ (j : ℕ))) (by simpa using hP.hm1) (analyticAt_pow_id (2 ^ (j : ℕ))),
    MeromorphicAt.comp_analyticAt (x := (0 : ℂ))
      (g := fun z : ℂ => z ^ (2 ^ (j : ℕ))) (by simpa using hP.hm2) (analyticAt_pow_id (2 ^ (j : ℕ)))⟩

end Work.EQ
