import Mathlib
import Submission.Work.EQ.ShiftCluster
import Submission.Work.EQ.H0_no_convergence
import Submission.Work.EQ.H0_hyperbolic
import Submission.Work.EQ.H0_regular_aux

/-!
# Step 4 of Rychlik's Theorem 11: the shifted cluster set along a good ray is uncountable

Combining `Work.EQ.not_tendsto_psi1_of_covering_ray` (the path-limit dichotomy says that `ψ₁`
cannot converge along a good radius of the disc cover of a component of `H0`) with
`Work.EQ.not_countable_shiftClusterSet` (the image of a non-convergent path in the torus
`ℂ*/λ^ℤ` has uncountably many shifted cluster points in the annulus `A(r₁,r₂)`, `r₁ ≤ λ r₂`):

**along a good ray, the set of limits of the shifted `ψ₁`-values `λ^{p_k} ψ₁(γ(s_k))` inside the
annulus `A(r₁,r₂)` is uncountable** (Rychlik (140)).

This is the input for the final contradiction of Theorem 11, where each such limit point gives a
chain of `H0` whose `ψ`-value is (approximately) the good limit `c₀`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Filter _root_.Topology Complex Metric

namespace Work.EQ

/-- **Step 4, quantitative form (Rychlik (140)).**  Let `q : 𝔻 → S` be a covering of a component
`S` of `H0`, `θ` a good direction (the `ψ`-limit `c₀ ≠ 0` exists along the radius and `c₀⁻¹` avoids
the set `L` of puncture values), and let `r₁ ≤ eqLam a · r₂`.  If the path-limit dichotomy `hpath`
holds, then `ψ₁` has no limit along the radius; consequently the set of shifted cluster points
`λ^{pₖ} ψ₁(γ(sₖ))` in the annulus `{r₁ ≤ ‖z‖ ≤ r₂}` is uncountable. -/
theorem not_countable_shiftClusterSet_of_good_ray {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {h : ℂ → ℂ} {P : H0 a h} {q : Disc → ↥(connectedComponent P)} (hq : IsCoveringMap q)
    {θ : ℝ} {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    (hlim : Tendsto (fun r : ℝ => psiC (q (discRay θ r))) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      (nhds c₀))
    {L : Set ℂ} (hL : c₀⁻¹ ∈ L → False)
    (hpath : ∀ (γ : ℝ → ChainData) (u v : ℂ), u ≠ 0 → v ≠ 0 →
      (∀ r : ℝ, r ∈ Set.Iio (1 : ℝ) → γ r ∈ H0 a h) →
      ContinuousOn γ (Set.Iio (1 : ℝ)) →
      Tendsto (fun r : ℝ => (γ r).2.1) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds u) →
      Tendsto (fun r : ℝ => (γ r).2.2) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds v) →
      (∃ p ∈ H0 a h, Tendsto γ (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds p)) ∨ (u * v)⁻¹ ∈ L)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ ≤ eqLam a * r₂) :
    ¬ Set.Countable {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ ∧
        ∃ s : ℕ → ℝ, Tendsto s atTop (nhdsWithin 1 (Set.Iio (1 : ℝ))) ∧
        ∃ p : ℕ → ℤ, Tendsto (fun k => (eqLam a : ℂ) ^ (p k) *
          (((q (discRay θ (s k)) : H0 a h)) : ChainData).2.1) atTop (nhds z)} := by
  have hne : ∀ s ∈ Set.Iio (1 : ℝ), (((q (discRay θ s) : H0 a h)) : ChainData).2.1 ≠ 0 :=
    fun s _ => psi1_ne_zero_of_mem (q (discRay θ s) : H0 a h).2
  have hcont : ContinuousOn (fun s : ℝ => (((q (discRay θ s) : H0 a h)) : ChainData).2.1)
      (Set.Iio (1 : ℝ)) := by
    have h1 : Continuous fun x : ↥(H0 a h) => (x : ChainData).2.1 := by fun_prop
    exact (h1.comp ((continuous_subtype_val :
      Continuous fun x : ↥(connectedComponent P) => (x : H0 a h)).comp hq.continuous)).continuousOn.comp
      (continuousOn_discRay θ) (fun r _ => Set.mem_univ _)
  have hnolim : ¬ ∃ z : ℂ, z ≠ 0 ∧
      Tendsto (fun s : ℝ => (((q (discRay θ s) : H0 a h)) : ChainData).2.1)
        (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds z) := by
    rintro ⟨z, hz, hzlim⟩
    exact not_tendsto_psi1_of_covering_ray hq hc₀ hz hlim hzlim hL hpath
  have hl0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hl1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  exact not_countable_shiftClusterSet hl0 hl1 hr₁ hr hne hcont hnolim

end Work.EQ
