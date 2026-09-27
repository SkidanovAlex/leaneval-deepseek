import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_regular_aux
import Submission.Work.EQ.H0_hyperbolic

/-!
# Rychlik's Theorem 11, step 4: `ψ₁` does not converge along a good ray

Let `q : 𝔻 → S` be a covering of a component `S` of `H0`.  Along a radius of the disc, suppose
that `ψ = ψ₁ψ₂` converges to `c₀ ≠ 0` (this is the "good ray" output of Fatou's theorem) and that
`ψ₁` converges to `w ≠ 0`.  Then `ψ₂` converges to `c₀/w`, so Rychlik's path-limit theorem
(`H0_path_limit`, taken here as the hypothesis `hpath`, parametrised at `1⁻`) applies: the path
either converges in `H0` — impossible, because the radius of the disc has no limit and a covering
does not create limits (`not_tendsto_comp_discRay`) — or it runs into a puncture, whose reciprocal
value `1/c₀` lies in the set `L` of puncture values, contradicting the goodness of the ray.

This is the input to the "cluster set in the torus is uncountable" step.
-/

noncomputable section

open Filter _root_.Topology Complex Metric

namespace Work.EQ

/-- **Rychlik's Theorem 11, step 4.**  `ψ₁` cannot converge along a good radius of the disc cover
of a component of `H0`. -/
theorem not_tendsto_psi1_of_covering_ray {a : ℝ} {h : ℂ → ℂ} {P : H0 a h}
    {q : Disc → ↥(connectedComponent P)} (hq : IsCoveringMap q) {θ : ℝ} {c₀ w : ℂ}
    (hc₀ : c₀ ≠ 0) (hw : w ≠ 0)
    (hlim : Tendsto (fun r : ℝ => psiC (q (discRay θ r))) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      (nhds c₀))
    (hpsi1 : Tendsto (fun r : ℝ => (((q (discRay θ r) : H0 a h)) : ChainData).2.1)
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds w))
    {L : Set ℂ} (hL : c₀⁻¹ ∈ L → False)
    (hpath : ∀ (γ : ℝ → ChainData) (u v : ℂ), u ≠ 0 → v ≠ 0 →
      (∀ r : ℝ, r ∈ Set.Iio (1 : ℝ) → γ r ∈ H0 a h) →
      ContinuousOn γ (Set.Iio (1 : ℝ)) →
      Tendsto (fun r : ℝ => (γ r).2.1) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds u) →
      Tendsto (fun r : ℝ => (γ r).2.2) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds v) →
      (∃ p ∈ H0 a h, Tendsto γ (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds p)) ∨ (u * v)⁻¹ ∈ L) :
    False := by
  set γ : ℝ → ChainData := fun r => (((q (discRay θ r) : H0 a h)) : ChainData) with hγdef
  have hγmem : ∀ r : ℝ, r ∈ Set.Iio (1 : ℝ) → γ r ∈ H0 a h :=
    fun r _ => (q (discRay θ r) : H0 a h).2
  have hγcont : ContinuousOn γ (Set.Iio (1 : ℝ)) :=
    (((continuous_subtype_val : Continuous fun x : ↥(H0 a h) => (x : ChainData)).comp
        ((continuous_subtype_val : Continuous fun x : ↥(connectedComponent P) =>
          (x : H0 a h)).comp hq.continuous)).continuousOn.comp
      (continuousOn_discRay θ) fun r _ => Set.mem_univ _)
  have hpen : Tendsto (fun r : ℝ => (γ r).2.1) (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds w) := hpsi1
  have hz : ∀ᶠ r in nhdsWithin 1 (Set.Iio (1 : ℝ)), (γ r).2.1 ≠ 0 := by
    refine hpen.eventually (isOpen_ne.mem_nhds ?_)
    simpa using hw
  have hpsi : Tendsto (fun r : ℝ => psiC (q (discRay θ r))) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      (nhds c₀) := hlim
  have hpsi' : Tendsto (fun r : ℝ => (γ r).2.1 * (γ r).2.2) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      (nhds c₀) := by
    simpa [hγdef, psiC, psi] using hpsi
  have h2 : Tendsto (fun r : ℝ => (γ r).2.2) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
      (nhds (c₀ / w)) := by
    have hdiv : Tendsto (fun r : ℝ => (γ r).2.1 * (γ r).2.2 / (γ r).2.1)
        (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (c₀ / w)) := hpsi'.div hpen hw
    refine hdiv.congr' ?_
    filter_upwards [hz] with r hr
    field_simp
  rcases hpath γ w (c₀ / w) hw (div_ne_zero hc₀ hw) hγmem hγcont hpen h2 with hconv | hpunct
  · obtain ⟨p, hp, hplim⟩ := hconv
    have hsubH : Tendsto (fun r : ℝ => (⟨γ r, (q (discRay θ r) : H0 a h).2⟩ : ↥(H0 a h)))
        (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (⟨p, hp⟩ : ↥(H0 a h))) := by
      rw [tendsto_subtype_rng]
      exact hplim
    have hpS : (⟨p, hp⟩ : ↥(H0 a h)) ∈ (connectedComponent P : Set ↥(H0 a h)) := by
      apply isClosed_connectedComponent.mem_of_tendsto hsubH
      exact Eventually.of_forall fun r => (q (discRay θ r)).2
    exact not_tendsto_comp_discRay hq θ ⟨⟨⟨p, hp⟩, hpS⟩, by
      rw [tendsto_subtype_rng, tendsto_subtype_rng]
      exact hplim⟩
  · exact hL (by rwa [mul_div_cancel₀ c₀ hw] at hpunct)

end Work.EQ
