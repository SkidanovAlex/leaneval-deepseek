import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E5G.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

set_option linter.unusedVariables false

/-- **Pointwise convergence plus a uniform `1/2`-Hölder bound on a compact set gives a uniform
bound on that set.**

Fix a point `q₀` of the compact set `K ⊆ Q0`.  Each slot `D_z^jD_θ^i (V n)` is `1/2`-Hölder with a
constant `C` that is uniform in `n` on `K` (`hequi`), whence for `p ∈ K`

`|D_z^jD_θ^i (V n) p| ≤ |D_z^jD_θ^i (V n) p - D_z^jD_θ^i (V n) q₀| + |D_z^jD_θ^i (V n) q₀|
 ≤ C · dist p q₀ ^ (1/2) + |D_z^jD_θ^i (V n) q₀| ≤ C · r ^ (1/2) + M`,

where `r` bounds `dist p q₀` (`p ∈ K`, `K` bounded) and `M` bounds the convergent sequence
`n ↦ D_z^jD_θ^i (V n) q₀` (`hconv`; a convergent sequence of reals is bounded). -/
theorem pointwise_bound_of_tendsto_of_equiholder {V : ℕ → Work.FTS.Galerkin.Fn}
    {Φ : Work.FTS.Galerkin.Fn} (j i : ℕ)
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hconv : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds (Φ q.1 q.2)))
    (hΦc : ContinuousOn (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2| ≤ C := by
  intro K hK hKQ0
  by_cases hKne : K.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hKne
    obtain ⟨Ce, hCe, hequiK⟩ := hequi K hK hKQ0
    -- The sequence of values at the fixed point `q₀` is bounded (`hconv` + boundedness of the
    -- range of a convergent sequence).
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n : ℕ,
        |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| ≤ M := by
      have h1 : Bornology.IsBounded
          (Set.range (fun n => Work.Spaces.mixed j i (V n) q₀.1 q₀.2)) :=
        Metric.isBounded_range_of_tendsto _ (hconv q₀ (hKQ0 hq₀))
      obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.1 h1
      refine ⟨C + |Work.Spaces.mixed j i (V 0) q₀.1 q₀.2|, fun n => ?_⟩
      have h2 : dist (Work.Spaces.mixed j i (V n) q₀.1 q₀.2)
          (Work.Spaces.mixed j i (V 0) q₀.1 q₀.2) ≤ C := hC n 0
      rw [Real.dist_eq] at h2
      have h3 : |Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
          ≤ |Work.Spaces.mixed j i (V n) q₀.1 q₀.2 - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2|
            + |Work.Spaces.mixed j i (V 0) q₀.1 q₀.2| := by
        have hsub : Work.Spaces.mixed j i (V n) q₀.1 q₀.2
            - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2
            + Work.Spaces.mixed j i (V 0) q₀.1 q₀.2
            = Work.Spaces.mixed j i (V n) q₀.1 q₀.2 := sub_add_cancel _ _
        calc |Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
            = |Work.Spaces.mixed j i (V n) q₀.1 q₀.2 - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2
                + Work.Spaces.mixed j i (V 0) q₀.1 q₀.2| := by rw [hsub]
          _ ≤ |Work.Spaces.mixed j i (V n) q₀.1 q₀.2 - Work.Spaces.mixed j i (V 0) q₀.1 q₀.2|
                + |Work.Spaces.mixed j i (V 0) q₀.1 q₀.2| := abs_add_le _ _
      linarith
    -- `K` is contained in a closed ball around `q₀`.
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall q₀
    refine ⟨max 0 (Ce * r ^ (1 / 2 : ℝ) + M), le_max_left _ _, fun n p hp => ?_⟩
    have h1 : |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
        ≤ Ce * dist p q₀ ^ (1 / 2 : ℝ) := hequiK n p hp q₀ hq₀
    have hpK : dist p q₀ ≤ r := Metric.mem_closedBall.mp (hr hp)
    have h2 : dist p q₀ ^ (1 / 2 : ℝ) ≤ r ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow dist_nonneg hpK (by norm_num)
    have h3 : Ce * dist p q₀ ^ (1 / 2 : ℝ) ≤ Ce * r ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hCe
    have h4 : |Work.Spaces.mixed j i (V n) p.1 p.2|
        ≤ |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
          + |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| := by
      have hsub : Work.Spaces.mixed j i (V n) p.1 p.2
          - Work.Spaces.mixed j i (V n) q₀.1 q₀.2 + Work.Spaces.mixed j i (V n) q₀.1 q₀.2
          = Work.Spaces.mixed j i (V n) p.1 p.2 := sub_add_cancel _ _
      calc |Work.Spaces.mixed j i (V n) p.1 p.2|
          = |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2
              + Work.Spaces.mixed j i (V n) q₀.1 q₀.2| := by rw [hsub]
        _ ≤ |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q₀.1 q₀.2|
              + |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| := abs_add_le _ _
    have h5 : |Work.Spaces.mixed j i (V n) q₀.1 q₀.2| ≤ M := hM n
    have h6 : Ce * r ^ (1 / 2 : ℝ) + M ≤ max 0 (Ce * r ^ (1 / 2 : ℝ) + M) := le_max_right _ _
    linarith
  · exact ⟨0, le_refl 0, fun n p hp => absurd ⟨p, hp⟩ hKne⟩

end Work.FTS.StrongEps.E5G
