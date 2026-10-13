import Mathlib
import Submission.Work.WilE3.API.eaTaylor_remainder

namespace Work.WilE3.Taylor

open Filter Topology WilkiesDesign.E

/-- The effective Taylor remainder of `Work.WilE3.API.eaTaylor_remainder`, made uniform over the
*finitely many* strict inequalities `g ∈ B.pos` of a basic set: one constant `Crew` and one radius
`R` that work for all of them.  Used in the `(⇐)` direction of `E3_taylor_closure` to show that
moving a point `x` of the Taylor set to a nearby point `z` of the zero set `Z` of the equations does
not destroy the strict inequalities `g > 0` (the remainder is only `O (dist (·,y)^{κ+1})`). -/
theorem E3_remainder_uniform {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (B : WilkiesDesign.E.Basic k r) (y : Fin k → ℝ) (κ : ℕ) :
    ∃ (Crew R : ℝ), 0 ≤ Crew ∧ 0 < R ∧ ∀ g ∈ B.pos, ∀ w : Fin k → ℝ, dist w y < R →
      |WilkiesDesign.E.eaEval c g w - WilkiesDesign.E.eaTaylor c g κ y w|
        ≤ Crew * dist w y ^ (κ + 1) := by
  classical
  -- For each individual polynomial `Q` the effective remainder estimate of
  -- `Work.WilE3.API.eaTaylor_remainder` furnishes a constant `C Q`.
  have hrem : ∀ Q : EAPoly k r, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in 𝓝 y,
      |eaEval c Q w - eaTaylor c Q κ y w| ≤ C * dist w y ^ (κ + 1) :=
    fun Q => Work.WilE3.API.eaTaylor_remainder c Q κ y
  choose C hCpos hCbound using hrem
  -- The *finite* intersection of the corresponding neighbourhoods is again a neighbourhood of `y`.
  have hmem : ∀ᶠ w in 𝓝 y, ∀ g ∈ B.pos.toFinset,
      |eaEval c g w - eaTaylor c g κ y w| ≤ C g * dist w y ^ (κ + 1) :=
    (Filter.eventually_all_finset B.pos.toFinset).mpr (fun g _ => hCbound g)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hmem
  -- A single constant: the sum of the finitely many individual constants; a single radius: `ε`.
  refine ⟨∑ g ∈ B.pos.toFinset, C g, ε, Finset.sum_nonneg (fun g _ => hCpos g), hε, ?_⟩
  intro g hg w hw
  have hgw : g ∈ B.pos.toFinset := List.mem_toFinset.mpr hg
  have h1 : |eaEval c g w - eaTaylor c g κ y w| ≤ C g * dist w y ^ (κ + 1) :=
    hball w (Metric.mem_ball.mpr hw) g hgw
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun g _ => hCpos g) hgw) (pow_nonneg dist_nonneg _)

end Work.WilE3.Taylor
