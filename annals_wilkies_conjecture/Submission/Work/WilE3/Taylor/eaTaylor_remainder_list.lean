import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.eaTaylor_remainder
import Submission.Work.WilE3.Taylor.E3_remainder_uniform

namespace Work.WilE3.Taylor

open Filter Topology WilkiesDesign.E

/-- The effective Taylor remainder of `Work.WilE3.API.eaTaylor_remainder`, made uniform over an
*arbitrary finite list* `l` of EA polynomials: the same generalization as
`Work.WilE3.Taylor.E3_remainder_uniform` but for a bare list rather than the strict-inequality list
`B.pos` of a basic set, and with a general order `N`.  Since `l` is finite, the finitely many
individual constants `C Q` and neighbourhoods furnished by `eaTaylor_remainder` can be combined
into one constant `C` and one radius `R`. -/
theorem eaTaylor_remainder_list {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (l : List (WilkiesDesign.E.EAPoly k r)) (y : Fin k → ℝ) (N : ℕ) :
    ∃ (C R : ℝ), 0 ≤ C ∧ 0 < R ∧ ∀ Q ∈ l, ∀ w : Fin k → ℝ, dist w y < R →
      |WilkiesDesign.E.eaEval c Q w - WilkiesDesign.E.eaTaylor c Q N y w|
        ≤ C * dist w y ^ (N + 1) := by
  classical
  -- For each individual polynomial `Q` the effective remainder estimate of
  -- `Work.WilE3.API.eaTaylor_remainder` furnishes a constant `C Q`.
  have hrem : ∀ Q : EAPoly k r, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in 𝓝 y,
      |eaEval c Q w - eaTaylor c Q N y w| ≤ C * dist w y ^ (N + 1) :=
    fun Q => Work.WilE3.API.eaTaylor_remainder c Q N y
  choose C hCpos hCbound using hrem
  -- The *finite* intersection of the corresponding neighbourhoods is again a neighbourhood of `y`.
  have hmem : ∀ᶠ w in 𝓝 y, ∀ Q ∈ l.toFinset,
      |eaEval c Q w - eaTaylor c Q N y w| ≤ C Q * dist w y ^ (N + 1) :=
    (Filter.eventually_all_finset l.toFinset).mpr (fun Q _ => hCbound Q)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hmem
  -- A single constant: the sum of the finitely many individual constants; a single radius: `ε`.
  refine ⟨∑ Q ∈ l.toFinset, C Q, ε, Finset.sum_nonneg (fun Q _ => hCpos Q), hε, ?_⟩
  intro Q hQ w hw
  have hQ' : Q ∈ l.toFinset := List.mem_toFinset.mpr hQ
  have h1 : |eaEval c Q w - eaTaylor c Q N y w| ≤ C Q * dist w y ^ (N + 1) :=
    hball w (Metric.mem_ball.mpr hw) Q hQ'
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun Q _ => hCpos Q) hQ') (pow_nonneg dist_nonneg _)

end Work.WilE3.Taylor
