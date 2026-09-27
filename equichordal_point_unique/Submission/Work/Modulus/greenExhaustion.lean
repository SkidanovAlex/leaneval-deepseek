import Mathlib
import Submission.Work.Modulus.Defs
import Submission.Work.Modulus.growth_of_unitGreen

/-!
# The Green function is bounded below by a positive constant on compacta

If `E : X → ℝ` is a Green function with pole `z₀` in the sense of
`Work.UnitGreen.IsUnitGreenFunctionAt` — positive and harmonic off `z₀`, with a logarithmic pole of
coefficient one there, and with relatively compact superlevel sets — then for every compact `K ⊆ X` there is
`ε > 0` with `ε ≤ E x` for every `x ∈ K`, `x ≠ z₀`.

Equivalently: the level sets `{x | E x < ε}` of a Green function escape to the *pole*, i.e. their
closures can only accumulate at `z₀`.  (In the intended application the level sets are the
exhausting family `{x | E x < ε}` whose closures are compact away from `z₀`, and one wants them to
be *nested with closure* inside the next one, which is exactly the statement that `E` is bounded
away from `0` on a compactum.)

The proof uses only three of the four pieces of data:

* positivity of `E` off the pole (`E x > 0` for `x ≠ z₀`);
* harmonicity off the pole, hence continuity off the pole (`HarmonicOnXAt.continuousAt`);
* the blow-up `E x → +∞` at `z₀`.

Fix a level `A = 1`.  The blow-up gives a neighbourhood `V` of `z₀` with `E > 1` on `V ∖ {z₀}`,
and then an *open* `O ⊆ V` with `z₀ ∈ O`.  On `K ∖ O` — a compact set, being a closed subset of the
compact `K`, disjoint from the pole — the continuous function `E` attains a minimum, which is
positive by positivity of `E` off the pole.  Therefore `ε = min (E on K ∖ O) 1 > 0` is a valid
lower bound: points of `K ∖ O` are handled by the minimum, and points of `K ∩ O` are not the pole
and satisfy `E > 1 ≥ ε`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A Green function is bounded below by a positive constant on compacta avoiding the pole.**

For every compact `K ⊆ X` there is `ε > 0` such that `ε ≤ E x` for all `x ∈ K`, `x ≠ z₀`. -/
theorem greenExhaustion
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    ∀ K : Set X, IsCompact K → ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, x ≠ z₀ → ε ≤ E x := by
  intro K hK
  obtain ⟨⟨hpos, hharm, _⟩, ⟨C₀, V₀, hV₀, hbnd₀⟩⟩ := hE
  have hgrowth : ∀ A : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ → A < E x :=
    growth_of_unitGreen hV₀ hbnd₀
  -- the level `1` of the blow-up at the pole, together with an open neighbourhood of the pole
  obtain ⟨V, hVn, hVgrow⟩ := hgrowth 1
  obtain ⟨O, hOV, hOopen, hzO⟩ := mem_nhds_iff.mp hVn
  -- `K ∖ O` is compact and disjoint from the pole, so `E` is continuous there
  have hKO : IsCompact (K \ O) := hK.diff hOopen
  have hcont : ContinuousOn E (K \ O) := by
    rintro x ⟨-, hxO⟩
    exact (hharm x ⟨Set.mem_univ x, fun h => hxO (by rw [h]; exact hzO)⟩).continuousAt.continuousWithinAt
  by_cases hne : (K \ O).Nonempty
  · -- `E` attains a positive minimum on `K ∖ O`
    obtain ⟨y, hy, hymin⟩ := hKO.exists_isMinOn hne hcont
    have hyne : y ≠ z₀ := fun h => hy.2 (by rw [h]; exact hzO)
    have hypos : 0 < E y := hpos y hyne
    refine ⟨min (E y) 1, lt_min hypos one_pos, fun x hxK hxne => ?_⟩
    by_cases hxO : x ∈ O
    · have h1 : 1 < E x := hVgrow x (hOV hxO) hxne
      exact le_trans (min_le_right _ _) h1.le
    · exact le_trans (min_le_left _ _) (hymin ⟨hxK, hxO⟩)
  · -- otherwise `K ⊆ O` and `E > 1` on all of `K ∖ {z₀}`
    refine ⟨1, one_pos, fun x hxK hxne => ?_⟩
    have hxO : x ∈ O := by
      by_contra h
      exact hne ⟨x, hxK, h⟩
    exact (hVgrow x (hOV hxO) hxne).le

end Work.Modulus
