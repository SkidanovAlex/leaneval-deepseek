import Mathlib
import Submission.Work.A7.CommonsDeps

/-!
# Vanishing order of a `conj`-symmetric function

For a function `f : ℂ → ℂ` which is invariant under the reflection
`s ↦ conj (f (conj s))` (i.e. `f` satisfies the Schwarz reflection symmetry
`conj (f (conj s)) = f s`), the order of vanishing of `f` at `ρ` and at `conj ρ`
coincide.

The proof goes through the general ("star conjugate") statement for an arbitrary
function: conjugating a holomorphic function is holomorphic, and the local
factorisation `f z = (z - z₀)^n • g z` is transported across the reflection.
-/

namespace Work.A7

open Complex Filter
open scoped Topology
open Commons.NumberTheory.DirichletCharacter (starComp)

/-- `starComp` is an involution on functions `ℂ → ℂ`. -/
lemma starComp_starComp (f : ℂ → ℂ) : starComp (starComp f) = f := by
  funext s
  simp [starComp]

/-- Pushing a filter statement through the complex conjugation homeomorphism. -/
lemma eventually_star_nhds_iff (z : ℂ) (P : ℂ → Prop) :
    (∀ᶠ u in 𝓝 z, P ((starRingEnd ℂ) u)) ↔ ∀ᶠ w in 𝓝 ((starRingEnd ℂ) z), P w := by
  constructor
  · intro h
    have hcont : Tendsto (starRingEnd ℂ) (𝓝 ((starRingEnd ℂ) z)) (𝓝 z) := by
      simpa using Complex.continuous_conj.tendsto ((starRingEnd ℂ) z)
    simpa using (hcont.eventually h)
  · intro h
    exact (Complex.continuous_conj.tendsto z).eventually h

/-- Local differentiability is preserved by the reflection `f ↦ starComp f`. -/
lemma differentiableAt_starComp_iff (f : ℂ → ℂ) (z : ℂ) :
    DifferentiableAt ℂ (starComp f) z ↔ DifferentiableAt ℂ f ((starRingEnd ℂ) z) := by
  constructor
  · intro hd
    have h1 : HasDerivAt (starComp f) (deriv (starComp f) z)
        ((starRingEnd ℂ) ((starRingEnd ℂ) z)) := by
      simpa using hd.hasDerivAt
    have h2 := Commons.NumberTheory.DirichletCharacter.hasDerivAt_star_comp h1
    rw [starComp_starComp] at h2
    exact h2.differentiableAt
  · intro hd
    have h1 : HasDerivAt f (deriv f ((starRingEnd ℂ) z)) ((starRingEnd ℂ) z) := hd.hasDerivAt
    exact (Commons.NumberTheory.DirichletCharacter.hasDerivAt_star_comp h1).differentiableAt

/-- Analyticity is preserved by the reflection `f ↦ starComp f`. -/
lemma analyticAt_starComp_iff (f : ℂ → ℂ) (z : ℂ) :
    AnalyticAt ℂ (starComp f) z ↔ AnalyticAt ℂ f ((starRingEnd ℂ) z) := by
  rw [analyticAt_iff_eventually_differentiableAt, analyticAt_iff_eventually_differentiableAt]
  simp only [differentiableAt_starComp_iff]
  exact eventually_star_nhds_iff z (fun w => DifferentiableAt ℂ f w)

/-- The vanishing order (as an element of `ℕ∞`) is preserved by the reflection
`f ↦ starComp f`, `conj`-ing the base point. -/
lemma analyticOrderAt_starComp (f : ℂ → ℂ) (z : ℂ) :
    analyticOrderAt (starComp f) z = analyticOrderAt f ((starRingEnd ℂ) z) := by
  by_cases hf : AnalyticAt ℂ f ((starRingEnd ℂ) z)
  · have hsf : AnalyticAt ℂ (starComp f) z := (analyticAt_starComp_iff f z).2 hf
    refine ENat.eq_of_forall_natCast_le_iff fun n => ?_
    rw [natCast_le_analyticOrderAt hsf, natCast_le_analyticOrderAt hf]
    constructor
    · rintro ⟨g, hga, hg⟩
      refine ⟨starComp g, (analyticAt_starComp_iff g ((starRingEnd ℂ) z)).2 (by simpa using hga), ?_⟩
      rw [← eventually_star_nhds_iff z (fun w => f w = (w - (starRingEnd ℂ) z)^n • starComp g w)]
      filter_upwards [hg] with u hu
      have := congrArg (starRingEnd ℂ) hu
      simpa [starComp, map_pow, map_mul, map_sub, smul_eq_mul] using this
    · rintro ⟨G, hGa, hG⟩
      refine ⟨starComp G, (analyticAt_starComp_iff G z).2 hGa, ?_⟩
      filter_upwards
        [(eventually_star_nhds_iff z (fun w => f w = (w - (starRingEnd ℂ) z)^n • G w)).2 hG]
        with u hu
      have := congrArg (starRingEnd ℂ) hu
      simpa [starComp, map_pow, map_mul, map_sub, smul_eq_mul] using this
  · have hsf : ¬ AnalyticAt ℂ (starComp f) z := fun hh => hf ((analyticAt_starComp_iff f z).1 hh)
    rw [analyticOrderAt_of_not_analyticAt hsf, analyticOrderAt_of_not_analyticAt hf]

theorem analyticOrderNatAt_star_symm (f : ℂ → ℂ) (h : ∀ s : ℂ, (starRingEnd ℂ) (f ((starRingEnd ℂ) s)) = f s) (ρ : ℂ) :
    analyticOrderNatAt f ((starRingEnd ℂ) ρ) = analyticOrderNatAt f ρ := by
  have hsf : starComp f = f := funext h
  have hmain := analyticOrderAt_starComp f ((starRingEnd ℂ) ρ)
  rw [hsf, starRingEnd_self_apply] at hmain
  simp only [analyticOrderNatAt, hmain]

end Work.A7
