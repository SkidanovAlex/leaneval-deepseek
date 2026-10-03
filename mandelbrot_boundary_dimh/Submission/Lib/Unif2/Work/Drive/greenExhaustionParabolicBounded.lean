import Mathlib
import Submission.Lib.Unif2.Work.Drive.WeakGreenAt
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Work.Drive.greenExhaustion_locallyBounded
import Submission.Lib.Unif2.Work.Drive.normalizedGreenExhaustion_locallyBounded
import Submission.Lib.Unif2.Work.Drive.greenExhaustion_parabolicCase

namespace Work.Drive

/-- **The parabolic branch of the normalised Green-function convergence (Kishi / Ahlfors).**

`WeakGreenAt X a` says that there is a *positive* harmonic function on `X ∖ {a}` with a unit
logarithmic pole at `a` (a "weak Green function").  The claim here is the complementary branch:
if no such function exists (`X` is parabolic at `a`), then there is an exhaustion `Ω n` of `X` by
nested relatively compact open sets with `a, x₁ ∈ Ω n` and Green functions `G n` of `Ω n` with pole
`a` (extended by `0` off `Ω n`) whose *normalised* differences `G n · - G n x₁` are uniformly bounded
on every compact subset of `X ∖ {a}`.

The exhaustion is supplied by `Work.Drive.greenExhaustion_data` (built from
`Work.SimplyConnected.ABS.green_reduction.exists_isGreenOn_precompact_superset`); the uniform bound
is the classical local boundedness of the normalised Green functions of an exhaustion (Kishi;
Ahlfors, *Conformal invariants*, Ch. 10), which holds in *both* the hyperbolic and the parabolic
case and is therefore independent of the parabolicity hypothesis `h`:

* if the family `G n` is bounded at one point off the pole, this is the Harnack argument
  `Work.Drive.greenExhaustion_hyperbolicCase`;
* otherwise `G n → +∞` at every point of `X ∖ {a}`, which is the parabolic case
  `Work.Drive.greenExhaustion_parabolicCase`. -/
theorem greenExhaustionParabolicBounded {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (a x₁ : X) (hx₁ : x₁ ≠ a)
    (h : ¬ Work.Drive.WeakGreenAt X a) :
    ∃ (Ω : ℕ → Set X) (G : ℕ → X → ℝ),
      (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, Ω n ⊆ Ω (n + 1)) ∧ (⋃ n, Ω n) = Set.univ ∧
      (∀ n, a ∈ Ω n) ∧ (∀ n, x₁ ∈ Ω n) ∧
      (∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n)) ∧
      (∀ n, ∀ x, x ∉ Ω n → G n x = 0) ∧
      (∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
        |G n x - G n x₁| ≤ C) := by
  obtain ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8⟩ := greenExhaustion_data (X := X) hX a x₁
  refine ⟨Ω, G, h1, h2, h3, h4, h5, h6, h7, h8, fun K hK hKsub => ?_⟩
  by_cases hbdd : ∃ x₀ : X, x₀ ≠ a ∧ ∃ C : ℝ, ∀ n, G n x₀ ≤ C
  · exact greenExhaustion_hyperbolicCase hx₁ h1 h2 h3 h4 h7 h8 hbdd K hK hKsub
  · refine greenExhaustion_parabolicCase hx₁ h1 h2 h3 h4 h7 h8 (fun x hx C => ?_) K hK hKsub
    by_contra hcon
    push_neg at hcon
    exact hbdd ⟨x, hx, C, hcon⟩

end Work.Drive
