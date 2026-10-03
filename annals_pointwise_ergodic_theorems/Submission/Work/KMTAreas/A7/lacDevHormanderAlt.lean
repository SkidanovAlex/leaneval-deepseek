import Mathlib
import Submission.Work.KMTAreas.A7.LoDevHormander

namespace Work.KMTAreas.A7

/-- The discrete Hörmander condition for the linearized lacunary deviation kernels
`lacDevLin K σ U ω`, under the requested name `lacDevHormanderAlt`.

The proof is in `Submission.Work.KMTAreas.A7.LoDevHormander`
(`Work.KMTAreas.A7.LoDevHormander`, sorry-free and axiom-clean), and is re-exported here so that
consumers of this area can import the statement under this name.  Its route: the single-scale
difference of the deviation kernel obeys
`‖devKernM K m (z - y) - devKernM K m z‖ ≤ A |y| m / (m + |z|)^3`
(Schwartz decay of `K` for the bump part, the Lipschitz bound `triKernel_lip` for the triangular
part), the lacunarity of `σ` gives the cubic lacunary summation
`∑_{n ∈ U} σ n / (σ n + |x|)^3 ≤ 4 / |x|^2`, so that on `2 |y| ≤ |x|`
`‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ ≤ 4 A |y| / |x|^2` uniformly in `σ, U, ω`;
summing this over the lattice points `|x| ≥ 2 |y|` (where `∑ 1 / |x|^2 ≤ 2 / |y|`) gives the
uniform bound. -/
theorem lacDevHormanderAlt (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (y : ℤ), y ≠ 0 →
        ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
            ‖Work.KMTAreas.A7.lacDevLin K σ U ω (x - y) - Work.KMTAreas.A7.lacDevLin K σ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal C :=
  LoDevHormander K

end Work.KMTAreas.A7
