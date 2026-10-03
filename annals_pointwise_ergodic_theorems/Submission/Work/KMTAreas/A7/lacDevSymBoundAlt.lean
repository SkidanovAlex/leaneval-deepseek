/-
# The uniform symbol bound for the linearised deviation kernel, requested form

`Work.KMTAreas.A7.lacDevSymBoundAlt`: for a Schwartz kernel `K` there is a constant `C` such that
for *every* `2`-lacunary scale sequence `σ` (with `1 ≤ σ n`), every finite index set `U`, every sign
pattern `ω` and every frequency `θ`,

  `‖∑'_j lacDevLin K σ U ω j · e^{2πi j θ}‖ ≤ C`.

This is the uniform `ℓ^∞` bound for the symbol of the linearised deviation family — the
Littlewood–Paley input of the square-function half of the lacunary bump-dilation variational
estimate.

The proof is `Work.KMTAreas.A7.LoDevSymBound` (in `Submission/Work/KMTAreas/A7/LoDevSymBound.lean`,
sorry-free and axiom-clean), re-exported here under the requested name so that consumers of this
area can import the statement under this name: the single-scale symbol estimates are the Poisson
summation bound `Work.KMTAreas.A7Hi.bumpSymQuad` and the Fejér bounds
`Work.KMTAreas.A7Hi.triSym_sub_one_le_zGap`/`zGap_mul_triSym_le`, and the lacunary summation is
`loLacSum` (`∑_{n ∈ U} min (σ n · s) (σ n · s)⁻¹ ≤ 4`) together with `loSumInvSqScale`
(`∑_{n ∈ U} (σ n)⁻² ≤ 2`), where `s = zGap θ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoDevSymBound

namespace Work.KMTAreas.A7

theorem lacDevSymBoundAlt (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ),
        ‖∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ‖ ≤ C :=
  LoDevSymBound K

end Work.KMTAreas.A7
