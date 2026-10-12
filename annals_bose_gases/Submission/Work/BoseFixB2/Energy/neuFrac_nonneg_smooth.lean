import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB2.Defs
import Submission.Work.BoseFixB2.Polar.BoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.neuFrac_nonneg_smooth` — `neuFrac` is nonnegative for a smooth state

`Work.BoseKinLoc.neuFrac ℓ a² u φ` is FS `eq:DefT`'s first term, the box
Neumann-resolvent fraction, defined as the `sInf` of the Dirichlet-principle trial
functional

`T(φ,g) = ∫_{Λ} φ² − 2a²∫_{Λ} φ g + a²(Σ_k∫_{Λ}(∂_k g)² + a²∫_{Λ} g²)`,   `Λ = ℓu + [−ℓ/2,ℓ/2]³`,

over globally smooth compactly supported trials `g`.

The nonnegativity is an elementary completion of the square: for every admissible `g`,

`T(φ,g) = ∫_Λ (φ − a²g)² + a²·Σ_k∫_Λ (∂_k g)²`   (up to the Bochner-integral convention
for the non-integrable case), which is `≥ 0`; the defining trial set is nonempty (`g = 0`),
hence its `sInf` is `≥ 0`.

The only hypothesis the argument really needs is that `φ²` be integrable on the box `Λ`
(that is the hypothesis of `Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2`): without it the
Bochner integral of `φ²` takes the junk value `0` and the cancellation that produces the
completion of the square is lost.  Here this integrability is supplied by the smoothness
hypothesis `ContDiff ℝ ⊤ φ`: the box `Λ = lamBox ℓ u` is compact for `ℓ > 0`, so `φ`, being
continuous, is square integrable on it
(`Work.BoseFixB2.Polar.integrableOn_sq_of_continuous`).
-/

namespace Work.BoseFixB2.Energy

/-- **The box Neumann-resolvent fraction `neuFrac` is nonnegative** for a smooth state `φ`,
`a² ≥ 0` and `ℓ > 0`.

Smoothness of `φ` makes `(φ z)²` integrable on the compact box `lamBox ℓ u`
(`Work.BoseFixB2.Polar.integrableOn_sq_of_continuous`), and the infimum is then `≥ 0`
because every admissible trial value is nonnegative by completing the square under the box
integral (`Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2`). -/
theorem neuFrac_nonneg_smooth {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2) (u : EuclideanSpace ℝ (Fin 3)) {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : 0 ≤ Work.BoseKinLoc.neuFrac ℓ a2 u φ :=
  Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2 ℓ a2 ha2 u φ
    (Work.BoseFixB2.Polar.integrableOn_sq_of_continuous hℓ u hφ.continuous)

end Work.BoseFixB2.Energy
