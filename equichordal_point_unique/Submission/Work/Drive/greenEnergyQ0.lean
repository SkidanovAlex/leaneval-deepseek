import Mathlib
import Submission.Work.Drive.greenEnergyGlue

/-!
# The "pairing of a harmonic function vanishes" identity (the `(Q)` of the route notes)
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- `ChartDiff` is preserved by multiplication. -/
theorem ChartDiff.mul {c : OpenPartialHomeomorph X ℂ} {f g : X → ℝ} {Ω : Set X}
    (hf : ChartDiff c f Ω) (hg : ChartDiff c g Ω) : ChartDiff c (f * g) Ω := by
  intro x hx
  exact (hf x hx).mul (hg x hx)

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

namespace GreenCover

variable {ι : Type*} [Fintype ι] {Ω : Set X} {a b : X} {U : Set X} (E : GreenCover ι Ω a b U)

/-- `β k` is `1` on the support of `ψ k * φ`. -/
theorem β_eq_one_of_mem {k : ι} {φ : X → ℝ} {x : X}
    (hx : x ∈ tsupport (E.ψ k * φ)) : E.β k x = 1 :=
  E.hβone k x (tsupport_mul_subset_left (f := E.ψ k) (g := φ) hx)

/-- The weight `ψ i * β k` agrees with `ψ i` on the support of `ψ k * φ`. -/
theorem ψ_mul_β_eq_ψ_of_mem {i k : ι} {φ : X → ℝ} {x : X}
    (hx : x ∈ tsupport (E.ψ k * φ)) : E.ψ i x * E.β k x = E.ψ i x := by
  rw [E.β_eq_one_of_mem hx, mul_one]

/-- `∑ i, ψ i = 1` on the support of `ψ k * φ`. -/
theorem sum_ψ_eq_one_of_mem {k : ι} {φ : X → ℝ} {x : X} (hφU : tsupport φ ⊆ U)
    (hx : x ∈ tsupport (E.ψ k * φ)) : ∑ i, E.ψ i x = 1 :=
  E.hsum x (hφU (tsupport_mul_subset_right (f := E.ψ k) (g := φ) hx))

/-- The product `∑ i, ψ i * β k` equals `(∑ i, ψ i) * β k`. -/
theorem sum_ψ_mul_β_eq (k : ι) : (∑ i, E.ψ i * E.β k) = (∑ i, E.ψ i) * E.β k := by
  funext x
  simp only [Finset.sum_apply, Pi.mul_apply, Finset.sum_mul]


end GreenCover

end Work.Drive
