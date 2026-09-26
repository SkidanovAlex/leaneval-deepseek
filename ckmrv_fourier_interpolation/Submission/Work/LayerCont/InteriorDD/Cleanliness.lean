/-
# The contour is pole-free in the interior of `𝒟` off the imaginary axis

The first isolated piece of the divisor-chain dominance feeding
`Work.Asymptotics.GoodAt`/`goodAt_of_contour_bound` is its **cleanliness** input: for `z` in a ball
around `τ₀ ∈ 𝒟` with `Re τ₀ ≠ 0`, the contour `t ↦ i t` meets no `SL(2,ℤ)`-translate of `z`, so
`z ↦ K(z, i t)` is holomorphic at `z` — i.e. the third hypothesis of `goodAt_of_contour_bound` holds
for *every* `t > 0`, not merely a.e.

The proof is two library facts:
* `Work.Asymptotics.orbit_imagAxis_of_mem_DomainD` : if a translate of `z ∈ 𝒟` is purely imaginary
  then `z.re = 0`;
* `Work.Asymptotics.jInvariantFun_eq_smul_of_eq` : `j τ = j w` iff `w` is an `SL(2,ℤ)`-translate
  of `τ`.
-/
import Mathlib
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.InteriorDD

open Work.Asymptotics Work.Kernels

/-- **Cleanliness in the interior of `𝒟` off the imaginary axis.**  For `z ∈ 𝒟` with `Re z ≠ 0`
and every `t > 0`, the point `z` is not in the `SL(2,ℤ)`-orbit of `i t` — equivalently
`j z ≠ j (i t)`, which is exactly the statement that `w ↦ K(w, i t)` is holomorphic at `w = z`. -/
theorem jInvariantFun_ne_imagAxis_of_mem_DomainD {z : UpperHalfPlane}
    (hz : z ∈ Work.Asymptotics.DomainD) (hre : z.re ≠ 0) (t : ℝ) (ht : 0 < t) :
    Work.Kernels.jInvariantFun z ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro hj
  -- `i t` is an `SL(2,ℤ)`-translate of `z`
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  -- so `γ⁻¹ • z = i t` is purely imaginary
  have h1 : ((γ⁻¹ • z : UpperHalfPlane) : ℂ) = ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) := by
    rw [← hγ]; simp
  have h2 : ((γ⁻¹ • z : UpperHalfPlane) : ℂ).re = 0 := by
    rw [h1, Work.Kernels.imagAxis]
    simp
  exact hre (Work.Asymptotics.orbit_imagAxis_of_mem_DomainD z hz γ⁻¹ h2)

end Work.LayerCont.InteriorDD
