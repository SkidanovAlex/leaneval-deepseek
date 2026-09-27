import Mathlib
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.gapA.slabDefs

/-!
# The Fermi slab about the standard geodesic is the image of a box

For the standard geodesic stratum of `ℍ³` (`stdTG 1 2`, the first coordinate axis in the
Fermi chart `fermi 1 2`), the slab

  `{x : E 3 | s ≤ arsinh (tpart x) < s + L, ‖nrmC 1 2 x‖ ≤ R}`

is the image under the Fermi chart of the product of the interval
`{v : E 1 | sinh s ≤ v 0 < sinh (s + L)}` in the axis coordinate and the closed ball of
radius `R` in the normal fibre.

The only mathematical content is that `fermiInv 1 2` is a bijection (`Work.Mostow.fermi_inv`)
together with the change of variable `arsinh y ∈ Ico s (s+L) ↔ y ∈ Ico (sinh s) (sinh (s+L))`
for the strictly monotone `Real.sinh`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow

/-- Change of variable through `arsinh`: since `Real.sinh` is strictly increasing with inverse
`Real.arsinh`, membership in a half-open interval transports across the two. -/
private lemma arsinh_mem_Ico_iff (s L y : ℝ) :
    Real.arsinh y ∈ Set.Ico s (s + L) ↔
      y ∈ Set.Ico (Real.sinh s) (Real.sinh (s + L)) := by
  rw [Set.mem_Ico, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← Real.sinh_arsinh y]; exact Real.sinh_le_sinh.mpr h1,
           by rw [← Real.sinh_arsinh y]; exact Real.sinh_lt_sinh.mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Real.sinh_le_sinh.mp (by rwa [Real.sinh_arsinh]),
           Real.sinh_lt_sinh.mp (by rwa [Real.sinh_arsinh])⟩

theorem fermiSlabImage (s L R : ℝ) :
    {x : Submission.Mostow.E 3 |
        Real.arsinh ((Submission.Mostow.fermiInv 1 2 x).1 0) ∈ Set.Ico s (s + L) ∧
        ‖(Submission.Mostow.fermiInv 1 2 x).2‖ ≤ R}
      = (fun p : Submission.Mostow.E 1 × Submission.Mostow.E 2 =>
            Submission.Mostow.fermi 1 2 p.1 p.2) ''
          ({v : Submission.Mostow.E 1 | v 0 ∈ Set.Ico (Real.sinh s) (Real.sinh (s + L))}
            ×ˢ Metric.closedBall (0 : Submission.Mostow.E 2) R) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Metric.mem_closedBall,
    dist_zero_right]
  constructor
  · -- `x` itself is the image of its Fermi coordinates
    rintro ⟨h1, h2⟩
    exact ⟨((fermiInv 1 2 x).1, (fermiInv 1 2 x).2), ⟨(arsinh_mem_Ico_iff s L _).mp h1, h2⟩,
      (Work.Mostow.fermi_inv 1 2).2.1 x⟩
  · -- any preimage of `x` is its Fermi coordinates, by injectivity of `fermi`
    rintro ⟨⟨v, w⟩, ⟨hv, hw⟩, hferm⟩
    rw [← hferm, (Work.Mostow.fermi_inv 1 2).1 v w]
    exact ⟨(arsinh_mem_Ico_iff s L (v 0)).mpr hv, hw⟩

end Work.Mostow.gapA
