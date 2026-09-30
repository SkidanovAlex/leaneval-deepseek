import Mathlib
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_wNorm_isLatticeNorm
import Submission.Work.BW.basisRed_bridge
import Submission.Work.BW.Minkowski2.volume_wNorm_ball
import Submission.Work.BW.Minkowski2.wNorm_bound_of_int
import Submission.Work.BW.Minkowski2.minkowski_second_lattice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Minkowski's second inequality for the weighted `ℓ¹` body

Minkowski's second inequality for the lattice `A ℤⁿ` (`A` an integer matrix with `det A ≠ 0`) and
the weighted `ℓ¹` body `{x | ∑ᵢ cᵢ |xᵢ| ≤ 1}` (`cᵢ > 0`):

`∏ j, succMin (latOf A) (wl1 c) (j+1) ≤ n! * |det A| * ∏ i, c i`.

Assembly:

* `Work.BW.basisRed_bridge` identifies the successive minima of `A ℤⁿ` with respect to `wl1 c`
  with those of `ℤⁿ` with respect to the weighted norm `wNorm A c = wl1 c ∘ A`;
* `Work.BW.Minkowski2.volume_wNorm_ball` computes the volume of the unit ball of that norm:
  `2 ^ n / (n! * (∏ i, c i) * |det A|)`;
* `Work.BW.Minkowski2.minkowski_second_lattice` is Minkowski's second inequality for the
  standard lattice `ℤⁿ` and a symmetric convex body `K`:
  `(∏ j, succMinBody (latOf 1) K (j+1)) * volume.real K ≤ 2 ^ n`;
* `Work.BW.Minkowski2.wNorm_bound_of_int` specialises it to `K = {y | wNorm A c y ≤ 1}` and
  converts `succMinBody (latOf 1)` into `succMinL (wNorm A c)`.

Dividing the second inequality by the volume of `{wNorm A c ≤ 1}` (which is
`2 ^ n / (n! * (∏ i, c i) * |det A|)`) gives the claim.
-/

namespace Work.BW

theorem minkowski_second_l1 {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∏ j : Fin n, Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) (j.1 + 1)
      ≤ (n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by
  have hbound := Minkowski2.wNorm_bound_of_int
    (fun d K hKc hsym hKcl hKbd hKi =>
      Minkowski2.minkowski_second_lattice K hKc hsym hKcl hKbd hKi)
    hn A hA c hc
  calc ∏ j : Fin n, Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) (j.1 + 1)
      = ∏ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        exact (basisRed_bridge A hA c (j.1 + 1)).symm
    _ ≤ (n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := hbound

end Work.BW
