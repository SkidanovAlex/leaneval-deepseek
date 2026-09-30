import Mathlib
import Submission.Work.BMF.recursion.Weyl_factor
import Submission.Work.BMF.recursion.norm_sum_pow_le
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- **Power-mean inequality for the Weyl sum over residue classes.**

For `1 ≤ p` the Weyl sum splits as `Weyl k Q θ = ∑_{y < p} WeylMod p k Q y θ`
(`Weyl_eq_sum_WeylMod`), so applying the finite-sum power-mean inequality
`norm_sum_pow_le` to the `p` complex numbers `WeylMod p k Q y θ` gives

`‖Weyl k Q θ‖ ^ (2m) ≤ p ^ (2m - 1) · ∑_{y < p} ‖WeylMod p k Q y θ‖ ^ (2m)`.

The case `m = 0` is handled separately since then `2m = 0 < 1` and `norm_sum_pow_le`
does not apply; there both sides reduce to `1 ≤ p`. -/
theorem weylmod_pow_le (p k Q m : ℕ) (hp : 1 ≤ p) (θ : UnitAddTorus (Fin (k + 1))) :
    ‖Weyl k Q θ‖ ^ (2 * m) ≤ (p : ℝ) ^ (2 * m - 1) *
      ∑ y ∈ Finset.range p, ‖WeylMod p k Q y θ‖ ^ (2 * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: both sides collapse to `1 ≤ p`.
    subst hm
    simp [hp]
  · -- `m ≥ 1`, so `q := 2 * m ≥ 1` and the power-mean inequality applies.
    have hq : 1 ≤ 2 * m := by omega
    -- The Weyl sum as a sum over `Fin p` (reindexing the residue classes).
    have hWeyl : Weyl k Q θ = ∑ i : Fin p, WeylMod p k Q i θ := by
      rw [Weyl_eq_sum_WeylMod hp, Finset.sum_apply]
      exact (Fin.sum_univ_eq_sum_range (fun i => WeylMod p k Q i θ) p).symm
    have hkey := norm_sum_pow_le p (2 * m) hp hq (fun i : Fin p => WeylMod p k Q i θ)
    rw [hWeyl]
    rw [show (∑ y ∈ Finset.range p, ‖WeylMod p k Q y θ‖ ^ (2 * m))
        = ∑ i : Fin p, ‖WeylMod p k Q i θ‖ ^ (2 * m) from
      (Fin.sum_univ_eq_sum_range (fun i => ‖WeylMod p k Q i θ‖ ^ (2 * m)) p).symm]
    exact hkey

end Work.BMF.recursion
