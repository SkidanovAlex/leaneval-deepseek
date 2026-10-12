import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.LatFourierDefs
import Submission.Work.BoseBoxFock.lattice_cubeTail_le
import Submission.Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latticeBall_tail_le`

For a complex family `F : ℤ³ → ℂ` whose modulus is dominated by a fast-decaying weight of the
lattice momentum,

    ‖F n‖ ≤ C · (1 + ‖vec n‖²)⁻⁵²      (`vec n = 2π n`),

the sums of `‖F n‖` over the *exterior* of the lattice ball of radius `N'` are arbitrarily small
for `N'` large:

    ∀ ε > 0, ∃ N ∈ ℕ, ∀ N' ≥ N,  Σ'_{n : N' ≤ ‖latVec n‖} ‖F n‖ ≤ ε .

This is the ball-index companion of the workspace's `lattice_cubeTail_le` (truncation by the cube
`∃ i, N' < |n i|`) and drops out of the general `tail_le_of_summable` (truncation by an arbitrary
norm `Λ' ≤ k n`, `Submission.Work.BoseBoxFock.kinFT_lattice_tail_sq_lt`) with `k n = ‖latVec n‖`:
the only extra content is the passage from the real threshold `Λ` to the natural number
`N = ⌈Λ⌉₊`, via `Nat.le_ceil`.

The summability input is exactly `summable_vec_inv_one_add_norm_sq` at `k = 52 ≥ 2`: the decay
`(1 + ‖vec n‖²)⁻⁵²` is summable over `ℤ³` (the threshold for summability of the weight is
`k ≥ 2` in dimension three), and `‖F ·‖` is dominated by a constant multiple of it.

The parameter `ℓ > 0` is part of the ambient box geometry (`latVec` is the `ℤ³`-vector of the box
lattice `(2π/ℓ)ℤ³` up to the factor `2π/ℓ`); no scale enters the estimate, which is purely about
the summability of the weighted tail.
-/

namespace Work.BoseBoxFock

theorem latticeBall_tail_le {ℓ : ℝ} (hℓ : 0 < ℓ) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∑' n : Fin 3 → ℤ, if (N' : ℝ) ≤ ‖Work.BoseBoxFock.latVec n‖ then ‖F n‖ else 0) ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := hF
  -- summability of the dominating weight
  have hsum : Summable (fun n : Fin 3 → ℤ => C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
    (summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C
  -- summability of `n ↦ ‖F n‖`
  have hg : Summable (fun n : Fin 3 → ℤ => ‖F n‖) :=
    Summable.of_nonneg_of_le
      (f := fun n : Fin 3 → ℤ => C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)
      (g := fun n : Fin 3 → ℤ => ‖F n‖)
      (fun n => norm_nonneg _) (fun n => hC n) hsum
  intro ε hε
  -- the general tail lemma at the norm `k n = ‖latVec n‖`
  obtain ⟨Λ, hΛ⟩ := tail_le_of_summable (k := fun n : Fin 3 → ℤ => ‖latVec n‖)
    (f := fun n : Fin 3 → ℤ => ‖F n‖) (fun n => norm_nonneg _) hg ε hε
  refine ⟨⌈Λ⌉₊, fun N' hN' => ?_⟩
  exact hΛ (N' : ℝ) (le_trans (Nat.le_ceil Λ) (by exact_mod_cast hN'))

end Work.BoseBoxFock
