import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.FRK.chiScale_kinFT_tail
import Submission.Work.BoseBoxFock.latticePoisson_kernel
import Submission.Work.BoseK15.sum_inv_one_add_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.hatChih_sum_le` — the uniform lattice sum of `χ̂`

A single absolute constant dominates, for **every** potential `v`, chemical potential `μ`
and lattice size `N`, the full lattice sum of `|χ̂|` over the box's momentum lattice:

    `∑_{k : Lab N} |χ̂(ℓ • kmomLab ℓ N k)| ≤ C`,     `ℓ = ellH v μ`,   `χ = corpusBox.chi`.

## Why this is true (and why the constant is uniform)

The `ℓ`-dependence cancels exactly: `kmomLab ℓ N k = ℓ⁻¹ • vec (labVec N k)` and `ℓ > 0`
(`ellH_pos`), so the argument of `χ̂` is the *dual-lattice* vector

    `ℓ • kmomLab ℓ N k = vec (labVec N k) = 2π • (labVec N k) ∈ (2π)ℤ³`,

which does not depend on `v`, `μ` or any other datum of the problem.  What remains is the
lattice sum of a rapidly decaying function over the finite cube
`labVec N '' Lab N = {-N, …, N}³ ⊆ ℤ³`.

The decay is FS's `lem:DecaychiHat` for the corpus bump, available at **every** order in
`Work.BoseK15.ChiReg_corpus` (`χ` is a `C^∞` bump with compact support): at order `3`,

    `|χ̂(p)| ≤ Cχ · (1 + ‖p‖²)^{-3}`      for all `p`,

and the lattice function `n ↦ (1 + ‖vec n‖²)^{-3}` has bounded finite sums over `ℤ³`
(`Work.BoseK15.sum_inv_one_add_norm_le 3`, proved from the `ZLattice` summability theorem,
the rank `3` being less than `4 = 2·3 - 2`).

The only structural input is the injectivity of `labVec N` — `ZMod.valMinAbs` is a *section*
of `ℤ → ZMod (2N+1)` (`ZMod.valMinAbs_inj`), so `labVec N` is injective and `Finset.sum_image`
turns the sum over `Lab N` into a sum over a finite subset of `ℤ³`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

/-- `labVec N` is injective: `ZMod.valMinAbs` is a section of the reduction
`ℤ → ZMod (2N+1)` (`ZMod.valMinAbs_inj`). -/
theorem labVec_injective (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b hab
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun hab i)

/-- **The lattice argument is `v`- and `μ`-independent**: `ℓ • kmomLab ℓ N k = vec (labVec N k)`
for `ℓ = ellH v μ` (the two `ℓ`'s cancel, `ellH_pos`). -/
theorem ellH_smul_kmomLab (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (N : ℕ)
    (k : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.ellH v μ •
        Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k
      = Work.BoseB4.vec (Work.BoseBoxFock.labVec N k) := by
  rw [Work.BoseBoxFock.kmomLab, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)), one_smul]

theorem hatChih_sum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (N : ℕ),
      ∑ k : Work.BoseBoxFock.Lab N,
        |Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)| ≤ C := by
  obtain ⟨Cχ, hCχ0, hχ⟩ := Work.BoseK15.ChiReg_corpus 3
  obtain ⟨C', _hC'0, hC'⟩ := Work.BoseK15.sum_inv_one_add_norm_le 3 (by norm_num)
  refine ⟨Cχ * C', by positivity, fun v μ N => ?_⟩
  -- the pointwise decay `|χ̂(vec (labVec N k))| ≤ Cχ (1 + ‖vec (labVec N k)‖²)^{-3}`
  have hpt : ∀ k : Work.BoseBoxFock.Lab N,
      |Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ •
          Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)|
        ≤ Cχ * (((1 : ℝ) + ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)‖ ^ 2) ^ 3)⁻¹ := by
    intro k
    rw [ellH_smul_kmomLab, ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) <
        (1 + ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)‖ ^ 2) ^ 3)).mpr
      (hχ.1 (Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)))
  calc ∑ k : Work.BoseBoxFock.Lab N,
        |Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)|
      ≤ ∑ k : Work.BoseBoxFock.Lab N,
          Cχ * (((1 : ℝ) + ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)‖ ^ 2) ^ 3)⁻¹ :=
        Finset.sum_le_sum (fun k _ => hpt k)
    _ = Cχ * ∑ k : Work.BoseBoxFock.Lab N,
          (((1 : ℝ) + ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)‖ ^ 2) ^ 3)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cχ * C' := by
        refine mul_le_mul_of_nonneg_left ?_ hCχ0
        -- replace the sum over `Lab N` by the sum over its image in `ℤ³`
        rw [← Finset.sum_image (s := Finset.univ) (g := Work.BoseBoxFock.labVec N)
          (f := fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 3)⁻¹)
          (fun _ _ _ _ hab => labVec_injective N hab)]
        exact hC' _
    _ = Cχ * C' := rfl

end Work.BoseBoxFock.PCFU
