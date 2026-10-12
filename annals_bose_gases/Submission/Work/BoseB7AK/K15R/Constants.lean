import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7AK.K15R.ChiReg_corpus
import Submission.Work.BoseB7AK.K15R.sum_inv_one_add_norm_le
import Submission.Work.BoseB7AK.K15R.sum_sem_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7AK.K15R.Constants` — the one absolute `K₀` of the chapter

`Work.BoseB7AK.K15R.K15Input` carries, besides FS's analytic rows, a block of *absolute*
constants: the χ-decay constant `Cchi` (`ChiReg`), the three lattice-sum constants
`Csum` (`Σ_n (1+‖vec n‖²)^{-26}`), `Ctail` (the same sum above a radius, decaying
as `R^{-M}`) and the scaled weighted lattice constant `Cwt`, and the chapter
constant `K₀` dominating them all.  (The ball count's constant is `1`, supplied
directly by `Work.BoseB7AK.K15R.card_le_of_vec_norm_le`.)

This module **produces** them from the corpus data alone —
`Work.BoseB7AK.K15R.ChiReg_corpus` for `Cchi`, `Work.BoseB7AK.K15R.sum_inv_one_add_norm_le`
for `Csum`, `Work.BoseB7AK.K15R.sum_inv_one_add_norm_tail` for `Ctail`,
`Work.BoseB7AK.K15R.card_le_of_vec_norm_le` for `Ccard`, `Work.BoseB7AK.K15R.sum_sem_le` for
`Cwt` — and takes `K₀` to be the maximum of the domination lower bounds.  The
result `Work.BoseB7AK.K15R.exists_constants` is the "choose the constants" step of the
honest-instance construction; nothing here looks at FS's potential or at any
instance-dependent quantity.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB7AK.K15R

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The absolute constants of the chapter exist.**  `Cchi` is the corpus χ's
decay constant at `decayOrder`, `Csum`/`Ctail` bound the two lattice sums,
`Ccard` the ball count, `Cwt` the scaled weighted lattice sum (`sum_sem_le`), and
`K₀` is at least `1` and dominates every constant it must (all four dominations
are *lower* bounds on `K₀`). -/
theorem exists_constants :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∃ Cchi Csum Ctail Cwt : ℝ,
      0 ≤ Cchi ∧ 0 ≤ Csum ∧ 0 ≤ Ctail ∧ 0 ≤ Cwt ∧
      Cchi * 8 ^ (2 * decayOrder) ≤ K₀ ∧ Cchi * (Csum + Ctail) ≤ K₀ ∧
      ChiReg corpusBox decayOrder Cchi ∧
      (∀ S : Finset (Fin 3 → ℤ),
        (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ decayOrder)⁻¹) ≤ Csum) ∧
      (∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
        (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
        (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ decayOrder)⁻¹)
          ≤ Ctail / R ^ 48) ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (kmom : Mode → ℝ³)
        (hlat : OnDualLattice ℓ kmom),
        (∑ q ∈ Work.BoseB7.excited Mode, (1 + ‖kmom q‖) ^ (-(4 : ℝ))) ≤ Cwt * ℓ ^ 3 := by
  obtain ⟨Cchi, hCchi0, hchi⟩ := ChiReg_corpus decayOrder
  obtain ⟨Csum, hCsum0, hsum⟩ := sum_inv_one_add_norm_le decayOrder (by decide)
  obtain ⟨Ctail, hCtail0, htail⟩ := sum_inv_one_add_norm_tail decayOrder 48 (by decide)
  obtain ⟨Cwt, hCwt0, hwt⟩ := sum_sem_le
  refine ⟨max 1 (max (Cchi * 8 ^ (2 * decayOrder))
      (max (Cchi * (Csum + Ctail)) (max 8 0))), ?_, ?_⟩
  · exact le_max_left _ _
  · refine ⟨Cchi, Csum, Ctail, Cwt, hCchi0, hCsum0, hCtail0,
      hCwt0, ?_, ?_, hchi, hsum, htail, hwt⟩
    · -- `Cchi · 8^{2·decayOrder} ≤ K₀`
      exact le_max_iff.mpr (Or.inr (le_max_iff.mpr (Or.inl (le_refl _))))
    · -- `Cchi · (Csum + Ctail) ≤ K₀`
      exact le_max_iff.mpr (Or.inr (le_max_iff.mpr (Or.inr
        (le_max_iff.mpr (Or.inl (le_refl _))))))
end Work.BoseB7AK.K15R
