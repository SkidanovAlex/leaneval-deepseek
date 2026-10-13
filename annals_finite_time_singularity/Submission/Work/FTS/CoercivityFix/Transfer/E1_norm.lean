/-
# `Transfer/E1_norm` — the `ℋⁿ`-norm bound for the `D_θ`-defect of the transfer

`E1 α f = (D_θΓ)·radA α f` is the defect of the transfer identity
`D_θ(𝓛_Γ^T f) = 𝓛̂(D_θf) + E1 α f` (`Transfer/Profiles.lean`).  This file proves the quantitative
statement needed by the induction of `Transfer/stepT`:

  `∃ κ ≥ 0, ∀ α ∈ (0,1], ∀ n ≤ 3, ∀ f ∈ CoerAdm α,
     |E1 α f|_n ≤ α·κ·(|f|_n + |D_θ f|_n)`,

i.e. the defect is `α`-small in the `ℋⁿ`-norm, uniformly in `α`, `n` and `f`.

The proof squares the inequality and runs through `E1Norm.Main.E1_hkSq_le`
(`|E1 α f|²_{ℋⁿ} ≤ C·α²·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`), which is the composition of

* the product separation `E1Norm.angRad_HkSq_le` applied to the angular profile `D_θΓ` with the
  gauge `Γ·(sin²2θ + α)` (the gauge mass `1000` is `E1Norm/GaugeMass.gauge_mass`, the pointwise
  angular data is `E1Norm/Lop_iter_LopGam_Gamma_bound` and
  `E1Norm/Lop_iter_LopGam_gauge_bound`), and
* the radial bound `E1Norm.Radial.radA_sum_le` for the `D_z`-iterates of `radA α f`.

Squaring is legitimate because `HkNorm` is the square root of `HkSq`; the final step is
`Real.sqrt_le_sqrt` together with `√(x+y) ≤ √x + √y`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Main
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Coer1T.gammaPointwiseBnd_fts
import Submission.Work.FTS.CoercivityFix.Transfer.E1_blocks

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false

theorem E1_norm :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.CoercivityFix.Transfer.E1Norm.E1_hkSq_le
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro α hα hα1 n hn f hf
  have hmem : Work.Spaces.HkMem α n f :=
    Work.FTS.CoercivityFix.Transfer.E1Norm.HkMem_of_coerAdm α n hf (by omega)
  have hkey := hC α n f hα hα1 hn hf hmem
  have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hNd : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
  -- the elementary inequality `Nf + Nd ≤ (√Nf + √Nd)²`
  have hsum : Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
      ≤ (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2 := by
    have h1 := Real.sq_sqrt hNf
    have h2 := Real.sq_sqrt hNd
    have h3 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α n f) := Real.sqrt_nonneg _
    have h4 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := Real.sqrt_nonneg _
    nlinarith [h1, h2, h3, h4]
  have hbound : C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      ≤ (α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))) ^ 2 := by
    have h1 : C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        ≤ C * α ^ 2 * ((Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hCpos.le]
    ring
  calc Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
      = Real.sqrt (Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)) := rfl
    _ ≤ Real.sqrt ((α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f)))) ^ 2) :=
        Real.sqrt_le_sqrt (le_trans hkey hbound)
    _ = α * Real.sqrt C * (Real.sqrt (Work.Spaces.HkSq α n f)
          + Real.sqrt (Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        Real.sqrt_sq (by positivity)
    _ = α * Real.sqrt C * (Work.Spaces.HkNorm α n f
          + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) := rfl

end Work.FTS.CoercivityFix.Transfer
