/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T45Defs` — the angular factor of the pointwise bound for a `𝒲^{6,∞}`-coefficient

The level-six rows `T45aRow`/`T6RowGen` pair a slot of the perturbation `A` (bounded in
`𝒲^{6,∞}` by `K`) against a slot of the datum `f`.  The pointwise consequence of
`WlInfMem α 6 A ∧ WlInf α 6 A ≤ K` that the assembly consumes is

  `|D_z^j D_θ^i A| ≤ C·K·Abnd α i θ`,

where the angular factor `Abnd α i θ` is `1` when no `θ`-derivative is present and
`(α + sin 2θ)·sin(2θ)^{α/5}` otherwise (`Spaces.pz_Dth_sup_bound`).  The second form is
what makes the leftover angular weight integrable: `sin(2θ)^{-q}·Abnd α i θ²` is
integrable on `Iθ` for `q = η` and for `q = γ(α)` because
`-(1+α/10) + 2α/5 = -1 + 3α/10 > -1`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-- The angular factor `m(θ)` of the pointwise bound for `D_z^j D_θ^i A` when `A` is
`𝒲^{l,∞}`-bounded: `1` for `i = 0` and `(α + sin 2θ)·sin(2θ)^{α/5}` for `i ≥ 1`
(`Spaces.pz_Dth_sup_bound`). -/
def Abnd (α : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  if i = 0 then 1
  else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- `Abnd` is nonnegative on the angular interval. -/
theorem Abnd_nonneg {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) :
    0 ≤ Abnd α i θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  unfold Abnd
  split_ifs with h
  · norm_num
  · exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)

/-- `Abnd α i θ ≤ 2` for every `α ∈ (0,1]` and `θ ∈ Iθ`. -/
theorem Abnd_le_two {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) : Abnd α i θ ≤ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  unfold Abnd
  split_ifs with h
  · norm_num
  · have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
    have h2 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
      Real.rpow_le_one hs hs1 (by linarith)
    calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        ≤ 2 * 1 := by
          refine mul_le_mul h1 h2 (Real.rpow_nonneg hs _) (by norm_num)
      _ = 2 := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
