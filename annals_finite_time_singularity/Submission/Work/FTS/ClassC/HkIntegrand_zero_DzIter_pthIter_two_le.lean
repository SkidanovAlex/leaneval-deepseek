import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.VanishFamilyDefs
import Submission.Work.FTS.ClassC.VanishWeightDom
import Submission.Work.FTS.ClassC.HkMem_seven_slots_of_plain_family

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pure-`z` slot `D_z^j (∂_θ²Ψ)` is dominated by the grid majorant `vanGrid`

The grid majorant `vanGrid α Ψ` (`ClassC/VanishFamilyDefs.lean`) is the sum of

* the singular-weight `ℋ^0`-integrands `HkIntegrand α 0 (D_z^l ∂_θ^m Ψ)` for `l ≤ 9`, `m ≤ 2`,
* the vanishing-weight integrands `hVint α Ψ t l = (D_z^l ∂_θ^t Ψ · w)² · sin(2θ)^{2t-4-γ}`
  for `3 ≤ t ≤ 9`, `l ≤ 9`.

The slot `HkIntegrand α 0 (D_z^j ∂_θ²Ψ)` with `j ≤ 7` is literally the summand `(l,m) = (j,2)`
of the first block, so it is bounded by `vanGrid`, hence by `4 * vanGrid` (the factor `4` being
the slack used by the surrounding assembly).  All summands are nonnegative, so no regularity of
`Ψ` is needed beyond what makes the statement typecheck.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- The `hVint` integrands are nonnegative on the angular interval. -/
private theorem hVint_nonneg_aux (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (t l : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ hVint α Ψ t l z θ := by
  rw [hVint]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)

/-- The pure-`z` slot `HkIntegrand α 0 (D_z^j ∂_θ²Ψ)`, `j ≤ 7`, is a summand of the first
block of the grid majorant, hence dominated by `vanGrid`, hence by `4 * vanGrid`. -/
theorem HkIntegrand_zero_DzIter_pthIter_two_le {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) z θ
        ≤ 4 * Work.FTS.ClassC.vanGrid α Ψ z θ := by
  intro j hj z _hz θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the summand `(l, m) = (j, 2)` of the first block of `vanGrid`
  have hjmem : j ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
  have h2mem : (2 : ℕ) ∈ Finset.range 3 := Finset.mem_range.mpr (by norm_num)
  have hstep1 : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ))
        z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun m => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter j (Work.Spaces.pthIter m Ψ)) z θ)
      (fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) h2mem
  have hstep2 : (∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter m Ψ)) z θ)
      ≤ ∑ l ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun l => ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      (fun l _ => Finset.sum_nonneg fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hjmem
  have hvan : 0 ≤ Work.FTS.ClassC.vanGrid α Ψ z θ :=
    vanGrid_nonneg α Ψ z hθIθ
  calc Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 Ψ)) z θ
      ≤ ∑ l ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ :=
        le_trans hstep1 hstep2
    _ ≤ Work.FTS.ClassC.vanGrid α Ψ z θ := by
        rw [Work.FTS.ClassC.vanGrid]
        exact le_add_of_nonneg_right
          (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ =>
            hVint_nonneg_aux α Ψ t l hθIθ)
    _ ≤ 4 * Work.FTS.ClassC.vanGrid α Ψ z θ :=
        le_mul_of_one_le_left hvan (by norm_num)

end Work.FTS.ClassC
