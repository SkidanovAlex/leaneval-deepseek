/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `∂_θ²` vanishing-slot bound, with clash-free helper names

The vanishing-slot bound for the middle conjunct `∂_θ²Ψ` of
`HkMem_seven_slots_of_vanishing_family` is elementary: on the open quadrant

  `vig α (∂_θ²Ψ) r j = hVint α Ψ (r+2) j`   (`∂_θ^r ∂_θ²Ψ = ∂_θ^{r+2}Ψ`, and
  `2(r+2) - 4 - γ = 2r - γ`),

which is a single summand of the grid majorant `vanGrid`.  This module records that bound under
distinct helper names (`vanFam_hVint_le_grid`, …), so that it can be imported together with
`vig_zsqPz2_le`, whose own helper `hVint_le_vanGrid` would otherwise clash (the two modules are
independent pieces of the same assembly).
-/
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

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- The vanishing integrand `hVint` is nonnegative on the angular interval. -/
theorem vanFam_hVint_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (t l : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ hVint α Ψ t l z θ := by
  rw [hVint]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)

/-- A vanishing grid slot is dominated by the grid majorant. -/
theorem vanFam_hVint_le_grid {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {t l : ℕ} (ht : 3 ≤ t) (ht9 : t ≤ 9) (hl : l ≤ 9) :
    hVint α Ψ t l z θ ≤ vanGrid α Ψ z θ := by
  have h1 : hVint α Ψ t l z θ ≤ ∑ l' ∈ Finset.range 10, hVint α Ψ t l' z θ :=
    Finset.single_le_sum (f := fun l' => hVint α Ψ t l' z θ)
      (fun l' _ => vanFam_hVint_nonneg α Ψ t l' hθ) (Finset.mem_range.mpr (by omega))
  have h2 : (∑ l' ∈ Finset.range 10, hVint α Ψ t l' z θ)
      ≤ ∑ t' ∈ Finset.Icc 3 9, ∑ l' ∈ Finset.range 10, hVint α Ψ t' l' z θ :=
    Finset.single_le_sum (f := fun t' => ∑ l' ∈ Finset.range 10, hVint α Ψ t' l' z θ)
      (fun t' _ => Finset.sum_nonneg fun l' _ => vanFam_hVint_nonneg α Ψ t' l' hθ)
      (Finset.mem_Icc.mpr ⟨ht, ht9⟩)
  have h3 : 0 ≤ ∑ l' ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.sum_nonneg fun l' _ => Finset.sum_nonneg fun m _ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  rw [vanGrid]
  exact le_trans h1 (le_trans h2 (le_add_of_nonneg_left h3))

/-- **The vanishing-slot bound for `∂_θ²Ψ`.** -/
theorem pthIter2_vig_le {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ 7 → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      vig α (Work.Spaces.pthIter 2 Ψ) r j z θ ≤ 4 * vanGrid α Ψ z θ := by
  intro j r hr hrj z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h2 : vig α (Work.Spaces.pthIter 2 Ψ) r j = hVint α Ψ (r + 2) j := by
    funext z' θ'
    rw [vig, hVint, show Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ)
        = Work.Spaces.pthIter (r + 2) Ψ from (seven_pthIter_add r 2 Ψ).symm]
    congr 2
    push_cast
    ring
  rw [h2]
  have h1 := vanFam_hVint_le_grid (α := α) (Ψ := Ψ) (z := z) (t := r + 2) (l := j) hθI
    (by omega) (by omega) (by omega)
  have h2' := vanGrid_nonneg α Ψ z hθI
  linarith

end Work.FTS.ClassC
