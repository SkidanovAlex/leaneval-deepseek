/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`0` honesty slot of `z²∂_z²Ψ` in the `H^7` estimate

This module proves that the *pure radial* level-`0` slot of the function `z²∂_z²Ψ`,

  `HkIntegrand α 0 (D_z^j (z²∂_z²Ψ))`,

is dominated by `4 · vanGrid α Ψ` for `j ≤ 7`.  This is the `h0`-hypothesis of
`HkIntegrand_seven_le_of_bounds` for the first of the three derivatives appearing in the
elliptic equation of Elgindi's §H2 (`z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ`).

The point is that the second radial derivative is a *difference* of two `D_z`-iterates of `Ψ`
itself: on the open quadrant

  `z² ∂_z² h = D_z²h − D_zh`   (`zsqPz2_eq_sub`),

and `D_z^j` commutes with the operator `z²∂_z²` (`NormPiecesAux.zsqPz2_DzIter_eqOn`), so

  `D_z^j (z²∂_z²Ψ) = D_z^{j+2}Ψ − D_z^{j+1}Ψ`   on the open quadrant.

Squaring, `(x − y)² ≤ 2x² + 2y²`, reduces the estimate to the two *pure* slots `D_z^{j+2}Ψ` and
`D_z^{j+1}Ψ`, whose angular order is `0 ≤ 2` and whose radial order is `≤ 7 + 2 = 9`: both are
summands of the grid majorant `vanGrid α Ψ`.

Everything here is `sorry`-free.
-/
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

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-! ## A single pure slot against the grid majorant -/

/-- Every pure slot `HkIntegrand α 0 (D_z^l Ψ)` with `l ≤ 9` is dominated by the grid majorant
`vanGrid α Ψ`, the sum of all the integrands whose integrability the vanishing-family
hypotheses supply. -/
theorem hkDze_zero_DzIter_le_vanGrid {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) {l : ℕ} (hl : l ≤ 9) :
    Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l Ψ) z θ
      ≤ vanGrid α Ψ z θ := by
  -- the `hV`-family is a sum of nonnegative integrands
  have hS2 : 0 ≤ ∑ t ∈ Finset.Icc 3 9, ∑ l' ∈ Finset.range 10, hVint α Ψ t l' z θ :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l' _ => by
      rw [hVint]
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)
  -- the slot is the `m = 0` term of the inner `∑_{m < 3}`
  have hinner' : Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l (Work.Spaces.pthIter 0 Ψ)) z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum (s := Finset.range 3) (a := 0)
      (f := fun m => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      (fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (Finset.mem_range.mpr (by norm_num : (0 : ℕ) < 3))
  have hinner : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l Ψ) z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ := by
    simpa only [Work.Spaces.pthIter_zero] using hinner'
  -- ... and that inner sum is the `l`-th term of the outer `∑_{l' < 10}`
  have houter : (∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      ≤ ∑ l' ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum (s := Finset.range 10) (a := l)
      (f := fun l' => ∑ m ∈ Finset.range 3,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ)
      (fun l' _ => Finset.sum_nonneg fun m _ =>
        Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (Finset.mem_range.mpr (by omega : l < 10))
  rw [vanGrid]
  exact le_trans (le_trans hinner houter) (le_add_of_nonneg_right hS2)

/-! ## The target estimate -/

theorem HkIntegrand_zero_DzIter_zsqPz2_le {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        ≤ 4 * Work.FTS.ClassC.vanGrid α Ψ z θ := by
  intro j hj z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the two composition identities `D_z^2 ∘ D_z^j = D_z^{j+2}`, `D_z^1 ∘ D_z^j = D_z^{j+1}`
  have hD2 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter j Ψ)
      = Work.Spaces.DzIter (j + 2) Ψ := by
    rw [← seven_DzIter_add 2 j Ψ]
    exact congrArg (fun k => Work.Spaces.DzIter k Ψ) (by omega : 2 + j = j + 2)
  have hD1 : Work.Spaces.DzIter 1 (Work.Spaces.DzIter j Ψ)
      = Work.Spaces.DzIter (j + 1) Ψ := by
    rw [← seven_DzIter_add 1 j Ψ]
    exact congrArg (fun k => Work.Spaces.DzIter k Ψ) (by omega : 1 + j = j + 1)
  -- `z²∂_z² = D_z² − D_z` on the open quadrant, commuted with `D_z^j`
  have hkey : Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Spaces.DzIter (j + 2) Ψ z θ - Work.Spaces.DzIter (j + 1) Ψ z θ := by
    rw [NormPiecesAux.zsqPz2_DzIter_eqOn Ψ hΨ j z θ hz hθ.1 hθ.2,
      seven_zsq_pzIter_two_eq (Work.Spaces.DzIter j Ψ) (hΨ.DzIter j) z θ hz hθ.1 hθ.2,
      hD2, hD1]
  -- the two summands are pure grid slots (`j + 2 ≤ 9`, `j + 1 ≤ 9`)
  have hAux : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 2) Ψ) z θ
      ≤ vanGrid α Ψ z θ := hkDze_zero_DzIter_le_vanGrid hθI (l := j + 2) (by omega)
  have hBux : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 1) Ψ) z θ
      ≤ vanGrid α Ψ z θ := hkDze_zero_DzIter_le_vanGrid hθI (l := j + 1) (by omega)
  -- `(x − y)² ≤ 2x² + 2y²`
  have hsq := seven_sq_sub_mul_sq_le (Work.Spaces.DzIter (j + 2) Ψ z θ)
    (Work.Spaces.DzIter (j + 1) Ψ z θ)
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
  calc Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        HkIntegrand_zero_eq_classC α _ z θ
    _ = ((Work.Spaces.DzIter (j + 2) Ψ z θ - Work.Spaces.DzIter (j + 1) Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [hkey]
    _ ≤ 2 * (Work.Spaces.DzIter (j + 2) Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + 2 * (Work.Spaces.DzIter (j + 1) Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hsq
    _ = 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 2) Ψ) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 1) Ψ) z θ := by
        rw [← HkIntegrand_zero_eq_classC α (Work.Spaces.DzIter (j + 2) Ψ) z θ,
          ← HkIntegrand_zero_eq_classC α (Work.Spaces.DzIter (j + 1) Ψ) z θ]
    _ ≤ 4 * Work.FTS.ClassC.vanGrid α Ψ z θ := by linarith

end Work.FTS.ClassC
