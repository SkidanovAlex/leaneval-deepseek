/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.Slot20Defs`: the vocabulary of the top angular slot at level 2

The target `Work.FTS.EllipticEst.TT.slot20_le` bounds the top angular slot of `∂_θθΨ` at level 2,

  `qLHS α Ψ := ∫_z ∫_θ (D_θ²(∂_θθΨ) · Wt α)²`,

by `C · (qPure Ψ + HkSq α 2 F)` uniformly for data of the weak class `EllWeakPos α 2 F Ψ`,
`0 < α ≤ 1/4`.  This module fixes the four quantities in which the proof is phrased:

* `qPure Ψ` — the pure (`i = 0`) slots of `∂_θθΨ` at level 2, i.e. `Σ_{j<3} |∂_θ²(D_z^jΨ)|²_{w,sEta}`;
* `qM3 α Ψ` — the top *first* angular slot, `∫_z∫_θ 8 w² (∂_θ³Ψ)² σ₂`
  (`= 8·|D_θ(∂_θθΨ)|²_{w,sGam}`);
* `qM4 α Ψ` — the top *second* angular slot, `∫_z∫_θ 2 w² (∂_θ⁴Ψ)² σ₄`.

The two analytic inputs of the proof are `qM3 α Ψ ≤ C(qPure Ψ + HkSq α 2 F)` (the paper's Step 4)
and `qM4 α Ψ ≤ C(qPure Ψ + HkSq α 2 F + qM3 α Ψ)`; the definitions and the elementary weight
comparisons on the open angular interval are collected here.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The quantities -/

/-- The left-hand side of the target: the top angular slot of `∂_θθΨ` at level `2`,
`∫_z∫_θ (D_θ²(∂_θθΨ)·Wt α)²`. -/
def qLHS (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed 0 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The pure (`i = 0`) part of the level-`2` norm of `∂_θθΨ`:
`Σ_{j<3} ∫_z∫_θ (∂_θ²D_z^jΨ)² w² sEta`. -/
def qPure (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))

/-- The top first angular slot: `∫_z∫_θ 8 w² (∂_θ³Ψ)² σ₂` with `σ₂ = sin(2θ)^{2-γ}`. -/
def qM3 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (8 : ℝ) * (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
        Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ)

/-- The top second angular slot: `∫_z∫_θ 2 w² (∂_θ⁴Ψ)² σ₄` with `σ₄ = sin(2θ)^{4-γ}`. -/
def qM4 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (2 : ℝ) * (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
        Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)

/-! ## Elementary facts about the weights -/

theorem sig2_eq (α θ : ℝ) :
    Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ
      = (Real.sin (2 * θ)) ^ ((2 : ℝ) - Work.Spaces.gam α) := rfl

theorem sig4_eq (α θ : ℝ) :
    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
      = (Real.sin (2 * θ)) ^ ((4 : ℝ) - Work.Spaces.gam α) := rfl

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sEta_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sig2_nonneg_of_Iθ (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ := by
  rw [sig2_eq]; exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

theorem sig4_nonneg_of_Iθ (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ := by
  rw [sig4_eq]; exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

theorem sincos_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ

/-! ## Nonnegativity of the three quantities -/

theorem qPure_nonneg (Ψ : ℝ → ℝ → ℝ) : 0 ≤ qPure Ψ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

theorem L2Sq_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.L2Sq g :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

theorem qM3_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : 0 ≤ qM3 α Ψ := by
  refine setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sig2_nonneg_of_Iθ α hθ))

theorem qM4_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : 0 ≤ qM4 α Ψ := by
  refine setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  refine setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sig4_nonneg_of_Iθ α hθ))

/-! ## Weight comparisons on the open angular interval -/

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `1 ≤ sEta` on the open interval. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sin_two_pos_of_mem_Ioo hθ)
    (Real.sin_le_one (2 * θ)) (by rw [Work.Spaces.eta]; norm_num)

/-- `σ₂ ≤ 1` on the open interval. -/
theorem sig2_le_one (α : ℝ) (hα4 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ ≤ 1 := by
  rw [sig2_eq]
  exact Real.rpow_le_one (sin_two_pos_of_mem_Ioo hθ).le (Real.sin_le_one (2 * θ)) (by
    rw [Work.Spaces.gam]; linarith)

/-- `σ₂ ≤ sEta` on the open interval. -/
theorem sig2_le_sEta (α : ℝ) (hα4 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [sig2_eq, Work.FTS.EllipticEst.sEta]
  refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_of_mem_Ioo hθ)
    (Real.sin_le_one (2 * θ)) ?_
  have hη : Work.Spaces.eta = 99 / 100 := rfl
  rw [hη, Work.Spaces.gam]; linarith

/-- `σ₄ ≤ sEta` on the open interval. -/
theorem sig4_le_sEta (α : ℝ) (hα4 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [sig4_eq, Work.FTS.EllipticEst.sEta]
  refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_of_mem_Ioo hθ)
    (Real.sin_le_one (2 * θ)) ?_
  have hη : Work.Spaces.eta = 99 / 100 := rfl
  rw [hη, Work.Spaces.gam]; linarith

/-- `σ₄ ≤ σ₂` on the open interval. -/
theorem sig4_le_sig2 (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
      ≤ Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ := by
  rw [sig4_eq, sig2_eq]
  refine Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_of_mem_Ioo hθ)
    (Real.sin_le_one (2 * θ)) (by norm_num)

theorem sig2_nonneg_of_Ioo (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ :=
  sig2_nonneg_of_Iθ α (Set.Ioo_subset_Icc_self hθ)

theorem sig4_nonneg_of_Ioo (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ :=
  sig4_nonneg_of_Iθ α (Set.Ioo_subset_Icc_self hθ)

end Work.FTS.EllipticEst.TT
