import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsL.LatticeCoulomb.reductionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.LatticeCoulomb

open MeasureTheory
open scoped Real BigOperators Topology

set_option autoImplicit false

/-!
# `Work.BoseRowsL.LatticeCoulomb.sum_chat_double`

The lattice side of the cos-cosine kernel is **tensored**: pulling the two `chat`
factors apart (which is `chat_eq_integral_cos`), each lattice mode `kₙ` contributes
`(∫_x f₁ x cos⟪kₙ,x⟫)(∫_y f₂ y cos⟪kₙ,y⟫)/(2‖kₙ‖²)`, i.e. the *product* of the two
one-dimensional transforms.  Summing over the finite set `T` and moving the finite
sum inside the two integrals gives the statement: both sides equal
`Σ_{n∈T} ∫_x ∫_y f₁ x f₂ y (cos⟪kₙ,x⟫cos⟪kₙ,y⟫)/(2‖kₙ‖²)`.

The only non-formal content is integrability (each step of the interchange needs
the relevant function to be integrable), which is immediate because a `L¹`
function times a bounded measurable one is `L¹`; the algebraic steps
(`∫ c·g = c·∫ g` and `∫ g·c = (∫ g)·c`) hold unconditionally. -/

/-- An `L¹` function times `cos⟪k,·⟫` (bounded by `1`) is `L¹`. -/
private lemma integrable_mul_cos {f : E3 → ℝ} (hf : Integrable f) (k : E3) :
    Integrable (fun y : E3 => f y * Real.cos (inner ℝ k y)) :=
  hf.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

/-- The inner `y`-integral of one lattice summand, in closed form (for fixed `x`). -/
private lemma inner_integral (k : E3) {f₁ f₂ : E3 → ℝ} (x : E3) :
    (∫ y, f₁ x * f₂ y * (Real.cos (inner ℝ k x) * Real.cos (inner ℝ k y) * (2 * ‖k‖ ^ 2)⁻¹))
      = (f₁ x * Real.cos (inner ℝ k x))
          * ((∫ y, f₂ y * Real.cos (inner ℝ k y)) * (2 * ‖k‖ ^ 2)⁻¹) := by
  rw [show (fun y : E3 => f₁ x * f₂ y *
        (Real.cos (inner ℝ k x) * Real.cos (inner ℝ k y) * (2 * ‖k‖ ^ 2)⁻¹))
      = (fun y : E3 => (f₁ x * Real.cos (inner ℝ k x)) *
          ((f₂ y * Real.cos (inner ℝ k y)) * (2 * ‖k‖ ^ 2)⁻¹)) from by funext y; ring]
  rw [integral_const_mul, integral_mul_const]

/-- One lattice summand equals the corresponding double integral. -/
private lemma chat_double_term (k : E3) {f₁ f₂ : E3 → ℝ}
    (hf1 : Integrable f₁) (hf2 : Integrable f₂) :
    Work.BoseFixR.chat f₁ k * Work.BoseFixR.chat f₂ k * (2 * ‖k‖ ^ 2)⁻¹
      = ∫ x, ∫ y, f₁ x * f₂ y *
          (Real.cos (inner ℝ k x) * Real.cos (inner ℝ k y) * (2 * ‖k‖ ^ 2)⁻¹) := by
  rw [chat_eq_integral_cos hf1 k, chat_eq_integral_cos hf2 k]
  have hinner : ∀ x : E3, (∫ y, f₁ x * f₂ y *
        (Real.cos (inner ℝ k x) * Real.cos (inner ℝ k y) * (2 * ‖k‖ ^ 2)⁻¹))
      = (f₁ x * Real.cos (inner ℝ k x))
          * ((∫ y, f₂ y * Real.cos (inner ℝ k y)) * (2 * ‖k‖ ^ 2)⁻¹) :=
    fun x => inner_integral k x
  rw [show (∫ x, ∫ y, f₁ x * f₂ y *
        (Real.cos (inner ℝ k x) * Real.cos (inner ℝ k y) * (2 * ‖k‖ ^ 2)⁻¹))
      = ∫ x, (f₁ x * Real.cos (inner ℝ k x)) *
            ((∫ y, f₂ y * Real.cos (inner ℝ k y)) * (2 * ‖k‖ ^ 2)⁻¹) from
      integral_congr_ae (Filter.Eventually.of_forall hinner)]
  rw [integral_mul_const]
  ring

theorem sum_chat_double (T : Finset (Fin 3 → ℤ)) (ℓ : ℝ) {f₁ f₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf1 : MeasureTheory.Integrable f₁) (hf2 : MeasureTheory.Integrable f₂) :
    ∑ n ∈ T, Work.BoseFixR.chat f₁ (ℓ⁻¹ • Work.BoseB4.vec n)
        * Work.BoseFixR.chat f₂ (ℓ⁻¹ • Work.BoseB4.vec n) / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec n‖ ^ 2)
      = ∫ x, ∫ y, f₁ x * f₂ y * Work.BoseRowsL.LatticeCoulomb.cosCosSum T ℓ x y := by
  classical
  set k : (Fin 3 → ℤ) → E3 := fun n => ℓ⁻¹ • Work.BoseB4.vec n with hk
  have hA : ∀ n : Fin 3 → ℤ, Integrable (fun x : E3 => f₁ x * Real.cos (inner ℝ (k n) x)) :=
    fun n => integrable_mul_cos hf1 (k n)
  -- integrability in `y` for fixed `x`
  have hy : ∀ (n : Fin 3 → ℤ) (x : E3), Integrable (fun y : E3 => f₁ x * f₂ y *
      (Real.cos (inner ℝ (k n) x) * Real.cos (inner ℝ (k n) y) * (2 * ‖k n‖ ^ 2)⁻¹)) := by
    intro n x
    have h : Integrable (fun y : E3 => (f₁ x * Real.cos (inner ℝ (k n) x) * (2 * ‖k n‖ ^ 2)⁻¹)
        * (f₂ y * Real.cos (inner ℝ (k n) y))) :=
      (integrable_mul_cos hf2 (k n)).const_mul _
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    ring
  -- integrability of the inner integral, as a function of `x`
  have hx : ∀ n : Fin 3 → ℤ, Integrable (fun x : E3 => ∫ y, f₁ x * f₂ y *
      (Real.cos (inner ℝ (k n) x) * Real.cos (inner ℝ (k n) y) * (2 * ‖k n‖ ^ 2)⁻¹)) := by
    intro n
    have hcl : (fun x : E3 => ∫ y, f₁ x * f₂ y *
        (Real.cos (inner ℝ (k n) x) * Real.cos (inner ℝ (k n) y) * (2 * ‖k n‖ ^ 2)⁻¹))
        = fun x : E3 => (f₁ x * Real.cos (inner ℝ (k n) x))
            * ((∫ y, f₂ y * Real.cos (inner ℝ (k n) y)) * (2 * ‖k n‖ ^ 2)⁻¹) := by
      funext x; exact inner_integral (k n) x
    rw [hcl]
    exact (hA n).mul_const _
  calc ∑ n ∈ T, Work.BoseFixR.chat f₁ (k n) * Work.BoseFixR.chat f₂ (k n) / (2 * ‖k n‖ ^ 2)
      = ∑ n ∈ T, ∫ x, ∫ y, f₁ x * f₂ y *
          (Real.cos (inner ℝ (k n) x) * Real.cos (inner ℝ (k n) y) * (2 * ‖k n‖ ^ 2)⁻¹) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        exact chat_double_term (k n) hf1 hf2
    _ = ∫ x, ∑ n ∈ T, ∫ y, f₁ x * f₂ y *
          (Real.cos (inner ℝ (k n) x) * Real.cos (inner ℝ (k n) y) * (2 * ‖k n‖ ^ 2)⁻¹) :=
        (integral_finsetSum T (fun n _ => hx n)).symm
    _ = ∫ x, ∫ y, ∑ n ∈ T, f₁ x * f₂ y *
          (Real.cos (inner ℝ (k n) x) * Real.cos (inner ℝ (k n) y) * (2 * ‖k n‖ ^ 2)⁻¹) := by
        apply integral_congr_ae
        filter_upwards with x
        exact (integral_finsetSum T (fun n _ => hy n x)).symm
    _ = ∫ x, ∫ y, f₁ x * f₂ y * Work.BoseRowsL.LatticeCoulomb.cosCosSum T ℓ x y := by
        apply integral_congr_ae
        filter_upwards with x
        apply integral_congr_ae
        filter_upwards with y
        simp only [hk, cosCosSum, div_eq_mul_inv, Finset.mul_sum]

end Work.BoseRowsL.LatticeCoulomb
