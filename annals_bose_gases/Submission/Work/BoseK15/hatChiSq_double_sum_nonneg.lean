import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.hatChiSq_double_sum_nonneg` — the box kernel `χ̂²` is a
positive-semidefinite kernel, tensored with the Fock form `bp`

## What is proved

`corpusBox.hatChiSq` is FS's `χ̂²(p) = ∫ χ²(x) cos⟪p,x⟫ dx`
(`Work.BoseB4.BoxData.hatChiSq`), the cosine transform of the *nonnegative*
weight `χ² dx`; `F.bp` is the Fock inner product of `Work.BoseB7.FockData`
(symmetric, positive semidefinite on the diagonal).  The theorem

    `0 ≤ Σ_s Σ_{s'} c s · c s' · χ̂²(M s' − M s) · ⟪v s', v s⟫`

is the statement that the Hadamard (entrywise) product of the two symmetric
positive-semidefinite kernels `(s,s') ↦ χ̂²(M s' − M s)` and
`(s,s') ↦ ⟪v s', v s⟫` is again positive semidefinite on any finite `S`
(this is the `hatChiSq_form` row of the `Q3Kernel` interface of
`Submission/Work/BoseB7A/`, FS `eq:Commutator_general`).

## The argument (two independent halves, glued by linearity)

1. **Pointwise (no measure theory).**  For each `x`, the cosine-difference
   identity `cos(a' − a) = cos a' cos a + sin a' sin a` writes the `x`-th
   bracket as

       `Σ_s Σ_{s'} c s c s' cos⟪M s' − M s, x⟫ ⟪v s', v s⟫`
         `= ⟪U_x, U_x⟫ + ⟪V_x, V_x⟫`,

   with `U_x = Σ_s (c s cos⟪M s, x⟫) • v s` and
   `V_x = Σ_s (c s sin⟪M s, x⟫) • v s`, hence is `≥ 0`
   (`cos_quadForm_nonneg`, via the bilinear expansion `bp_sum_sum`;
   equivalently the Schur product theorem for these two PSD kernels).

2. **Linearity of the Bochner integral over the finite sum**
   (`integral_double_sum_chiSq_cos`), which replaces the double sum of the
   `χ̂²`'s by `∫ x, χ²(x) · (bracket x)`.

The theorem is then `∫` of a nonnegative function.

## Contents

* `bp_sum_sum` — bilinear expansion of `F.bp` over two finite sums;
* `cos_quadForm_nonneg` — the pointwise nonnegativity (half 1);
* `integral_double_sum_chiSq_cos` — the integral identity (half 2);
* `hatChiSq_double_sum_nonneg` — the target.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseK15

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The bilinear expansion -/

/-- **Expansion of the Fock form over two finite sums.**
`⟪Σ_s a_s • v_s, Σ_{s'} b_{s'} • v_{s'}⟫ = Σ_s Σ_{s'} a_s b_{s'} ⟪v_s, v_{s'}⟫`.

Only bilinearity of `F.bp` (`map_sum`, `map_smul`, `LinearMap.sum_apply`,
`LinearMap.smul_apply`) is used; no symmetry and no positivity. -/
lemma bp_sum_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode)
    (S : Finset Mode) (a b : Mode → ℝ) (v : Mode → F.H) :
    F.bp (∑ s ∈ S, a s • v s) (∑ s' ∈ S, b s' • v s')
      = ∑ s ∈ S, ∑ s' ∈ S, a s * b s' * F.bp (v s) (v s') := by
  have h1 : F.bp (∑ s ∈ S, a s • v s) = ∑ s ∈ S, a s • F.bp (v s) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun s _ => by rw [map_smul])
  rw [h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [LinearMap.smul_apply, smul_eq_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  rw [map_smul, smul_eq_mul]
  ring

/-! ## 2. The pointwise nonnegativity -/

/-- **The cosine-difference quadratic form is nonnegative.**  For every
`x : ℝ³`,

`Σ_s Σ_{s'} c s c s' cos⟪M s' − M s, x⟫ ⟪v s', v s⟫ ≥ 0`.

This is the square completion `⟪U,U⟫ + ⟪V,V⟫` of the two sides of
`cos⟪M s' − M s, x⟫ = cos⟪M s', x⟫ cos⟪M s, x⟫ + sin⟪M s', x⟫ sin⟪M s, x⟫`. -/
theorem cos_quadForm_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode)
    (M : Mode → ℝ³) (S : Finset Mode) (c : Mode → ℝ)
    (v : Mode → F.H) (x : ℝ³) :
    0 ≤ ∑ s ∈ S, ∑ s' ∈ S,
      c s * c s' * Real.cos (inner ℝ (M s' - M s) x) * F.bp (v s') (v s) := by
  have hcos : ∀ s s' : Mode, Real.cos (inner ℝ (M s' - M s) x)
      = Real.cos (inner ℝ (M s') x) * Real.cos (inner ℝ (M s) x)
        + Real.sin (inner ℝ (M s') x) * Real.sin (inner ℝ (M s) x) := by
    intro s s'
    rw [inner_sub_left, Real.cos_sub]
  have hA : (∑ s ∈ S, ∑ s' ∈ S,
        c s * c s' * Real.cos (inner ℝ (M s) x) * Real.cos (inner ℝ (M s') x)
          * F.bp (v s') (v s))
      = F.bp (∑ s ∈ S, (c s * Real.cos (inner ℝ (M s) x)) • v s)
             (∑ s ∈ S, (c s * Real.cos (inner ℝ (M s) x)) • v s) := by
    rw [bp_sum_sum F S (fun s => c s * Real.cos (inner ℝ (M s) x))
        (fun s => c s * Real.cos (inner ℝ (M s) x)) v]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [F.bp_symm (v s) (v s')]
    ring
  have hB : (∑ s ∈ S, ∑ s' ∈ S,
        c s * c s' * Real.sin (inner ℝ (M s) x) * Real.sin (inner ℝ (M s') x)
          * F.bp (v s') (v s))
      = F.bp (∑ s ∈ S, (c s * Real.sin (inner ℝ (M s) x)) • v s)
             (∑ s ∈ S, (c s * Real.sin (inner ℝ (M s) x)) • v s) := by
    rw [bp_sum_sum F S (fun s => c s * Real.sin (inner ℝ (M s) x))
        (fun s => c s * Real.sin (inner ℝ (M s) x)) v]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [F.bp_symm (v s) (v s')]
    ring
  have hsplit : (∑ s ∈ S, ∑ s' ∈ S,
        c s * c s' * Real.cos (inner ℝ (M s' - M s) x) * F.bp (v s') (v s))
      = ∑ s ∈ S, ∑ s' ∈ S,
        ( c s * c s' * Real.cos (inner ℝ (M s) x) * Real.cos (inner ℝ (M s') x)
            * F.bp (v s') (v s)
          + c s * c s' * Real.sin (inner ℝ (M s) x) * Real.sin (inner ℝ (M s') x)
            * F.bp (v s') (v s) ) := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [hcos s s']
    ring
  rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [hA, hB]
  exact add_nonneg (F.bp_nonneg _) (F.bp_nonneg _)

/-! ## 3. The integral identity -/

/-- **Linearity of the Bochner integral over the double sum.**  For any
integrable weight `χ²` (the corpus `χ` is continuous with compact support),

`Σ_s Σ_{s'} c s c s' (∫ x, χ²(x) cos⟪M s' − M s, x⟫) · b s s'`
  `= ∫ x, χ²(x) · Σ_s Σ_{s'} c s c s' cos⟪M s' − M s, x⟫ · b s s'`.

Each summand `x ↦ χ²(x) cos⟪M s' − M s, x⟫` is integrable by domination
against `χ²` (`|cos| ≤ 1`), so `integral_finsetSum` applies; the constants are
moved by `integral_mul_const`. -/
theorem integral_double_sum_chiSq_cos {Mode : Type*} [Fintype Mode]
    (χ : ℝ³ → ℝ) (hχ : Integrable fun x => (χ x) ^ 2)
    (M : Mode → ℝ³) (S : Finset Mode) (c : Mode → ℝ)
    (b : Mode → Mode → ℝ) :
    ∑ s ∈ S, ∑ s' ∈ S,
        c s * c s' * (∫ x, (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x)) * b s s'
      = ∫ x, (χ x) ^ 2 *
          ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * Real.cos (inner ℝ (M s' - M s) x) * b s s' := by
  have hint : ∀ s s' : Mode,
      Integrable (fun x => (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x)) := by
    intro s s'
    refine hχ.mono' ?_ ?_
    · exact hχ.aestronglyMeasurable.mul
        ((Real.continuous_cos.comp (continuous_const.inner continuous_id)).aestronglyMeasurable)
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc (χ x) ^ 2 * |Real.cos (inner ℝ (M s' - M s) x)| ≤ (χ x) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg _)
        _ = (χ x) ^ 2 := by ring
  have hstep1 : (∑ s ∈ S, ∑ s' ∈ S,
        c s * c s' * (∫ x, (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x)) * b s s')
      = ∑ s ∈ S, ∑ s' ∈ S,
        ∫ x, (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x) * (c s * c s' * b s s') := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    refine Eq.trans ?_ (MeasureTheory.integral_mul_const (c s * c s' * b s s')
        (fun x => (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x))).symm
    ring
  have hstep2 : (∑ s ∈ S, ∑ s' ∈ S,
        ∫ x, (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x) * (c s * c s' * b s s'))
      = ∫ x, ∑ s ∈ S, ∑ s' ∈ S,
        (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x) * (c s * c s' * b s s') := by
    refine Eq.trans (Finset.sum_congr rfl fun s _ => ?_)
      ((MeasureTheory.integral_finsetSum S (fun s _ =>
        MeasureTheory.integrable_finsetSum S
          (fun s' _ => (hint s s').mul_const _))).symm)
    exact (MeasureTheory.integral_finsetSum S
      (fun s' _ => (hint s s').mul_const _)).symm
  have hstep3 : (∫ x, ∑ s ∈ S, ∑ s' ∈ S,
        (χ x) ^ 2 * Real.cos (inner ℝ (M s' - M s) x) * (c s * c s' * b s s'))
      = ∫ x, (χ x) ^ 2 * ∑ s ∈ S, ∑ s' ∈ S,
        c s * c s' * Real.cos (inner ℝ (M s' - M s) x) * b s s' := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  exact hstep1.trans (hstep2.trans hstep3)

/-! ## 4. The target -/

/-- **The `χ̂²`-kernel quadratic form is nonnegative.**  For any finite set `S`
of modes, any momenta `M`, any coefficients `c` and any Fock vectors `v`,

`0 ≤ Σ_{s,s'} c s · c s' · χ̂²(M s' − M s) · ⟪v s', v s⟫`.

The proof is `hatChiSq_double_sum_nonneg = ∫ x, χ²(x) · (nonnegative bracket x)`
(`integral_double_sum_chiSq_cos`), where the bracket is the square completion
of `cos⟪M s' − M s, x⟫` (`cos_quadForm_nonneg`). -/
theorem hatChiSq_double_sum_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode)
    (M : Mode → EuclideanSpace ℝ (Fin 3)) (S : Finset Mode) (c : Mode → ℝ)
    (v : Mode → F.H) :
    0 ≤ ∑ s ∈ S, ∑ s' ∈ S,
      c s * c s' * corpusBox.hatChiSq (M s' - M s) * F.bp (v s') (v s) := by
  simp only [Work.BoseB4.BoxData.hatChiSq]
  rw [integral_double_sum_chiSq_cos corpusBox.chi corpusBox.chi_sq_integrable M S c
    (fun s s' => F.bp (v s') (v s))]
  exact MeasureTheory.integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (cos_quadForm_nonneg F M S c v x)

end Work.BoseK15
