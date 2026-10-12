import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.abs_pairIntegral_le_sqrt`

The weighted Cauchy–Schwarz (Bessel) inequality for a finite family of pair integrals:

    |Σ_{p ∈ s} ∫ f_p·g_p·w_p dμ| ≤ √( (Σ_{p∈s} ∫ f_p²·w_p dμ) · (Σ_{p∈s} ∫ g_p²·w_p dμ) )

for a non-negative weight `w p x ≥ 0` and integrability of the three products
`(f p)² w p`, `(g p)² w p`, `(f p)(g p) w p`.

Only *integrability* is assumed — in particular neither `w p` nor `f p`, `g p` need be
measurable.  The argument is the quadratic-form (discriminant) argument applied to the
Bochner integral, which uses linearity of the integral only:

* per index `p`, `0 ≤ ∫ (λ·f_p − g_p)² w_p dμ` for every `λ`, and expanding the square gives
  a non-negative quadratic in `λ`, whose discriminant is `≤ 0`; this is
  `(∫ f_p g_p w_p)² ≤ (∫ f_p² w_p)(∫ g_p² w_p)`;
* summing over `p ∈ s` then uses the triangle inequality and the finite-dimensional
  Cauchy–Schwarz `Σ_p √(A_p B_p) ≤ √((Σ_p A_p)(Σ_p B_p))`.
-/

open MeasureTheory

namespace Work.BoseFixB1

/-! ## The two scalar cores -/

/-- **The quadratic discriminant.**  If the quadratic `λ ↦ λ²A − 2λC + B` is non-negative on
all of `ℝ`, then `C² ≤ A·B`.

(If `A = 0` the value at `λ = 0` gives `B ≥ 0` and any `λ ≠ 0` forces `C = 0`; if `A > 0` the
minimum is at `λ = C/A`.) -/
private lemma pairCS_quadDisc {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ s : ℝ, 0 ≤ s ^ 2 * A - 2 * s * C + B) : C ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hB0 : 0 ≤ B := by simpa using h 0
    have h1 : C = 0 := by
      by_contra hC
      have h2 := h ((B + 1) / (2 * C))
      rw [hA0] at h2
      have h4 : -2 * ((B + 1) / (2 * C)) * C + B = -1 := by
        field_simp
        ring
      nlinarith [h2, h4]
    rw [h1]
    nlinarith [hA, hB0]
  · have h2 := h (C / A)
    have h3 : (C / A) ^ 2 * A - 2 * (C / A) * C + B = B - C ^ 2 / A := by
      field_simp
      ring
    rw [h3] at h2
    have h4 : C ^ 2 / A ≤ B := by linarith
    calc C ^ 2 = A * (C ^ 2 / A) := by field_simp
      _ ≤ A * B := mul_le_mul_of_nonneg_left h4 (le_of_lt hApos)

/-- **Cauchy–Schwarz for a single weighted pair integral.**  For a non-negative weight `w` and
functions `a, b` with `a²w`, `b²w`, `abw` integrable,

    (∫ a·b·w)² ≤ (∫ a²w)·(∫ b²w) .

Proof: `0 ≤ ∫ (λa − b)²w = λ²(∫a²w) − 2λ(∫abw) + (∫b²w)` for every `λ`, then the
discriminant.  No measurability is used: the expansion is linearity of the Bochner integral
only. -/
private lemma pairCS_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b w : α → ℝ}
    (hw : ∀ x, 0 ≤ w x)
    (ha : Integrable (fun x => a x ^ 2 * w x) μ)
    (hb : Integrable (fun x => b x ^ 2 * w x) μ)
    (hab : Integrable (fun x => a x * b x * w x) μ) :
    (∫ x, a x * b x * w x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 * w x ∂μ) * (∫ x, b x ^ 2 * w x ∂μ) := by
  refine pairCS_quadDisc (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw x)) ?_
  intro s
  have h0 : 0 ≤ ∫ x, (s * a x - b x) ^ 2 * w x ∂μ :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw x)
  have hexp : (∫ x, (s * a x - b x) ^ 2 * w x ∂μ)
      = s ^ 2 * (∫ x, a x ^ 2 * w x ∂μ) - 2 * s * (∫ x, a x * b x * w x ∂μ)
        + (∫ x, b x ^ 2 * w x ∂μ) := by
    have h1 : (∫ x, (s * a x - b x) ^ 2 * w x ∂μ)
        = ∫ x, (s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x))
            + (b x ^ 2 * w x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    have h2 : (∫ x, (s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x))
          + (b x ^ 2 * w x) ∂μ)
        = (∫ x, s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x) ∂μ)
          + (∫ x, b x ^ 2 * w x ∂μ) :=
      integral_add ((ha.const_mul _).sub (hab.const_mul _)) hb
    have h3 : (∫ x, s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x) ∂μ)
        = (∫ x, s ^ 2 * (a x ^ 2 * w x) ∂μ) - (∫ x, 2 * s * (a x * b x * w x) ∂μ) :=
      integral_sub (ha.const_mul _) (hab.const_mul _)
    have h4 : (∫ x, s ^ 2 * (a x ^ 2 * w x) ∂μ) = s ^ 2 * (∫ x, a x ^ 2 * w x ∂μ) :=
      integral_const_mul (s ^ 2) (f := fun x => a x ^ 2 * w x)
    have h5 : (∫ x, 2 * s * (a x * b x * w x) ∂μ) = (2 * s) * (∫ x, a x * b x * w x ∂μ) :=
      integral_const_mul (2 * s) (f := fun x => a x * b x * w x)
    rw [h1, h2, h3, h4, h5]
  linarith [h0, hexp]

/-- **Cauchy–Schwarz for the finite sum of geometric means:**

    Σ_{p∈s} √(A_p B_p) ≤ √((Σ_{p∈s} A_p)·(Σ_{p∈s} B_p)) ,

for non-negative `A_p, B_p`.  This is `Real.sum_mul_le_sqrt_mul_sqrt` applied to the pairs
`(√(A_p), √(B_p))`, together with `(√A)² = A`. -/
private lemma pairCS_finset {ι : Type*} (s : Finset ι) (A B : ι → ℝ)
    (hA : ∀ p ∈ s, 0 ≤ A p) (hB : ∀ p ∈ s, 0 ≤ B p) :
    (∑ p ∈ s, Real.sqrt (A p * B p))
      ≤ Real.sqrt ((∑ p ∈ s, A p) * (∑ p ∈ s, B p)) := by
  have hAs : 0 ≤ ∑ p ∈ s, A p := Finset.sum_nonneg hA
  have h2 : (∑ p ∈ s, Real.sqrt (A p) ^ 2) = ∑ p ∈ s, A p :=
    Finset.sum_congr rfl fun p hp => Real.sq_sqrt (hA p hp)
  have h3 : (∑ p ∈ s, Real.sqrt (B p) ^ 2) = ∑ p ∈ s, B p :=
    Finset.sum_congr rfl fun p hp => Real.sq_sqrt (hB p hp)
  calc (∑ p ∈ s, Real.sqrt (A p * B p))
      = ∑ p ∈ s, Real.sqrt (A p) * Real.sqrt (B p) :=
        Finset.sum_congr rfl fun p hp => Real.sqrt_mul (hA p hp) (B p)
    _ ≤ Real.sqrt (∑ p ∈ s, Real.sqrt (A p) ^ 2) * Real.sqrt (∑ p ∈ s, Real.sqrt (B p) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ = Real.sqrt (∑ p ∈ s, A p) * Real.sqrt (∑ p ∈ s, B p) := by rw [h2, h3]
    _ = Real.sqrt ((∑ p ∈ s, A p) * (∑ p ∈ s, B p)) :=
        (Real.sqrt_mul hAs (∑ p ∈ s, B p)).symm

/-! ## The statement -/

theorem abs_pairIntegral_le_sqrt {ι α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (s : Finset ι) {f g w : ι → α → ℝ} (hw : ∀ p x, 0 ≤ w p x)
    (hf : ∀ p ∈ s, MeasureTheory.Integrable (fun x => f p x ^ 2 * w p x) μ)
    (hg : ∀ p ∈ s, MeasureTheory.Integrable (fun x => g p x ^ 2 * w p x) μ)
    (hfg : ∀ p ∈ s, MeasureTheory.Integrable (fun x => f p x * g p x * w p x) μ) :
    |∑ p ∈ s, ∫ x, f p x * g p x * w p x ∂μ|
      ≤ Real.sqrt ((∑ p ∈ s, ∫ x, f p x ^ 2 * w p x ∂μ)
          * (∑ p ∈ s, ∫ x, g p x ^ 2 * w p x ∂μ)) := by
  -- per index: `|C_p| ≤ √(A_p B_p)`
  have hper : ∀ p ∈ s, |∫ x, f p x * g p x * w p x ∂μ|
      ≤ Real.sqrt ((∫ x, f p x ^ 2 * w p x ∂μ) * (∫ x, g p x ^ 2 * w p x ∂μ)) :=
    fun p hp => Real.abs_le_sqrt (pairCS_sq (hw p) (hf p hp) (hg p hp) (hfg p hp))
  -- triangle inequality over `s`
  have h1 : |∑ p ∈ s, ∫ x, f p x * g p x * w p x ∂μ|
      ≤ ∑ p ∈ s, Real.sqrt ((∫ x, f p x ^ 2 * w p x ∂μ) * (∫ x, g p x ^ 2 * w p x ∂μ)) :=
    le_trans (Finset.abs_sum_le_sum_abs (fun p => ∫ x, f p x * g p x * w p x ∂μ) s)
      (Finset.sum_le_sum hper)
  -- finite-dimensional Cauchy–Schwarz over `s`
  have h2 : (∑ p ∈ s, Real.sqrt
        ((∫ x, f p x ^ 2 * w p x ∂μ) * (∫ x, g p x ^ 2 * w p x ∂μ)))
      ≤ Real.sqrt ((∑ p ∈ s, ∫ x, f p x ^ 2 * w p x ∂μ)
          * (∑ p ∈ s, ∫ x, g p x ^ 2 * w p x ∂μ)) :=
    pairCS_finset s _ _
      (fun p _ => integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw p x))
      (fun p _ => integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw p x))
  exact le_trans h1 h2

end Work.BoseFixB1
