/-
# ZeroFreeTables/P9/P3term_abs_le_of_far

The **far** bound of HB §9.  Writing `𝓛 = L`, `α = a + λ₁` and
`w = α/((s-u)L)`, the point of the estimate is that a zero `u` which is *not* within
`δ` of the reference point `1 + i·Im s` contributes a bounded amount to the near-zero
sum of HB (9.2)–(9.7):

  `|Re P₃(α/((s-u)L))| ≤ 8α/(δL)`  whenever `δ < ‖1 + i·Im s - u‖`.

The proof is elementary.  Put `A = α/L`, `w = s - u`.  Since `Re s = 1 + a/L` and
`1 - Re u ≥ λ₁/L` (this is the hypothesis `hmin`), we have

  `Re w ≥ a/L + λ₁/L = A > 0`,

so in particular `w ≠ 0`, `X := α/((s-u)L) = A/w` and

  `Re X = A·(Re w)/|w|²`,   `|X|² = A²/|w|²`.

From `A ≤ Re w` we get (i) `Re X ≥ 0`, (ii) `Re X ≤ 1` because
`A·Re w ≤ (Re w)² ≤ |w|²`, and (iii) `|X|² ≤ Re X` because `A² ≤ A·Re w`.
The hypothesis `δ < ‖1 + i·Im s - u‖` enters through the observation that
`1 + i·Im s - u = w - a/L` has non-negative real part, so `|w - a/L| ≤ |w|`; hence
`δ < |w|` and `Re X ≤ |X| = A/|w| ≤ A/δ`.

Writing `x = Re w`, the identity `P3_re_eq`, `Re P₃(X) = (8/3)x³ + (1+2x)(x - |X|²)`,
combined with `x - |X|² ≥ 0` and `|X|² ≥ x²` finally gives

  `|Re P₃(X)| = Re P₃(X) ≤ (2/3)x³ + x² + x`,

and since `x ≤ min(1, A/δ)`, this is at most `8·(A/δ) = 8α/(δL)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3Pos

open Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

/-! ## The algebraic core -/

/-- `|w|² = (Re w)² + (Im w)²` in the shape used below. -/
private lemma normSq_eq_re_sq_add_im_sq (w : ℂ) :
    Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.normSq_apply]; ring

/-- **Algebraic core of the far bound.**  If `0 ≤ Re w ≤ 1` and `|w|² ≤ Re w`, then
`|Re P₃(w)| ≤ (2/3)(Re w)³ + (Re w)² + Re w`.

Indeed `Re P₃(w) = (8/3)x³ + (1+2x)(x - |w|²)` with `x = Re w`; both `x ≥ 0` and
`x - |w|² ≥ 0` give `Re P₃(w) ≥ 0`, and `x - |w|² ≤ x - x²` (because `|w|² ≥ x²`)
turns the identity into
`Re P₃(w) ≤ (8/3)x³ + (1+2x)x(1-x) = (2/3)x³ + x² + x`. -/
private lemma P3_re_abs_le_quad {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1)
    (hns : Complex.normSq w ≤ w.re) :
    |(Work.ZeroFreeTables.P3 w).re| ≤ (2 / 3) * w.re ^ 3 + w.re ^ 2 + w.re := by
  have hform : (Work.ZeroFreeTables.P3 w).re
      = (8 / 3) * w.re ^ 3 + (1 + 2 * w.re) * (w.re - Complex.normSq w) :=
    Work.ZeroFreeTables.P3_re_eq w
  have hx2 : w.re ^ 2 ≤ Complex.normSq w := by
    rw [normSq_eq_re_sq_add_im_sq]; nlinarith [sq_nonneg w.im]
  have h1' : 0 ≤ 1 + 2 * w.re := by linarith
  have hnn : 0 ≤ w.re - Complex.normSq w := by linarith
  have hnonneg : 0 ≤ (8 / 3) * w.re ^ 3 + (1 + 2 * w.re) * (w.re - Complex.normSq w) := by
    have h3 : 0 ≤ (8 / 3) * w.re ^ 3 := by positivity
    nlinarith [mul_nonneg h1' hnn]
  have hle : (8 / 3) * w.re ^ 3 + (1 + 2 * w.re) * (w.re - Complex.normSq w)
      ≤ (2 / 3) * w.re ^ 3 + w.re ^ 2 + w.re := by
    have hsub : w.re - Complex.normSq w ≤ w.re - w.re ^ 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsub h1'
    nlinarith [hmul]
  rw [hform, abs_of_nonneg hnonneg]
  exact hle

/-- **Final scalar step.**  For `0 ≤ x ≤ 1` and `x ≤ q`, `(2/3)x³ + x² + x ≤ 8q`:
the left side is at most `(8/3)·min(1,q)`. -/
private lemma quad_le_eight {x q : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (hxq : x ≤ q) :
    (2 / 3) * x ^ 3 + x ^ 2 + x ≤ 8 * q := by
  have hx2 : x ^ 2 ≤ x := by nlinarith [mul_le_mul_of_nonneg_left h1 h0]
  have hx3 : x ^ 3 ≤ x := by nlinarith [mul_le_mul hx2 h1 h0 h0]
  have hf8 : (2 / 3) * x ^ 3 + x ^ 2 + x ≤ (8 / 3) * x := by nlinarith [hx2, hx3]
  by_cases hq : q ≤ 1
  · have hq0 : 0 ≤ q := le_trans h0 hxq
    have hq2 : q ^ 2 ≤ q := by nlinarith [mul_le_mul_of_nonneg_left hq hq0]
    have hq3 : q ^ 3 ≤ q := by nlinarith [mul_le_mul hq2 hq hq0 hq0]
    have hx2' : x ^ 2 ≤ q ^ 2 := by nlinarith [mul_le_mul hxq hxq h0 hq0]
    have hx3' : x ^ 3 ≤ q ^ 3 := by nlinarith [mul_le_mul hx2' hxq h0 (sq_nonneg q)]
    have hmono : (2 / 3) * x ^ 3 + x ^ 2 + x ≤ (2 / 3) * q ^ 3 + q ^ 2 + q := by
      nlinarith [hx2', hx3', hxq]
    have hq8 : (2 / 3) * q ^ 3 + q ^ 2 + q ≤ 8 * q := by nlinarith [hq2, hq3]
    linarith
  · have hq1 : (1 : ℝ) ≤ q := le_of_lt (lt_of_not_ge hq)
    nlinarith [hf8, hxq, hq1]

/-! ## The geometric facts about `α/((s-u)L)` -/

/-- **Geometry of the far case.**  With `A = α/L` and `w = s - u` (so `X = A/w`):
`0 ≤ Re X ≤ 1`, `|X|² ≤ Re X`, and `Re X ≤ A/δ`. -/
private lemma p3arg_facts_of_far {a lam₁ L δ : ℝ} {s u : ℂ} (hL : 0 < L) (ha : 0 < a)
    (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hmin : lam₁ ≤ (1 - u.re) * L)
    (hsre : s.re = 1 + a / L)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    0 ≤ (((a + lam₁) / ((s - u) * (L : ℂ)))).re ∧
      (((a + lam₁) / ((s - u) * (L : ℂ)))).re ≤ 1 ∧
      Complex.normSq ((a + lam₁) / ((s - u) * (L : ℂ)))
        ≤ (((a + lam₁) / ((s - u) * (L : ℂ)))).re ∧
      (((a + lam₁) / ((s - u) * (L : ℂ)))).re ≤ (a + lam₁) / (δ * L) := by
  set A : ℝ := (a + lam₁) / L with hA
  set w : ℂ := s - u with hw
  have hApos : 0 < A := by rw [hA]; positivity
  have hwre : w.re = 1 + a / L - u.re := by rw [hw, Complex.sub_re, hsre]
  have hσ : 0 ≤ 1 - u.re := by
    have h : lam₁ / L ≤ 1 - u.re := by rw [div_le_iff₀ hL]; linarith
    have h0 : 0 ≤ lam₁ / L := div_nonneg hlam₁ hL.le
    linarith
  have hAle : A ≤ w.re := by
    rw [hA, hwre]
    have h : lam₁ / L ≤ 1 - u.re := by rw [div_le_iff₀ hL]; linarith
    have he : (a + lam₁) / L = a / L + lam₁ / L := by ring
    rw [he]; linarith
  have hwpos : 0 < w.re := lt_of_lt_of_le hApos hAle
  have hDpos : 0 < Complex.normSq w := by
    rw [normSq_eq_re_sq_add_im_sq]; nlinarith [hwpos]
  -- `X = A · w⁻¹`
  have hX : (a + lam₁) / ((s - u) * (L : ℂ)) = ((A : ℝ) : ℂ) * w⁻¹ := by
    have hAc : ((A : ℝ) : ℂ) = ((a : ℂ) + (lam₁ : ℂ)) / (L : ℂ) := by
      rw [hA]; push_cast; ring
    rw [hw, hAc]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    push_cast
    ring
  have hreX : (((a + lam₁) / ((s - u) * (L : ℂ)))).re
      = A * (w.re / Complex.normSq w) := by
    rw [hX, Complex.mul_re, Complex.inv_re]
    simp [Complex.ofReal_re, Complex.ofReal_im]
  have hnsX : Complex.normSq ((a + lam₁) / ((s - u) * (L : ℂ)))
      = A ^ 2 / Complex.normSq w := by
    rw [hX, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal]
    ring
  -- `‖1 + i·Im s - u‖ ≤ ‖w‖`
  have hnorm_le : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ ‖w‖ := by
    have hsq : Complex.normSq ((1 : ℂ) + (s.im : ℂ) * Complex.I - u) ≤ Complex.normSq w := by
      have h1 : (1 : ℂ) + (s.im : ℂ) * Complex.I - u
          = ((1 - u.re : ℝ) : ℂ) + ((s.im - u.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
        · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have h2 : w = ((1 - u.re + a / L : ℝ) : ℂ) + ((s.im - u.im : ℝ) : ℂ) * Complex.I := by
        rw [hw]
        apply Complex.ext
        · simp [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, hsre]
          ring
        · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
      rw [h1, h2, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
      have haL : 0 ≤ a / L := div_nonneg ha.le hL.le
      have hcb : 1 - u.re ≤ 1 - u.re + a / L := by linarith
      have hc0 : 0 ≤ 1 - u.re + a / L := by linarith
      nlinarith [mul_le_mul hcb hcb hσ hc0, sq_nonneg (s.im - u.im)]
    have h2 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      exact hsq
    nlinarith [norm_nonneg ((1 : ℂ) + (s.im : ℂ) * Complex.I - u), norm_nonneg w]
  have hwlt : δ < ‖w‖ := lt_of_lt_of_le hfar hnorm_le
  have hwnormpos : 0 < ‖w‖ := lt_of_lt_of_le hwpos (Complex.re_le_norm w)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hreX]; positivity
  · rw [hreX]
    rw [show A * (w.re / Complex.normSq w) = A * w.re / Complex.normSq w from
      (mul_div_assoc A w.re (Complex.normSq w)).symm]
    rw [div_le_one hDpos]
    rw [normSq_eq_re_sq_add_im_sq]
    nlinarith [mul_le_mul_of_nonneg_right hAle hwpos.le, sq_nonneg w.im]
  · rw [hnsX, hreX]
    rw [show A * (w.re / Complex.normSq w) = A * w.re / Complex.normSq w from
      (mul_div_assoc A w.re (Complex.normSq w)).symm]
    rw [div_le_div_iff_of_pos_right hDpos]
    nlinarith [mul_le_mul_of_nonneg_left hAle hApos.le]
  · have hnormX : ‖((a + lam₁) / ((s - u) * (L : ℂ)))‖ = A * (‖w‖)⁻¹ := by
      have hA_norm : ‖((A : ℝ) : ℂ)‖ = A := by
        have h2 : ‖((A : ℝ) : ℂ)‖ ^ 2 = A ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
        nlinarith [norm_nonneg ((A : ℝ) : ℂ)]
      rw [hX, norm_mul, norm_inv, hA_norm]
    calc (((a + lam₁) / ((s - u) * (L : ℂ)))).re
        ≤ ‖((a + lam₁) / ((s - u) * (L : ℂ)))‖ := Complex.re_le_norm _
      _ = A * (‖w‖)⁻¹ := hnormX
      _ ≤ A * δ⁻¹ :=
          mul_le_mul_of_nonneg_left ((inv_le_inv₀ hwnormpos hδ).mpr hwlt.le) hApos.le
      _ = (a + lam₁) / (δ * L) := by
          rw [hA, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]; ring

/-! ## The far bound -/

theorem P3term_abs_le_of_far {a lam₁ L δ : ℝ} (hL : 0 < L) (ha : 0 < a)
    (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (haδ : 2 * a ≤ δ * L) {s u : ℂ}
    (hsre : s.re = 1 + a / L) (hmin : lam₁ ≤ (1 - u.re) * L)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    |(Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re|
      ≤ 8 * (a + lam₁) / (δ * L) := by
  obtain ⟨hX0, hX1, hXns, hXq⟩ := p3arg_facts_of_far hL ha hlam₁ hδ hmin hsre hfar
  have hcore := P3_re_abs_le_quad hX0 hX1 hXns
  have hscal := quad_le_eight hX0 hX1 hXq
  calc |(Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re|
      ≤ (2 / 3) * (((a + lam₁) / ((s - u) * (L : ℂ)))).re ^ 3
        + (((a + lam₁) / ((s - u) * (L : ℂ)))).re ^ 2
        + (((a + lam₁) / ((s - u) * (L : ℂ)))).re := hcore
    _ ≤ 8 * ((a + lam₁) / (δ * L)) := hscal
    _ = 8 * (a + lam₁) / (δ * L) := by ring

end Work.ZeroFreeTables.P9
