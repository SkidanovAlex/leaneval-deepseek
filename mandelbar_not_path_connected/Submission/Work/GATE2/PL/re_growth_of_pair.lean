import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

/-- **The one-variable inequality behind the pair estimate.**

Suppose `(A - a)² + b² ≤ C²·(a² + b²)` with `0 ≤ C < 1` and `a ≥ 0`.  Then
`A ≥ (1 - C/√(1-C²))·a`.

(Actually `A ≥ (1-C)·a` holds — the `1 - C/√(1-C²)` of the statement is the
weaker, but geometrically natural, constant coming from the two perpendicular
directions of the pair `(a,b)`: writing `e = (A-a) - b·i` and `d = a + b·i`,
the hypothesis is `‖e‖ ≤ C‖d‖`; comparing imaginary parts forces
`|b| ≤ C‖d‖ = C·√(a²+b²)`, whence `(A-a)² ≤ (1-C²)‖d‖²`, and adding the two
coordinate estimates recovers `A ≥ (1-C/√(1-C²))a` with `C/√(1-C²)` the
optimum obtained by balancing them.  The proof below uses the sharper
`1 - C`, which is enough since `√(1-C²) ≤ 1`.) -/
private lemma re_growth_aux {A a b C : ℝ} (hC0 : 0 ≤ C) (hC1 : C < 1) (ha : 0 ≤ a)
    (h : (A - a) ^ 2 + b ^ 2 ≤ C ^ 2 * (a ^ 2 + b ^ 2)) :
    (1 - C / Real.sqrt (1 - C ^ 2)) * a ≤ A := by
  have hC2 : C ^ 2 < 1 := by nlinarith
  -- Dropping the (non-negative) `b²` term, using `C² ≤ 1`:
  have h1 : (A - a) ^ 2 ≤ (C * a) ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg b]
  have h2 : |A - a| ≤ C * a := by
    have := (sq_le_sq.mp h1)
    rwa [abs_of_nonneg (mul_nonneg hC0 ha)] at this
  -- Hence `A ≥ (1 - C) a`, which is at least as strong as the claim.
  have hA : (1 - C) * a ≤ A := by
    have := (abs_le.mp h2).1
    linarith
  have hD : 0 < 1 - C ^ 2 := by linarith
  have hs0 : 0 < Real.sqrt (1 - C ^ 2) := Real.sqrt_pos.mpr hD
  have hs1 : Real.sqrt (1 - C ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [sq_nonneg C])
  have hcoef : 1 - C / Real.sqrt (1 - C ^ 2) ≤ 1 - C := by
    have : C ≤ C / Real.sqrt (1 - C ^ 2) := by
      rw [le_div_iff₀ hs0]
      nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hs1)]
    linarith
  exact le_trans (mul_le_mul_of_nonneg_right hcoef ha) hA

/-- **Real-part growth of a pair with equal imaginary parts.**

Let `ψ : ℂ → ℂ` be `C`-close to the identity on the right half-plane
`{Re > N}` in the uniform sense
`‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C‖w₂ - w₁‖` with `0 ≤ C < 1`.  If two points
`w₁ = s₀ + t₀ i`, `w₂ = s₁ + t₁ i` of that half-plane with `s₀ ≤ s₁` satisfy
`Im (ψ w₂) = Im (ψ w₁)`, then the real part of `ψ` grows at least linearly
from `w₁` to `w₂`:
`(1 - C/√(1-C²))·(s₁ - s₀) ≤ Re (ψ w₂) - Re (ψ w₁)`.

Indeed `ψ w₂ - ψ w₁ = A + 0·i` with `A = Re (ψ w₂) - Re (ψ w₁)`, while
`w₂ - w₁ = a + b i` with `a = s₁ - s₀ ≥ 0` and `b = t₁ - t₀`, so
`e := ψ w₂ - ψ w₁ - (w₂ - w₁) = (A - a) - b i` and the hypothesis squared gives
`(A - a)² + b² ≤ C²(a² + b²)`; the auxiliary inequality above finishes. -/
theorem re_growth_of_pair {ψ : ℂ → ℂ} {N C : ℝ} (hCnn : 0 ≤ C) (hC1 : C < 1)
    (hpair : ∀ w₁ w₂ : ℂ, N < w₁.re → N < w₂.re →
      ‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C * ‖w₂ - w₁‖)
    {s₀ s₁ t₀ t₁ : ℝ} (h₀ : N < s₀) (hs : s₀ ≤ s₁)
    (him : (ψ (s₀ + (t₀ : ℂ) * Complex.I)).im = (ψ (s₁ + (t₁ : ℂ) * Complex.I)).im) :
    (1 - C / Real.sqrt (1 - C ^ 2)) * (s₁ - s₀) ≤
      (ψ (s₁ + (t₁ : ℂ) * Complex.I)).re - (ψ (s₀ + (t₀ : ℂ) * Complex.I)).re := by
  set z₀ : ℂ := (s₀ : ℂ) + (t₀ : ℂ) * Complex.I with hz₀
  set z₁ : ℂ := (s₁ : ℂ) + (t₁ : ℂ) * Complex.I with hz₁
  have hz₀re : z₀.re = s₀ := by rw [hz₀]; simp
  have hz₁re : z₁.re = s₁ := by rw [hz₁]; simp
  have hz₀im : z₀.im = t₀ := by rw [hz₀]; simp
  have hz₁im : z₁.im = t₁ := by rw [hz₁]; simp
  have him' : (ψ z₀).im = (ψ z₁).im := him
  set A : ℝ := (ψ z₁).re - (ψ z₀).re with hA
  set a : ℝ := s₁ - s₀ with ha
  set b : ℝ := t₁ - t₀ with hb
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hp := hpair z₀ z₁ (by rw [hz₀re]; exact h₀)
    (by rw [hz₁re]; exact lt_of_lt_of_le h₀ hs)
  -- The real and imaginary parts of the defect `e = ψ z₁ - ψ z₀ - (z₁ - z₀)`.
  have he_re : (ψ z₁ - ψ z₀ - (z₁ - z₀)).re = A - a := by
    simp only [Complex.sub_re, hA, ha, hz₁re, hz₀re]
  have he_im : (ψ z₁ - ψ z₀ - (z₁ - z₀)).im = -b := by
    simp only [Complex.sub_im, hb, hz₁im, hz₀im, him']; ring
  have hd_re : (z₁ - z₀).re = a := by
    simp only [Complex.sub_re, hz₁re, hz₀re, ha]
  have hd_im : (z₁ - z₀).im = b := by
    simp only [Complex.sub_im, hz₁im, hz₀im, hb]
  -- Square the pair hypothesis.
  have hnorm : ‖ψ z₁ - ψ z₀ - (z₁ - z₀)‖ ^ 2 ≤ C ^ 2 * ‖z₁ - z₀‖ ^ 2 := by
    have hsq : ‖ψ z₁ - ψ z₀ - (z₁ - z₀)‖ ^ 2 ≤ (C * ‖z₁ - z₀‖) ^ 2 := by
      apply sq_le_sq'
      · nlinarith [norm_nonneg (ψ z₁ - ψ z₀ - (z₁ - z₀)),
          mul_nonneg hCnn (norm_nonneg (z₁ - z₀))]
      · exact hp
    simpa only [mul_pow] using hsq
  -- Rewrite both squared norms through the real/imaginary parts.
  have hE : ‖ψ z₁ - ψ z₀ - (z₁ - z₀)‖ ^ 2 = (A - a) ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, he_re, he_im]; ring
  have hD : ‖z₁ - z₀‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hd_re, hd_im]; ring
  have hmain : (A - a) ^ 2 + b ^ 2 ≤ C ^ 2 * (a ^ 2 + b ^ 2) := by
    rw [← hE, ← hD]; exact hnorm
  exact re_growth_aux hCnn hC1 ha0 hmain

end Work.GATE2.PL
