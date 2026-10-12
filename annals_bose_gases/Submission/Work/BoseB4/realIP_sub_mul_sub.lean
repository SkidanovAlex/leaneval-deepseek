import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.realIP_sub_mul_sub`

The real inner product `B.realIP f g = ∫ Re(conj(f x) · g x)` of `BoxChi` is
bilinear over the reals: for real scalars `c d`,

    `realIP (f − c g) (h − d j) = realIP f h − d·realIP f j − c·realIP g h + c·d·realIP g j`.

This is what lets FS's expressions `φ = f − c·g` (`eq:DefQ` and the split of the
trial state into `θ` and `Q`-parts) be expanded term by term.  The proof is the
pointwise expansion of the complex integrand (`re_conj_sub_mul_sub`, using that
`c, d` are real, hence fixed by complex conjugation) followed by the linearity of
the Bochner integral (`integral_add`, `integral_sub`, `integral_const_mul`), the
four integrability hypotheses being exactly the integrability of the four
elementary products.
-/

noncomputable section

namespace Work.BoseB4

/-- Pointwise form of the bilinearity: with `c d` real,
`Re(conj(z − c w)·(u − d v)) = Re(conj z · u) − d·Re(conj z · v) − c·Re(conj w · u) + c·d·Re(conj w · v)`. -/
private lemma re_conj_sub_mul_sub (z w u v : ℂ) (c d : ℝ) :
    ((starRingEnd ℂ) (z - (c : ℂ) * w) * (u - (d : ℂ) * v)).re
      = ((starRingEnd ℂ) z * u).re - d * ((starRingEnd ℂ) z * v).re
        - c * ((starRingEnd ℂ) w * u).re + c * d * ((starRingEnd ℂ) w * v).re := by
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.sub_re,
    Complex.mul_im, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem realIP_sub_mul_sub (B : Work.BoseB4.BoxData)
    (f g h j : EuclideanSpace ℝ (Fin 3) → ℂ) (c d : ℝ)
    (hfh : MeasureTheory.Integrable fun x => ((starRingEnd ℂ) (f x) * h x).re)
    (hfj : MeasureTheory.Integrable fun x => ((starRingEnd ℂ) (f x) * j x).re)
    (hgh : MeasureTheory.Integrable fun x => ((starRingEnd ℂ) (g x) * h x).re)
    (hgj : MeasureTheory.Integrable fun x => ((starRingEnd ℂ) (g x) * j x).re) :
    B.realIP (fun x => f x - (c : ℂ) * g x) (fun x => h x - (d : ℂ) * j x)
      = B.realIP f h - d * B.realIP f j - c * B.realIP g h + c * d * B.realIP g j := by
  simp only [Work.BoseB4.BoxData.realIP_apply]
  -- expand the integrand pointwise
  have hkey : ∀ x : EuclideanSpace ℝ (Fin 3),
      ((starRingEnd ℂ) (f x - (c : ℂ) * g x) * (h x - (d : ℂ) * j x)).re
        = ((starRingEnd ℂ) (f x) * h x).re - d * ((starRingEnd ℂ) (f x) * j x).re
          - c * ((starRingEnd ℂ) (g x) * h x).re
          + c * d * ((starRingEnd ℂ) (g x) * j x).re :=
    fun x => re_conj_sub_mul_sub (f x) (g x) (h x) (j x) c d
  rw [funext hkey]
  -- integrability of the pieces, in the exact shape they occur
  have h1 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((starRingEnd ℂ) (f x) * h x).re - d * ((starRingEnd ℂ) (f x) * j x).re
        - c * ((starRingEnd ℂ) (g x) * h x).re) :=
    (hfh.sub (hfj.const_mul d)).sub (hgh.const_mul c)
  have h2 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      c * d * ((starRingEnd ℂ) (g x) * j x).re) := hgj.const_mul (c * d)
  have h3 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((starRingEnd ℂ) (f x) * h x).re - d * ((starRingEnd ℂ) (f x) * j x).re) :=
    hfh.sub (hfj.const_mul d)
  have h4 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      c * ((starRingEnd ℂ) (g x) * h x).re) := hgh.const_mul c
  -- linearity of the integral
  calc ∫ x, (((starRingEnd ℂ) (f x) * h x).re - d * ((starRingEnd ℂ) (f x) * j x).re
        - c * ((starRingEnd ℂ) (g x) * h x).re + c * d * ((starRingEnd ℂ) (g x) * j x).re)
      = (∫ x, (((starRingEnd ℂ) (f x) * h x).re - d * ((starRingEnd ℂ) (f x) * j x).re
        - c * ((starRingEnd ℂ) (g x) * h x).re)) + ∫ x, c * d * ((starRingEnd ℂ) (g x) * j x).re :=
        MeasureTheory.integral_add h1 h2
    _ = ((∫ x, (((starRingEnd ℂ) (f x) * h x).re - d * ((starRingEnd ℂ) (f x) * j x).re))
          - ∫ x, c * ((starRingEnd ℂ) (g x) * h x).re)
          + ∫ x, c * d * ((starRingEnd ℂ) (g x) * j x).re := by
        rw [MeasureTheory.integral_sub h3 h4]
    _ = (((∫ x, ((starRingEnd ℂ) (f x) * h x).re) - ∫ x, d * ((starRingEnd ℂ) (f x) * j x).re)
          - ∫ x, c * ((starRingEnd ℂ) (g x) * h x).re)
          + ∫ x, c * d * ((starRingEnd ℂ) (g x) * j x).re := by
        rw [MeasureTheory.integral_sub hfh (hfj.const_mul d)]
    _ = (((∫ x, ((starRingEnd ℂ) (f x) * h x).re) - d * ∫ x, ((starRingEnd ℂ) (f x) * j x).re)
          - c * ∫ x, ((starRingEnd ℂ) (g x) * h x).re)
          + c * d * ∫ x, ((starRingEnd ℂ) (g x) * j x).re := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]

end Work.BoseB4
