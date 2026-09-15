import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m1
import Submission.Commons.NumberTheory.Zeta.measurable_riemannZeta

namespace Commons.NumberTheory.Zeta

open MeasureTheory

/-- The Green–Tao kernel along the vertical line `Γ₁`, with the constant weight `f ≡ 1`,
is a measurable function of the two parameters `(t, t') ↦ (zetaM1Eta R t, zetaM1Eta R t')`.

Each factor is a composition of the continuous (hence measurable) map
`p ↦ (zetaM1Eta R p.1, zetaM1Eta R p.2)` with a measurable function of `(z, z')`:
`riemannZeta` is measurable, `z ↦ R ^ z` is continuous for `R ≠ 0`, and products,
quotients and powers are measurable. -/
theorem measurable_zetaM1Kernel_eta {R : ℝ} (hR : R ≠ 0) :
    Measurable (fun p : ℝ × ℝ =>
      Commons.NumberTheory.Zeta.zetaM1Kernel R (fun _ _ => (1:ℂ))
        (Commons.NumberTheory.Zeta.zetaM1Eta R p.1)
        (Commons.NumberTheory.Zeta.zetaM1Eta R p.2)) := by
  have hz1 : Measurable (fun p : ℝ × ℝ => zetaM1Eta R p.1) :=
    (zetaM1Eta_continuous R).measurable.comp measurable_fst
  have hz2 : Measurable (fun p : ℝ × ℝ => zetaM1Eta R p.2) :=
    (zetaM1Eta_continuous R).measurable.comp measurable_snd
  have hZ3 : Measurable (fun p : ℝ × ℝ => riemannZeta
      (1 + zetaM1Eta R p.1 + zetaM1Eta R p.2)) :=
    measurable_riemannZeta.comp ((measurable_const.add hz1).add hz2)
  have hZ1 : Measurable (fun p : ℝ × ℝ => riemannZeta
      (1 + zetaM1Eta R p.1)) :=
    measurable_riemannZeta.comp (measurable_const.add hz1)
  have hZ2 : Measurable (fun p : ℝ × ℝ => riemannZeta
      (1 + zetaM1Eta R p.2)) :=
    measurable_riemannZeta.comp (measurable_const.add hz2)
  have hRne : (R:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  have hinst : NeZero (R:ℂ) := ⟨hRne⟩
  have hD : Measurable (fun p : ℝ × ℝ => (R:ℂ) ^
      (zetaM1Eta R p.1 + zetaM1Eta R p.2)) :=
    (continuous_const_cpow (R:ℂ)).measurable.comp (hz1.add hz2)
  have hE : Measurable (fun p : ℝ × ℝ =>
      zetaM1Eta R p.1 ^ 2 * zetaM1Eta R p.2 ^ 2) :=
    (hz1.pow_const 2).mul (hz2.pow_const 2)
  have hmain : Measurable (fun p : ℝ × ℝ =>
      (1:ℂ) * (riemannZeta (1 + zetaM1Eta R p.1 + zetaM1Eta R p.2)
          / (riemannZeta (1 + zetaM1Eta R p.1) * riemannZeta (1 + zetaM1Eta R p.2)))
        * (R:ℂ) ^ (zetaM1Eta R p.1 + zetaM1Eta R p.2)
        / (zetaM1Eta R p.1 ^ 2 * zetaM1Eta R p.2 ^ 2)) :=
    ((measurable_const.mul (hZ3.div (hZ1.mul hZ2))).mul hD).div hE
  simpa only [zetaM1Kernel] using hmain

end Commons.NumberTheory.Zeta
