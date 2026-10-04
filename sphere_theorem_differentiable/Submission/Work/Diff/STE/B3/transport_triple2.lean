import Mathlib
import Submission.Work.Diff.STE.B3.Comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-!
# The Leibniz rule of order two for the partial derivatives `pdR`

`Work.Diff.STE.pdR i f x = fderiv ℝ f x (Pi.single i 1)` is the `i`-th partial derivative of a real
function on `Fin n → ℝ`.  This file proves the second order Leibniz rule for `pdR` (for a product of
two functions of class `C²`) and applies it twice to obtain the expansion of the mixed second
derivative `∂_c ∂_d (A · B · C)` of a triple product into the nine terms in which exactly one of
`A`, `B`, `C` (resp. `A · B`) is differentiated twice.
-/

/-- **Leibniz rule for the first partial derivative.**  For functions `f g` differentiable at `z`,
`∂_p (f · g)(z) = f z · ∂_p g z + g z · ∂_p f z`. -/
private lemma pdR_mul {d : ℕ} {f g : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} (p : Fin d)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    Work.Diff.STE.pdR p (fun y => f y * g y) z
      = f z * Work.Diff.STE.pdR p g z + g z * Work.Diff.STE.pdR p f z := by
  show fderiv ℝ (fun y => f y * g y) z (Pi.single p 1) = _
  rw [fderiv_fun_mul hf hg]
  simp [Work.Diff.STE.pdR, smul_eq_mul]

/-- **Second order Leibniz rule.**  For `f` and `g` of class `C²` at `z`,

`∂_q∂_p (f · g)(z) = f z · ∂_q∂_p g z + ∂_p g z · ∂_q f z + ∂_q g z · ∂_p f z
  + g z · ∂_q∂_p f z`.

The proof differentiates the `C⁰` Leibniz identity `pdR p (f · g) = f · ∂_p g + g · ∂_p f`, valid on
a neighbourhood of `z` (`ContDiffAt.eventually`), using `EventuallyEq.fderiv_eq`, `fderiv_add` and
`fderiv_fun_mul`. -/
private lemma pdR2_mul {d : ℕ} {f g : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} (q p : Fin d)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => f y * g y)) z
      = f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
        + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
        + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
        + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z := by
  have hdf : DifferentiableAt ℝ f z := hf.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hdfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hdgd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hdfp : DifferentiableAt ℝ (Work.Diff.STE.pdR p f) z := by
    have h :=
      (hdfd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1 : ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single p (1 : ℝ))) z
    exact h
  have hdgp : DifferentiableAt ℝ (Work.Diff.STE.pdR p g) z := by
    have h :=
      (hdgd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1 : ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ g y (Pi.single p (1 : ℝ))) z
    exact h
  have hev : Work.Diff.STE.pdR p (fun y => f y * g y) =ᶠ[nhds z]
      (fun y => f y * Work.Diff.STE.pdR p g y + g y * Work.Diff.STE.pdR p f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact pdR_mul p (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hd1 : DifferentiableAt ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z := hdf.mul hdgp
  have hd2 : DifferentiableAt ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z := hdg.mul hdfp
  have hsum : fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y
        + g y * Work.Diff.STE.pdR p f y) z
      = fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z
        + fderiv ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z := fderiv_add hd1 hd2
  calc Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => f y * g y)) z
      = fderiv ℝ (Work.Diff.STE.pdR p (fun y => f y * g y)) z (Pi.single q 1) := rfl
    _ = fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y + g y * Work.Diff.STE.pdR p f y) z
          (Pi.single q 1) := by rw [hev.fderiv_eq]
    _ = (fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z
           + fderiv ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z) (Pi.single q 1) := by
          rw [hsum]
    _ = f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
        + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
        + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
        + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z := by
          rw [fderiv_fun_mul hdf hdgp, fderiv_fun_mul hdg hdfp]
          simp only [Work.Diff.STE.pdR, add_apply, smul_apply, smul_eq_mul]
          ring

theorem transport_triple2 {n : ℕ} (A B C : (Fin n → ℝ) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B) (hC : ContDiff ℝ (⊤ : ℕ∞) C)
    (c d : Fin n) (z : Fin n → ℝ) :
    Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y * C y)) z
      = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d A) z * B z * C z
        + Work.Diff.STE.pdR c A z * Work.Diff.STE.pdR d B z * C z
        + Work.Diff.STE.pdR c A z * B z * Work.Diff.STE.pdR d C z
        + Work.Diff.STE.pdR d A z * Work.Diff.STE.pdR c B z * C z
        + Work.Diff.STE.pdR d A z * B z * Work.Diff.STE.pdR c C z
        + A z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d B) z * C z
        + A z * Work.Diff.STE.pdR c B z * Work.Diff.STE.pdR d C z
        + A z * Work.Diff.STE.pdR d B z * Work.Diff.STE.pdR c C z
        + A z * B z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d C) z := by
  have hA2 : ContDiffAt ℝ 2 A z := hA.contDiffAt.of_le (by simp)
  have hB2 : ContDiffAt ℝ 2 B z := hB.contDiffAt.of_le (by simp)
  have hC2 : ContDiffAt ℝ 2 C z := hC.contDiffAt.of_le (by simp)
  have hAB2 : ContDiffAt ℝ 2 (fun y => A y * B y) z := hA2.mul hB2
  have hAd : DifferentiableAt ℝ A z := hA2.differentiableAt (by norm_num)
  have hBd : DifferentiableAt ℝ B z := hB2.differentiableAt (by norm_num)
  -- first order Leibniz rule, applied to `A * B`
  have hABd : Work.Diff.STE.pdR d (fun y => A y * B y) z
      = A z * Work.Diff.STE.pdR d B z + B z * Work.Diff.STE.pdR d A z :=
    pdR_mul d hAd hBd
  have hABc : Work.Diff.STE.pdR c (fun y => A y * B y) z
      = A z * Work.Diff.STE.pdR c B z + B z * Work.Diff.STE.pdR c A z :=
    pdR_mul c hAd hBd
  -- second order Leibniz rule, applied to `A * B`
  have h2 : Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y)) z
      = A z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d B) z
        + Work.Diff.STE.pdR d B z * Work.Diff.STE.pdR c A z
        + Work.Diff.STE.pdR c B z * Work.Diff.STE.pdR d A z
        + B z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d A) z :=
    pdR2_mul c d hA2 hB2
  -- second order Leibniz rule, applied to `(A * B) * C`
  have hmain : Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y * C y)) z
      = (A z * B z) * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d C) z
        + Work.Diff.STE.pdR d C z * Work.Diff.STE.pdR c (fun y => A y * B y) z
        + Work.Diff.STE.pdR c C z * Work.Diff.STE.pdR d (fun y => A y * B y) z
        + C z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y)) z :=
    pdR2_mul c d hAB2 hC2
  rw [hmain, hABd, hABc, h2]
  ring

end Work.Diff.STE.B3
