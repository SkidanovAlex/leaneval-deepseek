import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.dz_star_comp
import Submission.Work.MRMT.Found.dzbar_star_comp
import Submission.Work.MRMT.Found.dzbar_symm_le
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo
import Submission.Work.MRMT.Sobolev.QCCompAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-- **Pointwise energy comparison.**  Under the hypotheses of the main theorem, at every point
`w` the `∂`-energy density of `star ∘ F ∘ f ∘ F.symm` is bounded by `4/(1-k²)` times the
`∂`-energy density of `star ∘ F ∘ f` at `F.symm w`, weighted by the Jacobian determinant of
`F.symm`.

The proof combines the Wirtinger chain rule for `G ∘ F.symm` (with `G = star ∘ F ∘ f`), the
pointwise dilatation bound `‖∂̄G‖ ≤ k ‖∂G‖` for the orientation-preserving quasiconformal map
`G` (which follows from the anti-holomorphy of `f` and the Beltrami relation for `F`), the
inverse-map dilatation bound `‖∂̄(F.symm)‖ ≤ k ‖∂(F.symm)‖`, and the algebraic identity
`det D(F.symm) = ‖∂(F.symm)‖² - ‖∂̄(F.symm)‖²`. -/
private theorem pointwise_le {F : ℂ ≃ₜ ℂ} {μF f : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hbelt : ∀ z : ℂ, Work.MRMT.dzbar (F : ℂ → ℂ) z = μF z * Work.MRMT.dz (F : ℂ → ℂ) z)
    (hμ : ∀ z : ℂ, ‖μF z‖ ≤ k) (hf : Differentiable ℂ (star ∘ f)) (w : ℂ) :
    ENNReal.ofReal (‖Work.MRMT.dz ((star ∘ (F : ℂ → ℂ) ∘ f) ∘ (F.symm : ℂ → ℂ)) w‖ ^ 2) ≤
      ENNReal.ofReal (4 / (1 - k ^ 2)) *
        (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
          ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|) := by
  have hk2pos : 0 < 1 - k ^ 2 := by nlinarith [sq_nonneg k]
  set H : ℂ → ℂ := (F.symm : ℂ → ℂ) with hHdef
  set G : ℂ → ℂ := star ∘ (F : ℂ → ℂ) ∘ f with hGdef
  have hHdiff : DifferentiableAt ℝ H w :=
    (hFs.contDiffAt (x := w)).differentiableAt (by norm_num)
  have hfR : DifferentiableAt ℝ f (H w) :=
    Work.MRMT.Wirtinger.differentiableAt_of_antiholo (hf (H w))
  have hFf : DifferentiableAt ℝ ((F : ℂ → ℂ) ∘ f) (H w) :=
    ((hF.contDiffAt (x := f (H w))).differentiableAt (by norm_num)).comp (H w) hfR
  have hGdiff : DifferentiableAt ℝ G (H w) :=
    (Work.MRMT.Wirtinger.differentiableAt_star (F (f (H w)))).comp (H w) hFf
  have hchain := Work.MRMT.Wirtinger.dz_comp (f := H) (g := G) hGdiff hHdiff
  have hdilG : ‖Work.MRMT.dzbar G (H w)‖ ≤ k * ‖Work.MRMT.dz G (H w)‖ := by
    have hdzf : Work.MRMT.dz f (H w) = 0 := Work.MRMT.Wirtinger.dz_of_antiholo (hf (H w))
    have hFat : DifferentiableAt ℝ (F : ℂ → ℂ) (f (H w)) :=
      (hF.contDiffAt (x := f (H w))).differentiableAt (by norm_num)
    have h1 := Work.MRMT.Found.dzbar_star_comp (F := (F : ℂ → ℂ)) (f := f) (μF := μF)
        (z := H w) hFat hfR (hbelt (f (H w)))
    have h2 := Work.MRMT.Found.dz_star_comp (F := (F : ℂ → ℂ)) (f := f) (μF := μF)
        (z := H w) hFat hfR (hbelt (f (H w)))
    rw [hGdef, h1, h2]
    simp only [hdzf, star_zero, mul_zero, zero_add, add_zero]
    simp only [norm_mul, norm_star]
    set A : ℝ := ‖Work.MRMT.dz (F : ℂ → ℂ) (f (H w))‖ with hAdef
    set B : ℝ := ‖Work.MRMT.dzbar f (H w)‖ with hBdef
    set M : ℝ := ‖μF (f (H w))‖ with hMdef
    calc A * (M * B) = (A * B) * M := by ring
      _ ≤ (A * B) * k := mul_le_mul_of_nonneg_left (hμ (f (H w))) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = k * (A * B) := by ring
  have hdilH : ‖Work.MRMT.dzbar H w‖ ≤ k * ‖Work.MRMT.dz H w‖ :=
    (Work.MRMT.Found.dzbar_symm_le F μF k hF hFs hbelt hμ).1 w
  set P : ℝ := ‖Work.MRMT.dz H w‖ with hPdef
  set Q : ℝ := ‖Work.MRMT.dzbar H w‖ with hQdef
  set A : ℝ := ‖Work.MRMT.dz G (H w)‖ with hAdef
  set B : ℝ := ‖Work.MRMT.dzbar G (H w)‖ with hBdef
  have hPnn : 0 ≤ P := norm_nonneg _
  have hQnn : 0 ≤ Q := norm_nonneg _
  have hAnn : 0 ≤ A := norm_nonneg _
  have hBnn : 0 ≤ B := norm_nonneg _
  set det : ℝ := (fderiv ℝ H w).det with hdetdef
  have hdet_eq : det = P ^ 2 - Q ^ 2 := Work.MRMT.Sobolev.det_fderiv_eq H w
  have hBQ : B * Q ≤ k ^ 2 * (A * P) := by
    calc B * Q ≤ (k * A) * (k * P) := mul_le_mul hdilG hdilH hQnn (by positivity)
      _ = k ^ 2 * (A * P) := by ring
  have hstep1 : ‖Work.MRMT.dz (G ∘ H) w‖ ≤ A * P + B * Q := by
    rw [hchain]
    calc ‖Work.MRMT.dz G (H w) * Work.MRMT.dz H w + Work.MRMT.dzbar G (H w) * star (Work.MRMT.dzbar H w)‖
        ≤ ‖Work.MRMT.dz G (H w) * Work.MRMT.dz H w‖ + ‖Work.MRMT.dzbar G (H w) * star (Work.MRMT.dzbar H w)‖ := norm_add_le _ _
      _ = A * P + B * Q := by simp only [hAdef, hPdef, hBdef, hQdef, norm_mul, norm_star]
  have hstep2 : A * P + B * Q ≤ 2 * (A * P) := by
    have h1 : A * P + B * Q ≤ A * P + k ^ 2 * (A * P) := add_le_add le_rfl hBQ
    have h2 : A * P + k ^ 2 * (A * P) = (1 + k ^ 2) * (A * P) := by ring
    have h3 : (1 + k ^ 2) * (A * P) ≤ 2 * (A * P) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hAnn hPnn)
    linarith [h1, h2, h3]
  have hnorm : ‖Work.MRMT.dz (G ∘ H) w‖ ≤ 2 * (A * P) := le_trans hstep1 hstep2
  have hsq : ‖Work.MRMT.dz (G ∘ H) w‖ ^ 2 ≤ 4 * A ^ 2 * P ^ 2 := by
    calc ‖Work.MRMT.dz (G ∘ H) w‖ ^ 2 ≤ (2 * (A * P)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = 4 * A ^ 2 * P ^ 2 := by ring
  have hdet_ge : (1 - k ^ 2) * P ^ 2 ≤ det := by
    rw [hdet_eq]
    have hQ2 : Q ^ 2 ≤ k ^ 2 * P ^ 2 := by
      calc Q ^ 2 ≤ (k * P) ^ 2 := pow_le_pow_left₀ hQnn hdilH 2
        _ = k ^ 2 * P ^ 2 := by ring
    nlinarith
  have hdet_nonneg : 0 ≤ det := le_trans (mul_nonneg hk2pos.le (sq_nonneg P)) hdet_ge
  have hP2 : P ^ 2 ≤ det / (1 - k ^ 2) := by
    rw [le_div_iff₀ hk2pos]; linarith
  have hfinal : ‖Work.MRMT.dz (G ∘ H) w‖ ^ 2 ≤ (4 / (1 - k ^ 2)) * A ^ 2 * det := by
    have h1 : 4 * A ^ 2 * P ^ 2 ≤ 4 * A ^ 2 * (det / (1 - k ^ 2)) :=
      mul_le_mul_of_nonneg_left hP2 (by positivity)
    have h2 : 4 * A ^ 2 * (det / (1 - k ^ 2)) = (4 / (1 - k ^ 2)) * A ^ 2 * det := by ring
    linarith [hsq, h1, h2]
  have hfinal' : ‖Work.MRMT.dz ((star ∘ (F : ℂ → ℂ) ∘ f) ∘ (F.symm : ℂ → ℂ)) w‖ ^ 2 ≤
      (4 / (1 - k ^ 2)) * ‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2 *
        (fderiv ℝ (F.symm : ℂ → ℂ) w).det := by
    simpa only [hGdef, hHdef, hAdef, hdetdef] using hfinal
  have hdetnn' : 0 ≤ (fderiv ℝ (F.symm : ℂ → ℂ) w).det := by
    simpa only [hHdef, hdetdef] using hdet_nonneg
  have hA2nn : (0:ℝ) ≤ ‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2 :=
    sq_nonneg _
  have hfour : (0:ℝ) ≤ 4 / (1 - k ^ 2) := by positivity
  calc ENNReal.ofReal (‖Work.MRMT.dz ((star ∘ (F : ℂ → ℂ) ∘ f) ∘ (F.symm : ℂ → ℂ)) w‖ ^ 2)
      ≤ ENNReal.ofReal ((4 / (1 - k ^ 2)) *
          ‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2 *
            (fderiv ℝ (F.symm : ℂ → ℂ) w).det) := ENNReal.ofReal_le_ofReal hfinal'
    _ = ENNReal.ofReal (4 / (1 - k ^ 2)) *
          (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
            ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|) := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤
          4 / (1 - k ^ 2) * ‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2)]
        rw [ENNReal.ofReal_mul hfour, abs_of_nonneg hdetnn']
        ring

theorem lintegral_normSq_dz_conj_comp_le {F : ℂ ≃ₜ ℂ} {μF f : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hbelt : ∀ z : ℂ, Work.MRMT.dzbar (F : ℂ → ℂ) z = μF z * Work.MRMT.dz (F : ℂ → ℂ) z)
    (hμ : ∀ z : ℂ, ‖μF z‖ ≤ k) (hf : Differentiable ℂ (star ∘ f)) {L : Set ℂ} (hL : IsCompact L) :
    ∫⁻ w in L, ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)) w‖ ^ 2)
      ≤ ENNReal.ofReal (4 / (1 - k ^ 2)) *
        ∫⁻ z in (F.symm : ℂ → ℂ) '' L, ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) z‖ ^ 2) := by
  have hmeas : MeasurableSet L := hL.measurableSet
  have hpt : ∀ w : ℂ,
      ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)) w‖ ^ 2) ≤
        ENNReal.ofReal (4 / (1 - k ^ 2)) *
          (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
            ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|) :=
    fun w => pointwise_le hk0 hk1 hF hFs hbelt hμ hf w
  have hstep : ∫⁻ w in L, ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)) w‖ ^ 2)
      ≤ ∫⁻ w in L, ENNReal.ofReal (4 / (1 - k ^ 2)) *
          (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
            ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|) :=
    setLIntegral_mono_ae' hmeas (Eventually.of_forall fun w _ => hpt w)
  have hconst : ∫⁻ w in L, ENNReal.ofReal (4 / (1 - k ^ 2)) *
        (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
          ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|)
      = ENNReal.ofReal (4 / (1 - k ^ 2)) *
        ∫⁻ w in L, (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
          ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hderiv : ∀ x ∈ L, HasFDerivWithinAt (F.symm : ℂ → ℂ) (fderiv ℝ (F.symm : ℂ → ℂ) x) L x :=
    fun x _ => (hFs.contDiffAt (x := x)).differentiableAt (by norm_num) |>.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn (F.symm : ℂ → ℂ) L := (F.symm.injective).injOn
  have hcv := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure ℂ))
    (f := (F.symm : ℂ → ℂ)) (f' := fun w => fderiv ℝ (F.symm : ℂ → ℂ) w) (s := L)
    hmeas hderiv hinj (fun z => ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) z‖ ^ 2))
  have hcv' : ∫⁻ w in L, (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
        ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|)
      = ∫⁻ z in (F.symm : ℂ → ℂ) '' L, ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) z‖ ^ 2) := by
    rw [hcv]
    exact setLIntegral_congr_fun hmeas (fun w _ => mul_comm _ _)
  calc ∫⁻ w in L, ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)) w‖ ^ 2)
      ≤ ∫⁻ w in L, ENNReal.ofReal (4 / (1 - k ^ 2)) *
          (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
            ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|) := hstep
    _ = ENNReal.ofReal (4 / (1 - k ^ 2)) *
        ∫⁻ w in L, (ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)‖ ^ 2) *
          ENNReal.ofReal |(fderiv ℝ (F.symm : ℂ → ℂ) w).det|) := hconst
    _ = ENNReal.ofReal (4 / (1 - k ^ 2)) *
        ∫⁻ z in (F.symm : ℂ → ℂ) '' L, ENNReal.ofReal (‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) z‖ ^ 2) := by
        rw [hcv']

end Work.MRMT.Found
