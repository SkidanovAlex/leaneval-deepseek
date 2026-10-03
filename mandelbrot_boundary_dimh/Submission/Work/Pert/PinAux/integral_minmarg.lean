import Mathlib
import Submission.Work.Pert.PinAux.CollarDefs

namespace Work.Pert.PinAux

open MandelDim Complex Metric

noncomputable section

/-- Antiderivative formula: `∫ x in p..q, 1/(x + c) = log ((q + c)/(p + c))`, valid whenever
both `p + c` and `q + c` are positive. -/
lemma integral_one_div_add (p q c : ℝ) (hp : 0 < p + c) (hq : 0 < q + c) :
    (∫ x in p..q, 1 / (x + c)) = Real.log ((q + c) / (p + c)) := by
  rw [intervalIntegral.integral_comp_add_right (fun y : ℝ => 1 / y) c]
  exact integral_one_div_of_pos hp hq

theorem integral_minmarg {Ξ : ℝ} {α : ℂ} {z : ℂ} (hpos : 0 < Work.Pert.PinAux.minmarg Ξ α z) :
    (∫ x in (min z.re (Work.Pert.PinAux.med Ξ α z.im).re)..(max z.re (Work.Pert.PinAux.med Ξ α z.im).re),
        1 / Work.Pert.PinAux.minmarg Ξ α (x + z.im * Complex.I))
      = Real.log (Work.Pert.PinAux.minmarg Ξ α (Work.Pert.PinAux.med Ξ α z.im)
          / Work.Pert.PinAux.minmarg Ξ α z) := by
  -- `med Ξ α z.im` has height `z.im` and real part `(med Ξ α z.im).re`.
  have hpt : (((med Ξ α z.im).re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I = med Ξ α z.im := by
    have h := Complex.re_add_im (med Ξ α z.im)
    rw [med_im Ξ α z.im] at h
    exact h
  rcases le_total z.re (med Ξ α z.im).re with h | h
  · -- Case `z.re ≤ (med Ξ α z.im).re`: the min margin grows with slope `+1`.
    rw [min_eq_left h, max_eq_right h]
    have hmM : minmarg Ξ α (med Ξ α z.im)
        = minmarg Ξ α z + ((med Ξ α z.im).re - z.re) := by
      have haff := minmarg_affine_le (Ξ := Ξ) (α := α) (z := z)
        (x := (med Ξ α z.im).re) h ⟨h, le_refl _⟩
      rwa [hpt] at haff
    have hMpos : 0 < minmarg Ξ α (med Ξ α z.im) := by
      rw [hmM]; linarith [sub_nonneg.mpr h]
    have hcongr : (∫ x in z.re..(med Ξ α z.im).re, 1 / minmarg Ξ α (x + z.im * Complex.I))
        = ∫ x in z.re..(med Ξ α z.im).re, 1 / (x + (minmarg Ξ α z - z.re)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h] at hx
      have haff := minmarg_affine_le (Ξ := Ξ) (α := α) (z := z) (x := x) h hx
      change 1 / minmarg Ξ α (x + z.im * Complex.I)
        = 1 / (x + (minmarg Ξ α z - z.re))
      rw [haff]; ring
    have hshift : (∫ x in z.re..(med Ξ α z.im).re, 1 / (x + (minmarg Ξ α z - z.re)))
        = ∫ x in z.re + (minmarg Ξ α z - z.re)..(med Ξ α z.im).re + (minmarg Ξ α z - z.re),
            1 / x :=
      intervalIntegral.integral_comp_add_right (a := z.re) (b := (med Ξ α z.im).re)
        (fun y : ℝ => 1 / y) (minmarg Ξ α z - z.re)
    have h1 : z.re + (minmarg Ξ α z - z.re) = minmarg Ξ α z := by ring
    have h2 : (med Ξ α z.im).re + (minmarg Ξ α z - z.re)
        = minmarg Ξ α (med Ξ α z.im) := by rw [hmM]; ring
    rw [hcongr, hshift, h1, h2, integral_one_div_of_pos hpos hMpos]
  · -- Case `(med Ξ α z.im).re ≤ z.re`: the min margin grows with slope `-1`.
    rw [min_eq_right h, max_eq_left h]
    have hmM : minmarg Ξ α (med Ξ α z.im)
        = minmarg Ξ α z + (z.re - (med Ξ α z.im).re) := by
      have haff := minmarg_affine_ge (Ξ := Ξ) (α := α) (z := z)
        (x := (med Ξ α z.im).re) h ⟨le_refl _, h⟩
      rwa [hpt] at haff
    have hMpos : 0 < minmarg Ξ α (med Ξ α z.im) := by
      rw [hmM]; linarith [sub_nonneg.mpr h]
    have hcongr : (∫ x in (med Ξ α z.im).re..z.re, 1 / minmarg Ξ α (x + z.im * Complex.I))
        = ∫ x in (med Ξ α z.im).re..z.re,
            1 / ((-x) + (minmarg Ξ α z + z.re)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h] at hx
      have haff := minmarg_affine_ge (Ξ := Ξ) (α := α) (z := z) (x := x) h hx
      change 1 / minmarg Ξ α (x + z.im * Complex.I)
        = 1 / ((-x) + (minmarg Ξ α z + z.re))
      rw [haff]; ring
    have hneg : (∫ x in (med Ξ α z.im).re..z.re, 1 / ((-x) + (minmarg Ξ α z + z.re)))
        = ∫ x in -z.re..(-(med Ξ α z.im).re),
            1 / (x + (minmarg Ξ α z + z.re)) :=
      intervalIntegral.integral_comp_neg (a := (med Ξ α z.im).re) (b := z.re)
        (fun y : ℝ => 1 / (y + (minmarg Ξ α z + z.re)))
    have hnum : (-(med Ξ α z.im).re) + (minmarg Ξ α z + z.re)
        = minmarg Ξ α (med Ξ α z.im) := by rw [hmM]; ring
    have hden : (-z.re) + (minmarg Ξ α z + z.re) = minmarg Ξ α z := by ring
    have hpk : 0 < (-z.re) + (minmarg Ξ α z + z.re) := by rw [hden]; exact hpos
    have hqk : 0 < (-(med Ξ α z.im).re) + (minmarg Ξ α z + z.re) := by
      rw [hnum]; exact hMpos
    rw [hcongr, hneg,
      integral_one_div_add (-z.re) (-(med Ξ α z.im).re) (minmarg Ξ α z + z.re) hpk hqk,
      hnum, hden]

end

end Work.Pert.PinAux
