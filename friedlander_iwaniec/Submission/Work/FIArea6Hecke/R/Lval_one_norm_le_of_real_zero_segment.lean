import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea5.S16Hecke.hecke_prod_coeff_nonneg

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- **Mean value inequality along a real segment, for a complex-differentiable function.**
If `F : ℂ → ℂ` is complex differentiable at every real point `t` of the interval `[β,1]`, and
`‖F'(t)‖ ≤ D` there, then `‖F 1 - F β‖ ≤ (1-β)·D`.

The proof restricts `F` to the real axis (`HasDerivAt.comp_ofReal`) and applies the mean value
inequality `Convex.norm_image_sub_le_of_norm_deriv_le` on the convex set `[β,1] ⊂ ℝ`. -/
lemma norm_sub_le_of_norm_deriv_ofReal {F : ℂ → ℂ} {β D : ℝ} (hβ : β ≤ 1)
    (hdiff : ∀ t : ℝ, β ≤ t → t ≤ 1 → DifferentiableAt ℂ F (t : ℂ))
    (hderiv : ∀ t : ℝ, β ≤ t → t ≤ 1 → ‖deriv F (t : ℂ)‖ ≤ D) :
    ‖F 1 - F (β : ℂ)‖ ≤ (1 - β) * D := by
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℝ) (f := fun t : ℝ => F (t : ℂ)) (s := Set.Icc β 1) (x := β) (y := 1) (C := D)
    (fun t ht => ((hdiff t ht.1 ht.2).hasDerivAt.comp_ofReal).differentiableAt)
    (fun t ht => by
      rw [((hdiff t ht.1 ht.2).hasDerivAt.comp_ofReal).deriv]
      exact hderiv t ht.1 ht.2)
    (convex_Icc β 1) ⟨le_rfl, hβ⟩ ⟨hβ, le_rfl⟩
  have hnorm : ‖(1 : ℝ) - β‖ = 1 - β := by
    rw [Real.norm_eq_abs, abs_of_nonneg]; linarith
  rw [hnorm, mul_comm] at hmain
  simpa using hmain

/-- **The mean-value step of the Siegel argument, in the segment form actually used.**
`Lval d 0 Lam` is entire, so along the segment `[β,1] ⊂ ℝ ⊂ ℂ` the mean-value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` gives `‖f 1 - f β‖ ≤ D·(1-β)` whenever
`‖f'‖ ≤ D` on the segment; with `f β = 0` this is `‖f 1‖ ≤ (1-β)·D`.  The caller instantiates `D`
from the sharp derivative bound `R/Lval_deriv_bound_sharp` at the points of `[β,1]`, where
`1 - re s ≤ 1-β`. -/
theorem Lval_one_norm_le_of_real_zero_segment
    {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hχ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hre : ∀ z : GaussianInt, chi z = star (chi z))
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ)
    (hAgr : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ2 : 19 / 20 ≤ β)
    (hz : Work.FIArea6Hecke.Lval d 0 Lam (β : ℂ) = 0)
    {D : ℝ} (hD : 0 ≤ D)
    (hderiv : ∀ t : ℝ, β ≤ t → t ≤ 1 →
      ‖deriv (fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z) (t : ℂ)‖ ≤ D) :
    ‖Work.FIArea6Hecke.Lval d 0 Lam 1‖ ≤ (1 - β) * D := by
  -- `Lval d 0 Lam = Lam / heckeArch d 0` is holomorphic at every real point with `re s > 0`;
  -- the points of `[β,1]` are positive because `0 < β`.
  have hdiffC : ∀ t : ℝ, β ≤ t → t ≤ 1 →
      DifferentiableAt ℂ (fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z) (t : ℂ) := by
    intro t ht0 ht1
    have htpos : 0 < ((t : ℂ)).re := by
      rw [Complex.ofReal_re]; linarith
    unfold Work.FIArea6Hecke.Lval
    exact ((analyticOn_univ.mp hAn) (t : ℂ) (Set.mem_univ _)).differentiableAt.div
      (Work.FIArea6Hecke.R.heckeArch_differentiableAt_of_pos hd 0 htpos)
      (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 htpos)
  have key := norm_sub_le_of_norm_deriv_ofReal (F := fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z)
    (le_of_lt hβ1) hdiffC hderiv
  have hz' : Work.FIArea6Hecke.Lval d 0 Lam ((β : ℝ) : ℂ) = 0 := hz
  calc ‖Work.FIArea6Hecke.Lval d 0 Lam 1‖
      = ‖Work.FIArea6Hecke.Lval d 0 Lam 1 - Work.FIArea6Hecke.Lval d 0 Lam ((β : ℝ) : ℂ)‖ := by
        rw [hz', sub_zero]
    _ ≤ (1 - β) * D := key

end

end Work.FIArea6Hecke.R
