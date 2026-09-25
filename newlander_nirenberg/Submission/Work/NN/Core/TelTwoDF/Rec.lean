/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The structural lemmas of the parameterised `(0,2)`-recursion

This file adapts the lemmas of `Submission/Work/NN/Final/twoRec.lean` (stated there for the fixed
cutoff `openCut` and the fixed radii `cutIn`, `cutOut`, `trRho`) to the parametric cutoffs
`kappa G s`, `kappabar G s` and the transform radius `G.r s` of
`Submission/Work/NN/Core/TelTwoDF/Defs.lean`.
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-- The natural numbers are below `C^∞` in the `ℕ∞ω` indexing of `ContDiff`. -/
lemma le_infty'' (m : ℕ) : (m : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by exact_mod_cast le_top

/-! ## Smoothness of the transform of a cutoff product -/

/-- `TL G s` maps `C¹` data which vanish for `G.b s ≤ ‖y s‖` to `C¹` functions. -/
lemma contDiff_TL (G : Geom n) {s : Fin n} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ y, G.b s ≤ ‖y s‖ → g y = 0) : ContDiff ℝ 1 (TL G s g) := by
  rw [TL_eq G s hg.continuous]
  refine Work.CR.Flat.Cauchy.contDiff_dbarTransform (b := G.b s) ?_ s 1 hg hsupp
  have h1 := G.hbr s
  have h2 := G.hr s
  linarith

/-! ## The `∂̄`-derivative of the cutoffs -/

/-- The `∂̄`-derivative of the cutoff `kappa G s` in its own coordinate is `kappabar G s`. -/
lemma dbarCoord_kappa (G : Geom n) (s : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord s (kappa G s) z = kappabar G s z := by
  have hfun : (fun w : ℂ => kappa G s (Function.update z s w))
      = Work.NN.Core.sharpCut (G.a s) (G.b s) := by
    funext w; simp [kappa]
  have hdiff : DifferentiableAt ℝ (kappa G s) (Function.update z s (z s)) := by
    rw [Function.update_eq_self]
    exact (contDiff_kappa G s).contDiffAt.differentiableAt (by simp)
  have h := Work.CR.Flat.Cauchy.dbarSolution_dbarC_update_eq_dbarCoord s
    (g := kappa G s) (z := z) (u := z s) hdiff
  rw [Function.update_eq_self, hfun] at h
  exact h.symm

/-- A function of the `s`-th coordinate alone has vanishing `∂̄_l`-derivative for `l ≠ s`. -/
lemma dbarCoord_single {s l : Fin n} (h : l ≠ s) {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (z : Fin n → ℂ) : Work.CR.Flat.dbarCoord l (fun y => u (y s)) z = 0 := by
  have hfun : (fun w : ℂ => (fun y : Fin n → ℂ => u (y s)) (Function.update z l w))
      = fun _ => u (z s) := by
    funext w
    show u ((Function.update z l w) s) = u (z s)
    rw [Function.update_apply, if_neg (fun hsl => h hsl.symm)]
  have hdiff : DifferentiableAt ℝ (fun y : Fin n → ℂ => u (y s)) (Function.update z l (z l)) := by
    rw [Function.update_eq_self]
    exact (hu.comp (contDiff_apply ℝ ℂ s)).contDiffAt.differentiableAt (by simp)
  have h2 := Work.CR.Flat.Cauchy.dbarSolution_dbarC_update_eq_dbarCoord l
    (g := fun y : Fin n → ℂ => u (y s)) (z := z) (u := z l) hdiff
  rw [Function.update_eq_self, hfun] at h2
  rw [← h2]
  simp [Work.CR.Flat.dbarC]

lemma dbarCoord_kappa_eq_zero (G : Geom n) {s l : Fin n} (h : l ≠ s) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord l (kappa G s) z = 0 := by
  show Work.CR.Flat.dbarCoord l (fun y => Work.NN.Core.sharpCut (G.a s) (G.b s) (y s)) z = 0
  exact dbarCoord_single h (Work.NN.Core.contDiff_sharpCut (a := G.a s) (b := G.b s)) z

/-- Product rule for the cutoff, in a coordinate different from its own. -/
lemma dbarCoord_kappa_mul (G : Geom n) {s l : Fin n} (h : l ≠ s) {D : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hD : DifferentiableAt ℝ D z) :
    Work.CR.Flat.dbarCoord l (fun y => kappa G s y * D y) z
      = kappa G s z * Work.CR.Flat.dbarCoord l D z := by
  have hχ : DifferentiableAt ℝ (kappa G s) z :=
    (contDiff_kappa G s).contDiffAt.differentiableAt (by simp)
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul l _ _ z hχ hD, dbarCoord_kappa_eq_zero G h z]
  ring

/-- Product rule for the cutoff, in its own coordinate. -/
lemma dbarCoord_kappa_mul_self (G : Geom n) {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hD : DifferentiableAt ℝ D z) :
    Work.CR.Flat.dbarCoord s (fun y => kappa G s y * D y) z
      = kappabar G s z * D z + kappa G s z * Work.CR.Flat.dbarCoord s D z := by
  have hχ : DifferentiableAt ℝ (kappa G s) z :=
    (contDiff_kappa G s).contDiffAt.differentiableAt (by simp)
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul s _ _ z hχ hD, dbarCoord_kappa G s z]


lemma dbarCoord_kappabar_eq_zero (G : Geom n) {s l : Fin n} (h : l ≠ s) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord l (kappabar G s) z = 0 := by
  show Work.CR.Flat.dbarCoord l
    (fun y => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut (G.a s) (G.b s)) (y s)) z = 0
  exact dbarCoord_single h (contDiff_dbarC_sharpCut_aux (a := G.a s) (b := G.b s)) z

/-- Product rule for `kappabar`, in a coordinate different from its own. -/
lemma dbarCoord_kappabar_mul (G : Geom n) {s l : Fin n} (h : l ≠ s) {D : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hD : DifferentiableAt ℝ D z) :
    Work.CR.Flat.dbarCoord l (fun y => kappabar G s y * D y) z
      = kappabar G s z * Work.CR.Flat.dbarCoord l D z := by
  have hχ : DifferentiableAt ℝ (kappabar G s) z :=
    (contDiff_kappabar G s).contDiffAt.differentiableAt (by simp)
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul l _ _ z hχ hD, dbarCoord_kappabar_eq_zero G h z]
  ring

/-- `∂̄` of a constant is `0`. -/
lemma dbarCoord_const' (a : Fin n) (c : ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord a (fun _ : Fin n → ℂ => c) z = 0 := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp a (fun _ : Fin n → ℂ => c),
    show (fun _ : Fin n → ℂ => c) = Function.const (Fin n → ℂ) c from rfl, fderiv_const]
  simp

/-- `∂̄` is subtractive, at differentiability points. -/
lemma dbarCoord_sub' (a : Fin n) {u v : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    Work.CR.Flat.dbarCoord a (u - v) z
      = Work.CR.Flat.dbarCoord a u z - Work.CR.Flat.dbarCoord a v z := by
  have hfd : fderiv ℝ (u - v) z = fderiv ℝ u z - fderiv ℝ v z := fderiv_sub hu hv
  rw [Work.CR.Flat.dbarCoord, hfd, Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord]
  simp only [sub_apply]
  ring

/-- `∂̄` of a `C¹` function is continuous. -/
lemma continuous_dbarCoord {D : (Fin n → ℂ) → ℂ} (hD : ContDiff ℝ 1 D) (a : Fin n) :
    Continuous (Work.CR.Flat.dbarCoord a D) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp a D]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi a).continuous.comp (hD.continuous_fderiv one_ne_zero)

/-! ## The transform of a cutoff product -/

/-- `∂̄` of the transform of `kappabar G s · D`. -/
lemma dbarCoord_TL_kappabar (G : Geom n) {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) {z : Fin n → ℂ} (hzs : ‖z s‖ < G.r s / 2) (a : Fin n) :
    Work.CR.Flat.dbarCoord a (TL G s (fun y => kappabar G s y * D y)) z
      = if a = s then kappabar G s z * D z
        else TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord a D y) z := by
  have hg : ContDiff ℝ 1 (fun y => kappabar G s y * D y) :=
    ((contDiff_kappabar G s).of_le (le_infty'' 1)).mul hD
  have hsupp : ∀ y, G.r s / 2 ≤ ‖y s‖ → kappabar G s y * D y = 0 :=
    fun y hy => by
      rw [kappabar_eq_zero_of_ge G s (le_trans (G.hbr s) hy), zero_mul]
  have hcont : Continuous (fun y => kappabar G s y * Work.CR.Flat.dbarCoord a D y) :=
    (contDiff_kappabar G s).continuous.mul (continuous_dbarCoord hD a)
  rw [TL_eq G s hg.continuous]
  by_cases ha : a = s
  · rw [ha, if_pos rfl]
    rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r s) s s hg z,
      Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (G.hr s) s hg hsupp hzs]
  · rw [if_neg ha, Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r s) s a hg z,
      TL_eq G s hcont]
    congr 1
    funext y
    exact dbarCoord_kappabar_mul G ha ((hD.differentiable one_ne_zero).differentiableAt)

/-- `∂̄` of the transform of `kappa G s · D`, at a point where the cutoff equals `1`. -/
lemma dbarCoord_TL_kappa (G : Geom n) {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) {z : Fin n → ℂ} (hzs : ‖z s‖ < G.a s) (a : Fin n) :
    Work.CR.Flat.dbarCoord a (TL G s (fun y => kappa G s y * D y)) z
      = if a = s then D z
        else TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord a D y) z := by
  have hg : ContDiff ℝ 1 (fun y => kappa G s y * D y) :=
    ((contDiff_kappa G s).of_le (le_infty'' 1)).mul hD
  have hsupp : ∀ y, G.r s / 2 ≤ ‖y s‖ → kappa G s y * D y = 0 :=
    fun y hy => by
      rw [kappa_eq_zero G s (le_trans (G.hbr s) hy), zero_mul]
  have hzs' : ‖z s‖ < G.r s / 2 :=
    lt_of_lt_of_le hzs (le_trans (G.hab s).le (G.hbr s))
  have hcont : Continuous (fun y => kappa G s y * Work.CR.Flat.dbarCoord a D y) :=
    (contDiff_kappa G s).continuous.mul (continuous_dbarCoord hD a)
  rw [TL_eq G s hg.continuous]
  by_cases ha : a = s
  · rw [ha, if_pos rfl]
    rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r s) s s hg z,
      Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (G.hr s) s hg hsupp hzs']
    rw [kappa_eq_one G s (le_of_lt hzs), one_mul]
  · rw [if_neg ha, Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r s) s a hg z,
      TL_eq G s hcont]
    congr 1
    funext y
    exact dbarCoord_kappa_mul G ha ((hD.differentiable one_ne_zero).differentiableAt)

/-! ## The `∂̄`-derivative of one step -/

/-- `∂̄` of `(1 - kappa G s) * D`. -/
lemma dbarCoord_one_sub_kappa_mul (G : Geom n) {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) (a : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord a (fun w => (1 - kappa G s w) * D w) z
      = (1 - kappa G s z) * Work.CR.Flat.dbarCoord a D z
        - (if a = s then kappabar G s z * D z else 0) := by
  have hd1 : DifferentiableAt ℝ (fun w => 1 - kappa G s w) z :=
    (differentiableAt_const _).sub ((contDiff_kappa G s).contDiffAt.differentiableAt (by simp))
  have hdD : DifferentiableAt ℝ D z := (hD.differentiable one_ne_zero).differentiableAt
  have hsub : Work.CR.Flat.dbarCoord a (fun w => 1 - kappa G s w) z
      = if a = s then - kappabar G s z else 0 := by
    have hconst : DifferentiableAt ℝ (fun _ : Fin n → ℂ => (1 : ℂ)) z :=
      differentiableAt_const _
    have hk : DifferentiableAt ℝ (kappa G s) z :=
      (contDiff_kappa G s).contDiffAt.differentiableAt (by simp)
    change Work.CR.Flat.dbarCoord a ((fun _ : Fin n → ℂ => (1 : ℂ)) - kappa G s) z
      = if a = s then - kappabar G s z else 0
    rw [dbarCoord_sub' a hconst hk, dbarCoord_const' a 1 z]
    by_cases h : a = s
    · subst h
      rw [dbarCoord_kappa G a z, if_pos rfl]
      ring
    · rw [dbarCoord_kappa_eq_zero G h z, if_neg h]
      ring
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul a _ _ z hd1 hdD, hsub]
  by_cases h : a = s
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

lemma dbarCoord_uStep (G : Geom n) {s : Fin n}
    {D : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hD : ∀ i l, ContDiff ℝ 1 (D i l))
    {z : Fin n → ℂ} (hzs : ‖z s‖ < G.a s) (a i l : Fin n) :
    Work.CR.Flat.dbarCoord a (uStep G s D i l) z
      = (1 - kappa G s z) * Work.CR.Flat.dbarCoord a (D i l) z
        - (if a = s then kappabar G s z * D i l z else 0)
        + (if i = s ∨ l = s then 0
           else if a = s then kappabar G s z * D i l z
                else TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord a (D i l) y) z) := by
  have hzs' : ‖z s‖ < G.r s / 2 :=
    lt_of_lt_of_le hzs (le_trans (G.hab s).le (G.hbr s))
  have hA := dbarCoord_one_sub_kappa_mul G (s := s) (hD i l) a z
  have hB := dbarCoord_TL_kappabar G (s := s) (D := D i l) (hD i l) hzs' a
  have hsm : ContDiff ℝ 1 (fun y => kappabar G s y * D i l y) :=
    ((contDiff_kappabar G s).of_le (le_infty'' 1)).mul (hD i l)
  have hsupp : ∀ y, G.b s ≤ ‖y s‖ → kappabar G s y * D i l y = 0 :=
    fun y hy => by rw [kappabar_eq_zero_of_ge G s hy, zero_mul]
  by_cases hic : i = s ∨ l = s
  · have hfun : uStep G s D i l = fun w => (1 - kappa G s w) * D i l w := by
      funext w; rw [uStep_apply, if_pos hic]; ring
    rw [hfun, hA, if_pos hic]; ring
  · have hfun : uStep G s D i l = fun w => (1 - kappa G s w) * D i l w
        + TL G s (fun y => kappabar G s y * D i l y) w := by
      funext w; rw [uStep_apply, if_neg hic]
    rw [hfun]
    have hd1 : DifferentiableAt ℝ (fun w => (1 - kappa G s w) * D i l w) z :=
      ((differentiableAt_const _).sub
        ((contDiff_kappa G s).contDiffAt.differentiableAt (by simp))).mul
        ((hD i l).differentiable one_ne_zero).differentiableAt
    have hd2 : DifferentiableAt ℝ (TL G s (fun y => kappabar G s y * D i l y)) z :=
      ((contDiff_TL G hsm hsupp).differentiable one_ne_zero).differentiableAt
    rw [Work.CR.Flat.Polydisc.dbarCoord_add a _ _ z hd1 hd2, hA, hB, if_neg hic]

end Work.NN.Core.TelTwoDF
