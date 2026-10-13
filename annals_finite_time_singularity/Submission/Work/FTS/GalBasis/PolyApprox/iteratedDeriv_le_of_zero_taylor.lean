import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.PolyApprox

/-- One mean-value step: if `g` has right/within derivative `G` on `[a,b]`, `G` is bounded by
the constant `C` there, and `g a = 0`, then `‖g x‖ ≤ B` on `[a,b]` as soon as
`C * (b - a) ≤ B` (and `C ≥ 0`). -/
private lemma mvt_step {g G : ℝ → ℝ} {a b C B : ℝ} (hC0 : 0 ≤ C)
    (hg : ∀ x ∈ Set.Icc a b, HasDerivWithinAt g (G x) (Set.Icc a b) x)
    (hbound : ∀ x ∈ Set.Icc a b, ‖G x‖ ≤ C)
    (hga : g a = 0) (hCB : C * (b - a) ≤ B) :
    ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ B := by
  intro x hx
  have h1 : ‖g x - g a‖ ≤ C * (x - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hg
      (fun y hy => hbound y (Set.Ico_subset_Icc_self hy)) x hx
  rw [hga, sub_zero] at h1
  have hxa : x - a ≤ b - a := by linarith [hx.1, hx.2]
  exact h1.trans ((mul_le_mul_of_nonneg_left hxa hC0).trans hCB)

/-- On an open interval where `h` is `C^4`, each iterated derivative `iteratedDeriv i h`
(with `i < 4`) is differentiable. -/
private lemma differentiableOn_iteratedDeriv_open {c d : ℝ} {h : ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 h (Set.Ioo c d)) {i : ℕ} (hi : i < 4) :
    DifferentiableOn ℝ (iteratedDeriv i h) (Set.Ioo c d) := by
  have hilt : ((i : ℕ) : WithTop ℕ∞) < (4 : WithTop ℕ∞) := by exact_mod_cast hi
  have hd : DifferentiableOn ℝ (iteratedDerivWithin i h (Set.Ioo c d)) (Set.Ioo c d) :=
    hC.differentiableOn_iteratedDerivWithin hilt isOpen_Ioo.uniqueDiffOn
  exact hd.congr (fun y hy => (iteratedDerivWithin_of_isOpen isOpen_Ioo hy).symm)

/-- The within-derivative of the `i`-th iterated derivative is the `(i+1)`-th iterated
derivative, on `[a,b]`, for `h` of class `C^4` on a neighbourhood. -/
private lemma hasDerivWithinAt_iteratedDeriv {c d a b : ℝ} {h : ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 h (Set.Ioo c d)) (hsub : Set.Icc a b ⊆ Set.Ioo c d)
    {i : ℕ} (hi : i ≤ 3) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    HasDerivWithinAt (iteratedDeriv i h) (iteratedDeriv (i+1) h x) (Set.Icc a b) x := by
  have hxO : x ∈ Set.Ioo c d := hsub hx
  have hd : DifferentiableAt ℝ (iteratedDeriv i h) x :=
    (differentiableOn_iteratedDeriv_open hC (by omega)).differentiableAt (isOpen_Ioo.mem_nhds hxO)
  have h1 : HasDerivAt (iteratedDeriv i h) (deriv (iteratedDeriv i h) x) x := hd.hasDerivAt
  simpa only [iteratedDeriv_succ] using h1.hasDerivWithinAt

/-- If `h` is `C^4` on a neighbourhood of `[a,b]`, its fourth derivative is bounded by `M ≥ 0`
on `[a,b]`, and `h` together with its first three derivatives vanishes at `a`, then on `[a,b]`
each iterated derivative `iteratedDeriv i h`, `i ≤ 4`, is bounded by `M * (b - a) ^ (4 - i)`.

This is the un-sharpened Taylor bound: it is obtained by four successive applications of the
mean value theorem, each time using the previous (already proved) bound as the Lipschitz
constant. -/
theorem iteratedDeriv_le_of_zero_taylor {c d a b M : ℝ} (hab : a ≤ b) {h : ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 h (Set.Ioo c d)) (hsub : Set.Icc a b ⊆ Set.Ioo c d)
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 h y| ≤ M)
    (h0 : ∀ m < 4, iteratedDeriv m h a = 0) :
    ∀ i : ℕ, i ≤ 4 → ∀ x ∈ Set.Icc a b, |iteratedDeriv i h x| ≤ M * (b - a) ^ (4 - i) := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have H3 : ∀ x ∈ Set.Icc a b, |iteratedDeriv 3 h x| ≤ M * (b - a) := by
    refine mvt_step (g := iteratedDeriv 3 h) (G := iteratedDeriv 4 h) (C := M) (B := M * (b - a))
      hM0 (fun x hx => hasDerivWithinAt_iteratedDeriv hC hsub (by norm_num) hx)
      (fun x hx => hM x hx) (h0 3 (by norm_num)) (le_refl _)
  have H2 : ∀ x ∈ Set.Icc a b, |iteratedDeriv 2 h x| ≤ M * (b - a) ^ 2 := by
    refine mvt_step (g := iteratedDeriv 2 h) (G := iteratedDeriv 3 h) (C := M * (b - a))
      (B := M * (b - a) ^ 2) (mul_nonneg hM0 hba)
      (fun x hx => hasDerivWithinAt_iteratedDeriv hC hsub (by norm_num) hx)
      (fun x hx => H3 x hx) (h0 2 (by norm_num)) (le_of_eq (by ring))
  have H1 : ∀ x ∈ Set.Icc a b, |iteratedDeriv 1 h x| ≤ M * (b - a) ^ 3 := by
    refine mvt_step (g := iteratedDeriv 1 h) (G := iteratedDeriv 2 h) (C := M * (b - a) ^ 2)
      (B := M * (b - a) ^ 3) (mul_nonneg hM0 (pow_nonneg hba 2))
      (fun x hx => hasDerivWithinAt_iteratedDeriv hC hsub (by norm_num) hx)
      (fun x hx => H2 x hx) (h0 1 (by norm_num)) (le_of_eq (by ring))
  have H0 : ∀ x ∈ Set.Icc a b, |iteratedDeriv 0 h x| ≤ M * (b - a) ^ 4 := by
    refine mvt_step (g := iteratedDeriv 0 h) (G := iteratedDeriv 1 h) (C := M * (b - a) ^ 3)
      (B := M * (b - a) ^ 4) (mul_nonneg hM0 (pow_nonneg hba 3))
      (fun x hx => hasDerivWithinAt_iteratedDeriv hC hsub (by norm_num) hx)
      (fun x hx => H1 x hx) (h0 0 (by norm_num)) (le_of_eq (by ring))
  intro i hi x hx
  interval_cases i
  · simpa using H0 x hx
  · simpa using H1 x hx
  · simpa using H2 x hx
  · simpa using H3 x hx
  · simpa using hM x hx

end Work.FTS.GalBasis.PolyApprox
