import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.dev_horiz_le
import Submission.Work.Pert.V5.horiz_dev_le_of_margin
import Submission.Work.Pert.V5.deriv_sub_one_le_of_margin
import Submission.Work.Pert.V5.integral_marg_affine

set_option linter.unusedVariables false

/-!
# `Work.Pert.V5.corridor_dev_affine`

The **horizontal corridor** transport of the deviation `D w = Φm w - w` of a Fatou coordinate
`Φm` of the near-translation `F = liftF u σ α` on the gate `Qm Ξ α`, in the *logarithmic* form
adapted to the affine marginals of the gate.

Both marginals of the gate, restricted to the horizontal line at height `y`, are affine in the
abscissa:

* `mgA Ξ α (ξ + i y) = ξ + KA` (slope `+1`), `KA = -Ξ + Re (1/α) + |y + Im (1/α)|`;
* `mgB Ξ (ξ + i y) = KB - ξ` (slope `-1`), `KB = |y| - Ξ`.

Hence on the segment `[x, x₀]` the local margin `κ(ξ) = min (mgA) (mgB)` is positive as soon as
`mgA > 0` at the left end and `mgB > 0` at the right end, and Shishikura's derivative estimate
`‖Φ' - 1/v‖ ≤ C₂/R` at `R = κ/√2`, together with `‖1/v - 1‖ ≤ 1/31`, gives the pointwise bound

  `‖Φm' - 1‖ ≤ C₂ √2 (1/mgA + 1/mgB) + 1/31`,

which integrates along the corridor to exactly

  `C₂ √2 (log (mgA(x₀)/mgA(x)) + log (mgB(x)/mgB(x₀))) + (x₀ - x)/31`.

The two ingredients are the delegated lemmas `Work.Pert.V5.deriv_sub_one_le_of_margin` (the
pointwise derivative bound from a local margin) and `Work.Pert.V5.integral_marg_affine` (the
fundamental-theorem-of-calculus evaluation of the majorant), assembled here with
`Work.Pert.V5.dev_horiz_le`.
-/

namespace Work.Pert.V5

open Set Metric

theorem corridor_dev_affine {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {x x₀ y : ℝ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hxx : x ≤ x₀)
    (hseg : ∀ ξ ∈ Set.Icc x x₀, ((ξ : ℂ) + (y : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α)
    (hA : Real.sqrt 2 * Rde ≤ Work.Pert.V5.mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I))
    (hB : Real.sqrt 2 * Rde ≤ Work.Pert.V5.mgB Ξ ((x₀ : ℂ) + (y : ℂ) * Complex.I)) :
    ‖(Φm ((x₀ : ℂ) + (y : ℂ) * Complex.I) - ((x₀ : ℂ) + (y : ℂ) * Complex.I))
        - (Φm ((x : ℂ) + (y : ℂ) * Complex.I) - ((x : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ C₂ * Real.sqrt 2 *
          (Real.log (Work.Pert.V5.mgA Ξ α ((x₀ : ℂ) + (y : ℂ) * Complex.I)
                     / Work.Pert.V5.mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I))
         + Real.log (Work.Pert.V5.mgB Ξ ((x : ℂ) + (y : ℂ) * Complex.I)
                     / Work.Pert.V5.mgB Ξ ((x₀ : ℂ) + (y : ℂ) * Complex.I)))
        + (x₀ - x) / 31 := by
  have hsqrt2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpos2 : 0 < Real.sqrt 2 * Rde := mul_pos hsqrt2pos hRde
  -- ## the margin on the whole segment
  have hmarg : ∀ ξ ∈ Set.Icc x x₀,
      Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
                              (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) := by
    intro ξ hξ
    have hmm : Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
        = (ξ - x) + Work.Pert.V5.mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I) := by
      rw [Work.Pert.V5.mgA_re_im Ξ α ξ y, Work.Pert.V5.mgA_re_im Ξ α x y]; ring
    have hnn : Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)
        = (x₀ - ξ) + Work.Pert.V5.mgB Ξ ((x₀ : ℂ) + (y : ℂ) * Complex.I) := by
      rw [Work.Pert.V5.mgB_re_im Ξ ξ y, Work.Pert.V5.mgB_re_im Ξ x₀ y]; ring
    refine le_min ?_ ?_
    · rw [hmm]; linarith [hξ.1]
    · rw [hnn]; linarith [hξ.2]
  have hminpos : ∀ ξ ∈ Set.Icc x x₀,
      0 < min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
              (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) :=
    fun ξ hξ => lt_of_lt_of_le hpos2 (hmarg ξ hξ)
  have hmgApos : ∀ ξ ∈ Set.Icc x x₀, 0 < Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I) :=
    fun ξ hξ => lt_of_lt_of_le (hminpos ξ hξ) (min_le_left _ _)
  have hmgBpos : ∀ ξ ∈ Set.Icc x x₀, 0 < Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I) :=
    fun ξ hξ => lt_of_lt_of_le (hminpos ξ hξ) (min_le_right _ _)
  -- ## the pointwise derivative bound
  have hderiv : ∀ ξ ∈ Set.Icc x x₀,
      ‖deriv Φm ((ξ : ℂ) + (y : ℂ) * Complex.I) - 1‖
        ≤ C₂ * Real.sqrt 2 * (1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
            + 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) + 1 / 31 := by
    intro ξ hξ
    set κ : ℝ := min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
        (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) with hκdef
    have hκ : 0 < κ := hminpos ξ hξ
    have hκRde : Rde ≤ κ / Real.sqrt 2 := by
      have h := div_le_div_of_nonneg_right (hmarg ξ hξ) (le_of_lt hsqrt2pos)
      rwa [mul_div_cancel_left₀ Rde (ne_of_gt hsqrt2pos)] at h
    have hmargin' : κ ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
        (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) := le_of_eq hκdef
    -- Shishikura's derivative estimate, applied on the ball of radius `κ/√2`
    have h1 : ‖deriv Φm ((ξ : ℂ) + (y : ℂ) * Complex.I) - 1‖
        ≤ C₂ * Real.sqrt 2 / κ + 1 / 31 :=
      deriv_sub_one_le_of_margin (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
        (α := α) (σ := σ) (u := u) (Φm := Φm)
        (w := ((ξ : ℂ) + (y : ℂ) * Complex.I)) (κ := κ)
        hRde hC₂ hDE hNT hΦm (hseg ξ hξ) hκ hκRde hmargin'
    -- `1/κ ≤ 1/mgA + 1/mgB`
    have hinv : 1 / κ ≤ 1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
        + 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I) := by
      have h1a : (0 : ℝ) ≤ 1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I) :=
        le_of_lt (one_div_pos.mpr (hmgApos ξ hξ))
      have h1b : (0 : ℝ) ≤ 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I) :=
        le_of_lt (one_div_pos.mpr (hmgBpos ξ hξ))
      rcases min_cases (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
        (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [← h]; linarith
      · rw [← h]; linarith
    have h2 : C₂ * Real.sqrt 2 / κ
        ≤ C₂ * Real.sqrt 2 * (1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
            + 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) := by
      have hC : (0 : ℝ) ≤ C₂ * Real.sqrt 2 := le_of_lt (mul_pos hC₂ hsqrt2pos)
      have h3 : C₂ * Real.sqrt 2 / κ = C₂ * Real.sqrt 2 * (1 / κ) := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hinv hC
    linarith [h1, h2]
  -- ## continuity of the majorant on the corridor
  have hcontA : Continuous (fun ξ : ℝ => Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)) := by
    have he : (fun ξ : ℝ => Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
        = fun ξ : ℝ => (ξ - Ξ + (1 / α).re) + |y + (1 / α).im| := by
      funext ξ; rw [Work.Pert.V5.mgA_re_im]
    rw [he]; fun_prop
  have hcontB : Continuous (fun ξ : ℝ => Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) := by
    have he : (fun ξ : ℝ => Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))
        = fun ξ : ℝ => |y| - Ξ - ξ := by
      funext ξ; rw [Work.Pert.V5.mgB_re_im]
    rw [he]; fun_prop
  have hg1 : ContinuousOn (fun ξ : ℝ => 1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc x x₀) :=
    ContinuousOn.div continuousOn_const hcontA.continuousOn (fun ξ hξ => ne_of_gt (hmgApos ξ hξ))
  have hg2 : ContinuousOn (fun ξ : ℝ => 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc x x₀) :=
    ContinuousOn.div continuousOn_const hcontB.continuousOn (fun ξ hξ => ne_of_gt (hmgBpos ξ hξ))
  have hgcont : ContinuousOn (fun ξ : ℝ => C₂ * Real.sqrt 2 *
      (1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
        + 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) + 1 / 31)
      (Set.Icc x x₀) := by
    have h3 : ContinuousOn (fun ξ : ℝ => C₂ * Real.sqrt 2 *
        (1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
          + 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))) (Set.Icc x x₀) :=
      continuousOn_const.mul (hg1.add hg2)
    exact h3.add continuousOn_const
  -- ## integrate along the corridor
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  have hdev := Work.Pert.V5.dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (s := y)
    (a := x) (b := x₀)
    (g := fun ξ : ℝ => C₂ * Real.sqrt 2 *
      (1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
        + 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) + 1 / 31)
    hQopen hxx hseg hΦm.1 hderiv hgcont
  have hint := integral_marg_affine (Ξ := Ξ) (C₂ := C₂) (α := α) (x := x) (x₀ := x₀) (y := y)
    hxx (lt_of_lt_of_le hpos2 hA) (lt_of_lt_of_le hpos2 hB)
  rw [hint] at hdev
  exact hdev

end Work.Pert.V5
