import Mathlib
import Submission.Work.RPB.B5.kappaSmallAux

namespace Work.RPB.B5

theorem kshape_far_close (CI : Work.RPV.CurveIsotopy) (δ A M : ℝ) (k : ℤ) (hδ : 0 < δ) (hA : 0 < A)
    (hM : 1 ≤ M)
    (hbound : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖CI.c τ t‖ ≤ M ∧ ‖deriv (fun s : ℝ => CI.c τ s) t‖ ≤ M)
    (hδM : Real.sqrt 2 * δ * M ≤ A / 8) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ t : ℝ,
      DifferentiableAt ℝ (fun s : ℝ => Work.RPB.B5.kfsh CI δ k τ σ s) t ∧
      ‖Work.RPB.B5.kfsh CI δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t‖ ≤ A / 8 ∧
      ‖deriv (fun s : ℝ => Work.RPB.B5.kfsh CI δ k τ σ s) t
        - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t‖ ≤ A / 8 := by
  -- In the small-`δ` regime (`σ ≤ δ`) the far family is the plain rescaled curve
  -- `√(2+2σ) • CI.c τ`, so everything is a one-line comparison with `√2 • CI.c τ`.
  intro τ hτ σ hσ t
  obtain ⟨hσ0, hσδ⟩ := hσ
  have hM0 : 0 ≤ M := by linarith
  -- the `t`-slice of the curve family is `C¹`
  have hslice : ContDiff ℝ 1 (fun s : ℝ => CI.c τ s) := by
    have h0 : ContDiff ℝ 1 (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.of_le (by norm_num)
    simpa [Function.comp_def] using h0.comp ((contDiff_const (c := τ)).prodMk contDiff_id)
  have hdiffAt : DifferentiableAt ℝ (fun s : ℝ => CI.c τ s) t :=
    hslice.contDiffAt.differentiableAt (by norm_num)
  -- the pointwise identification of the far family with the rescaled curve
  have hval : Work.RPB.B5.kfsh CI δ k τ σ t = (Work.RPB.B5.krd σ : ℂ) * CI.c τ t :=
    Work.RPB.B5.kfsh_of_le CI hδ k hσδ
  have hfuneq : (fun s : ℝ => Work.RPB.B5.kfsh CI δ k τ σ s)
      = fun s : ℝ => (Work.RPB.B5.krd σ : ℂ) * CI.c τ s := by
    funext s; exact Work.RPB.B5.kfsh_of_le CI hδ k hσδ
  -- the two derivatives
  have hd1 : deriv (fun s : ℝ => Work.RPB.B5.kfsh CI δ k τ σ s) t
      = (Work.RPB.B5.krd σ : ℂ) * deriv (fun s : ℝ => CI.c τ s) t := by
    rw [hfuneq]; exact deriv_const_mul _ hdiffAt
  have hd0 : deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t
      = (Real.sqrt 2 : ℂ) * deriv (fun s : ℝ => CI.c τ s) t :=
    deriv_const_mul _ hdiffAt
  -- the radius estimate `|krd σ - √2| ≤ √2 σ`
  have habs : |Work.RPB.B5.krd σ - Real.sqrt 2| ≤ Real.sqrt 2 * σ :=
    Work.RPB.B5.abs_krd_sub_sqrt_two_le hσ0
  have hstep : Real.sqrt 2 * σ * M ≤ A / 8 := by
    have hs : Real.sqrt 2 * σ ≤ Real.sqrt 2 * δ :=
      mul_le_mul_of_nonneg_left hσδ (Real.sqrt_nonneg 2)
    have h2 : Real.sqrt 2 * σ * M ≤ Real.sqrt 2 * δ * M :=
      mul_le_mul_of_nonneg_right hs hM0
    linarith [hδM]
  have hbnd : ‖CI.c τ t‖ ≤ M := (hbound τ hτ t).1
  have hdbnd : ‖deriv (fun s : ℝ => CI.c τ s) t‖ ≤ M := (hbound τ hτ t).2
  have hns : ‖(Work.RPB.B5.krd σ : ℂ) - (Real.sqrt 2 : ℂ)‖
      = |Work.RPB.B5.krd σ - Real.sqrt 2| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hmain : |Work.RPB.B5.krd σ - Real.sqrt 2| * ‖CI.c τ t‖ ≤ A / 8 :=
    le_trans (mul_le_mul habs hbnd (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg 2) hσ0)) hstep
  have hmaind : |Work.RPB.B5.krd σ - Real.sqrt 2| * ‖deriv (fun s : ℝ => CI.c τ s) t‖ ≤ A / 8 :=
    le_trans (mul_le_mul habs hdbnd (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg 2) hσ0)) hstep
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun s : ℝ => Work.RPB.B5.kfsh CI δ k τ σ s)
        = (fun s : ℝ => (Work.RPB.B5.krd σ : ℂ) * CI.c τ s) from hfuneq]
    exact hdiffAt.const_mul _
  · rw [hval, ← sub_mul, norm_mul, hns]
    exact hmain
  · rw [hd1, hd0, ← sub_mul, norm_mul, hns]
    exact hmaind

end Work.RPB.B5
