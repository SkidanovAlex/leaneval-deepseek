import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.LinvI_solves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real ContDiff Topology

namespace Work.FTS.PhiStar.LinvFlat

open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-!
# `Linv_contDiffOn_hasDerivAt`

`Linv h θ = -(sin²θ cos³θ)⁻¹ · ∫_0^θ sin²t cos³t h t / sin 2t dt` is the `σ`-normalised
zero-moment Dirichlet inverse of `L₀` (`Work.FTS.PhiStar.Linv`).  This file shows that it
inherits the smoothness of the source and computes its derivative: `Linv h` is `C^n` on
`(0, π/2)` whenever `h` is, and

`(Linv h)'(θ) = -(1/sin 2θ)·(h θ + 2(2cos²θ - 3sin²θ)·Linv h θ)`.

The integrability hypothesis `hint` is exactly what makes the primitive `LinvPrim h` a
genuine (non-junk) integral: `LinvInt h = h·sin θcos²θ/2` identically, so `hint` says that
`LinvInt h` is integrable on `[0, π/2]`, hence on every `[0, θ]` with `θ < π/2`.
-/

/-- The integrand of `Linv`'s primitive, in the regularised form `sin t cos²t h t / 2`. -/
private lemma linvInt_eq_factor (h : ℝ → ℝ) :
    LinvInt h = fun t => (Real.sin t * Real.cos t ^ 2 / 2) * h t := by
  funext t; exact LinvInt_eq h t

/-- The integrand of `Linv`'s primitive, in the form `h t · sinCos2 t / 2`. -/
private lemma linvInt_eq_sinCos2 (h : ℝ → ℝ) :
    LinvInt h = fun t => (h t * Work.Elliptic.sinCos2 t) / 2 := by
  funext t; rw [LinvInt_eq]; simp only [Work.Elliptic.sinCos2]; ring

/-- `LinvInt h` is interval-integrable on `[0, θ]` for `θ ∈ (0, π/2)`: it is a multiple of
`h · sinCos2`, which is integrable on all of `[0, π/2]` by hypothesis. -/
private lemma intervalIntegrable_linvInt {h : ℝ → ℝ}
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    IntervalIntegrable (LinvInt h) volume 0 θ := by
  rw [linvInt_eq_sinCos2, intervalIntegrable_iff, Set.uIoc_of_le (le_of_lt hθ.1)]
  have hsub : Set.Ioc 0 θ ⊆ Work.Spaces.Iθ :=
    fun t ht => ⟨le_of_lt ht.1, le_of_lt (lt_of_le_of_lt ht.2 hθ.2)⟩
  exact (hint.mono_set hsub).div_const 2

/-- `LinvInt h` is continuous at every point of `(0, π/2)`. -/
private lemma continuousAt_linvInt {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (π/2)))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (π/2)) : ContinuousAt (LinvInt h) t := by
  rw [linvInt_eq_factor]
  exact ((by fun_prop : ContinuousAt (fun t : ℝ => Real.sin t * Real.cos t ^ 2 / 2) t)).mul
    (hcont.continuousAt (isOpen_Ioo.mem_nhds ht))

/-- Fundamental theorem of calculus for `LinvPrim`: on `(0, π/2)` its derivative is
`LinvInt h`. -/
private lemma hasDerivAt_LinvPrim_of {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ioo 0 (π/2)))
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    HasDerivAt (LinvPrim h) (LinvInt h θ) θ := by
  have hInt := intervalIntegrable_linvInt hint hθ
  have hcontAt := continuousAt_linvInt hcont hθ
  have hsm : StronglyMeasurableAtFilter (LinvInt h) (𝓝 θ) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun x hx => continuousAt_linvInt hcont hx) θ hθ
  exact intervalIntegral.integral_hasDerivAt_right hInt hsm hcontAt

/-- `LinvInt h` is `C^n` on `(0, π/2)` whenever `h` is. -/
private lemma contDiffOn_linvInt {n : ℕ} {h : ℝ → ℝ}
    (hcd : ContDiffOn ℝ (n : ℕ∞ω) h (Set.Ioo 0 (π/2))) :
    ContDiffOn ℝ (n : ℕ∞ω) (LinvInt h) (Set.Ioo 0 (π/2)) := by
  rw [linvInt_eq_factor]
  exact (by fun_prop : ContDiffOn ℝ (n : ℕ∞ω)
    (fun t : ℝ => Real.sin t * Real.cos t ^ 2 / 2) (Set.Ioo 0 (π/2))).mul hcd

/-- `LinvPrim h = ∫_0^θ LinvInt h` is `C^n` on `(0, π/2)` whenever `h` is: it is actually
`C^(n+1)`, since its derivative is `LinvInt h`, which is `C^n`. -/
private lemma contDiffOn_LinvPrim {n : ℕ} {h : ℝ → ℝ}
    (hcd : ContDiffOn ℝ (n : ℕ∞ω) h (Set.Ioo 0 (π/2)))
    (hcont : ContinuousOn h (Set.Ioo 0 (π/2)))
    (hint : IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    ContDiffOn ℝ (n : ℕ∞ω) (LinvPrim h) (Set.Ioo 0 (π/2)) := by
  have hP1 : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (LinvPrim h) (Set.Ioo 0 (π/2)) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_LinvPrim_of hcont hint hx).differentiableAt.differentiableWithinAt
    · intro hcon
      exact absurd hcon (by simp)
    · refine (contDiffOn_linvInt hcd).congr ?_
      intro x hx
      exact (hasDerivAt_LinvPrim_of hcont hint hx).deriv
  exact hP1.of_le (by simp)

/-- The reciprocal weight `θ ↦ (sin²θ cos³θ)⁻¹` is smooth on `(0, π/2)`. -/
private lemma contDiffOn_inv_LinvMu {n : ℕ} :
    ContDiffOn ℝ (n : ℕ∞ω) (fun θ => (LinvMu θ)⁻¹) (Set.Ioo 0 (π/2)) := by
  refine ContDiffOn.inv ?_ ?_
  · show ContDiffOn ℝ (n : ℕ∞ω) (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3)
      (Set.Ioo 0 (π/2))
    fun_prop
  · intro x hx
    have hs : Real.sin x ≠ 0 := ne_of_gt (linv_sin_pos hx)
    have hc : Real.cos x ≠ 0 := ne_of_gt (linv_cos_pos hx)
    exact mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 3 hc)

theorem Linv_contDiffOn_hasDerivAt {h : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcd : ContDiffOn ℝ n h (Set.Ioo 0 (π/2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => h θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    ContDiffOn ℝ n (Work.FTS.PhiStar.Linv h) (Set.Ioo 0 (π/2)) ∧
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) →
        HasDerivAt (Work.FTS.PhiStar.Linv h)
          (-(1 / Real.sin (2 * θ)) * (h θ + 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2)
            * Work.FTS.PhiStar.Linv h θ)) θ := by
  have hcont : ContinuousOn h (Set.Ioo 0 (π/2)) := hcd.continuousOn
  have hLP : ContDiffOn ℝ (n : ℕ∞ω) (LinvPrim h) (Set.Ioo 0 (π/2)) :=
    contDiffOn_LinvPrim hcd hcont hint
  have hμinv : ContDiffOn ℝ (n : ℕ∞ω) (fun θ => (LinvMu θ)⁻¹) (Set.Ioo 0 (π/2)) :=
    contDiffOn_inv_LinvMu
  have hmain : ContDiffOn ℝ (n : ℕ∞ω) (Linv h) (Set.Ioo 0 (π/2)) := by
    rw [Linv_eq]
    exact (hμinv.mul hLP).neg
  refine ⟨hmain, ?_⟩
  intro θ hθ
  have hS : Real.sin θ ≠ 0 := ne_of_gt (linv_sin_pos hθ)
  have hC : Real.cos θ ≠ 0 := ne_of_gt (linv_cos_pos hθ)
  have h3 : HasDerivAt (fun θ => -((LinvMu θ)⁻¹ * LinvPrim h θ))
      (-(1 / Real.sin (2 * θ)) * (h θ + 2 * (2 * Real.cos θ ^ 2 - 3 * Real.sin θ ^ 2)
        * Linv h θ)) θ := by
    have hbase := ((hasDerivAt_LinvMu θ).inv (LinvMu_ne_zero_of_mem_Ioo hθ)).mul
      (hasDerivAt_LinvPrim_of hcont hint hθ)
    refine (hbase.neg).congr_deriv ?_
    rw [Linv_apply, LinvInt_eq, Real.sin_two_mul]
    simp only [LinvMu, Pi.inv_apply]
    field_simp
    ring
  rw [Linv_eq]
  exact h3

end Work.FTS.PhiStar.LinvFlat
