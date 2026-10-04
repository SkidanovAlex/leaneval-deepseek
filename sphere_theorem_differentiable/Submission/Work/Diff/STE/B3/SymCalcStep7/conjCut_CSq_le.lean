import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.flatCut_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-- **The transported cutoff `V = conjCut ρ ε T T'` is of order `0`**, uniformly in `ε ∈ (0,1]`: `conjCut ρ ε T T' w = compMap T' (flatCut ρ ε (compMap T w))`, so the claim is the `flatCut_CSq_le` bound composed with two applications of `Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le` (for `T` and for `T'`; injectivity and non-vanishing of the differentials of `T`, `T'` are derived from `hTinv1`, `hTinv2`, and the `1`-periodicity of `T'` from `T` via `Work.Diff.STE.B3.SymCalcStep1.shift_T'`). -/
theorem conjCut_CSq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℝ) → ℝ)
    (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ w : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
      Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' w))
        ≤ C * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff w) := by
  classical
  -- ## Injectivity and invertibility of the differentials of `T` and `T'`
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
  have hdet_of : ∀ (A B : (ι → ℝ) →L[ℝ] (ι → ℝ)), A.comp B = 1 → B.det ≠ 0 := by
    intro A B hcomp hz
    have hinj : Function.Injective B := fun u v huv => by
      have h1 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L u) hcomp
      have h2 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
      rw [huv] at h1
      exact h1.symm.trans h2
    have hz' : LinearMap.det ((B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 0 := hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz') (by rw [LinearMap.ker_eq_bot]; exact hinj)
  have hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun x => T' (T x)) z = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hT'.differentiable (by simp)).differentiableAt)
        ((hT.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hT'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  -- ## The periodicity of `T'`
  have hT'per : ∀ (i : ι) (y : ι → ℝ), T' (y + Pi.single i 1) = T' y + Pi.single i 1 :=
    Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2
  -- ## The two pull-back bounds
  obtain ⟨C1, hC1nn, hC1⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le t T hT hTper hinjT hdetT
  obtain ⟨C2, hC2nn, hC2⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le t T' hT' hT'per hinjT' hdetT'
  refine ⟨C2 * C1, mul_nonneg hC2nn hC1nn, ?_⟩
  intro ε hε hε1 w hw hwp
  -- ## smoothness and periodicity of the intermediate objects
  have hcmp_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T w) := hw.comp hT
  have hcmp_per : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T w) := by
    intro i x
    show w (T (x + Pi.single i 1)) = w (T x)
    rw [hTper]
    exact hwp i (T x)
  set h : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalc.compMap T w with hh
  have hhsm : ContDiff ℝ (⊤ : ℕ∞) h := hcmp_sm
  have hhper : Work.Diff.STE.Periodic1 h := hcmp_per
  have hflat_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hhsm hhper
  have hflat_per : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε h
  -- the cutoff step and the two transport steps
  have hstep1 : Work.Diff.STE.CSq t
      (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h))
      ≤ Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff h) :=
    flatCut_CSq_le ρ hρ ε t h hhsm hhper
  have hstep2 : Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff h)
      ≤ C1 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff w) :=
    hC1 w hw hwp
  have hstep3 : Work.Diff.STE.CSq t
      (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T'
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)))
      ≤ C2 * Work.Diff.STE.CSq t
        (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)) :=
    hC2 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) hflat_sm hflat_per
  calc Work.Diff.STE.CSq t
        (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' w))
      = Work.Diff.STE.CSq t
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T'
            (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h))) := rfl
    _ ≤ C2 * Work.Diff.STE.CSq t
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)) := hstep3
    _ ≤ C2 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff h) :=
        mul_le_mul_of_nonneg_left hstep1 hC2nn
    _ ≤ C2 * (C1 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff w)) :=
        mul_le_mul_of_nonneg_left hstep2 hC2nn
    _ = C2 * C1 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff w) := by ring

end Work.Diff.STE.B3.SymCalcStep7
