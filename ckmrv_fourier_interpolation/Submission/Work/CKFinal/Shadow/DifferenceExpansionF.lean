import Submission.Work.FunctionalEquations.DifferenceExpansionF
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (PeriodicIntTranslate)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (DirichletExpansion)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (hasSum_nat_shift)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

theorem DifferenceExpansionF {n : ℕ} [NeZero n]
    (S : Work.FE.FunctionalEquationSolution n) (x : Work.FE.E n) :
    ∃ c : Set.Ici (1 : ℕ) → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          c m * Work.FE.dirichletTerm m.1 τ)
        (S.F (τ + 1) x - S.F τ x)) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        c m = ∫ t in (0 : ℝ)..1, (S.F ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
            - S.F ((t : ℂ) + (y : ℂ) * Complex.I) x) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨α, β, hα0, hβpos, hunif⟩ := S.uniform_F
  set h : ℂ → ℂ := fun τ => S.F (τ + 1) x - S.F τ x with hhdef
  have hper : ∀ τ : ℂ, 0 < τ.im → h (τ + 1) = h τ := by
    intro τ hτ
    have hr := S.recur_F τ x hτ
    simp only [hhdef]
    rw [show τ + 1 + 1 = τ + 2 from by ring]
    linear_combination hr
  have hhol : DifferentiableOn ℂ h {τ : ℂ | 0 < τ.im} := by
    have h1 : DifferentiableOn ℂ (fun τ : ℂ => S.F (τ + 1) x) {τ : ℂ | 0 < τ.im} := by
      have hg : DifferentiableOn ℂ (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} := by
        fun_prop
      refine (S.holomorphic_F x).comp hg ?_
      intro τ hτ; simpa using hτ
    rw [hhdef]
    exact h1.sub (S.holomorphic_F x)
  have himk : ∀ τ : ℂ, (τ - (⌈τ.re⌉ : ℂ)).im = τ.im := by
    intro τ
    simp [Complex.sub_im]
  have hM : ∀ τ : ℂ, 0 < τ.im → ‖h τ‖ ≤ 2 * α * τ.im ^ (-β) := by
    intro τ hτ
    set k : ℤ := ⌈τ.re⌉ with hk
    have him : (τ - (k : ℂ)).im = τ.im := by simp [Complex.sub_im]
    have hτ' : 0 < (τ - (k : ℂ)).im := by rw [him]; exact hτ
    have hτ'' : 0 < (τ - (k : ℂ) + 1).im := by
      rw [show (τ - (k:ℂ) + 1).im = τ.im by simp [Complex.add_im, Complex.sub_im]]; exact hτ
    have htrans : h (τ - (k : ℂ)) = h τ := by
      have hkcast : ((-k : ℤ) : ℂ) = -(k : ℂ) := by push_cast; ring
      simpa [hkcast, sub_eq_add_neg] using PeriodicIntTranslate hper (-k) τ hτ
    have hklt : ((k : ℤ) : ℝ) < τ.re + 1 := by rw [hk]; exact Int.ceil_lt_add_one τ.re
    have hkle : τ.re ≤ ((k : ℤ) : ℝ) := by rw [hk]; exact Int.le_ceil τ.re
    have hre : (τ - (k : ℂ)).re = τ.re - ((k : ℤ) : ℝ) := by
      simp [Complex.sub_re]
    have hre_lo : -1 ≤ (τ - (k : ℂ)).re := by rw [hre]; linarith
    have hre_hi : (τ - (k : ℂ)).re ≤ 1 := by rw [hre]; linarith
    have hre1 : -1 ≤ (τ - (k : ℂ) + 1).re := by
      rw [Complex.add_re, Complex.one_re]; linarith
    have hre2 : (τ - (k : ℂ) + 1).re ≤ 1 := by
      rw [Complex.add_re, Complex.one_re]; linarith
    rw [← htrans]
    calc ‖h (τ - (k : ℂ))‖
        = ‖S.F (τ - (k : ℂ) + 1) x - S.F (τ - (k : ℂ)) x‖ := by simp only [hhdef]
      _ ≤ ‖S.F (τ - (k : ℂ) + 1) x‖ + ‖S.F (τ - (k : ℂ)) x‖ := norm_sub_le _ _
      _ ≤ α * (τ - (k : ℂ) + 1).im ^ (-β) + α * (τ - (k : ℂ)).im ^ (-β) :=
            add_le_add (hunif _ x hτ'' hre1 hre2) (hunif _ x hτ' hre_lo hre_hi)
      _ = 2 * α * τ.im ^ (-β) := by
            rw [show (τ - (k:ℂ) + 1).im = τ.im by simp [Complex.add_im, Complex.sub_im], him]
            ring
  have hMbound : ∃ A β' : ℝ, 0 ≤ A ∧ 0 ≤ β' ∧
      ∀ y : ℝ, 0 < y → 2 * α * y ^ (-β) ≤ A * y ^ (-β') :=
    ⟨2 * α, β, by linarith, le_of_lt hβpos, fun y _ => le_refl _⟩
  have hdecay : ∀ m : ℕ, Tendsto (fun y : ℝ =>
      (2 * α * y ^ (-β)) * Real.exp (-(2 * Real.pi) * y) ^ m) atTop (𝓝 0) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have h0 : Tendsto (fun y : ℝ => y ^ (-β)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hβpos
      have hc : Tendsto (fun _ : ℝ => 2 * α) atTop (𝓝 (2 * α)) := tendsto_const_nhds
      simpa [pow_zero, mul_one] using hc.mul h0
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
      have hbase : Tendsto (fun y : ℝ =>
          y ^ (-β) * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1)) * y)) atTop (𝓝 0) :=
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-β) (2 * Real.pi * ((k : ℝ) + 1))
          (by positivity)
      have hc : Tendsto (fun _ : ℝ => 2 * α) atTop (𝓝 (2 * α)) := tendsto_const_nhds
      have heq : (fun y : ℝ => (2 * α * y ^ (-β)) * Real.exp (-(2 * Real.pi) * y) ^ (k + 1))
          = (fun y : ℝ => (2 * α) *
              (y ^ (-β) * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1)) * y))) := by
        funext y
        rw [← Real.exp_nat_mul]
        rw [show (↑(k + 1) : ℝ) * (-(2 * Real.pi) * y)
            = -(2 * Real.pi * ((k : ℝ) + 1)) * y from by push_cast; ring]
        ring
      rw [heq]
      simpa using hc.mul hbase
  obtain ⟨c', hc'sum, hc'int⟩ :=
    DirichletExpansion h hper hhol (fun y : ℝ => 2 * α * y ^ (-β)) hM hMbound hdecay
  refine ⟨fun m => c' (m.1 - 1), ?_, ?_⟩
  · intro τ hτ
    have hsum := hc'sum τ hτ
    have hshift := hasSum_nat_shift (c := c') (τ := τ) hsum
    have hdir : (fun m : Set.Ici (1 : ℕ) =>
          c' (m.1 - 1) * dirichletTerm m.1 τ)
        = (fun m : Set.Ici (1 : ℕ) =>
          c' (m.1 - 1) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * τ)) := by
      funext m; rw [dirichletTerm]
    rw [hdir]
    simpa only [hhdef] using hshift
  · intro m y hy
    have h1 := hc'int (m.1 - 1) y hy
    change c' (m.1 - 1) = _
    rw [h1]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [hhdef]
    rw [show ((m.1 - 1 : ℕ) : ℂ) + 1 = (m.1 : ℂ) from by
      rw [Nat.cast_sub m.2]; ring]

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
