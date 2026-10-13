import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Construction.H6N_GammaTerm_Lop_bound
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- The `𝒲^{l,∞}`-weight `Wt α θ = sin(2θ)^{-α/5}/(α + sin 2θ)` times the pointwise
bound `Γ(θ)·(sin²2θ + α)` for the `D_θ`-iterates of `ψ = c2m·Γ` is bounded by `1` on the
whole of `Iθ` (at the two endpoints both factors `Wt` and `Γ` vanish). -/
theorem gam_mul_sq_add_alpha_mul_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
      * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ 1 := by
  by_cases hθo : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.FstarPkg.sin_two_nonneg_of_mem_Iθ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hB : Work.Spaces.Gam α θ * Real.sin (2 * θ) ^ (-(α / 5)) ≤ 1 :=
      Work.FTS.Nonlinear.FstarPkg.GamSinRpowMulLeOne hα hα1 hθ
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hnum : 0 ≤ Real.sin (2 * θ) ^ 2 + α := by positivity
    have hfrac : (Real.sin (2 * θ) ^ 2 + α) / (α + Real.sin (2 * θ)) ≤ 1 := by
      rw [div_le_one hden]
      nlinarith [hs0, hs1, hα]
    have hid : Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        = (Work.Spaces.Gam α θ * Real.sin (2 * θ) ^ (-(α / 5)))
          * ((Real.sin (2 * θ) ^ 2 + α) / (α + Real.sin (2 * θ))) := by
      simp only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt]
      ring
    rw [hid]
    simpa using mul_le_mul hB hfrac (div_nonneg hnum hden.le) (by norm_num : (0 : ℝ) ≤ 1)
  · have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
      rcases hθ with ⟨h0, h1⟩
      rcases lt_or_eq_of_le h0 with h | h
      · right
        by_contra hne
        exact hθo ⟨h, lt_of_le_of_ne h1 hne⟩
      · exact Or.inl h.symm
    have hs : Real.sin (2 * θ) = 0 := by
      rcases hcases with h | h
      · rw [h]; simp
      · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have hWt : Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ = 0 := by
      simp only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt, hs]
      rw [Real.zero_rpow (by intro hc; linarith [hα]), zero_div]
    rw [hWt, mul_zero]
    norm_num

/-- On `Iθ` the angular factor `ψ = c2m·Γ`, its `D_θ`-iterates to order `6` and the
`𝒲^{6,∞}`-weight `Wt` satisfy `|D_θ^j ψ| · Wt ≤ 10⁹`, uniformly in `0 < α ≤ 1`. -/
theorem c2mGam_Wt_bound : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (j : ℕ), 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[j]) (Work.Construction.psiA α) θ|
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ K := by
  obtain ⟨D, hD, hDb⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
  refine ⟨D, hD, ?_⟩
  intro α hα hα1 j hj1 hj6 θ hθ
  by_cases hθo : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · have hbd := hDb α hα hα1 j hj1 hj6 θ hθo
    have hWt0 : 0 ≤ Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ :=
      Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
    have hkern : Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
        * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ 1 :=
      gam_mul_sq_add_alpha_mul_Wt_le_one hα hα1 hθ
    have hid : (D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α))
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        = D * (Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := by ring
    calc |(Work.Spaces.Lop^[j]) (Work.Construction.psiA α) θ|
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ
        ≤ (D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α))
            * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ :=
          mul_le_mul_of_nonneg_right hbd hWt0
      _ = D * (Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)
            * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ) := hid
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hkern hD.le
      _ = D := by ring
  · have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
      rcases hθ with ⟨h0, h1⟩
      rcases lt_or_eq_of_le h0 with h | h
      · right
        by_contra hne
        exact hθo ⟨h, lt_of_le_of_ne h1 hne⟩
      · exact Or.inl h.symm
    have hs : Real.sin (2 * θ) = 0 := by
      rcases hcases with h | h
      · rw [h]; simp
      · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    have hWt : Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ = 0 := by
      simp only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt, hs]
      rw [Real.zero_rpow (by intro hc; linarith [hα]), zero_div]
    rw [hWt, mul_zero]
    exact hD.le

end Work.FTS.StrongPersist.H6Pair6Aux
