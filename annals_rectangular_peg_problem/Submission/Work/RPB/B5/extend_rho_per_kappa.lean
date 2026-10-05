import Mathlib
import Submission.Work.RPB.B5.extend_rho_per

namespace Work.RPB.B5

open scoped ContDiff

/-- **Rescaling of the `κ = 1` extension.**  Given the radius family `ρh` on the slab
`[0,1] × ℝ × (-κ,κ)`, the rescaled family `ρh₁ τ t σ = ρh τ t (κ σ)` satisfies all the hypotheses of
`Work.RPB.B5.extend_rho_per`, so it admits a global `C⁸`, `2π`-periodic extension `ρe₁` on the unit
slab `(-1,1)`.  Undoing the rescaling, `ρe τ t σ = ρe₁ τ t (σ/κ)` is the required extension of `ρh`;
the constants `1/2` and `1/4` become `κ/2` and `κ/4`, and the uniform Lipschitz constant `L₁` becomes
`L₁/κ`. -/
theorem extend_rho_per_kappa (ρh : ℝ → ℝ → ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (hhmono : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      deriv (fun s : ℝ => ρh τ t s) σ ≠ 0)
    (hhpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) 0, 0 < ρh τ t σ) :
    ∃ (ρe : ℝ → ℝ → ℝ → ℝ) (L : ℝ), 0 < L ∧
      ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρe z.1 z.2.1 z.2.2) ∧
      (∀ τ t σ, ρe τ (t + 2 * Real.pi) σ = ρe τ t σ) ∧
      (∀ τ t, ρe τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| < κ / 2 → ρe τ t σ = ρh τ t σ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ κ / 4 → |ρh τ t σ| ≤ L * |σ|) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ κ / 4 →
        deriv (fun s : ℝ => ρe τ t s) σ < 0) := by
  classical
  -- Rescale the last variable so that the slab `(-κ,κ)` becomes the unit slab `(-1,1)`.
  let ρh₁ : ℝ → ℝ → ℝ → ℝ := fun τ t σ => ρh τ t (κ * σ)
  have h1_cd : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh₁ z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1) := by
    have hΦ : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, κ * z.2.2))) := by
      fun_prop
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, κ * z.2.2)))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := by
      rintro ⟨τ, t, σ⟩ ⟨hτ, -, hσ⟩
      refine ⟨hτ, trivial, ?_⟩
      rw [Set.mem_Ioo] at hσ ⊢
      exact ⟨by nlinarith [hσ.1, hκ], by nlinarith [hσ.2, hκ]⟩
    show ContDiffOn ℝ 8 ((fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      ∘ (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, κ * z.2.2))))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1) 1)
    exact hh.comp hΦ.contDiffOn hmap
  have h1_0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh₁ τ t 0 = 0 := by
    intro τ hτ t
    show ρh τ t (κ * 0) = 0
    rw [mul_zero]
    exact hh0 τ hτ t
  have h1_per : ∀ τ t σ, ρh₁ τ (t + 2 * Real.pi) σ = ρh₁ τ t σ := by
    intro τ t σ
    exact hhper τ t (κ * σ)
  have h1_mono : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1 : ℝ) 1,
      deriv (fun s : ℝ => ρh₁ τ t s) σ ≠ 0 := by
    intro τ hτ t σ hσ
    have hκσ : κ * σ ∈ Set.Ioo (-κ) κ := by
      rw [Set.mem_Ioo] at hσ ⊢
      exact ⟨by nlinarith [hσ.1, hκ], by nlinarith [hσ.2, hκ]⟩
    have hne : deriv (fun u : ℝ => ρh τ t u) (κ * σ) ≠ 0 := hhmono τ hτ t (κ * σ) hκσ
    -- a non-zero `deriv` already forces differentiability
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => ρh τ t u) (κ * σ) := by
      by_contra h
      exact hne (deriv_zero_of_not_differentiableAt h)
    have hinner : HasDerivAt (fun s : ℝ => κ * s) κ σ := hasDerivAt_const_mul κ
    have houter : HasDerivAt (fun u : ℝ => ρh τ t u)
        (deriv (fun u : ℝ => ρh τ t u) (κ * σ)) (κ * σ) := hdiff.hasDerivAt
    have hcomp : HasDerivAt ((fun u : ℝ => ρh τ t u) ∘ (fun s : ℝ => κ * s))
        (deriv (fun u : ℝ => ρh τ t u) (κ * σ) * κ) σ := houter.comp σ hinner
    have hd : deriv (fun s : ℝ => ρh₁ τ t s) σ
        = deriv (fun u : ℝ => ρh τ t u) (κ * σ) * κ := by
      show deriv ((fun u : ℝ => ρh τ t u) ∘ (fun s : ℝ => κ * s)) σ
        = deriv (fun u : ℝ => ρh τ t u) (κ * σ) * κ
      exact hcomp.deriv
    rw [hd]
    exact mul_ne_zero hne hκ.ne'
  have h1_pos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-1 : ℝ) 0,
      0 < ρh₁ τ t σ := by
    intro τ hτ t σ hσ
    have hκσ : κ * σ ∈ Set.Ioo (-κ) 0 := by
      rw [Set.mem_Ioo] at hσ ⊢
      exact ⟨by nlinarith [hσ.1, hκ], by nlinarith [hσ.2, hκ]⟩
    exact hhpos τ hτ t (κ * σ) hκσ
  -- Apply the `κ = 1` extension lemma to the rescaled family.
  obtain ⟨ρe₁, L₁, hL₁, hcd₁, hper₁, h0₁, hagree₁, hbnd₁, hder₁⟩ :=
    extend_rho_per ρh₁ h1_cd h1_0 h1_per h1_mono h1_pos
  refine ⟨fun τ t σ => ρe₁ τ t (σ / κ), L₁ / κ, div_pos hL₁ hκ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- global smoothness of the rescaled-back extension
    have hΨ : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, z.2.2 / κ))) := by
      fun_prop
    show ContDiff ℝ 8 ((fun z : ℝ × (ℝ × ℝ) => ρe₁ z.1 z.2.1 z.2.2)
      ∘ (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, z.2.2 / κ))))
    exact hcd₁.comp hΨ
  · -- periodicity in `t`
    intro τ t σ
    exact hper₁ τ t (σ / κ)
  · -- vanishing at `σ = 0`
    intro τ t
    show ρe₁ τ t (0 / κ) = 0
    rw [zero_div]
    exact h0₁ τ t
  · -- agreement with `ρh` on `|σ| < κ/2`
    intro τ hτ t σ hσ
    have hσ' : |σ / κ| < 1 / 2 := by
      rw [abs_div, abs_of_pos hκ, div_lt_iff₀ hκ]
      linarith [hσ]
    show ρe₁ τ t (σ / κ) = ρh τ t σ
    rw [hagree₁ τ hτ t (σ / κ) hσ']
    show ρh τ t (κ * (σ / κ)) = ρh τ t σ
    rw [mul_div_cancel₀ σ hκ.ne']
  · -- the uniform linear bound
    intro τ hτ t σ hσ
    have hσ' : |σ / κ| ≤ 1 / 4 := by
      rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
      linarith [hσ]
    have hb := hbnd₁ τ hτ t (σ / κ) hσ'
    have hleft : ρh₁ τ t (σ / κ) = ρh τ t σ := by
      show ρh τ t (κ * (σ / κ)) = ρh τ t σ
      rw [mul_div_cancel₀ σ hκ.ne']
    rw [hleft, abs_div, abs_of_pos hκ] at hb
    calc |ρh τ t σ| ≤ L₁ * (|σ| / κ) := hb
      _ = (L₁ / κ) * |σ| := by ring
  · -- strict negativity of the `σ`-derivative
    intro τ hτ t σ hσ
    have hσ' : |σ / κ| ≤ 1 / 4 := by
      rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
      linarith [hσ]
    have hslice : ContDiff ℝ 8 (fun u : ℝ => ρe₁ τ t u) :=
      hcd₁.comp (by fun_prop : ContDiff ℝ 8 (fun u : ℝ => (τ, (t, u))))
    have hdiff0 : Differentiable ℝ (fun u : ℝ => ρe₁ τ t u) :=
      hslice.differentiable (by norm_num)
    have hinner : HasDerivAt (fun s : ℝ => s / κ) (1 / κ) σ := by
      simpa using (hasDerivAt_id σ).div_const κ
    have houter : HasDerivAt (fun u : ℝ => ρe₁ τ t u)
        (deriv (fun u : ℝ => ρe₁ τ t u) (σ / κ)) (σ / κ) :=
      (hdiff0 (σ / κ)).hasDerivAt
    have hcomp : HasDerivAt ((fun u : ℝ => ρe₁ τ t u) ∘ (fun s : ℝ => s / κ))
        (deriv (fun u : ℝ => ρe₁ τ t u) (σ / κ) * (1 / κ)) σ := houter.comp σ hinner
    have hd : deriv (fun s : ℝ => ρe₁ τ t (s / κ)) σ
        = deriv (fun u : ℝ => ρe₁ τ t u) (σ / κ) * (1 / κ) := by
      show deriv ((fun u : ℝ => ρe₁ τ t u) ∘ (fun s : ℝ => s / κ)) σ
        = deriv (fun u : ℝ => ρe₁ τ t u) (σ / κ) * (1 / κ)
      exact hcomp.deriv
    rw [hd]
    have hneg := hder₁ τ hτ t (σ / κ) hσ'
    have hpos : (0 : ℝ) < 1 / κ := by positivity
    exact mul_neg_of_neg_of_pos hneg hpos

end Work.RPB.B5
