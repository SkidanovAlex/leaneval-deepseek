import Mathlib
import Submission.Work.RPB.B4.periodic_reduce
import Submission.Work.RPB.B4.periodic_deriv
import Submission.Work.RPB.B4.partial_deriv_eq

namespace Work.RPB.B5

/-- **Continuity of the slice derivative of a jointly `C¹` family.**

If the uncurrying `(τ, t) ↦ γ τ t` of a family `γ : ℝ → ℝ → ℂ` is `C¹`, then the family of
`t`-derivatives `(τ, t) ↦ deriv (γ τ) t` is continuous.

The slice derivative is the Fréchet derivative of the uncurrying applied to the direction `(0,1)`;
`ContDiff.continuous_fderiv` gives continuity of `p ↦ fderiv ℝ F p`, and evaluation at the fixed
vector `(0,1)` preserves it. -/
theorem continuous_deriv_family_one (γ : ℝ → ℝ → ℂ)
    (hγ : ContDiff ℝ 1 (fun z : ℝ × ℝ => γ z.1 z.2)) :
    Continuous (fun p : ℝ × ℝ => deriv (γ p.1) p.2) := by
  have hfun : (fun p : ℝ × ℝ => deriv (γ p.1) p.2)
      = fun p : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => γ z.1 z.2) p (0, 1) := by
    funext p
    exact (Work.RPB.B4.partial_deriv_eq (fun z : ℝ × ℝ => γ z.1 z.2) hγ p.1 p.2).deriv
  rw [hfun]
  exact (hγ.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The derivative of a `2π`-periodic family is `2π`-periodic in the same variable. -/
theorem deriv_family_shift_two_pi (γ : ℝ → ℝ → ℂ)
    (hper : ∀ τ t, γ τ (t + 2 * Real.pi) = γ τ t) (τ t : ℝ) :
    deriv (γ τ) (t + 2 * Real.pi) = deriv (γ τ) t :=
  Work.RPB.B4.periodic_deriv (γ τ) (2 * Real.pi) (hper τ) t

/-- **Uniform bounds for the derivative of a periodic `C¹` family of curves.**

For a jointly `C¹` family `γ : ℝ → ℝ → ℂ` which is `2π`-periodic in its second variable and whose
`t`-derivative `deriv (γ τ) t` is nowhere zero on the slab `τ ∈ [0,1]`, `t ∈ ℝ`, the norm of the
derivative admits a uniform positive lower bound `ε₁`, and is uniformly continuous on the slab:
there is `δ > 0`, `δ ≤ 1`, with `‖deriv (γ τ) (t+u) - deriv (γ τ) t‖ ≤ ε₁/2` whenever `|u| ≤ δ`.

The map `g : (τ,t) ↦ deriv (γ τ) t` is continuous (`continuous_deriv_family_one`) and `2π`-periodic
in `t` (`deriv_family_shift_two_pi`); on the compact box `[0,1] × [-1, 2π+1]` it therefore attains a
positive minimum `ε₁` for its norm, and is uniformly continuous (Heine–Cantor), which gives `δ`.
Periodicity reduces an arbitrary `t ∈ ℝ` to the fundamental domain, via
`Work.RPB.B4.periodic_reduce`. -/
theorem deriv_bounds_family (γ : ℝ → ℝ → ℂ)
    (hsm : ContDiff ℝ 1 (fun z : ℝ × ℝ => γ z.1 z.2))
    (hper : ∀ τ t, γ τ (t + 2 * Real.pi) = γ τ t)
    (hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (γ τ) t ≠ 0) :
    ∃ ε₁ > 0, ∃ δ > 0, δ ≤ 1 ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ε₁ ≤ ‖deriv (γ τ) t‖) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t u : ℝ,
        |u| ≤ δ → ‖deriv (γ τ) (t + u) - deriv (γ τ) t‖ ≤ ε₁ / 2) := by
  let g : ℝ × ℝ → ℂ := fun p => deriv (γ p.1) p.2
  have hg : Continuous g := continuous_deriv_family_one γ hsm
  have hperg : ∀ ρ t : ℝ, g (ρ, t + 2 * Real.pi) = g (ρ, t) :=
    fun ρ t => deriv_family_shift_two_pi γ hper ρ t
  -- the compact box on which the uniform bounds are measured
  have hKc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-1) (2 * Real.pi + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-1) (2 * Real.pi + 1)).Nonempty :=
    ⟨(0, 0), ⟨⟨le_refl 0, by norm_num⟩, ⟨by norm_num, by linarith [Real.pi_pos]⟩⟩⟩
  -- minimal norm on the box
  obtain ⟨p₀, hp₀K, hp₀min⟩ :=
    IsCompact.exists_isMinOn hKc hKne (continuous_norm.comp hg).continuousOn
  have hp₀mem : p₀.1 ∈ Set.Icc (0:ℝ) 1 := (Set.mem_prod.mp hp₀K).1
  have hne0 : g p₀ ≠ 0 := hderiv p₀.1 hp₀mem p₀.2
  have hε : 0 < ‖g p₀‖ := norm_pos_iff.mpr hne0
  -- uniform continuity on the box
  have hUC : UniformContinuousOn g (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-1) (2 * Real.pi + 1)) :=
    hKc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) (‖g p₀‖ / 2) (by linarith)
  have hδpos : 0 < min δ₀ 1 / 2 := by
    have h1 : 0 < min δ₀ 1 := lt_min hδ₀pos (by norm_num)
    linarith
  have hδle1 : min δ₀ 1 / 2 ≤ 1 := by
    have h : min δ₀ 1 ≤ 1 := min_le_right _ _
    linarith
  have hδltδ₀ : min δ₀ 1 / 2 < δ₀ := by
    have h : min δ₀ 1 ≤ δ₀ := min_le_left _ _
    linarith
  refine ⟨‖g p₀‖, hε, min δ₀ 1 / 2, hδpos, hδle1, ?_, ?_⟩
  · -- positive lower bound, reduced to the box by periodicity in `t`
    intro ρ hρ t
    obtain ⟨k, t', ht'mem, -, hft⟩ := Work.RPB.B4.periodic_reduce (fun s => g (ρ, s))
      (fun s => hperg ρ s) t
    have hbox : (ρ, t') ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-1) (2 * Real.pi + 1) :=
      ⟨hρ, ⟨by linarith [ht'mem.1], by linarith [ht'mem.2]⟩⟩
    have hmin : ‖g p₀‖ ≤ ‖g (ρ, t')‖ := hp₀min hbox
    show ‖g p₀‖ ≤ ‖g (ρ, t)‖
    rw [hft]
    exact hmin
  · -- uniform continuity, reduced to the box by periodicity in `t`
    intro ρ hρ t u hu
    obtain ⟨k, t', ht'mem, ht'eq, hft⟩ := Work.RPB.B4.periodic_reduce (fun s => g (ρ, s))
      (fun s => hperg ρ s) t
    have hbox1 : (ρ, t') ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-1) (2 * Real.pi + 1) :=
      ⟨hρ, ⟨by linarith [ht'mem.1], by linarith [ht'mem.2]⟩⟩
    have hu1 : -u ≤ min δ₀ 1 / 2 := by
      have := (abs_le.mp hu).1
      linarith
    have hu2 : u ≤ min δ₀ 1 / 2 := (abs_le.mp hu).2
    have hbox2 : (ρ, t' + u) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-1) (2 * Real.pi + 1) :=
      ⟨hρ, ⟨by linarith [ht'mem.1, hu1, hδle1], by linarith [ht'mem.2, hu2, hδle1]⟩⟩
    have hdist : dist (ρ, t') (ρ, t' + u) < δ₀ := by
      have hd : dist (ρ, t') (ρ, t' + u) = |u| := by
        have h2 : dist t' (t' + u) = |u| := by
          rw [Real.dist_eq, show t' - (t' + u) = -u by ring, abs_neg]
        rw [Prod.dist_eq, dist_self, h2, max_eq_right (abs_nonneg u)]
      rw [hd]
      exact lt_of_le_of_lt hu hδltδ₀
    have hb := hδ₀ (ρ, t') hbox1 (ρ, t' + u) hbox2 hdist
    rw [dist_eq_norm] at hb
    have heq2 : g (ρ, t + u) = g (ρ, t' + u) := by
      rw [show t + u = (t' + u) + k • (2 * Real.pi) by rw [ht'eq]; abel]
      exact ((show Function.Periodic (fun s => g (ρ, s)) (2 * Real.pi) from
        fun s => hperg ρ s).zsmul k) (t' + u)
    show ‖g (ρ, t + u) - g (ρ, t)‖ ≤ ‖g p₀‖ / 2
    rw [heq2, hft, norm_sub_rev]
    exact le_of_lt hb

end Work.RPB.B5
