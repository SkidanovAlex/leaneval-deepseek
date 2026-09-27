import Mathlib

namespace Work.Drive

/-- **The tube around the axis of a periodic continuous function.** A continuous function
`g : ℝ × ℝ → ℝ` which is `2π`-periodic in its first variable and positive on the axis
`τ = 0` is positive on a whole *uniform* band `|τ| ≤ δ`.  (Compactness of `[0, 2π]` + the tube
lemma; this is what turns the pointwise openness conditions at the seam circle into a positive
radius uniform in `σ`.) -/
theorem uniform_band_of_periodic {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hper : ∀ σ τ : ℝ, g (σ + 2 * Real.pi, τ) = g (σ, τ))
    (h0 : ∀ σ : ℝ, 0 < g (σ, 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ τ : ℝ, |τ| ≤ δ → 0 < g (σ, τ) := by
  -- Step 1: a uniform positive lower bound `g (σ₀, 0)` for `g (·, 0)` on one period `[0, 2π]`.
  have hcont_axis : Continuous fun σ : ℝ => g (σ, 0) :=
    hg.comp (continuous_id.prodMk continuous_const)
  obtain ⟨σ₀, hσ₀, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).exists_isMinOn
    ⟨0, ⟨le_refl 0, by positivity⟩⟩ hcont_axis.continuousOn
  have hm_pos : 0 < g (σ₀, 0) := h0 σ₀
  have hm_le : ∀ σ ∈ Set.Icc (0:ℝ) (2 * Real.pi), g (σ₀, 0) ≤ g (σ, 0) := fun σ hσ => hmin hσ
  -- Step 2: uniform continuity of `g` on the compact rectangle `[0, 2π] × [-1, 1]`.
  have hK : IsCompact (Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (-1:ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn g (Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (-1:ℝ) 1) :=
    hK.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δuc, hδuc_pos, hδuc⟩ := huc (g (σ₀, 0) / 2) (by linarith)
  -- Step 3: a uniform band over one period.
  have hband : ∀ σ ∈ Set.Icc (0:ℝ) (2*Real.pi), ∀ τ : ℝ,
      |τ| ≤ min (δuc / 2) 1 → 0 < g (σ, τ) := by
    intro σ hσ τ hτ
    have hτ1 : |τ| ≤ 1 := le_trans hτ (min_le_right _ _)
    have hτd : |τ| < δuc := lt_of_le_of_lt (le_trans hτ (min_le_left _ _)) (by linarith)
    have hxK : (σ, τ) ∈ Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (-1:ℝ) 1 :=
      ⟨hσ, abs_le.mp hτ1⟩
    have hyK : (σ, 0) ∈ Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (-1:ℝ) 1 :=
      ⟨hσ, by constructor <;> norm_num⟩
    have hd : dist (σ, τ) (σ, 0) < δuc := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, max_eq_right (abs_nonneg τ)]
      exact hτd
    have hclose := hδuc (σ, τ) hxK (σ, 0) hyK hd
    rw [Real.dist_eq] at hclose
    have hlow : g (σ₀, 0) ≤ g (σ, 0) := hm_le σ hσ
    have habs := abs_lt.mp hclose
    linarith [habs.1, hlow, hm_pos]
  -- Step 4: reduce an arbitrary `σ` to one lying in `[0, 2π]` using `2π`-periodicity.
  have hred : ∀ (σ τ : ℝ), ∃ σ' ∈ Set.Icc (0:ℝ) (2*Real.pi), g (σ, τ) = g (σ', τ) := by
    intro σ τ
    have hp : Function.Periodic (fun σ τ : ℝ => g (σ, τ)) (2 * Real.pi) :=
      fun σ => funext fun τ => hper σ τ
    refine ⟨2 * Real.pi * Int.fract (σ / (2 * Real.pi)), ⟨?_, ?_⟩, ?_⟩
    · have h := Int.fract_nonneg (σ / (2 * Real.pi))
      exact mul_nonneg (by linarith [Real.pi_pos]) h
    · have h := Int.fract_lt_one (σ / (2 * Real.pi))
      have := mul_le_of_le_one_right (show (0:ℝ) ≤ 2 * Real.pi by linarith [Real.pi_pos])
        (le_of_lt h)
      simpa using this
    · have hrec : σ = 2 * Real.pi * Int.fract (σ / (2*Real.pi))
          + (⌊σ / (2*Real.pi)⌋ : ℝ) * (2 * Real.pi) := by
        have h1 : (⌊σ / (2*Real.pi)⌋ : ℝ) + Int.fract (σ / (2*Real.pi)) = σ / (2*Real.pi) :=
          Int.floor_add_fract _
        have h2 : ((⌊σ / (2*Real.pi)⌋ : ℝ) + Int.fract (σ / (2*Real.pi))) * (2*Real.pi) = σ := by
          rw [h1, div_mul_cancel₀ _ (by positivity)]
        conv_lhs => rw [← h2]
        ring
      conv_lhs => rw [hrec]
      exact congrFun (hp.int_mul ⌊σ / (2*Real.pi)⌋ (2 * Real.pi * Int.fract (σ / (2*Real.pi)))) τ
  refine ⟨min (δuc / 2) 1, lt_min (by linarith) one_pos, ?_⟩
  intro σ τ hτ
  obtain ⟨σ', hσ', heq⟩ := hred σ τ
  rw [heq]
  exact hband σ' hσ' τ hτ

end Work.Drive
