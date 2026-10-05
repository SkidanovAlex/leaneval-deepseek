import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.B5.exists_add_int_mul_mem_Icc

/-!
# B5: uniform positive lower bound for the `π/2`-chord of a curve isotopy

For `τ ∈ [0,1]` the curve `t ↦ CI.c τ t` is an embedded `2π`-periodic curve with nonvanishing
derivative; since `t + π/2 - (t - π/2) = π` is not a multiple of `2π`, the two points of the
`π/2`-chord are distinct, and compactness of `[0,1] × [0,2π]` (with `2π`-periodicity in `t`)
turns that pointwise nonvanishing into a uniform positive lower bound.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The uniform chord length of the `π/2`-chord. -/
theorem chord_pi_lower_bound (CI : Work.RPV.CurveIsotopy) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ,
      μ ≤ ‖CI.c τ (t + Real.pi / 2) - CI.c τ (t - Real.pi / 2)‖ := by
  set g : ℝ × ℝ → ℝ :=
    fun p => ‖CI.c p.1 (p.2 + Real.pi / 2) - CI.c p.1 (p.2 - Real.pi / 2)‖ with hg
  have hc : Continuous (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.continuous
  have hcont : Continuous g := by
    rw [hg]
    exact ((hc.comp (Continuous.prodMk continuous_fst
        (continuous_snd.add continuous_const))).sub
      (hc.comp (Continuous.prodMk continuous_fst
        (continuous_snd.sub continuous_const)))).norm
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)).Nonempty :=
    Set.Nonempty.prod ⟨0, by simp only [Set.mem_Icc]; exact ⟨le_refl 0, by norm_num⟩⟩
      ⟨0, by simp only [Set.mem_Icc]; exact ⟨le_refl 0, by positivity⟩⟩
  -- pointwise positivity of the chord length on the fundamental domain
  have hgpos : ∀ p ∈ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)), 0 < g p := by
    rintro ⟨τ, s⟩ hp
    rw [Set.mem_prod] at hp
    obtain ⟨hτ, _hs⟩ := hp
    rw [hg]
    simp only []
    rw [norm_pos_iff]
    intro hcEq
    obtain ⟨m, hm⟩ :=
      CI.inj τ hτ (s + Real.pi / 2) (s - Real.pi / 2) (sub_eq_zero.mp hcEq)
    have key : (2 * (m:ℝ) + 1) * Real.pi = 0 := by nlinarith [hm]
    rcases mul_eq_zero.mp key with h | h
    · have h4 : ((2*m + 1 : ℤ) : ℝ) = ((0:ℤ):ℝ) := by push_cast; linarith
      exact absurd (Int.cast_injective h4) (by omega)
    · exact Real.pi_ne_zero h
  obtain ⟨p₀, hp₀K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  rw [IsMinOn, IsMinFilter, Filter.eventually_principal] at hmin
  refine ⟨g p₀, hgpos p₀ hp₀K, ?_⟩
  intro τ hτ t
  obtain ⟨t₀, k, ht₀, ht⟩ := exists_add_int_mul_mem_Icc t (2 * Real.pi) (by positivity)
  have hmem : (τ, t₀) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) :=
    Set.mem_prod.mpr ⟨hτ, ht₀⟩
  have hper : Function.Periodic (fun s => CI.c τ s) (2 * Real.pi) := fun s => CI.per τ s
  have heq : g (τ, t₀) = g (τ, t) := by
    simp only [hg]
    have h1 : CI.c τ (t + Real.pi / 2) = CI.c τ (t₀ + Real.pi / 2) := by
      rw [ht]
      have hthis := Function.Periodic.int_mul hper k (t₀ + Real.pi / 2)
      rw [show t₀ + (k:ℝ) * (2 * Real.pi) + Real.pi / 2
            = (t₀ + Real.pi / 2) + (k:ℝ) * (2 * Real.pi) by ring]
      exact hthis
    have h2 : CI.c τ (t - Real.pi / 2) = CI.c τ (t₀ - Real.pi / 2) := by
      rw [ht]
      have hthis := Function.Periodic.int_mul hper k (t₀ - Real.pi / 2)
      rw [show t₀ + (k:ℝ) * (2 * Real.pi) - Real.pi / 2
            = (t₀ - Real.pi / 2) + (k:ℝ) * (2 * Real.pi) by ring]
      exact hthis
    rw [h1, h2]
  calc g p₀ ≤ g (τ, t₀) := hmin (τ, t₀) hmem
    _ = g (τ, t) := heq

end Work.RPB.B5
