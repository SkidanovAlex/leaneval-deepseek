import Mathlib
import Submission.Work.WilC4aAL.Defs
import Submission.Work.WilC4aAL.Basic

namespace Work.WilC4aAL

open Classical Topology Filter
open WilkiesDesign.CG.C4a

theorem selector_zero_of_sign_zero {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ}
    (i₀ : Fin k) (hc : ∀ j, AnalyticAt ℝ (c i₀ j) 0) (hc₀ : ∀ j, c i₀ j 0 = 0)
    {ρ : ℝ → ℝ} (hρ : AnalyticAt ℝ ρ 0) {σ : Fin k → SignType} (hσ : σ i₀ = 0)
    (h : ∃ r₀ > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r₀, SignVectorOk c σ r (ρ r)) :
    ρ 0 = 0 := by
  obtain ⟨r₀, hr₀, hsr⟩ := h
  -- The function r ↦ mpoly (c i₀) r (ρ r) is analytic at 0 ...
  have hf : AnalyticAt ℝ (fun r => mpoly (c i₀) r (ρ r)) 0 := analyticAt_mpoly_comp hc hρ
  -- ... and vanishes for all small r > 0, by the sign condition at i₀.
  have hfeq : (fun r => mpoly (c i₀) r (ρ r)) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ) :=
    mem_of_superset (Ioo_mem_nhdsGT hr₀) (fun r hr => by
      have h1 : SignType.sign (mpoly (c i₀) r (ρ r)) = 0 := by
        have := hsr r hr i₀
        rwa [hσ] at this
      exact sign_eq_zero_iff.mp h1)
  -- Hence it vanishes at 0, by continuity.
  have hf0 : mpoly (c i₀) 0 (ρ 0) = 0 := by
    have ht1 : Tendsto (fun r => mpoly (c i₀) r (ρ r)) (𝓝[>] (0 : ℝ))
        (𝓝 (mpoly (c i₀) 0 (ρ 0))) :=
      hf.continuousAt.tendsto.mono_left inf_le_left
    have ht0 : Tendsto (fun r => mpoly (c i₀) r (ρ r)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      Tendsto.congr' hfeq.symm tendsto_const_nhds
    exact tendsto_nhds_unique ht1 ht0
  -- At r = 0 the polynomial is z ↦ z ^ (d i₀), since all coefficients vanish at 0.
  have hval : mpoly (c i₀) 0 (ρ 0) = (ρ 0) ^ (d i₀) := by
    simp [mpoly, hc₀]
  have hp : (ρ 0) ^ (d i₀) = 0 := by rw [← hval]; exact hf0
  by_cases hd : d i₀ = 0
  · rw [hd, pow_zero] at hp
    exact absurd hp one_ne_zero
  · exact (pow_eq_zero_iff hd).mp hp

end Work.WilC4aAL
