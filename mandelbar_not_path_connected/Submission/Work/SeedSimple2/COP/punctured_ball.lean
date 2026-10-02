/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2/COP — L5: a punctured ball is preconnected

`NOTES_LEAD_mandelbar_rn0.md` §2, L5: `Metric.ball z₀ ε \ {z₀}` is preconnected, as the polar
image of the preconnected set `Ioo 0 ε ×ˢ univ`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

noncomputable section

namespace Work.SeedSimple2.COP

theorem isPreconnected_ball_diff_singleton (z₀ : ℂ) (ε : ℝ) :
    IsPreconnected (Metric.ball z₀ ε \ {z₀}) := by
  by_cases hε : ε ≤ 0
  · have hsub : Metric.ball z₀ ε ⊆ {z₀} := fun z hz => by
      have h1 : dist z z₀ < ε := Metric.mem_ball.mp hz
      simp only [Set.mem_singleton_iff]
      by_contra hne
      have hpos : 0 < dist z z₀ := dist_pos.mpr hne
      linarith
    have hempty : Metric.ball z₀ ε \ {z₀} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      exact hz.2 (hsub hz.1)
    rw [hempty]
    exact isPreconnected_empty
  · push_neg at hε
    have himg : Metric.ball z₀ ε \ {z₀} =
        (fun p : ℝ × ℝ => z₀ + (p.1 : ℂ) * Complex.exp (↑p.2 * Complex.I)) ''
          (Set.Ioo 0 ε ×ˢ (Set.univ : Set ℝ)) := by
      ext z
      constructor
      · rintro ⟨hz, hz0⟩
        have h1 : dist z z₀ < ε := Metric.mem_ball.mp hz
        have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz0
        have hmod : ‖z - z₀‖ < ε := by simpa [dist_eq_norm] using h1
        have hpos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr hne
        refine ⟨(‖z - z₀‖, Complex.arg (z - z₀)), ?_, ?_⟩
        · exact ⟨⟨hpos, hmod⟩, Set.mem_univ _⟩
        · show z₀ + (↑‖z - z₀‖ : ℂ) * Complex.exp (↑(Complex.arg (z - z₀)) * Complex.I) = z
          rw [Complex.norm_mul_exp_arg_mul_I (z - z₀)]
          ring
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨r, θ⟩ := p
        simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_univ, and_true] at hp
        obtain ⟨hr0, hr1⟩ := hp
        constructor
        · rw [Metric.mem_ball, dist_eq_norm]
          have h1 : ‖(r : ℂ) * Complex.exp (↑θ * Complex.I)‖ = r := by
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hr0.le]
          have h2 : z₀ + (r : ℂ) * Complex.exp (↑θ * Complex.I) - z₀
              = (r : ℂ) * Complex.exp (↑θ * Complex.I) := by ring
          rw [h2, h1]
          exact hr1
        · intro hcon
          have h2 : (r : ℂ) * Complex.exp (↑θ * Complex.I) = 0 := by
            have := congrArg (fun w => w - z₀) hcon
            simpa using this
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h (by exact_mod_cast hr0.ne')
          · exact Complex.exp_ne_zero _ h
    rw [himg]
    refine IsPreconnected.image (((convex_Ioo 0 ε).prod convex_univ).isPreconnected)
      (fun p : ℝ × ℝ => z₀ + (p.1 : ℂ) * Complex.exp (↑p.2 * Complex.I)) ?_
    exact (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const)))).continuousOn

end Work.SeedSimple2.COP

end
