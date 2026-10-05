import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kappa_near_area
import Submission.Work.RPB.B5.kappa_tau0
import Submission.Work.RPB.B5.kappa_collar_area_emb
import Submission.Work.RPB.B5.kappa_shape_geom_small
import Submission.Work.RPB.B5.kdiagM_signedArea
import Submission.Work.RPB.B5.karS_nonpos
import Submission.Work.RPB.B5.karS_pos_of_nonneg

/-!
# B5: the area law and the non-vanishing of `karS` for **every** level `σ : ℝ`

This file proves `Work.RPB.B5.kappa_collar_area_all`: for small enough `δ` and every level
`σ : ℝ`, every `τ ∈ [0,1]` and every `k : ℤ`,

* the normalised collar `kgam CI W ρh δ k τ σ` has signed area `2π (1 + σ)` (this holds for
  *all* real `σ`, including `σ < -1`, where `kg` is negative and `kdiagM (kg)` reverses the
  orientation), and
* `karS CI W ρh δ k τ σ ≠ 0`.

This is the `σ`-unrestricted strengthening of `kappa_collar_area_emb` (which covers `σ ≥ 0`),
needed because the `x ≤ -√2` branch of the Lagrangian family evaluates the collar at every
`σ`, and because `kg = 2π(1+σ)/karS` is only the correct normalisation when `karS` does not
vanish.

## Structure of the proof

`kgam` is *by definition* the real-linear image `kdiagM (kg) ∘ kshape` of the glued shape and
`kg = 2π(1+σ)/karS`, where `karS = signedArea (kshape)`.  Since `kdiagM_signedArea` scales the
signed area by `kg` for *every* real `kg`, the area law is pure algebra:

`signedArea (kgam) = kg · karS = (2π(1+σ)/karS) · karS = 2π(1+σ)`   (as `karS ≠ 0`).

Hence *both* conjuncts of the statement reduce to the single fact `karS ≠ 0` on all of `ℝ`:
`karS` is `= 2π (1 + kclamp δ σ)` for `σ ≤ 0` (`karS_nonpos`, via `kappa_near_area` and
`kshape_left_eq_chart`) and positive for `σ ≥ 0` (`karS_pos_of_nonneg`, via
`kappa_shape_geom_small` near the diagonal and `ksb_karS_far` far away).  The threshold `δ₀`
is the minimum of the two thresholds, further capped by `1` so that `1 + kclamp δ σ > 0` for
`σ ≤ 0`.
-/

set_option autoImplicit false

namespace Work.RPB.B5

theorem kappa_collar_area_all (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ,
        Work.RPB.signedArea (Work.RPB.B5.kgam CI W ρh δ k τ σ) = 2 * Real.pi * (1 + σ) ∧
        Work.RPB.B5.karS CI W ρh δ k τ σ ≠ 0 := by
  -- the two one-sided non-vanishing statements for `karS`
  obtain ⟨δ₁, hδ₁pos, hδ₁κ, hnonpos⟩ :=
    karS_nonpos CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper k
  obtain ⟨δ₂, hδ₂pos, hδ₂κ, hpos⟩ :=
    karS_pos_of_nonneg CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl
      hρhper k
  refine ⟨min δ₁ (min δ₂ 1), lt_min hδ₁pos (lt_min hδ₂pos one_pos), ?_, ?_⟩
  · -- `δ₀ ≤ κ`
    calc min δ₁ (min δ₂ 1) ≤ δ₁ := min_le_left _ _
      _ ≤ κ := hδ₁κ
  · intro δ hδ τ hτ σ
    rw [Set.mem_Ioo] at hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    have hδ₁ : δ < δ₁ := lt_of_lt_of_le hδlt (min_le_left _ _)
    have hδ₂ : δ < δ₂ := lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδ1 : δ < 1 := lt_of_lt_of_le hδlt (le_trans (min_le_right _ _) (min_le_right _ _))
    -- `karS ≠ 0`, uniformly in the sign of `σ`
    have hkarS : karS CI W ρh δ k τ σ ≠ 0 := by
      rcases le_total σ 0 with hσ | hσ
      · -- `σ ≤ 0`: the glued shape is the clamped chart family, of area `2π (1 + kclamp δ σ)`
        rw [hnonpos δ ⟨hδpos, hδ₁⟩ τ hτ σ hσ]
        have hb := abs_kclamp_le (δ := δ) (σ := σ) hδpos
        rw [abs_le] at hb
        have h1 : (0 : ℝ) < 1 + kclamp δ σ := by linarith [hb.1, hδ1]
        exact ne_of_gt (by nlinarith [Real.pi_pos, h1])
      · -- `σ ≥ 0`
        exact ne_of_gt (hpos δ ⟨hδpos, hδ₂⟩ τ hτ σ hσ)
    refine ⟨?_, hkarS⟩
    -- the area law is the algebra `kdiagM_signedArea` + the definition of `kg`
    change Work.RPB.signedArea
        (fun t : ℝ => kdiagM (kg CI W ρh δ k τ σ) (kshape CI W ρh δ k τ σ t))
      = 2 * Real.pi * (1 + σ)
    rw [kdiagM_signedArea]
    rw [show Work.RPB.signedArea (fun t : ℝ => kshape CI W ρh δ k τ σ t)
          = karS CI W ρh δ k τ σ from rfl]
    rw [show kg CI W ρh δ k τ σ = 2 * Real.pi * (1 + σ) / karS CI W ρh δ k τ σ from rfl]
    exact div_mul_cancel₀ _ hkarS

end Work.RPB.B5
