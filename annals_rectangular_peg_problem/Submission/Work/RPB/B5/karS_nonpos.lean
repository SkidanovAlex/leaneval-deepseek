import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kappa_near_area
import Submission.Work.RPB.B5.kappa_tau0
import Submission.Work.RPB.B5.kshape_left_eq_chart
import Submission.Work.RPB.B5.kappaSmallAux

/-!
# B5: the signed area of the glued shape on the chord side of the collar

For `σ ≤ 0` the glued shape `kshape` of `kappaDefs` is (the reduced coordinate of) the chart point
on the *clamped* level `kclamp δ σ`.  Indeed the blend cutoff `kblf δ σ` vanishes for `σ ≤ 0`, and

* for `σ ≤ -δ/4` the correction cutoff `xfade δ σ` vanishes as well;
* for `-δ/4 < σ ≤ 0` the clamp is the identity (`|σ| ≤ δ/4 ≤ δ/2`), and the `τ = 0` correction
  `ktarg δ k σ t - uproj (W 0 t (ρh 0 t σ))` vanishes: for `σ < 0` this is the circle identity
  `kappa_tau0`, and at `σ = 0` it is the value of the vanishing jet of `kappa_tau0`.

Hence `karS` is the signed area of the level curve of the chart at the level `kclamp δ σ ∈ [-δ, 0]`,
which is `2π (1 + kclamp δ σ)` by `kappa_near_area`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem karS_nonpos (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
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
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, σ ≤ 0 →
        Work.RPB.B5.karS CI W ρh δ k τ σ = 2 * Real.pi * (1 + Work.RPB.B5.kclamp δ σ) := by
  -- the circle identity at `τ = 0` just below the diagonal
  obtain ⟨k', _hk'a, δ₁, hδ₁pos, _hδ₁κ, hmain₁, hjetU₁, _hjetA₁⟩ :=
    kappa_tau0 CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl
  -- the area law on the chord side near the diagonal
  obtain ⟨δ₂, hδ₂pos, _hδ₂κ, harea⟩ :=
    kappa_near_area CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper
  refine ⟨min (min δ₂ (4 * δ₁)) κ, lt_min (lt_min hδ₂pos (by linarith)) hκ, min_le_right _ _, ?_⟩
  intro δ hδ τ hτ σ hσ
  rw [Set.mem_Ioo] at hδ
  obtain ⟨hδpos, hδlt⟩ := hδ
  have hδδ₂ : δ < δ₂ := lt_of_lt_of_le hδlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ4 : δ < 4 * δ₁ := lt_of_lt_of_le hδlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ4' : δ / 4 < δ₁ := by linarith
  -- the glued shape agrees with the chart point on the clamped level
  have hshape : (fun t : ℝ => kshape CI W ρh δ k τ σ t)
      = fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t (kclamp δ σ))) := by
    funext t
    rcases le_or_gt σ (-(δ / 4)) with hle | hgt
    · -- far enough to the left: the correction cutoff vanishes
      have hblf : kblf δ σ = 0 := ksb_kblf_zero hδpos (by linarith)
      have hxf : xfade δ σ = 0 := xfade_zero hδpos hle
      unfold kshape knear
      rw [hblf, hxf]
      simp
    · -- in the transition region: the clamp is the identity and the correction vanishes
      have hclamp : kclamp δ σ = σ := by
        apply kclamp_of_abs_le hδpos
        rw [abs_of_nonpos hσ]
        linarith
      have hcorr : ktarg δ k σ t - Work.RPV.uproj (W 0 t (ρh 0 t (kclamp δ σ))) = 0 := by
        rw [hclamp]
        have h1 : Work.RPV.uproj (W 0 t (ρh 0 t σ))
            = (krd σ : ℂ) * Complex.exp (t * Complex.I) := by
          rcases lt_or_eq_of_le hσ with hlt | heq
          · have h := (hmain₁ t σ ⟨by linarith, hlt⟩).1
            simpa only [krd] using h
          · rw [heq]
            have hj := hjetU₁ t 0 (by norm_num)
            rw [iteratedDeriv_zero] at hj
            have h0 := sub_eq_zero.mp hj
            simpa only [krd] using h0
        rw [ktarg_of_le hδpos k (show σ ≤ δ by linarith), h1, sub_self]
      have hblf : kblf δ σ = 0 := ksb_kblf_zero hδpos (by linarith)
      unfold kshape knear
      rw [hblf, hcorr]
      simp
  rw [karS, hshape]
  refine harea τ hτ (kclamp δ σ) ⟨?_, kclamp_nonpos hδpos hσ⟩
  have h := abs_kclamp_le hδpos (σ := σ)
  rw [abs_le] at h
  linarith [h.1, hδδ₂]

end Work.RPB.B5
