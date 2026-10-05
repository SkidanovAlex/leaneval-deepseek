import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPB.B3.continuousOn_signedArea_levelData
import Submission.Work.RPB.B5.deriv_signedArea_general
import Submission.Work.RPB.B5.signedArea_scale_shift
import Submission.Work.RPB.B5.chordLoop_area
import Submission.Work.RPB.B5.signedArea_parallelogram
import Submission.Work.RPB.B5.signedArea_comp_reparam
import Submission.Work.RPB.B5.area_normalised
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.pos_min_of_compact
import Submission.Work.RPB.B5.kappa_aux
import Submission.Work.RPB.B5.kappa_W_sign
import Submission.Work.RPB.B5.kappa_rho_small
import Submission.Work.RPB.B5.kappa_area_open
import Submission.Work.RPB.B5.kappa_continuous

/-!
# B5: the area law on the chord side of the `κ`-collar, near the blown-up diagonal

Given the `ρ = r²`-chart `W` of the chord annulus and a level inversion `ρh` on `(-κ, κ)`
(`K₀ (W τ t (ρh τ t σ)) + 1 = -σ`), the level curve `t ↦ uproj (W τ t (ρh τ t σ))` has signed area
`2π(1+σ)` for every `σ ∈ [-δ, 0]`, for some `δ ∈ (0, κ]`.

The only point not contained in the existing pieces (`kappa_rho_small`, `kappa_area_open`,
`kappa_continuous`) is that the level inversion of the *chord* side is *positive* there: on the
chord annulus the level function `χ τ t ρ = K₀ (W τ t ρ) + 1` equals `‖halfChord‖²` for `ρ > 0`
and is `= 0` at `ρ = 0`; `kappa_W_sign` shows it is strictly negative for `ρ ∈ (-ε, 0)` uniformly
in `(τ,t)`.  Hence, since `χ (ρh τ t σ) = -σ > 0` for `σ < 0`, `ρh τ t σ` cannot be `≤ 0` and lies
in `(0, π²/4)` for `σ` in a uniform interval `(-δ, 0)`.  There the chord description applies and
`kappa_area_open` gives the area law on the open interval; the endpoints follow from
`kappa_continuous`.
-/

open Set Filter
open scoped Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.RPB.B5

/-- A continuous function agreeing with another one on one side of a point agrees with it at the
point. -/
private lemma continuousAt_eq_of_eventuallyEq (f g : ℝ → ℝ) {x : ℝ} (l : Filter ℝ) [l.NeBot]
    (hl : l ≤ 𝓝 x) (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f =ᶠ[l] g) : f x = g x :=
  tendsto_nhds_unique ((hf.tendsto.mono_left hl).congr' h) (hg.tendsto.mono_left hl)

theorem kappa_near_area (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
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
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ κ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc (-δ) 0,
        Work.RPB.signedArea (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ)))
          = 2 * Real.pi * (1 + σ) := by
  -- the level function is negative just below the diagonal
  obtain ⟨εW, hεWpos, hWsign⟩ := kappa_W_sign CI a ρ₀ hρ₀ W hW hWchord hWper
  -- the level inversion is uniformly small near `σ = 0`
  obtain ⟨δ₁, hδ₁pos, hδ₁κ, hδ₁small⟩ :=
    kappa_rho_small ρh κ hκ hρh hρh0 hρhper (min εW (Real.pi ^ 2 / 4))
      (lt_min hεWpos (by positivity))
  -- hence it is positive there
  have hpos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ₁) 0, 0 < ρh τ t σ := by
    intro τ hτ t σ hσ
    have hsmall := hδ₁small τ hτ t σ hσ
    have hσκ : σ ∈ Set.Ioo (-κ) κ := ⟨by linarith [hδ₁κ, hσ.1], by linarith [hκ, hσ.2]⟩
    have hne : ρh τ t σ ≠ 0 := by
      intro h0
      have hA := hρhl τ hτ t σ hσκ
      have hB := hρhl τ hτ t 0 ⟨by linarith, hκ⟩
      rw [h0] at hA
      rw [hρh0 τ hτ t] at hB
      linarith [hσ.2]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exfalso
      have hlt' : |ρh τ t σ| < εW := lt_of_lt_of_le hsmall (min_le_left _ _)
      have hmem : ρh τ t σ ∈ Set.Ioo (-εW) 0 :=
        ⟨by have := (abs_lt.mp hlt').1; linarith, hlt⟩
      have h1 := hWsign τ hτ t (ρh τ t σ) hmem
      have h2 := hρhl τ hτ t σ hσκ
      linarith [hσ.2]
    · exact hgt
  -- so it lands in the interior of the chord annulus
  have hreg₁ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ₁) 0,
      ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4) := by
    intro τ hτ t σ hσ
    have hp := hpos τ hτ t σ hσ
    refine ⟨hp, ?_⟩
    have hle := lt_of_lt_of_le (hδ₁small τ hτ t σ hσ) (min_le_right _ _)
    rwa [abs_of_pos hp] at hle
  -- shrink so that `-δ` is in the *open* interval `(-κ, κ)`
  let δ : ℝ := min δ₁ (κ / 2)
  have hδpos : 0 < δ := lt_min hδ₁pos (by linarith)
  have hδ_le₁ : δ ≤ δ₁ := min_le_left _ _
  have hδ_le_κ : δ ≤ κ := le_trans hδ_le₁ hδ₁κ
  have hδ_lt_κ : δ < κ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hreg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4) :=
    fun τ hτ t σ hσ => hreg₁ τ hτ t σ ⟨by linarith [hδ_le₁, hσ.1], hσ.2⟩
  -- continuity of the area in the level parameter
  have hcont : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ))))
        (Set.Ioo (-κ) κ) :=
    kappa_continuous W ρh ρ₀ κ hκ (hW.of_le (by norm_num)) (hρh.of_le (by norm_num)) hρhv
  refine ⟨δ, hδpos, hδ_le_κ, ?_⟩
  intro τ hτ σ hσ
  rcases lt_or_eq_of_le hσ.2 with hlt0 | heq0
  · rcases lt_or_eq_of_le hσ.1 with hlt1 | heq1
    · exact kappa_area_open CI a W hκ hWchord hρhl hρhper (hρh.of_le (by norm_num))
        hδpos hδ_le_κ hreg τ hτ σ ⟨hlt1, hlt0⟩
    · rw [← heq1]
      have hc : ContinuousAt
          (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ)))) (-δ) :=
        (hcont τ hτ).continuousAt
          (isOpen_Ioo.mem_nhds ⟨by linarith [hδ_lt_κ], by linarith [hδpos]⟩)
      have hev : (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ))))
          =ᶠ[𝓝[>] (-δ)] (fun σ => 2 * Real.pi * (1 + σ)) := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds (show (-δ : ℝ) < 0 from by linarith)).filter_mono
            (nhdsWithin_le_nhds (s := Set.Ioi (-δ)))] with σ hσ' hσlt
        exact kappa_area_open CI a W hκ hWchord hρhl hρhper (hρh.of_le (by norm_num))
          hδpos hδ_le_κ hreg τ hτ σ ⟨hσ', hσlt⟩
      exact continuousAt_eq_of_eventuallyEq _ _ _ nhdsWithin_le_nhds hc (by fun_prop) hev
  · rw [heq0]
    have hc : ContinuousAt
        (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ)))) 0 :=
      (hcont τ hτ).continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, hκ⟩)
    have hev : (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ))))
        =ᶠ[𝓝[<] (0 : ℝ)] (fun σ => 2 * Real.pi * (1 + σ)) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (-δ : ℝ) < 0 from by linarith)).filter_mono
          (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))] with σ hσ' hσgt
      exact kappa_area_open CI a W hκ hWchord hρhl hρhper (hρh.of_le (by norm_num))
        hδpos hδ_le_κ hreg τ hτ σ ⟨hσgt, hσ'⟩
    exact continuousAt_eq_of_eventuallyEq _ _ _ nhdsWithin_le_nhds hc (by fun_prop) hev

end Work.RPB.B5
