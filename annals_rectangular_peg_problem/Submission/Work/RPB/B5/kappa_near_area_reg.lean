import Mathlib
import Submission.Work.RPB.B5.kappa_area_open
import Submission.Work.RPB.B5.kappa_continuous
import Submission.Work.RPB.Defs

/-!
# B5: the chord-side area law on the closed interval `[-δ, 0]`, `κ`-parametrised

`Work.RPB.B5.kappa_near_area_reg`: given the `ρ = r²`-chart `W` of the chord annulus
(`W τ t (r ^ 2) = chordSurf CI.c a τ t r` for `0 < r ≤ π/2`) and a level inversion `ρh` on the
interval `(-κ, κ)` (`K₀ (W τ t (ρh τ t σ)) + 1 = -σ`) which on the regular interval `(-δ, 0)`,
`0 < δ < κ`, takes values in `(0, π²/4)`, the level curve `t ↦ uproj (W τ t (ρh τ t σ))` has signed
area `2π (1 + σ)` for *every* `σ ∈ [-δ, 0]`.

The open interval `(-δ, 0)` is `Work.RPB.B5.kappa_area_open` (the polarization identity for
`signedArea`, the constant-length chord loop `chordLoop_area`, and reparametrisation invariance
along the curve isotopy).  The two endpoints are obtained by continuity of the signed area in the
level parameter (`Work.RPB.B5.kappa_continuous`): on `(-κ, κ)` the map
`σ ↦ signedArea (fun t => uproj (W τ t (ρh τ t σ)))` is continuous, and on the one-sided
neighbourhoods of `0` and of `-δ` it agrees with the polynomial `σ ↦ 2π (1 + σ)`.
-/

open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- A continuous function agreeing with another one on one side of a point agrees with it at the
point. -/
private lemma continuousAt_eq_of_eventuallyEq (f g : ℝ → ℝ) {x : ℝ} (l : Filter ℝ) [l.NeBot]
    (hl : l ≤ 𝓝 x) (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f =ᶠ[l] g) : f x = g x :=
  tendsto_nhds_unique ((hf.tendsto.mono_left hl).congr' h) (hg.tendsto.mono_left hl)

/-- The two endpoints `σ = 0` and `σ = -δ` of the area law, by continuity in the level
parameter. -/
private lemma kappa_endpoints (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    {ρ₀ : ℝ} {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhp : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ)
    (hreg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t 0)))
        = 2 * Real.pi * (1 + 0)) ∧
      (Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t (-δ))))
        = 2 * Real.pi * (1 + -δ)) := by
  have hcont := kappa_continuous W ρh ρ₀ κ hκ hW hρh hρhv τ hτ
  have hopen := kappa_area_open CI a W hκ hchord hρhl hρhp hρh hδ (le_of_lt hδκ) hreg τ hτ
  constructor
  · -- at `σ = 0`, from the left
    have hct : ContinuousAt
        (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ)))) 0 :=
      hcont.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, hκ⟩)
    have hev : (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ))))
        =ᶠ[𝓝[<] (0:ℝ)] (fun σ : ℝ => 2 * Real.pi * (1 + σ)) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (-δ:ℝ) < 0 from by linarith [hδ])).filter_mono
          (nhdsWithin_le_nhds (s := Set.Iio (0:ℝ)))] with σ hσ hgt
      exact hopen σ ⟨hgt, hσ⟩
    exact continuousAt_eq_of_eventuallyEq _ _ _ nhdsWithin_le_nhds hct (by fun_prop) hev
  · -- at `σ = -δ`, from the right
    have hct : ContinuousAt
        (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ)))) (-δ) :=
      hcont.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    have hev : (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ))))
        =ᶠ[𝓝[>] (-δ)] (fun σ : ℝ => 2 * Real.pi * (1 + σ)) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (-δ:ℝ) < 0 from by linarith [hδ])).filter_mono
          (nhdsWithin_le_nhds (s := Set.Ioi (-δ)))] with σ hσ hlt
      exact hopen σ ⟨hσ, hlt⟩
    exact continuousAt_eq_of_eventuallyEq _ _ _ nhdsWithin_le_nhds hct (by fun_prop) hev

theorem kappa_near_area_reg (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhp : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ)
    (hreg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc (-δ) 0,
      Work.RPB.signedArea (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ)))
        = 2 * Real.pi * (1 + σ) := by
  have _hρ₀ := hρ₀
  have _hWper := hWper
  have _hρh0 := hρh0
  intro τ hτ σ hσ
  rcases lt_or_eq_of_le hσ.1 with hlt | heq
  · rcases lt_or_eq_of_le hσ.2 with hlt2 | heq2
    · exact kappa_area_open CI a W hκ hchord hρhl hρhp hρh hδ (le_of_lt hδκ) hreg τ hτ σ
        ⟨hlt, hlt2⟩
    · rw [heq2]
      exact (kappa_endpoints CI a hW hchord hκ hρh hρhv hρhl hρhp hδ hδκ hreg hτ).1
  · rw [← heq]
    exact (kappa_endpoints CI a hW hchord hκ hρh hρhv hρhl hρhp hδ hδκ hreg hτ).2

end Work.RPB.B5
