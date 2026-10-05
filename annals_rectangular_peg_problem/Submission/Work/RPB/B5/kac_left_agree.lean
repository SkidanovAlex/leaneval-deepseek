import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.uproj_chart_contDiffAt_kappa

namespace Work.RPB.B5

theorem kac_left_agree (CI : Work.RPV.CurveIsotopy) {ρ₀ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ < κ) (k : ℤ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    {η : ℝ} (hη : 0 < η) (hηκ : η ≤ κ)
    (hU : ∀ σ ∈ Set.Ioo (-η) 0, ∀ u : ℝ,
      kgam CI W ρh δ k τ σ u = Work.RPV.uproj (W τ u (ρh τ u σ)))
    (hdef : ∀ σ ∈ Set.Ioo (-η) 0, ∀ u : ℝ,
      Work.RPV.ωC (deriv (fun s : ℝ => Work.RPV.uproj (W τ u (ρh τ u s))) σ)
          (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) u)
        = deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) u) :
    ∀ σ ∈ Set.Ioo (-η) 0, ∀ t : ℝ,
      kac CI W ρh δ k τ σ t = kA0 W ρh δ k τ σ
        + ((W τ t (ρh τ t σ)).1.2 - (W τ 0 (ρh τ 0 σ)).1.2) := by
  intro σ hσ t
  -- `σ ∈ (-η,0)` lies in the level interval `(-κ,κ)`
  have hσκ : σ ∈ Set.Ioo (-κ) κ :=
    ⟨by linarith [hσ.1, hηκ], by linarith [hσ.2, hκ]⟩
  -- the `σ`-slice `s ↦ W τ s (ρh τ s σ)` of the chart is `C¹²` (hence `C¹`) in `s`
  have hFcd : ContDiffOn ℝ 12 (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) Set.univ := by
    have hφcd : ContDiffOn ℝ 12 (fun s : ℝ => (((τ), (s, σ)) : ℝ × (ℝ × ℝ))) Set.univ :=
      (by fun_prop : ContDiff ℝ 12 (fun s : ℝ => (((τ), (s, σ)) : ℝ × (ℝ × ℝ)))).contDiffOn
    have hφmap : Set.MapsTo (fun s : ℝ => (((τ), (s, σ)) : ℝ × (ℝ × ℝ))) Set.univ
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := fun s _ => ⟨hτ, trivial, hσκ⟩
    have hρhcomp : ContDiffOn ℝ 12 (fun s : ℝ => ρh τ s σ) Set.univ := hρh.comp hφcd hφmap
    have hΨcd : ContDiffOn ℝ 12 (fun s : ℝ => (((τ), (s, ρh τ s σ)) : ℝ × (ℝ × ℝ))) Set.univ :=
      ContDiffOn.prodMk contDiffOn_const (ContDiffOn.prodMk contDiffOn_id hρhcomp)
    have hΨmap : Set.MapsTo (fun s : ℝ => (((τ), (s, ρh τ s σ)) : ℝ × (ℝ × ℝ))) Set.univ
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) :=
      fun s _ => ⟨hτ, trivial, hρhv τ hτ s σ hσκ⟩
    have hWcomp : ContDiffOn ℝ 12 (fun s : ℝ => W τ s (ρh τ s σ)) Set.univ :=
      hW.comp hΨcd hΨmap
    have hproj : ContDiffOn ℝ 12 (fun p : Work.RPV.PS => p.1.2) Set.univ :=
      (by fun_prop : ContDiff ℝ 12 (fun p : Work.RPV.PS => p.1.2)).contDiffOn
    exact hproj.comp hWcomp (fun x _ => trivial)
  have hFcd1 : ContDiffOn ℝ 1 (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) Set.univ :=
    hFcd.of_le (by norm_num)
  -- hence its derivative is continuous, and the fundamental theorem of calculus applies
  have hcont : Continuous (deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2)) := by
    have h := hFcd1.continuousOn_derivWithin (uniqueDiffOn_univ) (le_refl (1 : WithTop ℕ∞))
    rw [derivWithin_univ] at h
    exact continuousOn_univ.mp h
  have hdiff : ∀ x ∈ Set.uIcc (0:ℝ) t,
      DifferentiableAt ℝ (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) x := by
    intro x hx
    exact (hFcd1.differentiableOn (one_ne_zero)).differentiableAt Filter.univ_mem
  have hFTC := intervalIntegral.integral_deriv_eq_sub (a := (0:ℝ)) (b := t)
    (f := fun s : ℝ => (W τ s (ρh τ s σ)).1.2) hdiff (hcont.intervalIntegrable 0 t)
  -- on the strip `σ ∈ (-η,0)` the collar coincides with the chart, so the two `deriv`s in the
  -- flux integrand can be replaced by those of `s ↦ uproj (W τ · (ρh τ · σ))`
  have hDeriv1 : ∀ u : ℝ, deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ
      = deriv (fun s : ℝ => Work.RPV.uproj (W τ u (ρh τ u s))) σ := by
    intro u
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hσ] with s hs
    exact hU s hs u
  have hDeriv2 : ∀ u : ℝ, deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u
      = deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) u := by
    intro u
    have hfun : (fun s : ℝ => kgam CI W ρh δ k τ σ s)
        = (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) := by
      funext s; exact hU σ hσ s
    rw [hfun]
  have hIntEq : (∫ u in (0:ℝ)..t,
        Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
          (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u))
      = ∫ u in (0:ℝ)..t, deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) u := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [hDeriv1 u, hDeriv2 u]
    exact hdef σ hσ u
  -- `kac` unfolds to `kA0` plus this flux integral
  show kA0 W ρh δ k τ σ + (∫ u in (0:ℝ)..t,
        Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
          (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u))
      = kA0 W ρh δ k τ σ + ((W τ t (ρh τ t σ)).1.2 - (W τ 0 (ρh τ 0 σ)).1.2)
  rw [hIntEq, hFTC]

end Work.RPB.B5
