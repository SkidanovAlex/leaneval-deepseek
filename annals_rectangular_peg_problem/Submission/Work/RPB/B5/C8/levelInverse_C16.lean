import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPA3.contDiff_param_intervalIntegral
import Submission.Work.RPB.B3.existsRadiusOpen
import Submission.Work.RPB.B3.EsTauAux
import Submission.Work.RPB.B3.esTauJetMatch
import Submission.Work.RPB.B3.esTauMultiLin
import Submission.Work.RPB.B3.esTauReflectCoeffs
import Submission.Work.RPB.B3.EvenTaylorSteps
import Submission.Work.RPB.B5.rho_range_kappa
import Submission.Work.RPB.B3.UniformInverseAux
import Submission.Work.RPB.B3.positivityExpansion
import Submission.Work.RPB.B3.boundsOnCompactBox
import Submission.Work.RPB.B5.slabInverseContDiffOn
import Submission.Work.RPB.B5.chordSurf_rhoChart_full
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chartLev_eq_sq_mul_hc
import Submission.Work.RPB.B5.slabDerivBounds
import Submission.Work.RPB.B5.slabMonoExistsUnique
import Submission.Work.RPB.B5.C8.slabInverseContDiffOn_C16

open scoped ContDiff

namespace Work.RPB.B5.C8

/-- Uniform smallness: a function `φ τ σ` vanishing on `σ = 0` and continuous on a compact box is
uniformly small for `σ` near `0` (from below). -/
private lemma exists_small_uniform {φ : ℝ → ℝ → ℝ} {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-c) c))
    (h0 : ∀ τ ∈ Set.Icc (0:ℝ) 1, φ τ 0 = 0) :
    ∃ s : ℝ, 0 < s ∧ s ≤ c ∧
      ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-s) 0, |φ τ σ| < η := by
  have hKc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-c) c) :=
    isCompact_Icc.prod isCompact_Icc
  have hUC : UniformContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-c) c) :=
    hKc.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδpos, hδ⟩ := hUC η hη
  refine ⟨min c δ, lt_min hc hδpos, min_le_left _ _, ?_⟩
  intro τ hτ σ hσ
  have hσc : σ ∈ Set.Icc (-c) c :=
    ⟨by linarith [hσ.1, min_le_left c δ], by linarith [hσ.2, lt_min hc hδpos]⟩
  have h0c : (0:ℝ) ∈ Set.Icc (-c) c := ⟨by linarith, by linarith⟩
  have hdist : dist (τ, σ) (τ, (0:ℝ)) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, max_eq_right (abs_nonneg σ)]
    have hσlt : |σ| < min c δ := by
      rw [abs_lt]
      exact ⟨hσ.1, by linarith [hσ.2, lt_min hc hδpos]⟩
    exact lt_of_lt_of_le hσlt (min_le_right c δ)
  have hres := hδ (τ, σ) ⟨hτ, hσc⟩ (τ, (0:ℝ)) ⟨hτ, h0c⟩ hdist
  rw [Real.dist_eq, h0 τ hτ, sub_zero] at hres
  exact hres

theorem levelInverse_C16 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s ≤ ε ∧ s ≤ κ ∧ ∃ rh : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 16 (fun z : ℝ × ℝ => rh z.1 z.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ioo (-s) s) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, rh τ 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Ioo (-s) 0, rh τ σ = ρh τ 0 σ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Ioo (-s) 0, 0 < rh τ σ ∧ rh τ σ < ε) := by
  classical
  -- ## 1. the smooth even half chord and its squared modulus
  obtain ⟨hc, hc_sm, hc_even, hc_per, hc_zero, hc_half⟩ :=
    Work.RPB.B5.halfChordSmooth CI.c CI.smooth CI.per
  set E : ℝ → ℝ → ℝ → ℝ := fun τ t r =>
    (hc τ t r).re * (hc τ t r).re + (hc τ t r).im * (hc τ t r).im with hEdef
  have hE_sm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => E z.1 z.2.1 z.2.2) := by
    rw [hEdef]
    have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
    have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
    fun_prop
  have hE_even : ∀ τ t r, E τ t (-r) = E τ t r := by
    intro τ t r
    simp only [hEdef]
    rw [hc_even τ t r]
  have hE_per : ∀ τ t r, E τ (t + 2 * Real.pi) r = E τ t r := by
    intro τ t r
    simp only [hEdef]
    rw [hc_per τ t r]
  -- its even `ρ`-chart, jointly `C¹⁶`
  obtain ⟨G, hG_sm, hG_val, hG_per⟩ := Work.RPB.B5.evenChart E 16 hE_sm hE_even hE_per
  -- ## 2. the smooth level function `S = ρ * G`
  set S : ℝ → ℝ → ℝ → ℝ := fun τ t ρ => ρ * G τ t ρ with hSdef
  have hS_sm : ContDiff ℝ 16 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) := by
    rw [hSdef]; fun_prop
  have hS8 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) :=
    hS_sm.of_le (by norm_num)
  have hS_per : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ := by
    intro τ t ρ; simp only [hSdef]; rw [hG_per τ t ρ]
  have hS0 : ∀ τ t, S τ t 0 = 0 := by
    intro τ t; simp only [hSdef]; ring
  have hG0 : ∀ τ t, G τ t 0 = E τ t 0 := by
    intro τ t
    have h := hG_val τ t 0 (le_refl (0:ℝ))
    simpa using h
  have hSδ : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, 0 < deriv (fun ρ => S τ t ρ) 0 := by
    intro τ hτ t
    have hGdiff : DifferentiableAt ℝ (fun ρ : ℝ => G τ t ρ) 0 := by
      have h := hG_sm.comp (f := fun ρ : ℝ => (τ, ((t:ℝ), ρ))) (by fun_prop)
      exact (h.differentiable (by norm_num)).differentiableAt
    have hd : deriv (fun ρ : ℝ => S τ t ρ) 0 = G τ t 0 := by
      simp only [hSdef]
      change deriv (id * fun ρ : ℝ => G τ t ρ) 0 = G τ t 0
      rw [deriv_mul differentiableAt_id hGdiff]
      simp
    rw [hd, hG0 τ t]
    have hE0 : E τ t 0 = ‖deriv (CI.c τ) t‖ ^ 2 := by
      simp only [hEdef]
      rw [hc_zero τ t, Complex.sq_norm, Complex.normSq_apply]
    rw [hE0]
    exact pow_pos (norm_pos_iff.mpr (CI.imm τ hτ t)) 2
  -- ## 3. `S` coincides with the level function of the chart on `(0, π²/4)`
  have hchordIoo : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, ∀ r ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r :=
    fun τ hτ t r hr => hWchord τ hτ t r ⟨hr.1, le_of_lt hr.2⟩
  have hSF : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (0:ℝ) (Real.pi ^ 2 / 4),
      S τ t ρ = Work.RPV.K0 (W τ t ρ) + 1 := by
    intro τ hτ t ρ hρ
    have hρ' : ρ ∈ Set.Ioo (0:ℝ) ((Real.pi / 2) ^ 2) := by
      refine ⟨hρ.1, ?_⟩
      have : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
      rw [this]; exact hρ.2
    have hcl := Work.RPB.B5.chartLev_eq_sq_mul_hc (CI := CI) (a := a) (W := W)
      hchordIoo hc_half hτ t ρ hρ'
    have hgv := hG_val τ t ρ hρ.1.le
    have hEeq : E τ t (Real.sqrt ρ) = ‖hc τ t (Real.sqrt ρ)‖ ^ 2 := by
      simp only [hEdef]
      rw [Complex.sq_norm, Complex.normSq_apply]
    change ρ * G τ t ρ = Work.RPV.K0 (W τ t ρ) + 1
    rw [hgv, hEeq]
    exact hcl.symm
  -- ## 4. uniform derivative bounds and strict monotonicity of the slices of `S`
  obtain ⟨ε₀, hε₀, δ, hδ, M, hM, hbound⟩ :=
    Work.RPB.B5.slabDerivBounds S hS8 hS_per hSδ
  have hderivfn : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀) ε₀,
      δ ≤ deriv (fun ρ => S τ t ρ) ρ :=
    fun τ hτ t ρ hρ => (hbound τ hτ t ρ hρ).1
  have hMono := Work.RPB.B5.slabMonoExistsUnique S hS8 hS0 δ ε₀ hδ hε₀ hderivfn
  -- shrink the interval so that it lies inside `(0, π²/4)`, where `S` is the chord chart
  set ε₀' : ℝ := min ε₀ (Real.pi ^ 2 / 4) with hε₀'def
  have hε₀'pos : 0 < ε₀' := lt_min hε₀ (by positivity)
  have hε₀'leε₀ : ε₀' ≤ ε₀ := min_le_left _ _
  have hε₀'lepi : ε₀' ≤ Real.pi ^ 2 / 4 := min_le_right _ _
  have hderivfn' : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀') ε₀',
      δ ≤ deriv (fun ρ => S τ t ρ) ρ := fun τ hτ t ρ hρ =>
    hderivfn τ hτ t ρ ⟨by linarith [hρ.1, hε₀'leε₀], by linarith [hρ.2, hε₀'leε₀]⟩
  have hMono' := Work.RPB.B5.slabMonoExistsUnique S hS8 hS0 δ ε₀' hδ hε₀'pos hderivfn'
  have hcover' : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-(δ * ε₀')) (δ * ε₀'),
      ∃! ρ, ρ ∈ Set.Ioo (-ε₀') ε₀' ∧ S τ t ρ = σ :=
    fun τ hτ t σ hσ => (hMono' τ hτ t).2.2.2 σ (abs_lt.mpr hσ)
  have hderivne : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε₀') ε₀',
      deriv (fun ρ => S τ t ρ) ρ ≠ 0 := by
    intro τ hτ t ρ hρ
    have h := hderivfn' τ hτ t ρ (Set.Ioo_subset_Icc_self hρ)
    intro hc; rw [hc] at h; linarith
  have hinj : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t,
      Set.InjOn (fun ρ => S τ t ρ) (Set.Ioo (-ε₀') ε₀') :=
    fun τ hτ t => (hMono' τ hτ t).1.injOn.mono (Set.Ioo_subset_Icc_self)
  -- ## 5. the `C¹⁶` level inverse on the slab
  have hift : ContDiffOn ℝ 16
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B3.inverseR S ε₀' z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-(δ * ε₀')) (δ * ε₀')) := by
    exact slabInverseContDiffOn_C16 S hS_sm ε₀' δ hε₀'pos hδ hderivne hcover'
  -- ## 6. radii
  obtain ⟨ε_r, hε_r_pos, hε_r_leκ, hε_r_range⟩ :=
    Work.RPB.B5.rho_range_kappa CI a ha ρ₀ hρ₀ W ρh hκ hW hWchord hρh hρh0 hρhv hρhl
  -- the slice `σ ↦ ρh τ 0 σ` is continuous on the compact box `[0,1] × [-κ/2, κ/2]`
  have hφcont : ContinuousOn (fun p : ℝ × ℝ => ρh p.1 0 p.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-(κ/2)) (κ/2)) := by
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, ((0:ℝ), p.2)))
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-(κ/2)) (κ/2))
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := by
      rintro ⟨τ, σ⟩ ⟨hτ, hσ⟩
      obtain ⟨hσ1, hσ2⟩ := Set.mem_Icc.mp hσ
      exact ⟨hτ, trivial, Set.mem_Ioo.mpr ⟨by linarith [hσ1, hκ], by linarith [hσ2, hκ]⟩⟩
    have hcomp := hρh.continuousOn.comp
      (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => (p.1, ((0:ℝ), p.2)))
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-(κ/2)) (κ/2))) hmap
    simpa only [Function.comp_def] using hcomp
  have hφ0 : ∀ τ ∈ Set.Icc (0:ℝ) 1, (fun p : ℝ × ℝ => ρh p.1 0 p.2) (τ, 0) = 0 :=
    fun τ hτ => hρh0 τ hτ 0
  obtain ⟨s₁, hs₁pos, hs₁κ, hs₁⟩ :=
    exists_small_uniform (φ := fun τ σ => ρh τ 0 σ) (by linarith [hκ]) hε₀'pos hφcont hφ0
  obtain ⟨s₂, hs₂pos, hs₂κ, hs₂⟩ :=
    exists_small_uniform (φ := fun τ σ => ρh τ 0 σ) (by linarith [hκ]) hε hφcont hφ0
  set r : ℝ := δ * ε₀' with hrdef
  have hrpos : 0 < r := mul_pos hδ hε₀'pos
  -- ## 7. the radius `s` and the inverse `rh`
  set s : ℝ := min ε (min κ (min r (min ε_r (min s₁ s₂)))) with hsdef
  have hs : 0 < s := by
    rw [hsdef]
    exact lt_min hε (lt_min hκ (lt_min hrpos (lt_min hε_r_pos (lt_min hs₁pos hs₂pos))))
  have hsε : s ≤ ε := by rw [hsdef]; exact min_le_left _ _
  have hsκ : s ≤ κ := by
    rw [hsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hsr : s ≤ r := by
    rw [hsdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hsεr : s ≤ ε_r := by
    rw [hsdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hs₁' : s ≤ s₁ := by
    rw [hsdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hs₂' : s ≤ s₂ := by
    rw [hsdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  set rh : ℝ → ℝ → ℝ := fun τ σ => Work.RPB.B3.inverseR S ε₀' τ 0 (-σ) with hrhdef
  have hrh_sm : ContDiffOn ℝ 16 (fun z : ℝ × ℝ => rh z.1 z.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioo (-s) s) := by
    have hinner : ContDiffOn ℝ 16 (fun z : ℝ × ℝ => (z.1, ((0:ℝ), -z.2)))
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioo (-s) s) := by fun_prop
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.1, ((0:ℝ), -z.2)))
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Ioo (-s) s)
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-r) r) := by
      rintro ⟨τ, σ⟩ ⟨hτ, hσ⟩
      obtain ⟨hσ1, hσ2⟩ := Set.mem_Ioo.mp hσ
      exact ⟨hτ, trivial, Set.mem_Ioo.mpr ⟨by linarith [hσ2, hsr], by linarith [hσ1, hsr]⟩⟩
    have h := hift.comp hinner hmap
    simpa only [Function.comp_def, hrhdef] using h
  have hrh0 : ∀ τ ∈ Set.Icc (0:ℝ) 1, rh τ 0 = 0 := by
    intro τ hτ
    simp only [hrhdef, neg_zero]
    refine Work.RPB.B3.inverseR_eq ⟨by linarith [hε₀'pos], by linarith [hε₀'pos]⟩
      (hS0 τ 0) ?_
    intro ρ' hρ' hS'
    refine hinj τ hτ 0 hρ' ⟨by linarith [hε₀'pos], by linarith [hε₀'pos]⟩ ?_
    show S τ 0 ρ' = S τ 0 0
    rw [hS', hS0 τ 0]
  have hrh_eq : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-s) 0, rh τ σ = ρh τ 0 σ := by
    intro τ hτ σ hσ
    have hσκ : σ ∈ Set.Ioo (-κ) κ := ⟨by linarith [hσ.1, hsκ], by linarith [hσ.2, hκ]⟩
    have hσr : σ ∈ Set.Ioo (-r) r := ⟨by linarith [hσ.1, hsr], by linarith [hσ.2, hrpos]⟩
    have hnegr : (-σ) ∈ Set.Ioo (-(δ * ε₀')) (δ * ε₀') := by
      rw [hrdef] at hσr
      exact ⟨by linarith [hσr.2], by linarith [hσr.1]⟩
    obtain ⟨hspec_mem, hspec_val⟩ :=
      Work.RPB.B3.inverseR_spec ((hcover' τ hτ 0 (-σ) hnegr).exists)
    have hrhpos : 0 < Work.RPB.B3.inverseR S ε₀' τ 0 (-σ) := by
      by_contra hcon
      rw [not_lt] at hcon
      have hm := (hMono' τ hτ 0).1.monotoneOn (Set.Ioo_subset_Icc_self hspec_mem)
        (show (0:ℝ) ∈ Set.Icc (-ε₀') ε₀' from ⟨by linarith [hε₀'pos], by linarith [hε₀'pos]⟩)
        hcon
      rw [hspec_val, hS0 τ 0] at hm
      linarith [hσ.2]
    have hρhpos : 0 < ρh τ 0 σ :=
      (hε_r_range τ hτ 0 σ ⟨by linarith [hσ.1, hsεr], hσ.2⟩).1
    have hρhlt : ρh τ 0 σ < ε₀' := by
      have h := hs₁ τ hτ σ ⟨by linarith [hσ.1, hs₁'], hσ.2⟩
      rwa [abs_of_pos hρhpos] at h
    have hmem1 : Work.RPB.B3.inverseR S ε₀' τ 0 (-σ) ∈ Set.Ioo (0:ℝ) (Real.pi ^ 2 / 4) :=
      ⟨hrhpos, lt_of_lt_of_le hspec_mem.2 hε₀'lepi⟩
    have hmem2 : ρh τ 0 σ ∈ Set.Ioo (0:ℝ) (Real.pi ^ 2 / 4) :=
      ⟨hρhpos, lt_of_lt_of_le hρhlt hε₀'lepi⟩
    have hS1 := hSF τ hτ 0 (Work.RPB.B3.inverseR S ε₀' τ 0 (-σ)) hmem1
    have hS2 := hSF τ hτ 0 (ρh τ 0 σ) hmem2
    have hF1 : Work.RPV.K0 (W τ 0 (Work.RPB.B3.inverseR S ε₀' τ 0 (-σ))) + 1 = -σ :=
      hS1.symm.trans hspec_val
    have hF2 : Work.RPV.K0 (W τ 0 (ρh τ 0 σ)) + 1 = -σ := hρhl τ hτ 0 σ hσκ
    have key : S τ 0 (Work.RPB.B3.inverseR S ε₀' τ 0 (-σ)) = S τ 0 (ρh τ 0 σ) := by
      rw [hS1, hS2, hF1, hF2]
    have := hinj τ hτ 0 hspec_mem ⟨by linarith [hρhpos], by linarith [hρhlt]⟩ key
    simpa only [hrhdef] using this
  have hrh_bnd : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-s) 0,
      0 < rh τ σ ∧ rh τ σ < ε := by
    intro τ hτ σ hσ
    rw [hrh_eq τ hτ σ hσ]
    have hpos : 0 < ρh τ 0 σ :=
      (hε_r_range τ hτ 0 σ ⟨by linarith [hσ.1, hsεr], hσ.2⟩).1
    refine ⟨hpos, ?_⟩
    have h := hs₂ τ hτ σ ⟨by linarith [hσ.1, hs₂'], hσ.2⟩
    rwa [abs_of_pos hpos] at h
  exact ⟨s, hs, hsε, hsκ, rh, hrh_sm, hrh0, hrh_eq, hrh_bnd⟩

end Work.RPB.B5.C8
