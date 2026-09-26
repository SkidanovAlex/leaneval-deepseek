import Mathlib
import Submission.Work.LayerCont.WindowChart
import Submission.Work.LayerCont.mdifferentiableOn_highPartAt
import Submission.Work.LayerCont.WindowRev

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- **The window chart of the CKMRV layer continuation** (the case `Im τ ≈ 1`, `Im τ > 1`).

At heights `1 < s₀ < 1 + A₁` neither the low chart (`s₀ + A₁ < 1`) nor the trunc chart
(`1 < s₀ - A₁`) applies, and the pole `z = τ - 1` (height `s₀`) and the removable `S`-branch
coincidence (`z = ST⁻¹τ`, height `s₀⁻¹ < s₀`) both lie in the extended low range `(0,p]` for
`p := max (s₀ + A₁) ((s₀ - A₁)⁻¹) + 1`.  The window layer

  `layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r + layerTruncAt (Gcusp ℓ d) ℓ d p r + highPartAt (Gcusp ℓ d) p r`

is then holomorphic on a ball `B(1 + i s₀, ε')` and equals the paper's layer `paperLayer` on
`{Re τ < 1} ∩ 𝒟` — the p-independence `layerAt_eq_paperLayer` moves the split point from `1` to
`p` while `layerLowDouble_eq_layerLowAt` performs the two contour corrections.

All the geometry (the two rectangles, their edge-avoidance and the web classification) is the
one of `Work.LayerCont.ECS.exists_contour_left_data`. -/
theorem layerWindowContinuation (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : 1 < s₀) :
    ∃ A₁ ξ₁ A₂ ξ₂ p : ℝ, 0 < A₁ ∧ 0 < ξ₁ ∧ 0 ≤ A₂ ∧ 0 ≤ ξ₂ ∧ 1 ≤ p ∧
      ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
            + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
            + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
          (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
              + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
              + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) := by
  obtain ⟨ε, hεpos, A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, hA₁s, hξ₁1, hA₂inv, h4sεA, h4sεξ,
    hsep1, hsep2, hclean, hedge₀, hclass, hA₂bd, hξ₂bd, hA₂q, hξ₂q, hε4, hεa₁, hεa₂,
    rw₀, hrw₀pos, hεw, hweb⟩ := Work.LayerCont.ECS.exists_contour_left_data s₀ hs₀
  have hs₀ne : s₀ ≠ 1 := by linarith
  have hA₂pos : 0 < A₂ := (hsep2 hs₀ne).1
  have hξ₂pos : 0 < ξ₂ := (hsep2 hs₀ne).2.1
  have h4ε : 4 * ε ≤ A₂ * s₀ := (hsep2 hs₀ne).2.2.1
  have hsep : A₁ + A₂ < |s₀ - s₀⁻¹| := (hsep2 hs₀ne).2.2.2.2
  have habs : |s₀ - s₀⁻¹| = s₀ - s₀⁻¹ := by
    rw [abs_of_pos]
    nlinarith [hs₀1, inv_pos.mpr hs₀, mul_inv_cancel₀ (ne_of_gt hs₀)]
  rw [habs] at hsep
  have hsA₁ : 0 < s₀ - A₁ := by linarith
  have hsep' : s₀⁻¹ + A₂ < s₀ - A₁ := by linarith
  -- the working radius (also below the simplicity radius of the pole) and the split point
  obtain ⟨ε₁, hε₁pos, hdeg₀⟩ := Work.Asymptotics.jprime_tauSubOne_ne_zero s₀ hs₀
  set εb : ℝ := min (min ε (1 / 16)) ε₁ with hεbdef
  have hεbpos : 0 < εb := lt_min (lt_min hεpos (by norm_num)) hε₁pos
  have hεbε : εb ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεb16 : εb ≤ 1 / 16 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεbε₁ : εb ≤ ε₁ := min_le_right _ _
  have hεb1 : εb ≤ 1 := le_trans hεb16 (by norm_num)
  have hεbw : εb ≤ rw₀ := le_trans hεbε hεw
  have h4sεb : 4 * s₀ * εb ≤ A₁ := by
    calc 4 * s₀ * εb ≤ 4 * s₀ * ε := by nlinarith
      _ ≤ A₁ := h4sεA
  have h4sεbξ : 4 * s₀ * εb ≤ ξ₁ := by
    calc 4 * s₀ * εb ≤ 4 * s₀ * ε := by nlinarith
      _ ≤ ξ₁ := h4sεξ
  have h4εb : 4 * εb ≤ A₂ * s₀ := by
    calc 4 * εb ≤ 4 * ε := by linarith
      _ ≤ A₂ * s₀ := h4ε
  set p : ℝ := max (s₀ + A₁) ((s₀ - A₁)⁻¹) + 1 with hpdef
  have hp1 : 1 ≤ p := by
    have h0 : (0 : ℝ) ≤ s₀ + A₁ := by linarith
    have h1 : (0 : ℝ) ≤ max (s₀ + A₁) ((s₀ - A₁)⁻¹) := le_trans h0 (le_max_left _ _)
    rw [hpdef]
    linarith
  have hp_hi : s₀ + A₁ ≤ p := by
    have h := le_max_left (s₀ + A₁) ((s₀ - A₁)⁻¹)
    rw [hpdef]
    linarith
  have hp_ge : max (s₀ + A₁) ((s₀ - A₁)⁻¹) + 1 ≤ p := le_of_eq hpdef.symm
  -- ### the three cleanliness families
  have hcleanTail : ∀ (s : ℝ) (hs : 0 < s), p ≤ s →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    clean_axis_tail_of_web hs₀ hA₁s hεbpos hεb16 hεbw h4sεb hp_ge hweb
  have hcleanAxisLow : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (s₀ - A₁) (s₀ + A₁)
        ∪ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsE τ hτ => clean_axis_retained_of_web hs₀ hA₁ hεbpos hεb16 hεbw h4sεb h4εb hweb
      s hs (fun hmem => hsE.2 (Or.inl hmem)) (fun hmem => hsE.2 (Or.inr hmem)) τ hτ
  -- ### the edge cleanliness of the two detour rectangles
  have hedge₁ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
        ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hεbε) (not_lt.mpr hge)
  have hedge₂ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = s₀⁻¹ - A₂ ∨ v = s₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ s₀⁻¹ - A₂ < v ∧ v < s₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hc))
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hεbε) (not_lt.mpr hge)
  -- ### the geometry of the two rectangles, for `τ.re < 1`
  have hI₂low : s₀⁻¹ + A₂ < 1 := sInvinv_add_lt_one hs₀1 hA₂bd hA₂q
  have hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 →
      -ξ₁ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        s₀ - A₁ < (Work.Asymptotics.tauSubOne τ).im ∧
        (Work.Asymptotics.tauSubOne τ).im < s₀ + A₁ := by
    intro τ hτ hτre
    obtain ⟨h1, h2⟩ := Work.Asymptotics.abs_re_im_sub_lt hs₀ hεbpos hεb1 hτ
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    have hre : (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 := tauSubOne_re' τ
    have him : (Work.Asymptotics.tauSubOne τ).im = τ.im := tauSubOne_im' τ
    rw [hre, him]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0 := by
    intro τ hτ hτre
    exact hdeg₀ τ (lt_of_lt_of_le hτ hεbε₁) hτre
  have hcl₁ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z →
          (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ) := by
    intro τ hτ hτre γ z hz
    by_cases h : z = γ • τ
    · right
      rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inl hz) h with h' | h'
      · exact h'
      · exfalso
        have hpos : 0 < (Work.Asymptotics.tauCoinc τ).re :=
          Work.Asymptotics.tauCoinc_re_pos τ hτre
        have hneg : z.re ≤ 0 := hz.2.1
        rw [h'] at hneg
        linarith
    · exact Or.inl h
  have hcl₂ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z → z ≠ γ • τ := by
    intro τ hτ hτre γ z hz hzeq
    have hτim_lo : s₀ - A₁ < τ.im := by
      have h2lo := (abs_lt.mp
        (Work.Asymptotics.abs_re_im_sub_lt hs₀ hεbpos hεb1 hτ).2).1
      have h3 : 3 * s₀ * εb ≤ A₁ := by linarith
      linarith
    rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inr hz) hzeq with h' | h'
    · have hzim : z.im = τ.im := by rw [h', tauSubOne_im']
      linarith [hz.2.2, hzim]
    · have hpos := Work.Asymptotics.tauCoinc_re_pos τ hτre
      rw [← h'] at hpos
      linarith [hz.2.1]
  refine ⟨A₁, ξ₁, A₂, ξ₂, p, hA₁, hξ₁, hA₂, hξ₂, hp1, εb, hεbpos, fun r => ?_,
    fun τ r hτ hτre hD => ?_⟩
  · -- ### holomorphy
    have h1 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      mdifferentiableOn_layerLowDouble ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos
        hsA₁ hp_hi hsep' hA₂inv hedge₁ hedge₂ hcleanAxisLow
    have h2 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      mdifferentiableOn_layerTruncAt ℓ d hd (p := p) hp1 hs₀ hεbpos r hcleanTail
    have h3 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      (mdifferentiableOn_highPartAt ℓ d hd p r).mono (Set.subset_univ _)
    exact (h1.add h2).add h3
  · -- ### the agreement with `paperLayer`
    have hcleanAll : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
      fun t ht _ => clean_axis_of_web_re_lt_one (ε := ε) hs₀ hεw hweb t ht τ
        (lt_of_lt_of_le hτ hεbε) hτre
    have hconv : layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ = layerLowAt ℓ d p r τ :=
      layerLowDouble_eq_layerLowAt ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos hsA₁ hp_hi
        hsep' hA₂inv hcl₁ hpole hdeg hcl₂ hτ hτre hcleanAll
    -- the tail integrability of the cusp-subtracted integrand on `[1,∞)`, from the cusp
    -- expansion on `𝒟`
    obtain ⟨C₂, M, T₀, hC₂pos, hMnn, hT₀nn, hbnd⟩ :=
      Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd (K := {τ}) isCompact_singleton
        (by rintro x rfl; exact hD)
    have hdom : ∀ t : ℝ, 1 ≤ t →
        ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Work.Asymptotics.gaussWeight r t‖
        ≤ (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
            * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
      intro t ht
      have hb := hbnd τ t (Set.mem_singleton τ) ht
      have hexp : Real.exp (-(Real.pi * (t - T₀)))
          = Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * T₀) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [norm_mul, Work.Asymptotics.norm_gaussWeight]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
            * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ (C₂ * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
              * Real.exp (-(Real.pi * r ^ 2 * t)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
        _ = (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
              * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
            rw [hexp]; ring
    have hdomint : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
        * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))))
        (Set.Ici (1 : ℝ)) := by
      have hbase : IntegrableOn (fun t : ℝ => (1 + t) ^ M
          * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) (Set.Ici (1 : ℝ)) :=
        TailIntegrable hMnn (by positivity)
      have h1 : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) (Set.Ici (1 : ℝ)) :=
        hbase.const_mul (C₂ * Real.exp (Real.pi * T₀))
      refine h1.congr_fun ?_ measurableSet_Ici
      intro t _
      simp only
      rw [show Real.exp (-((Real.pi * (1 + r ^ 2)) * t))
          = Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) by
        rw [← Real.exp_add]; congr 1; ring]
    have hIntG : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) := by
      show Integrable _ (volume.restrict (Set.Ici (1 : ℝ)))
      refine Integrable.mono' (g := fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t))))) ?_ ?_ ?_
      · rw [← IntegrableOn]; exact hdomint
      · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
          (by unfold Work.Asymptotics.Aexp; fun_prop)).mul
          (by unfold Work.Asymptotics.gaussWeight; fun_prop)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact hdom t ht
    have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
      layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 τ
        (fun t ht _ => clean_axis_of_web_re_lt_one (ε := ε) hs₀ hεw hweb t ht τ
          (lt_of_lt_of_le hτ hεbε) hτre) hIntG
    rw [hconv]
    exact hpaper

/-- **The window chart of the CKMRV layer continuation, reversed interval order** (`Im τ < 1`).

For `s₀ < 1` the pole interval `I₁ = (s₀-A₁, s₀+A₁)` lies *below* the coincidence interval
`I₂ = (s₀⁻¹-A₂, s₀⁻¹+A₂)`, so with the split point `p` above both the layer

  `layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r + layerTruncAt (Gcusp ℓ d) ℓ d p r + highPartAt (Gcusp ℓ d) p r`

is holomorphic on a ball `B(1 + i s₀, ε')` and equals `paperLayer` on `{Re τ < 1} ∩ 𝒟`.  The
proof is the mirror of `Work.LayerCont.layerWindowContinuation`, using
`Work.LayerCont.mdifferentiableOn_layerLowDouble_rev` /
`Work.LayerCont.layerLowDouble_eq_layerLowAt_rev`; the only place where the reversed order shows
up in the *geometry* is the exclusion of the pole `τ - 1` from the coincidence rectangle, where
the upper height bound `τ.im < s₀ + A₁ < s₀⁻¹ - A₂` is used. -/
theorem layerWindowContinuation_rev (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1) :
    ∃ A₁ ξ₁ A₂ ξ₂ p : ℝ, 0 < A₁ ∧ 0 < ξ₁ ∧ 0 ≤ A₂ ∧ 0 ≤ ξ₂ ∧ 1 ≤ p ∧
      ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
            + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
            + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
          (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
              + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
              + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) := by
  obtain ⟨ε, hεpos, A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, hA₁s, hξ₁1, hA₂inv, h4sεA, h4sεξ,
    hsep1, hsep2, hclean, hedge₀, hclass, hA₂bd, hξ₂bd, hA₂q, hξ₂q, hε4, hεa₁, hεa₂,
    rw₀, hrw₀pos, hεw, hweb⟩ := Work.LayerCont.ECS.exists_contour_left_data s₀ hs₀
  have hs₀ne : s₀ ≠ 1 := by linarith
  have hA₂pos : 0 < A₂ := (hsep2 hs₀ne).1
  have hξ₂pos : 0 < ξ₂ := (hsep2 hs₀ne).2.1
  have h4ε : 4 * ε ≤ A₂ * s₀ := (hsep2 hs₀ne).2.2.1
  have hsep : A₁ + A₂ < |s₀ - s₀⁻¹| := (hsep2 hs₀ne).2.2.2.2
  have habs : |s₀ - s₀⁻¹| = s₀⁻¹ - s₀ := by
    rw [abs_of_nonpos]
    · ring
    · have h1 : 0 < s₀⁻¹ := inv_pos.mpr hs₀
      nlinarith [hs₀1, h1, mul_inv_cancel₀ (ne_of_gt hs₀)]
  rw [habs] at hsep
  have hsA₁ : 0 < s₀ - A₁ := by linarith
  have hsep' : s₀ + A₁ < s₀⁻¹ - A₂ := by linarith
  -- the working radius (also below the simplicity radius of the pole) and the split point
  obtain ⟨ε₁, hε₁pos, hdeg₀⟩ := Work.Asymptotics.jprime_tauSubOne_ne_zero s₀ hs₀
  set εb : ℝ := min (min ε (1 / 16)) ε₁ with hεbdef
  have hεbpos : 0 < εb := lt_min (lt_min hεpos (by norm_num)) hε₁pos
  have hεbε : εb ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεb16 : εb ≤ 1 / 16 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεbε₁ : εb ≤ ε₁ := min_le_right _ _
  have hεb1 : εb ≤ 1 := le_trans hεb16 (by norm_num)
  have hεbw : εb ≤ rw₀ := le_trans hεbε hεw
  have h4sεb : 4 * s₀ * εb ≤ A₁ := by
    calc 4 * s₀ * εb ≤ 4 * s₀ * ε := by nlinarith
      _ ≤ A₁ := h4sεA
  have h4sεbξ : 4 * s₀ * εb ≤ ξ₁ := by
    calc 4 * s₀ * εb ≤ 4 * s₀ * ε := by nlinarith
      _ ≤ ξ₁ := h4sεξ
  have h4εb : 4 * εb ≤ A₂ * s₀ := by
    calc 4 * εb ≤ 4 * ε := by linarith
      _ ≤ A₂ * s₀ := h4ε
  set p : ℝ := max (max (s₀ + A₁) (s₀⁻¹ + A₂)) ((s₀ - A₁)⁻¹) + 1 with hpdef
  have hp1 : 1 ≤ p := by
    have h0 : (0 : ℝ) ≤ s₀ + A₁ := by linarith
    have h1 : (0 : ℝ) ≤ max (max (s₀ + A₁) (s₀⁻¹ + A₂)) ((s₀ - A₁)⁻¹) :=
      le_trans (le_trans h0 (le_max_left _ _)) (le_max_left _ _)
    rw [hpdef]
    linarith
  have hp_hi₁ : s₀ + A₁ ≤ p := by
    have h := le_max_left (s₀ + A₁) (s₀⁻¹ + A₂)
    have h2 := le_max_left (max (s₀ + A₁) (s₀⁻¹ + A₂)) ((s₀ - A₁)⁻¹)
    rw [hpdef]
    linarith
  have hp_hi₂ : s₀⁻¹ + A₂ ≤ p := by
    have h := le_max_right (s₀ + A₁) (s₀⁻¹ + A₂)
    have h2 := le_max_left (max (s₀ + A₁) (s₀⁻¹ + A₂)) ((s₀ - A₁)⁻¹)
    rw [hpdef]
    linarith
  have hp_ge : max (s₀ + A₁) ((s₀ - A₁)⁻¹) + 1 ≤ p := by
    have h2 := le_max_left (max (s₀ + A₁) (s₀⁻¹ + A₂)) ((s₀ - A₁)⁻¹)
    have h3 := le_max_right (max (s₀ + A₁) (s₀⁻¹ + A₂)) ((s₀ - A₁)⁻¹)
    have h4 := le_max_left (s₀ + A₁) (s₀⁻¹ + A₂)
    have h5 : max (s₀ + A₁) ((s₀ - A₁)⁻¹) ≤ max (max (s₀ + A₁) (s₀⁻¹ + A₂)) ((s₀ - A₁)⁻¹) :=
      max_le (le_trans h4 h2) h3
    rw [hpdef]
    linarith
  -- ### the three cleanliness families
  have hcleanTail : ∀ (s : ℝ) (hs : 0 < s), p ≤ s →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    clean_axis_tail_of_web hs₀ hA₁s hεbpos hεb16 hεbw h4sεb hp_ge hweb
  have hcleanAxisLow : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (s₀ - A₁) (s₀ + A₁)
        ∪ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsE τ hτ => clean_axis_retained_of_web hs₀ hA₁ hεbpos hεb16 hεbw h4sεb h4εb hweb
      s hs (fun hmem => hsE.2 (Or.inl hmem)) (fun hmem => hsE.2 (Or.inr hmem)) τ hτ
  -- ### the edge cleanliness of the two detour rectangles
  have hedge₁ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
        ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hεbε) (not_lt.mpr hge)
  have hedge₂ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = s₀⁻¹ - A₂ ∨ v = s₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ s₀⁻¹ - A₂ < v ∧ v < s₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hc))
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hεbε) (not_lt.mpr hge)
  -- ### the geometry of the two rectangles, for `τ.re < 1`
  have hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 →
      -ξ₁ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        s₀ - A₁ < (Work.Asymptotics.tauSubOne τ).im ∧
        (Work.Asymptotics.tauSubOne τ).im < s₀ + A₁ := by
    intro τ hτ hτre
    obtain ⟨h1, h2⟩ := Work.Asymptotics.abs_re_im_sub_lt hs₀ hεbpos hεb1 hτ
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    have hre : (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 := tauSubOne_re' τ
    have him : (Work.Asymptotics.tauSubOne τ).im = τ.im := tauSubOne_im' τ
    rw [hre, him]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0 := by
    intro τ hτ hτre
    exact hdeg₀ τ (lt_of_lt_of_le hτ hεbε₁) hτre
  have hcl₁ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z →
          (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ) := by
    intro τ hτ hτre γ z hz
    by_cases h : z = γ • τ
    · right
      rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inl hz) h with h' | h'
      · exact h'
      · exfalso
        have hpos : 0 < (Work.Asymptotics.tauCoinc τ).re :=
          Work.Asymptotics.tauCoinc_re_pos τ hτre
        have hneg : z.re ≤ 0 := hz.2.1
        rw [h'] at hneg
        linarith
    · exact Or.inl h
  have hcl₂ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z → z ≠ γ • τ := by
    intro τ hτ hτre γ z hz hzeq
    have hτim_hi : τ.im < s₀ + A₁ := by
      have h2hi := (abs_lt.mp
        (Work.Asymptotics.abs_re_im_sub_lt hs₀ hεbpos hεb1 hτ).2).2
      have h3 : 3 * s₀ * εb ≤ A₁ := by linarith
      linarith
    rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inr hz) hzeq with h' | h'
    · have hzim : z.im = τ.im := by rw [h', tauSubOne_im']
      linarith [hz.2.2, hzim, hsep']
    · have hpos := Work.Asymptotics.tauCoinc_re_pos τ hτre
      rw [← h'] at hpos
      linarith [hz.2.1]
  refine ⟨A₁, ξ₁, A₂, ξ₂, p, hA₁, hξ₁, hA₂, hξ₂, hp1, εb, hεbpos, fun r => ?_,
    fun τ r hτ hτre hD => ?_⟩
  · -- ### holomorphy
    have h1 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      mdifferentiableOn_layerLowDouble_rev ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos
        hsA₁ hp_hi₁ hp_hi₂ hsep' hA₂inv hedge₁ hedge₂ hcleanAxisLow
    have h2 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      mdifferentiableOn_layerTruncAt ℓ d hd (p := p) hp1 hs₀ hεbpos r hcleanTail
    have h3 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) :=
      (mdifferentiableOn_highPartAt ℓ d hd p r).mono (Set.subset_univ _)
    exact (h1.add h2).add h3
  · -- ### the agreement with `paperLayer`
    have hcleanAll : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
      fun t ht _ => clean_axis_of_web_re_lt_one (ε := ε) hs₀ hεw hweb t ht τ
        (lt_of_lt_of_le hτ hεbε) hτre
    have hconv : layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ = layerLowAt ℓ d p r τ :=
      layerLowDouble_eq_layerLowAt_rev ℓ d hd (r := r) hs₀ hA₁ hξ₁ hA₂pos hξ₂pos hεbpos hsA₁
        hp_hi₁ hp_hi₂ hsep' hA₂inv hcl₁ hpole hdeg hcl₂ hτ hτre hcleanAll
    obtain ⟨C₂, M, T₀, hC₂pos, hMnn, hT₀nn, hbnd⟩ :=
      Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd (K := {τ}) isCompact_singleton
        (by rintro x rfl; exact hD)
    have hdom : ∀ t : ℝ, 1 ≤ t →
        ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Work.Asymptotics.gaussWeight r t‖
        ≤ (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
            * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
      intro t ht
      have hb := hbnd τ t (Set.mem_singleton τ) ht
      have hexp : Real.exp (-(Real.pi * (t - T₀)))
          = Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * T₀) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [norm_mul, Work.Asymptotics.norm_gaussWeight]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
            * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ (C₂ * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
              * Real.exp (-(Real.pi * r ^ 2 * t)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
        _ = (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
              * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
            rw [hexp]; ring
    have hdomint : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
        * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))))
        (Set.Ici (1 : ℝ)) := by
      have hbase : IntegrableOn (fun t : ℝ => (1 + t) ^ M
          * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) (Set.Ici (1 : ℝ)) :=
        TailIntegrable hMnn (by positivity)
      have h1 : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) (Set.Ici (1 : ℝ)) :=
        hbase.const_mul (C₂ * Real.exp (Real.pi * T₀))
      refine h1.congr_fun ?_ measurableSet_Ici
      intro t _
      simp only
      rw [show Real.exp (-((Real.pi * (1 + r ^ 2)) * t))
          = Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) by
        rw [← Real.exp_add]; congr 1; ring]
    have hIntG : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) := by
      show Integrable _ (volume.restrict (Set.Ici (1 : ℝ)))
      refine Integrable.mono' (g := fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t))))) ?_ ?_ ?_
      · rw [← IntegrableOn]; exact hdomint
      · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
          (by unfold Work.Asymptotics.Aexp; fun_prop)).mul
          (by unfold Work.Asymptotics.gaussWeight; fun_prop)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact hdom t ht
    have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
      layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 τ
        (fun t ht _ => clean_axis_of_web_re_lt_one (ε := ε) hs₀ hεw hweb t ht τ
          (lt_of_lt_of_le hτ hεbε) hτre) hIntG
    rw [hconv]
    exact hpaper

/-- **The window chart for every height `≠ 1`.** -/
theorem layerWindowContinuation_ne_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ : ℝ} (hs₀ : 0 < s₀) (hne : s₀ ≠ 1) :
    ∃ A₁ ξ₁ A₂ ξ₂ p : ℝ, 0 < A₁ ∧ 0 < ξ₁ ∧ 0 ≤ A₂ ∧ 0 ≤ ξ₂ ∧ 1 ≤ p ∧
      ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
            + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
            + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
          (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
              + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
              + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact layerWindowContinuation_rev ℓ d hd hs₀ hlt
  · exact layerWindowContinuation ℓ d hd hs₀ hgt

/-- **The window chart at the cusp height `1`** (`τ = 1 + i`).

At height `1` the pole `z = τ - 1` and the removable `S`-branch coincidence `ST⁻¹τ` coalesce (both
at `z = i`), so the geometry degenerates: `A₂ = ξ₂ = 0` and the single interval
`I₁ = (1-A₁, 1+A₁)` carries both.  The chart is therefore the single-interval object
`layerLowOne ℓ d p 1 A₁ ξ₁ r` (over the extended contour `(0,p]`, with the pole detour and the
residue correction `resCorr`) together with the clean tail `layerTruncAt` and the closed-form
`highPartAt`; it is holomorphic on a ball around `1 + i` and agrees with `paperLayer` on
`{Re τ < 1} ∩ 𝒟`.

The only place where the coalescence is visible is the cleanliness of the retained contour
`(0,p] \ I₁`: the second branch of the web (`τ.im = s⁻¹`) puts `s` in `I₁` by the estimate
`|τ.im⁻¹ - 1| = |1 - τ.im|/τ.im < 3ε/(13/16) ≤ (4ε)·(12/13) < A₁`. -/
theorem layerWindowContinuation_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ A₁ ξ₁ p : ℝ, 0 < A₁ ∧ 0 < ξ₁ ∧ 1 ≤ p ∧
      ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => layerLowOne ℓ d p 1 A₁ ξ₁ r τ
            + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
            + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
          (Metric.ball (Work.Asymptotics.onePlusI 1 one_pos) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI 1 one_pos) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            layerLowOne ℓ d p 1 A₁ ξ₁ r τ
              + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
              + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) := by
  have h1 : (0 : ℝ) < 1 := one_pos
  obtain ⟨ε, hεpos, A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, hA₁s, hξ₁1, hA₂inv, h4sεA, h4sεξ,
    hsep1, hsep2, hclean, hedge₀, hclass, hA₂bd, hξ₂bd, hA₂q, hξ₂q, hε4, hεa₁, hεa₂,
    rw₀, hrw₀pos, hεw, hweb⟩ := Work.LayerCont.ECS.exists_contour_left_data 1 h1
  obtain ⟨hA₂0, -⟩ := hsep1 rfl
  obtain ⟨ε₁, hε₁pos, hdeg₀⟩ := Work.Asymptotics.jprime_tauSubOne_ne_zero 1 h1
  set εb : ℝ := min (min ε (1 / 16)) ε₁ with hεbdef
  have hεbpos : 0 < εb := lt_min (lt_min hεpos (by norm_num)) hε₁pos
  have hεbε : εb ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεb16 : εb ≤ 1 / 16 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεbε₁ : εb ≤ ε₁ := min_le_right _ _
  have hεb1 : εb ≤ 1 := le_trans hεb16 (by norm_num)
  have hεbw : εb ≤ rw₀ := le_trans hεbε hεw
  have h4sεb : 4 * 1 * εb ≤ A₁ := by
    calc 4 * 1 * εb ≤ 4 * 1 * ε := by nlinarith
      _ ≤ A₁ := h4sεA
  have h4sεbξ : 4 * 1 * εb ≤ ξ₁ := by
    calc 4 * 1 * εb ≤ 4 * 1 * ε := by nlinarith
      _ ≤ ξ₁ := h4sεξ
  set p : ℝ := max (1 + A₁) ((1 - A₁)⁻¹) + 1 with hpdef
  have hp1 : 1 ≤ p := by
    have h0 : (0 : ℝ) ≤ 1 + A₁ := by linarith
    have h1' : (0 : ℝ) ≤ max (1 + A₁) ((1 - A₁)⁻¹) := le_trans h0 (le_max_left _ _)
    rw [hpdef]
    linarith
  have hp_hi : 1 + A₁ ≤ p := by
    have h := le_max_left (1 + A₁) ((1 - A₁)⁻¹)
    rw [hpdef]
    linarith
  have hp_ge : max (1 + A₁) ((1 - A₁)⁻¹) + 1 ≤ p := le_of_eq hpdef.symm
  -- ### the cleanliness of the tail `[p,∞)`
  have hcleanTail : ∀ (s : ℝ) (hs : 0 < s), p ≤ s →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    clean_axis_tail_of_web h1 hA₁s hεbpos hεb16 hεbw h4sεb hp_ge hweb
  -- ### the cleanliness of the retained contour `(0,p] \ I₁`
  have hcleanAxisOne : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A₁) (1 + A₁) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
    intro s hs hsE τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hd : dist (σ • Work.Kernels.imagAxis s hs) (Work.Asymptotics.onePlusI 1 h1) < rw₀ := by
      rw [hσ]
      exact lt_of_lt_of_le hτ hεbw
    obtain ⟨hre, him⟩ := hweb σ s hs hd
    rw [hσ] at hre him
    obtain ⟨h2lo, h2hi⟩ := abs_lt.mp
      (Work.Asymptotics.abs_re_im_sub_lt h1 hεbpos hεb1 hτ).2
    refine absurd ?_ hsE.2
    rcases him with him | him
    · rw [Set.mem_Ioo, ← him]
      have h3 : 3 * 1 * εb ≤ A₁ := by linarith
      exact ⟨by linarith, by linarith⟩
    · have hs_eq : s = τ.im⁻¹ := by rw [him, inv_inv]
      rw [Set.mem_Ioo, hs_eq]
      have hτim_pos : 0 < τ.im := τ.im_pos
      have hτim_gt : (13 : ℝ) / 16 < τ.im := by nlinarith [h2lo, hεb16]
      have hnum : |1 - τ.im| < 3 * εb := by
        rw [abs_sub_comm]
        simpa using abs_lt.mpr ⟨h2lo, h2hi⟩
      have hkey : |τ.im⁻¹ - 1| < A₁ := by
        have hdiv : τ.im⁻¹ - 1 = (1 - τ.im) / τ.im := by
          field_simp
        rw [hdiv, abs_div, abs_of_pos hτim_pos]
        rw [div_lt_iff₀ hτim_pos]
        have h3 : 4 * εb ≤ A₁ := by linarith
        nlinarith [hnum.le, hτim_gt, h3, hA₁, hτim_pos]
      obtain ⟨h1', h2'⟩ := abs_lt.mp hkey
      exact ⟨by linarith, by linarith⟩
  -- ### the edge cleanliness of the detour rectangle
  have hedge : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = 1 - A₁ ∨ v = 1 + A₁))
        ∨ (u = -ξ₁ ∧ 1 - A₁ < v ∧ v < 1 + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI 1 h1) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hεbε) (not_lt.mpr hge)
  -- ### the geometry of the pole rectangle
  have hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < εb →
      τ.re < 1 →
      -ξ₁ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        1 - A₁ < (Work.Asymptotics.tauSubOne τ).im ∧
        (Work.Asymptotics.tauSubOne τ).im < 1 + A₁ := by
    intro τ hτ hτre
    obtain ⟨h1', h2'⟩ := Work.Asymptotics.abs_re_im_sub_lt h1 hεbpos hεb1 hτ
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1'
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2'
    have hre : (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 := tauSubOne_re' τ
    have him : (Work.Asymptotics.tauSubOne τ).im = τ.im := tauSubOne_im' τ
    rw [hre, him]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < εb →
      τ.re < 1 → Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0 := by
    intro τ hτ hτre
    exact hdeg₀ τ (lt_of_lt_of_le hτ hεbε₁) hτre
  have hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect 1 A₁ ξ₁ z →
          (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ) := by
    intro τ hτ hτre γ z hz
    by_cases h : z = γ • τ
    · right
      rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inl hz) h with h' | h'
      · exact h'
      · exfalso
        have hpos : 0 < (Work.Asymptotics.tauCoinc τ).re :=
          Work.Asymptotics.tauCoinc_re_pos τ hτre
        have hneg : z.re ≤ 0 := hz.2.1
        rw [h'] at hneg
        linarith
    · exact Or.inl h
  refine ⟨A₁, ξ₁, p, hA₁, hξ₁, hp1, εb, hεbpos, fun r => ?_, fun τ r hτ hτre hD => ?_⟩
  · have h1' : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerLowOne ℓ d p 1 A₁ ξ₁ r τ)
        (Metric.ball (Work.Asymptotics.onePlusI 1 h1) εb) :=
      mdifferentiableOn_layerLowOne ℓ d hd (r := r) h1 hA₁ hξ₁ hεbpos (by linarith) hp_hi hedge
        (fun s hs hsE τ hτ' => hcleanAxisOne s hs hsE τ hτ')
    have h2 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI 1 h1) εb) :=
      mdifferentiableOn_layerTruncAt ℓ d hd (p := p) hp1 h1 hεbpos r hcleanTail
    have h3 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI 1 h1) εb) :=
      (mdifferentiableOn_highPartAt ℓ d hd p r).mono (Set.subset_univ _)
    exact (h1'.add h2).add h3
  · have hconv : layerLowOne ℓ d p 1 A₁ ξ₁ r τ = layerLowAt ℓ d p r τ :=
      layerLowOne_eq_layerLowAt ℓ d hd (r := r) h1 hA₁ hξ₁ hεbpos (by linarith) hp_hi hcl hpole
        hdeg (fun s hs hsE τ' hτ' _ => hcleanAxisOne s hs hsE τ' hτ')
        τ r (lt_of_lt_of_le hτ le_rfl) hτre
    obtain ⟨C₂, M, T₀, hC₂pos, hMnn, hT₀nn, hbnd⟩ :=
      Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd (K := {τ}) isCompact_singleton
        (by rintro x rfl; exact hD)
    have hdom : ∀ t : ℝ, 1 ≤ t →
        ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Work.Asymptotics.gaussWeight r t‖
        ≤ (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
            * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
      intro t ht
      have hb := hbnd τ t (Set.mem_singleton τ) ht
      have hexp : Real.exp (-(Real.pi * (t - T₀)))
          = Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * T₀) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [norm_mul, Work.Asymptotics.norm_gaussWeight]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
            * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ (C₂ * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
              * Real.exp (-(Real.pi * r ^ 2 * t)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
        _ = (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
              * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
            rw [hexp]; ring
    have hdomint : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
        * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))))
        (Set.Ici (1 : ℝ)) := by
      have hbase : IntegrableOn (fun t : ℝ => (1 + t) ^ M
          * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) (Set.Ici (1 : ℝ)) :=
        TailIntegrable hMnn (by positivity)
      have h1' : IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) (Set.Ici (1 : ℝ)) :=
        hbase.const_mul (C₂ * Real.exp (Real.pi * T₀))
      refine h1'.congr_fun ?_ measurableSet_Ici
      intro t _
      simp only
      rw [show Real.exp (-((Real.pi * (1 + r ^ 2)) * t))
          = Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) by
        rw [← Real.exp_add]; congr 1; ring]
    have hIntG : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) := by
      show Integrable _ (volume.restrict (Set.Ici (1 : ℝ)))
      refine Integrable.mono' (g := fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t))))) ?_ ?_ ?_
      · rw [← IntegrableOn]; exact hdomint
      · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
          (by unfold Work.Asymptotics.Aexp; fun_prop)).mul
          (by unfold Work.Asymptotics.gaussWeight; fun_prop)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact hdom t ht
    have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
      layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 τ
        (fun t ht _ => clean_axis_of_web_re_lt_one (ε := ε) h1 hεw hweb t ht τ
          (lt_of_lt_of_le hτ hεbε) hτre) hIntG
    rw [hconv]
    exact hpaper

end Work.LayerCont
