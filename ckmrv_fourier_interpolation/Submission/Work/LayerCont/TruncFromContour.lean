import Mathlib
import Submission.Work.LayerCont.TruncHolomorphy
import Submission.Work.LayerCont.TruncAgreement
import Submission.Work.Asymptotics.contourLeftAux
import Submission.Work.Asymptotics.jprime_tauSubOne_ne_zero

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter

/-- Real part of `imagAxis` (local copy: the module must not import the `CleanBounded` chain). -/
lemma imagAxis_re' (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).re = 0 := by
  rw [← UpperHalfPlane.coe_re]
  simp [Work.Kernels.imagAxis]

/-- Imaginary part of `imagAxis`. -/
lemma imagAxis_im' (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  rw [← UpperHalfPlane.coe_im]
  simp [Work.Kernels.imagAxis]

/-- Real part of `tauSubOne`. -/
lemma tauSubOne_re' (τ : UpperHalfPlane) : (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 := by
  have h := congrArg Complex.re (Work.Asymptotics.tauSubOne_coe τ)
  simpa [UpperHalfPlane.coe_re] using h

/-- **The trunc-piece agreement, with the geometry of `exists_contour_left` fed in.**

The exact mirror of `Work.LayerCont.layerLowCont_eq_layerLow_of_contourLeft` for the truncated
piece `[1,∞)`: the pole height `s₀ > 1` is swept by the retained set `E = Ici 1 \ Ioo (s₀-A₁)(s₀+A₁)`,
the location/simplicity of the pole and the cleanliness of the retained axis are derived from the
same geometry, and `Work.LayerCont.TruncAgreement` gives the identity with the paper's trunc
layer on `{Re τ < 1} ∩ 𝒟`. -/
theorem layerTruncCont_eq_layerTrunc_of_contourLeft (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ A₁ ξ₁ A₂ ξ₂ ε : ℝ} (hs₀ : 0 < s₀)
    (hA₁ : 0 < A₁) (hA₁s : A₁ < s₀) (hξ₁ : 0 < ξ₁) (hA₂ : 0 ≤ A₂) (hξ₂ : 0 ≤ ξ₂)
    (hε : 0 < ε) (h4sεA : 4 * s₀ * ε ≤ A₁) (h4sεξ : 4 * s₀ * ε ≤ ξ₁)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∉ Set.Ioo (s₀ - A₁) (s₀ + A₁) →
      t ∉ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hclass : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        (Work.Asymptotics.leftRect s₀ A₁ ξ₁ z ∨ Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z) →
        z = γ • τ → z = Work.Asymptotics.tauSubOne τ ∨ z = Work.Asymptotics.tauCoinc τ)
    (hhi : 1 < s₀ - A₁) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' → τ.re < 1 →
        τ ∈ Work.Asymptotics.DomainD →
        layerTruncCont ℓ d s₀ A₁ ξ₁ r τ
          = Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r := by
  obtain ⟨ε₁, hε₁pos, hdeg₀⟩ := Work.Asymptotics.jprime_tauSubOne_ne_zero s₀ hs₀
  set ε' : ℝ := min ε (min ε₁ 1) with hε'def
  have hε'pos : 0 < ε' := lt_min hε (lt_min hε₁pos one_pos)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'ε₁ : ε' ≤ ε₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε'1 : ε' ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have h4sε' : 4 * s₀ * ε' ≤ A₁ := le_trans (mul_le_mul_of_nonneg_left hε'ε (by positivity)) h4sεA
  have h4sξ' : 4 * s₀ * ε' ≤ ξ₁ := le_trans (mul_le_mul_of_nonneg_left hε'ε (by positivity)) h4sεξ
  -- ### cleanliness of the retained trunc axis `E`
  have hcleanAxis : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ Set.Ici (1 : ℝ) \ Set.Ioo (s₀ - A₁) (s₀ + A₁) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' → τ.re < 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
    intro s hs hsE τ' hτ' hre' hjeq
    by_cases hsI₂ : s ∈ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂)
    · obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
      have hz : Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ (Work.Kernels.imagAxis s hs) := by
        rw [Work.Asymptotics.leftRect, imagAxis_re' s hs, imagAxis_im' s hs]
        exact ⟨by linarith, le_rfl, hsI₂.1.le, hsI₂.2.le⟩
      have hz' : Work.Kernels.imagAxis s hs = σ⁻¹ • τ' := (smul_eq_iff_eq_inv_smul σ).mp hσ
      rcases hclass τ' (lt_of_lt_of_le hτ' hε'ε) σ⁻¹ (Work.Kernels.imagAxis s hs)
        (Or.inr hz) hz' with h' | h'
      · have hre : (Work.Kernels.imagAxis s hs).re = (Work.Asymptotics.tauSubOne τ').re := by
          rw [h']
        rw [imagAxis_re' s hs, tauSubOne_re' τ'] at hre
        linarith
      · have hpos : 0 < (Work.Asymptotics.tauCoinc τ').re :=
          Work.Asymptotics.tauCoinc_re_pos τ' hre'
        rw [← h', imagAxis_re' s hs] at hpos
        exact absurd hpos (lt_irrefl 0)
    · exact hclean s hs hsE.2 hsI₂ τ' (lt_of_lt_of_le hτ' hε'ε) hjeq
  -- ### the location of the pole
  have hpole : ∀ τ' : UpperHalfPlane, dist τ' (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
      τ'.re < 1 →
      -ξ₁ < (Work.Asymptotics.tauSubOne τ').re ∧ (Work.Asymptotics.tauSubOne τ').re < 0 ∧
        s₀ - A₁ < (Work.Asymptotics.tauSubOne τ').im ∧
        (Work.Asymptotics.tauSubOne τ').im < s₀ + A₁ := by
    intro τ' hτ' _
    obtain ⟨h1, h2⟩ := Work.Asymptotics.abs_re_im_sub_lt hs₀ hε'pos hε'1 hτ'
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    have hre : (Work.Asymptotics.tauSubOne τ').re = τ'.re - 1 := tauSubOne_re' τ'
    have him : (Work.Asymptotics.tauSubOne τ').im = τ'.im := by
      have h := congrArg Complex.im (Work.Asymptotics.tauSubOne_coe τ')
      simpa using h
    rw [hre, him]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  -- ### the pole is simple
  have hdeg : ∀ τ' : UpperHalfPlane, dist τ' (Work.Asymptotics.onePlusI s₀ hs₀) < ε' → τ'.re < 1 →
      Work.Residues.jprime (Work.Asymptotics.tauSubOne τ') ≠ 0 :=
    fun τ' hτ' hre' => hdeg₀ τ' (lt_of_lt_of_le hτ' hε'ε₁) hre'
  -- ### the rectangle classification for the pole rectangle
  have hcl : ∀ τ' : UpperHalfPlane, dist τ' (Work.Asymptotics.onePlusI s₀ hs₀) < ε' → τ'.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z →
          (z ≠ γ • τ' ∨ z = Work.Asymptotics.tauSubOne τ') := by
    intro τ' hτ' hre' γ z hz
    by_cases h : z = γ • τ'
    · right
      rcases hclass τ' (lt_of_lt_of_le hτ' hε'ε) γ z (Or.inl hz) h with h' | h'
      · exact h'
      · exfalso
        have hpos : 0 < (Work.Asymptotics.tauCoinc τ').re :=
          Work.Asymptotics.tauCoinc_re_pos τ' hre'
        have hneg : z.re ≤ 0 := hz.2.1
        rw [h'] at hneg
        linarith
    · exact Or.inl h
  refine ⟨ε', hε'pos, hε'ε, fun τ r hτ hre hD => ?_⟩
  rw [layerTruncCont, layerTruncPiece]
  exact TruncAgreement ℓ d hd hs₀ hA₁ hξ₁ hε'pos hhi hcl hpole hdeg hcleanAxis τ r hτ hre hD

/-- **The trunc-piece holomorphy, with the geometry of `exists_contour_left` fed in.**

The mirror of `Work.LayerCont.mdifferentiableOn_layerLowCont_of_contourLeft`: the retained set
`E = Ici 1 \ Ioo (s₀-A₁)(s₀+A₁)` is clean for every `τ` of the ball as soon as the *second*
removed interval `I₂ = (s₀⁻¹-A₂, s₀⁻¹+A₂)` (the S-branch height) lies below `1`
(`hI₂low`), because `s ∈ E` forces `1 ≤ s`.  Then `Work.LayerCont.TruncHolomorphy` gives the
holomorphy of `layerTruncCont` on the ball. -/
theorem mdifferentiableOn_layerTruncCont_of_contourLeft (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ A₁ ξ₁ A₂ ξ₂ ε : ℝ} (hs₀ : 0 < s₀)
    (hA₁ : 0 < A₁) (hA₁s : A₁ < s₀) (hξ₁ : 0 < ξ₁) (hA₂ : 0 ≤ A₂) (hξ₂ : 0 ≤ ξ₂)
    (hε : 0 < ε) (hI₂low : s₀⁻¹ + A₂ < 1)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∉ Set.Ioo (s₀ - A₁) (s₀ + A₁) →
      t ∉ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hedge₀ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
        ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)
        ∨ (-ξ₂ < u ∧ u < 0 ∧ (v = s₀⁻¹ - A₂ ∨ v = s₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ s₀⁻¹ - A₂ < v ∧ v < s₀⁻¹ + A₂)) →
      ε ≤ dist (γ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀))
    (hhi : 1 < s₀ - A₁) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ∀ r : ℝ,
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerTruncCont ℓ d s₀ A₁ ξ₁ r τ)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε') := by
  set ε' : ℝ := min ε 1 with hε'def
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'ε : ε' ≤ ε := min_le_left _ _
  -- the retained trunc contour is clean for every `τ` of the ball
  have hcleanAxis : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ Set.Ici (1 : ℝ) \ Set.Ioo (s₀ - A₁) (s₀ + A₁) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
    intro s hs hsE τ hτ
    exact hclean s hs hsE.2
      (fun hmem => absurd hmem.2 (not_lt.mpr (le_trans hI₂low.le (Set.mem_Ici.mp hsE.1))))
      τ (lt_of_lt_of_le hτ hε'ε)
  -- the edges of the detour rectangle are clean
  have hedge : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = s₀ - A₁ ∨ v = s₀ + A₁))
        ∨ (u = -ξ₁ ∧ s₀ - A₁ < v ∧ v < s₀ + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI s₀ hs₀) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hε'ε) (not_lt.mpr hge)
  exact ⟨ε', hε'pos, hε'ε, fun r =>
    TruncHolomorphy ℓ d hd hs₀ hA₁ hξ₁ hε'pos hhi hedge hcleanAxis⟩

end Work.LayerCont
