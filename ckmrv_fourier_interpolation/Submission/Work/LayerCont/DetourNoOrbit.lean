import Mathlib
import Submission.Work.Asymptotics.detourLeftC_eq_interval_of_clean

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.Asymptotics

/-- **The left detour equals the replaced interval integral, pole-free case, without the
restriction `τ.re < 1`.**  This is `Work.Asymptotics.detourLeftC_eq_interval_of_clean` with the
`τ.re < 1` restriction dropped everywhere (the proof uses it only to feed the `hcl` hypothesis):
it is the form needed on the *right* of the line `Re τ = 1`, where the rectangle contains no
`SL(2,ℤ)`-orbit point of `τ` other than *removable* coincidences which are excluded by `hcl`. -/
theorem detourLeftC_eq_interval_of_noOrbit (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {r c A ξ ε t₀ : ℝ} (ht₀ : 0 < t₀) (hε : 0 < ε) (hA : 0 < A) (hξ : 0 < ξ) (hcA : 0 < c - A)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect c A ξ z → z ≠ γ • τ) :
    ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
      Work.Asymptotics.detourLeftC ℓ d r c A ξ τ
        = ∫ v in Set.Ioo (c - A) (c + A), Work.Asymptotics.edgeV ℓ d r τ 0 v := by
  intro τ hτball
  by_cases hd : d = 8 ∨ d = 24
  · have hcl' : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect c A ξ z → (z ≠ γ • τ ∨ z = tauSubOne τ) :=
      fun γ z hz => Or.inl (hcl τ hτball γ z hz)
    have hcleanish := dlcc_clean τ c A ξ hcA hcl'
    have hPoleNotMem : poleℂ τ ∉ leftRectℂ c A ξ :=
      poleℂ_notMem_leftRectℂ τ c A ξ hcA (fun γ z hz => hcl τ hτball γ z hz)
    have hcontRect : ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ) := by
      have h := dlcc_continuousOn ℓ d hd r τ c A ξ hcA hcleanish
      rwa [Set.sdiff_singleton_eq_self hPoleNotMem] at h
    set z₀ : ℂ := ((-ξ / 2 : ℝ) : ℂ) + ((c : ℝ) : ℂ) * Complex.I with hz₀
    have hz₀re : z₀.re = -ξ / 2 := by rw [hz₀]; simp
    have hz₀im : z₀.im = c := by rw [hz₀]; simp
    have hz₀open : z₀ ∈ openLeftRectℂ c A ξ := by
      simp only [openLeftRectℂ, Set.mem_ofPred_eq]
      exact ⟨by rw [hz₀re]; linarith, by rw [hz₀re]; linarith,
        by rw [hz₀im]; linarith, by rw [hz₀im]; linarith⟩
    have hmem₀ : leftRectℂ c A ξ ∈ 𝓝 z₀ :=
      Filter.mem_of_superset ((isOpen_openLeftRectℂ' c A ξ).mem_nhds hz₀open)
        (openLeftRectℂ_subset_leftRectℂ c A ξ)
    have hcont : ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ \ {z₀}) :=
      hcontRect.mono Set.sdiff_subset
    have hhol : ∀ z : ℂ, (-ξ) < z.re → z.re < 0 → c - A < z.im → z.im < c + A → z ≠ z₀ →
        DifferentiableAt ℂ (kerForm ℓ d r τ) z := by
      intro z h1 h2 h3 h4 _
      refine dlcc_differentiableAt ℓ d hd r τ c A ξ hcA hcleanish z ⟨h1, h2, h3, h4⟩ ?_
      intro hpe
      exact hPoleNotMem (hpe ▸ openLeftRectℂ_subset_leftRectℂ c A ξ ⟨h1, h2, h3, h4⟩)
    have hres : Filter.Tendsto (fun z : ℂ => (z - z₀) * kerForm ℓ d r τ z)
        (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
      have h1 : Filter.Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
        have h : Filter.Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 (z₀ - z₀)) :=
          (continuous_id.sub continuous_const).tendsto z₀
        simpa using h
      have h2 : Filter.Tendsto (fun z : ℂ => kerForm ℓ d r τ z) (𝓝 z₀)
          (𝓝 (kerForm ℓ d r τ z₀)) := hcontRect.continuousAt hmem₀
      have h3 := h1.mul h2
      have h3' : Filter.Tendsto (fun z : ℂ => (z - z₀) * kerForm ℓ d r τ z) (𝓝 z₀)
          (𝓝 (0 * kerForm ℓ d r τ z₀)) := h3
      rw [zero_mul] at h3'
      exact h3'.mono_left nhdsWithin_le_nhds
    have hrect := rectInt_eq_residue (kerForm ℓ d r τ) z₀ 0 (-ξ) 0 (c - A) (c + A)
      (by rw [hz₀re]; linarith) (by rw [hz₀re]; linarith)
      (by rw [hz₀im]; linarith) (by rw [hz₀im]; linarith) hcont hhol hres
    rw [mul_zero] at hrect
    rw [dlcc_integral_edgeV ℓ d r τ 0 (c - A) (c + A) hcA (by linarith)]
    rw [detourLeftC,
      dlcc_integral_edgeH_neg ℓ d r τ ξ (c - A) hξ hcA,
      dlcc_integral_edgeV ℓ d r τ (-ξ) (c - A) (c + A) hcA (by linarith),
      dlcc_integral_edgeH_neg ℓ d r τ ξ (c + A) hξ (by linarith)]
    linear_combination -hrect
  · simp only [not_or] at hd
    have hK (w : UpperHalfPlane) : Work.Kernels.Kfun ℓ d τ w = 0 :=
      Kfun_eq_zero_of_ne hd.1 hd.2 ℓ τ w
    have hdet : detourLeftC ℓ d r c A ξ τ = 0 := by
      simp [detourLeftC, edgeH, edgeV, hK]
    have hint : (∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ 0 v) = 0 := by
      simp [edgeV, hK]
    rw [hdet, hint]

end Work.Asymptotics
