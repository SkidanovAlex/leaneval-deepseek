import Mathlib
import Submission.Work.LayerCont.LowCoinc
import Submission.Work.LayerCont.TruncFromContour
import Submission.Work.LayerCont.TruncContData

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- Imaginary part of `tauSubOne`. -/
lemma tauSubOne_im' (τ : UpperHalfPlane) :
    (Work.Asymptotics.tauSubOne τ).im = τ.im := by
  have h := congrArg Complex.im (Work.Asymptotics.tauSubOne_coe τ)
  simpa using h

/-- **Holomorphy of the `high` part of the layer** (`τ ↦ highPart (Gcusp ℓ d) τ r`): a linear
combination of the coefficient functions `Gcusp ℓ d i j` with coefficients *constant in `τ`*
(`psi1` and the exponentials depend only on `r`). -/
theorem mdifferentiable_highPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  change DifferentiableOn ℂ (fun z : ℂ =>
    Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex z) r)
    {z | 0 < z.im}
  have hGc : ∀ i j : Fin 2, DifferentiableOn ℂ
      (fun z : ℂ => Work.Asymptotics.Gcusp ℓ d i j (UpperHalfPlane.ofComplex z))
      {z | 0 < z.im} :=
    fun i j => UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_Gcusp ℓ d hd i j)
  simp only [Work.Asymptotics.highPart]
  fun_prop

/-- **Cleanliness of the *low* range for `τ.re < 1`**, from the web classification.

If `j τ = j (i t)` then `τ = σ • (i t)` for some `σ`, and the web says that every orbit point of
`i t` within `rw₀` of `1 + i s₀` has real part exactly `1`.  So `τ.re = 1`, contradicting
`τ.re < 1` — *no height estimate is needed* (this is the `τ.re < 1` companion of
`Work.LayerCont.clean_axis_of_web`). -/
theorem clean_axis_of_web_low {s₀ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hεw : ε ≤ rw₀)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → τ.re < 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro t ht _ τ hτ hτre hjeq
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hd : dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ := by
    rw [hσ]
    exact lt_of_lt_of_le hτ hεw
  obtain ⟨hre, -⟩ := hweb σ t ht hd
  rw [hσ] at hre
  linarith

/-- **Cleanliness of the low range *minus* `I₂`, for every `τ` of the ball** (not only `τ.re < 1`).

Here the web gives `τ.re = 1` and `τ.im ∈ {t, t⁻¹}`:
* `τ.im = t ≤ 1` is impossible because the ball lies in the trunc case (`1 < s₀ - A₁` and the
  height bound `|τ.im - s₀| < 3 s₀ ε < A₁` give `τ.im > 1`);
* `τ.im = t⁻¹` gives `t = τ.im⁻¹`, and the estimates
  `|τ.im⁻¹ - s₀⁻¹| = |s₀ - τ.im|/(s₀ τ.im) < 3 s₀ ε/(s₀ τ.im)` together with `τ.im > 13 s₀/16`
  (`ε ≤ 1/16`) and `ε ≤ A₂ s₀ / 4` put `t` inside `I₂ = (s₀⁻¹-A₂, s₀⁻¹+A₂)`.

This is the cleanliness hypothesis of `Work.LayerCont.mdifferentiableOn_layerLowCoinc` (where the
`τ.re < 1` restriction is *not* available, since the holomorphy is needed on the whole ball). -/
theorem clean_axis_of_web_low_removed {s₀ A₁ A₂ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hhi : 1 < s₀ - A₁)
    (hgt : 3 * s₀ * ε < A₁) (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) (hεw : ε ≤ rw₀)
    (h4ε : 4 * ε ≤ A₂ * s₀)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (t : ℝ) (ht : 0 < t),
      t ∈ (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro t ht htE τ hτ hjeq
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hd : dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ := by
    rw [hσ]
    exact lt_of_lt_of_le hτ hεw
  obtain ⟨hre, him⟩ := hweb σ t ht hd
  rw [hσ] at hre him
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp
    (Work.Asymptotics.abs_re_im_sub_lt hs₀ hε (le_trans hε16 (by norm_num)) hτ).2
  have hτim_gt : s₀ - A₁ < τ.im := by linarith
  have h3sε : 3 * s₀ * ε ≤ 3 * s₀ * (1 / 16) := by nlinarith [hε16, hs₀]
  have hτim : 13 * s₀ / 16 < τ.im := by linarith
  have hA₂pos : 0 < A₂ := by
    rcases le_or_gt A₂ 0 with h | h
    · exfalso
      have h2 : A₂ * s₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hs₀.le
      linarith [h4ε, hε]
    · exact h
  rcases him with him | him
  · -- `τ.im = t ≤ 1`, but `τ.im > s₀ - A₁ > 1`
    exfalso
    linarith [htE.1.2, him, hτim_gt, hhi]
  · -- `τ.im = t⁻¹`: then `t = τ.im⁻¹ ∈ I₂`
    refine absurd ?_ htE.2
    have ht_eq : t = τ.im⁻¹ := by rw [him, inv_inv]
    have hkey : |t - s₀⁻¹| < A₂ := by
      rw [ht_eq]
      have hdiv : τ.im⁻¹ - s₀⁻¹ = (s₀ - τ.im) / (s₀ * τ.im) := by
        rw [inv_sub_inv (ne_of_gt τ.im_pos) (ne_of_gt hs₀)]
        ring
      rw [hdiv, abs_div, abs_of_pos (mul_pos hs₀ τ.im_pos)]
      have hnum : |s₀ - τ.im| < 3 * s₀ * ε := by
        rw [abs_sub_comm]
        exact abs_lt.mpr ⟨h2lo, h2hi⟩
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < s₀ * τ.im)]
      have hle1 : 3 * s₀ * ε ≤ 3 * s₀ * (A₂ * s₀ / 4) := by nlinarith [h4ε, hs₀]
      have hle2 : 3 * s₀ * (A₂ * s₀ / 4) < A₂ * s₀ * τ.im := by
        nlinarith [hτim, hs₀, hA₂pos]
      have := lt_of_le_of_lt hle1 hle2
      linarith [hnum.le, this]
    rw [Set.mem_Ioo]
    obtain ⟨h1, h2⟩ := abs_lt.mp hkey
    constructor <;> linarith

/-- **`I₂ ⊆ (0,1]` for every height `s₀ > 1`**: from the two stated clauses
`A₂ ≤ |s₀ - s₀⁻¹|/8` and `A₂ ≤ 1/4` (the second one is the clause added to
`Work.LayerCont.ECS.exists_contour_left_data`), which together cover all `s₀ > 1` — the first for
`s₀ < 7`, the second for `s₀ ≥ 7`. -/
theorem sInvinv_add_lt_one {s₀ A₂ : ℝ} (hs₀1 : 1 < s₀) (hA₂bd : A₂ ≤ |s₀ - s₀⁻¹| / 8)
    (hA₂q : A₂ ≤ 1 / 4) : s₀⁻¹ + A₂ < 1 := by
  have hs₀ : 0 < s₀ := by linarith
  rcases lt_or_ge s₀ 7 with h7 | h7
  · have hinvpos : 0 < s₀⁻¹ := inv_pos.mpr hs₀
    have habs : |s₀ - s₀⁻¹| = s₀ - s₀⁻¹ := by
      rw [abs_of_pos]
      nlinarith [hs₀1, hinvpos, mul_inv_cancel₀ (ne_of_gt hs₀)]
    rw [habs] at hA₂bd
    have hprod : (s₀ - 1) * (s₀ - 7) < 0 := by nlinarith [hs₀1, h7]
    have hsum : s₀ + 7 * s₀⁻¹ < 8 := by
      nlinarith [hprod, hs₀, hinvpos, mul_inv_cancel₀ (ne_of_gt hs₀)]
    have : s₀⁻¹ + (s₀ - s₀⁻¹) / 8 = (7 * s₀⁻¹ + s₀) / 8 := by ring
    linarith
  · have hinv : s₀⁻¹ ≤ 1 / 7 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 7 by norm_num) h7
      simpa [one_div] using h
    linarith [hA₂q]

/-- **The trunc-case continuation of the CKMRV layer across `Re τ = 1`.**

For every `s₀ > 0` there are the geometry parameters `A₁, ξ₁, A₂, ξ₂` of
`Work.LayerCont.ECS.exists_contour_left_data` such that, in the *trunc* case `1 < s₀ - A₁`
(the pole `τ - 1` swept by the truncated range `[1,∞)`), there is a ball `B(1 + i s₀, ε')` on which

* the corrected layer
  `Lcont := layerLowCoinc ℓ d s₀ A₂ ξ₂ r + layerTruncCont ℓ d s₀ A₁ ξ₁ r + highPart (Gcusp ℓ d) · r`
  is holomorphic for every `r`, and
* `Lcont` agrees with the paper's layer `paperLayer (Gcusp ℓ d) ℓ d · r` on
  `{Re τ < 1} ∩ 𝒟`.

This is the `Re τ = 1` continuation of `F₂` in the trunc case: the low piece carries the
*coincidence-removed* modification (`layerLowCoinc`, with the residue-free detour at height `s₀⁻¹`)
and the trunc piece carries the pole correction (`layerTruncCont`, with `resCorr`).  The
cleanliness hypotheses of both `LowCoinc` lemmas are supplied by the *web* classification
(`clean_axis_of_web_low`, `clean_axis_of_web`), so nothing else is assumed; the geometry gives
`I₂ ⊆ (0,1]` (`sInvinv_add_lt_one` from `A₂ ≤ |s₀-s₀⁻¹|/8` and `A₂ ≤ 1/4`). -/
theorem layerTruncContinuation (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ A₁ ξ₁ A₂ ξ₂ : ℝ, 0 < A₁ ∧ 0 < ξ₁ ∧ 0 ≤ A₂ ∧ 0 ≤ ξ₂ ∧
      (1 < s₀ - A₁ → ∃ ε' : ℝ, 0 < ε' ∧
        (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => layerLowCoinc ℓ d s₀ A₂ ξ₂ r τ
            + layerTruncCont ℓ d s₀ A₁ ξ₁ r τ
            + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r)
          (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε')) ∧
        (∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε' →
          τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
            layerLowCoinc ℓ d s₀ A₂ ξ₂ r τ + layerTruncCont ℓ d s₀ A₁ ξ₁ r τ
              + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r
              = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)) := by
  obtain ⟨ε, hεpos, A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, hA₁s, hξ₁1, hA₂inv, h4sεA, h4sεξ,
    hsep1, hsep2, hclean, hedge₀, hclass, hA₂bd, hξ₂bd, hA₂q, hξ₂q, hε4, hεa₁, hεa₂,
    rw₀, hrw₀pos, hεw, hweb⟩ := Work.LayerCont.ECS.exists_contour_left_data s₀ hs₀
  refine ⟨A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, fun hhi => ?_⟩
  have hs₀1 : 1 < s₀ := by linarith
  have hI₂low : s₀⁻¹ + A₂ < 1 := sInvinv_add_lt_one hs₀1 hA₂bd hA₂q
  have hs₀ne : s₀ ≠ 1 := by linarith
  have hA₂pos : 0 < A₂ := (hsep2 hs₀ne).1
  have hξ₂pos : 0 < ξ₂ := (hsep2 hs₀ne).2.1
  -- the working radius
  set εb : ℝ := min ε (1 / 16) with hεbdef
  have hεbpos : 0 < εb := lt_min hεpos (by norm_num)
  have hεbε : εb ≤ ε := min_le_left _ _
  have hεb16 : εb ≤ 1 / 16 := min_le_right _ _
  have hεb1 : εb ≤ 1 := le_trans hεb16 (by norm_num)
  have hεbw : εb ≤ rw₀ := le_trans hεbε hεw
  have h4sεb : 4 * s₀ * εb ≤ A₁ :=
    le_trans (mul_le_mul_of_nonneg_left hεbε (by positivity)) h4sεA
  have hgt : 3 * s₀ * εb < A₁ := by linarith
  have h4εb : 4 * εb ≤ A₂ * s₀ := by
    have h := (hsep2 hs₀ne).2.2.1
    linarith
  -- (a) the trunc agreement, at its own (smaller) radius
  obtain ⟨εa, hεapos, hεaε, hagreeTrunc⟩ :=
    layerTruncCont_eq_layerTrunc_of_contourLeft ℓ d hd hs₀ hA₁ hA₁s hξ₁ hA₂ hξ₂ hεpos h4sεA
      h4sεξ hclean hclass hhi
  -- (b) the low-range cleanliness, from the web
  have hcleanIoc : ∀ (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
    fun τ hτ hτre t ht htI => clean_axis_of_web_low hs₀ hεbw hweb t ht htI τ hτ hτre
  -- (b') the cleanliness of the retained low range for the *whole* ball
  have hcleanRemoved : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsE τ hτ =>
      clean_axis_of_web_low_removed hs₀ hhi hgt hεbpos hεb16 hεbw h4εb hweb s hs hsE τ hτ
  -- (c) the coincidence rectangle carries no orbit point
  have hcl₂ : ∀ (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z → z ≠ γ • τ := by
    intro τ hτ hτre γ z hz hzeq
    obtain ⟨h2lo, h2hi⟩ := abs_lt.mp
      (Work.Asymptotics.abs_re_im_sub_lt hs₀ hεbpos hεb1 hτ).2
    have hτim : 1 < τ.im := by linarith
    rcases hclass τ (lt_of_lt_of_le hτ hεbε) γ z (Or.inr hz) hzeq with h' | h'
    · have hzim : z.im = τ.im := by rw [h', tauSubOne_im']
      linarith [hz.2.2, hzim, hI₂low]
    · have hpos := Work.Asymptotics.tauCoinc_re_pos τ hτre
      rw [← h'] at hpos
      linarith [hz.2.1]
  -- (d) both low-piece statements at radius `εb`
  have hagreeLow : ∀ r : ℝ, ∀ (τ : UpperHalfPlane),
      dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < εb → τ.re < 1 →
        layerLowCoinc ℓ d s₀ A₂ ξ₂ r τ = Work.Asymptotics.layerLow ℓ d τ r := fun r =>
    layerLowCoinc_eq_layerLow ℓ d hd (r := r) hs₀ hA₂pos hξ₂pos hεbpos hA₂inv hI₂low hcl₂
      hcleanIoc
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
  have hholoLow : ∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerLowCoinc ℓ d s₀ A₂ ξ₂ r τ)
      (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) := fun r =>
    mdifferentiableOn_layerLowCoinc ℓ d hd (r := r) hs₀ hA₂pos hξ₂pos hεbpos hA₂inv hI₂low
      hedge₂ hcleanRemoved
  -- (e) the trunc holomorphy at radius `εb`, from the web
  have hholoTrunc := mdifferentiableOn_layerTruncCont_of_web ℓ d hd (A₂ := A₂) (ξ₂ := ξ₂) hs₀ hA₁
    hξ₁ hεbpos hεb1 hεbw hhi hgt
    (fun γ u v hv hc => le_trans hεbε (hedge₀ γ u v hv hc)) hweb
  -- (f) assembly
  refine ⟨min εa εb, lt_min hεapos hεbpos, fun r => ?_, fun τ r hτ hτre hD => ?_⟩
  · intro x hx
    have hx' : x ∈ Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb :=
      Metric.ball_subset_ball (min_le_right εa εb) hx
    have h1 := (hholoLow r) x hx'
    have h2 := (hholoTrunc r) x hx'
    have h3 : MDifferentiableWithinAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) εb) x :=
      ((mdifferentiable_highPart ℓ d hd r).mdifferentiableAt).mdifferentiableWithinAt
    exact ((h1.add h2).add h3).mono (Metric.ball_subset_ball (min_le_right εa εb))
  · have h1 := hagreeLow r τ (lt_of_lt_of_le hτ (min_le_right εa εb)) hτre
    have h2 := hagreeTrunc τ r (lt_of_lt_of_le hτ (min_le_left εa εb)) hτre hD
    rw [Work.Asymptotics.paperLayer, ← h1, ← h2]

end Work.LayerCont
