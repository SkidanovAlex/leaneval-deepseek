import Mathlib
import Submission.Work.LayerCont.Coinc.CoincClean
import Submission.Work.LayerCont.Coinc.DetourCoinc
import Submission.Work.LayerCont.Coinc.layerLowCoinc_eq_layerLow_far
import Submission.Work.LayerCont.LowDouble
import Submission.Work.LayerCont.DetourNoOrbit

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Coinc

/-- **The left detour equals the replaced interval integral, orbit-free case, pointwise form.**

This is `Work.Asymptotics.detourLeftC_eq_interval_of_noOrbit` with the ball-quantified
orbit-exclusion hypothesis replaced by its value at the single point `τ` (which is all its proof
uses), so that it can be applied when the orbit-exclusion is only available under the extra guard
`1 < τ.re`. -/
theorem detourLeftC_eq_interval_of_noOrbit_pointwise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {r c A ξ : ℝ} (hA : 0 < A) (hξ : 0 < ξ) (hcA : 0 < c - A) (τ : UpperHalfPlane)
    (hcl : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect c A ξ z → z ≠ γ • τ) :
    Work.Asymptotics.detourLeftC ℓ d r c A ξ τ
      = ∫ v in Set.Ioo (c - A) (c + A), Work.Asymptotics.edgeV ℓ d r τ 0 v := by
  by_cases hd : d = 8 ∨ d = 24
  · have hcl' : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect c A ξ z → (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ) :=
      fun γ z hz => Or.inl (hcl γ z hz)
    have hcleanish := Work.Asymptotics.dlcc_clean τ c A ξ hcA hcl'
    have hPoleNotMem : Work.Asymptotics.poleℂ τ ∉ Work.Asymptotics.leftRectℂ c A ξ :=
      Work.Asymptotics.poleℂ_notMem_leftRectℂ τ c A ξ hcA hcl
    have hcontRect : ContinuousOn (Work.Asymptotics.kerForm ℓ d r τ)
        (Work.Asymptotics.leftRectℂ c A ξ) := by
      have h := Work.Asymptotics.dlcc_continuousOn ℓ d hd r τ c A ξ hcA hcleanish
      rwa [Set.sdiff_singleton_eq_self hPoleNotMem] at h
    set z₀ : ℂ := ((-ξ / 2 : ℝ) : ℂ) + ((c : ℝ) : ℂ) * Complex.I with hz₀
    have hz₀re : z₀.re = -ξ / 2 := by rw [hz₀]; simp
    have hz₀im : z₀.im = c := by rw [hz₀]; simp
    have hz₀open : z₀ ∈ Work.Asymptotics.openLeftRectℂ c A ξ := by
      simp only [Work.Asymptotics.openLeftRectℂ, Set.mem_ofPred_eq]
      exact ⟨by rw [hz₀re]; linarith, by rw [hz₀re]; linarith,
        by rw [hz₀im]; linarith, by rw [hz₀im]; linarith⟩
    have hmem₀ : Work.Asymptotics.leftRectℂ c A ξ ∈ 𝓝 z₀ :=
      Filter.mem_of_superset ((Work.Asymptotics.isOpen_openLeftRectℂ' c A ξ).mem_nhds hz₀open)
        (Work.Asymptotics.openLeftRectℂ_subset_leftRectℂ c A ξ)
    have hcont : ContinuousOn (Work.Asymptotics.kerForm ℓ d r τ)
        (Work.Asymptotics.leftRectℂ c A ξ \ {z₀}) :=
      hcontRect.mono Set.sdiff_subset
    have hhol : ∀ z : ℂ, (-ξ) < z.re → z.re < 0 → c - A < z.im → z.im < c + A → z ≠ z₀ →
        DifferentiableAt ℂ (Work.Asymptotics.kerForm ℓ d r τ) z := by
      intro z h1 h2 h3 h4 _
      refine Work.Asymptotics.dlcc_differentiableAt ℓ d hd r τ c A ξ hcA hcleanish z
        ⟨h1, h2, h3, h4⟩ ?_
      intro hpe
      exact hPoleNotMem (hpe ▸ Work.Asymptotics.openLeftRectℂ_subset_leftRectℂ c A ξ
        ⟨h1, h2, h3, h4⟩)
    have hres : Filter.Tendsto (fun z : ℂ => (z - z₀) * Work.Asymptotics.kerForm ℓ d r τ z)
        (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
      have h1 : Filter.Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
        have h : Filter.Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 (z₀ - z₀)) :=
          (continuous_id.sub continuous_const).tendsto z₀
        simpa using h
      have h2 : Filter.Tendsto (fun z : ℂ => Work.Asymptotics.kerForm ℓ d r τ z) (𝓝 z₀)
          (𝓝 (Work.Asymptotics.kerForm ℓ d r τ z₀)) := hcontRect.continuousAt hmem₀
      have h3 := h1.mul h2
      have h3' : Filter.Tendsto
          (fun z : ℂ => (z - z₀) * Work.Asymptotics.kerForm ℓ d r τ z) (𝓝 z₀)
          (𝓝 (0 * Work.Asymptotics.kerForm ℓ d r τ z₀)) := h3
      rw [zero_mul] at h3'
      exact h3'.mono_left nhdsWithin_le_nhds
    have hrect := Work.Asymptotics.rectInt_eq_residue (Work.Asymptotics.kerForm ℓ d r τ) z₀ 0
      (-ξ) 0 (c - A) (c + A)
      (by rw [hz₀re]; linarith) (by rw [hz₀re]; linarith)
      (by rw [hz₀im]; linarith) (by rw [hz₀im]; linarith) hcont hhol hres
    rw [mul_zero] at hrect
    rw [Work.Asymptotics.dlcc_integral_edgeV ℓ d r τ 0 (c - A) (c + A) hcA (by linarith)]
    rw [Work.Asymptotics.detourLeftC,
      Work.Asymptotics.dlcc_integral_edgeH_neg ℓ d r τ ξ (c - A) hξ hcA,
      Work.Asymptotics.dlcc_integral_edgeV ℓ d r τ (-ξ) (c - A) (c + A) hcA (by linarith),
      Work.Asymptotics.dlcc_integral_edgeH_neg ℓ d r τ ξ (c + A) hξ (by linarith)]
    linear_combination -hrect
  · simp only [not_or] at hd
    have hK (w : UpperHalfPlane) : Work.Kernels.Kfun ℓ d τ w = 0 :=
      Work.Asymptotics.Kfun_eq_zero_of_ne hd.1 hd.2 ℓ τ w
    have hdet : Work.Asymptotics.detourLeftC ℓ d r c A ξ τ = 0 := by
      simp [Work.Asymptotics.detourLeftC, Work.Asymptotics.edgeH, Work.Asymptotics.edgeV, hK]
    have hint : (∫ v in Set.Ioo (c - A) (c + A), Work.Asymptotics.edgeV ℓ d r τ 0 v) = 0 := by
      simp [Work.Asymptotics.edgeV, hK]
    rw [hdet, hint]

/-- **Far-side twin of `Work.LayerCont.layerLowDouble_eq_layerLowAt`** (`1 < τ.re` instead of
`τ.re < 1`).

The near-side original (`Submission/Work/LayerCont/LowDouble.lean`, sorry-free) proves
`layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ = layerLowAt ℓ d p r τ` for `τ.re < 1`, using the
pole-side identity `Work.Asymptotics.detourLeftC_eq_interval_sub_residue` (which carries the
residue correction `-resCorr`) and the coincidence-side
`Work.Asymptotics.detourLeftC_eq_interval_of_clean`.

On the far side both detours are residue-free:
* the pole-side rectangle `leftRect t₀ A₁ ξ₁` is orbit-free (`hcl₁`), so
  `Work.Asymptotics.detourLeftC_eq_interval_of_noOrbit` (import
  `Submission/Work/LayerCont/DetourNoOrbit`) gives
  `detourLeftC ℓ d r t₀ A₁ ξ₁ τ = ∫_{I₁} edgeV` with **no** `resCorr`;
* the coincidence-side rectangle contains only the removable coincidence (`hcl₂`, `hcoinc`), so
  `Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc` (hypotheses `hclean`, `hcoinc`, `hdeg`)
  gives `detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ = ∫_{I₂} edgeV`.

Hence `layerLowDouble = sinSqC r * ∫_{(0,p]} + sinSqC r * resCorr r τ = layerLowAt + sinSqC r *
resCorr r τ`: the residue correction built into `layerLowDouble` is no longer cancelled.

Integrability comes from `Work.LayerCont.KaxisBoundedIocBall` with `p` after combining
`hcleanAll` (off `I₁ ∪ I₂`) with the cleanliness of `I₁` derived from `hcl₁`
(`Work.LayerCont.Coinc.jInvariantFun_ne_imagAxis_of_orbitFree`) and of `I₂` derived from
`hcl₂` + `hcoinc` (`Work.LayerCont.Coinc.jInvariantFun_ne_imagAxis_of_coinc`), then splitting
`∫_{(0,p]} = ∫_E + ∫_{I₁} + ∫_{I₂}` as in the near-side proof. -/
theorem layerLowDouble_eq_layerLowAt_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁) (hξ₁ : 0 < ξ₁)
    (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hlo : 0 < t₀ - A₁) (hhi : t₀ + A₁ ≤ p)
    (hsep : t₀⁻¹ + A₂ < t₀ - A₁) (hA₂inv : A₂ < t₀⁻¹)
    (hcl₁ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀ A₁ ξ₁ z → z ≠ γ • τ)
    (hcl₂ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ t₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.Residues.jprime τ ≠ 0)
    (hcleanAll : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
          ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
        = Work.LayerCont.layerLowAt ℓ d p r τ
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by
  intro τ hτ hτre
  have hp0 : 0 < p := by linarith
  have hA₂lo : 0 < t₀⁻¹ - A₂ := by linarith
  -- ### the two detour identities (both residue-free on the far side)
  have hres₁ : Work.Asymptotics.detourLeftC ℓ d r t₀ A₁ ξ₁ τ
      = (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁), Work.Asymptotics.edgeV ℓ d r τ 0 v) :=
    detourLeftC_eq_interval_of_noOrbit_pointwise ℓ d hA₁ hξ₁ hlo τ (hcl₁ τ hτ hτre)
  have hres₂ : Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ
      = (∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), Work.Asymptotics.edgeV ℓ d r τ 0 v) :=
    detourLeftC_eq_interval_of_coinc_pointwise ℓ d hd (r := r) (c := t₀⁻¹) (A := A₂) (ξ := ξ₂)
      hA₂ hξ₂ hA₂lo τ
      (dlcc_clean_coinc τ t₀⁻¹ A₂ ξ₂ hA₂lo (hcl₂ τ hτ hτre))
      (hcoinc τ hτ hτre) (hdeg τ hτ hτre)
  -- ### the axis integrand is the contour integrand on both intervals
  have hedge₁ : (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁), Work.Asymptotics.edgeV ℓ d r τ 0 v)
      = ∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun v hv => Work.LayerCont.edgeV_zero_eq ℓ d r τ (by linarith [hv.1, hlo]))
  have hedge₂ : (∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), Work.Asymptotics.edgeV ℓ d r τ 0 v)
      = ∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun v hv => Work.LayerCont.edgeV_zero_eq ℓ d r τ (by linarith [hv.1, hA₂lo]))
  -- ### far-side cleanliness of the two removed intervals
  have hcleanI₁ : ∀ (s : ℝ) (hs : 0 < s), s ∈ Set.Icc (t₀ - A₁) (t₀ + A₁) →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsI => jInvariantFun_ne_imagAxis_of_orbitFree τ (hcl₁ τ hτ hτre) hs
      (imagAxis_mem_leftRect hs hξ₁ hsI)
  have hcleanI₂ : ∀ (s : ℝ) (hs : 0 < s), s ∈ Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsI => jInvariantFun_ne_imagAxis_of_coinc τ (hcl₂ τ hτ hτre)
      (coincℂ_re_neg_of_mem_openLeftRectℂ (hcoinc τ hτ hτre)) hs
      (imagAxis_mem_leftRect hs hξ₂ hsI)
  -- ### cleanliness of the whole extended contour `(0,p]`
  have hcleanFull : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht htI
    by_cases hmem : t ∈ Set.Ioo (t₀ - A₁) (t₀ + A₁)
    · exact hcleanI₁ t ht ⟨hmem.1.le, hmem.2.le⟩
    · by_cases hmem₂ : t ∈ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)
      · exact hcleanI₂ t ht ⟨hmem₂.1.le, hmem₂.2.le⟩
      · exact hcleanAll τ hτ hτre t ht ⟨htI, fun h => h.elim hmem hmem₂⟩
  -- ### integrability from the uniform bound on the extended contour
  have hmeasmal : Measurable
      (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t) :=
    (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)
  obtain ⟨C, hCnn, hCb⟩ := Work.LayerCont.KaxisBoundedIocBall ℓ d hd τ hp0 hcleanFull
  have hIntF : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioc (0 : ℝ) p) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hmeasmal.aestronglyMeasurable (C * 1) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [norm_mul]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖
            * ‖Work.Asymptotics.gaussWeight r v‖
          ≤ C * 1 := mul_le_mul (hCb v hv) (Work.LayerCont.norm_gaussWeight_le_one r v
              (le_of_lt hv.1)) (norm_nonneg _) hCnn
        _ = C * 1 := rfl
  -- ### the two intervals lie in `(0,p]`
  have hI₁sub : Set.Ioo (t₀ - A₁) (t₀ + A₁) ⊆ Set.Ioc (0 : ℝ) p := fun x hx =>
    ⟨lt_trans hlo hx.1, le_of_lt (lt_of_lt_of_le hx.2 hhi)⟩
  have hI₂sub : Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) ⊆ Set.Ioc (0 : ℝ) p := fun x hx =>
    ⟨by linarith [hx.1, hA₂lo], by linarith [hx.2, hsep, hhi]⟩
  have hInt1 : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioo (t₀ - A₁) (t₀ + A₁)) :=
    hIntF.mono_set hI₁sub
  have hInt2 : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) :=
    hIntF.mono_set hI₂sub
  have hdisj : Disjoint (Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) (Set.Ioo (t₀ - A₁) (t₀ + A₁)) :=
    Set.disjoint_left.mpr (fun x hx₁ hx₂ => absurd hx₂.1 (not_lt.mpr (by linarith [hx₁.2, hsep])))
  have hIntE : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v)
      ((Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
        ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂))) :=
    hIntF.mono_set (fun x hx => hx.1)
  have hIntE₁ : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v)
      ((Set.Ioc (0 : ℝ) p) \ Set.Ioo (t₀ - A₁) (t₀ + A₁)) :=
    hIntF.mono_set (fun x hx => hx.1)
  -- ### the splitting of the extended contour
  have hsplit₁ : (∫ t in Set.Ioc (0 : ℝ) p,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
      = (∫ t in (Set.Ioc (0 : ℝ) p) \ Set.Ioo (t₀ - A₁) (t₀ + A₁),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
        + ∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v := by
    have hset : Set.Ioc (0 : ℝ) p
        = ((Set.Ioc (0 : ℝ) p) \ Set.Ioo (t₀ - A₁) (t₀ + A₁)) ∪ Set.Ioo (t₀ - A₁) (t₀ + A₁) := by
      rw [Set.sdiff_union_self, Set.union_eq_left.mpr hI₁sub]
    have h2 := MeasureTheory.setIntegral_union
      (s := (Set.Ioc (0 : ℝ) p) \ Set.Ioo (t₀ - A₁) (t₀ + A₁))
      (t := Set.Ioo (t₀ - A₁) (t₀ + A₁))
      (Set.disjoint_left.mpr (fun x hx hx' => hx.2 hx')) measurableSet_Ioo hIntE₁ hInt1
    rw [← hset] at h2
    exact h2
  have hsplit₂ : (∫ t in (Set.Ioc (0 : ℝ) p) \ Set.Ioo (t₀ - A₁) (t₀ + A₁),
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
      = (∫ t in (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
            ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
        + ∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v := by
    have hset : (Set.Ioc (0 : ℝ) p) \ Set.Ioo (t₀ - A₁) (t₀ + A₁)
        = ((Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
            ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂))) ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) := by
      ext x
      constructor
      · intro hx
        by_cases hx2 : x ∈ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)
        · exact Or.inr hx2
        · exact Or.inl ⟨hx.1, fun h => h.elim hx.2 hx2⟩
      · rintro (hx | hx)
        · exact ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
        · exact ⟨hI₂sub hx, fun h => Set.disjoint_left.mp hdisj hx h⟩
    have h2 := MeasureTheory.setIntegral_union
      (s := (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
        ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)))
      (t := Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂))
      (Set.disjoint_left.mpr (fun x hx hx' => hx.2 (Or.inr hx'))) measurableSet_Ioo hIntE hInt2
    rw [← hset] at h2
    exact h2
  -- ### `layerLowAt` unfolded
  have hlow : Work.LayerCont.layerLowAt ℓ d p r τ
      = Work.Asymptotics.sinSqC r * (∫ t in Set.Ioc (0 : ℝ) p,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t) := by
    rw [Work.LayerCont.layerLowAt, intervalIntegral.integral_of_le hp0.le]
  -- ### assembly
  have hdet₁ : Work.Asymptotics.detourLeftC ℓ d r t₀ A₁ ξ₁ τ
      = (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v) := by
    rw [hres₁, hedge₁]
  have hdet₂ : Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ
      = ∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v := by
    rw [hres₂, hedge₂]
  simp only [Work.LayerCont.layerLowDouble]
  rw [hdet₁, hdet₂]
  have halg : Work.Asymptotics.sinSqC r
        * ((∫ t in (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
              ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)),
              Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
          + (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁),
              Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v)
          + (∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
              Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v))
      = Work.Asymptotics.sinSqC r
        * (∫ t in Set.Ioc (0 : ℝ) p,
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t) := by
    rw [hsplit₁, hsplit₂]
    ring
  rw [halg, hlow]

end Work.LayerCont.Coinc
