/-
# The pointwise far-side double-piece agreement

`Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far` states the far-side agreement with its
geometric hypotheses quantified over a whole hyperbolic ball `B(1 + i t₀, ε)`.  Its proof only ever
uses them at the point `τ` under consideration, so this file records the same identity with the
hypotheses at a *single* far-side point — the shape a caller needs when its region is not a ball.

Because on the far side (`1 < τ.re`) both detour identities
(`Work.LayerCont.Coinc.detourLeftC_eq_interval_of_noOrbit_pointwise` and
`Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc_pointwise`) are residue-free, the identity
carries the shift `sinSqC r * resCorr r τ` that `layerLowDouble` has and `layerLowAt` does not.
-/
import Mathlib
import Submission.Work.LayerCont.Coinc.CoincClean
import Submission.Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far
import Submission.Work.LayerCont.DetourNoOrbit

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Coinc

/-- **Pointwise far-side double-piece agreement.**  The hypotheses are those of
`Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far` at the single point `τ`. -/
theorem layerLowDouble_eq_layerLowAt_at (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁) (hξ₁ : 0 < ξ₁)
    (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hlo : 0 < t₀ - A₁) (hhi : t₀ + A₁ ≤ p)
    (hsep : t₀⁻¹ + A₂ < t₀ - A₁) (hA₂inv : A₂ < t₀⁻¹)
    (τ : UpperHalfPlane) (hre : 1 < τ.re)
    (hcl₁ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀ A₁ ξ₁ z → z ≠ γ • τ)
    (hcl₂ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ t₀⁻¹ A₂ ξ₂)
    (hdeg : Work.Residues.jprime τ ≠ 0)
    (hcleanAll : ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
          ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
      = Work.LayerCont.layerLowAt ℓ d p r τ
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by

  have hp0 : 0 < p := by linarith
  have hA₂lo : 0 < t₀⁻¹ - A₂ := by linarith
  -- ### the two detour identities (both residue-free on the far side)
  have hres₁ : Work.Asymptotics.detourLeftC ℓ d r t₀ A₁ ξ₁ τ
      = (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁), Work.Asymptotics.edgeV ℓ d r τ 0 v) :=
    detourLeftC_eq_interval_of_noOrbit_pointwise ℓ d hA₁ hξ₁ hlo τ (hcl₁)
  have hres₂ : Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ
      = (∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), Work.Asymptotics.edgeV ℓ d r τ 0 v) :=
    detourLeftC_eq_interval_of_coinc_pointwise ℓ d hd (r := r) (c := t₀⁻¹) (A := A₂) (ξ := ξ₂)
      hA₂ hξ₂ hA₂lo τ
      (dlcc_clean_coinc τ t₀⁻¹ A₂ ξ₂ hA₂lo (hcl₂))
      (hcoinc) (hdeg)
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
    fun s hs hsI => jInvariantFun_ne_imagAxis_of_orbitFree τ (hcl₁) hs
      (imagAxis_mem_leftRect hs hξ₁ hsI)
  have hcleanI₂ : ∀ (s : ℝ) (hs : 0 < s), s ∈ Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsI => jInvariantFun_ne_imagAxis_of_coinc τ (hcl₂)
      (coincℂ_re_neg_of_mem_openLeftRectℂ (hcoinc)) hs
      (imagAxis_mem_leftRect hs hξ₂ hsI)
  -- ### cleanliness of the whole extended contour `(0,p]`
  have hcleanFull : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht htI
    by_cases hmem : t ∈ Set.Ioo (t₀ - A₁) (t₀ + A₁)
    · exact hcleanI₁ t ht ⟨hmem.1.le, hmem.2.le⟩
    · by_cases hmem₂ : t ∈ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)
      · exact hcleanI₂ t ht ⟨hmem₂.1.le, hmem₂.2.le⟩
      · exact hcleanAll t ht ⟨htI, fun h => h.elim hmem hmem₂⟩
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
