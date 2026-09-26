/-
# The far side of the window chart in the *reversed* regime (`s₀ < 1`)

`Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far` computes the far-side (`1 < Re τ`)
identity of the window chart under the ordering hypothesis `t₀⁻¹ + A₂ < t₀ - A₁`, i.e. for heights
`t₀ > 1`, where the pole rectangle (height `t₀`) lies *above* the coincidence rectangle
(height `t₀⁻¹`).  For the heights `t₀ < 1` of `Work.LayerCont.layerWindowContinuation_rev` the two
rectangles are the other way round, and the same conclusion holds: on the far side the only orbit
point that the two swept rectangles can meet is the removable coincidence `ST⁻¹τ`, so both left
detours are residue-free and the chart is `layerLowAt + sinSqC r · resCorr r`.

The proof is the same contour computation as in the `t₀ > 1` case; only the two purely geometric
consequences of the separation hypothesis change:

* the coincidence interval `I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)` lies inside the extended contour `(0,p]`
  because `p` is chosen above `t₀⁻¹ + A₂` (`hhi₂`; the reversed capstone
  `Work.LayerCont.layerWindowContinuation_rev` chooses its split point this way), and
* `I₁` and `I₂` are disjoint by the *reversed* separation `t₀ + A₁ ≤ t₀⁻¹ - A₂`.
-/
import Mathlib
import Submission.Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far
import Submission.Work.LayerCont.FarTail.FarIdentity

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

open Work.LayerCont.Coinc

/-- **The far-side contour identity of the window chart, reversed regime.**  For `1 < τ.re`, and
with the pole rectangle (height `t₀`) *below* the coincidence rectangle (height `t₀⁻¹`), the
corrected low piece equals `layerLowAt` plus the residue correction. -/
theorem layerLowDouble_eq_layerLowAt_far_rev (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁) (hξ₁ : 0 < ξ₁)
    (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hlo : 0 < t₀ - A₁) (hhi₁ : t₀ + A₁ ≤ p) (hhi₂ : t₀⁻¹ + A₂ ≤ p)
    (hsep : t₀ + A₁ ≤ t₀⁻¹ - A₂) (hA₂inv : A₂ < t₀⁻¹)
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
    ⟨lt_trans hlo hx.1, le_of_lt (lt_of_lt_of_le hx.2 hhi₁)⟩
  have hI₂sub : Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) ⊆ Set.Ioc (0 : ℝ) p := fun x hx =>
    ⟨by linarith [hx.1, hA₂lo], by linarith [hx.2, hhi₂]⟩
  have hInt1 : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioo (t₀ - A₁) (t₀ + A₁)) :=
    hIntF.mono_set hI₁sub
  have hInt2 : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) :=
    hIntF.mono_set hI₂sub
  have hdisj : Disjoint (Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) (Set.Ioo (t₀ - A₁) (t₀ + A₁)) :=
    Set.disjoint_left.mpr (fun x hx₁ hx₂ => absurd hx₂.2 (not_lt.mpr (by linarith [hx₁.1, hsep])))
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


/-- **The far-side identity of the window chart in the reversed regime (`s₀ < 1`).** -/
theorem far_identity_rev (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ A₁ ξ₁ A₂ ξ₂ p ε : ℝ} (hs₀ : 0 < s₀) (hA₁ : 0 < A₁) (hξ₁ : 0 < ξ₁) (hA₂ : 0 < A₂)
    (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hp1 : 1 ≤ p) (hlo : 0 < s₀ - A₁) (hhi₁ : s₀ + A₁ ≤ p)
    (hhi₂ : s₀⁻¹ + A₂ ≤ p) (hsep : s₀ + A₁ ≤ s₀⁻¹ - A₂) (hA₂inv : A₂ < s₀⁻¹)
    (hcl₁ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z → z ≠ γ • τ)
    (hcl₂ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ s₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      Work.Residues.jprime τ ≠ 0)
    (hclean : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (hInt : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ r : ℝ, MeasureTheory.IntegrableOn (fun t : ℝ =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ))) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      windowChart ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by
  intro τ r hτ hτre
  have hlow : Work.LayerCont.layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ
      = Work.LayerCont.layerLowAt ℓ d p r τ
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ :=
    layerLowDouble_eq_layerLowAt_far_rev ℓ d hd hs₀ hA₁ hξ₁ hA₂ hξ₂ hε hlo hhi₁ hhi₂ hsep hA₂inv
      hcl₁ hcl₂ hcoinc hdeg (fun σ hσ hre t ht _ => hclean σ hσ hre t ht) τ hτ hτre
  have hat : Work.LayerCont.layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
    Work.LayerCont.layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (p := p) hp1 τ
      (fun t ht _ => hclean τ hτ hτre t ht) (hInt τ hτ hτre r)
  exact windowChart_eq_paperLayer_add_resCorr ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r τ hlow hat

end Work.LayerCont.FarTail
