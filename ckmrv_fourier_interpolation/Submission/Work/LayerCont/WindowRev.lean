import Mathlib
import Submission.Work.LayerCont.LowDouble

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- **The window-chart agreement, reversed interval order** (`t₀ < 1`): with BOTH intervals removed and both detours added the corrected low piece over `(0,p]` equals
`layerLowAt` on `{Re τ < 1}`.  Here the pole interval `I₁ = (t₀-A₁,t₀+A₁)` lies *below* the
coincidence interval `I₂ = (t₀⁻¹-A₂,t₀⁻¹+A₂)`, so the split point `p` must be taken above both
(`hhi₂`); the pole detour still carries the residue correction `resCorr` and the coincidence
detour is residue-free.  (The mirror of `Work.LayerCont.layerLowDouble_eq_layerLowAt`.) -/
theorem layerLowDouble_eq_layerLowAt_rev (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁) (hξ₁ : 0 < ξ₁)
    (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hlo : 0 < t₀ - A₁)
    (hhi₁ : t₀ + A₁ ≤ p) (hhi₂ : t₀⁻¹ + A₂ ≤ p) (hsep : t₀ + A₁ < t₀⁻¹ - A₂)
    (hA₂inv : A₂ < t₀⁻¹)
    (hcl₁ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀ A₁ ξ₁ z → (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ))
    (hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      -ξ₁ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        t₀ - A₁ < (Work.Asymptotics.tauSubOne τ).im ∧
        (Work.Asymptotics.tauSubOne τ).im < t₀ + A₁)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0)
    (hcl₂ : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀⁻¹ A₂ ξ₂ z → z ≠ γ • τ)
    {τ : UpperHalfPlane} (hτ : dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε) (hτre : τ.re < 1)
    (hcleanAll : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ = layerLowAt ℓ d p r τ := by
  have hp0 : 0 < p := by linarith
  have hA₂lo : 0 < t₀⁻¹ - A₂ := by linarith
  -- ### the two residues / detour identities
  have hres₁ : Work.Asymptotics.detourLeftC ℓ d r t₀ A₁ ξ₁ τ
      = (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁), Work.Asymptotics.edgeV ℓ d r τ 0 v)
        - Work.Asymptotics.resCorr r τ :=
    Work.Asymptotics.detourLeftC_eq_interval_sub_residue ℓ d hd ht₀ hε hA₁ hξ₁ hlo
      hcl₁ hpole hdeg τ hτ hτre
  have hres₂ : Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ
      = (∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), Work.Asymptotics.edgeV ℓ d r τ 0 v) :=
    Work.Asymptotics.detourLeftC_eq_interval_of_clean ℓ d
      (r := r) (c := t₀⁻¹) (A := A₂) (ξ := ξ₂) (t₀ := t₀) ht₀ hε hA₂ hξ₂ hA₂lo hcl₂ τ hτ hτre
  -- ### the axis integrand is the contour integrand on both intervals
  have hedge₁ : (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁), Work.Asymptotics.edgeV ℓ d r τ 0 v)
      = ∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun v hv => edgeV_zero_eq ℓ d r τ (by linarith [hv.1, hlo]))
  have hedge₂ : (∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), Work.Asymptotics.edgeV ℓ d r τ 0 v)
      = ∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun v hv => edgeV_zero_eq ℓ d r τ (by linarith [hv.1, hA₂lo]))
  -- ### integrability from the uniform bound on the extended contour
  have hmeasmal : Measurable
      (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t) :=
    (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)
  obtain ⟨C, hCnn, hCb⟩ := KaxisBoundedIocBall ℓ d hd τ hp0 hcleanAll
  have hIntF : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioc (0 : ℝ) p) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hmeasmal.aestronglyMeasurable (C * 1) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [norm_mul]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖
            * ‖Work.Asymptotics.gaussWeight r v‖
          ≤ C * 1 := mul_le_mul (hCb v hv) (norm_gaussWeight_le_one r v (le_of_lt hv.1))
            (norm_nonneg _) hCnn
        _ = C * 1 := rfl
  -- ### the two intervals lie in `(0,p]`
  have hI₁sub : Set.Ioo (t₀ - A₁) (t₀ + A₁) ⊆ Set.Ioc (0 : ℝ) p := fun x hx =>
    ⟨lt_trans hlo hx.1, le_of_lt (lt_of_lt_of_le hx.2 hhi₁)⟩
  have hI₂sub : Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) ⊆ Set.Ioc (0 : ℝ) p := fun x hx =>
    ⟨by linarith [hx.1, hA₂lo], le_trans (le_of_lt hx.2) hhi₂⟩
  have hInt1 : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioo (t₀ - A₁) (t₀ + A₁)) :=
    hIntF.mono_set hI₁sub
  have hInt2 : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) :=
    hIntF.mono_set hI₂sub
  have hdisj : Disjoint (Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) (Set.Ioo (t₀ - A₁) (t₀ + A₁)) :=
    Set.disjoint_left.mpr (fun x hx₁ hx₂ => absurd hx₁.1 (not_lt.mpr (by linarith [hx₂.2, hsep])))
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
  have hlow : layerLowAt ℓ d p r τ
      = Work.Asymptotics.sinSqC r * (∫ t in Set.Ioc (0 : ℝ) p,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t) := by
    rw [layerLowAt, intervalIntegral.integral_of_le hp0.le]
  -- ### assembly
  have hdet₁ : Work.Asymptotics.detourLeftC ℓ d r t₀ A₁ ξ₁ τ
      = (∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v)
        - Work.Asymptotics.resCorr r τ := by
    rw [hres₁, hedge₁]
  have hdet₂ : Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ
      = ∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v := by
    rw [hres₂, hedge₂]
  simp only [layerLowDouble]
  rw [hdet₁, hdet₂]
  have halg : Work.Asymptotics.sinSqC r
        * ((∫ t in (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
              ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)),
              Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
          + ((∫ v in Set.Ioo (t₀ - A₁) (t₀ + A₁),
                Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v)
              - Work.Asymptotics.resCorr r τ)
          + ∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
              Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v)
      + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ
      = Work.Asymptotics.sinSqC r
        * (∫ t in Set.Ioc (0 : ℝ) p,
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t) := by
    rw [hsplit₁, hsplit₂]
    ring
  rw [halg, hlow]

/-- **Holomorphy of the window-chart low piece, reversed interval order** (`t₀ < 1`):
identical to `Work.LayerCont.mdifferentiableOn_layerLowDouble` with the two swept intervals
exchanged (`I₁ = (t₀-A₁,t₀+A₁)` below `I₂ = (t₀⁻¹-A₂,t₀⁻¹+A₂)`), so the dominator splits into
`(0, t₀-A₁]` (`KaxisBoundedIocClosedBall`), `[t₀+A₁, t₀⁻¹-A₂]` and `[t₀⁻¹+A₂, p]` (two
`GapBoundKaxisLow` bounds). -/
theorem mdifferentiableOn_layerLowDouble_rev (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁)
    (hξ₁ : 0 < ξ₁) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hlo : 0 < t₀ - A₁)
    (hhi₁ : t₀ + A₁ ≤ p) (hhi₂ : t₀⁻¹ + A₂ ≤ p) (hsep : t₀ + A₁ < t₀⁻¹ - A₂)
    (hA₂inv : A₂ < t₀⁻¹)
    (hedge₁ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = t₀ - A₁ ∨ v = t₀ + A₁))
        ∨ (u = -ξ₁ ∧ t₀ - A₁ < v ∧ v < t₀ + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v))
    (hedge₂ : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ < v ∧ v < t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v))
    (hcleanAxis : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
        ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ)
      (Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε) := by
  classical
  have hA₂lo : 0 < t₀⁻¹ - A₂ := by linarith
  have hdet₁ := Work.Asymptotics.detourLeftC_mdifferentiableOn_MR ℓ d hd
    (r := r) (c := t₀) ht₀ hA₁ hξ₁ hlo hε hedge₁
  have hdet₂ := Work.Asymptotics.detourLeftC_mdifferentiableOn_MR ℓ d hd
    (r := r) (c := t₀⁻¹) ht₀ hA₂ hξ₂ hA₂lo hε hedge₂
  have hres : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.resCorr r τ) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (by fun_prop : DifferentiableOn ℂ (fun z : ℂ =>
      Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (z - 1))) {z : ℂ | 0 < z.im}).congr ?_
    intro z hz
    show Work.Asymptotics.resCorr r (UpperHalfPlane.ofComplex z)
        = Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (z - 1))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    rfl
  have hpiece : ∀ x ∈ Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε,
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => ∫ t in (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
            ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t) x := by
    intro x hx
    have hxdist : dist x (Work.Asymptotics.onePlusI t₀ ht₀) < ε := by
      simpa [Metric.mem_ball] using hx
    set ρ : ℝ := (ε - dist x (Work.Asymptotics.onePlusI t₀ ht₀)) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    have hρlt : dist x (Work.Asymptotics.onePlusI t₀ ht₀) + ρ < ε := by rw [hρdef]; linarith
    set E : Set ℝ := (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
      ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) with hEdef
    have hEmeas : MeasurableSet E :=
      measurableSet_Ioc.diff (measurableSet_Ioo.union measurableSet_Ioo)
    have hEsub : E ⊆ Set.Ioi (0 : ℝ) := fun y hy => Set.mem_Ioi.mpr hy.1.1
    have hcleanE : ∀ (w : UpperHalfPlane), w ∈ Metric.closedBall x ρ → ∀ (t : ℝ) (ht : 0 < t),
        t ∈ E → Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      intro w hw t ht htE
      have hdist : dist w (Work.Asymptotics.onePlusI t₀ ht₀) < ε := by
        calc dist w (Work.Asymptotics.onePlusI t₀ ht₀)
            ≤ dist w x + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := dist_triangle _ _ _
          _ ≤ ρ + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := by
              linarith [Metric.mem_closedBall.mp hw]
          _ < ε := by linarith
      exact hcleanAxis t ht htE w hdist
    -- the three sub-intervals
    obtain ⟨C₁, hC₁nn, hC₁b⟩ := KaxisBoundedIocClosedBall ℓ d hd x ρ (p := t₀ - A₁) hlo
      (fun w hw t ht htI => hcleanE w hw t ht
        ⟨⟨htI.1, le_trans htI.2 (by linarith [hhi₁, hA₁])⟩,
          fun hmem => hmem.elim (fun h => absurd h.1 (not_lt.mpr htI.2))
            (fun h => absurd h.1 (not_lt.mpr (by linarith [htI.2, hsep])))⟩)
    obtain ⟨C₂, hC₂nn, hC₂b⟩ := GapBoundKaxisLow ℓ d hd (K := Metric.closedBall x ρ)
      (isCompact_closedBall x ρ) (δ := t₀ + A₁) (T := t₀⁻¹ - A₂) (by linarith)
      (fun w hw t ht htI => hcleanE w hw t ht
        ⟨⟨by linarith [htI.1], le_trans htI.2 (by linarith [hhi₂])⟩,
          fun hmem => hmem.elim (fun h => absurd h.2 (not_lt.mpr htI.1))
            (fun h => absurd h.1 (not_lt.mpr htI.2))⟩)
    obtain ⟨C₃, hC₃nn, hC₃b⟩ := GapBoundKaxisLow ℓ d hd (K := Metric.closedBall x ρ)
      (isCompact_closedBall x ρ) (δ := t₀⁻¹ + A₂) (T := p) (by linarith)
      (fun w hw t ht htI => hcleanE w hw t ht
        ⟨⟨by linarith [htI.1], htI.2⟩,
          fun hmem => hmem.elim (fun h => absurd h.2 (not_lt.mpr (by linarith [htI.1, hsep])))
            (fun h => absurd h.2 (not_lt.mpr htI.1))⟩)
    set C : ℝ := max C₁ (max C₂ C₃) with hCdef
    have hCnn : 0 ≤ C := le_trans hC₁nn (le_max_left C₁ (max C₂ C₃))
    have hbound : ∀ v ∈ E, ∀ w : UpperHalfPlane, dist w x ≤ ρ →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w v * Work.Asymptotics.gaussWeight r v‖ ≤ C := by
      intro v hv w hw
      have hvpos : 0 < v := hv.1.1
      have hkey : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w v‖ ≤ C := by
        rcases le_or_gt v (t₀ - A₁) with hv₁ | hv₁
        · exact le_trans (hC₁b w (Metric.mem_closedBall.mpr hw) v ⟨hvpos, hv₁⟩)
            (le_max_left C₁ (max C₂ C₃))
        · have hge₁ : t₀ + A₁ ≤ v := by
            by_contra h
            exact hv.2 (Or.inl ⟨hv₁, lt_of_not_ge h⟩)
          rcases le_or_gt v (t₀⁻¹ - A₂) with hv₂ | hv₂
          · exact le_trans (hC₂b w v (Metric.mem_closedBall.mpr hw) ⟨hge₁, hv₂⟩)
              (le_trans (le_max_left C₂ C₃) (le_max_right C₁ (max C₂ C₃)))
          · have hge₂ : t₀⁻¹ + A₂ ≤ v := by
              by_contra h
              exact hv.2 (Or.inr ⟨hv₂, lt_of_not_ge h⟩)
            exact le_trans (hC₃b w v (Metric.mem_closedBall.mpr hw) ⟨hge₂, hv.1.2⟩)
              (le_trans (le_max_right C₂ C₃) (le_max_right C₁ (max C₂ C₃)))
      rw [norm_mul]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w v‖
            * ‖Work.Asymptotics.gaussWeight r v‖
          ≤ C * 1 := mul_le_mul hkey (norm_gaussWeight_le_one r v hvpos.le) (norm_nonneg _) hCnn
        _ = C := mul_one _
    set bound : ℝ → ℝ := E.indicator (fun _ => C) with hbounddef
    have hEfin : volume E ≠ ⊤ := by
      have h : volume E ≤ volume (Set.Ioc (0 : ℝ) p) := measure_mono Set.sdiff_subset
      rw [Real.volume_Ioc] at h
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    have hbc : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
      show Integrable (E.indicator (fun _ => C)) (volume.restrict (Set.Ioi (0 : ℝ)))
      rw [integrable_indicator_iff hEmeas]
      show Integrable (fun _ : ℝ => C) ((volume.restrict (Set.Ioi (0 : ℝ))).restrict E)
      rw [Measure.restrict_restrict_of_subset hEsub]
      exact MeasureTheory.integrableOn_const hEfin (by simp)
    set U : Set ℂ := (UpperHalfPlane.coe : UpperHalfPlane → ℂ) '' (Metric.ball x ρ) with hUdef
    have hUopen : IsOpen U :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
    have hxU : (x : ℂ) ∈ U := ⟨x, Metric.mem_ball_self hρpos, rfl⟩
    have hUim : ∀ z ∈ U, 0 < z.im := by
      rintro z ⟨w, _, rfl⟩
      exact w.im_pos
    have hUb : ∀ z ∈ U, ∃ w : UpperHalfPlane, dist w x ≤ ρ ∧ (w : ℂ) = z := by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, le_of_lt (Metric.mem_ball.mp hw), rfl⟩
    set F : ℂ → ℝ → ℂ := fun z t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
      (UpperHalfPlane.ofComplex z) t * Work.Asymptotics.gaussWeight r t with hFdef
    have hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, ‖Set.indicator E (fun t' => F z t') t‖ ≤ bound t := by
      filter_upwards with t
      intro z hz
      by_cases htE : t ∈ E
      · obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hcoe : UpperHalfPlane.ofComplex z = w := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUim z hz), UpperHalfPlane.coe_mk, hwz]
        rw [Set.indicator_apply, if_pos htE, hbounddef, Set.indicator_apply, if_pos htE]
        simp only [hFdef, hcoe]
        exact hbound t htE w hwρ
      · rw [Set.indicator_apply, if_neg htE, norm_zero, hbounddef, Set.indicator_apply, if_neg htE]
    have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, DifferentiableAt ℂ (fun z' => Set.indicator E (fun t' => F z' t') t) z := by
      filter_upwards with t
      intro z hz
      have hzim : 0 < z.im := hUim z hz
      have heq : (fun z' : ℂ => Set.indicator E (fun t' => F z' t') t)
          = fun z' : ℂ => if t ∈ E then F z' t else 0 := by
        funext z'
        simp only [Set.indicator_apply]
      rw [heq]
      by_cases htE : t ∈ E
      · simp only [if_pos htE]
        have ht0 : 0 < t := htE.1.1
        obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hJ : Work.Kernels.jInvariantFun (⟨z, hzim⟩ : UpperHalfPlane)
            ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
          have hdist : dist (⟨z, hzim⟩ : UpperHalfPlane) x ≤ ρ := by
            have hzw : (⟨z, hzim⟩ : UpperHalfPlane) = w := UpperHalfPlane.ext hwz.symm
            rw [hzw]; exact hwρ
          exact hcleanE ⟨z, hzim⟩ (Metric.mem_closedBall.mpr hdist) t ht0 htE
        have heq2 : (fun z' : ℂ => F z' t)
            = fun z' : ℂ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex z')
                (Work.Kernels.imagAxis t ht0) * Work.Asymptotics.gaussWeight r t := by
          funext z'
          simp only [hFdef, Work.Kernels.Kaxis, dif_pos ht0]
        rw [heq2]
        exact (Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd
          (τ := (⟨z, hzim⟩ : UpperHalfPlane)) (z := Work.Kernels.imagAxis t ht0) hJ).mul_const _
      · simp only [if_neg htE]
        exact differentiableAt_const _
    have hmeas : ∀ z ∈ U, AEStronglyMeasurable
        (fun t : ℝ => Set.indicator E (fun t' => F z t') t)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      intro z hz
      have hFmeas : Measurable (fun t : ℝ => F z t) := by
        have h1 : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
            (UpperHalfPlane.ofComplex z) t) :=
          Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd (UpperHalfPlane.ofComplex z)
        have h2 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
          unfold Work.Asymptotics.gaussWeight; fun_prop
        exact h1.mul h2
      have h4 : Measurable (E.indicator (fun t : ℝ => F z t)) := hFmeas.indicator hEmeas
      simpa only using h4.aestronglyMeasurable
    have hdiffOn : DifferentiableOn ℂ
        (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), Set.indicator E (fun t' => F z t') t) U :=
      Work.Asymptotics.differentiableOn_integral_Ioi hUopen bound hbc hbb hdiff hmeas
        (fun z hz => Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
          hUopen hmeas hdiff z hz)
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    refine (hdiffOn.differentiableAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hxU] with z hz
    simp only [Function.comp_apply, hEdef, hFdef]
    exact layerLowDouble_piece_eq_indicatorIoi ℓ d p t₀ A₁ A₂ r z
  intro x hx
  simp only [layerLowDouble]
  exact ((((hpiece x hx).add
    (hdet₁.mdifferentiableAt (Metric.isOpen_ball.mem_nhds hx))).add
    (hdet₂.mdifferentiableAt (Metric.isOpen_ball.mem_nhds hx))).const_smul
    (Work.Asymptotics.sinSqC r)).add
    ((hres x).const_smul (Work.Asymptotics.sinSqC r)) |>.mdifferentiableWithinAt

end Work.LayerCont
