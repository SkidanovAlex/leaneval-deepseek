import Mathlib
import Submission.Work.LayerCont.Coinc.CoincClean
import Submission.Work.LayerCont.Coinc.DetourCoinc
import Submission.Work.LayerCont.LowCoinc
import Submission.Work.LayerCont.SplitPoint

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Coinc

open Work.Asymptotics

/-- **The left detour equals the replaced interval integral at a residue-free coincidence,
in the pointwise (guarded) form.**

This is `Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc` with the ball-quantified
hypotheses replaced by the hypotheses at the single point `τ` (which is all its proof uses), so
that it can be applied when the orbit-exclusion and coincidence hypotheses are only available
under the extra guard `1 < τ.re`. -/
theorem detourLeftC_eq_interval_of_coinc_pointwise (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r c A ξ : ℝ} (hA : 0 < A) (hξ : 0 < ξ) (hcA : 0 < c - A)
    (τ : UpperHalfPlane)
    (hclean : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ coincℂ τ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z))
    (hcoinc : coincℂ τ ∈ openLeftRectℂ c A ξ)
    (hdeg : Work.Residues.jprime τ ≠ 0) :
    detourLeftC ℓ d r c A ξ τ = ∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ 0 v := by
  set z₀ : ℂ := coincℂ τ with hz₀
  have hclean' : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ z₀ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) :=
    fun z hz hz' => hclean z hz (by rwa [hz₀] at hz')
  have hmem : z₀ ∈ openLeftRectℂ c A ξ := by rw [hz₀]; exact hcoinc
  simp only [openLeftRectℂ, Set.mem_ofPred_eq] at hmem
  obtain ⟨hre₁, hre₂, him₁, him₂⟩ := hmem
  have hcont : ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ \ {z₀}) :=
    dlcc_continuousOn_generic ℓ d hd r τ c A ξ z₀ hcA hclean'
  have hhol : ∀ z : ℂ, (-ξ) < z.re → z.re < 0 → c - A < z.im → z.im < c + A → z ≠ z₀ →
      DifferentiableAt ℂ (kerForm ℓ d r τ) z :=
    fun z h1 h2 h3 h4 hz =>
      dlcc_differentiableAt_generic ℓ d hd r τ c A ξ z₀ hcA hclean' z ⟨h1, h2, h3, h4⟩ hz
  have hres : Filter.Tendsto (fun z : ℂ => (z - z₀) * kerForm ℓ d r τ z)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    simpa only [← hz₀] using tendsto_coinc_residue ℓ d hd r τ hdeg
  have hrect := rectInt_eq_residue (kerForm ℓ d r τ) z₀ 0 (-ξ) 0 (c - A) (c + A)
    hre₁ hre₂ him₁ him₂ hcont hhol hres
  rw [mul_zero] at hrect
  rw [dlcc_integral_edgeV ℓ d r τ 0 (c - A) (c + A) hcA (by linarith)]
  rw [detourLeftC,
    dlcc_integral_edgeH_neg ℓ d r τ ξ (c - A) hξ hcA,
    dlcc_integral_edgeV ℓ d r τ (-ξ) (c - A) (c + A) hcA (by linarith),
    dlcc_integral_edgeH_neg ℓ d r τ ξ (c + A) hξ (by linarith)]
  linear_combination -hrect

/-- **Far-side twin of `Work.LayerCont.layerLowCoinc_eq_layerLow`** (`1 < τ.re` instead of
`τ.re < 1`).

The near-side original (`Submission/Work/LayerCont/LowCoinc.lean`, sorry-free) proves
`layerLowCoinc ℓ d t₀ A₂ ξ₂ r τ = layerLow ℓ d τ r` for `τ.re < 1`; it removes the interval
`I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)` from `(0,1]`, replaces it by the residue-free left detour
`Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ` and uses
`Work.Asymptotics.detourLeftC_eq_interval_of_clean` under an *orbit-free* hypothesis.

On the far side the coincidence `coincℂ τ = ST⁻¹τ` has negative real part and lies in the swept
rectangle, so:
* the orbit-exclusion is relaxed to "the only translate of `τ` in `leftRect t₀⁻¹ A₂ ξ₂` is
  `ModularGroup.S • ((-1:ℝ) +ᵥ τ)`";
* the detour identity becomes `Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc`
  (hypotheses `hclean`, `hcoinc`, `hdeg`), and the `j`-cleanliness it needs is
  `Work.LayerCont.Coinc.dlcc_clean_coinc`;
* cleanliness of `I₂` (needed to bound `∫_{I₂}` via `Work.LayerCont.GapBoundKaxisLow`) is
  *derived* from `hcl` and `hcoinc` by `Work.LayerCont.Coinc.jInvariantFun_ne_imagAxis_of_coinc`;
* `hcleanIoc` is therefore needed only on `(0,1] \ I₂`; combined with the previous point it gives
  cleanliness on all of `(0,1]`, so `Work.LayerCont.KaxisBoundedIocBall` dominates every piece.

The rest is the split `∫_{(0,1]} = ∫_{(0,1]\I₂} + ∫_{I₂}` exactly as in the near-side proof.
Copy `layerLowCoinc_eq_layerLow` and adjust.  Note `Work.LayerCont.DetourNoOrbit` must be
imported for `Work.Asymptotics.detourLeftC_eq_interval_of_noOrbit`, and
`Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc_far` is the guarded (usable) form of the
coincidence detour identity. -/
theorem layerLowCoinc_eq_layerLow_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {t₀ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂)
    (hε : 0 < ε) (hA₂inv : A₂ < t₀⁻¹) (hI₂low : t₀⁻¹ + A₂ < 1)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ t₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.Residues.jprime τ ≠ 0)
    (hcleanIoc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.LayerCont.layerLowCoinc ℓ d t₀ A₂ ξ₂ r τ = Work.Asymptotics.layerLow ℓ d τ r := by
  intro τ hτ hτre
  set I₂ : Set ℝ := Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) with hI₂def
  set E : Set ℝ := (Set.Ioc (0 : ℝ) 1) \ I₂ with hEdef
  set f : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
    * Work.Asymptotics.gaussWeight r t with hfdef
  have hcA : 0 < t₀⁻¹ - A₂ := by linarith
  have hI₂sub : I₂ ⊆ Set.Ioc (0 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1, hA₂inv], by linarith [hx.2, hI₂low]⟩
  have hEmeas : MeasurableSet E := by rw [hEdef]; exact measurableSet_Ioc.diff measurableSet_Ioo
  have hI₂meas : MeasurableSet I₂ := by rw [hI₂def]; exact measurableSet_Ioo
  have hfm : Measurable f := by
    rw [hfdef]
    exact (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)
  -- ### the detour identity (residue-free, at the removable coincidence)
  have hdet : Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ = ∫ v in I₂, f v := by
    rw [detourLeftC_eq_interval_of_coinc_pointwise ℓ d hd (r := r) (c := t₀⁻¹) (A := A₂)
      (ξ := ξ₂) hA₂ hξ₂ hcA τ
      (dlcc_clean_coinc τ t₀⁻¹ A₂ ξ₂ hcA (hcl τ hτ hτre))
      (hcoinc τ hτ hτre) (hdeg τ hτ hτre)]
    refine MeasureTheory.setIntegral_congr_fun hI₂meas (fun v hv => ?_)
    have hvpos : 0 < v := by linarith [hv.1, hA₂inv]
    rw [hfdef]
    exact edgeV_zero_eq ℓ d r τ hvpos
  -- ### bounds on the two pieces
  obtain ⟨C₁, hC₁nn, hC₁b⟩ := KaxisBoundedLowBall ℓ d hd τ 0 t₀ A₂ hA₂ hA₂inv hI₂low
    (fun w hw t ht htE => by
      have hw' : w = τ := by simpa using hw
      rw [hw']
      exact hcleanIoc τ hτ hτre t ht htE)
  obtain ⟨C₂, hC₂nn, hC₂b⟩ := GapBoundKaxisLow ℓ d hd (K := {τ}) isCompact_singleton
    (δ := (t₀⁻¹ - A₂) / 2) (T := t₀⁻¹ + A₂) (by linarith)
    (fun w hw t ht htI => by
      have hw' : w = τ := by simpa using hw
      rw [hw']
      by_cases htle : t ≤ t₀⁻¹ - A₂
      · exact hcleanIoc τ hτ hτre t ht
          ⟨⟨by linarith [htI.1, hcA], by linarith [htle, hI₂low, hA₂]⟩,
            fun hmem => by linarith [hmem.1, htle]⟩
      · exact jInvariantFun_ne_imagAxis_of_coinc τ (hcl τ hτ hτre)
          (coincℂ_re_neg_of_mem_openLeftRectℂ (hcoinc τ hτ hτre)) ht
          (imagAxis_mem_leftRect ht hξ₂ ⟨by linarith [not_le.mp htle], htI.2⟩))
  have hbE : ∀ t ∈ E, ‖f t‖ ≤ max C₁ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (ht.1.1).le
    rw [hfdef, norm_mul]
    exact le_trans (mul_le_mul (hC₁b τ (Metric.mem_closedBall.mpr (by simp)) t ht)
      (norm_gaussWeight_le_one r t ht0) (norm_nonneg _) hC₁nn) (by rw [mul_one]; exact le_max_left _ _)
  have hb2 : ∀ t ∈ I₂, ‖f t‖ ≤ max C₂ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_trans (by linarith [ht.1, hA₂inv]) ht.1)
    rw [hfdef, norm_mul]
    have hδ : (t₀⁻¹ - A₂) / 2 ≤ t := by linarith [ht.1, hA₂inv]
    exact le_trans (mul_le_mul (hC₂b τ t (Set.mem_singleton τ) ⟨hδ, ht.2.le⟩)
      (norm_gaussWeight_le_one r t ht0) (norm_nonneg _) hC₂nn)
      (by rw [mul_one]; exact le_max_left _ _)
  -- ### integrability of the two pieces
  have hI₂fin : volume I₂ ≠ ⊤ := by
    have h : volume I₂ ≤ volume (Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) :=
      measure_mono Set.Ioo_subset_Icc_self
    rw [Real.volume_Icc] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hEfin : volume E ≠ ⊤ := by
    have h : volume E ≤ volume (Set.Ioc (0 : ℝ) 1) := measure_mono Set.sdiff_subset
    rw [Real.volume_Ioc] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hIntE : IntegrableOn f E := by
    haveI : IsFiniteMeasure (volume.restrict E) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact lt_of_le_of_ne le_top hEfin⟩
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => max C₁ 0)
      (MeasureTheory.integrable_const _) hfm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hEmeas] with t ht
    exact hbE t ht
  have hInt2 : IntegrableOn f I₂ := by
    haveI : IsFiniteMeasure (volume.restrict I₂) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact lt_of_le_of_ne le_top hI₂fin⟩
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => max C₂ 0)
      (MeasureTheory.integrable_const _) hfm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hI₂meas] with t ht
    exact hb2 t ht
  -- ### the split of the low range
  have hunion : (Set.Ioc (0 : ℝ) 1 \ I₂) ∪ I₂ = Set.Ioc (0 : ℝ) 1 := by
    rw [Set.diff_union_self]
    exact Set.union_eq_left.mpr hI₂sub
  have hsplit : (∫ t in Set.Ioc (0 : ℝ) 1, f t ∂volume)
      = (∫ t in (Set.Ioc (0 : ℝ) 1) \ I₂, f t ∂volume)
        + (∫ t in I₂, f t ∂volume) := by
    have h := MeasureTheory.setIntegral_union (s := Set.Ioc (0 : ℝ) 1 \ I₂) (t := I₂)
      Set.disjoint_sdiff_left hI₂meas hIntE hInt2
    rw [hunion] at h
    exact h
  -- ### `layerLow` as a set integral
  have hll : Work.Asymptotics.layerLow ℓ d τ r
      = Work.Asymptotics.sinSqC r * ∫ t in Set.Ioc (0 : ℝ) 1, f t := by
    rw [Work.Asymptotics.layerLow, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
  rw [layerLowCoinc, hll, hdet, hsplit]

end Work.LayerCont.Coinc
