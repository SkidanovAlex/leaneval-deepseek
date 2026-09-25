import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haar" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-! ## The canonical lift `iwRep` in the fundamental domain `Ioc (−1/2) (1/2]`

The four elementary facts about `iwRep = AddCircle.liftIoc 1 (−1/2) id` used below.  They are
reproved here (rather than imported from `memLp_scaled_bump`/`mstKernel_helpers`) so that this
module depends only on the level-set vocabulary `mst_level_defs`. -/

private lemma iwRep_mem_Ioc_ae (ζ : Circ) : iwRep ζ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
  have h := (AddCircle.equivIoc (1 : ℝ) (-(1 / 2)) ζ).2
  have h' : (iwRep ζ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + 1) := h
  rwa [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num] at h'

private lemma iwRep_coe_of_mem_ae {y : ℝ} (hy : y ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :
    iwRep (y : Circ) = y := by
  have h := AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
    (f := fun x : ℝ => x) (x := y) (by
      rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]; exact hy)
  simpa only [iwRep] using h

private lemma coe_iwRep_ae (ζ : Circ) : ((iwRep ζ : ℝ) : Circ) = ζ := by
  have := AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := -(1 / 2 : ℝ)) (y := ζ)
  simpa only [iwRep, AddCircle.liftIoc, Set.domRestrict_def, Function.comp_apply] using this

/-- **The canonical lift is odd off the single point `ζ = 1/2`**: `iwRep (-ζ) = -iwRep ζ` whenever
`iwRep ζ ≠ 1/2`.  Indeed `w := iwRep ζ ∈ Ioc (−1/2) (1/2]` and `-w ∈ Ioc (−1/2) (1/2]` exactly when
`w ≠ 1/2`; in that case `-ζ = ((−w : ℝ) : Circle)` (`AddCircle.coe_neg`, `coe_iwRep`) and both
`−w` and `iwRep (-ζ)` are canonical representatives of `-ζ`. -/
private lemma iwRep_neg_of_ne_half {ζ : Circ} (hw : iwRep ζ ≠ 1 / 2) :
    iwRep (-ζ) = -iwRep ζ := by
  have hw_mem := iwRep_mem_Ioc_ae ζ
  rw [Set.mem_Ioc] at hw_mem
  have hwlt : iwRep ζ < 1 / 2 := lt_of_le_of_ne hw_mem.2 hw
  have hneg : -iwRep ζ ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [Set.mem_Ioc]
    exact ⟨by linarith, by linarith⟩
  have hcoe : ((-iwRep ζ : ℝ) : Circ) = -ζ := by
    rw [AddCircle.coe_neg, coe_iwRep_ae ζ]
  calc iwRep (-ζ) = iwRep (((-iwRep ζ : ℝ)) : Circ) := by rw [← hcoe]
    _ = -iwRep ζ := iwRep_coe_of_mem_ae hneg

/-- **The reflected level bump is the reflected level bump, pointwise off `ζ = 1/2`.**  With
`η' := fun x => η (-x)` one has `mstEta d χ η' s ζ = mstEta d χ η s (-ζ)` for every circle point
`ζ` with `iwRep ζ ≠ 1/2` (the only bad point being `ζ = 1/2`). -/
private lemma mstEta_reflect_of_ne_half (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) {ζ : Circ}
    (hw : iwRep ζ ≠ 1 / 2) :
    mstEta d χ (fun x : ℝ => η (-x)) s ζ = mstEta d χ η s (-ζ) := by
  simp only [mstEta_apply]
  rw [iwRep_neg_of_ne_half hw, mul_neg]

/-! ## The exceptional point `1/2` is null

`haarAddCircle (T := 1)` is `volume` on `AddCircle 1` (`AddCircle.volume_eq_smul_haarAddCircle`),
and the preimage of a singleton under the covering map `ℝ → AddCircle 1` meets any fundamental
domain of length `1` in at most one point (`AddCircle.coe_eq_coe_iff_of_mem_Ioc`), hence is null
(`Set.Subsingleton.measure_zero`); conclude with `AddCircle.measurePreserving_mk`. -/

private lemma haarAddCircle_singleton (x : Circ) : haar {x} = 0 := by
  rw [show (AddCircle.haarAddCircle (T := 1)) = (volume : Measure Circ) from by
    have h := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
    simpa using h.symm]
  have hmp := AddCircle.measurePreserving_mk (T := (1 : ℝ)) (1 / 2 : ℝ)
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable (measurableSet_singleton x)]
  rw [Measure.restrict_apply (hmp.measurable (measurableSet_singleton x))]
  apply Set.Subsingleton.measure_zero
  intro y hy z hz
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hy hz
  exact AddCircle.coe_eq_coe_iff_of_mem_Ioc (a := (1 / 2 : ℝ)) hy.2 hz.2
    |>.mp (by rw [hy.1, hz.1])

/-- **The exceptional point of `iwRep_neg_of_ne_half` is null**: any `ζ` with `iwRep ζ = 1/2` is
the point `↑(1/2)`, whose `haarAddCircle`-measure is zero. -/
private lemma ae_iwRep_ne_half : ∀ᵐ ζ ∂haar, iwRep ζ ≠ 1 / 2 := by
  rw [ae_iff]
  refine measure_mono_null (fun ζ hζ => ?_) (haarAddCircle_singleton ((1 / 2 : ℝ) : Circ))
  simp only [Set.mem_ofPred_eq, not_not] at hζ
  rw [Set.mem_singleton_iff]
  exact show ζ = ((1 / 2 : ℝ) : Circ) from by rw [← coe_iwRep_ae ζ, hζ]

/-- **The canonical lift is odd, almost everywhere** (the form of `iwRep_neg_ae` proved here): the
exceptional set is the single point `↑(1/2)`, which is null. -/
private lemma iwRep_neg_ae' :
    ∀ᵐ ζ ∂haar, iwRep (-ζ) = -iwRep ζ := by
  filter_upwards [ae_iwRep_ne_half] with ζ hζ
  exact iwRep_neg_of_ne_half hζ

/-- **The level bump with the reflected bump-function is the reflection of the level bump, almost
everywhere.** With `mstEta d χ η s ζ = η (2^{s(d-χ)} · iwRep ζ)` (`mst_level_defs.lean`), denoting
by `η' := fun x => η (-x)` the reflected bump, one has
  `(fun ζ => mstEta d χ η' s ζ) =ᵐ[haarAddCircle] fun ζ => mstEta d χ η s (-ζ)`,
i.e. `η' (c_s · iwRep ζ) = η (c_s · iwRep (-ζ))` for a.e. `ζ`, which holds off the single point
`ζ = 1/2` because the canonical lift `iwRep` is odd there: for `w := iwRep ζ ≠ 1/2` one has
`iwRep (-ζ) = -w` (`iwRep_coe_of_mem` applied to `-w ∈ Ioc (-1/2) (1/2]`, using
`-ζ = ((-w : ℝ) : Circle)`), and the exceptional point `1/2` is null.  No smoothness or support
hypothesis on `η` is needed. -/
theorem mstEta_neg_ae (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) :
    (fun ζ : Work.BourgainPlan.IonescuWainger.Circle => Work.BourgainPlan.Maximal.mstEta d χ (fun x : ℝ => η (-x)) s ζ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ζ => Work.BourgainPlan.Maximal.mstEta d χ η s (-ζ) := by
  filter_upwards [iwRep_neg_ae'] with ζ hζ
  simp only [mstEta_apply]
  rw [hζ, mul_neg]

end

end Work.BourgainPlan.Maximal
