import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# `Work.EKLRelProduct.ae_eq_zero_of_preimage_integral`

A measurable function is `0` almost everywhere if its integral vanishes on the preimages of a
generating π-system.

Concretely: let `ν` be a finite measure on `SL₃(ℝ)`, `φ` measurable, `C` a π-system generating the
Borel σ-algebra which admits a countable cover `Bs` of the whole space, and let `ψ = G ∘ φ` with
`G` measurable and `ψ` bounded.  If `∫_{φ⁻¹ A} ψ = 0` for every `A ∈ C`, then `ψ = 0` a.e.

The proof pushes the two positive/negative parts of `ψ` forward along `φ` and uses
`Measure.ext_of_generateFrom_of_iUnion` on the resulting (finite) measures: they agree on `C`, hence
everywhere, and evaluating the resulting identity on `{G > 0}` and `{G < 0}` kills `ψ⁺` and `ψ⁻`.

The two helper lemmas `withDensity_ofReal_apply` and `map_withDensity_ofReal_apply` convert between
`Measure.withDensity` of `ENNReal.ofReal f` and the Bochner integral of `f`.
-/

open MeasureTheory
open Work.EKLContract

set_option linter.style.haveILetI false

namespace Work.EKLRelProduct

/-- The measure with density `ENNReal.ofReal f` w.r.t. `ν`, evaluated on a measurable set, is the
`ENNReal.ofReal` of the Bochner integral of `f` over that set (for `f` integrable and nonnegative
a.e.). -/
theorem withDensity_ofReal_apply {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {f : α → ℝ} (hfi : Integrable f ν) (hnn : 0 ≤ᵐ[ν] f) {s : Set α} (hs : MeasurableSet s) :
    (ν.withDensity (fun x => ENNReal.ofReal (f x))) s = ENNReal.ofReal (∫ x in s, f x ∂ν) := by
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (hfi.restrict (s := s)) (ae_restrict_of_ae hnn)]

/-- The pushforward of the previous measure along a measurable map `φ`, evaluated on a measurable
set `s`, is the `ENNReal.ofReal` of the Bochner integral of `f` over the preimage `φ ⁻¹' s`. -/
theorem map_withDensity_ofReal_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) {φ : α → β} (hφ : Measurable φ) {f : α → ℝ} (hfi : Integrable f ν)
    (hnn : 0 ≤ᵐ[ν] f) {s : Set β} (hs : MeasurableSet s) :
    (Measure.map φ (ν.withDensity (fun x => ENNReal.ofReal (f x)))) s
      = ENNReal.ofReal (∫ x in φ ⁻¹' s, f x ∂ν) := by
  rw [Measure.map_apply hφ hs, withDensity_ofReal_apply _ hfi hnn (hs.preimage hφ)]

theorem ae_eq_zero_of_preimage_integral {ν : MeasureTheory.Measure Work.EKLContract.SL3}
    (hνfin : ν Set.univ ≠ ⊤)
    {φ : Work.EKLContract.SL3 → Work.EKLContract.SL3} (hφ : Measurable φ)
    {C : Set (Set Work.EKLContract.SL3)} (hC : IsPiSystem C)
    (hgen : MeasurableSpace.generateFrom C = borel Work.EKLContract.SL3)
    {Bs : ℕ → Set Work.EKLContract.SL3} (hBs : ⋃ i, Bs i = Set.univ) (hBsC : ∀ i, Bs i ∈ C)
    {ψ : Work.EKLContract.SL3 → ℝ} (hψb : ∃ K, ∀ h, |ψ h| ≤ K)
    {G : Work.EKLContract.SL3 → ℝ} (hG : Measurable G) (hfac : ∀ h, ψ h = G (φ h))
    (hint : ∀ A ∈ C, ∫ h in φ ⁻¹' A, ψ h ∂ν = 0) :
    ψ =ᵐ[ν] 0 := by
  classical
  obtain ⟨K, hK⟩ := hψb
  have hK0 : 0 ≤ K := le_trans (abs_nonneg (ψ 1)) (hK 1)
  have hψmeas : Measurable ψ := by
    have hψeq : ψ = G ∘ φ := funext hfac
    rw [hψeq]; exact hG.comp hφ
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hνfin⟩
  -- the positive and negative parts of `ψ`
  let ψp : SL3 → ℝ := fun x => max (ψ x) 0
  let ψm : SL3 → ℝ := fun x => max (-(ψ x)) 0
  have hψpmeas : Measurable ψp := hψmeas.max measurable_const
  have hψmmeas : Measurable ψm := hψmeas.neg.max measurable_const
  have hψp_nn : ∀ x, 0 ≤ ψp x := fun x => le_max_right _ _
  have hψm_nn : ∀ x, 0 ≤ ψm x := fun x => le_max_right _ _
  have hψp_le : ∀ x, ψp x ≤ K := fun x => max_le (le_trans (le_abs_self (ψ x)) (hK x)) hK0
  have hψm_le : ∀ x, ψm x ≤ K := fun x => max_le (by linarith [hK x, neg_le_abs (ψ x)]) hK0
  have hψp_int : Integrable ψp ν :=
    Integrable.of_bound hψpmeas.aestronglyMeasurable K
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψp_nn x)]; exact hψp_le x))
  have hψm_int : Integrable ψm ν :=
    Integrable.of_bound hψmmeas.aestronglyMeasurable K
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψm_nn x)]; exact hψm_le x))
  -- the two finite measures on the target
  let μp : Measure SL3 := ν.withDensity (fun x => ENNReal.ofReal (ψp x))
  let μm : Measure SL3 := ν.withDensity (fun x => ENNReal.ofReal (ψm x))
  let mP : Measure SL3 := Measure.map φ μp
  let mN : Measure SL3 := Measure.map φ μm
  have hψp_nn_ae : 0 ≤ᵐ[ν] ψp := Filter.Eventually.of_forall hψp_nn
  have hψm_nn_ae : 0 ≤ᵐ[ν] ψm := Filter.Eventually.of_forall hψm_nn
  have hCmeas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    have h1 := MeasurableSpace.measurableSet_generateFrom hs
    rwa [hgen] at h1
  have hmapP : ∀ {s : Set SL3}, MeasurableSet s →
      mP s = ENNReal.ofReal (∫ x in φ ⁻¹' s, ψp x ∂ν) :=
    fun {s} hs => map_withDensity_ofReal_apply ν hφ hψp_int hψp_nn_ae hs
  have hmapN : ∀ {s : Set SL3}, MeasurableSet s →
      mN s = ENNReal.ofReal (∫ x in φ ⁻¹' s, ψm x ∂ν) :=
    fun {s} hs => map_withDensity_ofReal_apply ν hφ hψm_int hψm_nn_ae hs
  -- the two measures agree on the π-system `C`
  have h_eq : ∀ s ∈ C, mP s = mN s := by
    intro s hs
    have hsm := hCmeas s hs
    rw [hmapP hsm, hmapN hsm]
    have hkey : ∫ x in φ ⁻¹' s, ψp x ∂ν = ∫ x in φ ⁻¹' s, ψm x ∂ν := by
      have h0 : ∫ x in φ ⁻¹' s, ψp x ∂ν - ∫ x in φ ⁻¹' s, ψm x ∂ν = 0 := by
        rw [← integral_sub' (hψp_int.restrict) (hψm_int.restrict)]
        rw [show (∫ x in φ ⁻¹' s, (ψp - ψm) x ∂ν) = ∫ x in φ ⁻¹' s, ψ x ∂ν from
          setIntegral_congr_fun (hsm.preimage hφ) (fun x _ => by
            change max (ψ x) 0 - max (-(ψ x)) 0 = ψ x
            exact max_zero_sub_max_neg_zero_eq_self (ψ x))]
        exact hint s hs
      exact sub_eq_zero.mp h0
    rw [hkey]
  have hμB : ∀ i, mP (Bs i) ≠ ⊤ := by
    intro i
    rw [hmapP (hCmeas _ (hBsC i))]
    exact ENNReal.ofReal_ne_top
  have hm : mP = mN :=
    Measure.ext_of_generateFrom_of_iUnion C Bs hgen.symm hC hBs hBsC hμB h_eq
  -- endgame: evaluate `mP = mN` on the sign sets of `G`
  have hApos : MeasurableSet {y : SL3 | 0 < G y} := hG measurableSet_Ioi
  have hprepos : φ ⁻¹' {y : SL3 | 0 < G y} = {x : SL3 | 0 < ψ x} := by
    ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq]; rw [hfac x]
  have hψpos_meas : MeasurableSet {x : SL3 | 0 < ψ x} := hψmeas measurableSet_Ioi
  have hmP_Ap : mP {y : SL3 | 0 < G y} = ∫⁻ x, ENNReal.ofReal (ψp x) ∂ν := by
    rw [show mP {y | 0 < G y} = μp (φ ⁻¹' {y | 0 < G y}) from Measure.map_apply hφ hApos,
      hprepos,
      show μp {x | 0 < ψ x} = ∫⁻ x in {x | 0 < ψ x}, ENNReal.ofReal (ψp x) ∂ν from
        withDensity_apply _ hψpos_meas]
    rw [← lintegral_indicator hψpos_meas]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ {x : SL3 | 0 < ψ x}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hxle : ψ x ≤ 0 := not_lt.mp (by simpa using hx)
      have : ψp x = 0 := by change max (ψ x) 0 = 0; exact max_eq_right hxle
      simp [this]
  have hmN_Ap : mN {y : SL3 | 0 < G y} = 0 := by
    rw [show mN {y | 0 < G y} = μm (φ ⁻¹' {y | 0 < G y}) from Measure.map_apply hφ hApos,
      hprepos,
      show μm {x | 0 < ψ x} = ∫⁻ x in {x | 0 < ψ x}, ENNReal.ofReal (ψm x) ∂ν from
        withDensity_apply _ hψpos_meas]
    rw [← lintegral_indicator hψpos_meas]
    have hz : ({x : SL3 | 0 < ψ x}.indicator (fun x => ENNReal.ofReal (ψm x))) = 0 := by
      funext x
      by_cases hx : x ∈ {x : SL3 | 0 < ψ x}
      · rw [Set.indicator_of_mem hx]
        have hxpos : 0 < ψ x := hx
        have : ψm x = 0 := by change max (-(ψ x)) 0 = 0; exact max_eq_right (by linarith)
        rw [this, ENNReal.ofReal_zero]; simp
      · rw [Set.indicator_of_notMem hx]; simp
    rw [hz]; simp
  have hlP : ∫⁻ x, ENNReal.ofReal (ψp x) ∂ν = 0 := by
    rw [← hmP_Ap, hm, hmN_Ap]
  have hψp_ae : ψp =ᵐ[ν] 0 := by
    have h := (lintegral_eq_zero_iff' hψpmeas.ennreal_ofReal.aemeasurable).mp hlP
    filter_upwards [h] with x hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hψp_nn x)
  have hAneg : MeasurableSet {y : SL3 | G y < 0} := hG measurableSet_Iio
  have hpreneg : φ ⁻¹' {y : SL3 | G y < 0} = {x : SL3 | ψ x < 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq]; rw [hfac x]
  have hψneg_meas : MeasurableSet {x : SL3 | ψ x < 0} := hψmeas measurableSet_Iio
  have hmN_An : mN {y : SL3 | G y < 0} = ∫⁻ x, ENNReal.ofReal (ψm x) ∂ν := by
    rw [show mN {y | G y < 0} = μm (φ ⁻¹' {y | G y < 0}) from Measure.map_apply hφ hAneg,
      hpreneg,
      show μm {x | ψ x < 0} = ∫⁻ x in {x | ψ x < 0}, ENNReal.ofReal (ψm x) ∂ν from
        withDensity_apply _ hψneg_meas]
    rw [← lintegral_indicator hψneg_meas]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ {x : SL3 | ψ x < 0}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hxle : 0 ≤ ψ x := not_lt.mp (by simpa using hx)
      have : ψm x = 0 := by change max (-(ψ x)) 0 = 0; exact max_eq_right (by linarith)
      simp [this]
  have hmP_An : mP {y : SL3 | G y < 0} = 0 := by
    rw [show mP {y | G y < 0} = μp (φ ⁻¹' {y | G y < 0}) from Measure.map_apply hφ hAneg,
      hpreneg,
      show μp {x | ψ x < 0} = ∫⁻ x in {x | ψ x < 0}, ENNReal.ofReal (ψp x) ∂ν from
        withDensity_apply _ hψneg_meas]
    rw [← lintegral_indicator hψneg_meas]
    have hz : ({x : SL3 | ψ x < 0}.indicator (fun x => ENNReal.ofReal (ψp x))) = 0 := by
      funext x
      by_cases hx : x ∈ {x : SL3 | ψ x < 0}
      · rw [Set.indicator_of_mem hx]
        have : ψp x = 0 := by change max (ψ x) 0 = 0; exact max_eq_right (le_of_lt hx)
        rw [this, ENNReal.ofReal_zero]; simp
      · rw [Set.indicator_of_notMem hx]; simp
    rw [hz]; simp
  have hlM : ∫⁻ x, ENNReal.ofReal (ψm x) ∂ν = 0 := by
    rw [← hmN_An, ← hm, hmP_An]
  have hψm_ae : ψm =ᵐ[ν] 0 := by
    have h := (lintegral_eq_zero_iff' hψmmeas.ennreal_ofReal.aemeasurable).mp hlM
    filter_upwards [h] with x hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hψm_nn x)
  filter_upwards [hψp_ae, hψm_ae] with x hp hq
  change max (ψ x) 0 = 0 at hp
  change max (-(ψ x)) 0 = 0 at hq
  rw [← max_zero_sub_max_neg_zero_eq_self (ψ x), hp, hq, sub_zero]
  rfl

end Work.EKLRelProduct
