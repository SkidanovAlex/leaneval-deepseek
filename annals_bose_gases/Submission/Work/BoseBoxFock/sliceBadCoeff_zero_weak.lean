import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SliceBadCoeffAux
import Submission.Work.BoseBoxFock.sector_XSpow_width_holds_weak
import Submission.Work.BoseBoxFock.slice_Xpow_fubini_bdd_cb_weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weak-state twin of `Work.BoseBoxFock.sliceBadCoeff_zero`

`Work.BoseBoxFock.box_to_model` quantifies over `Φ : Work.BoseKinLoc.BoxState n ℓ`, a class with
no support hypothesis, so the BF3c `ExcWindow` chain must be run at the box restriction
`Θ = Φ·1_abox` (`Work.BoseBoxFock.boxRestrictState`), which is measurable and everywhere bounded
but *not* continuous.  This module re-runs the two bottom nodes of that chain

* `sliceBadCoeff_zero_aux_weak` — the assembly of `sliceBadCoeff_zero_aux` with the state
  hypotheses `Continuous Φ` + `tsupport Φ ⊆ abox n ℓ` replaced by
  `Measurable Φ` + `∃ C, ∀ x, |Φ x| ≤ C` + `Function.support Φ ⊆ abox n ℓ`;
* `sliceBadCoeff_zero_weak` — the same replacement in `sliceBadCoeff_zero`, whose sector-moment
  input `sector_XSpow_width_holds_kf` is replaced by its weak twin
  `Work.BoseBoxFock.sector_XSpow_width_holds_weak`.

Everything else (the `∫⁻`-moment limit, `ae_ae_slice_regular`, `slice_coeff_pointwise_bound`,
`slotExact_ae_bounded_of_bounded`, and the weak Fubini identity
`Work.BoseBoxFock.slice_Xpow_fubini_bdd_cb_weak`) is state-class-free.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped ENNReal Topology

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem sliceBadCoeff_zero_aux_weak (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦm : Measurable Φ)
    (hΦb : ∃ C : ℝ, ∀ x, |Φ x| ≤ C)
    (hΦsupp : Function.support Φ ⊆ Submission.BoseGases.abox n ℓ)
    {M : ℝ} (hM : 0 ≤ M)
    {m : ℕ} [NeZero m] {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) (α : Fin m →₀ ℕ)
    (hbad : ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ))
    {Bval : ℝ} (hBval : 0 ≤ Bval)
    (hsec : ∀ j : ℕ,
      (∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.BoseBoxFock.XSpow ℓ S j (slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
        ≤ M ^ (2 * j) * (Bval)) :
    ∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      ‖∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
          * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2 = 0 := by
  classical
  -- the complexified state is `L^∞` (measurable, everywhere bounded), so the sector is a.e.
  -- strongly measurable and a.e. bounded by `slotExact_ae_bounded_of_bounded`
  have hΦb' : ∃ C : ℝ, ∀ x, |Φ x| ≤ C := hΦb
  obtain ⟨B, hB⟩ := hΦb'
  have hΨbdd : ∀ x, ‖(fun x => ((Φ x : ℝ) : ℂ)) x‖ ≤ max B 0 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hB x) (le_max_left B 0)
  have hΨm : MemLp (fun x => ((Φ x : ℝ) : ℂ)) ⊤
      (volume : Measure (Fin n → Ω)) :=
    memLp_top_of_bound (Complex.continuous_ofReal.measurable.comp hΦm).aestronglyMeasurable
      (max B 0) (Filter.Eventually.of_forall hΨbdd)
  obtain ⟨hΘmeas, C, hΘbdd⟩ := slotExact_ae_bounded_of_bounded hbdd hsupp S hΨm
  -- ## numeric facts on the excited-slot count `S.card - α 0`
  have hk1 : ⌊M⌋₊ + 1 ≤ S.card - α 0 := by
    have h3 : ⌊M⌋₊ < S.card - α 0 := by exact_mod_cast hbad
    omega
  have hkpos : 0 < S.card - α 0 := by omega
  have hRpos : 0 < (((S.card - α 0 : ℕ)) : ℝ) := by exact_mod_cast hkpos
  have hMk : M < (((S.card - α 0 : ℕ)) : ℝ) := by
    have h1 : (⌊M⌋₊ : ℝ) + 1 ≤ (((S.card - α 0 : ℕ)) : ℝ) := by exact_mod_cast hk1
    have h2 : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
    linarith
  have hratio_lt : M / (((S.card - α 0 : ℕ)) : ℝ) < 1 := (div_lt_one hRpos).mpr hMk
  have hratio_nn : 0 ≤ M / (((S.card - α 0 : ℕ)) : ℝ) := div_nonneg hM hRpos.le
  -- ## regularity of the slices, and honesty of the sliced iterate marginal
  have hslicereg := ae_ae_slice_regular (S := S)
    (Θ := slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) (C := C) hΘmeas hΘbdd
  have hInt_j : ∀ j : ℕ, Integrable (fun y : {i // i ∉ S} → Ω =>
      ∫ u in Submission.BoseGases.abox S.card ℓ,
        ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
          (sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) u‖ ^ 2) :=
    fun j => (slice_Xpow_fubini_bdd_cb_weak ℓ hℓ hsupp hbdd S hΦm hΦb hΦsupp j).2
  -- ## the `j`-th moment bound on the coefficient, in `∫⁻` form
  have key : ∀ j : ℕ,
      (∫⁻ y : {i // i ∉ S} → Ω, ENNReal.ofReal
          (‖∫ u in Submission.BoseGases.abox S.card ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
              * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2))
        ≤ ENNReal.ofReal ((∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
            * (Bval)
            * ((M / (((S.card - α 0 : ℕ)) : ℝ)) ^ 2) ^ j) := by
    intro j
    have hA0nn : 0 ≤ ∫ u in Submission.BoseGases.abox S.card ℓ,
        ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2 :=
      integral_nonneg (fun u => sq_nonneg _)
    have hpt : ∀ᵐ y : {i // i ∉ S} → Ω,
        ‖∫ u in Submission.BoseGases.abox S.card ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
              * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2
          ≤ ((∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
              / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j))
            * (∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
                  (sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) u‖ ^ 2) := by
      filter_upwards [hslicereg] with y hy
      obtain ⟨hym, hyb⟩ := hy
      have hgm : AEStronglyMeasurable (sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y)
          (volume : Measure (Fin S.card → Ω)) := by
        show AEStronglyMeasurable (fun u : Fin S.card → Ω =>
          slotExact e S (fun x => ((Φ x : ℝ) : ℂ))
            (pairCoord S (fun i => u (S.equivFin i)) y)) (volume : Measure (Fin S.card → Ω))
        exact hym
      have hgb : ∀ᵐ u ∂(volume : Measure (Fin S.card → Ω)),
          ‖sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ≤ C := by
        show ∀ᵐ u ∂(volume : Measure (Fin S.card → Ω)),
          ‖slotExact e S (fun x => ((Φ x : ℝ) : ℂ))
            (pairCoord S (fun i => u (S.equivFin i)) y)‖ ≤ C
        exact hyb
      exact slice_coeff_pointwise_bound (ℓ := ℓ) hℓ he hbdd hsupp hc (α := α) (j := j)
        (g := sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) (C := C) hgm hgb hkpos
    have hc₀nn : 0 ≤ (∫ u in Submission.BoseGases.abox S.card ℓ,
          ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
        / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j) :=
      div_nonneg hA0nn (by positivity)
    calc (∫⁻ y : {i // i ∉ S} → Ω, ENNReal.ofReal
            (‖∫ u in Submission.BoseGases.abox S.card ℓ,
              (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
                * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2))
        ≤ ∫⁻ y : {i // i ∉ S} → Ω, ENNReal.ofReal
            (((∫ u in Submission.BoseGases.abox S.card ℓ,
                  ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
                / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j))
              * (∫ u in Submission.BoseGases.abox S.card ℓ,
                  ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
                    (sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) u‖ ^ 2)) :=
          lintegral_mono_ae
            (Filter.Eventually.mono hpt (fun y hy => ENNReal.ofReal_le_ofReal hy))
      _ = ENNReal.ofReal ((∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
              / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j))
            * ∫⁻ y : {i // i ∉ S} → Ω, ENNReal.ofReal
              (∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
                  (sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) u‖ ^ 2) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr (fun y => ?_)
          rw [ENNReal.ofReal_mul hc₀nn]
      _ = ENNReal.ofReal ((∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
              / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j))
            * ENNReal.ofReal (∫ y : {i // i ∉ S} → Ω,
                ∫ u in Submission.BoseGases.abox S.card ℓ,
                  ‖XSpow ℓ (Finset.univ : Finset (Fin S.card)) j
                    (sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y) u‖ ^ 2) := by
          refine congrArg _ ?_
          exact (ofReal_integral_eq_lintegral_ofReal (hInt_j j)
            (Filter.Eventually.of_forall
              (fun y => integral_nonneg (fun u => sq_nonneg _)))).symm
      _ = ENNReal.ofReal ((∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
              / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j))
            * ENNReal.ofReal (∫ x in Submission.BoseGases.abox n ℓ,
                ‖XSpow ℓ S j (slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2) := by
          rw [(slice_Xpow_fubini_bdd_cb_weak ℓ hℓ hsupp hbdd S hΦm hΦb hΦsupp j).1]
      _ ≤ ENNReal.ofReal ((∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
              / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j))
            * ENNReal.ofReal (M ^ (2 * j) * (Bval)) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
          exact hsec j
      _ = ENNReal.ofReal (((∫ u in Submission.BoseGases.abox S.card ℓ,
                ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
              / (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j))
            * (M ^ (2 * j) * (Bval))) := by
          rw [← ENNReal.ofReal_mul hc₀nn]
      _ = ENNReal.ofReal ((∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
            * (Bval)
            * ((M / (((S.card - α 0 : ℕ)) : ℝ)) ^ 2) ^ j) := by
          congr 1
          have hM2 : M ^ (2 * j) = (M ^ 2) ^ j := pow_mul M 2 j
          have hR2 : (((S.card - α 0 : ℕ)) : ℝ) ^ (2 * j)
              = ((((S.card - α 0 : ℕ)) : ℝ) ^ 2) ^ j := pow_mul _ 2 j
          have hr : ((M / (((S.card - α 0 : ℕ)) : ℝ)) ^ 2) ^ j
              = (M ^ 2) ^ j / ((((S.card - α 0 : ℕ)) : ℝ) ^ 2) ^ j := by
            rw [← pow_mul, div_pow, hM2, hR2]
          rw [hM2, hR2, hr]
          have hne : ((((S.card - α 0 : ℕ)) : ℝ) ^ 2) ^ j ≠ 0 := by positivity
          field_simp
          try ring
  -- ## the limit
  have hYle : ∀ j : ℕ,
      (∫ y : {i // i ∉ S} → Ω, ‖∫ u in Submission.BoseGases.abox S.card ℓ,
          (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
            * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2)
        ≤ (∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
            * (Bval)
            * ((M / (((S.card - α 0 : ℕ)) : ℝ)) ^ 2) ^ j := by
    intro j
    by_cases hInt : Integrable (fun y : {i // i ∉ S} → Ω =>
        ‖∫ u in Submission.BoseGases.abox S.card ℓ,
          (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
            * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2)
    · have h1 : (∫ y : {i // i ∉ S} → Ω, ‖∫ u in Submission.BoseGases.abox S.card ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
              * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2)
          = (∫⁻ y : {i // i ∉ S} → Ω, ENNReal.ofReal
              (‖∫ u in Submission.BoseGases.abox S.card ℓ,
                (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
                  * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2)).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun y => sq_nonneg _))
          hInt.aestronglyMeasurable
      rw [h1]
      refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (key j)) ?_
      rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg
        (integral_nonneg (fun u => sq_nonneg _))
        hBval) (pow_nonneg (sq_nonneg _) j))]
    · rw [integral_undef hInt]
      exact mul_nonneg (mul_nonneg (integral_nonneg (fun u => sq_nonneg _))
        hBval) (pow_nonneg (sq_nonneg _) j)
  have hlim : Filter.Tendsto (fun j : ℕ =>
      (∫ u in Submission.BoseGases.abox S.card ℓ,
          ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
        * (Bval)
        * ((M / (((S.card - α 0 : ℕ)) : ℝ)) ^ 2) ^ j) Filter.atTop (𝓝 0) := by
    have h0 : 0 ≤ (M / (((S.card - α 0 : ℕ)) : ℝ)) ^ 2 := sq_nonneg _
    have h1 : (M / (((S.card - α 0 : ℕ)) : ℝ)) ^ 2 < 1 := by
      nlinarith [hratio_lt, hratio_nn]
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul
      ((∫ u in Submission.BoseGases.abox S.card ℓ,
          ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
        * (Bval))
    simpa using h2
  have hY0 : (∫ y : {i // i ∉ S} → Ω, ‖∫ u in Submission.BoseGases.abox S.card ℓ,
      (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
        * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2) = 0 := by
    refine le_antisymm ?_ (integral_nonneg (fun y => sq_nonneg _))
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hYle
  -- ## transport the box integral to the unrestricted one
  have hMαsupp : Function.support (Work.BoseDict.modeProd e S.card α)
      ⊆ Submission.BoseGases.abox S.card ℓ := modeProd_support_subset_abox hℓ hsupp S.card α
  have hconv : ∀ y : {i // i ∉ S} → Ω,
      (∫ u : Fin S.card → Ω, (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
          * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u)
        = ∫ u in Submission.BoseGases.abox S.card ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
              * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u := by
    intro y
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox S.card ℓ)
      (f := fun u => (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
        * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u) (fun u hu => by
          have h0 : Work.BoseDict.modeProd e S.card α u = 0 := by
            by_contra hne
            exact hu (hMαsupp (Function.mem_support.mpr hne))
          rw [h0, map_zero, zero_mul])).symm
  rw [← hY0]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  show ‖∫ u : Fin S.card → Ω, (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
        * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2
      = ‖∫ u in Submission.BoseGases.abox S.card ℓ,
          (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
            * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2
  rw [hconv y]


/-- **`ExcWindow`, step 6 of the BF3c pipeline at the weak state class.**  The single change with
respect to `Work.BoseBoxFock.sliceBadCoeff_zero` is the state class: `Continuous Φ` and
`tsupport Φ ⊆ abox n ℓ` become `Measurable Φ`, a global bound and `support Φ ⊆ abox n ℓ` (the
class of the box restriction `Θ = Φ·1_abox`).  The sector-moment input is
`Work.BoseBoxFock.sector_XSpow_width_holds_weak`, the weak twin of
`Work.BoseBoxFock.sector_XSpow_width_holds_kf`. -/
theorem sliceBadCoeff_zero_weak (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hΦm : Measurable Φ) (hΦb : ∃ C : ℝ, ∀ x, |Φ x| ≤ C)
    (hΦsupp : Function.support Φ ⊆ Submission.BoseGases.abox n ℓ)
    {M : ℝ} (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    {m : ℕ} [NeZero m] {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) (α : Fin m →₀ ℕ)
    (hdeg : α.sum (fun _ k => k) = S.card)
    (hbad : ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ)) :
    ∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      ‖∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
          * sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2 = 0 := by
  refine sliceBadCoeff_zero_aux_weak ℓ hℓ hΦm hΦb hΦsupp hM he hbdd hsupp hc S α hbad
    (Bval := ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
    (integral_nonneg (fun x => sq_nonneg (Φ x))) ?_
  intro j
  exact sector_XSpow_width_holds_weak ℓ hℓ S hΦm hΦb hM hmom he hbdd hsupp hc j

end Work.BoseBoxFock
