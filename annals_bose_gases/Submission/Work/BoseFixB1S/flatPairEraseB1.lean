import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotDefs
import Submission.Work.FibreWord.SliceAE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary helpers -/

/-- A continuous state is bounded on the compact analysis box. -/
private theorem fp_abox_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox N ℓ, |Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => by
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)⟩

/-- Inserting a point of `A` into a slot of a box configuration keeps it in the box. -/
private theorem fp_update_mem_abox {N : ℕ} {ℓ : ℝ} {A : Set E3} (hAc : A ⊆ acube ℓ)
    {x : X N} (hx : x ∈ abox N ℓ) (k : Fin N) {z : E3} (hz : z ∈ A) :
    Function.update x k z ∈ abox N ℓ := by
  intro m
  rw [Function.update_apply]
  by_cases hm : m = k
  · rw [if_pos hm]; exact hAc hz
  · rw [if_neg hm]; exact hx m

/-- `P_kΦ = 1_A(x k)·(one-slot mean)` (the definition of the box projection in mean form). -/
private theorem fp_boxPInd_eq (volA : ℝ) (A : Set E3) {N : ℕ} (k : Fin N)
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd volA A k Φ x = Aind A (x k) * oneMean volA A k Φ x := by
  unfold Work.UBBInputs8.boxPInd Aind oneMean
  ring

/-- `Q_kΦ = 1_A(x k)·Φ − P_kΦ` (definitional). -/
private theorem fp_boxQInd_eq (volA : ℝ) (A : Set E3) {N : ℕ} (k : Fin N)
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxQInd volA A k Φ x
      = Aind A (x k) * Φ x - Work.UBBInputs8.boxPInd volA A k Φ x := rfl

/-- `P_iP_jΦ = 1_A(x i)·1_A(x j)·(two-slot mean)` for `i ≠ j` (pure definitional bookkeeping). -/
private theorem fp_boxPInd_twoMean {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = Aind A (x i) * Aind A (x j) * twoMean volA A i j Φ x := by
  have hinner : ∀ z : E3, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i z)
      = Aind A (x j)
        * ((1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) := by
    intro z
    rw [Work.UBBInputs8.boxPInd]
    have h1 : (Function.update x i z) j = x j := by
      rw [Function.update_apply, if_neg]
      exact fun h => hij h.symm
    rw [h1]
    unfold Aind
    ring
  rw [Work.UBBInputs8.boxPInd]
  rw [show (∫ z in A, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i z))
      = ∫ z in A, Aind A (x j)
          * ((1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) from by
    apply MeasureTheory.integral_congr_ae; filter_upwards with z; exact hinner z]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul]
  unfold twoMean Aind
  ring

/-- The `k`-slot slice of a measurable state bounded on the box is integrable over `A ⊆ acube ℓ`
(at box configurations). -/
private theorem fp_slotInt_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (k : Fin N) (x : X N) (hx : x ∈ abox N ℓ)
    {f : X N → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ y ∈ abox N ℓ, |f y| ≤ C) :
    IntegrableOn (fun z : E3 => f (Function.update x k z)) A volume := by
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  refine MeasureTheory.IntegrableOn.of_bound hfin ?_ C ?_
  · exact (hf.comp (by fun_prop : Measurable (fun z : E3 => Function.update x k z))).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall (fun z hz => by
      rw [Real.norm_eq_abs]
      exact hb _ (fp_update_mem_abox hAc hx k hz))

/-- **The slot mean of an a.e.-vanishing state vanishes a.e.**  Cut the state by the box
indicator (so that it vanishes `volume`-a.e. on the whole space), apply the fibre slice-a.e. lemma
`Work.FibreWord.ae_eq_slice_set`, and undo the indicator on the box (an inserted configuration
stays in the box). -/
private theorem fp_sliceMean_ae_zero {N : ℕ} {ℓ : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (k : Fin N) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    (hΨ : Ψ =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)] 0) :
    (fun x : X N => ∫ z in A, Ψ (Function.update x k z))
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)] 0 := by
  classical
  have hbox : MeasurableSet (abox N ℓ) := Submission.BoseGases.abox_measurable N ℓ
  -- the box truncation vanishes a.e. on the whole space
  have hglob : (fun y : X N => (abox N ℓ).indicator Ψ y) =ᵐ[volume] 0 := by
    have hΨ' : ∀ᵐ y ∂(MeasureTheory.volume.restrict (abox N ℓ)), Ψ y = 0 := hΨ
    have hnull : (MeasureTheory.volume.restrict (abox N ℓ)) {y : X N | Ψ y ≠ 0} = 0 := by
      simpa using MeasureTheory.ae_iff.mp hΨ'
    refine MeasureTheory.ae_iff.mpr ?_
    show (volume : Measure (X N)) {y : X N | (abox N ℓ).indicator Ψ y ≠ 0} = 0
    have hset : {y : X N | (abox N ℓ).indicator Ψ y ≠ 0}
        = (abox N ℓ) ∩ {y : X N | Ψ y ≠ 0} := by
      ext y
      by_cases hy : y ∈ abox N ℓ
      · rw [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.indicator_of_mem hy]
        exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩
      · rw [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.indicator_of_notMem hy]
        exact ⟨fun h => absurd rfl h, fun h => absurd h.1 hy⟩
    rw [hset, show (abox N ℓ) ∩ {y : X N | Ψ y ≠ 0}
        = {y : X N | Ψ y ≠ 0} ∩ (abox N ℓ) from Set.inter_comm _ _]
    have h1 : (MeasureTheory.volume.restrict (abox N ℓ)) {y : X N | Ψ y ≠ 0}
        = MeasureTheory.volume ({y : X N | Ψ y ≠ 0} ∩ abox N ℓ) :=
      MeasureTheory.Measure.restrict_apply (hΨm (measurableSet_singleton 0).compl)
    rw [h1] at hnull
    exact hnull
  -- the slice integral of the truncation vanishes a.e.
  have hslice := Work.FibreWord.ae_eq_slice_set k A hglob
  have hslice0 : (fun x : X N => ∫ z in A, (abox N ℓ).indicator Ψ (Function.update x k z))
      =ᵐ[volume] 0 := by
    have hzero : (fun x : X N => ∫ z in A, (0 : X N → ℝ) (Function.update x k z))
        = (0 : X N → ℝ) := by
      funext x
      simp
    rwa [hzero] at hslice
  -- restrict to the box, and undo the indicator
  filter_upwards [hslice0.filter_mono (MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_le_self (s := abox N ℓ))),
    MeasureTheory.ae_restrict_mem hbox] with x hx hxbox
  have hcongr : (∫ z in A, (abox N ℓ).indicator Ψ (Function.update x k z))
      = ∫ z in A, Ψ (Function.update x k z) :=
    MeasureTheory.setIntegral_congr_fun hA (fun z hz => by
      rw [Set.indicator_of_mem (fp_update_mem_abox hAc hxbox k hz)])
  rw [← hcongr]
  exact hx

/-! ## 2. The target -/

theorem flatPairEraseB1 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) {M : ℕ} (hM : 1 ≤ M) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0) {i j : Fin n} (hij : i ≠ j) : (fun x : Submission.BoseGases.X n => (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) * Φ x - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) j Φ) x) =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0 := by
  classical
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal :=
    (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u).trans
      (MeasureTheory.measureReal_def _ _)
  have hVnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [hVeq]; exact ENNReal.toReal_nonneg
  obtain ⟨C, hC0, hCb⟩ := fp_abox_bound (N := n) hℓ hΦc
  -- ## bounds on the two box projections, uniform in the box volume
  have hPbd : ∀ (k : Fin n) (x : X n), x ∈ abox n ℓ →
      |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) k Φ x| ≤ C := by
    intro k x hx
    by_cases hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u
    · exact Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc k hCb x hx
    · have hV0 : Work.SmallBoxSliding.boxMass ℓ d u = 0 := le_antisymm (not_lt.mp hV) hVnn
      have hz : Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) k Φ x = 0 := by
        simp only [Work.UBBInputs8.boxPInd, hV0, div_zero, zero_mul]
      rw [hz, abs_zero]
      exact hC0
  have hQbd : ∀ (k : Fin n) (x : X n), x ∈ abox n ℓ →
      |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) k Φ x| ≤ 2 * C := by
    intro k x hx
    rw [fp_boxQInd_eq (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
      k Φ x]
    calc |Aind (Submission.BoseGases.dlBox ℓ d u) (x k) * Φ x
          - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) k Φ x|
        ≤ |Aind (Submission.BoseGases.dlBox ℓ d u) (x k) * Φ x|
          + |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) k Φ x| := by
          simpa [sub_eq_add_neg] using abs_add_le
            (Aind (Submission.BoseGases.dlBox ℓ d u) (x k) * Φ x)
            (-(Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) k Φ x))
      _ ≤ 1 * C + C := by
          refine add_le_add ?_ (hPbd k x hx)
          rw [abs_mul]
          exact mul_le_mul (Aind_abs_le_one (Submission.BoseGases.dlBox ℓ d u) (x k))
            (hCb x hx) (abs_nonneg _) (by linarith)
      _ = 2 * C := by ring
  have hQint : ∀ k : Fin n, IntegrableOn (fun x : X n =>
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) k Φ x) ^ 2) (abox n ℓ) volume :=
    fun k => Work.BoseFixB1S.integrableOn_sq_of_bound hℓ
      (Work.SlotWord.measurable_boxQInd _ _ hA k hΦc.measurable) (hQbd k)
  -- ## the flat count forces every mean-free box projection to vanish a.e.
  have hQ : ∀ k : Fin n, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) k Φ
      =ᵐ[MeasureTheory.volume.restrict (abox n ℓ)] 0 := by
    intro k
    have hsum : (∑ m : Fin n, ∫ x in abox n ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) m Φ x) ^ 2) = 0 := by
      simpa only [Work.UBBInputs8.cnPlusBoxInd] using hflat
    have hterm : (∫ x in abox n ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) k Φ x) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun m _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _)).mp hsum k
        (Finset.mem_univ k)
    have hz := (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (hQint k)).mp hterm
    filter_upwards [hz] with x hx
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hx
  -- ## the slice mean of `Q_{B,j}Φ` vanishes a.e.
  have hsliceQj : (fun x : X n => ∫ z in Submission.BoseGases.dlBox ℓ d u,
      Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z))
      =ᵐ[MeasureTheory.volume.restrict (abox n ℓ)] 0 :=
    fp_sliceMean_ae_zero hA hAc i
      (Work.SlotWord.measurable_boxQInd _ _ hA j hΦc.measurable) (hQ j)
  -- ## the pointwise collapse at a.e. box configuration
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ),
    hQ i, hsliceQj] with x hxbox hQi_x hslice_x
  simp only [Pi.zero_apply] at hQi_x hslice_x
  show (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
      * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) * Φ x
      - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) j Φ) x = 0
  -- (a) the one-slot collapse of `Q_iΦ`
  have hone_i : Aind (Submission.BoseGases.dlBox ℓ d u) (x i) * Φ x
      = Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
        * oneMean (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          i Φ x := by
    have h := hQi_x
    rw [fp_boxQInd_eq (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        i Φ x,
      fp_boxPInd_eq (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        i Φ x] at h
    linarith
  -- the two slot integrals
  set A1 : ℝ := ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (Function.update x i z)
    with hA1def
  set A2 : ℝ := ∫ z in Submission.BoseGases.dlBox ℓ d u,
      ∫ w in Submission.BoseGases.dlBox ℓ d u,
        Φ (Function.update (Function.update x i z) j w) with hA2def
  -- (b) the split of the vanishing slice mean
  have hslice_split : Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
      * (A1 - (1 / Work.SmallBoxSliding.boxMass ℓ d u) * A2) = 0 := by
    -- the two slot slices are integrable over `B(u)`
    have hint1 : IntegrableOn (fun z : E3 => Φ (Function.update x i z))
        (Submission.BoseGases.dlBox ℓ d u) volume :=
      fp_slotInt_of_bound hℓ hA hAc i x hxbox hΦc.measurable hCb
    have hmeas : Measurable (oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) j Φ) :=
      (Work.BoseFixB1S.measurable_fibreMean (Submission.BoseGases.dlBox ℓ d u) hA j
        hΦc.measurable).const_mul (1 / Work.SmallBoxSliding.boxMass ℓ d u)
    have h1bd : ∀ y ∈ abox n ℓ,
        |oneMean (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          j Φ y| ≤ C := by
      intro y hy
      by_cases hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u
      · rw [show oneMean (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
            j Φ y = (1 / Work.SmallBoxSliding.boxMass ℓ d u)
              * ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (Function.update y j z) from rfl]
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hV)]
        have hfin : (volume : Measure E3) (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
          Work.BoseFixB1S.volume_A_lt_top hℓ hAc
        have hb : |∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (Function.update y j z)|
            ≤ C * Work.SmallBoxSliding.boxMass ℓ d u := by
          have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3))
            hfin (s := Submission.BoseGases.dlBox ℓ d u)
            (f := fun z : E3 => Φ (Function.update y j z)) (C := C)
            (fun z hz => by
              rw [Real.norm_eq_abs]
              exact hCb _ (fp_update_mem_abox hAc hy j hz))
          rwa [Real.norm_eq_abs, MeasureTheory.Measure.real_def, ← hVeq] at h
        calc (1 / Work.SmallBoxSliding.boxMass ℓ d u)
              * |∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (Function.update y j z)|
            ≤ (1 / Work.SmallBoxSliding.boxMass ℓ d u)
              * (C * Work.SmallBoxSliding.boxMass ℓ d u) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = C := by field_simp
      · have hV0 : Work.SmallBoxSliding.boxMass ℓ d u = 0 := le_antisymm (not_lt.mp hV) hVnn
        rw [show oneMean (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
              j Φ y = (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                * ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (Function.update y j z) from rfl,
          hV0, div_zero, zero_mul, abs_zero]
        exact hC0
    have hint2 : IntegrableOn (fun z : E3 => oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z))
        (Submission.BoseGases.dlBox ℓ d u) volume :=
      fp_slotInt_of_bound hℓ hA hAc i x hxbox hmeas h1bd
    -- the integrand of the slice mean, in factored form
    have hfun : (fun z : E3 => Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z))
        = fun z : E3 => Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
            * (Φ (Function.update x i z)
              - oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z)) := by
      funext z
      rw [fp_boxQInd_eq (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          j Φ (Function.update x i z),
        fp_boxPInd_eq (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          j Φ (Function.update x i z)]
      have h1 : (Function.update x i z) j = x j := by
        rw [Function.update_apply, if_neg]
        exact fun h => hij h.symm
      rw [h1]
      ring
    have hzero : Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
        * ∫ z in Submission.BoseGases.dlBox ℓ d u,
            (Φ (Function.update x i z)
              - oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z)) = 0 := by
      have hcongr : (∫ z in Submission.BoseGases.dlBox ℓ d u,
            Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z))
          = ∫ z in Submission.BoseGases.dlBox ℓ d u,
              Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
                * (Φ (Function.update x i z)
                  - oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact congrFun hfun z
      rw [hcongr, MeasureTheory.integral_const_mul] at hslice_x
      exact hslice_x
    -- identify the second slot integral with the double mean
    have hone : (∫ z in Submission.BoseGases.dlBox ℓ d u,
          oneMean (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
            j Φ (Function.update x i z))
        = (1 / Work.SmallBoxSliding.boxMass ℓ d u) * A2 := by
      rw [hA2def]
      rw [show (fun z : E3 => oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z))
          = fun z : E3 => (1 / Work.SmallBoxSliding.boxMass ℓ d u)
              * ∫ w in Submission.BoseGases.dlBox ℓ d u,
                  Φ (Function.update (Function.update x i z) j w) from by
        funext z; rfl]
      rw [MeasureTheory.integral_const_mul]
    have hsplit : (∫ z in Submission.BoseGases.dlBox ℓ d u,
          (Φ (Function.update x i z)
            - oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ (Function.update x i z)))
        = A1 - (1 / Work.SmallBoxSliding.boxMass ℓ d u) * A2 := by
      rw [hA1def, ← hone]
      rw [← MeasureTheory.integral_sub hint1 hint2]
    rw [hsplit] at hzero
    exact hzero
  -- (c) the pair identity closes the goal
  have hPiPj := fp_boxPInd_twoMean (Work.SmallBoxSliding.boxMass ℓ d u)
    (Submission.BoseGases.dlBox ℓ d u) hij Φ x
  have htwo : twoMean (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
      i j Φ x = (1 / Work.SmallBoxSliding.boxMass ℓ d u)
        * ((1 / Work.SmallBoxSliding.boxMass ℓ d u) * A2) := by
    rw [hA2def]
    rfl
  have hone_i' : oneMean (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ x
      = (1 / Work.SmallBoxSliding.boxMass ℓ d u) * A1 := by
    rw [hA1def]
    rfl
  have hfinal : Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
      * Aind (Submission.BoseGases.dlBox ℓ d u) (x j) * Φ x
      = Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
        * Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
        * twoMean (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
            i j Φ x := by
    rw [htwo]
    calc Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
          * Aind (Submission.BoseGases.dlBox ℓ d u) (x j) * Φ x
        = Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
          * (Aind (Submission.BoseGases.dlBox ℓ d u) (x i) * Φ x) := by ring
      _ = Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
          * (Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
            * ((1 / Work.SmallBoxSliding.boxMass ℓ d u) * A1)) := by
          rw [← hone_i']
          rw [← hone_i]
      _ = Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
          * Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
          * ((1 / Work.SmallBoxSliding.boxMass ℓ d u) * A1) := by ring
      _ = Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
          * Aind (Submission.BoseGases.dlBox ℓ d u) (x j)
          * ((1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ((1 / Work.SmallBoxSliding.boxMass ℓ d u) * A2)) := by
          linear_combination
            (Aind (Submission.BoseGases.dlBox ℓ d u) (x i)
              * (1 / Work.SmallBoxSliding.boxMass ℓ d u)) * hslice_split
  rw [show (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
      = Aind (Submission.BoseGases.dlBox ℓ d u) (x i) from rfl,
    show (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j)
      = Aind (Submission.BoseGases.dlBox ℓ d u) (x j) from rfl,
    hPiPj]
  exact sub_eq_zero.mpr hfinal

end Work.BoseFixB1S
