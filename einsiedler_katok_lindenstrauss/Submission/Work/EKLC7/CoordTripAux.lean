import Mathlib
import Submission.Work.EKLC7.CoordTripDefs

/-!
# C7 (`CoordTrip`): measure-theoretic helpers
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

open scoped ENNReal

namespace Work.EKLC7

open MeasureTheory Filter Topology
open Work.EKLContract
open Work.EKLContract.Lemmas

/-! ## Measures concentrated on a root group -/

/-- On the root group `U_ab`, the `(a,b)`-entry is the parameter of the transvection. -/
theorem uij_entry_of_mem {a b : Fin 3} (h : a ≠ b) {g : SL3} (hg : g ∈ Uij h) :
    uij h (toMat g a b) = g := by
  obtain ⟨s, rfl⟩ := (horoUij_mem_iff h g).mp hg
  rw [uij_eval_self h s]

/-- A measure supported on the root group `U_ab` is the pushforward of its parameter measure
along the one-parameter subgroup. -/
theorem measure_eq_map_uij_entry {a b : Fin 3} (h : a ≠ b) {A : Measure SL3}
    (hA : A (Uij h)ᶜ = 0) :
    A = (A.map (fun g => toMat g a b)).map (fun s => uij h s) := by
  have hae : (fun g : SL3 => uij h (toMat g a b)) =ᵐ[A] id := by
    have hcompl : ∀ᵐ g ∂A, g ∈ Uij h := by
      rw [ae_iff]; exact hA
    filter_upwards [hcompl] with g hg
    exact uij_entry_of_mem h hg
  have hmap : A.map (fun g : SL3 => uij h (toMat g a b)) = A :=
    (Measure.map_congr hae).trans Measure.map_id
  rw [Measure.map_map (horoUij_cont h).measurable (continuous_toMat_entry a b).measurable]
  exact hmap.symm

/-- The parameter measure of a measure supported on a root group is finite on compacts. -/
theorem isFiniteMeasureOnCompacts_map_entry {a b : Fin 3} (h : a ≠ b) {A : Measure SL3}
    [IsFiniteMeasureOnCompacts A] (hA : A (Uij h)ᶜ = 0) :
    IsFiniteMeasureOnCompacts (A.map (fun g => toMat g a b)) := by
  refine ⟨fun K hK => ?_⟩
  rw [Measure.map_apply (continuous_toMat_entry a b).measurable hK.measurableSet]
  have hsub : Set.preimage (fun g : SL3 => toMat g a b) K ⊆ Set.image (uij h) K ∪ (Uij h)ᶜ := by
    intro g hg
    by_cases hmem : g ∈ Uij h
    · exact Or.inl ⟨toMat g a b, hg, uij_entry_of_mem h hmem⟩
    · exact Or.inr hmem
  calc A (Set.preimage (fun g : SL3 => toMat g a b) K)
      ≤ A (Set.image (uij h) K ∪ (Uij h)ᶜ) := measure_mono hsub
    _ ≤ A (Set.image (uij h) K) + A ((Uij h)ᶜ) := measure_union_le _ _
    _ = A (Set.image (uij h) K) := by rw [hA, add_zero]
    _ < ∞ := (hK.image (horoUij_cont h)).measure_lt_top

/-! ## Product measures -/

/-- Pushforward of a triple product along the product map. -/
theorem map_prod_prod_prod {α β γ δ η θ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] [MeasurableSpace η] [MeasurableSpace θ]
    {f : α → β} {g : γ → δ} {h : η → θ} {A : Measure α} {B : Measure γ} {C : Measure η}
    [SFinite A] [SFinite B] [SFinite C] (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) :
    (A.prod (B.prod C)).map (Prod.map f (Prod.map g h))
      = ((A.map f).prod ((B.map g).prod (C.map h))) := by
  rw [← Measure.map_prod_map A (B.prod C) hf (hg.prodMap hh),
    ← Measure.map_prod_map B C hg hh]

/-- The first product measure is the pushforward of the product of the parameter measures. -/
theorem prod_eq_map_paramA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {A B C : Measure SL3} [SFinite A] [SFinite B] [SFinite C]
    {Ap Bp Cp : Measure ℝ} [SFinite Ap] [SFinite Bp] [SFinite Cp]
    (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s))
    (hC : C = Cp.map (fun s => uij hik s)) :
    A.prod (B.prod C) = (Ap.prod (Bp.prod Cp)).map (paramA hij hjk hik) := by
  rw [hA, hB, hC, paramA_eq hij hjk hik,
    map_prod_prod_prod (horoUij_cont hij).measurable (horoUij_cont hjk).measurable
      (horoUij_cont hik).measurable]

/-- The second product measure is the pushforward of the product of the parameter measures. -/
theorem prod_eq_map_paramB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {A B C : Measure SL3} [SFinite A] [SFinite B] [SFinite C]
    {Ap Bp Cp : Measure ℝ} [SFinite Ap] [SFinite Bp] [SFinite Cp]
    (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s))
    (hC : C = Cp.map (fun s => uij hik s)) :
    B.prod (A.prod C) = (Bp.prod (Ap.prod Cp)).map (paramB hij hjk hik) := by
  rw [hA, hB, hC, paramB_eq hij hjk hik,
    map_prod_prod_prod (horoUij_cont hjk).measurable (horoUij_cont hij).measurable
      (horoUij_cont hik).measurable]

/-! ## The Heisenberg pushforward measures -/

/-- `rhoA` is the pushforward of the product of the parameter measures along `heisA`. -/
theorem rhoA_eq {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {A B C : Measure SL3} [SFinite A] [SFinite B] [SFinite C]
    {Ap Bp Cp : Measure ℝ} [SFinite Ap] [SFinite Bp] [SFinite Cp]
    (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s))
    (hC : C = Cp.map (fun s => uij hik s)) :
    (A.prod (B.prod C)).map mult3 = (Ap.prod (Bp.prod Cp)).map (heisA hij hjk hik) := by
  rw [prod_eq_map_paramA hij hjk hik hA hB hC,
    Measure.map_map continuous_mult3.measurable (continuous_paramA hij hjk hik).measurable]
  congr 1
  funext x
  exact mult3_paramA hij hjk hik x

/-- `rhoB` is the pushforward of the product of the parameter measures along `heisB`. -/
theorem rhoB_eq {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {A B C : Measure SL3} [SFinite A] [SFinite B] [SFinite C]
    {Ap Bp Cp : Measure ℝ} [SFinite Ap] [SFinite Bp] [SFinite Cp]
    (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s))
    (hC : C = Cp.map (fun s => uij hik s)) :
    (B.prod (A.prod C)).map mult3 = (Bp.prod (Ap.prod Cp)).map (heisB hij hjk hik) := by
  rw [prod_eq_map_paramB hij hjk hik hA hB hC,
    Measure.map_map continuous_mult3.measurable (continuous_paramB hij hjk hik).measurable]
  congr 1
  funext x
  exact mult3_paramB hij hjk hik x

/-- The coordinate pushforward of `rhoA`. -/
theorem rhoA_map_coordMap {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {A B C : Measure SL3} [SFinite A] [SFinite B] [SFinite C]
    {Ap Bp Cp : Measure ℝ} [SFinite Ap] [SFinite Bp] [SFinite Cp]
    (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s))
    (hC : C = Cp.map (fun s => uij hik s)) :
    ((A.prod (B.prod C)).map mult3).map (coordMap i j k)
      = (Ap.prod (Bp.prod Cp)).map shearA := by
  rw [rhoA_eq hij hjk hik hA hB hC,
    Measure.map_map (continuous_coordMap i j k).measurable
      (continuous_heisA hij hjk hik).measurable]
  congr 1
  funext x
  exact coordMap_heisA hij hjk hik x

/-- The coordinate pushforward of `rhoB`. -/
theorem rhoB_map_coordMap {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {A B C : Measure SL3} [SFinite A] [SFinite B] [SFinite C]
    {Ap Bp Cp : Measure ℝ} [SFinite Ap] [SFinite Bp] [SFinite Cp]
    (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s))
    (hC : C = Cp.map (fun s => uij hik s)) :
    ((B.prod (A.prod C)).map mult3).map (coordMap i j k)
      = (Bp.prod (Ap.prod Cp)).map shearB := by
  rw [rhoB_eq hij hjk hik hA hB hC,
    Measure.map_map (continuous_coordMap i j k).measurable
      (continuous_heisB hij hjk hik).measurable]
  congr 1
  funext x
  exact coordMap_heisB hij hjk hik x

/-! ## Bounds on compact sets -/

/-- The coordinates of a compact subset of `R^3` are bounded. -/
theorem isCompact_exists_abs_bound_triple (K : Set (ℝ × ℝ × ℝ)) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, |z.1| ≤ M ∧ |z.2.1| ≤ M ∧ |z.2.2| ≤ M := by
  obtain ⟨M1, hM1, h1⟩ := isCompact_exists_abs_bound
    (Set.image (fun z : ℝ × ℝ × ℝ => z.1) K)
    (hK.image (continuous_fst : Continuous fun z : ℝ × (ℝ × ℝ) => z.1))
  obtain ⟨M2, hM2, h2⟩ := isCompact_exists_abs_bound_prod
    (Set.image (fun z : ℝ × ℝ × ℝ => z.2) K)
    (hK.image (continuous_snd : Continuous fun z : ℝ × (ℝ × ℝ) => z.2))
  refine ⟨max M1 M2, le_trans hM1 (le_max_left _ _), fun z hz => ⟨?_, ?_, ?_⟩⟩
  · exact le_trans (h1 z.1 ⟨z, hz, rfl⟩) (le_max_left _ _)
  · exact le_trans (h2 z.2 ⟨z, hz, rfl⟩).1 (le_max_right _ _)
  · exact le_trans (h2 z.2 ⟨z, hz, rfl⟩).2 (le_max_right _ _)

/-- The matrix entries of a compact subset of `SL_3(R)` are bounded. -/
theorem isCompact_exists_entry_bound (K : Set SL3) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ∀ a b : Fin 3, |toMat g a b| ≤ M := by
  have h : ∀ p : Fin 3 × Fin 3, ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, |toMat g p.1 p.2| ≤ M := by
    intro p
    obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound (Set.image (fun g => toMat g p.1 p.2) K)
      (hK.image (continuous_toMat_entry p.1 p.2))
    exact ⟨M, hM0, fun g hg => hM _ ⟨g, hg, rfl⟩⟩
  choose M hM0 hM using h
  refine ⟨∑ p : Fin 3 × Fin 3, M p, Finset.sum_nonneg fun p _ => hM0 p, fun g hg a b => ?_⟩
  exact le_trans (hM (a, b) g hg)
    (Finset.single_le_sum (fun p _ => hM0 p) (Finset.mem_univ (a, b)))

theorem measure_prod_prod_icc_lt_top {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp] (a b c d e f : ℝ) :
    Ap (Set.Icc a b) * (Bp (Set.Icc c d) * Cp (Set.Icc e f)) < ∞ := by
  have h1 : Ap (Set.Icc a b) < ∞ := isCompact_Icc.measure_lt_top
  have h2 : Bp (Set.Icc c d) < ∞ := isCompact_Icc.measure_lt_top
  have h3 : Cp (Set.Icc e f) < ∞ := isCompact_Icc.measure_lt_top
  exact ENNReal.mul_lt_top h1 (ENNReal.mul_lt_top h2 h3)

/-! ## Finiteness of the Heisenberg pushforwards -/

theorem isFiniteMeasureOnCompacts_rhoA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {A B C : Measure SL3} [IsFiniteMeasureOnCompacts A]
    [IsFiniteMeasureOnCompacts B] [IsFiniteMeasureOnCompacts C] [SFinite A] [SFinite B]
    [SFinite C] {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp] [SFinite Ap] [SFinite Bp]
    [SFinite Cp] (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s)) (hC : C = Cp.map (fun s => uij hik s)) :
    IsFiniteMeasureOnCompacts ((A.prod (B.prod C)).map mult3) := by
  rw [rhoA_eq hij hjk hik hA hB hC]
  refine ⟨fun K hK => ?_⟩
  rw [Measure.map_apply (continuous_heisA hij hjk hik).measurable hK.measurableSet]
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_entry_bound K hK
  have hsub : Set.preimage (heisA hij hjk hik) K ⊆
      Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-(M + M ^ 2)) (M + M ^ 2)) := by
    intro x hx
    obtain ⟨h1, h3, h2⟩ := abs_le_of_abs_heisA hij hjk hik (hM (heisA hij hjk hik x) hx)
    exact ⟨abs_le.mp h1, abs_le.mp h3, abs_le.mp h2⟩
  calc (Ap.prod (Bp.prod Cp)) (Set.preimage (heisA hij hjk hik) K)
      ≤ (Ap.prod (Bp.prod Cp))
          (Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-(M + M ^ 2)) (M + M ^ 2))) :=
        measure_mono hsub
    _ = Ap (Set.Icc (-M) M) * (Bp (Set.Icc (-M) M) * Cp (Set.Icc (-(M + M ^ 2)) (M + M ^ 2))) := by
        rw [Measure.prod_prod, Measure.prod_prod]
    _ < ∞ := measure_prod_prod_icc_lt_top _ _ _ _ _ _

theorem isFiniteMeasureOnCompacts_rhoB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {A B C : Measure SL3} [IsFiniteMeasureOnCompacts A]
    [IsFiniteMeasureOnCompacts B] [IsFiniteMeasureOnCompacts C] [SFinite A] [SFinite B]
    [SFinite C] {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp] [SFinite Ap] [SFinite Bp]
    [SFinite Cp] (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s)) (hC : C = Cp.map (fun s => uij hik s)) :
    IsFiniteMeasureOnCompacts ((B.prod (A.prod C)).map mult3) := by
  rw [rhoB_eq hij hjk hik hA hB hC]
  refine ⟨fun K hK => ?_⟩
  rw [Measure.map_apply (continuous_heisB hij hjk hik).measurable hK.measurableSet]
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_entry_bound K hK
  have hsub : Set.preimage (heisB hij hjk hik) K ⊆
      Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M) := by
    intro x hx
    obtain ⟨h1, h3, h2⟩ := abs_le_of_abs_heisB hij hjk hik (hM (heisB hij hjk hik x) hx)
    exact ⟨abs_le.mp h1, abs_le.mp h3, abs_le.mp h2⟩
  calc (Bp.prod (Ap.prod Cp)) (Set.preimage (heisB hij hjk hik) K)
      ≤ (Bp.prod (Ap.prod Cp))
          (Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M)) := measure_mono hsub
    _ = Bp (Set.Icc (-M) M) * (Ap (Set.Icc (-M) M) * Cp (Set.Icc (-M) M)) := by
        rw [Measure.prod_prod, Measure.prod_prod]
    _ < ∞ := measure_prod_prod_icc_lt_top _ _ _ _ _ _

/-! ## Compact support after composing with the shear maps -/

theorem hasCompactSupport_comp_shearA {F : ℝ × ℝ × ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (fun x : ℝ × ℝ × ℝ => F (shearA x)) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound_triple (tsupport F) hF
  have hS : IsCompact (Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ
      Set.Icc (-(M + M ^ 2)) (M + M ^ 2))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsub : Function.support (fun x : ℝ × ℝ × ℝ => F (shearA x)) ⊆
      Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-(M + M ^ 2)) (M + M ^ 2)) := by
    intro x hx
    have hxt : shearA x ∈ tsupport F := subset_tsupport F (by simpa using hx)
    obtain ⟨h1, h2, h3⟩ := hM (shearA x) hxt
    have h1b : |x.1| ≤ M := by simpa [shearA] using h1
    have h2b : |x.1 * x.2.1 + x.2.2| ≤ M := by simpa [shearA] using h2
    have h3b : |x.2.1| ≤ M := by simpa [shearA] using h3
    exact ⟨abs_le.mp h1b, abs_le.mp h3b, abs_le.mp (abs_bound_last h1b h2b h3b)⟩
  rw [hasCompactSupport_def]
  exact hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hS.isClosed)

theorem hasCompactSupport_comp_shearB {F : ℝ × ℝ × ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (fun x : ℝ × ℝ × ℝ => F (shearB x)) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound_triple (tsupport F) hF
  have hS : IsCompact (Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsub : Function.support (fun x : ℝ × ℝ × ℝ => F (shearB x)) ⊆
      Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M) := by
    intro x hx
    have hxt : shearB x ∈ tsupport F := subset_tsupport F (by simpa using hx)
    obtain ⟨h1, h2, h3⟩ := hM (shearB x) hxt
    exact ⟨abs_le.mp (by simpa [shearB] using h3), abs_le.mp (by simpa [shearB] using h1),
      abs_le.mp (by simpa [shearB] using h2)⟩
  rw [hasCompactSupport_def]
  exact hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hS.isClosed)

/-! ## Integrability of the coordinate functions -/

theorem integrable_comp_coordMap_rhoA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {A B C : Measure SL3} [IsFiniteMeasureOnCompacts A]
    [IsFiniteMeasureOnCompacts B] [IsFiniteMeasureOnCompacts C] [SFinite A] [SFinite B]
    [SFinite C] {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp] [SFinite Ap] [SFinite Bp]
    [SFinite Cp] (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s)) (hC : C = Cp.map (fun s => uij hik s))
    (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ) :
    Integrable (fun g : SL3 => F (coordMap i j k g)) ((A.prod (B.prod C)).map mult3) := by
  rw [rhoA_eq hij hjk hik hA hB hC]
  refine (integrable_map_measure ?_ (continuous_heisA hij hjk hik).aemeasurable).mpr ?_
  · exact (F.continuous.comp (continuous_coordMap i j k)).aestronglyMeasurable
  · have h1 : ((fun g : SL3 => F (coordMap i j k g)) ∘ heisA hij hjk hik) =
        fun x : ℝ × ℝ × ℝ => F (shearA x) := by
      funext x
      simp only [Function.comp_apply]
      rw [coordMap_heisA]
    rw [h1]
    exact (F.continuous.comp continuous_shearA).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_shearA F.hasCompactSupport)

theorem integrable_comp_coordMap_rhoB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {A B C : Measure SL3} [IsFiniteMeasureOnCompacts A]
    [IsFiniteMeasureOnCompacts B] [IsFiniteMeasureOnCompacts C] [SFinite A] [SFinite B]
    [SFinite C] {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp] [SFinite Ap] [SFinite Bp]
    [SFinite Cp] (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s)) (hC : C = Cp.map (fun s => uij hik s))
    (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ) :
    Integrable (fun g : SL3 => F (coordMap i j k g)) ((B.prod (A.prod C)).map mult3) := by
  rw [rhoB_eq hij hjk hik hA hB hC]
  refine (integrable_map_measure ?_ (continuous_heisB hij hjk hik).aemeasurable).mpr ?_
  · exact (F.continuous.comp (continuous_coordMap i j k)).aestronglyMeasurable
  · have h1 : ((fun g : SL3 => F (coordMap i j k g)) ∘ heisB hij hjk hik) =
        fun x : ℝ × ℝ × ℝ => F (shearB x) := by
      funext x
      simp only [Function.comp_apply]
      rw [coordMap_heisB]
    rw [h1]
    exact (F.continuous.comp continuous_shearB).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_shearB F.hasCompactSupport)

/-! ## The swap map on `R x (R x R)` -/

/-- The map swapping the last two coordinates. -/
def shearB2 : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x => (x.1, x.2.2, x.2.1)

theorem shearB2_eq : shearB2 = Prod.map id Prod.swap := rfl

theorem continuous_shearB2 : Continuous shearB2 := by
  show Continuous (fun x : ℝ × ℝ × ℝ => (x.1, x.2.2, x.2.1)); fun_prop

/-- A bound on a compactly supported continuous function on `R^3`. -/
theorem exists_abs_bound_cc (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ) :
    ∃ C : ℝ, ∀ y : ℝ × ℝ × ℝ, |F y| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound (Set.image F (tsupport F))
    (F.hasCompactSupport.image F.continuous)
  refine ⟨M, fun y => ?_⟩
  by_cases hy : y ∈ tsupport F
  · exact hM (F y) ⟨y, hy, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero]; exact hM0

/-! ## The two integration lemmas -/

theorem ofReal_abs_add (a : ℝ) : ENNReal.ofReal |a| = ENNReal.ofReal a + ENNReal.ofReal (-a) := by
  by_cases h : 0 ≤ a
  · have h1 : ENNReal.ofReal (-a) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    rw [abs_of_nonneg h, h1, add_zero]
  · have h1 : ENNReal.ofReal a = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    rw [abs_of_neg (not_le.mp h), h1, zero_add]

/-- If the `toReal` of the lower integrals of all bounded continuous functions agree up to a
constant, then so do the Bochner integrals. -/
theorem integral_eq_of_ofReal_lintegral_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ ν : Measure X) (c : ℝ)
    (h : ∀ g : X → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
      (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal
        = c * (∫⁻ x, ENNReal.ofReal (g x) ∂ν).toReal) :
    ∀ g : X → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
      ∫ x, g x ∂μ = c * ∫ x, g x ∂ν := by
  intro g hgc hgb
  obtain ⟨C, hC⟩ := hgb
  have hgn : Continuous fun x => -(g x) := hgc.neg
  have hga : Continuous fun x => |g x| := hgc.abs
  have hA := h g hgc ⟨C, hC⟩
  have hB := h (fun x => -(g x)) hgn ⟨C, fun x => by rw [abs_neg]; exact hC x⟩
  have hR := h (fun x => |g x|) hga ⟨C, fun x => by simpa using hC x⟩
  have hsplit : ∀ (μ2 : Measure X), (∫⁻ x, ENNReal.ofReal |g x| ∂μ2)
      = (∫⁻ x, ENNReal.ofReal (g x) ∂μ2) + (∫⁻ x, ENNReal.ofReal (-(g x)) ∂μ2) := by
    intro μ2
    calc ∫⁻ x, ENNReal.ofReal |g x| ∂μ2
        = ∫⁻ x, (ENNReal.ofReal (g x) + ENNReal.ofReal (-(g x))) ∂μ2 :=
          lintegral_congr fun x => ofReal_abs_add (g x)
      _ = ∫⁻ x, ENNReal.ofReal (g x) ∂μ2 + ∫⁻ x, ENNReal.ofReal (-(g x)) ∂μ2 :=
          lintegral_add_left' (ENNReal.measurable_ofReal.comp_aemeasurable hgc.aemeasurable) _
  rw [hsplit μ, hsplit ν] at hR
  set P : ENNReal := ∫⁻ x, ENNReal.ofReal (g x) ∂μ with hP
  set Q : ENNReal := ∫⁻ x, ENNReal.ofReal (-(g x)) ∂μ with hQ
  set Pv : ENNReal := ∫⁻ x, ENNReal.ofReal (g x) ∂ν with hPv
  set Qv : ENNReal := ∫⁻ x, ENNReal.ofReal (-(g x)) ∂ν with hQv
  have hA2 : P.toReal = c * Pv.toReal := by rw [hP, hPv]; exact hA
  have hB2 : Q.toReal = c * Qv.toReal := by rw [hQ, hQv]; exact hB
  have hR2 : (P + Q).toReal = c * (Pv + Qv).toReal := by rw [hP, hQ, hPv, hQv]; exact hR
  have hInt : ∀ (μ2 : Measure X), Integrable g μ2 ↔
      (∫⁻ x, ENNReal.ofReal |g x| ∂μ2) < ∞ := by
    intro μ2
    constructor
    · intro hg
      have h2 := hg.2
      rw [hasFiniteIntegral_iff_norm] at h2
      simpa [Real.norm_eq_abs] using h2
    · intro hfin
      exact ⟨hgc.aestronglyMeasurable,
        by rw [hasFiniteIntegral_iff_norm]; simpa [Real.norm_eq_abs] using hfin⟩
  have hIntP : Integrable g μ ↔ P + Q < ∞ := by rw [hInt μ, hsplit μ, ← hP, ← hQ]
  have hIntPv : Integrable g ν ↔ Pv + Qv < ∞ := by rw [hInt ν, hsplit ν, ← hPv, ← hQv]
  by_cases hmu : P + Q < ∞
  · by_cases hnu : Pv + Qv < ∞
    · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hIntP.mpr hmu),
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hIntPv.mpr hnu),
        ← hP, ← hQ, ← hPv, ← hQv, hA2, hB2]
      ring
    · rw [integral_undef (fun hc => hnu (hIntPv.mp hc))]
      have hzero : P + Q = 0 := by
        have htop : Pv + Qv = ∞ := le_antisymm le_top (not_lt.mp hnu)
        have h2 : (P + Q).toReal = 0 := by rw [hR2, htop, ENNReal.toReal_top, mul_zero]
        rw [ENNReal.toReal_eq_zero_iff] at h2
        rcases h2 with h3 | h3
        · exact h3
        · exact absurd h3 (ne_of_lt hmu)
      have hP0 : P = 0 := le_antisymm
        (le_trans (self_le_add_right P Q) (le_of_eq hzero)) (zero_le (a := P))
      have hQ0 : Q = 0 := le_antisymm
        (le_trans (self_le_add_left Q P) (le_of_eq hzero)) (zero_le (a := Q))
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hIntP.mpr hmu),
        ← hP, ← hQ, hP0, hQ0]
      norm_num
  · rw [integral_undef (fun hc => hmu (hIntP.mp hc))]
    by_cases hnu : Pv + Qv < ∞
    · have h2 : c * (Pv + Qv).toReal = 0 := by
        have htop : P + Q = ∞ := le_antisymm le_top (not_lt.mp hmu)
        rw [← hR2, htop, ENNReal.toReal_top]
      rcases mul_eq_zero.mp h2 with hc | h3
      · rw [hc, zero_mul]
      · have hzero : Pv + Qv = 0 := by
          rw [ENNReal.toReal_eq_zero_iff] at h3
          rcases h3 with h4 | h4
          · exact h4
          · exact absurd h4 (ne_of_lt hnu)
        have hPv0 : Pv = 0 := le_antisymm
          (le_trans (self_le_add_right Pv Qv) (le_of_eq hzero)) (zero_le (a := Pv))
        have hQv0 : Qv = 0 := le_antisymm
          (le_trans (self_le_add_left Qv Pv) (le_of_eq hzero)) (zero_le (a := Qv))
        rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hIntPv.mpr hnu),
          ← hPv, ← hQv, hPv0, hQv0]
        norm_num
    · rw [integral_undef (fun hc => hnu (hIntPv.mp hc))]
      norm_num

/-! ## Positive and negative parts of a compactly supported function -/

/-- The positive part of a compactly supported continuous function. -/
def ccPos {X : Type*} [TopologicalSpace X] [T2Space X] (f : CompactlySupportedContinuousMap X ℝ) :
    CompactlySupportedContinuousMap X ℝ :=
  ⟨⟨fun x => max (f x) 0, f.continuous.max continuous_const⟩, by
    rw [hasCompactSupport_def]
    refine f.hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ?_) f.hasCompactSupport.isClosed)
    refine subset_tsupport f ?_
    simp only [Function.mem_support, ne_eq] at hx ⊢
    exact fun h0 => hx (by simp [h0])⟩

/-- The negative part of a compactly supported continuous function. -/
def ccNeg {X : Type*} [TopologicalSpace X] [T2Space X] (f : CompactlySupportedContinuousMap X ℝ) :
    CompactlySupportedContinuousMap X ℝ :=
  ⟨⟨fun x => max (-(f x)) 0, f.continuous.neg.max continuous_const⟩, by
    rw [hasCompactSupport_def]
    refine f.hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ?_) f.hasCompactSupport.isClosed)
    refine subset_tsupport f ?_
    simp only [Function.mem_support, ne_eq] at hx ⊢
    exact fun h0 => hx (by simp [h0])⟩

theorem coe_ccPos {X : Type*} [TopologicalSpace X] [T2Space X] (f : CompactlySupportedContinuousMap X ℝ)
    (x : X) : (ccPos f : X → ℝ) x = max (f x) 0 := rfl

theorem coe_ccNeg {X : Type*} [TopologicalSpace X] [T2Space X] (f : CompactlySupportedContinuousMap X ℝ)
    (x : X) : (ccNeg f : X → ℝ) x = max (-(f x)) 0 := rfl

/-- If the integral of every nonnegative compactly supported function vanishes, then so does
the integral of every compactly supported function. -/
theorem integral_eq_zero_of_nonneg_eq_zero {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (h : ∀ f : CompactlySupportedContinuousMap X ℝ, 0 ≤ (f : X → ℝ) →
      ∫ x, (f : X → ℝ) x ∂μ = 0) :
    ∀ f : CompactlySupportedContinuousMap X ℝ, ∫ x, (f : X → ℝ) x ∂μ = 0 := by
  intro f
  have h1 : Integrable (ccPos f : X → ℝ) μ :=
    (ccPos f).continuous.integrable_of_hasCompactSupport (ccPos f).hasCompactSupport
  have h2 : Integrable (ccNeg f : X → ℝ) μ :=
    (ccNeg f).continuous.integrable_of_hasCompactSupport (ccNeg f).hasCompactSupport
  have hsub : ∀ x : X, (f : X → ℝ) x = (ccPos f : X → ℝ) x - (ccNeg f : X → ℝ) x := by
    intro x
    rw [coe_ccPos, coe_ccNeg]
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right hx, max_eq_left (by linarith), sub_neg_eq_add, add_comm]
      simp
  calc ∫ x, (f : X → ℝ) x ∂μ
      = ∫ x, ((ccPos f : X → ℝ) x - (ccNeg f : X → ℝ) x) ∂μ :=
        integral_congr_ae (Eventually.of_forall hsub)
    _ = ∫ x, (ccPos f : X → ℝ) x ∂μ - ∫ x, (ccNeg f : X → ℝ) x ∂μ := integral_sub h1 h2
    _ = 0 := by rw [h (ccPos f) (fun x => le_max_right _ _),
        h (ccNeg f) (fun x => le_max_right _ _), sub_zero]

/-! ## Integrability of the sheared functions -/

theorem integrable_comp_snd {μ ν : Measure ℝ} [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ)
    (p : ℝ) : Integrable (fun w : ℝ × ℝ => F (p, w.1, w.2)) (μ.prod ν) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound_triple (tsupport F) F.hasCompactSupport
  have hcont : Continuous fun w : ℝ × ℝ => F (p, w.1, w.2) :=
    F.continuous.comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
  refine hcont.integrable_of_hasCompactSupport ?_
  rw [hasCompactSupport_def]
  set K : Set (ℝ × ℝ) := Set.Icc (-M) M ×ˢ Set.Icc (-M) M with hKdef
  have hKc : IsCompact K := hKdef.symm ▸ isCompact_Icc.prod isCompact_Icc
  refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
  intro w hw
  have hwt : (p, w.1, w.2) ∈ tsupport F := subset_tsupport F (by simpa using hw)
  obtain ⟨h1, h2, h3⟩ := hM (p, w.1, w.2) hwt
  rw [hKdef]
  exact ⟨abs_le.mp h2, abs_le.mp h3⟩

theorem hasCompactSupport_comp_shearB2 {F : ℝ × ℝ × ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (fun x : ℝ × ℝ × ℝ => F (shearB2 x)) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound_triple (tsupport F) hF
  have hS : IsCompact (Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hsub : Function.support (fun x : ℝ × ℝ × ℝ => F (shearB2 x)) ⊆
      Set.Icc (-M) M ×ˢ (Set.Icc (-M) M ×ˢ Set.Icc (-M) M) := by
    intro x hx
    have hxt : shearB2 x ∈ tsupport F := subset_tsupport F (by simpa using hx)
    obtain ⟨h1, h2, h3⟩ := hM (shearB2 x) hxt
    exact ⟨abs_le.mp (by simpa [shearB2] using h1), abs_le.mp (by simpa [shearB2] using h3),
      abs_le.mp (by simpa [shearB2] using h2)⟩
  rw [hasCompactSupport_def]
  exact hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hS.isClosed)

theorem integrable_shearA {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ) :
    Integrable (fun x : ℝ × ℝ × ℝ => F (shearA x)) (Ap.prod (Bp.prod Cp)) :=
  (F.continuous.comp continuous_shearA).integrable_of_hasCompactSupport
    (hasCompactSupport_comp_shearA F.hasCompactSupport)

theorem integrable_shearA_snd {Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Bp]
    [IsFiniteMeasureOnCompacts Cp] (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ)
    (p : ℝ) : Integrable (fun w : ℝ × ℝ => F (shearA (p, w))) (Bp.prod Cp) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound_triple (tsupport F) F.hasCompactSupport
  have hcont : Continuous fun w : ℝ × ℝ => F (shearA (p, w)) :=
    F.continuous.comp (continuous_shearA.comp (continuous_const.prodMk continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  rw [hasCompactSupport_def]
  set K : Set (ℝ × ℝ) := Set.Icc (-M) M ×ˢ Set.Icc (-(M + |p| * M)) (M + |p| * M) with hKdef
  have hKc : IsCompact K := hKdef.symm ▸ isCompact_Icc.prod isCompact_Icc
  refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
  intro w hw
  have hwt : shearA (p, w) ∈ tsupport F := subset_tsupport F (by simpa using hw)
  obtain ⟨h1, h2, h3⟩ := hM (shearA (p, w)) hwt
  have h2b : |p * w.1 + w.2| ≤ M := by simpa [shearA] using h2
  have h3b : |w.1| ≤ M := by simpa [shearA] using h3
  have h4 : |w.2| ≤ M + |p| * M := by
    have habs : |w.2| = |(p * w.1 + w.2) - p * w.1| := by congr 1; ring
    rw [habs]
    calc |(p * w.1 + w.2) - p * w.1| ≤ |p * w.1 + w.2| + |p * w.1| := by
          rw [sub_eq_add_neg]
          calc |(p * w.1 + w.2) + -(p * w.1)|
              ≤ |p * w.1 + w.2| + |-(p * w.1)| := abs_add_le _ _
            _ = |p * w.1 + w.2| + |p * w.1| := by rw [abs_neg]
      _ ≤ M + |p| * M := by
          have h5 : |p * w.1| ≤ |p| * M := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3b (abs_nonneg p)
          linarith
  rw [hKdef]
  exact ⟨abs_le.mp h3b, abs_le.mp h4⟩

theorem integrable_shearB2 {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ) :
    Integrable (fun x : ℝ × ℝ × ℝ => F (shearB2 x)) (Ap.prod (Bp.prod Cp)) :=
  (F.continuous.comp continuous_shearB2).integrable_of_hasCompactSupport
    (hasCompactSupport_comp_shearB2 F.hasCompactSupport)

theorem integrable_shearB2_snd {Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Bp]
    [IsFiniteMeasureOnCompacts Cp] (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ)
    (p : ℝ) : Integrable (fun w : ℝ × ℝ => F (shearB2 (p, w))) (Bp.prod Cp) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound_triple (tsupport F) F.hasCompactSupport
  have hcont : Continuous fun w : ℝ × ℝ => F (shearB2 (p, w)) :=
    F.continuous.comp (continuous_shearB2.comp (continuous_const.prodMk continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  rw [hasCompactSupport_def]
  set K : Set (ℝ × ℝ) := Set.Icc (-M) M ×ˢ Set.Icc (-M) M with hKdef
  have hKc : IsCompact K := hKdef.symm ▸ isCompact_Icc.prod isCompact_Icc
  refine hKc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc.isClosed)
  intro w hw
  have hwt : shearB2 (p, w) ∈ tsupport F := subset_tsupport F (by simpa using hw)
  obtain ⟨h1, h2, h3⟩ := hM (shearB2 (p, w)) hwt
  have h2b : |w.2| ≤ M := by simpa [shearB2] using h2
  have h3b : |w.1| ≤ M := by simpa [shearB2] using h3
  rw [hKdef]
  exact ⟨abs_le.mp h3b, abs_le.mp h2b⟩

/-! ## The Fubini computations -/

theorem fubini_shearA {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ) :
    ∫ x, F (shearA x) ∂(Ap.prod (Bp.prod Cp))
      = ∫ p, ∫ r, ∫ q, F (p, p * r + q, r) ∂Cp ∂Bp ∂Ap := by
  rw [integral_prod (fun x : ℝ × ℝ × ℝ => F (shearA x)) (integrable_shearA F)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  show ∫ w : ℝ × ℝ, F (shearA (p, w)) ∂(Bp.prod Cp)
      = ∫ r, ∫ q, F (p, p * r + q, r) ∂Cp ∂Bp
  rw [integral_prod (fun w : ℝ × ℝ => F (shearA (p, w))) (integrable_shearA_snd F p)]
  rfl

theorem fubini_shearB2 {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    (F : CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ) :
    ∫ x, F (shearB2 x) ∂(Ap.prod (Bp.prod Cp))
      = ∫ p, ∫ r, ∫ q, F (p, q, r) ∂Cp ∂Bp ∂Ap := by
  rw [integral_prod (fun x : ℝ × ℝ × ℝ => F (shearB2 x)) (integrable_shearB2 F)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  show ∫ w : ℝ × ℝ, F (shearB2 (p, w)) ∂(Bp.prod Cp)
      = ∫ r, ∫ q, F (p, q, r) ∂Cp ∂Bp
  rw [integral_prod (fun w : ℝ × ℝ => F (shearB2 (p, w))) (integrable_shearB2_snd F p)]
  rfl

/-! ## Rewriting the coordinate pushforward of the second order -/

/-- The coordinate pushforward of the second Heisenberg pushforward, written with the same
product measure as the first one. -/
theorem rhoB_map_coordMap2 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {A B C : Measure SL3} [SFinite A] [SFinite B] [SFinite C]
    {Ap Bp Cp : Measure ℝ} [SFinite Ap] [SFinite Bp] [SFinite Cp]
    (hA : A = Ap.map (fun s => uij hij s))
    (hB : B = Bp.map (fun s => uij hjk s))
    (hC : C = Cp.map (fun s => uij hik s)) :
    ((B.prod (A.prod C)).map mult3).map (coordMap i j k)
      = (Ap.prod (Bp.prod Cp)).map shearB2 := by
  rw [rhoB_map_coordMap hij hjk hik hA hB hC]
  have h1 : (Bp.prod (Ap.prod Cp)).map shearB = Ap.prod (Cp.prod Bp) := by
    have hmm : (Bp.prod (Ap.prod Cp)).map shearB
        = ((Bp.prod (Ap.prod Cp)).map Prod.swap).map MeasurableEquiv.prodAssoc := by
      rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable measurable_swap]
      rfl
    rw [hmm, Measure.prod_swap, Measure.prodAssoc_prod]
  have h2 : (Ap.prod (Bp.prod Cp)).map shearB2 = Ap.prod (Cp.prod Bp) := by
    rw [shearB2_eq,
      ← Measure.map_prod_map Ap (Bp.prod Cp) measurable_id measurable_swap,
      Measure.prod_swap]
    simp
  rw [h1, h2]

/-! ## Function versions of the Fubini computations -/

/-- A bound on a continuous compactly supported function on `R^3`. -/
theorem exists_abs_bound_of_continuous {F : ℝ × ℝ × ℝ → ℝ} (hFc : Continuous F)
    (hFs : HasCompactSupport F) : ∃ C : ℝ, ∀ y : ℝ × ℝ × ℝ, |F y| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound (Set.image F (tsupport F))
    (hFs.image hFc)
  refine ⟨M, fun y => ?_⟩
  by_cases hy : y ∈ tsupport F
  · exact hM (F y) ⟨y, hy, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero]; exact hM0

theorem fubini_shearA_of {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    {F : ℝ × ℝ × ℝ → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F) :
    ∫ x, F (shearA x) ∂(Ap.prod (Bp.prod Cp))
      = ∫ p, ∫ r, ∫ q, F (p, p * r + q, r) ∂Cp ∂Bp ∂Ap :=
  fubini_shearA (Ap := Ap) (Bp := Bp) (Cp := Cp) ⟨⟨F, hFc⟩, hFs⟩

theorem fubini_shearB2_of {Ap Bp Cp : Measure ℝ} [IsFiniteMeasureOnCompacts Ap]
    [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    {F : ℝ × ℝ × ℝ → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F) :
    ∫ x, F (shearB2 x) ∂(Ap.prod (Bp.prod Cp))
      = ∫ p, ∫ r, ∫ q, F (p, q, r) ∂Cp ∂Bp ∂Ap :=
  fubini_shearB2 (Ap := Ap) (Bp := Bp) (Cp := Cp) ⟨⟨F, hFc⟩, hFs⟩

end Work.EKLC7
