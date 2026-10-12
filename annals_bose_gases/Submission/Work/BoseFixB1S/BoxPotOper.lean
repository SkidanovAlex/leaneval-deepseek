import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPotDefs
import Submission.Work.SlotWord.abs_boxQInd_le_of_bound
import Submission.Work.SlotWord.measurable_boxQInd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary helpers -/

/-- A continuous state is bounded on the (compact) analysis box. -/
theorem exists_abox_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) : ∃ C, 0 ≤ C ∧ ∀ x ∈ abox N ℓ, |Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => by
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)⟩

/-- Inserting a point of `A` in one slot of a configuration of the box keeps it in the box. -/
theorem update_mem_abox' {N : ℕ} {ℓ : ℝ} {A : Set ℝ³} (hAc : A ⊆ acube ℓ)
    {x : Submission.BoseGases.X N} (hx : x ∈ abox N ℓ)
    (i : Fin N) {z : ℝ³} (hz : z ∈ A) : Function.update x i z ∈ abox N ℓ := by
  rw [mem_abox_iff]
  intro k
  rw [Function.update_apply]
  by_cases hk : k = i
  · rw [if_pos hk]; exact hAc hz
  · rw [if_neg hk]; exact hx k

/-- The `i`-slot integral of a function bounded on the box is integrable over `A`
(for `A ⊆ acube ℓ` and `x` in the box). -/
theorem slotInt_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin N) (x : Submission.BoseGases.X N)
    (hx : x ∈ abox N ℓ) {f : Submission.BoseGases.X N → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ y ∈ abox N ℓ, |f y| ≤ C) :
    IntegrableOn (fun z => f (Function.update x i z)) A volume := by
  have hfin : (volume : Measure ℝ³) A < ⊤ := volume_A_lt_top hℓ hAc
  refine IntegrableOn.of_bound hfin ?_ C ?_
  · exact (hf.comp (by fun_prop : Measurable (fun z : ℝ³ => Function.update x i z))).aestronglyMeasurable
  · rw [ae_restrict_iff' hA]
    apply Filter.Eventually.of_forall
    intro z hz
    rw [Real.norm_eq_abs]
    exact hb _ (update_mem_abox' hAc hx i hz)

/-! ## The mean form of the box projections -/

/-- `P_iΨ = 1_A(x_i) · oneMean`. -/
theorem boxPInd_eq (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i Φ x = Aind A (x i) * oneMean volA A i Φ x := by
  unfold Work.UBBInputs8.boxPInd Aind oneMean
  ring

/-- `Q_iΨ = 1_A(x_i)·Ψ − P_iΨ` (definitional). -/
theorem boxQInd_eq (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxQInd volA A i Φ x
      = Aind A (x i) * Φ x - Work.UBBInputs8.boxPInd volA A i Φ x := rfl

/-- The `i`-slot mean does not depend on the `i`-th coordinate. -/
theorem oneMean_slot (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) (z : ℝ³) :
    oneMean volA A i Φ (Function.update x i z) = oneMean volA A i Φ x := by
  unfold oneMean
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  congr 1
  rw [Function.update_idem]

/-! ## The two-slot structure -/

/-- `P_iP_jΨ = 1_A(x_i)·1_A(x_j)·twoMean` for `i ≠ j`. -/
theorem boxPInd_twoMean {N : ℕ} (volA : ℝ) (A : Set ℝ³) {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = Aind A (x i) * Aind A (x j) * twoMean volA A i j Φ x := by
  have hinner : ∀ z : ℝ³, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i z)
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
    apply integral_congr_ae; filter_upwards with z; exact hinner z]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul]
  unfold twoMean Aind
  ring

/-- The two-slot mean is symmetric in the two slots (`i ≠ j`). -/
theorem twoMean_comm {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (x : Submission.BoseGases.X N) :
    twoMean volA A i j Φ x = twoMean volA A j i Φ x := by
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ³ × ℝ³ => Φ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure ℝ³).restrict A).prod ((volume : Measure ℝ³).restrict A)) := by
    have hfin : (volume : Measure ℝ³) A < ⊤ := volume_A_lt_top hℓ hAc
    haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict A) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin)
    have hcomp : IsCompact ((fun p : ℝ³ × ℝ³ =>
        Function.update (Function.update x i p.1) j p.2) '' (acube ℓ ×ˢ acube ℓ)) :=
      ((acube_compact hℓ).prod (acube_compact hℓ)).image (by fun_prop)
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hΦc.continuousOn
    refine MeasureTheory.Integrable.of_bound (by fun_prop) (max C 0) ?_
    have hae : ∀ᵐ p ∂(((volume : Measure ℝ³).restrict A).prod
        ((volume : Measure ℝ³).restrict A)), p ∈ A ×ˢ A := by
      rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hA.prod hA)]
      exact Filter.Eventually.of_forall (fun p hp => hp)
    filter_upwards [hae] with p hp
    have h := hC _ (Set.mem_image_of_mem _ (Set.mk_mem_prod (hAc hp.1) (hAc hp.2)))
    rw [Real.norm_eq_abs] at h ⊢
    exact le_trans h (le_max_left C 0)
  have hswap : (∫ z in A, ∫ w in A, Φ (Function.update (Function.update x i z) j w))
      = ∫ w in A, ∫ z in A, Φ (Function.update (Function.update x i z) j w) :=
    MeasureTheory.integral_integral_swap hInt
  unfold twoMean
  rw [hswap]
  congr 2
  apply integral_congr_ae; filter_upwards with w
  apply integral_congr_ae; filter_upwards with z
  rw [Function.update_comm hij]

/-! ## Commutation, `σ`-multiplication, linearity -/

/-- `P_iP_j = P_jP_i` for `i ≠ j`. -/
theorem boxPInd_comm {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x := by
  rw [boxPInd_twoMean volA A hij Φ x, boxPInd_twoMean volA A hij.symm Φ x,
    twoMean_comm hℓ hA hAc hij hΦc x]
  ring

/-- `P_i` commutes with multiplication by the box indicator in another slot (`i ≠ j`). -/
theorem boxPInd_smul {N : ℕ} (volA : ℝ) (A : Set ℝ³) {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i (fun y => Aind A (y j) * Φ y) x
      = Aind A (x j) * Work.UBBInputs8.boxPInd volA A i Φ x := by
  unfold Work.UBBInputs8.boxPInd
  have h : (∫ z in A, Aind A ((Function.update x i z) j) * Φ (Function.update x i z))
      = Aind A (x j) * ∫ z in A, Φ (Function.update x i z) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae; filter_upwards with z
    have h1 : (Function.update x i z) j = x j := by
      rw [Function.update_apply, if_neg]; exact fun h => hij h.symm
    rw [h1]
  rw [h]; ring

/-- `Q_i` commutes with multiplication by the box indicator in another slot (`i ≠ j`). -/
theorem boxQInd_smul {N : ℕ} (volA : ℝ) (A : Set ℝ³) {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxQInd volA A i (fun y => Aind A (y j) * Φ y) x
      = Aind A (x i) * (Aind A (x j) * Φ x)
        - Aind A (x j) * Work.UBBInputs8.boxPInd volA A i Φ x := by
  rw [Work.UBBInputs8.boxQInd, boxPInd_smul volA A hij Φ x]
  unfold Aind
  ring

/-- Additivity of `P_i` (with the two slot-integrability side conditions). -/
theorem boxPInd_add {N : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin N)
    (x : Submission.BoseGases.X N) {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : IntegrableOn (fun z => Φ (Function.update x i z)) A volume)
    (hΨ : IntegrableOn (fun z => Ψ (Function.update x i z)) A volume) :
    Work.UBBInputs8.boxPInd volA A i (Φ + Ψ) x
      = Work.UBBInputs8.boxPInd volA A i Φ x + Work.UBBInputs8.boxPInd volA A i Ψ x := by
  unfold Work.UBBInputs8.boxPInd
  have h : (∫ z in A, (Φ + Ψ) (Function.update x i z))
      = (∫ z in A, Φ (Function.update x i z)) + ∫ z in A, Ψ (Function.update x i z) := by
    rw [← integral_add hΦ hΨ]
    apply integral_congr_ae; filter_upwards with z
    rfl
  rw [h]; ring

/-- Subtracting: `P_i(Φ − Ψ) = P_iΦ − P_iΨ` (same side conditions). -/
theorem boxPInd_sub {N : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin N)
    (x : Submission.BoseGases.X N) {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : IntegrableOn (fun z => Φ (Function.update x i z)) A volume)
    (hΨ : IntegrableOn (fun z => Ψ (Function.update x i z)) A volume) :
    Work.UBBInputs8.boxPInd volA A i (Φ - Ψ) x
      = Work.UBBInputs8.boxPInd volA A i Φ x - Work.UBBInputs8.boxPInd volA A i Ψ x := by
  unfold Work.UBBInputs8.boxPInd
  have h : (∫ z in A, (Φ - Ψ) (Function.update x i z))
      = (∫ z in A, Φ (Function.update x i z)) - ∫ z in A, Ψ (Function.update x i z) := by
    rw [← integral_sub hΦ hΨ]
    apply integral_congr_ae; filter_upwards with z
    rfl
  rw [h]; ring

/-- Additivity of `Q_i`. -/
theorem boxQInd_add {N : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin N)
    (x : Submission.BoseGases.X N) {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : IntegrableOn (fun z => Φ (Function.update x i z)) A volume)
    (hΨ : IntegrableOn (fun z => Ψ (Function.update x i z)) A volume) :
    Work.UBBInputs8.boxQInd volA A i (Φ + Ψ) x
      = Work.UBBInputs8.boxQInd volA A i Φ x + Work.UBBInputs8.boxQInd volA A i Ψ x := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd,
    boxPInd_add volA A i x hΦ hΨ]
  simp only [Pi.add_apply]
  ring

/-- Subtracting: `Q_i(Φ − Ψ) = Q_iΦ − Q_iΨ`. -/
theorem boxQInd_sub {N : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin N)
    (x : Submission.BoseGases.X N) {Φ Ψ : Submission.BoseGases.X N → ℝ}
    (hΦ : IntegrableOn (fun z => Φ (Function.update x i z)) A volume)
    (hΨ : IntegrableOn (fun z => Ψ (Function.update x i z)) A volume) :
    Work.UBBInputs8.boxQInd volA A i (Φ - Ψ) x
      = Work.UBBInputs8.boxQInd volA A i Φ x - Work.UBBInputs8.boxQInd volA A i Ψ x := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd,
    boxPInd_sub volA A i x hΦ hΨ]
  simp only [Pi.sub_apply]
  ring

/-! ## The four patterns and the orientation swaps -/

/-- The three standard bounds on the analysis box for a continuous state: the state itself, the
box condensate projection `P_iΨ` in every slot, and the mean-free projection `Q_iΨ` in every slot. -/
theorem boxBounds {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set ℝ³}
    (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    ∃ C, 0 ≤ C ∧ (∀ y ∈ abox N ℓ, |Φ y| ≤ C) ∧
      (∀ i, ∀ y ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ y| ≤ C) ∧
      (∀ i, ∀ y ∈ abox N ℓ, |Work.UBBInputs8.boxQInd volA A i Φ y| ≤ 2 * C) := by
  obtain ⟨C, hC0, hC⟩ := exists_abox_bound hℓ hΦc
  refine ⟨C, hC0, hC, fun i y hy => abs_boxPInd_le hℓ hvol hA hvolA hAc i hC y hy,
    fun i y hy => ?_⟩
  have h : Work.UBBInputs8.boxQInd volA A i Φ y
      = Aind A (y i) * Φ y - Work.UBBInputs8.boxPInd volA A i Φ y := rfl
  rw [h]
  have hP := abs_boxPInd_le hℓ hvol hA hvolA hAc i hC y hy
  calc |Aind A (y i) * Φ y - Work.UBBInputs8.boxPInd volA A i Φ y|
      ≤ |Aind A (y i) * Φ y| + |Work.UBBInputs8.boxPInd volA A i Φ y| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (Aind A (y i) * Φ y) (-(Work.UBBInputs8.boxPInd volA A i Φ y))
    _ ≤ 1 * C + C := by
        refine add_le_add ?_ hP
        rw [abs_mul]
        exact mul_le_mul (Aind_abs_le_one A (y i)) (hC y hy) (abs_nonneg _) (by linarith)
    _ = 2 * C := by ring

/-- The box indicator in a slot is measurable. -/
theorem measurable_sigAt {N : ℕ} (A : Set ℝ³) (hA : MeasurableSet A) (j : Fin N) :
    Measurable (fun y : Submission.BoseGases.X N => Aind A (y j)) := by
  unfold Aind
  exact (measurable_const.indicator hA).comp (measurable_pi_apply j)

/-- The slot integral of a two-slot mean is integrable over the box `A`. -/
theorem slotInt2_of_bound {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    (i j : Fin N) (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {C : ℝ} (hC : ∀ y ∈ abox N ℓ, |Φ y| ≤ C) :
    IntegrableOn (fun z => (1 / volA) * ∫ w in A,
      Φ (Function.update (Function.update x i z) j w)) A volume := by
  have hfin : (volume : Measure ℝ³) A < ⊤ := volume_A_lt_top hℓ hAc
  have hm1 : Measurable (fun y : Submission.BoseGases.X N =>
      ∫ w in A, Φ (Function.update y j w)) := measurable_fibreMean A hA j hΦc.measurable
  have hm2 : Measurable (fun z : ℝ³ =>
      ∫ w in A, Φ (Function.update (Function.update x i z) j w)) :=
    hm1.comp (by fun_prop : Measurable (fun z : ℝ³ => Function.update x i z))
  refine IntegrableOn.of_bound hfin ((hm2.const_mul (1 / volA)).aestronglyMeasurable) C ?_
  rw [ae_restrict_iff' hA]
  apply Filter.Eventually.of_forall
  intro z hz
  rw [Real.norm_eq_abs]
  have hInt : |∫ w in A, Φ (Function.update (Function.update x i z) j w)| ≤ C * volA := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³)) hfin (s := A)
      (f := fun w : ℝ³ => Φ (Function.update (Function.update x i z) j w)) (C := C) (fun w hw => by
        rw [Real.norm_eq_abs]
        exact hC _ (update_mem_abox' hAc (update_mem_abox' hAc hx i hz) j hw))
    rw [Real.norm_eq_abs, MeasureTheory.Measure.real_def, ← hvolA] at h
    exact h
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
  calc (1 / volA) * |∫ w in A, Φ (Function.update (Function.update x i z) j w)|
      ≤ (1 / volA) * (C * volA) :=
        mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = C := by field_simp

/-- The `B` pattern in mean form: `P_iQ_jΨ = 1_A(x_i)·1_A(x_j)·(oneMeanᵢ − twoMeanᵢⱼ)`. -/
theorem boxPInd_boxQInd_twoMean {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = Aind A (x i) * Aind A (x j)
        * (oneMean volA A i Φ x - twoMean volA A i j Φ x) := by
  obtain ⟨C, hC0, hC, hPb, hQb⟩ := boxBounds hℓ hvol hA hvolA hAc hΦc
  have hinner : ∀ z : ℝ³, Work.UBBInputs8.boxQInd volA A j Φ (Function.update x i z)
      = Aind A (x j) * (Φ (Function.update x i z)
          - (1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) := by
    intro z
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    have h1 : (Function.update x i z) j = x j := by
      rw [Function.update_apply, if_neg]
      exact fun h => hij h.symm
    rw [h1]
    unfold Aind
    ring
  rw [Work.UBBInputs8.boxPInd]
  rw [show (∫ z in A, Work.UBBInputs8.boxQInd volA A j Φ (Function.update x i z))
      = ∫ z in A, Aind A (x j) * (Φ (Function.update x i z)
          - (1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) from by
    apply integral_congr_ae; filter_upwards with z; exact hinner z]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub
    (slotInt_of_bound hℓ hA hAc i x hx hΦc.measurable hC)
    (slotInt2_of_bound hℓ hvol hA hvolA hAc i j x hx hΦc hC)]
  rw [MeasureTheory.integral_const_mul]
  unfold oneMean twoMean Aind
  ring

/-- The `C` pattern in mean form: `Q_iP_jΨ = 1_A(x_i)·1_A(x_j)·(oneMeanⱼ − twoMeanᵢⱼ)`. -/
theorem boxQInd_boxPInd_twoMean (volA : ℝ) (A : Set ℝ³) {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = Aind A (x i) * Aind A (x j)
        * (oneMean volA A j Φ x - twoMean volA A i j Φ x) := by
  rw [Work.UBBInputs8.boxQInd, boxPInd_eq volA A j Φ x, boxPInd_twoMean volA A hij Φ x]
  unfold Aind
  ring

/-- The `D` pattern in mean form:
`Q_iQ_jΨ = 1_A(x_i)·1_A(x_j)·(Ψ − oneMeanᵢ − oneMeanⱼ + twoMeanᵢⱼ)`. -/
theorem boxQInd_boxQInd_twoMean {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = Aind A (x i) * Aind A (x j)
        * (Φ x - oneMean volA A i Φ x - oneMean volA A j Φ x + twoMean volA A i j Φ x) := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd,
    boxPInd_boxQInd_twoMean hℓ hvol hA hvolA hAc hij hΦc x hx, boxPInd_eq volA A j Φ x]
  unfold Aind
  ring

/-- The pattern sum: `(P_i+Q_i)(P_j+Q_j)Ψ = 1_A(x_i)·1_A(x_j)·Ψ`. -/
theorem boxPatternSum {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = Aind A (x i) * Aind A (x j) * Φ x := by
  obtain ⟨C, hC0, hC, hPb, hQb⟩ := boxBounds hℓ hvol hA hvolA hAc hΦc
  have hPi : Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x
      = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x :=
    boxPInd_add volA A i x
      (slotInt_of_bound hℓ hA hAc i x hx (measurable_boxPInd volA A hA j hΦc.measurable) (hPb j))
      (slotInt_of_bound hℓ hA hAc i x hx (Work.SlotWord.measurable_boxQInd volA A hA j hΦc.measurable) (hQb j))
  have hQi : Work.UBBInputs8.boxQInd volA A i
        (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x
      = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x :=
    boxQInd_add volA A i x
      (slotInt_of_bound hℓ hA hAc i x hx (measurable_boxPInd volA A hA j hΦc.measurable) (hPb j))
      (slotInt_of_bound hℓ hA hAc i x hx (Work.SlotWord.measurable_boxQInd volA A hA j hΦc.measurable) (hQb j))
  have hsum : (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ)
      = fun y => Aind A (y j) * Φ y := by
    funext y
    show Work.UBBInputs8.boxPInd volA A j Φ y + Work.UBBInputs8.boxQInd volA A j Φ y
      = Aind A (y j) * Φ y
    unfold Work.UBBInputs8.boxQInd Aind
    ring
  calc Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) := by ring
    _ = Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x
        + Work.UBBInputs8.boxQInd volA A i
          (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x := by
          rw [hPi, hQi]
    _ = Work.UBBInputs8.boxPInd volA A i (fun y => Aind A (y j) * Φ y) x
        + Work.UBBInputs8.boxQInd volA A i (fun y => Aind A (y j) * Φ y) x := by rw [hsum]
    _ = Aind A (x j) * Work.UBBInputs8.boxPInd volA A i Φ x
        + (Aind A (x i) * (Aind A (x j) * Φ x)
          - Aind A (x j) * Work.UBBInputs8.boxPInd volA A i Φ x) := by
          rw [boxPInd_smul volA A hij Φ x, boxQInd_smul volA A hij Φ x]
    _ = Aind A (x i) * Aind A (x j) * Φ x := by ring

/-- Orientation swap of the `PP` pattern. -/
theorem boxPPswap {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
      = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x :=
  boxPInd_comm hℓ hvol hA hvolA hAc hij.symm hΦc x

/-- Orientation swap of the `PQ` pattern: `P_jQ_i = Q_iP_j`. -/
theorem boxPQswap {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
      = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x := by
  rw [boxPInd_boxQInd_twoMean hℓ hvol hA hvolA hAc hij.symm hΦc x hx,
    boxQInd_boxPInd_twoMean volA A hij Φ x,
    twoMean_comm hℓ hA hAc hij hΦc x]
  ring

/-- Orientation swap of the `QP` pattern: `Q_jP_i = P_iQ_j`. -/
theorem boxQPswap {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
      = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x := by
  rw [boxQInd_boxPInd_twoMean volA A hij.symm Φ x,
    boxPInd_boxQInd_twoMean hℓ hvol hA hvolA hAc hij hΦc x hx,
    twoMean_comm hℓ hA hAc hij hΦc x]
  ring

/-- Orientation swap of the `QQ` pattern: `Q_jQ_i = Q_iQ_j`. -/
theorem boxQQswap {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
      = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x := by
  rw [boxQInd_boxQInd_twoMean hℓ hvol hA hvolA hAc hij.symm hΦc x hx,
    boxQInd_boxQInd_twoMean hℓ hvol hA hvolA hAc hij hΦc x hx,
    twoMean_comm hℓ hA hAc hij hΦc x]
  ring

end Work.BoseFixB1S
