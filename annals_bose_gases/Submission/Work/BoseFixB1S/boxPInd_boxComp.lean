import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.BoxSpectralDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxPInd_boxComp`

The joint component `boxComp volA A S Φ = (∏_{i∈S}Pᵢ)(∏_{j∉S}Qⱼ)Φ` of the commuting family of
FS box projections `Pᵢ = UBBInputs8.boxPInd volA A i`, `Qᵢ = UBBInputs8.boxQInd volA A i` (FS
`eq:HBU`, both carrying the box indicator `1_A`) is an **eigenvector of every `Pⱼ`**:

    Pⱼ (boxComp S Φ) = if j ∈ S then boxComp S Φ else 0      (pointwise on the box `abox N ℓ`),

which is the "eigenvalue of `n₀ = ΣⱼPⱼ` on the range of `boxComp S` is `S.card`" statement in
single-slot form (see `BoxSpectralDefs`).

## Math

`boxComp` is a `List.foldl` over `List.finRange N` of the slot operators
`Op i Ψ = if i ∈ S then PᵢΨ else QᵢΨ`.  The three structural facts about the slot operators are

* `PⱼPⱼ = Pⱼ` (`boxPInd_idem`, unconditional);
* `PⱼQⱼ = 0` on the box (`boxPInd_boxQInd_self_zero`), obtained from the identity
  `Pⱼ(Aind(·j)·Ψ) = PⱼΨ` (`boxPInd_sig_smul`), additivity of `Pⱼ` (`boxPInd_sub`) and idempotence;
* `Pⱼ` commutes with `Pᵢ` and with `Qᵢ` for `i ≠ j` (`boxPInd_boxPInd_comm_good`,
  `boxPInd_boxQInd_comm_good`), from the unconditional two-slot mean formulas
  (`boxPInd_twoMean`, `boxQInd_boxPInd_twoMean`, `boxPInd_smul`) and the two-slot Fubini identity
  `twoMean_comm_good`.

The Fubini identity needs integrability of the doubly-inserted state over `A × A`, which is
available for every state that is *measurable and bounded on the analysis box* (`GoodState`);
the slot operators preserve that class (`goodState_Op`) and only ever evaluate their argument at
points of the box.  The fold is then handled by a mutual induction
(`boxCompAux_ind`) which pushes `Pⱼ` inward to the unique slot where it occurs, using
`agreeBox_boxCompAux` (the fold only reads the box values of its argument) to handle the
`Qⱼ`-case.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The slot operator of `boxComp` and its fold -/

/-- The operator that `boxComp` applies in slot `i` for the slot set `S`. -/
noncomputable def Op {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N)) (i : Fin N)
    (Ψ : X N → ℝ) (y : X N) : ℝ :=
  if i ∈ S then UBBInputs8.boxPInd volA A i Ψ y else UBBInputs8.boxQInd volA A i Ψ y

theorem Op_apply {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N)) (i : Fin N)
    (Ψ : X N → ℝ) (y : X N) :
    Op volA A S i Ψ y
      = if i ∈ S then UBBInputs8.boxPInd volA A i Ψ y
        else UBBInputs8.boxQInd volA A i Ψ y := rfl

/-- The one-step unfolding of `boxCompAux` in terms of `Op`. -/
theorem boxCompAux_cons_Op {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N))
    (i : Fin N) (L : List (Fin N)) (Ψ : X N → ℝ) :
    boxCompAux volA A S (i :: L) Ψ = boxCompAux volA A S L (Op volA A S i Ψ) := by
  rw [boxCompAux_cons]
  congr 1
  funext y
  rw [Op_apply]
  by_cases h : i ∈ S
  · simp only [h, if_true]
  · simp only [h, if_false]

/-! ## 2. The box indicator and the mean identities -/

/-- `∫_{z∈A} 1_A(z) = volA`. -/
theorem setIntegral_Aind {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (volume A).toReal) :
    (∫ z in A, Aind A z) = volA := by
  have h1 : Aind A =ᵐ[(volume : Measure E3).restrict A] (fun _ => (1 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict hA] with z hz
    simp only [Aind, Set.indicator_of_mem hz]
  calc (∫ z in A, Aind A z) = ∫ z in A, (1 : ℝ) := integral_congr_ae h1
    _ = volA := by rw [setIntegral_const, Measure.real_def, ← hvolA]; simp [smul_eq_mul]

/-- The `j`-slot mean of `PⱼΨ` equals the `j`-slot mean of `Ψ`: averaging over the slot of a
function that is constant in that slot. -/
theorem oneMean_boxPInd_eq {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (hvolA : volA = (volume A).toReal) (hvol : volA ≠ 0) (j : Fin N) (Ψ : X N → ℝ)
    (x : X N) :
    oneMean volA A j (UBBInputs8.boxPInd volA A j Ψ) x = oneMean volA A j Ψ x := by
  have h1 : (∫ z in A, UBBInputs8.boxPInd volA A j Ψ (Function.update x j z))
      = ∫ z in A, Aind A z * oneMean volA A j Ψ x := by
    apply integral_congr_ae
    filter_upwards with z
    rw [boxPInd_eq volA A j Ψ (Function.update x j z), Function.update_self,
      oneMean_slot volA A j Ψ x z]
  calc oneMean volA A j (UBBInputs8.boxPInd volA A j Ψ) x
      = (1 / volA) * ∫ z in A, Aind A z * oneMean volA A j Ψ x := by
        rw [show oneMean volA A j (UBBInputs8.boxPInd volA A j Ψ) x
              = (1 / volA)
                * ∫ z in A, UBBInputs8.boxPInd volA A j Ψ (Function.update x j z) from rfl, h1]
    _ = (1 / volA) * ((∫ z in A, Aind A z) * oneMean volA A j Ψ x) := by
        rw [integral_mul_const]
    _ = (1 / volA) * (volA * oneMean volA A j Ψ x) := by rw [setIntegral_Aind hA hvolA]
    _ = oneMean volA A j Ψ x := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hvol, one_mul]

/-- **Idempotence**: `PⱼPⱼ = Pⱼ`. -/
theorem boxPInd_idem {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (hvolA : volA = (volume A).toReal) (hvol : volA ≠ 0) (j : Fin N) (Ψ : X N → ℝ) :
    UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A j Ψ)
      = UBBInputs8.boxPInd volA A j Ψ := by
  funext x
  rw [boxPInd_eq volA A j (UBBInputs8.boxPInd volA A j Ψ) x, boxPInd_eq volA A j Ψ x]
  congr 1
  exact oneMean_boxPInd_eq volA A hA hvolA hvol j Ψ x

/-- `Pⱼ` does not see the box indicator in its own slot: `Pⱼ(1_A(·j)·Ψ) = PⱼΨ`. -/
theorem boxPInd_sig_smul {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A) (j : Fin N)
    (Ψ : X N → ℝ) :
    UBBInputs8.boxPInd volA A j (fun y => Aind A (y j) * Ψ y)
      = UBBInputs8.boxPInd volA A j Ψ := by
  funext x
  rw [boxPInd_eq volA A j (fun y => Aind A (y j) * Ψ y) x, boxPInd_eq volA A j Ψ x]
  congr 1
  unfold oneMean
  congr 1
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict hA] with z hz
  simp [Aind, Function.update_self, Set.indicator_of_mem hz]

/-! ## 3. The state class and the operators on it -/

/-- States that are measurable and bounded on the analysis box: the class on which the slot
operators are integrable and the two-slot Fubini identity holds. -/
def GoodState {N : ℕ} (ℓ : ℝ) (Ψ : X N → ℝ) : Prop :=
  Measurable Ψ ∧ ∃ C : ℝ, ∀ x ∈ abox N ℓ, |Ψ x| ≤ C

theorem goodState_zero {N : ℕ} (ℓ : ℝ) : GoodState ℓ (0 : X N → ℝ) :=
  ⟨measurable_const, 0, by intro x hx; simp⟩

theorem goodState_boxPInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    GoodState ℓ (UBBInputs8.boxPInd volA A i Ψ) := by
  obtain ⟨hm, C, hb⟩ := hΨ
  exact ⟨measurable_boxPInd volA A hA i hm, C, abs_boxPInd_le hℓ hvol hA hvolA hAc i hb⟩

theorem goodState_boxQInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    GoodState ℓ (UBBInputs8.boxQInd volA A i Ψ) := by
  obtain ⟨hm, C, hb⟩ := hΨ
  refine ⟨Work.SlotWord.measurable_boxQInd volA A hA i hm, 2 * C, ?_⟩
  intro x hx
  have hP := abs_boxPInd_le hℓ hvol hA hvolA hAc i hb x hx
  calc |UBBInputs8.boxQInd volA A i Ψ x|
      = |Aind A (x i) * Ψ x - UBBInputs8.boxPInd volA A i Ψ x| := rfl
    _ ≤ |Aind A (x i) * Ψ x| + |UBBInputs8.boxPInd volA A i Ψ x| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (Aind A (x i) * Ψ x) (-(UBBInputs8.boxPInd volA A i Ψ x))
    _ ≤ 1 * C + C := by
        refine add_le_add ?_ hP
        rw [abs_mul]
        exact mul_le_mul (Aind_abs_le_one A (x i)) (hb x hx) (abs_nonneg _) zero_le_one
    _ = 2 * C := by ring

theorem goodState_Op {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) (i : Fin N) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) : GoodState ℓ (Op volA A S i Ψ) := by
  by_cases h : i ∈ S
  · have hop : Op volA A S i Ψ = UBBInputs8.boxPInd volA A i Ψ := by
      funext y; rw [Op_apply]; simp only [h, if_true]
    rw [hop]; exact goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
  · have hop : Op volA A S i Ψ = UBBInputs8.boxQInd volA A i Ψ := by
      funext y; rw [Op_apply]; simp only [h, if_false]
    rw [hop]; exact goodState_boxQInd hℓ hvol hA hvolA hAc i hΨ

/-! ## 4. The zero function -/

theorem boxPInd_zero {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) :
    UBBInputs8.boxPInd volA A i (0 : X N → ℝ) = 0 := by
  funext y
  simp [UBBInputs8.boxPInd]

theorem boxQInd_zero {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) :
    UBBInputs8.boxQInd volA A i (0 : X N → ℝ) = 0 := by
  funext y
  simp [UBBInputs8.boxQInd, UBBInputs8.boxPInd]

theorem Op_zero {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N)) (i : Fin N) :
    Op volA A S i (0 : X N → ℝ) = 0 := by
  funext y
  rw [Op_apply]
  by_cases h : i ∈ S
  · simp only [h, if_true, boxPInd_zero, Pi.zero_apply]
  · simp only [h, if_false, boxQInd_zero, Pi.zero_apply]

/-! ## 5. `PⱼQⱼ = 0` on the box -/

theorem boxPInd_boxQInd_self_zero {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (j : Fin N) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A j Ψ) x = 0 := by
  obtain ⟨hm, C, hb⟩ := hΨ
  intro x hx
  have hInt1 : IntegrableOn
      (fun z => (fun y : X N => Aind A (y j) * Ψ y) (Function.update x j z)) A volume :=
    slotInt_of_bound (f := fun y : X N => Aind A (y j) * Ψ y) hℓ hA hAc j x hx
      ((measurable_sigAt A hA j).mul hm) (fun y hy => by
        rw [abs_mul]
        calc |Aind A (y j)| * |Ψ y| ≤ 1 * C :=
              mul_le_mul (Aind_abs_le_one A (y j)) (hb y hy) (abs_nonneg _) zero_le_one
          _ = C := one_mul C)
  have hInt2 : IntegrableOn
      (fun z => UBBInputs8.boxPInd volA A j Ψ (Function.update x j z)) A volume :=
    slotInt_of_bound (f := fun y : X N => UBBInputs8.boxPInd volA A j Ψ y) hℓ hA hAc j x hx
      (measurable_boxPInd volA A hA j hm) (abs_boxPInd_le hℓ hvol hA hvolA hAc j hb)
  have hsub := boxPInd_sub (Φ := fun y : X N => Aind A (y j) * Ψ y)
    (Ψ := UBBInputs8.boxPInd volA A j Ψ) volA A j x hInt1 hInt2
  rw [show UBBInputs8.boxQInd volA A j Ψ
        = (fun y : X N => Aind A (y j) * Ψ y) - UBBInputs8.boxPInd volA A j Ψ from rfl, hsub,
    boxPInd_sig_smul volA A hA j Ψ, boxPInd_idem volA A hA hvolA (ne_of_gt hvol) j Ψ]
  ring

/-! ## 6. Commutation of `Pⱼ` with the other slot operators -/

/-- The two-slot mean is symmetric, for measurable states bounded on the box (Fubini). -/
theorem twoMean_comm_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {Ψ : X N → ℝ} (hm : Measurable Ψ) {C : ℝ} (hb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C)
    (x : X N) (hx : x ∈ abox N ℓ) :
    twoMean volA A i j Ψ x = twoMean volA A j i Ψ x := by
  have hfin : (volume : Measure E3) A < ⊤ := volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin)
  have hInt : Integrable
      (fun p : E3 × E3 => Ψ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · have hupd : Measurable
          (fun p : E3 × E3 => (Function.update x i p.1, p.2)) :=
        ((measurable_update x).comp measurable_fst).prodMk measurable_snd
      exact (hm.comp ((measurable_update' (a := j)).comp hupd)).aestronglyMeasurable
    · have hae : ∀ᵐ p ∂(((volume : Measure E3).restrict A).prod
          ((volume : Measure E3).restrict A)), p ∈ A ×ˢ A := by
        rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hA.prod hA)]
        exact Filter.Eventually.of_forall (fun p hp => hp)
      filter_upwards [hae] with p hp
      have hmem : Function.update (Function.update x i p.1) j p.2 ∈ abox N ℓ :=
        update_mem_abox' hAc (update_mem_abox' hAc hx i hp.1) j hp.2
      simpa [Real.norm_eq_abs] using hb _ hmem
  have hswap : (∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
      = ∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x i z) j w) :=
    MeasureTheory.integral_integral_swap hInt
  unfold twoMean
  rw [hswap]
  congr 2
  apply integral_congr_ae; filter_upwards with w
  apply integral_congr_ae; filter_upwards with z
  rw [Function.update_comm hij]

/-- `PⱼPᵢ = PᵢPⱼ` on the box for `i ≠ j`. -/
theorem boxPInd_boxPInd_comm_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x
      = UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x := by
  obtain ⟨hm, C, hb⟩ := hΨ
  intro x hx
  rw [boxPInd_twoMean volA A hij.symm Ψ x, boxPInd_twoMean volA A hij Ψ x,
    twoMean_comm_good hℓ hA hAc hij hm hb x hx]
  ring

/-- `PⱼQᵢ = QᵢPⱼ` on the box for `i ≠ j`. -/
theorem boxPInd_boxQInd_comm_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Ψ) x
      = UBBInputs8.boxQInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x := by
  obtain ⟨hm, C, hb⟩ := hΨ
  intro x hx
  have hInt1 : IntegrableOn
      (fun z => (fun y : X N => Aind A (y i) * Ψ y) (Function.update x j z)) A volume :=
    slotInt_of_bound (f := fun y : X N => Aind A (y i) * Ψ y) hℓ hA hAc j x hx
      ((measurable_sigAt A hA i).mul hm) (fun y hy => by
        rw [abs_mul]
        calc |Aind A (y i)| * |Ψ y| ≤ 1 * C :=
              mul_le_mul (Aind_abs_le_one A (y i)) (hb y hy) (abs_nonneg _) zero_le_one
          _ = C := one_mul C)
  have hInt2 : IntegrableOn
      (fun z => UBBInputs8.boxPInd volA A i Ψ (Function.update x j z)) A volume :=
    slotInt_of_bound (f := fun y : X N => UBBInputs8.boxPInd volA A i Ψ y) hℓ hA hAc j x hx
      (measurable_boxPInd volA A hA i hm) (abs_boxPInd_le hℓ hvol hA hvolA hAc i hb)
  have hsub := boxPInd_sub (Φ := fun y : X N => Aind A (y i) * Ψ y)
    (Ψ := UBBInputs8.boxPInd volA A i Ψ) volA A j x hInt1 hInt2
  rw [show UBBInputs8.boxQInd volA A i Ψ
        = (fun y : X N => Aind A (y i) * Ψ y) - UBBInputs8.boxPInd volA A i Ψ from rfl, hsub,
    boxPInd_smul volA A hij.symm Ψ x,
    boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij ⟨hm, C, hb⟩ x hx]
  rfl

/-! ## 7. The fold only reads the box values of its argument -/

theorem agreeBox_boxPInd {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ₁ Ψ₂ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Ψ₁ y = Ψ₂ y) :
    ∀ y ∈ abox N ℓ, UBBInputs8.boxPInd volA A i Ψ₁ y = UBBInputs8.boxPInd volA A i Ψ₂ y := by
  intro y hy
  rw [boxPInd_eq volA A i Ψ₁ y, boxPInd_eq volA A i Ψ₂ y]
  congr 1
  unfold oneMean
  congr 1
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict hA] with z hz
  rw [h (Function.update y i z) (update_mem_abox' hAc hy i hz)]

theorem agreeBox_boxQInd {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ₁ Ψ₂ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Ψ₁ y = Ψ₂ y) :
    ∀ y ∈ abox N ℓ, UBBInputs8.boxQInd volA A i Ψ₁ y = UBBInputs8.boxQInd volA A i Ψ₂ y := by
  intro y hy
  rw [show UBBInputs8.boxQInd volA A i Ψ₁ y
        = Aind A (y i) * Ψ₁ y - UBBInputs8.boxPInd volA A i Ψ₁ y from rfl,
    show UBBInputs8.boxQInd volA A i Ψ₂ y
        = Aind A (y i) * Ψ₂ y - UBBInputs8.boxPInd volA A i Ψ₂ y from rfl,
    h y hy, agreeBox_boxPInd hA hAc i h y hy]

theorem agreeBox_Op {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) (i : Fin N) {Ψ₁ Ψ₂ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Ψ₁ y = Ψ₂ y) :
    ∀ y ∈ abox N ℓ, Op volA A S i Ψ₁ y = Op volA A S i Ψ₂ y := by
  intro y hy
  rw [Op_apply, Op_apply]
  by_cases hS : i ∈ S
  · simp only [hS, if_true]
    exact agreeBox_boxPInd hA hAc i h y hy
  · simp only [hS, if_false]
    exact agreeBox_boxQInd hA hAc i h y hy

theorem agreeBox_boxCompAux {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) (L : List (Fin N)) {Ψ₁ Ψ₂ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Ψ₁ y = Ψ₂ y) :
    ∀ y ∈ abox N ℓ, boxCompAux volA A S L Ψ₁ y = boxCompAux volA A S L Ψ₂ y := by
  induction L generalizing Ψ₁ Ψ₂ with
  | nil => simpa using h
  | cons i l ih =>
    intro y hy
    rw [boxCompAux_cons_Op, boxCompAux_cons_Op]
    exact ih (agreeBox_Op hA hAc S i h) y hy

theorem boxCompAux_zero {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N))
    (L : List (Fin N)) :
    boxCompAux volA A S L (0 : X N → ℝ) = 0 := by
  induction L with
  | nil => rfl
  | cons i l ih => rw [boxCompAux_cons_Op, Op_zero, ih]

/-! ## 8. The fold induction -/

theorem boxCompAux_ind {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) (j : Fin N) :
    ∀ L : List (Fin N), L.Nodup →
      ((j ∈ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxPInd volA A j (boxCompAux volA A S L Ψ) x
            = (if j ∈ S then boxCompAux volA A S L Ψ x else 0))
        ∧ (j ∉ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxPInd volA A j (boxCompAux volA A S L Ψ) x
            = boxCompAux volA A S L (UBBInputs8.boxPInd volA A j Ψ) x)) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨?_, ?_⟩
    · intro hj
      exact absurd hj (by simp)
    · intro _ Ψ _ x hx
      simp
  | cons i l ih =>
    intro hnd
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hnd
    obtain ⟨ihC, ihD⟩ := ih hl
    refine ⟨?_, ?_⟩
    · intro hj Ψ hΨ x hx
      rw [boxCompAux_cons_Op]
      have hΨ' : GoodState ℓ (Op volA A S i Ψ) := goodState_Op hℓ hvol hA hvolA hAc S i hΨ
      rcases (List.mem_cons).mp hj with hji | hjl
      · rw [hji] at ihD ⊢
        have hd := ihD hi (Op volA A S i Ψ) hΨ' x hx
        by_cases hS : i ∈ S
        · have hop : Op volA A S i Ψ = UBBInputs8.boxPInd volA A i Ψ := by
            funext y; rw [Op_apply]; simp only [hS, if_true]
          have hidem := boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i Ψ
          rw [hd, hop, hidem, if_pos hS]
        · have hop : Op volA A S i Ψ = UBBInputs8.boxQInd volA A i Ψ := by
            funext y; rw [Op_apply]; simp only [hS, if_false]
          have hzero := boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc i hΨ
          rw [hd, hop, if_neg hS]
          have hagree : ∀ y ∈ abox N ℓ,
              UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A i Ψ) y
                = (0 : X N → ℝ) y := by
            intro y hy; rw [hzero y hy]; rfl
          rw [agreeBox_boxCompAux hA hAc S l hagree x hx, boxCompAux_zero]
          simp
      · exact ihC hjl (Op volA A S i Ψ) hΨ' x hx
    · intro hj Ψ hΨ x hx
      have hjl : j ∉ l := fun h => hj ((List.mem_cons).mpr (Or.inr h))
      have hij : i ≠ j := fun h => hj ((List.mem_cons).mpr (Or.inl h.symm))
      rw [boxCompAux_cons_Op, boxCompAux_cons_Op]
      have hΨ' : GoodState ℓ (Op volA A S i Ψ) := goodState_Op hℓ hvol hA hvolA hAc S i hΨ
      rw [ihD hjl (Op volA A S i Ψ) hΨ' x hx]
      refine agreeBox_boxCompAux hA hAc S l ?_ x hx
      intro y hy
      by_cases hS : i ∈ S
      · have hop : Op volA A S i Ψ = UBBInputs8.boxPInd volA A i Ψ := by
          funext z; rw [Op_apply]; simp only [hS, if_true]
        have hop2 : Op volA A S i (UBBInputs8.boxPInd volA A j Ψ)
            = UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) := by
          funext z; rw [Op_apply]; simp only [hS, if_true]
        rw [hop, hop2]
        exact boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hΨ y hy
      · have hop : Op volA A S i Ψ = UBBInputs8.boxQInd volA A i Ψ := by
          funext z; rw [Op_apply]; simp only [hS, if_false]
        have hop2 : Op volA A S i (UBBInputs8.boxPInd volA A j Ψ)
            = UBBInputs8.boxQInd volA A i (UBBInputs8.boxPInd volA A j Ψ) := by
          funext z; rw [Op_apply]; simp only [hS, if_false]
        rw [hop, hop2]
        exact boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij hΨ y hy

/-! ## 9. The theorem -/

theorem boxPInd_boxComp {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxComp volA A S Φ) x
        = (if j ∈ S then Work.BoseFixB1S.boxComp volA A S Φ x else 0) := by
  intro x hx
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦgood : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  obtain ⟨hC, _⟩ :=
    boxCompAux_ind hℓ hvol hA hvolA hAc S j (List.finRange N) (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦgood x hx
  rw [boxComp_eq_aux]
  exact hres

end Work.BoseFixB1S
