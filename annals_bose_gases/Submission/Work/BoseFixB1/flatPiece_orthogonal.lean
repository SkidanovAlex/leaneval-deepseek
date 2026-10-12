import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPPcomm_bdd
import Submission.Work.BoseFixB1.boxQInd_selfAdjoint_bdd
import Submission.Work.BoseFixB1.flatPieceList_meas_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 0. Elementary helpers -/

/-- Rewriting an integral over the box by a pointwise identity on the box. -/
theorem flatOrth_integral_congr_abox {N : ℕ} {ℓ : ℝ} {F G : X N → ℝ}
    (h : ∀ x ∈ abox N ℓ, F x = G x) :
    (∫ x in abox N ℓ, F x) = ∫ x in abox N ℓ, G x :=
  MeasureTheory.setIntegral_congr_fun (abox_measurable N ℓ) h

/-- The box projection of the zero state. -/
theorem flatOrth_boxPInd_zero {N : ℕ} (V : ℝ) (A : Set E3) (i : Fin N) (x : X N) :
    Work.UBBInputs8.boxPInd V A i (fun _ : X N => (0 : ℝ)) x = 0 := by
  simp only [Work.UBBInputs8.boxPInd, MeasureTheory.integral_zero, zero_mul, mul_zero]

/-- The mean-free box projection of the zero state. -/
theorem flatOrth_boxQInd_zero {N : ℕ} (V : ℝ) (A : Set E3) (i : Fin N) (x : X N) :
    Work.UBBInputs8.boxQInd V A i (fun _ : X N => (0 : ℝ)) x = 0 := by
  rw [Work.UBBInputs8.boxQInd, flatOrth_boxPInd_zero]
  ring

/-- A state vanishing on the box has vanishing box projection on the box. -/
theorem flatOrth_boxPInd_eq_zero_of_eq_zero {N : ℕ} {ℓ : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (V : ℝ) (i : Fin N) {H : X N → ℝ}
    (hH : ∀ x ∈ abox N ℓ, H x = 0) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd V A i H x = 0 := by
  intro x hx
  have h1 : (∫ z in A, H (Function.update x i z)) = 0 := by
    have h2 : (∫ z in A, H (Function.update x i z)) = ∫ z in A, (0 : ℝ) :=
      MeasureTheory.setIntegral_congr_fun hA
        (fun z hz => hH _ (Work.BoseFixB1S.update_mem_abox' hAc hx i hz))
    rw [h2, MeasureTheory.integral_zero]
  simp only [Work.UBBInputs8.boxPInd]
  rw [h1]
  ring

/-- A state vanishing on the box has vanishing mean-free projection on the box. -/
theorem flatOrth_boxQInd_eq_zero_of_eq_zero {N : ℕ} {ℓ : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (V : ℝ) (i : Fin N) {H : X N → ℝ}
    (hH : ∀ x ∈ abox N ℓ, H x = 0) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxQInd V A i H x = 0 := by
  intro x hx
  rw [Work.UBBInputs8.boxQInd, hH x hx,
    flatOrth_boxPInd_eq_zero_of_eq_zero hA hAc V i hH x hx]
  ring

/-- Multiplying a state by the box indicator in its own slot does not change its box
projection: `Pᵢ(1_A(·ᵢ)·Φ) = PᵢΦ`. -/
theorem flatOrth_boxPInd_indicator_self {N : ℕ} {A : Set E3} (hA : MeasurableSet A)
    (V : ℝ) (i : Fin N) (f : X N → ℝ) :
    Work.UBBInputs8.boxPInd V A i (fun y => Work.BoseFixB1S.Aind A (y i) * f y)
      = Work.UBBInputs8.boxPInd V A i f := by
  funext x
  have hmain : (∫ z in A, Work.BoseFixB1S.Aind A ((Function.update x i z) i)
        * f (Function.update x i z))
      = ∫ z in A, f (Function.update x i z) := by
    apply MeasureTheory.setIntegral_congr_fun hA
    intro z hz
    simp only [Function.update_self, Work.BoseFixB1S.Aind, Set.indicator_of_mem hz, one_mul]
  simp only [Work.UBBInputs8.boxPInd]
  rw [hmain]

/-- Multiplying a state by the box indicator in a slot is bounded on the box by the bound of the
state. -/
theorem flatOrth_abs_indicator_mul_le {N : ℕ} (A : Set E3) {ℓ : ℝ} {f : X N → ℝ} {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) (j : Fin N) :
    ∀ x ∈ abox N ℓ, |Work.BoseFixB1S.Aind A (x j) * f x| ≤ C := by
  intro x hx
  rw [abs_mul]
  calc |Work.BoseFixB1S.Aind A (x j)| * |f x|
      ≤ 1 * |f x| :=
        mul_le_mul_of_nonneg_right (Work.BoseFixB1S.Aind_abs_le_one A (x j)) (abs_nonneg _)
    _ ≤ C := by rw [one_mul]; exact hfb x hx

/-- `Qᵢ` is bounded on the box by twice the bound of the state. -/
theorem flatOrth_abs_boxQInd_le {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {f : X N → ℝ} {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) :
    ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A i f x| ≤ 2 * C := by
  intro x hx
  have hP := Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hfb x hx
  have hM := flatOrth_abs_indicator_mul_le A hfb i x hx
  have hQ : Work.UBBInputs8.boxQInd V A i f x
      = Work.BoseFixB1S.Aind A (x i) * f x - Work.UBBInputs8.boxPInd V A i f x := rfl
  rw [hQ]
  calc |Work.BoseFixB1S.Aind A (x i) * f x - Work.UBBInputs8.boxPInd V A i f x|
      ≤ |Work.BoseFixB1S.Aind A (x i) * f x| + |Work.UBBInputs8.boxPInd V A i f x| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (Work.BoseFixB1S.Aind A (x i) * f x) (-(Work.UBBInputs8.boxPInd V A i f x))
    _ ≤ C + C := add_le_add hM hP
    _ = 2 * C := by ring

/-- The diagonal product of the box projections kills: `Pᵢ(QᵢΦ) = 0` on the box (for states
measurable and bounded on the box). -/
theorem flatOrth_boxPInd_boxQInd_zero {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {f : X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A i f) x = 0 := by
  intro x hx
  have hMm : Measurable (fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y) :=
    ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hfm
  have hMb : ∀ y ∈ abox N ℓ, |(fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y) y| ≤ C :=
    fun y hy => flatOrth_abs_indicator_mul_le A hfb i y hy
  have hIntM := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx hMm hMb
  have hIntPf := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
      (Work.BoseFixB1S.measurable_boxPInd V A hA i hfm)
      (Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hfb)
  have hsub := Work.BoseFixB1S.boxPInd_sub V A i x
    (Φ := fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y)
    (Ψ := Work.UBBInputs8.boxPInd V A i f) hIntM hIntPf
  have hQ : Work.UBBInputs8.boxQInd V A i f
      = (fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y) - Work.UBBInputs8.boxPInd V A i f :=
    rfl
  rw [hQ, hsub, flatOrth_boxPInd_indicator_self hA V i f,
    Work.BoseFixB1.boxPInd_self_idem hV hA hVeq i f]
  ring

/-! ## 1. The orientation swaps of the one-slot operators

These are the operator identities `PᵢPⱼ = PⱼPᵢ`, `PᵢQⱼ = QⱼPᵢ`, `QᵢPⱼ = PⱼQᵢ`, `QᵢQⱼ = QⱼQᵢ`
for `i ≠ j`, at points of the box and for states measurable and bounded on the box.  Only the
first is analytic (`boxPPcomm_bdd`, Fubini over `A × A`); the other three are algebraic
consequences of `boxPInd_smul` (multipliers in another slot), `boxPInd_sub` (linearity of `Pᵢ`)
and the first swap. -/

theorem flatOrth_PPswap {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {f : X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) {i j : Fin N} (hij : i ≠ j) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j f) x
      = Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i f) x :=
  fun x hx => boxPPcomm_bdd hℓ hV hA hVeq hAc hfm hfb hij hx

theorem flatOrth_PQswap {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {f : X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) {i j : Fin N} (hij : i ≠ j) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j f) x
      = Work.UBBInputs8.boxQInd V A j (Work.UBBInputs8.boxPInd V A i f) x := by
  intro x hx
  have hMm : Measurable (fun y : X N => Work.BoseFixB1S.Aind A (y j) * f y) :=
    ((measurable_const.indicator hA).comp (measurable_pi_apply j)).mul hfm
  have hMb : ∀ y ∈ abox N ℓ, |(fun y : X N => Work.BoseFixB1S.Aind A (y j) * f y) y| ≤ C :=
    fun y hy => flatOrth_abs_indicator_mul_le A hfb j y hy
  have hIntM := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx hMm hMb
  have hIntPj := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
      (Work.BoseFixB1S.measurable_boxPInd V A hA j hfm)
      (Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc j hfb)
  have hsub := Work.BoseFixB1S.boxPInd_sub V A i x
    (Φ := fun y : X N => Work.BoseFixB1S.Aind A (y j) * f y)
    (Ψ := Work.UBBInputs8.boxPInd V A j f) hIntM hIntPj
  have h1 : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j f) x
      = Work.UBBInputs8.boxPInd V A i ((fun y : X N => Work.BoseFixB1S.Aind A (y j) * f y)
          - Work.UBBInputs8.boxPInd V A j f) x := rfl
  have h2 : Work.UBBInputs8.boxPInd V A i ((fun y : X N => Work.BoseFixB1S.Aind A (y j) * f y)
        - Work.UBBInputs8.boxPInd V A j f) x
      = Work.BoseFixB1S.Aind A (x j) * Work.UBBInputs8.boxPInd V A i f x
        - Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i f) x := by
    rw [hsub, Work.BoseFixB1S.boxPInd_smul V A hij f x,
      flatOrth_PPswap hℓ hV hA hVeq hAc hfm hfb hij x hx]
  rw [h1, h2]
  simp only [Work.UBBInputs8.boxQInd, Work.BoseFixB1S.Aind]

theorem flatOrth_QPswap {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {f : X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) {i j : Fin N} (hij : i ≠ j) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxPInd V A j f) x
      = Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i f) x := by
  intro x hx
  have hMm : Measurable (fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y) :=
    ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hfm
  have hMb : ∀ y ∈ abox N ℓ, |(fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y) y| ≤ C :=
    fun y hy => flatOrth_abs_indicator_mul_le A hfb i y hy
  have hIntM := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc j x hx hMm hMb
  have hIntPi := Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc j x hx
      (Work.BoseFixB1S.measurable_boxPInd V A hA i hfm)
      (Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hfb)
  have hsub := Work.BoseFixB1S.boxPInd_sub V A j x
    (Φ := fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y)
    (Ψ := Work.UBBInputs8.boxPInd V A i f) hIntM hIntPi
  have h1 : Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxPInd V A j f) x
      = Work.BoseFixB1S.Aind A (x i) * Work.UBBInputs8.boxPInd V A j f x
        - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j f) x := rfl
  have h2 : Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i f) x
      = Work.UBBInputs8.boxPInd V A j ((fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y)
          - Work.UBBInputs8.boxPInd V A i f) x := rfl
  have h3 : Work.UBBInputs8.boxPInd V A j ((fun y : X N => Work.BoseFixB1S.Aind A (y i) * f y)
        - Work.UBBInputs8.boxPInd V A i f) x
      = Work.BoseFixB1S.Aind A (x i) * Work.UBBInputs8.boxPInd V A j f x
        - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j f) x := by
    rw [hsub, Work.BoseFixB1S.boxPInd_smul V A hij.symm f x,
      flatOrth_PPswap hℓ hV hA hVeq hAc hfm hfb hij x hx]
  rw [h1, h2, h3]

theorem flatOrth_QQswap {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {f : X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) {i j : Fin N} (hij : i ≠ j) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxQInd V A j f) x
      = Work.UBBInputs8.boxQInd V A j (Work.UBBInputs8.boxQInd V A i f) x := by
  intro x hx
  have h1 : Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxQInd V A j f) x
      = Work.BoseFixB1S.Aind A (x i) * Work.UBBInputs8.boxQInd V A j f x
        - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j f) x := rfl
  have h2 : Work.UBBInputs8.boxQInd V A j (Work.UBBInputs8.boxQInd V A i f) x
      = Work.BoseFixB1S.Aind A (x j) * Work.UBBInputs8.boxQInd V A i f x
        - Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i f) x := rfl
  have h3 : Work.UBBInputs8.boxQInd V A j f x
      = Work.BoseFixB1S.Aind A (x j) * f x - Work.UBBInputs8.boxPInd V A j f x := rfl
  have h4 : Work.UBBInputs8.boxQInd V A i f x
      = Work.BoseFixB1S.Aind A (x i) * f x - Work.UBBInputs8.boxPInd V A i f x := rfl
  have h5 : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j f) x
      = Work.BoseFixB1S.Aind A (x j) * Work.UBBInputs8.boxPInd V A i f x
        - Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i f) x := by
    rw [flatOrth_PQswap hℓ hV hA hVeq hAc hfm hfb hij x hx]
    rfl
  have h6 : Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i f) x
      = Work.BoseFixB1S.Aind A (x i) * Work.UBBInputs8.boxPInd V A j f x
        - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j f) x := by
    rw [← flatOrth_QPswap hℓ hV hA hVeq hAc hfm hfb hij x hx]
    rfl
  have h7 := flatOrth_PPswap hℓ hV hA hVeq hAc hfm hfb hij x hx
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

/-! ## 2. The fold commutes with a one-slot operator in a fresh slot -/

/-- Rewriting the argument of a one-slot operator by a pointwise identity on the box. -/
theorem flatOrth_boxPInd_congr {N : ℕ} {ℓ V : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {f g : X N → ℝ}
    (h : ∀ x ∈ abox N ℓ, f x = g x) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd V A i f x = Work.UBBInputs8.boxPInd V A i g x := by
  intro x hx
  have h1 : (∫ z in A, f (Function.update x i z)) = ∫ z in A, g (Function.update x i z) :=
    MeasureTheory.setIntegral_congr_fun hA
      (fun z hz => h _ (Work.BoseFixB1S.update_mem_abox' hAc hx i hz))
  simp only [Work.UBBInputs8.boxPInd]
  rw [h1]

/-- The `Q` version of `flatOrth_boxPInd_congr`. -/
theorem flatOrth_boxQInd_congr {N : ℕ} {ℓ V : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {f g : X N → ℝ}
    (h : ∀ x ∈ abox N ℓ, f x = g x) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxQInd V A i f x = Work.UBBInputs8.boxQInd V A i g x := by
  intro x hx
  simp only [Work.UBBInputs8.boxQInd]
  rw [h x hx, flatOrth_boxPInd_congr hA hAc i h x hx]

/-- The fold commutes with the box projection in a slot outside the list. -/
theorem flatOrth_fold_comm_boxPInd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) {f : X N → ℝ} (hfm : Measurable f)
    {C : ℝ} (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) (i : Fin N) :
    ∀ (l : List (Fin N)), l.Nodup → i ∉ l → ∀ x ∈ abox N ℓ,
      flatPieceList V A l S (Work.UBBInputs8.boxPInd V A i f) x
        = Work.UBBInputs8.boxPInd V A i (flatPieceList V A l S f) x := by
  intro l
  induction l with
  | nil =>
    intro _ _ x _
    rfl
  | cons j l' ih =>
    intro hl hi x hx
    obtain ⟨hjl', hl'⟩ := List.nodup_cons.mp hl
    have hi' : i ∉ l' := fun h => hi (List.mem_cons.mpr (Or.inr h))
    have hij : j ≠ i := fun h => hi (by rw [← h]; exact List.mem_cons_self)
    have hF : ∀ y ∈ abox N ℓ, flatPieceList V A l' S (Work.UBBInputs8.boxPInd V A i f) y
        = (Work.UBBInputs8.boxPInd V A i (flatPieceList V A l' S f)) y :=
      ih hl' hi'
    obtain ⟨hGm, CG, hGb⟩ := flatPieceList_meas_bdd hℓ hV hA hVeq hAc l' S hfm hfb
    calc flatPieceList V A (j :: l') S (Work.UBBInputs8.boxPInd V A i f) x
        = (if j ∈ S then Work.UBBInputs8.boxPInd V A j else Work.UBBInputs8.boxQInd V A j)
            (Work.UBBInputs8.boxPInd V A i (flatPieceList V A l' S f)) x := by
          rw [flatPieceList_cons]
          split_ifs with hjS
          · exact flatOrth_boxPInd_congr hA hAc j hF x hx
          · exact flatOrth_boxQInd_congr hA hAc j hF x hx
      _ = Work.UBBInputs8.boxPInd V A i
            ((if j ∈ S then Work.UBBInputs8.boxPInd V A j else Work.UBBInputs8.boxQInd V A j)
              (flatPieceList V A l' S f)) x := by
          split_ifs with hjS
          · exact flatOrth_PPswap hℓ hV hA hVeq hAc hGm hGb hij x hx
          · exact flatOrth_QPswap hℓ hV hA hVeq hAc hGm hGb hij x hx
      _ = Work.UBBInputs8.boxPInd V A i (flatPieceList V A (j :: l') S f) x := by
          rw [flatPieceList_cons]

/-- The fold commutes with the mean-free box projection in a slot outside the list. -/
theorem flatOrth_fold_comm_boxQInd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) {f : X N → ℝ} (hfm : Measurable f)
    {C : ℝ} (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) (i : Fin N) :
    ∀ (l : List (Fin N)), l.Nodup → i ∉ l → ∀ x ∈ abox N ℓ,
      flatPieceList V A l S (Work.UBBInputs8.boxQInd V A i f) x
        = Work.UBBInputs8.boxQInd V A i (flatPieceList V A l S f) x := by
  intro l
  induction l with
  | nil =>
    intro _ _ x _
    rfl
  | cons j l' ih =>
    intro hl hi x hx
    obtain ⟨hjl', hl'⟩ := List.nodup_cons.mp hl
    have hi' : i ∉ l' := fun h => hi (List.mem_cons.mpr (Or.inr h))
    have hij : j ≠ i := fun h => hi (by rw [← h]; exact List.mem_cons_self)
    have hF : ∀ y ∈ abox N ℓ, flatPieceList V A l' S (Work.UBBInputs8.boxQInd V A i f) y
        = (Work.UBBInputs8.boxQInd V A i (flatPieceList V A l' S f)) y :=
      ih hl' hi'
    obtain ⟨hGm, CG, hGb⟩ := flatPieceList_meas_bdd hℓ hV hA hVeq hAc l' S hfm hfb
    calc flatPieceList V A (j :: l') S (Work.UBBInputs8.boxQInd V A i f) x
        = (if j ∈ S then Work.UBBInputs8.boxPInd V A j else Work.UBBInputs8.boxQInd V A j)
            (Work.UBBInputs8.boxQInd V A i (flatPieceList V A l' S f)) x := by
          rw [flatPieceList_cons]
          split_ifs with hjS
          · exact flatOrth_boxPInd_congr hA hAc j hF x hx
          · exact flatOrth_boxQInd_congr hA hAc j hF x hx
      _ = Work.UBBInputs8.boxQInd V A i
            ((if j ∈ S then Work.UBBInputs8.boxPInd V A j else Work.UBBInputs8.boxQInd V A j)
              (flatPieceList V A l' S f)) x := by
          split_ifs with hjS
          · exact flatOrth_PQswap hℓ hV hA hVeq hAc hGm hGb hij x hx
          · exact flatOrth_QQswap hℓ hV hA hVeq hAc hGm hGb hij x hx
      _ = Work.UBBInputs8.boxQInd V A i (flatPieceList V A (j :: l') S f) x := by
          rw [flatPieceList_cons]

/-! ## 3. Self-adjointness of the fold -/

/-- The fold is self-adjoint on `L²(abox N ℓ)` for states measurable and bounded on the box. -/
theorem flatOrth_fold_selfadj {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) {f : X N → ℝ} (hfm : Measurable f)
    {Cf : ℝ} (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf) :
    ∀ (l : List (Fin N)), l.Nodup → ∀ (g : X N → ℝ), Measurable g →
      (∃ Cg : ℝ, ∀ x ∈ abox N ℓ, |g x| ≤ Cg) →
        (∫ x in abox N ℓ, flatPieceList V A l S f x * g x)
          = ∫ x in abox N ℓ, f x * flatPieceList V A l S g x := by
  intro l
  induction l with
  | nil =>
    intro _ g _ _
    rfl
  | cons i l' ih =>
    intro hl g hgm hgb
    obtain ⟨Cg, hgb⟩ := hgb
    obtain ⟨hil', hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨hFm, CF, hFb⟩ := flatPieceList_meas_bdd hℓ hV hA hVeq hAc l' S hfm hfb
    have hPgm : Measurable (Work.UBBInputs8.boxPInd V A i g) :=
      Work.BoseFixB1S.measurable_boxPInd V A hA i hgm
    have hPgb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd V A i g x| ≤ Cg :=
      Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hgb
    have hQgm : Measurable (Work.UBBInputs8.boxQInd V A i g) :=
      Work.SlotWord.measurable_boxQInd V A hA i hgm
    have hQgb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A i g x| ≤ 2 * Cg :=
      flatOrth_abs_boxQInd_le hℓ hV hA hVeq hAc i hgb
    conv_lhs => rw [flatPieceList_cons]
    split_ifs with hiS
    · rw [Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hV hA hVeq hAc i hFm hFb hgm hgb]
      rw [ih hl' (Work.UBBInputs8.boxPInd V A i g) hPgm ⟨Cg, hPgb⟩]
      rw [flatPieceList_cons, if_pos hiS]
      apply flatOrth_integral_congr_abox
      intro x hx
      rw [flatOrth_fold_comm_boxPInd hℓ hV hA hVeq hAc S hgm hgb i l' hl' hil' x hx]
    · rw [boxQInd_selfAdjoint_bdd hℓ hV hA hVeq hAc i hFm hFb hgm hgb]
      rw [ih hl' (Work.UBBInputs8.boxQInd V A i g) hQgm ⟨2 * Cg, hQgb⟩]
      rw [flatPieceList_cons, if_neg hiS]
      apply flatOrth_integral_congr_abox
      intro x hx
      rw [flatOrth_fold_comm_boxQInd hℓ hV hA hVeq hAc S hgm hgb i l' hl' hil' x hx]

/-! ## 4. The product of two distinct folds vanishes -/

/-- If `S` and `T` differ at a slot of the list, then the fold of `S` applied to the fold of `T`
vanishes on the box. -/
theorem flatOrth_fold_prod_zero {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) {f : X N → ℝ} (hfm : Measurable f)
    {C : ℝ} (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) :
    ∀ (l : List (Fin N)), l.Nodup → (∃ i ∈ l, (i ∈ S) ≠ (i ∈ T)) →
      ∀ x ∈ abox N ℓ, flatPieceList V A l S (flatPieceList V A l T f) x = 0 := by
  intro l
  induction l with
  | nil =>
    intro _ hd
    obtain ⟨i, hi, _⟩ := hd
    simp at hi
  | cons j l' ih =>
    intro hl hd x hx
    obtain ⟨hjl', hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨hGm, CG, hGb⟩ := flatPieceList_meas_bdd hℓ hV hA hVeq hAc l' T hfm hfb
    obtain ⟨hHm, CH, hHb⟩ := flatPieceList_meas_bdd hℓ hV hA hVeq hAc l' S hGm hGb
    by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T
    · -- `j ∈ S` and `j ∈ T`: the witness slot lies in the tail
      have hd' : ∃ i ∈ l', (i ∈ S) ≠ (i ∈ T) := by
        obtain ⟨i, hi, hne⟩ := hd
        rcases List.mem_cons.mp hi with hij | hi'
        · exact absurd (by rw [hij]; exact propext ⟨fun _ => hjT, fun _ => hjS⟩) hne
        · exact ⟨i, hi', hne⟩
      have hH0 : ∀ y ∈ abox N ℓ, flatPieceList V A l' S (flatPieceList V A l' T f) y = 0 :=
        ih hl' hd'
      rw [flatPieceList_cons, flatPieceList_cons, if_pos hjS, if_pos hjT]
      rw [flatOrth_boxPInd_congr hA hAc j
        (flatOrth_fold_comm_boxPInd hℓ hV hA hVeq hAc S hGm hGb j l' hl' hjl') x hx]
      exact flatOrth_boxPInd_eq_zero_of_eq_zero hA hAc V j
        (flatOrth_boxPInd_eq_zero_of_eq_zero hA hAc V j hH0) x hx
    · -- `j ∈ S` and `j ∉ T`: `Pⱼ Qⱼ = 0`
      rw [flatPieceList_cons, flatPieceList_cons, if_pos hjS, if_neg hjT]
      rw [flatOrth_boxPInd_congr hA hAc j
        (flatOrth_fold_comm_boxQInd hℓ hV hA hVeq hAc S hGm hGb j l' hl' hjl') x hx]
      exact flatOrth_boxPInd_boxQInd_zero hℓ hV hA hVeq hAc j hHm hHb x hx
    · -- `j ∉ S` and `j ∈ T`: `Qⱼ Pⱼ = 0`
      rw [flatPieceList_cons, flatPieceList_cons, if_neg hjS, if_pos hjT]
      rw [flatOrth_boxQInd_congr hA hAc j
        (flatOrth_fold_comm_boxPInd hℓ hV hA hVeq hAc S hGm hGb j l' hl' hjl') x hx]
      exact Work.BoseFixB1.boxQInd_self_boxPInd hV hA hVeq j
        (flatPieceList V A l' S (flatPieceList V A l' T f)) x
    · -- `j ∉ S` and `j ∉ T`: the witness slot lies in the tail
      have hd' : ∃ i ∈ l', (i ∈ S) ≠ (i ∈ T) := by
        obtain ⟨i, hi, hne⟩ := hd
        rcases List.mem_cons.mp hi with hij | hi'
        · exact absurd (by rw [hij]; exact propext ⟨fun h => absurd h hjS, fun h => absurd h hjT⟩) hne
        · exact ⟨i, hi', hne⟩
      have hH0 : ∀ y ∈ abox N ℓ, flatPieceList V A l' S (flatPieceList V A l' T f) y = 0 :=
        ih hl' hd'
      rw [flatPieceList_cons, flatPieceList_cons, if_neg hjS, if_neg hjT]
      rw [flatOrth_boxQInd_congr hA hAc j
        (flatOrth_fold_comm_boxQInd hℓ hV hA hVeq hAc S hGm hGb j l' hl' hjl') x hx]
      exact flatOrth_boxQInd_eq_zero_of_eq_zero hA hAc V j
        (flatOrth_boxQInd_eq_zero_of_eq_zero hA hAc V j hH0) x hx

/-! ## 5. The target: distinct flat pieces are orthogonal -/

theorem flatPiece_orthogonal {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (S T : Finset (Fin N)) (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1.flatPiece V A S Φ x * Work.BoseFixB1.flatPiece V A T Φ x) = 0 := by
  obtain ⟨C, hC0, hCb⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have hΦm : Measurable Φ := hΦc.measurable
  -- a slot at which `S` and `T` differ, inside the enumeration `List.finRange N`
  have hdiff : ∃ i ∈ List.finRange N, (i ∈ S) ≠ (i ∈ T) := by
    have hSS : ∃ i : Fin N, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_contra h
      exact hST (Finset.ext fun i => ⟨fun hi => by
        by_contra hni
        exact h ⟨i, Or.inl ⟨hi, hni⟩⟩, fun hi => by
        by_contra hni
        exact h ⟨i, Or.inr ⟨hi, hni⟩⟩⟩)
    obtain ⟨i, hi⟩ := hSS
    refine ⟨i, List.mem_finRange i, ?_⟩
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro heq
      rw [heq] at h1
      exact h2 h1
    · intro heq
      rw [heq] at h2
      exact h2 h1
  obtain ⟨hTm, CT, hTb⟩ :=
    flatPieceList_meas_bdd hℓ hV hA hVeq hAc (List.finRange N) T hΦm hCb
  show (∫ x in abox N ℓ, flatPieceList V A (List.finRange N) S Φ x
      * flatPieceList V A (List.finRange N) T Φ x) = 0
  rw [flatOrth_fold_selfadj hℓ hV hA hVeq hAc S hΦm hCb
    (List.finRange N) (List.nodup_finRange N)
    (flatPieceList V A (List.finRange N) T Φ) hTm ⟨CT, hTb⟩]
  rw [show (0 : ℝ) = ∫ _x in abox N ℓ, (0 : ℝ) from by simp]
  apply flatOrth_integral_congr_abox
  intro x hx
  rw [flatOrth_fold_prod_zero hℓ hV hA hVeq hAc S T hΦm hCb
    (List.finRange N) (List.nodup_finRange N) hdiff x hx, mul_zero]

end Work.BoseFixB1
