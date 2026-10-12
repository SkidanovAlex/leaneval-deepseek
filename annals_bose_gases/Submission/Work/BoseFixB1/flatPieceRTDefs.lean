import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.a0FlatPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 1000000

/-! ## 1. The slot factors -/

/-- The `i`-th slot reading of the box indicator: `indSlot A i y = 1_A(y i)`. -/
def indSlot (A : Set 𝔼3) {N : ℕ} (i : Fin N) : X N → ℝ :=
  fun y => Work.BoseFixB1S.Aind A (y i)

@[simp] theorem indSlot_apply (A : Set 𝔼3) {N : ℕ} (i : Fin N) (y : X N) :
    indSlot A i y = Work.BoseFixB1S.Aind A (y i) := rfl

@[simp] theorem indSlot_update_self (A : Set 𝔼3) {N : ℕ} (i : Fin N) (x : X N) (z : 𝔼3) :
    indSlot A i (Function.update x i z) = Work.BoseFixB1S.Aind A z := by
  simp [indSlot]

/-- `Aind` is the indicator of `A`, definitionally. -/
theorem Aind_eq_indicator (A : Set 𝔼3) (z : 𝔼3) :
    Work.BoseFixB1S.Aind A z = A.indicator (fun _ => (1 : ℝ)) z := rfl

/-- The indicator of the complement as `1 − 1_A`. -/
theorem indicator_compl (A : Set 𝔼3) (z : 𝔼3) :
    Aᶜ.indicator (fun _ => (1 : ℝ)) z = 1 - Work.BoseFixB1S.Aind A z := by
  rw [Aind_eq_indicator]
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_notMem, Set.indicator_of_mem hz]
    · ring
    · simpa [Set.mem_compl_iff] using hz
  · rw [Set.indicator_of_mem, Set.indicator_of_notMem hz]
    · ring
    · simpa [Set.mem_compl_iff] using hz

/-- `Rᵢ` is multiplication by the complement indicator. -/
theorem rInd_apply {N : ℕ} (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) (y : X N) :
    rInd A i Ψ y = (1 - indSlot A i y) * Ψ y := by
  show Aᶜ.indicator (fun _ => (1 : ℝ)) (y i) * Ψ y
      = (1 - Work.BoseFixB1S.Aind A (y i)) * Ψ y
  rw [indicator_compl]

/-- The slot factor of the slot-`i` operator of a `(S,T)`-piece: `1_A(xᵢ)` for `i ∈ S ∪ T`, and
`1_{Aᶜ}(xᵢ)` otherwise. -/
def cOf (A : Set 𝔼3) {N : ℕ} (S T : Finset (Fin N)) (i : Fin N) : X N → ℝ :=
  fun y => if i ∈ S ∪ T then Work.BoseFixB1S.Aind A (y i)
    else 1 - Work.BoseFixB1S.Aind A (y i)

theorem cOf_apply (A : Set 𝔼3) {N : ℕ} (S T : Finset (Fin N)) (i : Fin N) (y : X N) :
    cOf A S T i y = if i ∈ S ∪ T then Work.BoseFixB1S.Aind A (y i)
      else 1 - Work.BoseFixB1S.Aind A (y i) := rfl

theorem cOf_of_mem {N : ℕ} {A : Set 𝔼3} {S T : Finset (Fin N)} {i : Fin N}
    (h : i ∈ S ∪ T) : cOf A S T i = indSlot A i := by
  funext y
  simp only [cOf, if_pos h, indSlot]

theorem cOf_of_notMem {N : ℕ} {A : Set 𝔼3} {S T : Finset (Fin N)} {i : Fin N}
    (h : i ∉ S ∪ T) : cOf A S T i = fun y => 1 - indSlot A i y := by
  funext y
  simp only [cOf, if_neg h, indSlot]

theorem cOf_mul_self {N : ℕ} (A : Set 𝔼3) (S T : Finset (Fin N)) (i : Fin N) (y : X N) :
    cOf A S T i y * cOf A S T i y = cOf A S T i y := by
  by_cases h : i ∈ S ∪ T
  · simp only [cOf, if_pos h]
    exact Work.BoseFixB1S.Aind_mul_self A (y i)
  · simp only [cOf, if_neg h]
    have h2 := Work.BoseFixB1S.Aind_mul_self A (y i)
    nlinarith

theorem cOf_invariant {N : ℕ} (A : Set 𝔼3) (S T : Finset (Fin N)) {i j : Fin N} (hij : i ≠ j)
    (y : X N) (z : 𝔼3) :
    cOf A S T j (Function.update y i z) = cOf A S T j y := by
  simp only [cOf]
  rw [Function.update_apply, if_neg (fun h : j = i => hij h.symm)]

/-! ## 2. The list product of slot factors -/

/-- The product of the slot factors over a list of slots. -/
def cFold (A : Set 𝔼3) {N : ℕ} (S T : Finset (Fin N)) : List (Fin N) → X N → ℝ
  | [], _ => 1
  | i :: l, y => cOf A S T i y * cFold A S T l y

@[simp] theorem cFold_nil {N : ℕ} (A : Set 𝔼3) (S T : Finset (Fin N)) :
    cFold A S T ([] : List (Fin N)) = fun _ => (1 : ℝ) := rfl

theorem cFold_cons_apply {N : ℕ} (A : Set 𝔼3) (S T : Finset (Fin N)) (i : Fin N)
    (l : List (Fin N)) (y : X N) :
    cFold A S T (i :: l) y = cOf A S T i y * cFold A S T l y := rfl

/-- `cFold` over a list of slots not containing `i` is invariant under updating the slot `i`. -/
theorem cFold_invariant {N : ℕ} (A : Set 𝔼3) (S T : Finset (Fin N)) (l : List (Fin N))
    {i : Fin N} (hi : i ∉ l) (y : X N) (z : 𝔼3) :
    cFold A S T l (Function.update y i z) = cFold A S T l y := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at hi
    obtain ⟨hij, hil⟩ := hi
    simp only [cFold_cons_apply]
    rw [cOf_invariant A S T hij y z, ih hil]

/-- Remove *every* occurrence of a slot from a list of slots. -/
def eraseSlot {N : ℕ} : List (Fin N) → Fin N → List (Fin N)
  | [], _ => []
  | j :: l, i => if j = i then eraseSlot l i else j :: eraseSlot l i

theorem not_mem_eraseSlot {N : ℕ} (l : List (Fin N)) (i : Fin N) : i ∉ eraseSlot l i := by
  induction l with
  | nil => simp [eraseSlot]
  | cons j l ih =>
    by_cases hji : j = i
    · simp only [eraseSlot, if_pos hji]
      exact ih
    · simp only [eraseSlot, if_neg hji, List.mem_cons, not_or]
      exact ⟨fun h => hji h.symm, ih⟩

theorem eraseSlot_eq_self_of_notMem {N : ℕ} {l : List (Fin N)} {i : Fin N} (hi : i ∉ l) :
    eraseSlot l i = l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at hi
    obtain ⟨hij, hil⟩ := hi
    have hji : ¬ (j = i) := fun h => hij h.symm
    simp only [eraseSlot, if_neg hji, ih hil]

/-- **Extraction of the slot factor at a slot in the list**: the product over a list splits off
the factor of any one of its slots. -/
theorem cFold_eq_cOf_mul_eraseSlot {N : ℕ} (A : Set 𝔼3) (S T : Finset (Fin N))
    (l : List (Fin N)) (i : Fin N) (hi : i ∈ l) (y : X N) :
    cFold A S T l y = cOf A S T i y * cFold A S T (eraseSlot l i) y := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.mem_cons] at hi
    by_cases hij : i = j
    · rw [hij]
      rw [hij] at ih
      rw [cFold_cons_apply]
      by_cases hil : j ∈ l
      · rw [ih hil, show eraseSlot (j :: l) j = eraseSlot l j from by simp [eraseSlot],
          ← mul_assoc, cOf_mul_self]
      · rw [show eraseSlot (j :: l) j = eraseSlot l j from by simp [eraseSlot],
          eraseSlot_eq_self_of_notMem hil]
    · have hi' : i ∈ l := by
        rcases hi with h | h
        · exact absurd h hij
        · exact h
      have hji : ¬ (j = i) := fun hh => hij hh.symm
      rw [cFold_cons_apply,
        show eraseSlot (j :: l) i = j :: eraseSlot l i from by simp [eraseSlot, hji],
        cFold_cons_apply, ih hi']
      ring

/-! ## 3. The fold of the mean parts -/

/-- The fold of the mean parts `oneMean i`, `id − oneMean i`, `id` of the slot operators of a
`(S,T)`-piece, in the order in which `flatPieceRTList` applies them. -/
def tFold (V : ℝ) (A : Set 𝔼3) {N : ℕ} (S T : Finset (Fin N)) :
    List (Fin N) → (X N → ℝ) → (X N → ℝ)
  | [], Ψ => Ψ
  | i :: l, Ψ =>
      (if i ∈ S then (fun f => Work.BoseFixB1S.oneMean V A i f)
       else if i ∈ T then (fun f => f - Work.BoseFixB1S.oneMean V A i f)
       else id) (tFold V A S T l Ψ)

@[simp] theorem tFold_nil {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N))
    (Ψ : X N → ℝ) : tFold V A S T ([] : List (Fin N)) Ψ = Ψ := rfl

theorem tFold_cons_of_mem_S {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N)) {i : Fin N}
    (hi : i ∈ S) (l : List (Fin N)) (Ψ : X N → ℝ) :
    tFold V A S T (i :: l) Ψ = Work.BoseFixB1S.oneMean V A i (tFold V A S T l Ψ) := by
  show (if i ∈ S then (fun f => Work.BoseFixB1S.oneMean V A i f)
      else if i ∈ T then (fun f => f - Work.BoseFixB1S.oneMean V A i f) else id)
      (tFold V A S T l Ψ) = Work.BoseFixB1S.oneMean V A i (tFold V A S T l Ψ)
  rw [if_pos hi]

theorem tFold_cons_of_mem_T {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N)) {i : Fin N}
    (hiS : i ∉ S) (hiT : i ∈ T) (l : List (Fin N)) (Ψ : X N → ℝ) :
    tFold V A S T (i :: l) Ψ
      = tFold V A S T l Ψ - Work.BoseFixB1S.oneMean V A i (tFold V A S T l Ψ) := by
  show (if i ∈ S then (fun f => Work.BoseFixB1S.oneMean V A i f)
      else if i ∈ T then (fun f => f - Work.BoseFixB1S.oneMean V A i f) else id)
      (tFold V A S T l Ψ)
      = tFold V A S T l Ψ - Work.BoseFixB1S.oneMean V A i (tFold V A S T l Ψ)
  rw [if_neg hiS, if_pos hiT]

theorem tFold_cons_of_notMem {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N)) {i : Fin N}
    (hiS : i ∉ S) (hiT : i ∉ T) (l : List (Fin N)) (Ψ : X N → ℝ) :
    tFold V A S T (i :: l) Ψ = tFold V A S T l Ψ := by
  show (if i ∈ S then (fun f => Work.BoseFixB1S.oneMean V A i f)
      else if i ∈ T then (fun f => f - Work.BoseFixB1S.oneMean V A i f) else id)
      (tFold V A S T l Ψ) = tFold V A S T l Ψ
  rw [if_neg hiS, if_neg hiT]
  rfl

/-! ## 4. The `oneMean` calculus -/

/-- A factor that is invariant under the slot-`i` update pulls out of the slot-`i` mean. -/
theorem oneMean_mul_of_invariant {N : ℕ} {V : ℝ} {A : Set 𝔼3} (i : Fin N) {h : X N → ℝ}
    {f : X N → ℝ} (hinv : ∀ y z, h (Function.update y i z) = h y) :
    Work.BoseFixB1S.oneMean V A i (fun y => h y * f y)
      = fun y => h y * Work.BoseFixB1S.oneMean V A i f y := by
  funext x
  have h1 : (∫ z in A, h (Function.update x i z) * f (Function.update x i z))
      = ∫ z in A, h x * f (Function.update x i z) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [hinv x z]
  show (1 / V) * (∫ z in A, h (Function.update x i z) * f (Function.update x i z))
      = h x * ((1 / V) * ∫ z in A, f (Function.update x i z))
  rw [h1, MeasureTheory.integral_const_mul]
  ring

/-- The slot-`i` mean absorbs the slot-`i` box indicator. -/
theorem oneMean_indSlot_mul {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A) (i : Fin N)
    (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i (fun y => indSlot A i y * f y)
      = Work.BoseFixB1S.oneMean V A i f := by
  funext x
  show (1 / V) * (∫ z in A, indSlot A i (Function.update x i z) * f (Function.update x i z))
      = (1 / V) * ∫ z in A, f (Function.update x i z)
  congr 1
  apply MeasureTheory.setIntegral_congr_fun hA
  intro z hz
  have hz1 : Work.BoseFixB1S.Aind A z = 1 := by
    rw [Work.BoseFixB1S.Aind, Set.indicator_of_mem hz]
  show indSlot A i (Function.update x i z) * f (Function.update x i z) = f (Function.update x i z)
  rw [indSlot_update_self, hz1, one_mul]

/-- The slot-`i` mean kills the complementary slot-`i` indicator. -/
theorem oneMean_one_sub_indSlot_mul {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A)
    (i : Fin N) (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i (fun y => (1 - indSlot A i y) * f y) = 0 := by
  funext x
  show (1 / V) * (∫ z in A,
      (1 - indSlot A i (Function.update x i z)) * f (Function.update x i z)) = 0
  have h1 : (∫ z in A,
      (1 - indSlot A i (Function.update x i z)) * f (Function.update x i z)) = 0 := by
    have hz : ∀ z ∈ A,
        (1 - indSlot A i (Function.update x i z)) * f (Function.update x i z) = 0 := by
      intro z hz
      have hz1 : Work.BoseFixB1S.Aind A z = 1 := by
        rw [Work.BoseFixB1S.Aind, Set.indicator_of_mem hz]
      rw [indSlot_update_self, hz1, sub_self, zero_mul]
    rw [MeasureTheory.setIntegral_congr_fun hA hz, MeasureTheory.integral_zero]
  rw [h1, mul_zero]

/-- The slot-`i` mean is idempotent. -/
theorem oneMean_idem {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hVeq : V = (volume A).toReal) (hV : V ≠ 0)
    (i : Fin N) (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i (Work.BoseFixB1S.oneMean V A i f)
      = Work.BoseFixB1S.oneMean V A i f := by
  funext x
  have h1 : (∫ z in A, Work.BoseFixB1S.oneMean V A i f (Function.update x i z))
      = ∫ z in A, Work.BoseFixB1S.oneMean V A i f x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    exact Work.BoseFixB1S.oneMean_slot V A i f x z
  show (1 / V) * (∫ z in A, Work.BoseFixB1S.oneMean V A i f (Function.update x i z))
      = (1 / V) * ∫ z in A, f (Function.update x i z)
  rw [h1, MeasureTheory.setIntegral_const, smul_eq_mul, Measure.real_def, ← hVeq]
  rw [show Work.BoseFixB1S.oneMean V A i f x = (1 / V) * ∫ z in A, f (Function.update x i z)
    from rfl]
  field_simp

/-- The slot mean of the zero function vanishes. -/
theorem oneMean_zero {N : ℕ} (V : ℝ) {A : Set 𝔼3} (i : Fin N) :
    Work.BoseFixB1S.oneMean V A i (0 : X N → ℝ) = 0 := by
  funext x
  show (1 / V) * (∫ z in A, (0 : X N → ℝ) (Function.update x i z)) = 0
  simp

/-- A continuous state composed with a slot update is integrable over a box inside `acube ℓ`. -/
theorem integrableOn_comp_update {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set 𝔼3}
    (hAc : A ⊆ acube ℓ) (i : Fin N) {f : X N → ℝ} (hf : Continuous f) (x : X N) :
    IntegrableOn (fun z : 𝔼3 => f (Function.update x i z)) A volume := by
  have hcont : Continuous fun z : 𝔼3 => f (Function.update x i z) := by
    fun_prop
  exact (hcont.continuousOn.integrableOn_compact (acube_compact hℓ)).mono_set hAc

/-- The slot mean is additive on continuous states. -/
theorem oneMean_sub_of_continuous {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) {A : Set 𝔼3}
    (hAc : A ⊆ acube ℓ) (i : Fin N) {f g : X N → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Work.BoseFixB1S.oneMean V A i (f - g)
      = Work.BoseFixB1S.oneMean V A i f - Work.BoseFixB1S.oneMean V A i g := by
  funext x
  show (1 / V) * (∫ z in A, (f - g) (Function.update x i z))
      = (1 / V) * (∫ z in A, f (Function.update x i z))
        - (1 / V) * (∫ z in A, g (Function.update x i z))
  rw [show (∫ z in A, (f - g) (Function.update x i z))
      = ∫ z in A, (f (Function.update x i z) - g (Function.update x i z)) from rfl]
  rw [MeasureTheory.integral_sub (integrableOn_comp_update hℓ hAc i hf x)
    (integrableOn_comp_update hℓ hAc i hg x)]
  ring

/-- Re-export of the continuity of the slot mean of a continuous state. -/
theorem exists_update_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦ : Continuous Φ) (i : Fin N) (K : Set (X N)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ a ∈ acube ℓ, |Φ (Function.update x i a)| ≤ C := by
  have hK' : IsCompact (K ×ˢ acube ℓ) := hK.prod (acube_compact hℓ)
  have hcont : ContinuousOn (fun p : X N × 𝔼3 => Φ (Function.update p.1 i p.2))
      (K ×ˢ acube ℓ) :=
    hΦ.continuousOn.comp (continuous_update i).continuousOn (fun p _ => Set.mem_univ _)
  obtain ⟨C, hC⟩ := hK'.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx a ha => ?_⟩
  have h := hC (x, a) ⟨hx, ha⟩
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- The slot mean of a continuous state is continuous. -/
theorem continuous_oneMean {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : Continuous Φ) : Continuous (Work.BoseFixB1S.oneMean V A i Φ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hAfin : (volume : Measure 𝔼3) A < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono hAc) (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  haveI : IsFiniteMeasure ((volume : Measure 𝔼3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hAfin.ne
  obtain ⟨C, hC0, hC⟩ :=
    exists_update_bound hℓ hΦ i (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1)
  have hmain : ContinuousAt (fun x => ∫ a in A, Φ (Function.update x i a)) x₀ := by
    refine continuousAt_of_dominated
      (μ := (volume : Measure 𝔼3).restrict A)
      (F := fun x a => Φ (Function.update x i a)) (bound := fun _ => C) (x₀ := x₀) ?_ ?_ ?_ ?_
    · filter_upwards with x
      exact (hΦ.comp ((continuous_update i).comp
        (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
      rw [ae_restrict_iff' hA]
      filter_upwards with a ha
      exact hC x (Metric.ball_subset_closedBall hx) a (hAc ha)
    · exact MeasureTheory.integrable_const C
    · filter_upwards with a
      exact (hΦ.comp ((continuous_update i).comp
        (Continuous.prodMk continuous_id continuous_const))).continuousAt
  show ContinuousAt (fun x => (1 / V) * ∫ a in A, Φ (Function.update x i a)) x₀
  exact hmain.const_mul (1 / V)

/-- The two-slot mean is the iterated slot mean. -/
theorem twoMean_eq_oneMean_comp {N : ℕ} (V : ℝ) (A : Set 𝔼3) (f : X N → ℝ) (i j : Fin N) :
    Work.BoseFixB1S.twoMean V A i j f
      = Work.BoseFixB1S.oneMean V A i (Work.BoseFixB1S.oneMean V A j f) := by
  funext x
  simp only [Work.BoseFixB1S.twoMean, Work.BoseFixB1S.oneMean]
  rw [MeasureTheory.integral_const_mul]

/-- The slot means in two distinct slots commute (Fubini), for a continuous state. -/
theorem oneMean_comm_continuous {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {f : X N → ℝ} (hf : Continuous f) :
    Work.BoseFixB1S.oneMean V A i (Work.BoseFixB1S.oneMean V A j f)
      = Work.BoseFixB1S.oneMean V A j (Work.BoseFixB1S.oneMean V A i f) := by
  funext x
  rw [← twoMean_eq_oneMean_comp V A f i j, ← twoMean_eq_oneMean_comp V A f j i]
  exact Work.BoseFixB1S.twoMean_comm hℓ hA hAc hij hf x

/-- The slot mean only depends on the state as a function. -/
theorem oneMean_congr {N : ℕ} (V : ℝ) {A : Set 𝔼3} (i : Fin N) {f g : X N → ℝ} (h : f = g) :
    Work.BoseFixB1S.oneMean V A i f = Work.BoseFixB1S.oneMean V A i g := by rw [h]

/-! ## 5. Function-level forms of the three slot operators and of the factor arithmetic -/

/-- The slot indicator is idempotent. -/
theorem indSlot_mul_self {N : ℕ} (A : Set 𝔼3) (i : Fin N) :
    indSlot A i * indSlot A i = indSlot A i := by
  funext y
  exact Work.BoseFixB1S.Aind_mul_self A (y i)

/-- The complementary slot indicator is idempotent. -/
theorem one_sub_indSlot_mul_self {N : ℕ} (A : Set 𝔼3) (i : Fin N) :
    (1 - indSlot A i) * (1 - indSlot A i) = 1 - indSlot A i := by
  funext y
  have h := Work.BoseFixB1S.Aind_mul_self A (y i)
  show (1 - Work.BoseFixB1S.Aind A (y i)) * (1 - Work.BoseFixB1S.Aind A (y i))
      = 1 - Work.BoseFixB1S.Aind A (y i)
  nlinarith

/-- The two complementary slot indicators multiply to zero. -/
theorem indSlot_mul_one_sub {N : ℕ} (A : Set 𝔼3) (i : Fin N) :
    indSlot A i * (1 - indSlot A i) = 0 := by
  funext y
  have h := Work.BoseFixB1S.Aind_mul_self A (y i)
  show Work.BoseFixB1S.Aind A (y i) * (1 - Work.BoseFixB1S.Aind A (y i)) = 0
  nlinarith

/-- `indSlotᵢ · (indSlotᵢ · X) = indSlotᵢ · X`. -/
theorem indSlot_mul_indSlot_mul {N : ℕ} (A : Set 𝔼3) (i : Fin N) (X : X N → ℝ) :
    indSlot A i * (indSlot A i * X) = indSlot A i * X := by
  rw [← mul_assoc, indSlot_mul_self]

/-- `(1 − indSlotᵢ) · ((1 − indSlotᵢ) · X) = (1 − indSlotᵢ) · X`. -/
theorem one_sub_indSlot_mul_one_sub_indSlot_mul {N : ℕ} (A : Set 𝔼3) (i : Fin N) (X : X N → ℝ) :
    (1 - indSlot A i) * ((1 - indSlot A i) * X) = (1 - indSlot A i) * X := by
  rw [← mul_assoc, one_sub_indSlot_mul_self]

/-- `indSlotᵢ · ((1 − indSlotᵢ) · X) = 0`. -/
theorem indSlot_mul_one_sub_indSlot_mul {N : ℕ} (A : Set 𝔼3) (i : Fin N) (X : X N → ℝ) :
    indSlot A i * ((1 - indSlot A i) * X) = 0 := by
  rw [← mul_assoc, indSlot_mul_one_sub, zero_mul]

/-- `(1 − indSlotᵢ) · (indSlotᵢ · X) = 0`. -/
theorem one_sub_indSlot_mul_indSlot_mul {N : ℕ} (A : Set 𝔼3) (i : Fin N) (X : X N → ℝ) :
    (1 - indSlot A i) * (indSlot A i * X) = 0 := by
  rw [← mul_assoc, mul_comm (1 - indSlot A i) (indSlot A i), indSlot_mul_one_sub, zero_mul]

/-- `Pᵢ` as a product of the slot factor and the mean part, at the level of functions. -/
theorem boxPInd_eq_fun {N : ℕ} (V : ℝ) (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxPInd V A i Ψ = indSlot A i * Work.BoseFixB1S.oneMean V A i Ψ := by
  funext x
  rw [Pi.mul_apply, indSlot_apply, Work.BoseFixB1S.boxPInd_eq]

/-- `Qᵢ` as a product of the slot factor and the mean part, at the level of functions. -/
theorem boxQInd_eq_fun {N : ℕ} (V : ℝ) (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxQInd V A i Ψ = indSlot A i * Ψ - Work.UBBInputs8.boxPInd V A i Ψ := by
  funext x
  rw [Pi.sub_apply, Pi.mul_apply, indSlot_apply, Work.BoseFixB1S.boxQInd_eq]

/-- `Rᵢ` as multiplication by the complementary slot factor, at the level of functions. -/
theorem rInd_eq_fun {N : ℕ} (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) :
    rInd A i Ψ = (1 - indSlot A i) * Ψ := by
  funext y
  rw [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, rInd_apply]

/-- A slot-invariant factor pulls out of the slot mean, function-product form. -/
theorem oneMean_mul_of_invariant_fun {N : ℕ} {V : ℝ} {A : Set 𝔼3} (i : Fin N) {h : X N → ℝ}
    (hinv : ∀ y z, h (Function.update y i z) = h y) (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i (h * f) = h * Work.BoseFixB1S.oneMean V A i f :=
  oneMean_mul_of_invariant (V := V) (A := A) (i := i) hinv

/-- The slot mean absorbs the slot indicator, function-product form. -/
theorem oneMean_indSlot_mul_fun {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A)
    (i : Fin N) (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i (indSlot A i * f) = Work.BoseFixB1S.oneMean V A i f :=
  oneMean_indSlot_mul hA i f

/-- The slot mean kills the complementary slot indicator, function-product form. -/
theorem oneMean_one_sub_indSlot_mul_fun {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A)
    (i : Fin N) (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i ((1 - indSlot A i) * f) = 0 :=
  oneMean_one_sub_indSlot_mul hA i f

/-- The slot mean of `indSlotᵢ · (h · f)` for a slot-`i`-invariant `h`. -/
theorem oneMean_indSlot_mul_invariant {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A)
    (i : Fin N) {h : X N → ℝ} (hinv : ∀ y z, h (Function.update y i z) = h y) (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i (indSlot A i * (h * f))
      = h * Work.BoseFixB1S.oneMean V A i f := by
  have h1 : indSlot A i * (h * f) = h * (indSlot A i * f) := by
    funext y
    simp only [Pi.mul_apply]
    ring
  rw [h1, oneMean_mul_of_invariant_fun (V := V) (A := A) (i := i) hinv,
    oneMean_indSlot_mul_fun hA i f]

/-- The slot mean of `(1 − indSlotᵢ) · (h · f)` for a slot-`i`-invariant `h` vanishes. -/
theorem oneMean_one_sub_indSlot_mul_invariant {N : ℕ} {V : ℝ} {A : Set 𝔼3}
    (hA : MeasurableSet A) (i : Fin N) {h : X N → ℝ}
    (hinv : ∀ y z, h (Function.update y i z) = h y) (f : X N → ℝ) :
    Work.BoseFixB1S.oneMean V A i ((1 - indSlot A i) * (h * f)) = 0 := by
  have h1 : (1 - indSlot A i) * (h * f) = h * ((1 - indSlot A i) * f) := by
    funext y
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
    ring
  rw [h1, oneMean_mul_of_invariant_fun (V := V) (A := A) (i := i) hinv,
    oneMean_one_sub_indSlot_mul_fun hA i f]
  exact mul_zero h

end Work.BoseFixB1
