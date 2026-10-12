import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.a0FlatPieces
import Submission.Work.BoseFixB1S.Clean.Target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.flatPiece_eigen` — the joint `(P,Q)`-spectral decomposition of the box
projections

With `Pᵢ = UBBInputs8.boxPInd V A i` and `Qᵢ = UBBInputs8.boxQInd V A i` (FS `eq:HBU`, the box
projections *carrying* the box indicator), and `Π_S = flatPiece V A S Φ = (∏_{i∈S}Pᵢ)(∏_{i∉S}Qᵢ)Φ`
(`Work.BoseFixB1.a0FlatPieces`), this file proves the eigenvalue statement

    PᵢΠ_S = [i ∈ S]·Π_S ,        QᵢΠ_S = [i ∉ S]·Π_S ,

i.e. `Π_S` is the spectral projection of the joint `(P,Q)`-family on the `|S|` "occupied" slots.

The mathematical content is the *commutation* of the slot operators `Pᵢ`, `Qᵢ` for `i ≠ j`
(two-slot Fubini over `A × A` together with the commutation of the two slot updates) plus the
one-slot identities `PᵢPᵢ = Pᵢ`, `PᵢQᵢ = 0`, `QᵢPᵢ = 0`, `QᵢQᵢ = Qᵢ`.

Because the intermediate composites `Π_S` are *not* continuous, the auxiliary commutation lemmas
are proved here for the weaker hypothesis class "measurable and bounded on the analysis box
`abox N ℓ`" (which is preserved by `Pᵢ`, `Qᵢ` and which every continuous state satisfies, by the
compactness of `abox N ℓ`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 1600000

/-! ## 1. An elementary measure-theory helper -/

/-- A function which vanishes pointwise on `A` has vanishing integral over `A`. -/
theorem setIntegral_eq_zero_of_eq_zero_on {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {A : Set α} (hA : MeasurableSet A) {f : α → ℝ} (hf : ∀ x ∈ A, f x = 0) :
    ∫ x in A, f x ∂μ = 0 := by
  rw [MeasureTheory.setIntegral_congr_fun hA hf]
  simp

/-- If `∫_A f = a·V` with `V = (μ A).toReal ≠ 0`, then `∫_A (f − a) = 0`.

No measurability nor integrability hypothesis is needed on `f`: in the non-integrable case the
Bochner convention gives `∫_A f = 0`, hence `a = 0`, and then `f − a = f` also has vanishing
integral. -/
theorem setIntegral_sub_const_eq_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A : Set α} (hfin : μ A < ⊤) {f : α → ℝ} {a : ℝ} (hV : (μ A).toReal ≠ 0)
    (h : ∫ x in A, f x ∂μ = a * (μ A).toReal) :
    ∫ x in A, (f x - a) ∂μ = 0 := by
  by_cases hf : Integrable f (μ.restrict A)
  · haveI : IsFiniteMeasure (μ.restrict A) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin)
    rw [MeasureTheory.integral_sub hf (MeasureTheory.integrable_const a), h,
      MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real_def]
    ring
  · rw [MeasureTheory.integral_undef hf] at h
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact h'
      · exact absurd h' hV
    subst ha
    simp only [sub_zero]
    exact MeasureTheory.integral_undef hf

/-! ## 2. The one-slot identities `PᵢQᵢ = 0` and `QᵢQᵢ = Qᵢ` -/

/-- **`Pᵢ` kills the range of `Qᵢ`**, pointwise: `Pᵢ(QᵢΨ)(x) = 0`.

On a configuration `x` the mean `PᵢΨ(x|i↦z)` is the *constant* `m = V⁻¹∫_{z∈A}Ψ(x|i↦z)`, so on
`A` the integrand of `Pᵢ(QᵢΨ)(x)` is `Ψ(x|i↦z) − m`, whose integral is `∫_{z∈A}Ψ − m·V = 0`. -/
theorem boxPInd_boxQInd_apply_zero {N : ℕ} {V : ℝ} (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (i : Fin N) (Ψ : X N → ℝ)
    (x : X N) : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A i Ψ) x = 0 := by
  set a : ℝ := (1 / V) * (∫ z in A, Ψ (Function.update x i z)) with ha
  -- `PᵢΨ` is constant (equal to `a`) on the box, in slot `i`
  have hPz : ∀ z : 𝔼3, Work.UBBInputs8.boxPInd V A i Ψ (Function.update x i z)
      = a * A.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    rw [Work.UBBInputs8.boxPInd, ha]
    have h1 : (∫ w in A, Ψ (Function.update (Function.update x i z) i w))
        = ∫ w in A, Ψ (Function.update x i w) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      rw [Function.update_idem]
    rw [h1, Function.update_self]
  -- hence on `A` the integrand of `Pᵢ(QᵢΨ)(x)` is `Ψ(x|i↦z) − a`
  have hkey : (∫ z in A, (Ψ (Function.update x i z) - a)) = 0 := by
    have hfin : (volume : Measure 𝔼3) A < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => ?_
      rw [htop, ENNReal.toReal_top] at hVeq
      rw [hVeq] at hV
      exact lt_irrefl 0 hV
    refine setIntegral_sub_const_eq_zero (volume : Measure 𝔼3) hfin ?_ ?_
    · rw [← hVeq]; exact hV.ne'
    · rw [ha]
      have hVne : V ≠ 0 := hV.ne'
      have h2 : (1 / V) * (∫ z in A, Ψ (Function.update x i z)) * V
          = ∫ z in A, Ψ (Function.update x i z) := by
        rw [one_div, mul_assoc, mul_comm (∫ z in A, Ψ (Function.update x i z)) V,
          ← mul_assoc, inv_mul_cancel₀ hVne, one_mul]
      rw [← hVeq]
      exact h2.symm
  have hcongr : (∫ z in A, Work.UBBInputs8.boxQInd V A i Ψ (Function.update x i z))
      = ∫ z in A, (Ψ (Function.update x i z) - a) := by
    refine MeasureTheory.setIntegral_congr_fun hA (fun z hz => ?_)
    show Work.UBBInputs8.boxQInd V A i Ψ (Function.update x i z)
        = Ψ (Function.update x i z) - a
    have h1 : Work.UBBInputs8.boxQInd V A i Ψ (Function.update x i z)
        = A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) i) * Ψ (Function.update x i z)
          - Work.UBBInputs8.boxPInd V A i Ψ (Function.update x i z) := rfl
    rw [h1, Function.update_self, hPz z, Set.indicator_of_mem hz, one_mul, mul_one]
  rw [Work.UBBInputs8.boxPInd, hcongr, hkey]
  simp

/-- **`Pᵢ` kills the range of `Qᵢ`**: `Pᵢ ∘ Qᵢ = 0`. -/
theorem boxPInd_boxQInd_self_zero {N : ℕ} {V : ℝ} (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (i : Fin N) (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A i Ψ) = 0 :=
  funext (boxPInd_boxQInd_apply_zero hV hA hVeq i Ψ)

/-- **`Qᵢ` is idempotent**: `Qᵢ ∘ Qᵢ = Qᵢ` (consequence of `PᵢQᵢ = 0` and `1_A(xᵢ)² = 1_A(xᵢ)`). -/
theorem boxQInd_self_idem {N : ℕ} {V : ℝ} (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (i : Fin N) (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxQInd V A i Ψ)
      = Work.UBBInputs8.boxQInd V A i Ψ := by
  funext x
  rw [show Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxQInd V A i Ψ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Work.UBBInputs8.boxQInd V A i Ψ x
        - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A i Ψ) x from rfl]
  rw [boxPInd_boxQInd_apply_zero hV hA hVeq i Ψ x, sub_zero,
    Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hx : x i ∈ A
  · rw [Set.indicator_of_mem hx]; ring
  · rw [Set.indicator_of_notMem hx]; ring

/-! ## 2. Closure properties of the flat pieces -/

/-- **The flat pieces of a measurable state are measurable.** -/
theorem flatPieceList_measurable {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A)
    (l : List (Fin N)) (S : Finset (Fin N)) {Ψ : X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (flatPieceList V A l S Ψ) := by
  induction l with
  | nil => rwa [flatPieceList_nil]
  | cons i l ih =>
    rw [flatPieceList_cons]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact Work.BoseFixB1S.measurable_boxPInd V A hA i ih
    · rw [if_neg hi]
      exact Work.SlotWord.measurable_boxQInd V A hA i ih

/-- A single `Qᵢ` at most doubles a bound on the analysis box. -/
theorem abs_boxQInd_le_abox {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ) (i : Fin N)
    {Ψ : X N → ℝ} {C : ℝ} (hC : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A i Ψ x| ≤ 2 * C := by
  intro x hx
  have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hmem : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hmem]
  have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * C :=
          mul_le_mul hσ (hC x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have h2 : |Work.UBBInputs8.boxPInd V A i Ψ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hC x hx
  have h3 : Work.UBBInputs8.boxQInd V A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - Work.UBBInputs8.boxPInd V A i Ψ x := rfl
  rw [h3]
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x - Work.UBBInputs8.boxPInd V A i Ψ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x|
          + |Work.UBBInputs8.boxPInd V A i Ψ x| := abs_sub _ _
    _ ≤ C + C := add_le_add h1 h2
    _ = 2 * C := by ring

/-- **The flat pieces of a state bounded on the analysis box are bounded on it.** -/
theorem flatPieceList_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    (l : List (Fin N)) (S : Finset (Fin N)) {Ψ : X N → ℝ} {C : ℝ}
    (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) :
    ∃ C', ∀ y ∈ abox N ℓ, |flatPieceList V A l S Ψ y| ≤ C' := by
  induction l with
  | nil => exact ⟨C, by rw [flatPieceList_nil]; exact hΨC⟩
  | cons i l ih =>
    obtain ⟨C', hC'⟩ := ih
    rw [flatPieceList_cons]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact ⟨C', Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hC'⟩
    · rw [if_neg hi]
      exact ⟨2 * C', abs_boxQInd_le_abox hℓ hV hA hVeq hAc i hC'⟩

/-- **Every flat piece is supported in the box fibre `A ^ N`**: if the slot `k ∈ l` of `y` lies
outside `A` then `flatPieceList V A l S Ψ y = 0`, for *every* state `Ψ`. -/
theorem flatPieceList_eq_zero_of_not_mem {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A)
    (l : List (Fin N)) (S : Finset (Fin N)) (Ψ : X N → ℝ) :
    ∀ y : X N, (∃ k ∈ l, y k ∉ A) → flatPieceList V A l S Ψ y = 0 := by
  induction l with
  | nil => intro y hy; obtain ⟨k, hk, _⟩ := hy; simp at hk
  | cons i l ih =>
    intro y hy
    obtain ⟨k, hk, hky⟩ := hy
    rw [flatPieceList_cons]
    by_cases hyi : y i ∈ A
    · -- the head slot lies in `A`, so the witness lies in the tail and differs from `i`
      have hk' : k ∈ l := by
        rcases List.mem_cons.mp hk with h | h
        · subst h; exact absurd hyi hky
        · exact h
      have hki : k ≠ i := by
        intro h; subst h; exact absurd hyi hky
      have hy0 : flatPieceList V A l S Ψ y = 0 := ih y ⟨k, hk', hky⟩
      have hvan : ∀ z ∈ A, flatPieceList V A l S Ψ (Function.update y i z) = 0 := by
        intro z hz
        refine ih _ ⟨k, hk', ?_⟩
        have h1 : Function.update y i z k = y k := by
          rw [Function.update_apply]
          exact if_neg hki
        rw [h1]
        exact hky
      by_cases hi : i ∈ S
      · rw [if_pos hi, Work.UBBInputs8.boxPInd,
          setIntegral_eq_zero_of_eq_zero_on _ hA hvan]
        ring
      · rw [if_neg hi, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd,
          setIntegral_eq_zero_of_eq_zero_on _ hA hvan, hy0]
        ring
    · -- the head slot lies outside `A`: the head operator already kills the term
      by_cases hi : i ∈ S
      · rw [if_pos hi, Work.UBBInputs8.boxPInd, Set.indicator_of_notMem hyi]
        ring
      · rw [if_neg hi, Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd,
          Set.indicator_of_notMem hyi]
        ring

/-! ## 3. The two-slot means and the orientation swaps for bounded states

The proofs are the ones of `Work.BoseFixB1S.BoxPotOper` with the continuity hypothesis replaced by
the (weaker) boundedness hypothesis on the analysis box, which is what the flat pieces satisfy. -/

/-- **The two-slot mean is symmetric** for measurable states bounded on the analysis box
(`i ≠ j`): Fubini over `A × A` plus the commutation of the two slot updates. -/
theorem twoMean_comm_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set 𝔼3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.BoseFixB1S.twoMean volA A i j Ψ x = Work.BoseFixB1S.twoMean volA A j i Ψ x := by
  have hfin : (volume : Measure 𝔼3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure 𝔼3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin)
  have hInt : MeasureTheory.Integrable
      (fun p : 𝔼3 × 𝔼3 => Ψ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure 𝔼3).restrict A).prod ((volume : Measure 𝔼3).restrict A)) := by
    refine MeasureTheory.Integrable.of_bound ((hΨm.comp (by fun_prop)).aestronglyMeasurable)
      (max C 0) ?_
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hA.prod hA)]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    have hmem : Function.update (Function.update x i p.1) j p.2 ∈ abox N ℓ :=
      Work.BoseFixB1S.update_mem_abox' hAc
        (Work.BoseFixB1S.update_mem_abox' hAc hx i hp.1) j hp.2
    rw [Real.norm_eq_abs]
    exact le_trans (hΨC _ hmem) (le_max_left C 0)
  have hswap : (∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
      = ∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x i z) j w) :=
    MeasureTheory.integral_integral_swap hInt
  unfold Work.BoseFixB1S.twoMean
  rw [hswap]
  congr 2
  apply MeasureTheory.integral_congr_ae; filter_upwards with w
  apply MeasureTheory.integral_congr_ae; filter_upwards with z
  rw [Function.update_comm hij]

/-- `Pᵢ` preserves the *boundedness on the analysis box* (the slot mean of a bounded integrand). -/
theorem slotInt_of_bound_bdd {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (i : Fin N) (x : X N) (hx : x ∈ abox N ℓ)
    {Ψ : X N → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hb : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) :
    IntegrableOn (fun z => Ψ (Function.update x i z)) A volume := by
  have hfin : (volume : Measure 𝔼3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  refine MeasureTheory.IntegrableOn.of_bound hfin
    (hΨ.comp (by fun_prop : Measurable (fun z : 𝔼3 => Function.update x i z))).aestronglyMeasurable
    C ?_
  rw [MeasureTheory.ae_restrict_iff' hA]
  exact Filter.Eventually.of_forall (fun z hz => by
    rw [Real.norm_eq_abs]
    exact hb _ (Work.BoseFixB1S.update_mem_abox' hAc hx i hz))

/-- The slot integral of a two-slot mean of a bounded state is integrable over `A`. -/
theorem slotInt2_of_bound_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set 𝔼3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i j : Fin N) (x : X N) (hx : x ∈ abox N ℓ)
    {Ψ : X N → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hb : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) :
    IntegrableOn (fun z => (1 / volA) * ∫ w in A,
      Ψ (Function.update (Function.update x i z) j w)) A volume := by
  have hfin : (volume : Measure 𝔼3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  have hm1 : Measurable (fun y : X N => ∫ w in A, Ψ (Function.update y j w)) :=
    Work.BoseFixB1S.measurable_fibreMean A hA j hΨ
  have hm2 : Measurable (fun z : 𝔼3 =>
      ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) :=
    hm1.comp (by fun_prop : Measurable (fun z : 𝔼3 => Function.update x i z))
  refine MeasureTheory.IntegrableOn.of_bound hfin
    ((hm2.const_mul (1 / volA)).aestronglyMeasurable) C ?_
  rw [MeasureTheory.ae_restrict_iff' hA]
  exact Filter.Eventually.of_forall (fun z hz => by
    have hInt : |∫ w in A, Ψ (Function.update (Function.update x i z) j w)| ≤ C * volA := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure 𝔼3)) hfin (s := A)
        (f := fun w : 𝔼3 => Ψ (Function.update (Function.update x i z) j w)) (C := C)
        (fun w hw => by
          rw [Real.norm_eq_abs]
          exact hb _ (Work.BoseFixB1S.update_mem_abox' hAc (Work.BoseFixB1S.update_mem_abox' hAc hx i hz) j hw))
      rw [Real.norm_eq_abs, MeasureTheory.Measure.real_def, ← hvolA] at h
      exact h
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
    calc (1 / volA) * |∫ w in A, Ψ (Function.update (Function.update x i z) j w)|
        ≤ (1 / volA) * (C * volA) := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = C := by field_simp)

/-- **The `P Q` pattern in mean form**, for measurable states bounded on the analysis box. -/
theorem boxPInd_boxQInd_twoMean_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set 𝔼3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
      = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)
        * (Work.BoseFixB1S.oneMean volA A i Ψ x
          - Work.BoseFixB1S.twoMean volA A i j Ψ x) := by
  have hinner : ∀ z : 𝔼3, Work.UBBInputs8.boxQInd volA A j Ψ (Function.update x i z)
      = Work.BoseFixB1S.Aind A (x j)
        * (Ψ (Function.update x i z)
          - (1 / volA) * ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) := by
    intro z
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    have h1 : (Function.update x i z) j = x j := by
      rw [Function.update_apply, if_neg]
      exact fun h => hij h.symm
    rw [h1]
    unfold Work.BoseFixB1S.Aind
    ring
  rw [Work.UBBInputs8.boxPInd]
  rw [show (∫ z in A, Work.UBBInputs8.boxQInd volA A j Ψ (Function.update x i z))
      = ∫ z in A, Work.BoseFixB1S.Aind A (x j) * (Ψ (Function.update x i z)
          - (1 / volA) * ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) from by
    apply MeasureTheory.integral_congr_ae; filter_upwards with z; exact hinner z]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub
    (f := fun z : 𝔼3 => Ψ (Function.update x i z))
    (g := fun z : 𝔼3 => (1 / volA) * ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
    (slotInt_of_bound_bdd hℓ hA hAc i x hx hΨm hΨC)
    (slotInt2_of_bound_bdd hℓ hvol hA hvolA hAc i j x hx hΨm hΨC)]
  rw [MeasureTheory.integral_const_mul]
  unfold Work.BoseFixB1S.oneMean Work.BoseFixB1S.twoMean Work.BoseFixB1S.Aind
  ring

/-- **The `Q Q` pattern in mean form**, for measurable states bounded on the analysis box. -/
theorem boxQInd_boxQInd_twoMean_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set 𝔼3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x
      = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)
        * (Ψ x - Work.BoseFixB1S.oneMean volA A i Ψ x - Work.BoseFixB1S.oneMean volA A j Ψ x
          + Work.BoseFixB1S.twoMean volA A i j Ψ x) := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd,
    boxPInd_boxQInd_twoMean_bdd hℓ hvol hA hvolA hAc hij hΨm hΨC x hx,
    Work.BoseFixB1S.boxPInd_eq volA A j Ψ x]
  unfold Work.BoseFixB1S.Aind
  ring

/-- **`PᵢPⱼ = PⱼPᵢ`** for `i ≠ j`, for measurable states bounded on the analysis box. -/
theorem boxPInd_comm_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) :
    ∀ x ∈ abox N ℓ,
      Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Ψ) x
        = Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Ψ) x := by
  intro x hx
  rw [Work.BoseFixB1S.boxPInd_twoMean V A hij Ψ x,
    Work.BoseFixB1S.boxPInd_twoMean V A hij.symm Ψ x,
    twoMean_comm_bdd hℓ hA hAc hij hΨm hΨC x hx]
  ring

/-- **`PᵢQⱼ = QⱼPᵢ`** for `i ≠ j`, for measurable states bounded on the analysis box. -/
theorem boxPInd_boxQInd_comm_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) :
    ∀ x ∈ abox N ℓ,
      Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxQInd V A j Ψ) x
        = Work.UBBInputs8.boxQInd V A j (Work.UBBInputs8.boxPInd V A i Ψ) x := by
  intro x hx
  rw [boxPInd_boxQInd_twoMean_bdd hℓ hV hA hVeq hAc hij hΨm hΨC x hx,
    Work.BoseFixB1S.boxQInd_boxPInd_twoMean V A hij.symm Ψ x,
    twoMean_comm_bdd hℓ hA hAc hij hΨm hΨC x hx]
  ring

/-- **`QᵢPⱼ = PⱼQᵢ`** for `i ≠ j`, for measurable states bounded on the analysis box. -/
theorem boxQInd_boxPInd_comm_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) :
    ∀ x ∈ abox N ℓ,
      Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxPInd V A j Ψ) x
        = Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Ψ) x := by
  intro x hx
  rw [Work.BoseFixB1S.boxQInd_boxPInd_twoMean V A hij Ψ x,
    boxPInd_boxQInd_twoMean_bdd hℓ hV hA hVeq hAc hij.symm hΨm hΨC x hx,
    twoMean_comm_bdd hℓ hA hAc hij hΨm hΨC x hx]
  ring

/-- **`QᵢQⱼ = QⱼQᵢ`** for `i ≠ j`, for measurable states bounded on the analysis box. -/
theorem boxQInd_boxQInd_comm_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨm : Measurable Ψ)
    {C : ℝ} (hΨC : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) :
    ∀ x ∈ abox N ℓ,
      Work.UBBInputs8.boxQInd V A i (Work.UBBInputs8.boxQInd V A j Ψ) x
        = Work.UBBInputs8.boxQInd V A j (Work.UBBInputs8.boxQInd V A i Ψ) x := by
  intro x hx
  rw [boxQInd_boxQInd_twoMean_bdd hℓ hV hA hVeq hAc hij hΨm hΨC x hx,
    boxQInd_boxQInd_twoMean_bdd hℓ hV hA hVeq hAc hij.symm hΨm hΨC x hx,
    twoMean_comm_bdd hℓ hA hAc hij hΨm hΨC x hx]
  ring

/-! ## 4. Two elementary helpers: `ite` under a slot operator, and congruence on the box -/

/-- `Pⱼ` of a state switched off by an `if`. -/
theorem boxPInd_ite_zero {N : ℕ} (V : ℝ) {A : Set 𝔼3} (j : Fin N) (c : Prop) [Decidable c]
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd V A j (fun y => if c then Φ y else 0) x
      = if c then Work.UBBInputs8.boxPInd V A j Φ x else 0 := by
  simp only [Work.UBBInputs8.boxPInd]
  by_cases hc : c
  · simp only [if_pos hc]
  · simp only [if_neg hc]
    simp

/-- `Pⱼ` of a state switched *on* by an `if`. -/
theorem boxPInd_zero_ite {N : ℕ} (V : ℝ) {A : Set 𝔼3} (j : Fin N) (c : Prop) [Decidable c]
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd V A j (fun y => if c then 0 else Φ y) x
      = if c then 0 else Work.UBBInputs8.boxPInd V A j Φ x := by
  simp only [Work.UBBInputs8.boxPInd]
  by_cases hc : c
  · simp only [if_pos hc]
    simp
  · simp only [if_neg hc]

/-- `Qⱼ` of a state switched off by an `if`. -/
theorem boxQInd_ite_zero {N : ℕ} (V : ℝ) {A : Set 𝔼3} (j : Fin N) (c : Prop) [Decidable c]
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxQInd V A j (fun y => if c then Φ y else 0) x
      = if c then Work.UBBInputs8.boxQInd V A j Φ x else 0 := by
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hc : c
  · simp only [if_pos hc]
  · simp only [if_neg hc]
    simp

/-- `Qⱼ` of a state switched *on* by an `if`. -/
theorem boxQInd_zero_ite {N : ℕ} (V : ℝ) {A : Set 𝔼3} (j : Fin N) (c : Prop) [Decidable c]
    (Φ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxQInd V A j (fun y => if c then 0 else Φ y) x
      = if c then 0 else Work.UBBInputs8.boxQInd V A j Φ x := by
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hc : c
  · simp only [if_pos hc]
    simp
  · simp only [if_neg hc]

/-- **Slot operators depend on their argument only through the analysis box**: states which agree
on `abox N ℓ` have equal `Pⱼ`- and `Qⱼ`-values at every point of `abox N ℓ`. -/
theorem boxInd_congr_on {N : ℕ} (V : ℝ) {ℓ : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (j : Fin N) {x : X N} (hx : x ∈ abox N ℓ) {Φ Ψ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Φ y = Ψ y) :
    Work.UBBInputs8.boxPInd V A j Φ x = Work.UBBInputs8.boxPInd V A j Ψ x
    ∧ Work.UBBInputs8.boxQInd V A j Φ x = Work.UBBInputs8.boxQInd V A j Ψ x := by
  have hP : Work.UBBInputs8.boxPInd V A j Φ x = Work.UBBInputs8.boxPInd V A j Ψ x := by
    simp only [Work.UBBInputs8.boxPInd]
    rw [MeasureTheory.setIntegral_congr_fun hA (fun z hz =>
      h _ (Work.BoseFixB1S.update_mem_abox' hAc hx j hz))]
  refine ⟨hP, ?_⟩
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd, hP, h x hx]

/-! ## 5. The eigenvalue statement for the flat pieces -/

/-- **The flat piece `Π_S` is the joint eigenspace of the slot operators**: for `i ∈ l`, `Pᵢ` acts
on `Π_S = flatPieceList V A l S Ψ` as multiplication by `[i ∈ S]` and `Qᵢ` as multiplication by
`[i ∉ S]` (on the analysis box, where all the slot integrals live). -/
theorem flatPieceList_eigen {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    (l : List (Fin N)) (S : Finset (Fin N)) :
    ∀ (Ψ : X N → ℝ), Measurable Ψ → (∃ C, ∀ y ∈ abox N ℓ, |Ψ y| ≤ C) →
      (∀ i ∈ l, ∀ x ∈ abox N ℓ,
          Work.UBBInputs8.boxPInd V A i (flatPieceList V A l S Ψ) x
            = if i ∈ S then flatPieceList V A l S Ψ x else 0)
      ∧ (∀ i ∈ l, ∀ x ∈ abox N ℓ,
          Work.UBBInputs8.boxQInd V A i (flatPieceList V A l S Ψ) x
            = if i ∈ S then 0 else flatPieceList V A l S Ψ x) := by
  induction l with
  | nil =>
    intro Ψ hΨm hb
    exact ⟨fun i hi => absurd hi List.not_mem_nil,
      fun i hi => absurd hi List.not_mem_nil⟩
  | cons j l ih =>
    intro Ψ hΨm hb
    obtain ⟨ihP, ihQ⟩ := ih Ψ hΨm hb
    obtain ⟨C, hC⟩ := hb
    obtain ⟨C', hC'⟩ := flatPieceList_bdd hℓ hV hA hVeq hAc l S hC
    have hm' : Measurable (flatPieceList V A l S Ψ) := flatPieceList_measurable hA l S hΨm
    refine ⟨?_, ?_⟩
    · intro i hi x hx
      rw [flatPieceList_cons]
      by_cases hij : i = j
      · -- the diagonal case `i = j`: `PⱼPⱼ = Pⱼ` and `PⱼQⱼ = 0`
        rw [hij]
        by_cases hjS : j ∈ S
        · simp only [if_pos hjS]
          exact congr_fun (boxPInd_self_idem hV hA hVeq j (flatPieceList V A l S Ψ)) x
        · simp only [if_neg hjS]
          exact boxPInd_boxQInd_apply_zero hV hA hVeq j (flatPieceList V A l S Ψ) x
      · -- the off-diagonal case: commute `Pᵢ` with the head operator, then use the induction
        -- hypothesis on the tail
        have hi' : i ∈ l := (List.mem_cons.mp hi).resolve_left hij
        have hP : ∀ y ∈ abox N ℓ,
            Work.UBBInputs8.boxPInd V A i (flatPieceList V A l S Ψ) y
              = (fun y => if i ∈ S then flatPieceList V A l S Ψ y else 0) y :=
          fun y hy => ihP i hi' y hy
        by_cases hjS : j ∈ S
        · simp only [if_pos hjS]
          rw [boxPInd_comm_bdd hℓ hV hA hVeq hAc hij hm' hC' x hx,
            show Work.UBBInputs8.boxPInd V A j
                  (Work.UBBInputs8.boxPInd V A i (flatPieceList V A l S Ψ)) x
                = Work.UBBInputs8.boxPInd V A j
                  (fun y => if i ∈ S then flatPieceList V A l S Ψ y else 0) x from
              (boxInd_congr_on V hA hAc j hx hP).1,
            boxPInd_ite_zero V j (i ∈ S) (flatPieceList V A l S Ψ) x]
        · simp only [if_neg hjS]
          rw [boxPInd_boxQInd_comm_bdd hℓ hV hA hVeq hAc hij hm' hC' x hx,
            show Work.UBBInputs8.boxQInd V A j
                  (Work.UBBInputs8.boxPInd V A i (flatPieceList V A l S Ψ)) x
                = Work.UBBInputs8.boxQInd V A j
                  (fun y => if i ∈ S then flatPieceList V A l S Ψ y else 0) x from
              (boxInd_congr_on V hA hAc j hx hP).2,
            boxQInd_ite_zero V j (i ∈ S) (flatPieceList V A l S Ψ) x]
    · intro i hi x hx
      rw [flatPieceList_cons]
      by_cases hij : i = j
      · rw [hij]
        by_cases hjS : j ∈ S
        · simp only [if_pos hjS]
          exact Work.BoseFixB1.boxQInd_self_boxPInd hV hA hVeq j (flatPieceList V A l S Ψ) x
        · simp only [if_neg hjS]
          exact congr_fun (boxQInd_self_idem hV hA hVeq j (flatPieceList V A l S Ψ)) x
      · have hi' : i ∈ l := (List.mem_cons.mp hi).resolve_left hij
        have hQ : ∀ y ∈ abox N ℓ,
            Work.UBBInputs8.boxQInd V A i (flatPieceList V A l S Ψ) y
              = (fun y => if i ∈ S then 0 else flatPieceList V A l S Ψ y) y :=
          fun y hy => ihQ i hi' y hy
        by_cases hjS : j ∈ S
        · simp only [if_pos hjS]
          rw [boxQInd_boxPInd_comm_bdd hℓ hV hA hVeq hAc hij hm' hC' x hx,
            show Work.UBBInputs8.boxPInd V A j
                  (Work.UBBInputs8.boxQInd V A i (flatPieceList V A l S Ψ)) x
                = Work.UBBInputs8.boxPInd V A j
                  (fun y => if i ∈ S then 0 else flatPieceList V A l S Ψ y) x from
              (boxInd_congr_on V hA hAc j hx hQ).1,
            boxPInd_zero_ite V j (i ∈ S) (flatPieceList V A l S Ψ) x]
        · simp only [if_neg hjS]
          rw [boxQInd_boxQInd_comm_bdd hℓ hV hA hVeq hAc hij hm' hC' x hx,
            show Work.UBBInputs8.boxQInd V A j
                  (Work.UBBInputs8.boxQInd V A i (flatPieceList V A l S Ψ)) x
                = Work.UBBInputs8.boxQInd V A j
                  (fun y => if i ∈ S then 0 else flatPieceList V A l S Ψ y) x from
              (boxInd_congr_on V hA hAc j hx hQ).2,
            boxQInd_zero_ite V j (i ∈ S) (flatPieceList V A l S Ψ) x]

theorem flatPiece_eigen {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (S : Finset (Fin N)) (i : Fin N) :
    (Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.flatPiece V A S Φ)
        = if i ∈ S then Work.BoseFixB1.flatPiece V A S Φ else 0)
    ∧ (Work.UBBInputs8.boxQInd V A i (Work.BoseFixB1.flatPiece V A S Φ)
        = if i ∈ S then 0 else Work.BoseFixB1.flatPiece V A S Φ) := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have heigen := flatPieceList_eigen hℓ hV hA hVeq hAc (List.finRange N) S Φ hΦc.measurable
    ⟨C, hC⟩
  constructor
  · funext x
    by_cases hxsl : ∀ k, x k ∈ A
    · -- the configuration lies in the box fibre: the eigenvalue statement applies
      have hxbox : x ∈ abox N ℓ := fun k => hAc (hxsl k)
      have hRHS : (if i ∈ S then Work.BoseFixB1.flatPiece V A S Φ else 0) x
          = if i ∈ S then Work.BoseFixB1.flatPiece V A S Φ x else 0 := by
        rw [ite_apply]
        by_cases hiS : i ∈ S <;> simp [hiS]
      rw [hRHS]
      exact heigen.1 i (List.mem_finRange i) x hxbox
    · -- some slot of `x` lies outside `A`: all the pieces vanish there
      push_neg at hxsl
      obtain ⟨k, hk⟩ := hxsl
      have hy0 : Work.BoseFixB1.flatPiece V A S Φ x = 0 :=
        flatPieceList_eq_zero_of_not_mem hA (List.finRange N) S Φ x
          ⟨k, List.mem_finRange k, hk⟩
      have hRHS : (if i ∈ S then Work.BoseFixB1.flatPiece V A S Φ else 0) x = 0 := by
        rw [ite_apply]
        by_cases hiS : i ∈ S <;> simp [hiS, hy0]
      by_cases hxi : x i ∈ A
      · have hvan : ∀ z ∈ A,
            Work.BoseFixB1.flatPiece V A S Φ (Function.update x i z) = 0 := by
          intro z hz
          refine flatPieceList_eq_zero_of_not_mem hA (List.finRange N) S Φ _
            ⟨k, List.mem_finRange k, ?_⟩
          have hki : k ≠ i := by rintro rfl; exact hk hxi
          rw [Function.update_apply, if_neg hki]
          exact hk
        have hval : Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.flatPiece V A S Φ) x
            = (1 / V) * (∫ z in A,
                Work.BoseFixB1.flatPiece V A S Φ (Function.update x i z))
              * Work.BoseFixB1S.Aind A (x i) := rfl
        rw [hval, setIntegral_eq_zero_of_eq_zero_on _ hA hvan, hRHS]
        ring
      · have hval : Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.flatPiece V A S Φ) x
            = (1 / V) * (∫ z in A,
                Work.BoseFixB1.flatPiece V A S Φ (Function.update x i z))
              * Work.BoseFixB1S.Aind A (x i) := rfl
        rw [hval, Work.BoseFixB1S.Aind, Set.indicator_of_notMem hxi, hRHS]
        ring
  · funext x
    by_cases hxsl : ∀ k, x k ∈ A
    · have hxbox : x ∈ abox N ℓ := fun k => hAc (hxsl k)
      have hRHS : (if i ∈ S then (0 : Submission.BoseGases.X N → ℝ)
            else Work.BoseFixB1.flatPiece V A S Φ) x
          = if i ∈ S then 0 else Work.BoseFixB1.flatPiece V A S Φ x := by
        rw [ite_apply]
        by_cases hiS : i ∈ S <;> simp [hiS]
      rw [hRHS]
      exact heigen.2 i (List.mem_finRange i) x hxbox
    · push_neg at hxsl
      obtain ⟨k, hk⟩ := hxsl
      have hy0 : Work.BoseFixB1.flatPiece V A S Φ x = 0 :=
        flatPieceList_eq_zero_of_not_mem hA (List.finRange N) S Φ x
          ⟨k, List.mem_finRange k, hk⟩
      have hRHS : (if i ∈ S then (0 : Submission.BoseGases.X N → ℝ)
            else Work.BoseFixB1.flatPiece V A S Φ) x = 0 := by
        rw [ite_apply]
        by_cases hiS : i ∈ S <;> simp [hiS, hy0]
      by_cases hxi : x i ∈ A
      · have hvan : ∀ z ∈ A,
            Work.BoseFixB1.flatPiece V A S Φ (Function.update x i z) = 0 := by
          intro z hz
          refine flatPieceList_eq_zero_of_not_mem hA (List.finRange N) S Φ _
            ⟨k, List.mem_finRange k, ?_⟩
          have hki : k ≠ i := by rintro rfl; exact hk hxi
          rw [Function.update_apply, if_neg hki]
          exact hk
        have hval : Work.UBBInputs8.boxQInd V A i (Work.BoseFixB1.flatPiece V A S Φ) x
            = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1.flatPiece V A S Φ x
              - (1 / V) * (∫ z in A,
                  Work.BoseFixB1.flatPiece V A S Φ (Function.update x i z))
                * Work.BoseFixB1S.Aind A (x i) := rfl
        rw [hval, setIntegral_eq_zero_of_eq_zero_on _ hA hvan, hy0, hRHS]
        ring
      · have hval : Work.UBBInputs8.boxQInd V A i (Work.BoseFixB1.flatPiece V A S Φ) x
            = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1.flatPiece V A S Φ x
              - (1 / V) * (∫ z in A,
                  Work.BoseFixB1.flatPiece V A S Φ (Function.update x i z))
                * Work.BoseFixB1S.Aind A (x i) := rfl
        rw [hval, Work.BoseFixB1S.Aind, Set.indicator_of_notMem hxi, hRHS]
        ring

end Work.BoseFixB1
