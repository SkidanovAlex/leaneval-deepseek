import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.BoseFixB1S.n0SpectralDefs
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The slot mean -/

/-- **The slot mean** `M_iΨ(x) = volA⁻¹ ∫_{z ∈ A} Ψ(x|i↦z) dz`. -/
def n0Mean {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (Ψ : X N → ℝ) : X N → ℝ :=
  fun x => (1 / volA) * ∫ z in A, Ψ (Function.update x i z)

/-- The FS projection `P_{B,i}` is the slot mean times the box indicator. -/
theorem boxPInd_eq_mean_mul {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (Ψ : X N → ℝ) :
    UBBInputs8.boxPInd volA A i Ψ
      = fun x => n0Mean volA A i Ψ x * A.indicator (fun _ => (1 : ℝ)) (x i) := rfl

/-- The slot mean does not depend on its own slot. -/
theorem n0Mean_indep {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (Ψ : X N → ℝ)
    (x : X N) (t : E3) :
    n0Mean volA A i Ψ (Function.update x i t) = n0Mean volA A i Ψ x := by
  simp only [n0Mean]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [Function.update_idem]

/-- `∫_{z∈A} 1_A(z) = volA`. -/
theorem setIntegral_indicator_one_eq {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (volume : Measure E3).real A) :
    (∫ z in A, A.indicator (fun _ => (1 : ℝ)) z) = volA := by
  rw [setIntegral_congr_fun (f := fun z => A.indicator (fun _ => (1 : ℝ)) z) (g := fun _ => 1) hA
      (fun z hz => by simp [Set.indicator_of_mem hz])]
  rw [setIntegral_const, smul_eq_mul, mul_one, hvolA]

/-! ## 2. The class `BoxNice`: measurable and bounded on the box -/

/-- `ψ` is measurable and bounded on the box `abox N ℓ`. -/
def BoxNice {N : ℕ} (ℓ : ℝ) (ψ : X N → ℝ) : Prop :=
  Measurable ψ ∧ ∃ C : ℝ, ∀ x ∈ abox N ℓ, |ψ x| ≤ C

/-- A continuous function is `BoxNice`. -/
theorem BoxNice.of_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) : BoxNice ℓ Ψ := by
  refine ⟨hΨ.measurable, ?_⟩
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ)
    (f := Ψ) hΨ.continuousOn
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

/-- `BoxNice` is closed under subtraction. -/
theorem BoxNice.sub {N : ℕ} {ℓ : ℝ} {ψ φ : X N → ℝ} (hψ : BoxNice ℓ ψ)
    (hφ : BoxNice ℓ φ) : BoxNice ℓ (ψ - φ) := by
  obtain ⟨hm1, C, hC⟩ := hψ
  obtain ⟨hm2, D, hD⟩ := hφ
  refine ⟨hm1.sub hm2, |C| + |D|, fun x hx => ?_⟩
  have h1 : |ψ x| ≤ |C| := le_trans (hC x hx) (le_abs_self C)
  have h2 : |φ x| ≤ |D| := le_trans (hD x hx) (le_abs_self D)
  calc |(ψ - φ) x| = |ψ x - φ x| := rfl
    _ ≤ |ψ x| + |φ x| := abs_sub _ _
    _ ≤ |C| + |D| := add_le_add h1 h2

/-- `BoxNice` is closed under the slot projection `boxPInd`. -/
theorem BoxNice.boxPInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set E3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A) (hAc : A ⊆ acube ℓ)
    (i : Fin N) {ψ : X N → ℝ} (hψ : BoxNice ℓ ψ) :
    BoxNice ℓ (UBBInputs8.boxPInd volA A i ψ) := by
  obtain ⟨hm, C, hC⟩ := hψ
  refine ⟨measurable_boxPInd volA A hA i hm, ?_⟩
  have hfin : (volume : Measure E3) A < ∞ := Q0C.volume_A_lt_top hℓ hAc
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hbnd : ∀ y ∈ abox N ℓ, |ψ y| ≤ max C 0 := fun y hy => le_trans (hC y hy) (le_max_left _ _)
  refine ⟨max C 0, fun x hx => ?_⟩
  have hInt : ‖∫ z in A, ψ (Function.update x i z)‖ ≤ max C 0 * volA := by
    have h := norm_setIntegral_le_of_norm_le_const hfin
      (f := fun z : E3 => ψ (Function.update x i z)) (C := max C 0) (fun z hz => by
        rw [Real.norm_eq_abs]
        exact hbnd _ (Q0C.update_mem_abox hAc hx i hz))
    rwa [← hvolA] at h
  simp only [UBBInputs8.boxPInd]
  by_cases hxi : x i ∈ A
  · rw [Set.indicator_of_mem hxi, mul_one, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
    calc (1 / volA) * |∫ z in A, ψ (Function.update x i z)|
        ≤ (1 / volA) * (max C 0 * volA) :=
          mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hInt) (by positivity)
      _ = max C 0 := by field_simp
  · rw [Set.indicator_of_notMem hxi, mul_zero, abs_zero]
    exact hC0

/-! ## 3. Integrability of the slot pullbacks -/

/-- The single slot pullback of a `BoxNice` function is integrable on `A`. -/
theorem integrableOn_update_pullback {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (i : Fin N) {ψ : X N → ℝ} (hψ : BoxNice ℓ ψ)
    {x : X N} (hx : x ∈ abox N ℓ) :
    IntegrableOn (fun z : E3 => ψ (Function.update x i z)) A volume := by
  obtain ⟨hm, C, hC⟩ := hψ
  have hfin : (volume : Measure E3) A < ∞ := Q0C.volume_A_lt_top hℓ hAc
  refine IntegrableOn.of_bound hfin ?_ (max C 0) ?_
  · exact (hm.comp (by fun_prop : Measurable fun z : E3 => Function.update x i z)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict hA] with z hz
    rw [Real.norm_eq_abs]
    exact le_trans (hC _ (Q0C.update_mem_abox hAc hx i hz)) (le_max_left _ _)

/-- The double slot pullback of a `BoxNice` function is integrable on `A × A`. -/
theorem integrable_prod_update_pullback {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (i j : Fin N) {ψ : X N → ℝ} (hψ : BoxNice ℓ ψ)
    {x : X N} (hx : x ∈ abox N ℓ) :
    Integrable (fun q : E3 × E3 => ψ (Function.update (Function.update x i q.1) j q.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
  obtain ⟨hm, C, hC⟩ := hψ
  have hfin : (volume : Measure E3) A < ∞ := Q0C.volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine Integrable.mono' (integrable_const (max C 0)) ?_ ?_
  · exact (hm.comp (by fun_prop : Measurable fun q : E3 × E3 =>
      Function.update (Function.update x i q.1) j q.2)).aestronglyMeasurable
  · filter_upwards [Q0C.ae_mem_prod_restrict hA] with q hq
    rw [Real.norm_eq_abs]
    exact le_trans (hC _ (Q0C.update_mem_abox hAc (Q0C.update_mem_abox hAc hx i hq.1) j hq.2))
      (le_max_left _ _)

/-! ## 4. The slot iteration -/

/-- `BoxNice` is closed under the slot iteration. -/
theorem BoxNice.iter {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set E3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A) (hAc : A ⊆ acube ℓ)
    (b : Fin N → Bool) {ψ : X N → ℝ} (hψ : BoxNice ℓ ψ) (l : List (Fin N)) :
    BoxNice ℓ (n0Iter volA A b l ψ) := by
  induction l generalizing ψ with
  | nil => rw [n0Iter]; exact hψ
  | cons i l ih =>
    rw [n0Iter]
    by_cases hb : b i = true
    · rw [if_pos hb]
      exact ih (hψ.boxPInd hℓ hvol hA hvolA hAc i)
    · rw [if_neg hb]
      exact ih (hψ.sub (hψ.boxPInd hℓ hvol hA hvolA hAc i))

/-- The slot iteration of the zero function vanishes. -/
theorem n0Iter_zero {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) :
    ∀ l : List (Fin N), n0Iter volA A b l (0 : X N → ℝ) = 0 := by
  intro l
  induction l with
  | nil => rw [n0Iter]
  | cons i l ih =>
    rw [n0Iter]
    by_cases hb : b i = true
    · rw [if_pos hb]
      have h1 : (fun x => UBBInputs8.boxPInd volA A i (0 : X N → ℝ) x) = 0 := by
        funext x
        simp [UBBInputs8.boxPInd]
      rw [h1, ih]
    · rw [if_neg hb]
      have h1 : (fun x => (0 : X N → ℝ) x - UBBInputs8.boxPInd volA A i (0 : X N → ℝ) x) = 0 := by
        funext x
        simp [UBBInputs8.boxPInd]
      rw [h1, ih]

/-- The slot iteration only depends on the values of the pattern on the slot list. -/
theorem n0Iter_congr {N : ℕ} (volA : ℝ) (A : Set E3) {b b' : Fin N → Bool} :
    ∀ (l : List (Fin N)) (ψ : X N → ℝ), (∀ j ∈ l, b j = b' j) →
      n0Iter volA A b l ψ = n0Iter volA A b' l ψ := by
  intro l
  induction l with
  | nil => intro ψ _; rw [n0Iter, n0Iter]
  | cons i l ih =>
    intro ψ h
    rw [n0Iter, n0Iter]
    have hi : b i = b' i := h i (List.mem_cons_self : i ∈ i :: l)
    by_cases hb : b i = true
    · rw [if_pos hb, if_pos (by rw [← hi]; exact hb)]
      exact ih _ (fun j hj => h j (List.mem_cons_of_mem i hj))
    · rw [if_neg hb, if_neg (by rw [← hi]; exact hb)]
      exact ih _ (fun j hj => h j (List.mem_cons_of_mem i hj))

/-- The slot iteration only sees the values of its argument on the box. -/
theorem n0Iter_eq_of_eqOn_box {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) {f g : X N → ℝ}
    (hfg : ∀ y ∈ abox N ℓ, f y = g y) :
    ∀ (l : List (Fin N)) (x : X N), x ∈ abox N ℓ →
      n0Iter volA A b l f x = n0Iter volA A b l g x := by
  intro l
  induction l generalizing f g with
  | nil => intro x hx; exact hfg x hx
  | cons i l ih =>
    intro x hx
    have hPf : ∀ y ∈ abox N ℓ,
        UBBInputs8.boxPInd volA A i f y = UBBInputs8.boxPInd volA A i g y := by
      intro y hy
      have hInt : (∫ z in A, f (Function.update y i z))
          = (∫ z in A, g (Function.update y i z)) := by
        apply setIntegral_congr_fun hA
        intro z hz
        exact hfg _ (Q0C.update_mem_abox hAc hy i hz)
      simp only [UBBInputs8.boxPInd, hInt]
    have hQf : ∀ y ∈ abox N ℓ,
        (f y - UBBInputs8.boxPInd volA A i f y) = (g y - UBBInputs8.boxPInd volA A i g y) := by
      intro y hy
      rw [hfg y hy, hPf y hy]
    rw [n0Iter, n0Iter]
    by_cases hb : b i = true
    · rw [if_pos hb, if_pos hb]
      exact ih hPf x hx
    · rw [if_neg hb, if_neg hb]
      exact ih hQf x hx

end Work.BoseFixB1S
