import Mathlib
import Submission.Commons.Probability.Levy.essen_level_set_bound

open MeasureTheory
open scoped ENNReal BigOperators

namespace Commons.Probability.Levy

noncomputable section

lemma sub_eq_div_sub (c l ρ : ℝ) (hc : c ≠ 0) : (l - c * ρ) / c = l / c - ρ := by
  field_simp [hc]

lemma add_eq_div_add (c l ρ : ℝ) (hc : c ≠ 0) : (l + c * ρ) / c = l / c + ρ := by
  field_simp [hc]

lemma mul_preimage_Icc (c l ρ : ℝ) (hc : 0 < c) :
    (fun x : ℝ => c * x) ⁻¹' Set.Icc (l - c * ρ) (l + c * ρ) = Set.Icc (l / c - ρ) (l / c + ρ) := by
  ext x
  constructor
  · intro hx
    have hcne : c ≠ 0 := ne_of_gt hc
    rw [Set.mem_preimage, Set.mem_Icc] at hx
    rw [Set.mem_Icc]
    constructor
    · rw [← sub_eq_div_sub c l ρ hcne]
      exact (div_le_iff₀ hc).2 (by simpa only [mul_comm] using hx.1)
    · rw [← add_eq_div_add c l ρ hcne]
      exact (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hx.2)
  · intro hx
    have hcne : c ≠ 0 := ne_of_gt hc
    rw [Set.mem_Icc] at hx
    rw [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rw [mul_comm c x]
      exact (div_le_iff₀ hc).1 (by
        rw [sub_eq_div_sub c l ρ hcne]
        exact hx.1)
    · rw [mul_comm c x]
      exact (le_div_iff₀ hc).1 (by
        rw [add_eq_div_add c l ρ hcne]
        exact hx.2)

lemma map_mul_window_eq (μ : Measure ℝ) (c l ρ : ℝ) (hc : 0 < c) :
    (μ.map (fun x : ℝ => c * x)) (Set.Icc (l - c * ρ) (l + c * ρ))
      = μ (Set.Icc (l / c - ρ) (l / c + ρ)) := by
  have hmeas : Measurable (fun x : ℝ => c * x) := by fun_prop
  rw [Measure.map_apply hmeas measurableSet_Icc]
  rw [mul_preimage_Icc c l ρ hc]

lemma levyQ_map_const_mul (μ : Measure ℝ) (c ρ : ℝ) (hc : 0 < c) :
    levyQ (μ.map (fun x : ℝ => c * x)) (c * ρ) = levyQ μ ρ := by
  unfold levyQ
  apply le_antisymm
  · rw [sSup_le_iff]
    rintro a ⟨l, rfl⟩
    rw [map_mul_window_eq μ c l ρ hc]
    exact le_sSup ⟨l / c, rfl⟩
  · rw [sSup_le_iff]
    rintro a ⟨l, rfl⟩
    have hm' : (μ.map (fun x : ℝ => c * x)) (Set.Icc (c * l - c * ρ) (c * l + c * ρ))
        = μ (Set.Icc (l - ρ) (l + ρ)) := by
      rw [map_mul_window_eq μ c (c * l) ρ hc]
      congr 2 <;> field_simp [ne_of_gt hc]
    rw [← hm']
    exact le_sSup ⟨c * l, rfl⟩

lemma charFun_map_mul' (μ : Measure ℝ) (c t : ℝ) :
    charFun (μ.map (fun x : ℝ => c * x)) t = charFun μ (c * t) := by
  simpa using (charFun_map_mul (μ := μ) c t)

lemma interval_integral_inv_mul (r : ℝ) (hr : r ≠ 0) (G : ℝ → ℝ) :
    (∫ t in (-(1 / r))..(1 / r), G t)
      = (1 / r) * (∫ s in (-(1 : ℝ))..(1 : ℝ), G (s / r)) := by
  have h1 : (∫ s in (-(1 : ℝ))..(1 : ℝ), G (s / r)) = r * (∫ t in (-(1 / r))..(1 / r), G t) := by
    rw [intervalIntegral.integral_comp_div (f := G) (c := r) (a := (-(1:ℝ))) (b := (1:ℝ)) hr]
    rw [smul_eq_mul]
    have hb1 : (-(1:ℝ)) / r = -(1 / r) := by field_simp [hr]
    rw [hb1]
  calc
    (∫ t in (-(1 / r))..(1 / r), G t)
        = (1 / r) * (r * (∫ t in (-(1 / r))..(1 / r), G t)) := by
            field_simp [hr]
    _ = (1 / r) * (∫ s in (-(1 : ℝ))..(1 : ℝ), G (s / r)) := by rw [h1]

lemma product_integral_bound_of_r1_core (C : ℝ) (hCpos : 0 < C)
    (hcore : ∀ (m : ℕ) (μ : Fin m → Measure ℝ) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
      (ρ : Fin m → ℝ), (∀ i : Fin m, 0 < ρ i) → (∀ i : Fin m, ρ i ≤ 1) →
      (0 < ∑ i : Fin m,
        (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
          * (ρ i) ^ 2) →
      (∫ t in (-(1 : ℝ))..(1 : ℝ), ∏ i : Fin m, ‖charFun (μ i) t‖) ≤
        C / Real.sqrt (∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
            * (ρ i) ^ 2)) :
    ∀ (m : ℕ) (μ : Fin m → Measure ℝ) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
      (r : ℝ), 0 < r → (ρ : Fin m → ℝ) → (∀ i : Fin m, 0 < ρ i) →
      (∀ i : Fin m, ρ i ≤ r) →
      (0 < ∑ i : Fin m,
        (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
          * (ρ i) ^ 2) →
      (∫ t in (-(1 / r))..(1 / r), ∏ i : Fin m, ‖charFun (μ i) t‖) ≤
        C / Real.sqrt (∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
            * (ρ i) ^ 2) := by
  intro m μ _ r hr ρ hρpos hρle hD
  let c : ℝ := 1 / r
  let ν : Fin m → Measure ℝ := fun i => (μ i).map (fun x : ℝ => c * x)
  let ρ' : Fin m → ℝ := fun i => c * ρ i
  let S : ℝ := ∑ i : Fin m, (1 - (levyQ (μ i) (ρ i)).toReal) * (ρ i) ^ 2
  let S' : ℝ := ∑ i : Fin m, (1 - (levyQ (ν i) (ρ' i)).toReal) * (ρ' i) ^ 2
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hrne : r ≠ 0 := ne_of_gt hr
  have hρ'eq : ∀ i : Fin m, ρ' i = ρ i / r := by
    intro i
    dsimp [ρ', c]
    ring
  have hρ'pos : ∀ i : Fin m, 0 < ρ' i := by
    intro i
    rw [hρ'eq i]
    exact div_pos (hρpos i) hr
  have hρ'le : ∀ i : Fin m, ρ' i ≤ 1 := by
    intro i
    rw [hρ'eq i]
    exact (div_le_iff₀ hr).2 (by simpa using hρle i)
  have hνprob : ∀ i : Fin m, MeasureTheory.IsProbabilityMeasure (ν i) := by
    intro i
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable (fun x : ℝ => c * x) (μ i))
  have hS : 0 < S := by
    dsimp [S]
    simpa [levyQ] using hD
  have hQν : ∀ i : Fin m, (levyQ (ν i) (ρ' i)).toReal = (levyQ (μ i) (ρ i)).toReal := by
    intro i
    have hsc' : levyQ (ν i) (ρ' i) = levyQ (μ i) (ρ i) := by
      have hsc := levyQ_map_const_mul (μ i) c (ρ i) hc0
      simpa [ν, ρ'] using hsc
    exact congrArg ENNReal.toReal hsc'
  have hS'eq : S' = S / r ^ 2 := by
    dsimp [S', S]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hQν i, hρ'eq i]
    field_simp [hrne]
  have hS'pos : 0 < S' := by
    rw [hS'eq]
    exact div_pos hS (sq_pos_of_ne_zero hrne)
  have hS0 : 0 ≤ S := le_of_lt hS
  have hcore_apply := hcore m ν ρ' hρ'pos hρ'le (by simpa [S', levyQ] using hS'pos)
  have hcoreI : (∫ s in (-(1 : ℝ))..(1 : ℝ), ∏ i : Fin m, ‖charFun (ν i) s‖)
      ≤ C / Real.sqrt S' := by
    simpa [S', levyQ] using hcore_apply
  have hfun : ∀ s : ℝ,
      (∏ i : Fin m, ‖charFun (μ i) (s / r)‖) = (∏ i : Fin m, ‖charFun (ν i) s‖) := by
    intro s
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    have hcf : charFun (ν i) s = charFun (μ i) (c * s) := by
      dsimp [ν]
      exact charFun_map_mul' (μ i) c s
    rw [hcf]
    congr 1
    dsimp [c]
    ring
  calc
    (∫ t in (-(1 / r))..(1 / r), ∏ i : Fin m, ‖charFun (μ i) t‖)
        = (1 / r) * (∫ s in (-(1 : ℝ))..(1 : ℝ), ∏ i : Fin m, ‖charFun (μ i) (s / r)‖) := by
            simpa using (interval_integral_inv_mul r hrne (fun t => ∏ i : Fin m, ‖charFun (μ i) t‖))
    _ = (1 / r) * (∫ s in (-(1 : ℝ))..(1 : ℝ), ∏ i : Fin m, ‖charFun (ν i) s‖) := by
            rw [show (fun s : ℝ => ∏ i : Fin m, ‖charFun (μ i) (s / r)‖)
                  = (fun s : ℝ => ∏ i : Fin m, ‖charFun (ν i) s‖) from funext hfun]
    _ ≤ (1 / r) * (C / Real.sqrt S') := by
            exact mul_le_mul_of_nonneg_left hcoreI (by positivity)
    _ = C / Real.sqrt S := by
            have hsqrt' : Real.sqrt S' = Real.sqrt S / r := by
              rw [hS'eq, Real.sqrt_div hS0 (r ^ 2), Real.sqrt_sq_eq_abs, abs_of_pos hr]
            rw [hsqrt']
            field_simp [hrne, ne_of_gt (Real.sqrt_pos.2 hS)]

end

end Commons.Probability.Levy
