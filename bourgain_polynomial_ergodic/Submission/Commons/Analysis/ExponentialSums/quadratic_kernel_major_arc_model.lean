import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic_at_quarter
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_circle_method_inputs

namespace Commons.Analysis.ExponentialSums

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable def quadraticKernel (N : ℕ) (α : ℝ) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * Finset.sum (Finset.range N)
    (fun n => Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ 2 : ℝ)) : ℂ)))

noncomputable def modelTerm (N q : ℕ) (a : ℕ) (l : ℤ) (α : ℝ) : ℂ :=
  ((q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun r =>
      Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ)) : ℂ))))
    * (∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
        ((((α - (a : ℝ) / (q : ℝ) - (l : ℝ)) * (N : ℝ) ^ 2 * s ^ 2 : ℝ)) : ℂ)))

noncomputable def majorArcBlock (δ : ℝ) (N : ℕ) (α : ℝ) (q : ℕ) : ℂ :=
  ∑ a ∈ Finset.range q,
    if Nat.gcd a q = 1 then
      ∑ l ∈ Finset.Icc (-2 : ℤ) 2,
        if |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹
          then modelTerm N q a l α else 0
    else 0

noncomputable def majorArcModel (δ : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ δ)), majorArcBlock δ N α q

/-- If a valid major-arc triple exists, the model collapses to the corresponding single term. -/
lemma majorArcModel_eq_single {δ : ℝ} {N : ℕ} {α : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hN : 3 ≤ N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h : ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ δ) ∧ x.2.1 < x.1 ∧
        Nat.gcd x.2.1 x.1 = 1 ∧ x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
        |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹) :
    majorArcModel δ N α = modelTerm N h.choose.1 h.choose.2.1 h.choose.2.2 α := by
  obtain ⟨hq1, hqfl, ha, hgcd, hl, hdist⟩ := h.choose_spec
  have hblk : majorArcBlock δ N α h.choose.1
      = modelTerm N h.choose.1 h.choose.2.1 h.choose.2.2 α := by
    rw [majorArcBlock]
    rw [Finset.sum_eq_single (s := Finset.range h.choose.1) (f := fun a =>
      (if Nat.gcd a h.choose.1 = 1 then
        ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          if |α - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
            then modelTerm N h.choose.1 a l α else 0
        else 0 : ℂ)) h.choose.2.1
      (fun a hamem hane => by
        by_cases hg : Nat.gcd a h.choose.1 = 1
        · rw [if_pos hg]
          refine Finset.sum_eq_zero (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
            (if |α - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
                then modelTerm N h.choose.1 a l α else 0 : ℂ)) (fun l hlmem => ?_)
          by_cases hc : |α - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
          · rw [if_pos hc]
            exact absurd (major_arc_representation_unique hN hδ hδ4 hα0 hα1
              hq1 hqfl (Finset.mem_range.mp hamem) hg hq1 hqfl ha hgcd hlmem hl hc hdist).2.1 hane
          · rw [if_neg hc]
        · rw [if_neg hg])
      (fun hnot => absurd (Finset.mem_range.mpr ha) hnot)]
    rw [if_pos hgcd]
    rw [Finset.sum_eq_single (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
      (if |α - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
          then modelTerm N h.choose.1 h.choose.2.1 l α else 0 : ℂ)) h.choose.2.2
      (fun l hlmem hlne => by
        by_cases hc : |α - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
        · rw [if_pos hc]
          exact absurd (major_arc_representation_unique hN hδ hδ4 hα0 hα1
            hq1 hqfl ha hgcd hq1 hqfl ha hgcd hl hlmem hdist hc).2.2 (Ne.symm hlne)
        · rw [if_neg hc])
      (fun hnot => absurd hl hnot)]
    rw [if_pos hdist]
  rw [majorArcModel]
  rw [Finset.sum_eq_single (s := Finset.Icc 1 (Nat.floor ((N : ℝ) ^ δ)))
    (f := majorArcBlock δ N α) h.choose.1
    (fun q hqmem hqne => by
      rw [majorArcBlock]
      refine Finset.sum_eq_zero (s := Finset.range q) (f := fun a =>
        (if Nat.gcd a q = 1 then
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
              then modelTerm N q a l α else 0
          else 0 : ℂ)) (fun a hamem => ?_)
      by_cases hg : Nat.gcd a q = 1
      · rw [if_pos hg]
        refine Finset.sum_eq_zero (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
          (if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
              then modelTerm N q a l α else 0 : ℂ)) (fun l hlmem => ?_)
        by_cases hc : |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
        · rw [if_pos hc]
          exact absurd (major_arc_representation_unique hN hδ hδ4 hα0 hα1
            (Finset.mem_Icc.mp hqmem).1 (Finset.mem_Icc.mp hqmem).2 (Finset.mem_range.mp hamem) hg
            hq1 hqfl ha hgcd hlmem hl hc hdist).1 hqne
        · rw [if_neg hc]
      · rw [if_neg hg])
    (fun hnot => absurd (Finset.mem_Icc.mpr ⟨hq1, hqfl⟩) hnot)]
  exact hblk

/-- If no valid major-arc triple exists, the model vanishes. -/
lemma majorArcModel_eq_zero {δ : ℝ} {N : ℕ} {α : ℝ}
    (h : ¬ ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ δ) ∧ x.2.1 < x.1 ∧
        Nat.gcd x.2.1 x.1 = 1 ∧ x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
        |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ ((N : ℝ) ^ (1 + δ))⁻¹) :
    majorArcModel δ N α = 0 := by
  rw [majorArcModel]
  refine Finset.sum_eq_zero (s := Finset.Icc 1 (Nat.floor ((N : ℝ) ^ δ)))
    (f := majorArcBlock δ N α) (fun q hqmem => ?_)
  rw [majorArcBlock]
  refine Finset.sum_eq_zero (s := Finset.range q) (f := fun a =>
    (if Nat.gcd a q = 1 then
      ∑ l ∈ Finset.Icc (-2:ℤ) 2,
        if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
          then modelTerm N q a l α else 0
      else 0 : ℂ)) (fun a hamem => ?_)
  by_cases hg : Nat.gcd a q = 1
  · rw [if_pos hg]
    refine Finset.sum_eq_zero (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
      (if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
          then modelTerm N q a l α else 0 : ℂ)) (fun l hlmem => ?_)
    by_cases hc : |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ ((N:ℝ)^(1+δ))⁻¹
    · rw [if_pos hc]
      exact absurd ⟨(q, a, l), (Finset.mem_Icc.mp hqmem).1, (Finset.mem_Icc.mp hqmem).2,
        Finset.mem_range.mp hamem, hg, hlmem, hc⟩ h
    · rw [if_neg hc]
  · rw [if_neg hg]

/-- Major-arc asymptotic for the square kernel with the scale fixed to `1/4`. -/
theorem quadratic_kernel_major_arc_bound_quarter :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ), 3 ≤ N → ∀ (a : ℤ) (q : ℕ) (l : ℤ) (α : ℝ), 1 ≤ q →
        (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) → Int.gcd a (q : ℤ) = 1 →
        |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ ((N : ℝ) ^ (1 + (1:ℝ)/4))⁻¹ →
        ‖quadraticKernel N α
          - ((q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun r =>
              Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ)) : ℂ))))
            * (∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
                ((((α - (a : ℝ) / (q : ℝ) - (l : ℝ)) * (N : ℝ) ^ 2 * s ^ 2 : ℝ)) : ℂ)))‖
        ≤ C * ((N : ℝ) ^ c)⁻¹ := by
  obtain ⟨θ, hθ0, C, hC0, hasym⟩ :=
    Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic_at_quarter
  refine ⟨θ, C, hθ0, hC0, ?_⟩
  intro N hN a q l α hq hqδ hgcd hb
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hkey := hasym N a q (α - (a : ℝ) / (q : ℝ) - (l : ℝ)) (by omega) (by omega) hqδ hgcd hb
  have hphase : ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ 2 : ℝ)) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I *
            ((((a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ) - (l : ℝ))) * (n : ℝ) ^ 2 : ℝ) : ℂ)) := by
    intro n
    rw [show (a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ) - (l : ℝ)) = α - (l : ℝ) by ring]
    have harg : (α * (n : ℝ) ^ 2 : ℝ)
        = ((α - (l : ℝ)) * (n : ℝ) ^ 2) - (-(l * ((n : ℤ)) ^ 2) : ℤ) := by push_cast; ring
    rw [harg]
    exact exp_phase_shift_int ((α - (l : ℝ)) * (n : ℝ) ^ 2) (-(l * ((n : ℤ)) ^ 2))
  have hsum : Finset.sum (Finset.range N) (fun n =>
        Complex.exp (2 * Real.pi * Complex.I * ((α * (n : ℝ) ^ 2 : ℝ) : ℂ)))
      = Finset.sum (Finset.range N) (fun n => Complex.exp (2 * Real.pi * Complex.I *
          ((((a : ℝ) / (q : ℝ) + (α - (a : ℝ) / (q : ℝ) - (l : ℝ))) * (n : ℝ) ^ 2 : ℝ) : ℂ))) :=
    Finset.sum_congr rfl (fun n _ => hphase n)
  have hcast : (((N : ℝ)) : ℂ)⁻¹ = ((((N : ℝ)⁻¹ : ℝ)) : ℂ) := by rw [← Complex.ofReal_inv]
  rw [quadraticKernel]
  rw [hsum, hcast]
  exact hkey


lemma sq_inv_le_sq_inv {N : ℕ} (hN1 : (1 : ℝ) ≤ (N : ℝ)) {a b : ℝ}
    (hab : b ≤ a) : ((N : ℝ) ^ a)⁻¹ ≤ ((N : ℝ) ^ b)⁻¹ :=
  inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hN1 hab)

theorem quadratic_kernel_major_arc_model :
    ∃ cm Cm : ℝ, 0 < cm ∧ 0 < Cm ∧
      ∀ (N : ℕ), 3 ≤ N → ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
        ‖quadraticKernel N α - majorArcModel ((1:ℝ)/4) N α‖ ≤ Cm * ((N : ℝ) ^ cm)⁻¹ := by
  obtain ⟨ca, Ca, hca0, hCa0, hmaj⟩ := quadratic_kernel_major_arc_bound_quarter
  obtain ⟨ν, Cν, hν0, hCν0, hmin⟩ := quadratic_kernel_minor_arc_bound ((1:ℝ)/4)
    (by norm_num) (by norm_num)
  refine ⟨min ca ν, max Ca Cν + 1, lt_min hca0 hν0, by positivity, ?_⟩
  intro N hN α hα0 hα1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  by_cases hcase : ∃ x : ℕ × ℕ × ℤ,
      1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) ∧ x.2.1 < x.1 ∧ Nat.gcd x.2.1 x.1 = 1 ∧
      x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
      |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ ((N : ℝ) ^ (1 + (1:ℝ)/4))⁻¹
  · obtain ⟨hq1, hqfl, ha, hgcd, hl, hdist⟩ := hcase.choose_spec
    rw [majorArcModel_eq_single (by norm_num) (by norm_num) hN hα0 hα1 hcase]
    have hqN : ((hcase.choose.1 : ℝ)) ≤ (N : ℝ) ^ ((1:ℝ)/4) := by
      have h1 : ((hcase.choose.1 : ℝ)) ≤ (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) : ℝ) := by
        exact_mod_cast hqfl
      have h2 := Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hNpos ((1:ℝ)/4)))
      linarith
    have hgcd' : Int.gcd ((hcase.choose.2.1 : ℤ)) ((hcase.choose.1 : ℤ)) = 1 := by
      rw [Int.gcd_natCast_natCast]; exact hgcd
    have hdist' : |α - ((hcase.choose.2.1 : ℤ) : ℝ) / (hcase.choose.1 : ℝ)
        - (hcase.choose.2.2 : ℝ)| ≤ ((N : ℝ) ^ (1 + (1:ℝ)/4))⁻¹ := by
      rw [show ((hcase.choose.2.1 : ℤ) : ℝ) = (hcase.choose.2.1 : ℝ) by push_cast; ring]
      exact hdist
    have hkey := hmaj N hN ((hcase.choose.2.1 : ℤ)) hcase.choose.1 hcase.choose.2.2 α hq1
      hqN hgcd' hdist'
    simp only [modelTerm] at hkey ⊢
    have hfin : Ca * ((N : ℝ) ^ ca)⁻¹ ≤ (max Ca Cν + 1) * ((N : ℝ) ^ (min ca ν))⁻¹ := by
      have h1 : ((N : ℝ) ^ ca)⁻¹ ≤ ((N : ℝ) ^ (min ca ν))⁻¹ :=
        sq_inv_le_sq_inv hN1 (min_le_left _ _)
      have h2 : Ca ≤ max Ca Cν + 1 := by have := le_max_left Ca Cν; linarith
      exact mul_le_mul h2 h1 (by positivity) (by positivity)
    exact le_trans hkey hfin
  · rw [majorArcModel_eq_zero hcase, sub_zero]
    have hnoarc : ∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) →
        a < q → Nat.gcd a q = 1 →
        ((N : ℝ) ^ (1 + (1:ℝ)/4))⁻¹ < |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| := by
      intro q a l hq hqfl ha hg
      by_cases hl : l ∈ Finset.Icc (-2 : ℤ) 2
      · by_contra hcon
        push_neg at hcon
        exact hcase ⟨(q, a, l), hq, hqfl, ha, hg, hl, hcon⟩
      · have hlarge : (1 : ℝ) < |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| := by
          have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
          have haq0 : 0 ≤ (a : ℝ) / (q : ℝ) := by positivity
          have haq1 : (a : ℝ) / (q : ℝ) < 1 := by
            rw [div_lt_one hqpos]; exact_mod_cast ha
          have hl' : (l : ℤ) ≤ -3 ∨ 3 ≤ (l : ℤ) := by
            rw [Finset.mem_Icc] at hl
            omega
          rcases hl' with hl2 | hl3
          · have hle : (l : ℝ) ≤ -3 := by exact_mod_cast hl2
            rw [abs_of_pos (by linarith)]
            linarith
          · have hle : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl3
            rw [abs_of_neg (by linarith)]
            linarith
        have hsmall : ((N : ℝ) ^ (1 + (1:ℝ)/4))⁻¹ ≤ (1 : ℝ) := by
          rw [inv_le_one₀ (by positivity)]
          exact Real.one_le_rpow hN1 (by norm_num)
        linarith
    have hkey := hmin ((1:ℝ)/4) (by norm_num) (by norm_num) N hN α hα0 hα1 hnoarc
    have hfin : Cν * ((N : ℝ) ^ ν)⁻¹ ≤ (max Ca Cν + 1) * ((N : ℝ) ^ (min ca ν))⁻¹ := by
      have h1 : ((N : ℝ) ^ ν)⁻¹ ≤ ((N : ℝ) ^ (min ca ν))⁻¹ :=
        sq_inv_le_sq_inv hN1 (min_le_right _ _)
      have h2 : Cν ≤ max Ca Cν + 1 := by have := le_max_right Ca Cν; linarith
      exact mul_le_mul h2 h1 (by positivity) (by positivity)
    exact le_trans hkey hfin

end Commons.Analysis.ExponentialSums
