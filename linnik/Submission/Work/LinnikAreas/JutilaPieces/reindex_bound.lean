import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.JutilaPieces

open scoped BigOperators
open Finset
open Work.LinnikAreas.Density4 (SmoothOf)

/-- If `μ n ≠ 0` then `(μ n)² = 1` over the reals. -/
private lemma moebius_cast_sq (n : ℕ) (hn : ArithmeticFunction.moebius n ≠ 0) :
    (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
  have hsf : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hn
  have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  exact_mod_cast h

/-- Two factorisations of the same integer `l₁ d₁ = l₂ d₂` with `l₁, l₂` squarefree and
`dᵢ ∣ lᵢ ^ dᵢ` (every prime factor of `dᵢ` divides `lᵢ`) force `l₁ = l₂`: indeed both `lᵢ`
equal `rad (lᵢ dᵢ)`. -/
private lemma resonant_inj {l₁ d₁ l₂ d₂ : ℕ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hsf₁ : Squarefree l₁) (hsf₂ : Squarefree l₂)
    (hsm₁ : d₁ ∣ l₁ ^ d₁) (hsm₂ : d₂ ∣ l₂ ^ d₂)
    (heq : l₁ * d₁ = l₂ * d₂) : l₁ = l₂ := by
  have hpf : l₁.primeFactors = l₂.primeFactors := by
    ext p
    rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hpp, hpd, _⟩
      have hpd' : p ∣ l₂ * d₂ := by rw [← heq]; exact dvd_mul_of_dvd_left hpd d₁
      rcases (hpp.dvd_mul).mp hpd' with h | h
      · exact ⟨hpp, h, hl₂⟩
      · exact ⟨hpp, hpp.dvd_of_dvd_pow (h.trans hsm₂), hl₂⟩
    · rintro ⟨hpp, hpd, _⟩
      have hpd' : p ∣ l₁ * d₁ := by rw [heq]; exact dvd_mul_of_dvd_left hpd d₂
      rcases (hpp.dvd_mul).mp hpd' with h | h
      · exact ⟨hpp, h, hl₁⟩
      · exact ⟨hpp, hpp.dvd_of_dvd_pow (h.trans hsm₁), hl₁⟩
  calc l₁ = ∏ p ∈ l₁.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsf₁).symm
    _ = ∏ p ∈ l₂.primeFactors, p := by rw [hpf]
    _ = l₂ := Nat.prod_primeFactors_of_squarefree hsf₂

lemma reindex_bound (V : ℕ) (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) :
    (∑ l ∈ Finset.Icc 1 V,
        ∑ d ∈ (Finset.Icc 1 (V / l)).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
          (ArithmeticFunction.moebius l : ℝ) ^ 2 * ((1 / ((l * d : ℕ) : ℝ)) * h (l * d)))
      ≤ ∑ n ∈ Finset.Icc 1 V, (1 / (n : ℝ)) * h n := by
  classical
  let G : ℕ → ℝ := fun n => (1 / (n : ℝ)) * h n
  set S : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.Icc 1 V).sigma (fun l => (Finset.Icc 1 (V / l)).filter (fun d => SmoothOf d l))
    with hSdef
  set S1 : Finset (Σ _ : ℕ, ℕ) :=
    S.filter (fun p => ArithmeticFunction.moebius p.1 ≠ 0) with hS1def
  have h1 : (∑ l ∈ Finset.Icc 1 V,
        ∑ d ∈ (Finset.Icc 1 (V / l)).filter (fun d => SmoothOf d l),
          (ArithmeticFunction.moebius l : ℝ) ^ 2 * ((1 / ((l * d : ℕ) : ℝ)) * h (l * d)))
      = ∑ p ∈ S, (ArithmeticFunction.moebius p.1 : ℝ) ^ 2 * G (p.1 * p.2) := by
    rw [hSdef]
    refine (Finset.sum_sigma (s := Finset.Icc 1 V)
      (t := fun l => (Finset.Icc 1 (V / l)).filter (fun d => SmoothOf d l))
      (f := fun p : (Σ _ : ℕ, ℕ) =>
        (ArithmeticFunction.moebius p.1 : ℝ) ^ 2 * G (p.1 * p.2))).symm
  have h2 : (∑ p ∈ S, (ArithmeticFunction.moebius p.1 : ℝ) ^ 2 * G (p.1 * p.2))
      = ∑ p ∈ S1, (ArithmeticFunction.moebius p.1 : ℝ) ^ 2 * G (p.1 * p.2) := by
    rw [hS1def]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro p hpS hpnotin
    rw [Finset.mem_filter] at hpnotin
    by_cases hmu : ArithmeticFunction.moebius p.1 = 0
    · simp [hmu]
    · exact absurd ⟨hpS, hmu⟩ hpnotin
  have h3 : (∑ p ∈ S1, (ArithmeticFunction.moebius p.1 : ℝ) ^ 2 * G (p.1 * p.2))
      = ∑ p ∈ S1, G (p.1 * p.2) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp' : ArithmeticFunction.moebius p.1 ≠ 0 := by
      rw [hS1def, Finset.mem_filter] at hp
      exact hp.2
    rw [moebius_cast_sq p.1 hp', one_mul]
  have hsub : S1.image (fun p : (Σ _ : ℕ, ℕ) => p.1 * p.2) ⊆ Finset.Icc 1 V := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    rw [hS1def, Finset.mem_filter] at hp
    rw [hSdef, Finset.mem_sigma] at hp
    obtain ⟨hp1, hp2⟩ := hp.1
    rw [Finset.mem_Icc] at hp1
    rw [Finset.mem_filter, Finset.mem_Icc] at hp2
    obtain ⟨⟨hp2a, hp2b⟩, -⟩ := hp2
    rw [Finset.mem_Icc]
    constructor
    · have : 0 < p.1 * p.2 := Nat.mul_pos (by omega) (by omega)
      omega
    · calc p.1 * p.2 ≤ p.1 * (V / p.1) := Nat.mul_le_mul_left p.1 hp2b
        _ ≤ V := Nat.mul_div_le V p.1
  have h4 : (∑ p ∈ S1, G (p.1 * p.2))
      = ∑ n ∈ S1.image (fun p : (Σ _ : ℕ, ℕ) => p.1 * p.2), G n := by
    refine (Finset.sum_image ?_).symm
    intro p hp q hq heq
    obtain ⟨l₁, d₁⟩ := p
    obtain ⟨l₂, d₂⟩ := q
    rw [Finset.mem_coe, hS1def, Finset.mem_filter] at hp hq
    obtain ⟨hpS, hpμ⟩ := hp
    obtain ⟨hqS, hqμ⟩ := hq
    rw [hSdef, Finset.mem_sigma] at hpS hqS
    obtain ⟨hp1, hp2⟩ := hpS
    obtain ⟨hq1, hq2⟩ := hqS
    have hsm₁ : d₁ ∣ l₁ ^ d₁ := (Finset.mem_filter.mp hp2).2
    have hsm₂ : d₂ ∣ l₂ ^ d₂ := (Finset.mem_filter.mp hq2).2
    have hsf₁ : Squarefree l₁ := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hpμ
    have hsf₂ : Squarefree l₂ := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hqμ
    have hl₁ : l₁ ≠ 0 := hsf₁.ne_zero
    have hl₂ : l₂ ≠ 0 := hsf₂.ne_zero
    have heq' : l₁ * d₁ = l₂ * d₂ := heq
    have hlc : l₁ = l₂ := resonant_inj hl₁ hl₂ hsf₁ hsf₂ hsm₁ hsm₂ heq'
    have hdd : d₁ = d₂ := by
      rw [hlc] at heq'
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hl₂) heq'
    cases hlc
    cases hdd
    rfl
  have h5 : (∑ n ∈ S1.image (fun p : (Σ _ : ℕ, ℕ) => p.1 * p.2), G n)
      ≤ ∑ n ∈ Finset.Icc 1 V, G n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro n hn hnin
    exact mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg n)) (hh n)
  calc (∑ l ∈ Finset.Icc 1 V,
        ∑ d ∈ (Finset.Icc 1 (V / l)).filter (fun d => SmoothOf d l),
          (ArithmeticFunction.moebius l : ℝ) ^ 2 * ((1 / ((l * d : ℕ) : ℝ)) * h (l * d)))
      = ∑ p ∈ S, (ArithmeticFunction.moebius p.1 : ℝ) ^ 2 * G (p.1 * p.2) := h1
    _ = ∑ p ∈ S1, (ArithmeticFunction.moebius p.1 : ℝ) ^ 2 * G (p.1 * p.2) := h2
    _ = ∑ p ∈ S1, G (p.1 * p.2) := h3
    _ = ∑ n ∈ S1.image (fun p : (Σ _ : ℕ, ℕ) => p.1 * p.2), G n := h4
    _ ≤ ∑ n ∈ Finset.Icc 1 V, G n := h5

end Work.LinnikAreas.JutilaPieces
