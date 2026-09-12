import Mathlib
import Submission.S6Core

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex
open FlatLittlewoodPoly
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false


namespace Submission
namespace Flat

/-- Family 1: Rudin-Shapiro P-block cosine monomials. -/
def fP (t q : ℕ) : ℂ[X] :=
  ∑ r ∈ Finset.range (2 ^ t),
    Polynomial.C ((RudinShapiro.P t).coeff r) *
      (Polynomial.X ^ (2 * q + 2 * (Sec3H.T t + r)) +
        Polynomial.X ^ (2 * q - 2 * (Sec3H.T t + r)))
/-- Family 2: Rudin-Shapiro Q-block cosine monomials. -/
def fQ (t q : ℕ) : ℂ[X] :=
  ∑ r ∈ Finset.range (2 ^ t),
    Polynomial.C ((RudinShapiro.Q t).coeff r) *
      (Polynomial.X ^ (2 * q + 2 * (2 * Sec3H.T t + r)) +
        Polynomial.X ^ (2 * q - 2 * (2 * Sec3H.T t + r)))
/-- Family 3: even sine monomials over `j ∉ Cp`. -/
def fC (s q t : ℕ) : ℂ[X] :=
  ∑ j ∈ (Finset.Icc 1 q) \ Cp t,
    Polynomial.C ((RudinShapiro.P s).coeff j) *
      (Polynomial.X ^ (2 * q + 2 * j) - Polynomial.X ^ (2 * q - 2 * j))
/-- Family 4: odd sine monomials from the colouring. -/
def fD (q : ℕ) (eps : Fin q → ℝ) : ℂ[X] :=
  ∑ i : Fin q, Polynomial.C ((eps i : ℝ) : ℂ) *
      (Polynomial.X ^ (2 * q + (2 * i.1 + 1)) - Polynomial.X ^ (2 * q - (2 * i.1 + 1)))

lemma flatPoly_eq (t s q : ℕ) (eps : Fin q → ℝ) :
    flatPoly t s q eps = Polynomial.X ^ (2 * q) + fP t q + fQ t q + fC s q t + fD q eps := by
  rfl


/-! ## coeff of `C c * (X^e1 ± X^e2)` -/

lemma coeff_C_mul_add_X_pow (c : ℂ) (e1 e2 m : ℕ) :
    (Polynomial.C c * (Polynomial.X ^ e1 + Polynomial.X ^ e2)).coeff m =
      (if m = e1 then c else 0) + (if m = e2 then c else 0) := by
  rw [mul_add]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]

lemma coeff_C_mul_sub_X_pow (c : ℂ) (e1 e2 m : ℕ) :
    (Polynomial.C c * (Polynomial.X ^ e1 - Polynomial.X ^ e2)).coeff m =
      (if m = e1 then c else 0) - (if m = e2 then c else 0) := by
  rw [mul_sub]
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]

/-! ## Bounds from `hm` -/

lemma T_add_r_le_q {t q : ℕ} (hm : Sec3.m_t t ≤ q) (r : ℕ) (hr : r < 2 ^ t) :
    Sec3H.T t + r ≤ q := by
  have hmem : Sec3H.T t + r ∈ C1 t := (mem_C1_iff (t := t) (Sec3H.T t + r)).mpr ⟨r, hr, rfl⟩
  have hicc : Sec3H.T t + r ∈ Finset.Icc 1 q :=
    (Cp_subset_Icc (t := t) (q := q) hm) (Finset.mem_union_left (C2 t) hmem)
  exact (Finset.mem_Icc.mp hicc).2

lemma twoT_add_r_le_q {t q : ℕ} (hm : Sec3.m_t t ≤ q) (r : ℕ) (hr : r < 2 ^ t) :
    2 * Sec3H.T t + r ≤ q := by
  have hmem : 2 * Sec3H.T t + r ∈ C2 t := (mem_C2_iff (t := t) (2 * Sec3H.T t + r)).mpr ⟨r, hr, rfl⟩
  have hicc : 2 * Sec3H.T t + r ∈ Finset.Icc 1 q :=
    (Cp_subset_Icc (t := t) (q := q) hm) (Finset.mem_union_right (C1 t) hmem)
  exact (Finset.mem_Icc.mp hicc).2

lemma q_pos_of_hm {t q : ℕ} (hm : Sec3.m_t t ≤ q) : 1 ≤ q := by
  have h1 : 2 ≤ 2 ^ (t + 11) := by
    have hp : 2 ^ 1 ≤ 2 ^ (t + 11) := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega : 1 ≤ t + 11)
    norm_num at hp
    exact hp
  change 2 ^ (t + 11) + 2 ^ t - 1 ≤ q at hm
  have h2 : 1 ≤ 2 ^ t := RudinShapiro.two_pow_ge_one t
  omega

/-! ## Collapse of indicator sums over `r < 2^t` -/

lemma sum_if_C1 (t : ℕ) (j : ℕ) (p : ℕ → ℂ) :
    (∑ r ∈ Finset.range (2 ^ t), if Sec3H.T t + r = j then p r else 0) =
      if j ∈ C1 t then p (j - Sec3H.T t) else 0 := by
  by_cases hj : j ∈ C1 t
  · rcases (mem_C1_iff (t := t) j).mp hj with ⟨r0, hr0lt, hr0eq⟩
    rw [if_pos hj]
    have hsum0 :
        (∑ r ∈ Finset.range (2 ^ t), if Sec3H.T t + r = j then p r else 0)
          = (if Sec3H.T t + r0 = j then p r0 else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun r => if Sec3H.T t + r = j then p r else 0) r0 ?_ ?_
      · exact Finset.mem_range.mpr hr0lt
      · intro b hb hbne
        have hcond : Sec3H.T t + b ≠ j := by
          intro hc
          have hbr : b = r0 := by omega
          exact hbne hbr
        simp [hcond]
    have hsum : (∑ r ∈ Finset.range (2 ^ t), if Sec3H.T t + r = j then p r else 0) = p r0 := by
      simpa [hr0eq.symm] using hsum0
    calc
      (∑ r ∈ Finset.range (2 ^ t), if Sec3H.T t + r = j then p r else 0) = p r0 := hsum
      _ = p (j - Sec3H.T t) := by
        congr 1
        omega
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro r hr
    have hcond : Sec3H.T t + r ≠ j := by
      intro hc
      exact hj ((mem_C1_iff (t := t) j).mpr ⟨r, Finset.mem_range.mp hr, hc.symm⟩)
    simp [hcond]

lemma sum_if_C2 (t : ℕ) (j : ℕ) (p : ℕ → ℂ) :
    (∑ r ∈ Finset.range (2 ^ t), if 2 * Sec3H.T t + r = j then p r else 0) =
      if j ∈ C2 t then p (j - 2 * Sec3H.T t) else 0 := by
  by_cases hj : j ∈ C2 t
  · rcases (mem_C2_iff (t := t) j).mp hj with ⟨r0, hr0lt, hr0eq⟩
    rw [if_pos hj]
    have hsum0 :
        (∑ r ∈ Finset.range (2 ^ t), if 2 * Sec3H.T t + r = j then p r else 0)
          = (if 2 * Sec3H.T t + r0 = j then p r0 else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun r => if 2 * Sec3H.T t + r = j then p r else 0) r0 ?_ ?_
      · exact Finset.mem_range.mpr hr0lt
      · intro b hb hbne
        have hcond : 2 * Sec3H.T t + b ≠ j := by
          intro hc
          have hbr : b = r0 := by omega
          exact hbne hbr
        simp [hcond]
    have hsum : (∑ r ∈ Finset.range (2 ^ t), if 2 * Sec3H.T t + r = j then p r else 0) = p r0 := by
      simpa [hr0eq.symm] using hsum0
    calc
      (∑ r ∈ Finset.range (2 ^ t), if 2 * Sec3H.T t + r = j then p r else 0) = p r0 := hsum
      _ = p (j - 2 * Sec3H.T t) := by
        congr 1
        omega
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro r hr
    have hcond : 2 * Sec3H.T t + r ≠ j := by
      intro hc
      exact hj ((mem_C2_iff (t := t) j).mpr ⟨r, Finset.mem_range.mp hr, hc.symm⟩)
    simp [hcond]

/-! ## Coefficient of `fP` at `2q+2j` (plus side) -/

lemma coeff_fP_even_plus (t q j : ℕ) (hj1 : 1 ≤ j) :
    (fP t q).coeff (2 * q + 2 * j) =
      if j ∈ C1 t then (RudinShapiro.P t).coeff (j - Sec3H.T t) else 0 := by
  unfold fP
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hminus : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hcond : 2 * q + 2 * j ≠ 2 * q - 2 * (Sec3H.T t + r) := by omega
    simp [hcond]
  rw [hminus, add_zero]
  by_cases hj : j ∈ C1 t
  · rcases (mem_C1_iff (t := t) j).mp hj with ⟨r0, hr0lt, hr0eq⟩
    rw [if_pos hj]
    have hsum0 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0)
        = (if 2 * q + 2 * j = 2 * q + 2 * (Sec3H.T t + r0) then (RudinShapiro.P t).coeff r0 else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun r => if 2 * q + 2 * j = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) r0 ?_ ?_
      · exact Finset.mem_range.mpr hr0lt
      · intro b hb hbne
        by_cases hc : 2 * q + 2 * j = 2 * q + 2 * (Sec3H.T t + b)
        · have hbr : b = r0 := by omega
          exfalso
          exact hbne hbr
        · rw [if_neg hc]
    have hsum : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0)
        = (RudinShapiro.P t).coeff r0 := by
      simpa [hr0eq.symm] using hsum0
    calc
      (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0)
        = (RudinShapiro.P t).coeff r0 := hsum
      _ = (RudinShapiro.P t).coeff (j - Sec3H.T t) := by
        congr 1
        omega
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q + 2 * j = 2 * q + 2 * (Sec3H.T t + r)
    · have hjr : j = Sec3H.T t + r := by omega
      exfalso
      exact hj ((mem_C1_iff (t := t) j).mpr ⟨r, Finset.mem_range.mp hr, hjr⟩)
    · rw [if_neg hc]


lemma T_ge_one (t : ℕ) : 1 ≤ Sec3H.T t := by
  unfold Sec3H.T
  exact RudinShapiro.two_pow_ge_one (t + 10)

/-- coeff of `fQ` at `2q+2j` (plus side). -/
lemma coeff_fQ_even_plus (t q j : ℕ) (hj1 : 1 ≤ j) :
    (fQ t q).coeff (2 * q + 2 * j) =
      if j ∈ C2 t then (RudinShapiro.Q t).coeff (j - 2 * Sec3H.T t) else 0 := by
  unfold fQ
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hminus : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hcond : 2 * q + 2 * j ≠ 2 * q - 2 * (2 * Sec3H.T t + r) := by omega
    simp [hcond]
  rw [hminus, add_zero]
  by_cases hj : j ∈ C2 t
  · rcases (mem_C2_iff (t := t) j).mp hj with ⟨r0, hr0lt, hr0eq⟩
    rw [if_pos hj]
    have hsum0 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0)
        = (if 2 * q + 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r0) then (RudinShapiro.Q t).coeff r0 else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun r => if 2 * q + 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) r0 ?_ ?_
      · exact Finset.mem_range.mpr hr0lt
      · intro b hb hbne
        by_cases hc : 2 * q + 2 * j = 2 * q + 2 * (2 * Sec3H.T t + b)
        · have hbr : b = r0 := by omega
          exfalso
          exact hbne hbr
        · rw [if_neg hc]
    have hsum : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0)
        = (RudinShapiro.Q t).coeff r0 := by
      simpa [hr0eq.symm] using hsum0
    calc
      (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0)
        = (RudinShapiro.Q t).coeff r0 := hsum
      _ = (RudinShapiro.Q t).coeff (j - 2 * Sec3H.T t) := by
        congr 1
        omega
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q + 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r)
    · have hjr : j = 2 * Sec3H.T t + r := by omega
      exfalso
      exact hj ((mem_C2_iff (t := t) j).mpr ⟨r, Finset.mem_range.mp hr, hjr⟩)
    · rw [if_neg hc]

/-- coeff of `fC` at `2q+2j` (plus side). -/
lemma coeff_fC_even_plus (s q t j : ℕ) (hj1 : 1 ≤ j) :
    (fC s q t).coeff (2 * q + 2 * j) =
      if j ∈ (Finset.Icc 1 q) \ Cp t then (RudinShapiro.P s).coeff j else 0 := by
  unfold fC
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hminus : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q + 2 * j = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    have hcond : 2 * q + 2 * j ≠ 2 * q - 2 * j' := by omega
    simp [hcond]
  rw [hminus, sub_zero]
  by_cases hj : j ∈ (Finset.Icc 1 q) \ Cp t
  · rw [if_pos hj]
    have hsum0 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q + 2 * j = 2 * q + 2 * j' then (RudinShapiro.P s).coeff j' else 0)
        = (if 2 * q + 2 * j = 2 * q + 2 * j then (RudinShapiro.P s).coeff j else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun j' => if 2 * q + 2 * j = 2 * q + 2 * j' then (RudinShapiro.P s).coeff j' else 0) j ?_ ?_
      · exact hj
      · intro b hb hbne
        by_cases hc : 2 * q + 2 * j = 2 * q + 2 * b
        · have hbr : b = j := by omega
          exfalso
          exact hbne hbr
        · rw [if_neg hc]
    simpa using hsum0
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hc : 2 * q + 2 * j = 2 * q + 2 * b
    · have hbr : b = j := by omega
      exfalso
      exact hj (by simpa [hbr] using hb)
    · rw [if_neg hc]

/-- coeff of `fD` at an even exponent `2q+2j` is 0. -/
lemma coeff_fD_even_plus_zero (q j : ℕ) (eps : Fin q → ℝ) (hj1 : 1 ≤ j) :
    (fD q eps).coeff (2 * q + 2 * j) = 0 := by
  unfold fD
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ i : Fin q,
        if 2 * q + 2 * j = 2 * q + (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : 2 * q + 2 * j = 2 * q + (2 * i.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ i : Fin q,
        if 2 * q + 2 * j = 2 * q - (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : 2 * q + 2 * j = 2 * q - (2 * i.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num


/-- coeff of `fP` at `2q-2j` (minus side). -/
lemma coeff_fP_even_minus (t q : ℕ) (hm : Sec3.m_t t ≤ q) (j : ℕ) (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (fP t q).coeff (2 * q - 2 * j) =
      if j ∈ C1 t then (RudinShapiro.P t).coeff (j - Sec3H.T t) else 0 := by
  unfold fP
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hplus : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - 2 * j = 2 * q + 2 * (Sec3H.T t + r)
    · exfalso
      have hTr : 1 ≤ Sec3H.T t + r := by omega
      omega
    · rw [if_neg hc]
  rw [hplus, zero_add]
  by_cases hj : j ∈ C1 t
  · rcases (mem_C1_iff (t := t) j).mp hj with ⟨r0, hr0lt, hr0eq⟩
    rw [if_pos hj]
    have hsum0 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0)
        = (if 2 * q - 2 * j = 2 * q - 2 * (Sec3H.T t + r0) then (RudinShapiro.P t).coeff r0 else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun r => if 2 * q - 2 * j = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) r0 ?_ ?_
      · exact Finset.mem_range.mpr hr0lt
      · intro b hb hbne
        by_cases hc : 2 * q - 2 * j = 2 * q - 2 * (Sec3H.T t + b)
        · have hbq : Sec3H.T t + b ≤ q := T_add_r_le_q hm b (Finset.mem_range.mp hb)
          have hbr : b = r0 := by omega
          exfalso
          exact hbne hbr
        · rw [if_neg hc]
    have hsum : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0)
        = (RudinShapiro.P t).coeff r0 := by
      simpa [hr0eq.symm] using hsum0
    calc
      (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0)
        = (RudinShapiro.P t).coeff r0 := hsum
      _ = (RudinShapiro.P t).coeff (j - Sec3H.T t) := by
        congr 1
        omega
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - 2 * j = 2 * q - 2 * (Sec3H.T t + r)
    · have hbq : Sec3H.T t + r ≤ q := T_add_r_le_q hm r (Finset.mem_range.mp hr)
      have hjr : j = Sec3H.T t + r := by omega
      exfalso
      exact hj ((mem_C1_iff (t := t) j).mpr ⟨r, Finset.mem_range.mp hr, hjr⟩)
    · rw [if_neg hc]

/-- coeff of `fQ` at `2q-2j` (minus side). -/
lemma coeff_fQ_even_minus (t q : ℕ) (hm : Sec3.m_t t ≤ q) (j : ℕ) (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (fQ t q).coeff (2 * q - 2 * j) =
      if j ∈ C2 t then (RudinShapiro.Q t).coeff (j - 2 * Sec3H.T t) else 0 := by
  unfold fQ
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hplus : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - 2 * j = 2 * q + 2 * (2 * Sec3H.T t + r)
    · exfalso
      have hTr : 1 ≤ 2 * Sec3H.T t + r := by omega
      omega
    · rw [if_neg hc]
  rw [hplus, zero_add]
  by_cases hj : j ∈ C2 t
  · rcases (mem_C2_iff (t := t) j).mp hj with ⟨r0, hr0lt, hr0eq⟩
    rw [if_pos hj]
    have hsum0 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0)
        = (if 2 * q - 2 * j = 2 * q - 2 * (2 * Sec3H.T t + r0) then (RudinShapiro.Q t).coeff r0 else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun r => if 2 * q - 2 * j = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) r0 ?_ ?_
      · exact Finset.mem_range.mpr hr0lt
      · intro b hb hbne
        by_cases hc : 2 * q - 2 * j = 2 * q - 2 * (2 * Sec3H.T t + b)
        · have hbq : 2 * Sec3H.T t + b ≤ q := twoT_add_r_le_q hm b (Finset.mem_range.mp hb)
          have hbr : b = r0 := by omega
          exfalso
          exact hbne hbr
        · rw [if_neg hc]
    have hsum : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0)
        = (RudinShapiro.Q t).coeff r0 := by
      simpa [hr0eq.symm] using hsum0
    calc
      (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - 2 * j = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0)
        = (RudinShapiro.Q t).coeff r0 := hsum
      _ = (RudinShapiro.Q t).coeff (j - 2 * Sec3H.T t) := by
        congr 1
        omega
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - 2 * j = 2 * q - 2 * (2 * Sec3H.T t + r)
    · have hbq : 2 * Sec3H.T t + r ≤ q := twoT_add_r_le_q hm r (Finset.mem_range.mp hr)
      have hjr : j = 2 * Sec3H.T t + r := by omega
      exfalso
      exact hj ((mem_C2_iff (t := t) j).mpr ⟨r, Finset.mem_range.mp hr, hjr⟩)
    · rw [if_neg hc]

/-- coeff of `fC` at `2q-2j` (minus side). -/
lemma coeff_fC_even_minus (s q t : ℕ) (j : ℕ) (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (fC s q t).coeff (2 * q - 2 * j) =
      if j ∈ (Finset.Icc 1 q) \ Cp t then - (RudinShapiro.P s).coeff j else 0 := by
  unfold fC
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hplus : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q - 2 * j = 2 * q + 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : 2 * q - 2 * j = 2 * q + 2 * j'
    · exfalso
      omega
    · rw [if_neg hc]
  have hminus : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q - 2 * j = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0)
        = if j ∈ (Finset.Icc 1 q) \ Cp t then (RudinShapiro.P s).coeff j else 0 := by
    by_cases hj : j ∈ (Finset.Icc 1 q) \ Cp t
    · rw [if_pos hj]
      have hsum0 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
          if 2 * q - 2 * j = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0)
          = (if 2 * q - 2 * j = 2 * q - 2 * j then (RudinShapiro.P s).coeff j else 0) := by
        refine Finset.sum_eq_single_of_mem
          (f := fun j' => if 2 * q - 2 * j = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0) j ?_ ?_
        · exact hj
        · intro b hb hbne
          by_cases hc : 2 * q - 2 * j = 2 * q - 2 * b
          · have hbj : b ≤ q := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hb).1).2
            have hbr : b = j := by omega
            exfalso
            exact hbne hbr
          · rw [if_neg hc]
      simpa using hsum0
    · rw [if_neg hj]
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hc : 2 * q - 2 * j = 2 * q - 2 * b
      · have hbj : b ≤ q := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hb).1).2
        have hbr : b = j := by omega
        exfalso
        exact hj (by simpa [hbr] using hb)
      · rw [if_neg hc]
  rw [hplus, hminus]
  by_cases hj : j ∈ (Finset.Icc 1 q) \ Cp t
  · simp [hj]
  · simp [hj]

/-- coeff of `fD` at an even exponent `2q-2j` is 0. -/
lemma coeff_fD_even_minus_zero (q j : ℕ) (eps : Fin q → ℝ) (hj1 : 1 ≤ j) :
    (fD q eps).coeff (2 * q - 2 * j) = 0 := by
  unfold fD
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ i : Fin q,
        if 2 * q - 2 * j = 2 * q + (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : 2 * q - 2 * j = 2 * q + (2 * i.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ i : Fin q,
        if 2 * q - 2 * j = 2 * q - (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : 2 * q - 2 * j = 2 * q - (2 * i.1 + 1)
    · have hqi : 2 * i.1 + 1 ≤ 2 * q := by omega
      exfalso
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num


/-! ### coefficients vanish at `2q` (middle) -/

lemma coeff_fP_mid_zero (t q : ℕ) (hm : Sec3.m_t t ≤ q) :
    (fP t q).coeff (2 * q) = 0 := by
  unfold fP
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q = 2 * q + 2 * (Sec3H.T t + r)
    · exfalso
      have hTr : 1 ≤ Sec3H.T t + r := by
        have hT : 1 ≤ Sec3H.T t := T_ge_one t
        omega
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q = 2 * q - 2 * (Sec3H.T t + r)
    · exfalso
      have hTr1 : 1 ≤ Sec3H.T t + r := by
        have hT : 1 ≤ Sec3H.T t := T_ge_one t
        omega
      have hTr : Sec3H.T t + r ≤ q := T_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fQ_mid_zero (t q : ℕ) (hm : Sec3.m_t t ≤ q) :
    (fQ t q).coeff (2 * q) = 0 := by
  unfold fQ
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q = 2 * q + 2 * (2 * Sec3H.T t + r)
    · exfalso
      have hTr : 1 ≤ 2 * Sec3H.T t + r := by
        have hT : 1 ≤ Sec3H.T t := T_ge_one t
        omega
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q = 2 * q - 2 * (2 * Sec3H.T t + r)
    · exfalso
      have hTr1 : 1 ≤ 2 * Sec3H.T t + r := by
        have hT : 1 ≤ Sec3H.T t := T_ge_one t
        omega
      have hTr : 2 * Sec3H.T t + r ≤ q := twoT_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fC_mid_zero (s q t : ℕ) :
    (fC s q t).coeff (2 * q) = 0 := by
  unfold fC
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q = 2 * q + 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : 2 * q = 2 * q + 2 * j'
    · exfalso
      have h1 : 1 ≤ j' := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj').1).1
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : 2 * q = 2 * q - 2 * j'
    · exfalso
      have h1 : 1 ≤ j' := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj').1).1
      have h2 : j' ≤ q := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj').1).2
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fD_mid_zero (q : ℕ) (eps : Fin q → ℝ) :
    (fD q eps).coeff (2 * q) = 0 := by
  unfold fD
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ i : Fin q,
        if 2 * q = 2 * q + (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : 2 * q = 2 * q + (2 * i.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ i : Fin q,
        if 2 * q = 2 * q - (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : 2 * q = 2 * q - (2 * i.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

/-! ### coefficient of odd families at odd targets is zero -/

lemma coeff_fP_odd_plus_zero (t q : ℕ) (hm : Sec3.m_t t ≤ q) (i : ℕ) (hiq : i < q) :
    (fP t q).coeff (2 * q + (2 * i + 1)) = 0 := by
  unfold fP
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + (2 * i + 1) = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q + (2 * i + 1) = 2 * q + 2 * (Sec3H.T t + r)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + (2 * i + 1) = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q + (2 * i + 1) = 2 * q - 2 * (Sec3H.T t + r)
    · exfalso
      have hTr : Sec3H.T t + r ≤ q := T_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fQ_odd_plus_zero (t q : ℕ) (hm : Sec3.m_t t ≤ q) (i : ℕ) (hiq : i < q) :
    (fQ t q).coeff (2 * q + (2 * i + 1)) = 0 := by
  unfold fQ
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + (2 * i + 1) = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q + (2 * i + 1) = 2 * q + 2 * (2 * Sec3H.T t + r)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q + (2 * i + 1) = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q + (2 * i + 1) = 2 * q - 2 * (2 * Sec3H.T t + r)
    · exfalso
      have hTr : 2 * Sec3H.T t + r ≤ q := twoT_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fC_odd_plus_zero (s q t : ℕ) (i : ℕ) (hiq : i < q) :
    (fC s q t).coeff (2 * q + (2 * i + 1)) = 0 := by
  unfold fC
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q + (2 * i + 1) = 2 * q + 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : 2 * q + (2 * i + 1) = 2 * q + 2 * j'
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q + (2 * i + 1) = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : 2 * q + (2 * i + 1) = 2 * q - 2 * j'
    · exfalso
      have h2 : j' ≤ q := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj').1).2
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fP_odd_minus_zero (t q : ℕ) (hm : Sec3.m_t t ≤ q) (i : ℕ) (hiq : i < q) :
    (fP t q).coeff (2 * q - (2 * i + 1)) = 0 := by
  unfold fP
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - (2 * i + 1) = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - (2 * i + 1) = 2 * q + 2 * (Sec3H.T t + r)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - (2 * i + 1) = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - (2 * i + 1) = 2 * q - 2 * (Sec3H.T t + r)
    · exfalso
      have hTr : Sec3H.T t + r ≤ q := T_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fQ_odd_minus_zero (t q : ℕ) (hm : Sec3.m_t t ≤ q) (i : ℕ) (hiq : i < q) :
    (fQ t q).coeff (2 * q - (2 * i + 1)) = 0 := by
  unfold fQ
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - (2 * i + 1) = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - (2 * i + 1) = 2 * q + 2 * (2 * Sec3H.T t + r)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if 2 * q - (2 * i + 1) = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : 2 * q - (2 * i + 1) = 2 * q - 2 * (2 * Sec3H.T t + r)
    · exfalso
      have hTr : 2 * Sec3H.T t + r ≤ q := twoT_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fC_odd_minus_zero (s q t : ℕ) (i : ℕ) (hiq : i < q) :
    (fC s q t).coeff (2 * q - (2 * i + 1)) = 0 := by
  unfold fC
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q - (2 * i + 1) = 2 * q + 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : 2 * q - (2 * i + 1) = 2 * q + 2 * j'
    · exfalso
      have h1 : 1 ≤ j' := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj').1).1
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if 2 * q - (2 * i + 1) = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : 2 * q - (2 * i + 1) = 2 * q - 2 * j'
    · exfalso
      have h2 : j' ≤ q := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj').1).2
      have hqi : 2 * i + 1 ≤ 2 * q := by omega
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num



/-! ### coefficient of `fD` at odd targets -/

lemma coeff_fD_odd_plus (q : ℕ) (eps : Fin q → ℝ) (i : ℕ) (hiq : i < q) :
    (fD q eps).coeff (2 * q + (2 * i + 1)) = (eps (⟨i, hiq⟩ : Fin q) : ℂ) := by
  unfold fD
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum2 : (∑ i0 : Fin q,
        if 2 * q + (2 * i + 1) = 2 * q - (2 * i0.1 + 1) then (eps i0 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i0 hi0
    by_cases hc : 2 * q + (2 * i + 1) = 2 * q - (2 * i0.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum1 : (∑ i0 : Fin q,
        if 2 * q + (2 * i + 1) = 2 * q + (2 * i0.1 + 1) then (eps i0 : ℂ) else 0)
        = (eps (⟨i, hiq⟩ : Fin q) : ℂ) := by
    have hsum0 : (∑ i0 : Fin q,
        if 2 * q + (2 * i + 1) = 2 * q + (2 * i0.1 + 1) then (eps i0 : ℂ) else 0)
        = (if 2 * q + (2 * i + 1) = 2 * q + (2 * ((⟨i, hiq⟩ : Fin q)).1 + 1) then (eps (⟨i, hiq⟩ : Fin q) : ℂ) else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun i0 => if 2 * q + (2 * i + 1) = 2 * q + (2 * i0.1 + 1) then (eps i0 : ℂ) else 0) ⟨i, hiq⟩ ?_ ?_
      · simp
      · intro b hb hbne
        by_cases hc : 2 * q + (2 * i + 1) = 2 * q + (2 * b.1 + 1)
        · have hbr : b.1 = i := by omega
          exfalso
          exact hbne (Fin.ext hbr)
        · rw [if_neg hc]
    simpa using hsum0
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fD_odd_minus (q : ℕ) (eps : Fin q → ℝ) (i : ℕ) (hiq : i < q) :
    (fD q eps).coeff (2 * q - (2 * i + 1)) = - (eps (⟨i, hiq⟩ : Fin q) : ℂ) := by
  unfold fD
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ i0 : Fin q,
        if 2 * q - (2 * i + 1) = 2 * q + (2 * i0.1 + 1) then (eps i0 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i0 hi0
    by_cases hc : 2 * q - (2 * i + 1) = 2 * q + (2 * i0.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ i0 : Fin q,
        if 2 * q - (2 * i + 1) = 2 * q - (2 * i0.1 + 1) then (eps i0 : ℂ) else 0)
        = (eps (⟨i, hiq⟩ : Fin q) : ℂ) := by
    have hsum0 : (∑ i0 : Fin q,
        if 2 * q - (2 * i + 1) = 2 * q - (2 * i0.1 + 1) then (eps i0 : ℂ) else 0)
        = (if 2 * q - (2 * i + 1) = 2 * q - (2 * ((⟨i, hiq⟩ : Fin q)).1 + 1) then (eps (⟨i, hiq⟩ : Fin q) : ℂ) else 0) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun i0 => if 2 * q - (2 * i + 1) = 2 * q - (2 * i0.1 + 1) then (eps i0 : ℂ) else 0) ⟨i, hiq⟩ ?_ ?_
      · simp
      · intro b hb hbne
        by_cases hc : 2 * q - (2 * i + 1) = 2 * q - (2 * b.1 + 1)
        · have hbr : b.1 = i := by omega
          exfalso
          exact hbne (Fin.ext hbr)
        · rw [if_neg hc]
    simpa using hsum0
  rw [hsum1, hsum2]
  norm_num

/-! ### coefficient of the middle monomial -/

lemma coeff_X_twoq_ne (q m : ℕ) (hne : m ≠ 2 * q) :
    (Polynomial.X ^ (2 * q) : ℂ[X]).coeff m = 0 := by
  rw [coeff_X_pow_twoq]
  simp [hne]

lemma coeff_flat_mid_value (t s q : ℕ) (eps : Fin q → ℝ) (hm : Sec3.m_t t ≤ q) :
    (flatPoly t s q eps).coeff (2 * q) = 1 := by
  rw [flatPoly_eq]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_add]
  rw [coeff_fP_mid_zero (t := t) (q := q) hm]
  rw [coeff_fQ_mid_zero (t := t) (q := q) hm]
  rw [coeff_fC_mid_zero (s := s) (q := q) (t := t)]
  rw [coeff_fD_mid_zero (q := q) (eps := eps)]
  simp [Polynomial.coeff_X_pow_self]

/-! ### assembled value at even exponents (plus and minus side) -/

lemma coeff_flat_even_plus_value (t s q : ℕ) (eps : Fin q → ℝ) (j : ℕ) (hj1 : 1 ≤ j) :
    (flatPoly t s q eps).coeff (2 * q + 2 * j) =
      (if j ∈ C1 t then (RudinShapiro.P t).coeff (j - Sec3H.T t) else 0)
    + (if j ∈ C2 t then (RudinShapiro.Q t).coeff (j - 2 * Sec3H.T t) else 0)
    + (if j ∈ (Finset.Icc 1 q) \ Cp t then (RudinShapiro.P s).coeff j else 0) := by
  rw [flatPoly_eq]
  repeat rw [Polynomial.coeff_add]
  rw [coeff_X_twoq_ne (q := q) (m := 2 * q + 2 * j) (by omega)]
  rw [coeff_fP_even_plus (t := t) (q := q) (j := j) hj1]
  rw [coeff_fQ_even_plus (t := t) (q := q) (j := j) hj1]
  rw [coeff_fC_even_plus (s := s) (q := q) (t := t) (j := j) hj1]
  rw [coeff_fD_even_plus_zero (q := q) (j := j) (eps := eps) hj1]
  simp [add_assoc]

lemma coeff_flat_even_minus_value (t s q : ℕ) (eps : Fin q → ℝ) (hm : Sec3.m_t t ≤ q)
    (j : ℕ) (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (flatPoly t s q eps).coeff (2 * q - 2 * j) =
      (if j ∈ C1 t then (RudinShapiro.P t).coeff (j - Sec3H.T t) else 0)
    + (if j ∈ C2 t then (RudinShapiro.Q t).coeff (j - 2 * Sec3H.T t) else 0)
    + (if j ∈ (Finset.Icc 1 q) \ Cp t then - (RudinShapiro.P s).coeff j else 0) := by
  rw [flatPoly_eq]
  repeat rw [Polynomial.coeff_add]
  rw [coeff_X_twoq_ne (q := q) (m := 2 * q - 2 * j) (by omega)]
  rw [coeff_fP_even_minus (t := t) (q := q) hm (j := j) hj1 hjq]
  rw [coeff_fQ_even_minus (t := t) (q := q) hm (j := j) hj1 hjq]
  rw [coeff_fC_even_minus (s := s) (q := q) (t := t) (j := j) hj1 hjq]
  rw [coeff_fD_even_minus_zero (q := q) (j := j) (eps := eps) hj1]
  simp [add_assoc]



lemma mem_Icc1q (j q : ℕ) (hj1 : 1 ≤ j) (hjq : j ≤ q) : j ∈ Finset.Icc 1 q := by
  rw [Finset.mem_Icc]
  exact ⟨hj1, hjq⟩

/-! ### value at odd exponents (assembled) -/

lemma coeff_flat_odd_plus_value (t s q : ℕ) (eps : Fin q → ℝ) (hm : Sec3.m_t t ≤ q)
    (i : ℕ) (hiq : i < q) :
    (flatPoly t s q eps).coeff (2 * q + (2 * i + 1)) = (eps (⟨i, hiq⟩ : Fin q) : ℂ) := by
  rw [flatPoly_eq]
  repeat rw [Polynomial.coeff_add]
  rw [coeff_X_twoq_ne (q := q) (m := 2 * q + (2 * i + 1)) (by omega)]
  rw [coeff_fP_odd_plus_zero (t := t) (q := q) hm (i := i) hiq]
  rw [coeff_fQ_odd_plus_zero (t := t) (q := q) hm (i := i) hiq]
  rw [coeff_fC_odd_plus_zero (s := s) (q := q) (t := t) (i := i) hiq]
  rw [coeff_fD_odd_plus (q := q) (eps := eps) (i := i) hiq]
  simp

lemma coeff_flat_odd_minus_value (t s q : ℕ) (eps : Fin q → ℝ) (hm : Sec3.m_t t ≤ q)
    (i : ℕ) (hiq : i < q) :
    (flatPoly t s q eps).coeff (2 * q - (2 * i + 1)) = - (eps (⟨i, hiq⟩ : Fin q) : ℂ) := by
  rw [flatPoly_eq]
  repeat rw [Polynomial.coeff_add]
  rw [coeff_X_twoq_ne (q := q) (m := 2 * q - (2 * i + 1)) (by omega)]
  rw [coeff_fP_odd_minus_zero (t := t) (q := q) hm (i := i) hiq]
  rw [coeff_fQ_odd_minus_zero (t := t) (q := q) hm (i := i) hiq]
  rw [coeff_fC_odd_minus_zero (s := s) (q := q) (t := t) (i := i) hiq]
  rw [coeff_fD_odd_minus (q := q) (eps := eps) (i := i) hiq]
  simp

/-! ### coefficients are `±1` -/

lemma flat_coeff_mid_mem (t s q : ℕ) (eps : Fin q → ℝ) (hm : Sec3.m_t t ≤ q) :
    (flatPoly t s q eps).coeff (2 * q) = 1 ∨ (flatPoly t s q eps).coeff (2 * q) = -1 := by
  left
  exact coeff_flat_mid_value t s q eps hm

lemma flat_coeff_even_plus_mem (t s q : ℕ) (eps : Fin q → ℝ) (hcol : S5.IsColoring eps)
    (hsq : q + 1 ≤ 2 ^ s) (j : ℕ) (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (flatPoly t s q eps).coeff (2 * q + 2 * j) = 1 ∨ (flatPoly t s q eps).coeff (2 * q + 2 * j) = -1 := by
  rw [coeff_flat_even_plus_value (t := t) (s := s) (q := q) (eps := eps) (j := j) hj1]
  by_cases h1 : j ∈ C1 t
  · have h2 : j ∉ C2 t := by
      intro hc
      exact (Finset.disjoint_left.mp (C1_disjoint_C2 t)) h1 hc
    have h3 : j ∉ (Finset.Icc 1 q) \ Cp t := by
      intro hc
      exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_left (C2 t) h1)
    simp [h1, h2, h3]
    rcases (mem_C1_iff (t := t) j).mp h1 with ⟨r0, hr0lt, hr0eq⟩
    have hr : j - Sec3H.T t < 2 ^ t := by
      have : j - Sec3H.T t = r0 := by omega
      rw [this]
      exact hr0lt
    rcases RudinShapiro.P_coeff_mem t (j - Sec3H.T t) hr with h | h
    · left
      exact h
    · right
      exact h
  · by_cases h2 : j ∈ C2 t
    · have h3 : j ∉ (Finset.Icc 1 q) \ Cp t := by
        intro hc
        exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_right (C1 t) h2)
      simp [h1, h2, h3]
      rcases (mem_C2_iff (t := t) j).mp h2 with ⟨r0, hr0lt, hr0eq⟩
      have hr : j - 2 * Sec3H.T t < 2 ^ t := by
        have : j - 2 * Sec3H.T t = r0 := by omega
        rw [this]
        exact hr0lt
      rcases RudinShapiro.Q_coeff_mem t (j - 2 * Sec3H.T t) hr with h | h
      · left
        exact h
      · right
        exact h
    · have h3 : j ∈ (Finset.Icc 1 q) \ Cp t := by
        rw [Finset.mem_sdiff]
        constructor
        · exact mem_Icc1q j q hj1 hjq
        · intro hcp
          rcases Finset.mem_union.mp hcp with hc1 | hc2
          · exact h1 hc1
          · exact h2 hc2
      simp [h1, h2, h3]
      have hjs : j < 2 ^ s := by omega
      rcases RudinShapiro.P_coeff_mem s j hjs with h | h
      · left
        exact h
      · right
        exact h

lemma flat_coeff_even_minus_mem (t s q : ℕ) (eps : Fin q → ℝ) (hcol : S5.IsColoring eps)
    (hsq : q + 1 ≤ 2 ^ s) (hm : Sec3.m_t t ≤ q) (j : ℕ) (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (flatPoly t s q eps).coeff (2 * q - 2 * j) = 1 ∨ (flatPoly t s q eps).coeff (2 * q - 2 * j) = -1 := by
  rw [coeff_flat_even_minus_value (t := t) (s := s) (q := q) (eps := eps) hm (j := j) hj1 hjq]
  by_cases h1 : j ∈ C1 t
  · have h2 : j ∉ C2 t := by
      intro hc
      exact (Finset.disjoint_left.mp (C1_disjoint_C2 t)) h1 hc
    have h3 : j ∉ (Finset.Icc 1 q) \ Cp t := by
      intro hc
      exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_left (C2 t) h1)
    simp [h1, h2, h3]
    rcases (mem_C1_iff (t := t) j).mp h1 with ⟨r0, hr0lt, hr0eq⟩
    have hr : j - Sec3H.T t < 2 ^ t := by
      have : j - Sec3H.T t = r0 := by omega
      rw [this]
      exact hr0lt
    rcases RudinShapiro.P_coeff_mem t (j - Sec3H.T t) hr with h | h
    · left
      exact h
    · right
      exact h
  · by_cases h2 : j ∈ C2 t
    · have h3 : j ∉ (Finset.Icc 1 q) \ Cp t := by
        intro hc
        exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_right (C1 t) h2)
      simp [h1, h2, h3]
      rcases (mem_C2_iff (t := t) j).mp h2 with ⟨r0, hr0lt, hr0eq⟩
      have hr : j - 2 * Sec3H.T t < 2 ^ t := by
        have : j - 2 * Sec3H.T t = r0 := by omega
        rw [this]
        exact hr0lt
      rcases RudinShapiro.Q_coeff_mem t (j - 2 * Sec3H.T t) hr with h | h
      · left
        exact h
      · right
        exact h
    · have h3 : j ∈ (Finset.Icc 1 q) \ Cp t := by
        rw [Finset.mem_sdiff]
        constructor
        · exact mem_Icc1q j q hj1 hjq
        · intro hcp
          rcases Finset.mem_union.mp hcp with hc1 | hc2
          · exact h1 hc1
          · exact h2 hc2
      simp [h1, h2, h3]
      have hjs : j < 2 ^ s := by omega
      rcases RudinShapiro.P_coeff_mem s j hjs with h | h
      · right
        simpa [h]
      · left
        simpa [h]

lemma flat_coeff_odd_plus_mem (t s q : ℕ) (eps : Fin q → ℝ) (hcol : S5.IsColoring eps)
    (hm : Sec3.m_t t ≤ q) (i : ℕ) (hiq : i < q) :
    (flatPoly t s q eps).coeff (2 * q + (2 * i + 1)) = 1 ∨
      (flatPoly t s q eps).coeff (2 * q + (2 * i + 1)) = -1 := by
  rw [coeff_flat_odd_plus_value (t := t) (s := s) (q := q) (eps := eps) hm (i := i) hiq]
  rcases hcol (⟨i, hiq⟩ : Fin q) with h | h
  · left
    simpa [h]
  · right
    simpa [h]

lemma flat_coeff_odd_minus_mem (t s q : ℕ) (eps : Fin q → ℝ) (hcol : S5.IsColoring eps)
    (hm : Sec3.m_t t ≤ q) (i : ℕ) (hiq : i < q) :
    (flatPoly t s q eps).coeff (2 * q - (2 * i + 1)) = 1 ∨
      (flatPoly t s q eps).coeff (2 * q - (2 * i + 1)) = -1 := by
  rw [coeff_flat_odd_minus_value (t := t) (s := s) (q := q) (eps := eps) hm (i := i) hiq]
  rcases hcol (⟨i, hiq⟩ : Fin q) with h | h
  · right
    simpa [h]
  · left
    simpa [h]



/-! ### coefficients vanish above `4q`; degree -/

lemma coeff_fP_gt4q_zero (t q m : ℕ) (hm : Sec3.m_t t ≤ q) (hm4 : 4 * q < m) :
    (fP t q).coeff m = 0 := by
  unfold fP
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if m = 2 * q + 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : m = 2 * q + 2 * (Sec3H.T t + r)
    · exfalso
      have hTr : Sec3H.T t + r ≤ q := T_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if m = 2 * q - 2 * (Sec3H.T t + r) then (RudinShapiro.P t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : m = 2 * q - 2 * (Sec3H.T t + r)
    · exfalso
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fQ_gt4q_zero (t q m : ℕ) (hm : Sec3.m_t t ≤ q) (hm4 : 4 * q < m) :
    (fQ t q).coeff m = 0 := by
  unfold fQ
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_add_X_pow]
  rw [Finset.sum_add_distrib]
  have hsum1 : (∑ r ∈ Finset.range (2 ^ t),
        if m = 2 * q + 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : m = 2 * q + 2 * (2 * Sec3H.T t + r)
    · exfalso
      have hTr : 2 * Sec3H.T t + r ≤ q := twoT_add_r_le_q hm r (Finset.mem_range.mp hr)
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ r ∈ Finset.range (2 ^ t),
        if m = 2 * q - 2 * (2 * Sec3H.T t + r) then (RudinShapiro.Q t).coeff r else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hc : m = 2 * q - 2 * (2 * Sec3H.T t + r)
    · exfalso
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fC_gt4q_zero (s q t m : ℕ) (hm4 : 4 * q < m) :
    (fC s q t).coeff m = 0 := by
  unfold fC
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if m = 2 * q + 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : m = 2 * q + 2 * j'
    · exfalso
      have h2 : j' ≤ q := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hj').1).2
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ j' ∈ (Finset.Icc 1 q) \ Cp t,
        if m = 2 * q - 2 * j' then (RudinShapiro.P s).coeff j' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j' hj'
    by_cases hc : m = 2 * q - 2 * j'
    · exfalso
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_fD_gt4q_zero (q m : ℕ) (eps : Fin q → ℝ) (hm4 : 4 * q < m) :
    (fD q eps).coeff m = 0 := by
  unfold fD
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_sub_X_pow]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (∑ i : Fin q,
        if m = 2 * q + (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : m = 2 * q + (2 * i.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  have hsum2 : (∑ i : Fin q,
        if m = 2 * q - (2 * i.1 + 1) then (eps i : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : m = 2 * q - (2 * i.1 + 1)
    · exfalso
      omega
    · rw [if_neg hc]
  rw [hsum1, hsum2]
  norm_num

lemma coeff_flat_gt4q_zero (t s q : ℕ) (eps : Fin q → ℝ) (hm : Sec3.m_t t ≤ q)
    {m : ℕ} (hm4 : 4 * q < m) :
    (flatPoly t s q eps).coeff m = 0 := by
  rw [flatPoly_eq]
  repeat rw [Polynomial.coeff_add]
  rw [coeff_X_twoq_ne (q := q) (m := m) (by omega)]
  rw [coeff_fP_gt4q_zero (t := t) (q := q) (m := m) hm hm4]
  rw [coeff_fQ_gt4q_zero (t := t) (q := q) (m := m) hm hm4]
  rw [coeff_fC_gt4q_zero (s := s) (q := q) (t := t) (m := m) hm4]
  rw [coeff_fD_gt4q_zero (q := q) (m := m) (eps := eps) hm4]
  simp

lemma flat_natDegree_le (t s q : ℕ) (eps : Fin q → ℝ) (hm : Sec3.m_t t ≤ q) :
    (flatPoly t s q eps).natDegree ≤ 4 * q := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm4
  exact coeff_flat_gt4q_zero t s q eps hm hm4

lemma flat_coeff_4q_ne_zero (t s q : ℕ) (eps : Fin q → ℝ) (hcol : S5.IsColoring eps)
    (hsq : q + 1 ≤ 2 ^ s) (hm : Sec3.m_t t ≤ q) :
    (flatPoly t s q eps).coeff (4 * q) ≠ 0 := by
  have hq1 : 1 ≤ q := q_pos_of_hm hm
  rw [show 4 * q = 2 * q + 2 * q by omega]
  rcases flat_coeff_even_plus_mem t s q eps hcol hsq (j := q) hq1 (by omega) with h | h <;> simp [h]

lemma flat_natDegree_eq (t s q : ℕ) (eps : Fin q → ℝ) (hcol : S5.IsColoring eps)
    (hsq : q + 1 ≤ 2 ^ s) (hm : Sec3.m_t t ≤ q) :
    (flatPoly t s q eps).natDegree = 4 * q := by
  have hle : (flatPoly t s q eps).natDegree ≤ 4 * q := flat_natDegree_le t s q eps hm
  have hne : (flatPoly t s q eps).coeff (4 * q) ≠ 0 := flat_coeff_4q_ne_zero t s q eps hcol hsq hm
  have hge : ¬ (flatPoly t s q eps).natDegree < 4 * q := by
    intro hlt
    have hz : (flatPoly t s q eps).coeff (4 * q) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    exact hne hz
  omega

/-! ### every coefficient below `4q` is `±1` -/

lemma flat_coeff_all_mem (t s q : ℕ) (eps : Fin q → ℝ) (hcol : S5.IsColoring eps)
    (hsq : q + 1 ≤ 2 ^ s) (hm : Sec3.m_t t ≤ q) :
    ∀ m ≤ 4 * q, (flatPoly t s q eps).coeff m = 1 ∨ (flatPoly t s q eps).coeff m = -1 := by
  intro m hm4
  by_cases hm_eq : m = 2 * q
  · rw [hm_eq]
    exact flat_coeff_mid_mem t s q eps hm
  · have hm_ne : m ≠ 2 * q := hm_eq
    by_cases hgt : 2 * q < m
    · by_cases hpar : m % 2 = 0
      · let k := m / 2
        have hmk : m = 2 * k := by omega
        let j := k - q
        have hj1 : 1 ≤ j := by dsimp [j]; omega
        have hjq : j ≤ q := by dsimp [j]; omega
        have hmv : m = 2 * q + 2 * j := by dsimp [j]; omega
        rw [hmv]
        exact flat_coeff_even_plus_mem t s q eps hcol hsq (j := j) hj1 hjq
      · have hmodd : m % 2 = 1 := by omega
        let k := m / 2
        have hmk : m = 2 * k + 1 := by omega
        let i := k - q
        have hiq : i < q := by dsimp [i]; omega
        have hmv : m = 2 * q + (2 * i + 1) := by dsimp [i]; omega
        rw [hmv]
        exact flat_coeff_odd_plus_mem t s q eps hcol hm (i := i) hiq
    · have hlt : m < 2 * q := by omega
      by_cases hpar : m % 2 = 0
      · let k := m / 2
        have hmk : m = 2 * k := by omega
        let j := q - k
        have hj1 : 1 ≤ j := by dsimp [j]; omega
        have hjq : j ≤ q := by dsimp [j]; omega
        have hmv : m = 2 * q - 2 * j := by dsimp [j]; omega
        rw [hmv]
        exact flat_coeff_even_minus_mem t s q eps hcol hsq hm (j := j) hj1 hjq
      · have hmodd : m % 2 = 1 := by omega
        let k := m / 2
        have hmk : m = 2 * k + 1 := by omega
        let i := q - 1 - k
        have hiq : i < q := by dsimp [i]; omega
        have hmv : m = 2 * q - (2 * i + 1) := by dsimp [i]; omega
        rw [hmv]
        exact flat_coeff_odd_minus_mem t s q eps hcol hm (i := i) hiq

theorem flatPoly_littlewood (t s q : ℕ) (eps : Fin q → ℝ)
    (hcol : S5.IsColoring eps) (hsq : q + 1 ≤ 2 ^ s) (hm : Sec3.m_t t ≤ q) :
    IsLittlewoodPolynomial (flatPoly t s q eps) ∧
      (flatPoly t s q eps).natDegree = 4 * q := by
  constructor
  · intro i hi
    have hle : i ≤ 4 * q := by
      have hdeg := flat_natDegree_eq t s q eps hcol hsq hm
      rw [hdeg] at hi
      exact hi
    exact flat_coeff_all_mem t s q eps hcol hsq hm i hle
  · exact flat_natDegree_eq t s q eps hcol hsq hm


end Flat
end Submission
