import Mathlib
import Submission.Work.BMF.polyrel_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

open Polynomial Finset

namespace Work.BMF

/-! ## Auxiliary lemmas for the Chinese remainder property of `PolyRel` -/

lemma IntegralOn.crtConst (δ : ℝ) (c : ℤ) : IntegralOn δ (C (c : ℝ)) := by
  intro n
  exact ⟨c, by simp⟩

lemma IntegralOn.crtAdd {δ : ℝ} {γ₁ γ₂ : Polynomial ℝ} (h₁ : IntegralOn δ γ₁) (h₂ : IntegralOn δ γ₂) :
    IntegralOn δ (γ₁ + γ₂) := by
  intro n
  obtain ⟨m₁, hm₁⟩ := h₁ n
  obtain ⟨m₂, hm₂⟩ := h₂ n
  exact ⟨m₁ + m₂, by rw [Polynomial.eval_add, hm₁, hm₂]; push_cast; ring⟩

lemma IntegralOn.crtIntMulLeft (δ : ℝ) (c : ℤ) {Q : Polynomial ℝ} (h : IntegralOn δ Q) :
    IntegralOn δ (C (c : ℝ) * Q) := by
  intro n
  obtain ⟨m, hm⟩ := h n
  exact ⟨c * m, by rw [Polynomial.eval_mul, Polynomial.eval_C, hm]; push_cast; ring⟩

lemma IntegralOn.crtIntMul (δ : ℝ) (c : ℤ) {Q : Polynomial ℝ} (h : IntegralOn δ Q) :
    IntegralOn ((c : ℝ) * δ) Q := by
  intro n
  obtain ⟨m, hm⟩ := h (c * n)
  refine ⟨m, ?_⟩
  rw [← hm]
  congr 1
  push_cast
  ring

lemma IntegralOn.crtNeg {δ : ℝ} {Q : Polynomial ℝ} (h : IntegralOn δ Q) : IntegralOn δ (-Q) := by
  intro n
  obtain ⟨m, hm⟩ := h n
  exact ⟨-m, by rw [Polynomial.eval_neg, hm]; push_cast; ring⟩

/-! ### The finite-difference operator `Δ p = p(X+1) - p(X)` -/

noncomputable def DF : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
  Polynomial.taylor (1 : ℝ) - LinearMap.id

lemma DF_apply (p : Polynomial ℝ) : DF p = p.comp (X + C 1) - p := by
  simp [DF, Polynomial.taylor_apply]

lemma DF_X_pow_coeff (j n : ℕ) :
    (DF (X ^ j)).coeff n = (j.choose n : ℝ) - (if n = j then 1 else 0) := by
  rw [DF_apply, Polynomial.X_pow_comp, Polynomial.coeff_sub, Polynomial.coeff_X_add_C_pow,
    Polynomial.coeff_X_pow]
  simp

lemma DF_sum (k : ℕ) {p : Polynomial ℝ} (hp : p ∈ degreeLE ℝ k) :
    DF p = ∑ j ∈ range (k + 1), C (p.coeff j) * DF (X ^ j) := by
  have hnat : p.natDegree < k + 1 := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · have h1 : p.degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp hp
      rw [Polynomial.degree_eq_natDegree hp0] at h1
      have h2 : p.natDegree ≤ k := by exact_mod_cast h1
      omega
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' p hnat]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.C_mul', map_smul, Polynomial.C_mul']

lemma DF_mem_degreeLE {k : ℕ} {p : Polynomial ℝ} (hp : p ∈ degreeLE ℝ k) :
    DF p ∈ degreeLE ℝ (((k - 1 : ℕ) : WithBot ℕ)) := by
  rw [Polynomial.mem_degreeLE, Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  have hkm : k ≤ m := by
    have h : k - 1 < m := WithBot.coe_lt_coe.mp hm
    have h2 : (k - 1) + 1 ≤ m := Nat.succ_le_of_lt h
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; exact Nat.zero_le _
    · rw [Nat.sub_add_cancel hkpos] at h2; exact h2
  rw [DF_sum k hp, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Polynomial.coeff_C_mul, DF_X_pow_coeff]
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  rcases lt_or_eq_of_le (le_trans hjk hkm) with hlt | heq
  · rw [Nat.choose_eq_zero_of_lt hlt, if_neg (by omega)]
    simp
  · subst heq
    rw [Nat.choose_self, if_pos rfl]
    ring

lemma DF_coeff_top {k : ℕ} (hk : 1 ≤ k) {p : Polynomial ℝ} (hp : p ∈ degreeLE ℝ k) :
    (DF p).coeff (k - 1) = (k : ℝ) * p.coeff k := by
  rw [DF_sum k hp, Polynomial.finsetSum_coeff, Finset.sum_range_succ]
  have hzero : ∀ j ∈ range k, (C (p.coeff j) * DF (X ^ j)).coeff (k - 1) = 0 := by
    intro j hj
    rw [Polynomial.coeff_C_mul, DF_X_pow_coeff]
    have hj' : j ≤ k - 1 := by have := Finset.mem_range.mp hj; omega
    rcases lt_or_eq_of_le hj' with hlt | heq
    · rw [Nat.choose_eq_zero_of_lt (by omega : j < k - 1), if_neg (by omega)]
      simp
    · subst heq
      rw [Nat.choose_self, if_pos rfl]
      ring
  rw [Finset.sum_eq_zero hzero, zero_add, Polynomial.coeff_C_mul, DF_X_pow_coeff,
    if_neg (by omega : ¬ (k - 1 = k))]
  have hkk : k.choose (k - 1) = k := by
    have h := Nat.choose_symm (by omega : k - 1 ≤ k)
    rw [show k - (k - 1) = 1 by omega] at h
    rw [← h, Nat.choose_one_right]
  rw [hkk, sub_zero]
  ring

lemma DFpow_eq (k : ℕ) : ∀ (p : Polynomial ℝ), p ∈ degreeLE ℝ k →
    (DF^[k]) p = C ((k.factorial : ℝ) * p.coeff k) := by
  induction k with
  | zero =>
      intro p hp
      rw [Function.iterate_zero_apply]
      have h : p = C (p.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero (Polynomial.mem_degreeLE.mp hp)
      rw [h]
      simp
  | succ k ih =>
      intro p hp
      rw [Function.iterate_succ_apply]
      have hmem : DF p ∈ degreeLE ℝ k := by
        have h := DF_mem_degreeLE hp
        rwa [show k + 1 - 1 = k by omega] at h
      rw [ih (DF p) hmem, Polynomial.C_inj]
      have hct := DF_coeff_top (k := k + 1) (by omega) hp
      rw [show k + 1 - 1 = k by omega] at hct
      rw [hct, Nat.factorial_succ]
      push_cast
      ring

lemma binom_recur (k : ℕ) (g : ℕ → ℝ) :
    (∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * g (i + 1))
      - (∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * g i)
    = ∑ i ∈ range (k + 2), (-1 : ℝ) ^ (k + 1 - i) * ((k + 1).choose i : ℝ) * g i := by
  have hA : (∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * g (i + 1))
      = (∑ i ∈ range k, (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * g (i + 1)) + g (k + 1) := by
    rw [Finset.sum_range_succ]
    have h : (-1 : ℝ) ^ (k - k) * (k.choose k : ℝ) * g (k + 1) = g (k + 1) := by simp
    rw [h]
  have hBsum : (∑ i ∈ range k, (-1 : ℝ) ^ (k - (i + 1)) * (k.choose (i + 1) : ℝ) * g (i + 1))
      = ∑ i ∈ range k, (-1 : ℝ) ^ (k - i - 1) * (k.choose (i + 1) : ℝ) * g (i + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k - (i + 1) = k - i - 1 by omega]
  have hB : (∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * g i)
      = (-1 : ℝ) ^ k * g 0
        + ∑ i ∈ range k, (-1 : ℝ) ^ (k - i - 1) * (k.choose (i + 1) : ℝ) * g (i + 1) := by
    rw [Finset.sum_range_succ', hBsum]
    have h0 : (-1 : ℝ) ^ (k - 0) * (k.choose 0 : ℝ) * g 0 = (-1 : ℝ) ^ k * g 0 := by simp
    rw [h0]
    ring
  have hR1sum : (∑ i ∈ range (k + 1),
        (-1 : ℝ) ^ (k + 1 - (i + 1)) * ((k + 1).choose (i + 1) : ℝ) * g (i + 1))
      = (∑ i ∈ range k,
        (-1 : ℝ) ^ (k + 1 - (i + 1)) * ((k + 1).choose (i + 1) : ℝ) * g (i + 1)) + g (k + 1) := by
    rw [Finset.sum_range_succ]
    have hk : (-1 : ℝ) ^ (k + 1 - (k + 1)) * ((k + 1).choose (k + 1) : ℝ) * g (k + 1)
        = g (k + 1) := by simp
    rw [hk]
  have hR1 : (∑ i ∈ range (k + 2), (-1 : ℝ) ^ (k + 1 - i) * ((k + 1).choose i : ℝ) * g i)
      = (-1 : ℝ) ^ (k + 1) * g 0 + g (k + 1)
        + ∑ i ∈ range k, (-1 : ℝ) ^ (k + 1 - (i + 1)) * ((k + 1).choose (i + 1) : ℝ) * g (i + 1) := by
    rw [Finset.sum_range_succ', hR1sum]
    have h0 : (-1 : ℝ) ^ (k + 1 - 0) * ((k + 1).choose 0 : ℝ) * g 0
        = (-1 : ℝ) ^ (k + 1) * g 0 := by simp
    rw [h0]
    ring
  have hR2 : (∑ i ∈ range k, (-1 : ℝ) ^ (k + 1 - (i + 1)) * ((k + 1).choose (i + 1) : ℝ) * g (i + 1))
      = ∑ i ∈ range k, (-1 : ℝ) ^ (k - i) * ((k.choose i + k.choose (i + 1) : ℕ) : ℝ) * g (i + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k + 1 - (i + 1) = k - i by omega, Nat.choose_succ_succ]
  have hbc : (∑ i ∈ range k, (-1 : ℝ) ^ (k - i - 1) * (k.choose (i + 1) : ℝ) * g (i + 1))
      + (∑ i ∈ range k, (-1 : ℝ) ^ (k - i) * ((k.choose i + k.choose (i + 1) : ℕ) : ℝ) * g (i + 1))
      = ∑ i ∈ range k, (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * g (i + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    have hs : (-1 : ℝ) ^ (k - i - 1) = -((-1 : ℝ) ^ (k - i)) := by
      have h1 : k - i = (k - i - 1) + 1 := by omega
      conv_rhs => rw [h1, pow_succ]
      ring
    rw [hs]
    push_cast
    ring_nf
  have hbcrel : (∑ i ∈ range k, (-1 : ℝ) ^ (k - i - 1) * (k.choose (i + 1) : ℝ) * g (i + 1))
      = (∑ i ∈ range k, (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * g (i + 1))
        - (∑ i ∈ range k, (-1 : ℝ) ^ (k - i) * ((k.choose i + k.choose (i + 1) : ℕ) : ℝ) * g (i + 1)) := by
    linarith [hbc]
  have hsgn : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by
    rw [pow_succ]
    ring
  rw [hA, hB, hR1, hR2, hsgn, hbcrel]
  ring

lemma DFpow_eval (k : ℕ) : ∀ (p : Polynomial ℝ) (x : ℝ),
    ((DF^[k]) p).eval x
      = ∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * p.eval (x + (i : ℝ)) := by
  induction k with
  | zero =>
      intro p x
      simp
  | succ k ih =>
      intro p x
      rw [Function.iterate_succ_apply, ih (DF p) x]
      have hDF : ∀ t : ℝ, (DF p).eval t = p.eval (t + 1) - p.eval t := by
        intro t
        rw [DF_apply, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C]
      simp only [hDF, mul_sub]
      rw [Finset.sum_sub_distrib]
      have hconv : (∑ i ∈ range (k + 1),
            (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * p.eval ((x + (i : ℝ)) + 1))
          = ∑ i ∈ range (k + 1),
            (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * p.eval (x + ((i + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h : (x + (i : ℝ)) + 1 = x + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [h]
      rw [hconv]
      exact binom_recur k (fun i => p.eval (x + (i : ℝ)))

lemma factorial_coeff_int_aux (k : ℕ) (ψ : Polynomial ℝ) (hdeg : ψ ∈ degreeLE ℝ k)
    (hint : ∀ n : ℤ, ∃ m : ℤ, ψ.eval (n : ℝ) = (m : ℝ)) :
    ∃ c : ℤ, (k.factorial : ℝ) * ψ.coeff k = (c : ℝ) := by
  have h1 := DFpow_eq k ψ hdeg
  have h2 := DFpow_eval k ψ 0
  rw [h1] at h2
  simp only [Polynomial.eval_C, zero_add] at h2
  have hmin : ∀ i : ℕ, ∃ m : ℤ, ψ.eval (i : ℝ) = (m : ℝ) := by
    intro i
    obtain ⟨m, hm⟩ := hint (i : ℤ)
    exact ⟨m, by simpa using hm⟩
  choose mm hmm using hmin
  have hInt : ∃ c : ℤ,
      (∑ i ∈ range (k + 1), (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * ψ.eval (i : ℝ)) = (c : ℝ) := by
    refine ⟨∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * mm i, ?_⟩
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hmm i]
  rw [h2]
  exact hInt

/-! ### The `X ↦ cX` substitution -/

lemma coeff_comp_C_mul_X (γ : Polynomial ℝ) (c : ℝ) (n : ℕ) :
    (γ.comp (C c * X)).coeff n = γ.coeff n * c ^ n := by
  have hsum : γ.comp (C c * X)
      = ∑ j ∈ range (γ.natDegree + 1), C (γ.coeff j * c ^ j) * X ^ j := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' γ (Nat.lt_succ_self γ.natDegree)]
    rw [Polynomial.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, mul_pow,
      ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul]
  rw [hsum, Polynomial.finsetSum_coeff]
  have hterm : ∀ j : ℕ, (C (γ.coeff j * c ^ j) * X ^ j).coeff n
      = (if n = j then γ.coeff j * c ^ j else 0) := by
    intro j
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq]
  by_cases hn : n ∈ Finset.range (γ.natDegree + 1)
  · simp [hn]
  · simp only [hn, ite_false]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn), zero_mul]

lemma degree_comp_C_mul_X_le {k : ℕ} {γ : Polynomial ℝ} (hdeg : γ ∈ degreeLE ℝ k) (c : ℝ) :
    γ.comp (C c * X) ∈ degreeLE ℝ k := by
  rw [Polynomial.mem_degreeLE]
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  · rcases eq_or_ne c 0 with rfl | hc
    · rw [show C (0 : ℝ) * X = 0 by simp, Polynomial.comp_zero]
      exact le_trans Polynomial.degree_C_le (by simp)
    · have h1 : γ.degree ≤ (k : WithBot ℕ) := Polynomial.mem_degreeLE.mp hdeg
      have h2 : γ.natDegree ≤ k := by
        rw [Polynomial.degree_eq_natDegree hγ] at h1
        exact_mod_cast h1
      have h3 : (γ.comp (C c * X)).natDegree = γ.natDegree := by
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X c hc, mul_one]
      rw [← Polynomial.natDegree_le_iff_degree_le, h3]
      exact h2

/-! ### Degree-`< n` polynomials vanishing at `n` consecutive points -/

lemma eq_zero_of_degree_lt_of_eval_eq_zero {n : ℕ} {β : Polynomial ℝ} {x : ℝ}
    (hdeg : β.degree < (n : ℕ)) (h : ∀ i : ℕ, i < n → β.eval (x + (i : ℝ)) = 0) :
    β = 0 := by
  have hinj : Set.InjOn (fun i : Fin n => x + (i : ℝ))
      (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    intro i _ j _ hij
    have h2 : (i : ℝ) = (j : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast h2)
  have hcard : ((Finset.univ : Finset (Fin n)).card : WithBot ℕ) = (n : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hLag := Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin n)))
    (v := fun i : Fin n => x + (i : ℝ)) (f := β) hinj (by rw [hcard]; exact hdeg)
  rw [hLag, Lagrange.interpolate_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [h i i.isLt]
  simp

/-! ### `poly_const_of_intval` -/

lemma poly_const_of_intval : ∀ (k : ℕ) (M a L : ℝ) (δ : Polynomial ℝ),
    δ ∈ degreeLE ℝ k → 1 ≤ M →
    (∀ t ∈ Set.Icc a (a + L), |δ.eval t| ≤ M) →
    (∀ n : ℤ, (n : ℝ) ∈ Set.Icc a (a + L) → ∃ m : ℤ, δ.eval (n : ℝ) = (m : ℝ)) →
    (k : ℝ) + 1 ≤ L → (2 : ℝ) ^ k * M + ((2 : ℝ) ^ (k - 1) - 1) < L →
    ∃ c : ℤ, δ = C (c : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro M a L δ hdeg hM1 hbdd hint hL0 hL
    have hconst : δ = C (δ.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (Polynomial.mem_degreeLE.mp hdeg)
    have hn₀ : ((⌈a⌉ : ℤ) : ℝ) ∈ Set.Icc a (a + L) := by
      rw [Set.mem_Icc]
      refine ⟨Int.le_ceil a, ?_⟩
      have h1 := Int.ceil_lt_add_one a
      linarith
    obtain ⟨mm, hmm⟩ := hint ⌈a⌉ hn₀
    have hev : δ.coeff 0 = (mm : ℝ) := by
      have h2 : δ.eval ((⌈a⌉ : ℤ) : ℝ) = δ.coeff 0 := by
        conv_lhs => rw [hconst]
        rw [Polynomial.eval_C]
      rw [← h2, hmm]
    exact ⟨mm, by rw [hconst, hev]⟩
  | succ m ih =>
    intro M a L δ hdeg hM1 hbdd hint hL0 hL
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · -- target degree one
      subst hm0
      have hL2 : (2 : ℝ) ≤ L := by
        have h := hL0
        norm_num at h
        exact h
      have hlin : δ = C (δ.coeff 1) * X + C (δ.coeff 0) :=
        Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.mem_degreeLE.mp hdeg)
      have hn₀ : ((⌈a⌉ : ℤ) : ℝ) ∈ Set.Icc a (a + L) := by
        rw [Set.mem_Icc]
        refine ⟨Int.le_ceil a, ?_⟩
        have h1 := Int.ceil_lt_add_one a
        linarith
      have hn₁ : (((⌈a⌉ : ℤ) + 1 : ℤ) : ℝ) ∈ Set.Icc a (a + L) := by
        rw [Set.mem_Icc]
        refine ⟨by push_cast; linarith [Int.le_ceil a], ?_⟩
        have h1 := Int.ceil_lt_add_one a
        push_cast
        linarith
      obtain ⟨p1, hp1⟩ := hint ⌈a⌉ hn₀
      obtain ⟨p2, hp2⟩ := hint (⌈a⌉ + 1) hn₁
      have hstep : δ.eval (((⌈a⌉ : ℤ) + 1 : ℤ) : ℝ) - δ.eval ((⌈a⌉ : ℤ) : ℝ) = δ.coeff 1 := by
        conv_lhs => rw [hlin]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_sub]
        push_cast
        ring
      have hz1 : ∃ z : ℤ, δ.coeff 1 = (z : ℝ) := by
        refine ⟨p2 - p1, ?_⟩
        rw [← hstep, hp2, hp1]
        push_cast
        ring
      obtain ⟨z, hz⟩ := hz1
      have hL2M : 2 * M < L := by
        have h := hL
        norm_num at h ⊢
        linarith
      have hz0 : (z : ℝ) = 0 := by
        by_contra hzne
        have hz1' : (1 : ℝ) ≤ |(z : ℝ)| := by
          have hzne' : z ≠ 0 := fun h => hzne (by rw [h]; norm_num)
          have h : (1 : ℤ) ≤ |z| := by
            rcases lt_or_ge 0 z with hpos | hneg
            · rw [abs_of_nonneg (le_of_lt hpos)]; omega
            · rw [abs_of_nonpos hneg]; omega
          rw [← Int.cast_abs]
          exact_mod_cast h
        have hdiff : |δ.eval (a + L) - δ.eval a| = |(z : ℝ)| * L := by
          have hval : δ.eval (a + L) - δ.eval a = (z : ℝ) * L := by
            conv_lhs => rw [hlin, hz]
            simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X]
            ring
          rw [hval, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < L)]
        have hb1 : |δ.eval (a + L)| ≤ M :=
          hbdd (a + L) (by rw [Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩)
        have hb2 : |δ.eval a| ≤ M :=
          hbdd a (by rw [Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩)
        have h3 : |δ.eval (a + L) - δ.eval a| ≤ 2 * M := by
          have hab := abs_sub_le (δ.eval (a + L)) 0 (δ.eval a)
          simp only [sub_zero, zero_sub, abs_neg] at hab
          calc |δ.eval (a + L) - δ.eval a| ≤ |δ.eval (a + L)| + |δ.eval a| := hab
            _ ≤ M + M := add_le_add hb1 hb2
            _ = 2 * M := by ring
        rw [hdiff] at h3
        nlinarith [hz1', hL2M, h3]
      have hconst : δ = C (δ.coeff 0) := by
        rw [hlin, hz, hz0]
        simp
      have hev : δ.coeff 0 = (p1 : ℝ) := by
        have h2 : δ.eval ((⌈a⌉ : ℤ) : ℝ) = δ.coeff 0 := by
          conv_lhs => rw [hconst]
          rw [Polynomial.eval_C]
        rw [← h2, hp1]
      exact ⟨p1, by rw [hconst, hev]⟩
    · -- target degree at least two
      have hmem : DF δ ∈ degreeLE ℝ m := by
        have h := DF_mem_degreeLE hdeg
        rwa [show m + 1 - 1 = m by omega] at h
      have hbdd' : ∀ t ∈ Set.Icc a (a + (L - 1)), |(DF δ).eval t| ≤ 2 * M := by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [DF_apply, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C]
        calc |δ.eval (t + 1) - δ.eval t| ≤ |δ.eval (t + 1)| + |δ.eval t| := by
              have hab := abs_sub_le (δ.eval (t + 1)) 0 (δ.eval t)
              simpa using hab
          _ ≤ M + M := add_le_add
              (hbdd (t + 1) (by rw [Set.mem_Icc]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩))
              (hbdd t (by rw [Set.mem_Icc]; exact ⟨ht.1, by linarith [ht.2]⟩))
          _ = 2 * M := by ring
      have hint' : ∀ n : ℤ, (n : ℝ) ∈ Set.Icc a (a + (L - 1)) →
          ∃ z : ℤ, (DF δ).eval (n : ℝ) = (z : ℝ) := by
        intro n hn
        rw [Set.mem_Icc] at hn
        obtain ⟨m1, hm1⟩ := hint n (by rw [Set.mem_Icc]; exact ⟨hn.1, by linarith [hn.2]⟩)
        obtain ⟨m2, hm2⟩ := hint (n + 1) (by
          rw [Set.mem_Icc]
          exact ⟨by push_cast; linarith [hn.1], by push_cast; linarith [hn.2]⟩)
        refine ⟨m2 - m1, ?_⟩
        rw [DF_apply, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C]
        have hm2' : δ.eval ((n : ℝ) + 1) = (m2 : ℝ) := by
          rw [← hm2]
          congr 1
          push_cast
          ring
        rw [hm2', hm1]
        push_cast
        ring
      have hL0' : (m : ℝ) + 1 ≤ L - 1 := by
        have h := hL0
        have h' : ((m : ℝ) + 1) + 1 ≤ L := by
          rw [show ((m : ℝ) + 1) + 1 = (((m + 1 : ℕ)) : ℝ) + 1 by push_cast; ring]
          exact h
        linarith
      have hL' : (2 : ℝ) ^ m * (2 * M) + ((2 : ℝ) ^ (m - 1) - 1) < L - 1 := by
        have h := hL
        rw [show m + 1 - 1 = m by omega] at h
        have hpk : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := pow_succ 2 m
        have hkey : (2 : ℝ) ^ (m - 1) ≤ (2 : ℝ) ^ m - 1 := by
          have hpk2 : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
            rw [← pow_succ, Nat.sub_add_cancel hm]
          have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ (m - 1) := one_le_pow₀ (by norm_num)
          nlinarith [hpk2, h2m]
        nlinarith [h, hpk, hkey]
      obtain ⟨z, hz⟩ := ih (2 * M) a (L - 1) (DF δ) hmem (by linarith) hbdd' hint' hL0' hL'
      obtain ⟨n₀, hn₀⟩ : ∃ n : ℤ, (n : ℝ) ∈ Set.Icc a (a + L) := by
        refine ⟨⌈a⌉, ?_⟩
        rw [Set.mem_Icc]
        exact ⟨Int.le_ceil a, by have h1 := Int.ceil_lt_add_one a; linarith⟩
      have hshift : ∀ x : ℝ, δ.eval (x + 1) - δ.eval x = (z : ℝ) := by
        intro x
        have hh := congrArg (Polynomial.eval x) hz
        rw [DF_apply, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C] at hh
        linarith [hh]
      have hlin : ∀ i : ℕ, i ≤ m + 1 →
          δ.eval ((n₀ + i : ℤ) : ℝ) = δ.eval (n₀ : ℝ) + (z : ℝ) * (i : ℝ) := by
        intro i
        induction i with
        | zero => intro _; simp
        | succ i ih2 =>
            intro hi
            have hi' : i ≤ m + 1 := by omega
            have hcast : (((n₀ + ((i + 1 : ℕ))) : ℤ) : ℝ)
                = (((n₀ + (i : ℕ)) : ℤ) : ℝ) + 1 := by push_cast; ring
            have hstep := hshift ((((n₀ + (i : ℕ)) : ℤ)) : ℝ)
            have hstep' : δ.eval (((((n₀ + (i : ℕ)) : ℤ)) : ℝ) + 1)
                = δ.eval ((((n₀ + (i : ℕ)) : ℤ)) : ℝ) + (z : ℝ) := by linarith [hstep]
            rw [hcast, hstep', ih2 hi']
            push_cast
            ring
      have hdegβ : (δ - C (z : ℝ) * X - C (δ.eval (n₀ : ℝ) - (z : ℝ) * (n₀ : ℝ))).degree
          < (((m + 1) + 1 : ℕ) : WithBot ℕ) := by
        have hδ := Polynomial.mem_degreeLE.mp hdeg
        have hlin' : (C (z : ℝ) * X + C (δ.eval (n₀ : ℝ) - (z : ℝ) * (n₀ : ℝ))).degree
            ≤ (1 : WithBot ℕ) := by
          refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)
          · calc (C (z : ℝ) * X : Polynomial ℝ).degree
                ≤ (C (z : ℝ)).degree + (X : Polynomial ℝ).degree := Polynomial.degree_mul_le _ _
              _ ≤ 0 + 1 := by
                  rw [Polynomial.degree_X]
                  exact add_le_add Polynomial.degree_C_le le_rfl
              _ = 1 := by simp
          · exact le_trans Polynomial.degree_C_le (by simp)
        have hsub : (δ - (C (z : ℝ) * X + C (δ.eval (n₀ : ℝ) - (z : ℝ) * (n₀ : ℝ)))).degree
            ≤ max ((((m + 1 : ℕ)) : WithBot ℕ)) (1 : WithBot ℕ) :=
          Polynomial.degree_sub_le_of_le hδ hlin'
        have heq : δ - C (z : ℝ) * X - C (δ.eval (n₀ : ℝ) - (z : ℝ) * (n₀ : ℝ))
            = δ - (C (z : ℝ) * X + C (δ.eval (n₀ : ℝ) - (z : ℝ) * (n₀ : ℝ))) := by ring
        rw [heq]
        refine lt_of_le_of_lt hsub ?_
        rw [max_lt_iff]
        refine ⟨WithBot.coe_lt_coe.mpr (show m + 1 < m + 1 + 1 by omega),
          WithBot.coe_lt_coe.mpr (show 1 < m + 1 + 1 by omega)⟩
      have hβ : δ - C (z : ℝ) * X - C (δ.eval (n₀ : ℝ) - (z : ℝ) * (n₀ : ℝ)) = 0 := by
        refine eq_zero_of_degree_lt_of_eval_eq_zero (n := m + 2) (x := (n₀ : ℝ)) hdegβ ?_
        intro i hi
        have hi' : i ≤ m + 1 := by omega
        have h1 := hlin i hi'
        have hcast : ((n₀ + i : ℤ) : ℝ) = (n₀ : ℝ) + (i : ℝ) := by push_cast; ring
        rw [hcast] at h1
        rw [Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, Polynomial.eval_C, h1]
        ring
      have hδeq : δ = C (z : ℝ) * X + C (δ.eval (n₀ : ℝ) - (z : ℝ) * (n₀ : ℝ)) := by
        have h := hβ
        rw [sub_eq_zero] at h
        rw [← h]
        ring
      have hL2M : 2 * M < L := by
        have h := hL
        rw [show m + 1 - 1 = m by omega] at h
        have h2 : (4 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
          have h3 : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (m + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          norm_num at h3 ⊢
          linarith
        have h2m1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        nlinarith [h, h2, h2m1, hM1]
      have hz0 : (z : ℝ) = 0 := by
        by_contra hzne
        have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
          have hzne' : z ≠ 0 := fun h => hzne (by rw [h]; norm_num)
          have h : (1 : ℤ) ≤ |z| := by
            rcases lt_or_ge 0 z with hpos | hneg
            · rw [abs_of_nonneg (le_of_lt hpos)]; omega
            · rw [abs_of_nonpos hneg]; omega
          rw [← Int.cast_abs]
          exact_mod_cast h
        have hLpos : (0 : ℝ) < L := by
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith [hL0', hm0]
        have hdiff : |δ.eval (a + L) - δ.eval a| = |(z : ℝ)| * L := by
          have hval : δ.eval (a + L) - δ.eval a = (z : ℝ) * L := by
            conv_lhs => rw [hδeq]
            simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X]
            ring
          rw [hval, abs_mul, abs_of_pos hLpos]
        have hb1 : |δ.eval (a + L)| ≤ M :=
          hbdd (a + L) (by rw [Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩)
        have hb2 : |δ.eval a| ≤ M :=
          hbdd a (by rw [Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩)
        have h3 : |δ.eval (a + L) - δ.eval a| ≤ 2 * M := by
          have hab := abs_sub_le (δ.eval (a + L)) 0 (δ.eval a)
          simp only [sub_zero, zero_sub, abs_neg] at hab
          calc |δ.eval (a + L) - δ.eval a| ≤ |δ.eval (a + L)| + |δ.eval a| := hab
            _ ≤ M + M := add_le_add hb1 hb2
            _ = 2 * M := by ring
        rw [hdiff] at h3
        nlinarith [hz1, hL2M, h3]
      have hconst : δ = C (δ.eval (n₀ : ℝ)) := by
        rw [hδeq, hz0]
        simp
      obtain ⟨mm, hmm⟩ := hint n₀ hn₀
      exact ⟨mm, by rw [hconst, hmm]⟩


/-! ### The descending Pochhammer polynomial -/

lemma descPochhammer_eval_natCast (m s : ℕ) :
    (descPochhammer ℝ m).eval (s : ℝ) = ((s.descFactorial m : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [descPochhammer_succ_eval, ih, Nat.descFactorial_succ]
      rcases lt_or_ge s m with h | h
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.mul_zero]
        simp
      · rw [Nat.cast_mul, Nat.cast_sub h]
        ring

lemma descPochhammer_fac_dvd (m : ℕ) (t : ℤ) :
    ∃ c : ℤ, (descPochhammer ℝ m).eval (t : ℝ) = (m.factorial : ℝ) * (c : ℝ) := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    exact ⟨1, by simp⟩
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    rcases lt_or_ge t 0 with ht | ht
    · -- t < 0
      obtain ⟨r, hr⟩ : ∃ r : ℕ, t = -((r : ℤ)) := ⟨(-t).toNat, by
        have h : (0 : ℤ) ≤ -t := by omega
        have h2 : ((((-t).toNat : ℕ)) : ℤ) = -t := Int.toNat_of_nonneg h
        omega⟩
      have key : (descPochhammer ℝ m).eval (-(r : ℝ))
          = (-1 : ℝ) ^ m * ((r.ascFactorial m : ℕ) : ℝ) := by
        have hcast : (ascPochhammer ℝ m).eval (r : ℝ) = ((r.ascFactorial m : ℕ) : ℝ) :=
          (Nat.cast_ascFactorial (S := ℝ) (a := r) (b := m)).symm
        have hneg := ascPochhammer_eval_neg_eq_descPochhammer (R := ℝ) (-(r : ℝ)) m
        rw [neg_neg] at hneg
        have h1 : (-1 : ℝ) ^ m * (descPochhammer ℝ m).eval (-(r : ℝ))
            = ((r.ascFactorial m : ℕ) : ℝ) := by rw [← hneg, hcast]
        have h2 : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
          rw [← mul_pow]; norm_num
        calc (descPochhammer ℝ m).eval (-(r : ℝ))
            = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * (descPochhammer ℝ m).eval (-(r : ℝ)) := by
              rw [h2, one_mul]
          _ = (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m * (descPochhammer ℝ m).eval (-(r : ℝ))) := by ring
          _ = (-1 : ℝ) ^ m * ((r.ascFactorial m : ℕ) : ℝ) := by rw [h1]
      refine ⟨(-1 : ℤ) ^ m * ((r + m - 1).choose m : ℤ), ?_⟩
      rw [hr]
      have hcast2 : ((((-(r : ℤ)) : ℤ)) : ℝ) = -(r : ℝ) := by push_cast; ring
      rw [hcast2, key, Nat.ascFactorial_eq_factorial_mul_choose']
      push_cast
      ring
    · -- 0 ≤ t
      obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = (s : ℤ) := ⟨t.toNat, (Int.toNat_of_nonneg ht).symm⟩
      refine ⟨(s.choose m : ℤ), ?_⟩
      rw [show (((s : ℤ)) : ℝ) = (s : ℝ) by norm_cast]
      rw [descPochhammer_eval_natCast, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      ring

lemma descPochhammer_comp_natDegree_le (m : ℕ) (c : ℝ) :
    ((descPochhammer ℝ m).comp (C c * X)).natDegree ≤ m := by
  calc ((descPochhammer ℝ m).comp (C c * X)).natDegree
      ≤ (descPochhammer ℝ m).natDegree * (C c * X).natDegree := Polynomial.natDegree_comp_le
    _ ≤ m * 1 := by
        refine Nat.mul_le_mul (le_of_eq (descPochhammer_natDegree ℝ m)) ?_
        calc (C c * X : Polynomial ℝ).natDegree
            ≤ (C c).natDegree + (X : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
          _ ≤ 0 + 1 := by
              simp [Polynomial.natDegree_X, Polynomial.natDegree_C]
          _ = 1 := by simp
    _ = m := by simp

lemma descPochhammer_comp_coeff {m : ℕ} {c : ℝ} (hc : c ≠ 0) :
    ((descPochhammer ℝ m).comp (C c * X)).coeff m = c ^ m := by
  have hnd : (C c * X : Polynomial ℝ).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul_X c hc]
    norm_num
  have h := Polynomial.coeff_comp_degree_mul_degree
    (p := descPochhammer ℝ m) (q := (C c * X : Polynomial ℝ)) hnd
  rw [Polynomial.natDegree_C_mul_X c hc, mul_one, descPochhammer_natDegree ℝ] at h
  rw [h, show (descPochhammer ℝ m).leadingCoeff = 1 from monic_descPochhammer ℝ m, one_mul,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, mul_one]

/-! ### The two-element lattice Chinese remainder theorem -/

lemma prod_primes_ne_zero {S : Finset ℕ} (h : ∀ p ∈ S, p.Prime) : S.prod (fun p => p) ≠ 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T _ ih =>
      rw [Finset.prod_insert ‹a ∉ T›]
      exact mul_ne_zero (h a (Finset.mem_insert_self a T)).ne_zero
        (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

theorem integralOn_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    ∀ (k : ℕ) (γ : Polynomial ℝ), γ ∈ degreeLE ℝ k →
      IntegralOn (1 / (a : ℝ)) γ → IntegralOn (1 / (b : ℝ)) γ →
      IntegralOn (1 / ((a * b : ℕ) : ℝ)) γ := by
  intro k
  induction k with
  | zero =>
    intro γ hdeg h₁ h₂
    have hconst : γ = C (γ.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (Polynomial.mem_degreeLE.mp hdeg)
    obtain ⟨m, hm⟩ := h₁ 0
    have hm' : γ.eval (0 : ℝ) = (m : ℝ) := by simpa using hm
    have hc : γ.coeff 0 = (m : ℝ) := by
      have h2 : γ.eval (0 : ℝ) = γ.coeff 0 := by
        conv_lhs => rw [hconst]
        rw [Polynomial.eval_C]
      rw [← h2, hm']
    rw [hconst, hc]
    exact IntegralOn.crtConst _ m
  | succ k ih =>
    intro γ hdeg h₁ h₂
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hcc0 : ((a * b : ℕ) : ℝ) ≠ 0 := by
      have h : a * b ≠ 0 := mul_ne_zero ha hb
      exact_mod_cast h
    set N : ℕ := k + 1 with hN
    have hdega : γ.comp (C (1 / (a : ℝ)) * X) ∈ degreeLE ℝ N := degree_comp_C_mul_X_le hdeg _
    have hinta : ∀ n : ℤ, ∃ m : ℤ, (γ.comp (C (1 / (a : ℝ)) * X)).eval (n : ℝ) = (m : ℝ) := by
      intro n
      obtain ⟨m, hm⟩ := h₁ n
      exact ⟨m, by
        rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        exact hm⟩
    obtain ⟨c₁, hc₁⟩ := factorial_coeff_int_aux N (γ.comp (C (1 / (a : ℝ)) * X)) hdega hinta
    have hdegb : γ.comp (C (1 / (b : ℝ)) * X) ∈ degreeLE ℝ N := degree_comp_C_mul_X_le hdeg _
    have hintb : ∀ n : ℤ, ∃ m : ℤ, (γ.comp (C (1 / (b : ℝ)) * X)).eval (n : ℝ) = (m : ℝ) := by
      intro n
      obtain ⟨m, hm⟩ := h₂ n
      exact ⟨m, by
        rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        exact hm⟩
    obtain ⟨c₂, hc₂⟩ := factorial_coeff_int_aux N (γ.comp (C (1 / (b : ℝ)) * X)) hdegb hintb
    have hkeya : ((N.factorial : ℝ)) * γ.coeff N = (c₁ : ℝ) * (a : ℝ) ^ N := by
      have hmul : ((N.factorial : ℝ)) * (γ.comp (C (1 / (a : ℝ)) * X)).coeff N * (a : ℝ) ^ N
          = (c₁ : ℝ) * (a : ℝ) ^ N := by rw [hc₁]
      rw [coeff_comp_C_mul_X, one_div, inv_pow] at hmul
      have haN : (a : ℝ) ^ N ≠ 0 := pow_ne_zero N haR
      have hsimp : ((N.factorial : ℝ)) * (γ.coeff N * ((a : ℝ) ^ N)⁻¹) * (a : ℝ) ^ N
          = ((N.factorial : ℝ)) * γ.coeff N := by field_simp
      rwa [hsimp] at hmul
    have hkeyb : ((N.factorial : ℝ)) * γ.coeff N = (c₂ : ℝ) * (b : ℝ) ^ N := by
      have hmul : ((N.factorial : ℝ)) * (γ.comp (C (1 / (b : ℝ)) * X)).coeff N * (b : ℝ) ^ N
          = (c₂ : ℝ) * (b : ℝ) ^ N := by rw [hc₂]
      rw [coeff_comp_C_mul_X, one_div, inv_pow] at hmul
      have hbN : (b : ℝ) ^ N ≠ 0 := pow_ne_zero N hbR
      have hsimp : ((N.factorial : ℝ)) * (γ.coeff N * ((b : ℝ) ^ N)⁻¹) * (b : ℝ) ^ N
          = ((N.factorial : ℝ)) * γ.coeff N := by field_simp
      rwa [hsimp] at hmul
    have hAeq : ((c₁ * (a : ℤ) ^ N : ℤ) : ℝ) = ((N.factorial : ℝ)) * γ.coeff N := by
      rw [hkeya]; push_cast; ring
    have hBeq : ((c₂ * (b : ℤ) ^ N : ℤ) : ℝ) = ((N.factorial : ℝ)) * γ.coeff N := by
      rw [hkeyb]; push_cast; ring
    have hAB : c₁ * (a : ℤ) ^ N = c₂ * (b : ℤ) ^ N := by
      have hh : ((c₁ * (a : ℤ) ^ N : ℤ) : ℝ) = ((c₂ * (b : ℤ) ^ N : ℤ) : ℝ) := by rw [hAeq, hBeq]
      exact_mod_cast hh
    have hcopab : IsCoprime ((a : ℤ) ^ N) ((b : ℤ) ^ N) :=
      (Nat.isCoprime_iff_coprime.mpr hab).pow
    have hdvd : ((a * b : ℕ) : ℤ) ^ N ∣ c₁ * (a : ℤ) ^ N := by
      have h1 : (a : ℤ) ^ N ∣ c₁ * (a : ℤ) ^ N := ⟨c₁, by ring⟩
      have h2 : (b : ℤ) ^ N ∣ c₁ * (a : ℤ) ^ N := ⟨c₂, by rw [hAB]; ring⟩
      have h3 := hcopab.mul_dvd h1 h2
      have h4 : ((a : ℤ) * (b : ℤ)) = ((a * b : ℕ) : ℤ) := by push_cast; ring
      rwa [← mul_pow, h4] at h3
    obtain ⟨c, hc⟩ := hdvd
    set cc : ℝ := ((a * b : ℕ) : ℝ) with hccdef
    have hcc0' : cc ≠ 0 := by rw [hccdef]; exact hcc0
    set Q : Polynomial ℝ := C (1 / ((N.factorial : ℝ))) * (descPochhammer ℝ N).comp (C cc * X)
      with hQdef
    have hQdeg : Q ∈ degreeLE ℝ N := by
      rw [hQdef, Polynomial.mem_degreeLE, ← Polynomial.natDegree_le_iff_degree_le]
      calc (C (1 / ((N.factorial : ℝ))) * (descPochhammer ℝ N).comp (C cc * X)).natDegree
          ≤ (C (1 / ((N.factorial : ℝ)))).natDegree
            + ((descPochhammer ℝ N).comp (C cc * X)).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 0 + N := add_le_add (le_of_eq (Polynomial.natDegree_C _))
              (descPochhammer_comp_natDegree_le N cc)
        _ = N := by simp
    have hQcoeff : Q.coeff N = cc ^ N * (1 / ((N.factorial : ℝ))) := by
      rw [hQdef, Polynomial.coeff_C_mul, descPochhammer_comp_coeff hcc0']
      ring
    have hQint : IntegralOn (1 / cc) Q := by
      intro n
      obtain ⟨z, hz⟩ := descPochhammer_fac_dvd N n
      refine ⟨z, ?_⟩
      rw [hQdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      have harg : cc * ((1 / cc) * (n : ℝ)) = (n : ℝ) := by
        rw [one_div, ← mul_assoc, mul_inv_cancel₀ hcc0', one_mul]
      rw [harg, hz]
      have hfac : ((N.factorial : ℝ)) ≠ 0 := by positivity
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]
    have hQa : IntegralOn (1 / (a : ℝ)) Q := by
      have h := IntegralOn.crtIntMul (1 / cc) (b : ℤ) hQint
      have heq : ((b : ℤ) : ℝ) * (1 / cc) = 1 / (a : ℝ) := by
        rw [hccdef, one_div, one_div]
        push_cast
        field_simp
      rwa [heq] at h
    have hQb : IntegralOn (1 / (b : ℝ)) Q := by
      have h := IntegralOn.crtIntMul (1 / cc) (a : ℤ) hQint
      have heq : ((a : ℤ) : ℝ) * (1 / cc) = 1 / (b : ℝ) := by
        rw [hccdef, one_div, one_div]
        push_cast
        field_simp
      rwa [heq] at h
    have hkey : ((N.factorial : ℝ)) * γ.coeff N = (c : ℝ) * cc ^ N := by
      rw [← hAeq, hc, hccdef]
      push_cast
      ring
    have hγ'coeff : (γ - C (c : ℝ) * Q).coeff N = 0 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hQcoeff]
      have hfac : ((N.factorial : ℝ)) ≠ 0 := by positivity
      have hcN : γ.coeff N = (c : ℝ) * (cc ^ N * (1 / ((N.factorial : ℝ)))) := by
        have hh : γ.coeff N * ((N.factorial : ℝ))
            = (c : ℝ) * (cc ^ N * (1 / ((N.factorial : ℝ)))) * ((N.factorial : ℝ)) := by
          rw [show (c : ℝ) * (cc ^ N * (1 / ((N.factorial : ℝ)))) * ((N.factorial : ℝ))
              = (c : ℝ) * cc ^ N by field_simp]
          rw [mul_comm, hkey]
        exact mul_right_cancel₀ hfac hh
      rw [hcN]
      ring
    have hγ'deg : γ - C (c : ℝ) * Q ∈ degreeLE ℝ k := by
      rw [Polynomial.mem_degreeLE, Polynomial.degree_le_iff_coeff_zero]
      intro m hm
      have hmk : k < m := WithBot.coe_lt_coe.mp hm
      rcases eq_or_lt_of_le (show k + 1 ≤ m by omega) with hm1 | hm2
      · rw [show m = N by omega]
        exact hγ'coeff
      · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        have hγ0 : γ.coeff m = 0 :=
          Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_le_of_lt (Polynomial.mem_degreeLE.mp hdeg) (WithBot.coe_lt_coe.mpr (by omega)))
        have hQ0 : Q.coeff m = 0 :=
          Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_le_of_lt (Polynomial.mem_degreeLE.mp hQdeg) (WithBot.coe_lt_coe.mpr (by omega)))
        rw [hγ0, hQ0, mul_zero, sub_zero]
    have hγ'a : IntegralOn (1 / (a : ℝ)) (γ - C (c : ℝ) * Q) := by
      have hneg : IntegralOn (1 / (a : ℝ)) (-(C (c : ℝ) * Q)) :=
        (IntegralOn.crtIntMulLeft (1 / (a : ℝ)) c (Q := Q) hQa).neg
      have h := IntegralOn.crtAdd h₁ hneg
      rwa [show γ + -(C (c : ℝ) * Q) = γ - C (c : ℝ) * Q by ring] at h
    have hγ'b : IntegralOn (1 / (b : ℝ)) (γ - C (c : ℝ) * Q) := by
      have hneg : IntegralOn (1 / (b : ℝ)) (-(C (c : ℝ) * Q)) :=
        (IntegralOn.crtIntMulLeft (1 / (b : ℝ)) c (Q := Q) hQb).neg
      have h := IntegralOn.crtAdd h₂ hneg
      rwa [show γ + -(C (c : ℝ) * Q) = γ - C (c : ℝ) * Q by ring] at h
    have hfinal : IntegralOn (1 / cc) γ := by
      have h := IntegralOn.crtAdd (ih (γ - C (c : ℝ) * Q) hγ'deg hγ'a hγ'b)
        (IntegralOn.crtIntMulLeft (1 / cc) c (Q := Q) hQint)
      rwa [show (γ - C (c : ℝ) * Q) + C (c : ℝ) * Q = γ by ring] at h
    rwa [show cc = ((a * b : ℕ) : ℝ) from hccdef] at hfinal

/-! ### Iterating the two-element theorem over a finite set of primes -/

lemma integralOn_prod_primes {k : ℕ} {γ : Polynomial ℝ} (hdeg : γ ∈ degreeLE ℝ k) :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, IntegralOn (1 / (p : ℝ)) γ) →
      S.Nonempty → IntegralOn (1 / ((S.prod (fun p => p) : ℕ) : ℝ)) γ := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _ _ hS
      obtain ⟨p, hp⟩ := hS
      exact absurd hp (by simp)
  | insert a T ha ih =>
      intro hprime h hS
      rw [Finset.prod_insert ha]
      rcases T.eq_empty_or_nonempty with hE | hne
      · subst hE
        rw [Finset.prod_empty, mul_one]
        exact h a (Finset.mem_insert_self a ∅)
      · have hpr : ∀ p ∈ T, p.Prime := fun p hp => hprime p (Finset.mem_insert_of_mem hp)
        have hh : ∀ p ∈ T, IntegralOn (1 / (p : ℝ)) γ :=
          fun p hp => h p (Finset.mem_insert_of_mem hp)
        have ih' := ih hpr hh hne
        have hap : a.Prime := hprime a (Finset.mem_insert_self a T)
        have hb0 : T.prod (fun p => p) ≠ 0 := prod_primes_ne_zero hpr
        have hcop : a.Coprime (T.prod (fun p => p)) := by
          rw [Nat.coprime_prod_right_iff]
          intro b hbT
          rw [Nat.coprime_primes hap (hpr b hbT)]
          intro hab
          rw [← hab] at hbT
          exact ha hbT
        have h1 : IntegralOn (1 / (a : ℝ)) γ := h a (Finset.mem_insert_self a T)
        exact integralOn_coprime hap.ne_zero hb0 hcop k γ hdeg h1 ih'

/-! ### Arithmetic for the main theorem -/

lemma crt_len_ge {k : ℕ} {C L : ℝ} (h2C : 1 ≤ 2 * C)
    (hbig : 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) < L) :
    (k : ℝ) + 1 ≤ L := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) ^ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · exact one_le_pow₀ (by exact_mod_cast hk)
  have h2 : (1 : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hp : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h3 : (k : ℝ) + 1 ≤ 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) := by
    have step0 : (k : ℝ) + 1 ≤ 2 * C * ((k : ℝ) + 1) := by
      calc (k : ℝ) + 1 = 1 * ((k : ℝ) + 1) := by ring
        _ ≤ 2 * C * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_right h2C (by positivity)
    have step1 : 2 * C * ((k : ℝ) + 1) ≤ 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k := by
      calc 2 * C * ((k : ℝ) + 1) = 2 * C * ((k : ℝ) + 1) * 1 := by ring
        _ ≤ 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have step2 : 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k
        ≤ 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) := by
      calc 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k
            = 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * 1 := by ring
        _ ≤ 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [step0, step1, step2]
  linarith [h3, hbig]

lemma crt_len_lt {k : ℕ} {C L : ℝ} (hC1 : 1 ≤ C)
    (hbig : 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) < L) :
    (2 : ℝ) ^ k * (2 * C) + ((2 : ℝ) ^ (k - 1) - 1) < L := by
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · norm_num at hbig ⊢
      linarith
    · norm_num at hbig ⊢
      linarith
  · have h2k : (2 : ℝ) ^ k ≤ (k : ℝ) ^ k :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hk) k
    have h2k1 : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
    have hpk : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
    have hfac : 2 ≤ ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      have h3 : (2 : ℝ) ≤ (k : ℝ) + 1 := by
        have h4 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      have h4 : (1 : ℝ) ≤ (k.factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
      nlinarith [h3, h4]
    have hCfac : 2 * C + 1 ≤ 2 * C * (((k : ℝ) + 1) * (k.factorial : ℝ)) := by
      nlinarith [hC1, hfac]
    have step1 : (2 : ℝ) ^ k * (2 * C) + ((2 : ℝ) ^ (k - 1) - 1)
        ≤ ((2 : ℝ) ^ k) * (2 * C + 1) := by nlinarith [h2k1]
    have step2 : ((2 : ℝ) ^ k) * (2 * C + 1) ≤ (k : ℝ) ^ k * (2 * C + 1) :=
      mul_le_mul_of_nonneg_right h2k (by linarith)
    have step3 : (k : ℝ) ^ k * (2 * C + 1)
        ≤ (k : ℝ) ^ k * (2 * C * (((k : ℝ) + 1) * (k.factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hCfac hpk
    have step4 : (k : ℝ) ^ k * (2 * C * (((k : ℝ) + 1) * (k.factorial : ℝ)))
        = 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) := by ring
    linarith [step1, step2, step3, step4, hbig]

/-! ### The Chinese remainder property of `PolyRel` -/

/-- **Chinese remainder property for `PolyRel`** (MRTTZ Prop. 3.5(ii)): if two polynomial
phases are `(1/p)`-equivalent for every prime `p` in a nonempty finite set `S`, then they are
`(1/∏S)`-equivalent, as soon as the interval is long compared with the constant. -/
theorem polyRel_crt {k : ℕ} {C : ℝ} (hC : 0 < C) {S : Finset ℕ} (hS : S.Nonempty)
    (hprime : ∀ p ∈ S, p.Prime) {x₁ L₁ x₂ L₂ : ℝ} {P₁ P₂ : Polynomial ℝ}
    (hL₁ : 1 ≤ L₁)
    (hbig : 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) < L₁)
    (h : ∀ p ∈ S, Work.BMF.PolyRel k C (1 / (p : ℝ)) x₁ L₁ P₁ x₂ L₂ P₂) :
    Work.BMF.PolyRel k C (1 / ((S.prod (fun p => p) : ℕ) : ℝ)) x₁ L₁ P₁ x₂ L₂ P₂ := by
  obtain ⟨p₀, hp₀⟩ := hS
  obtain ⟨h1, h2, h3, ε₀, γ₀, hε₀, hγ₀, heq₀, hb₀, hi₀⟩ := h p₀ hp₀
  have hL₁pos : 0 < L₁ := lt_of_lt_of_le zero_lt_one hL₁
  have hC1 : 1 ≤ C := by
    have hC2 : 1 ≤ C * C := by nlinarith [h1, h2, hC, hL₁pos]
    nlinarith [hC2, hC]
  have h2C : (1 : ℝ) ≤ 2 * C := by linarith
  have hL0le : (k : ℝ) + 1 ≤ L₁ := crt_len_ge h2C hbig
  have hLbig : (2 : ℝ) ^ k * (2 * C) + ((2 : ℝ) ^ (k - 1) - 1) < L₁ := crt_len_lt hC1 hbig
  have key : ∀ p ∈ S, IntegralOn (1 / (p : ℝ)) γ₀ := by
    intro p hp
    obtain ⟨g1, g2, g3, ε, γ, hε, hγ, heq, hb, hi⟩ := h p hp
    have hεγ : ε + γ = ε₀ + γ₀ := by
      have hh : ε + P₂ + γ = ε₀ + P₂ + γ₀ := heq.symm.trans heq₀
      linear_combination hh
    have hδ : ∃ c : ℤ, ε - ε₀ = Polynomial.C (c : ℝ) := by
      refine poly_const_of_intval k (2 * C) x₁ L₁ (ε - ε₀) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Submodule.sub_mem _ hε hε₀
      · linarith
      · intro t ht
        rw [Polynomial.eval_sub]
        calc |ε.eval t - ε₀.eval t| ≤ |ε.eval t| + |ε₀.eval t| := by
              have hab := abs_sub_le (ε.eval t) 0 (ε₀.eval t)
              simpa using hab
          _ ≤ C + C := add_le_add (hb t ht) (hb₀ t ht)
          _ = 2 * C := by ring
      · intro n hn
        obtain ⟨m₁, hm₁⟩ := hi₀ (p₀ * n)
        obtain ⟨m₂, hm₂⟩ := hi (p * n)
        have hp₀0 : (p₀ : ℝ) ≠ 0 := by exact_mod_cast (hprime p₀ hp₀).ne_zero
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
        have hm₁' : γ₀.eval (n : ℝ) = (m₁ : ℝ) := by
          have hkey : (1 / (p₀ : ℝ)) * (((p₀ * n : ℤ)) : ℝ) = (n : ℝ) := by
            have h2 : ((p₀ * n : ℤ) : ℝ) = (p₀ : ℝ) * (n : ℝ) := by push_cast; ring
            rw [h2, one_div, ← mul_assoc, inv_mul_cancel₀ hp₀0, one_mul]
          rw [← hm₁, hkey]
        have hm₂' : γ.eval (n : ℝ) = (m₂ : ℝ) := by
          have hkey : (1 / (p : ℝ)) * (((p * n : ℤ)) : ℝ) = (n : ℝ) := by
            have h2 : ((p * n : ℤ) : ℝ) = (p : ℝ) * (n : ℝ) := by push_cast; ring
            rw [h2, one_div, ← mul_assoc, inv_mul_cancel₀ hpR, one_mul]
          rw [← hm₂, hkey]
        have hev : ε.eval (n : ℝ) - ε₀.eval (n : ℝ) = γ₀.eval (n : ℝ) - γ.eval (n : ℝ) := by
          have hh := congrArg (Polynomial.eval (n : ℝ)) hεγ
          rw [Polynomial.eval_add, Polynomial.eval_add] at hh
          linarith
        refine ⟨m₁ - m₂, ?_⟩
        rw [Polynomial.eval_sub, hev, hm₁', hm₂']
        push_cast
        ring
      · exact hL0le
      · exact hLbig
    obtain ⟨c, hc⟩ := hδ
    have hd : γ₀ = γ + Polynomial.C (c : ℝ) := by
      have hge : γ₀ - γ = ε - ε₀ := by
        have h1 : γ₀ - γ = (ε₀ + γ₀) - ε₀ - γ := by ring
        have h2 : (ε₀ + γ₀) - ε₀ - γ = (ε + γ) - ε₀ - γ := by rw [hεγ]
        have h3 : (ε + γ) - ε₀ - γ = ε - ε₀ := by ring
        rw [h1, h2, h3]
      rw [hc] at hge
      calc γ₀ = (γ₀ - γ) + γ := by ring
        _ = Polynomial.C (c : ℝ) + γ := by rw [hge]
        _ = γ + Polynomial.C (c : ℝ) := by ring
    rw [hd]
    exact IntegralOn.crtAdd hi (IntegralOn.crtConst _ c)
  have hprod := integralOn_prod_primes hγ₀ S hprime key ⟨p₀, hp₀⟩
  exact ⟨h1, h2, h3, ε₀, γ₀, hε₀, hγ₀, heq₀, hb₀, hprod⟩

end Work.BMF
