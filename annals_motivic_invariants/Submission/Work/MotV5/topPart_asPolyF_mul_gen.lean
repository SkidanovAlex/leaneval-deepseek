import Mathlib
import Submission.Work.MotV5.WtDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top part of `(T⁵ - T - g) · A` at the maximal weight

Let `v` be a valuation of a field `F` with `1 < v g`, `A ∈ F[T]` and `i₁` a *unique* maximiser of
the weighted degree function `wt v g (A.coeff i) i = (v g)^i (v (A.coeff i))^5`
(`Submission/Work/MotV5/WtDefs.lean`).  The main result of this file is
`Work.MotV5.topPart_asPolyF_mul_gen`:

* the top part of `(T⁵ - T - g) · A` consists of exactly two monomials, of degrees `i₁` and
  `i₁ + 5`:
  `topPart v g (asPolyF g * A) = C b_{i₁+5} T^{i₁+5} + C b_{i₁} T^{i₁}`;
* the coefficient of degree `i₁ + 5` does not vanish;
* the weight of the coefficient of degree `i₁` is `(v g)^5 · wt v g (A.coeff i₁) i₁`.

The mechanism: multiplying the monomial `A_i T^i` by `T⁵`, `-T`, `-g` gives monomials of weights
`(v g)^5 w_i` (at degree `i+5`), `(v g) w_i` (at degree `i+1`) and `(v g)^5 w_i` (at degree `i`).
Since `v g > 1` and `w_i ≤ w_{i₁}` with equality only for `i = i₁`, the maximal weight is
`(v g)^5 w_{i₁}` and it is attained without cancellation only at the degrees `i₁ + 5` (from
`A_{i₁} T⁵`, unique dominant term) and `i₁` (from `-g A_{i₁}`, unique dominant term).
No hypothesis on the degree of `A` is needed.
-/

set_option autoImplicit false

namespace Work.MotV5

open Polynomial

section Helpers

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]

/-- Shifting the index of a monomial weight by `m`. -/
lemma wt_add_index (v : Valuation F Γ₀) (g c : F) (l m : ℕ) :
    wt v g c (l + m) = (v g) ^ m * wt v g c l := by
  rw [wt, wt, pow_add]; ac_rfl

/-- Shifting the index of a monomial weight down by `m ≤ n`. -/
lemma wt_shift_index (v : Valuation F Γ₀) (g c : F) (m : ℕ) {n : ℕ} (h : m ≤ n) :
    wt v g c n = (v g) ^ m * wt v g c (n - m) := by
  rw [show wt v g c n = wt v g c ((n - m) + m) from by rw [Nat.sub_add_cancel h]]
  exact wt_add_index v g c (n - m) m

/-- The weight of the coefficient of `C g * A` at degree `l`. -/
lemma wt_g_mul_coeff (v : Valuation F Γ₀) (g c : F) (l : ℕ) :
    wt v g (g * c) l = (v g) ^ 5 * wt v g c l := by
  have h := wt_mul v g g c 0 l
  rw [zero_add] at h
  rw [h, show wt v g g 0 = (v g) ^ 5 from by simp [wt]]

/-- The weight of the zero coefficient. -/
lemma wt_zero_coeff (v : Valuation F Γ₀) (g : F) (l : ℕ) : wt v g (0 : F) l = 0 := by
  rw [wt, map_zero, zero_pow (by norm_num : 5 ≠ 0), mul_zero]

/-- Monotonicity of the weight in the coefficient. -/
lemma wt_le_wt_of_val_le (v : Valuation F Γ₀) (g : F) {c d : F} {l : ℕ} (h : v c ≤ v d) :
    wt v g c l ≤ wt v g d l := by
  simp only [wt]
  exact mul_le_mul_right (pow_le_pow_left₀ zero_le h 5) _

/-- Comparison of weights of two coefficients at the *same* degree, via the fifth-root of the
value group. -/
lemma wt_lt_wt_iff (v : Valuation F Γ₀) {g : F} (hg : v g ≠ 0) {c d : F} {l : ℕ} :
    wt v g c l < wt v g d l ↔ v c < v d := by
  have hρ : 0 < (v g) ^ l := pow_pos (zero_lt_iff.mpr hg) l
  simp only [wt]
  rw [mul_lt_mul_iff_of_pos_left hρ]
  exact pow_lt_pow_iff_left₀ zero_le zero_le (by norm_num)

/-- A three-term difference whose *last* term dominates. -/
lemma map_sub_sub_eq_of_lt_right (v : Valuation F Γ₀) {a b c : F}
    (ha : v a < v c) (hb : v b < v c) : v (a - b - c) = v c := by
  have h1 : v (a - b) < v c := lt_of_le_of_lt (Valuation.map_sub v a b) (max_lt ha hb)
  rw [Valuation.map_sub_eq_of_lt_right v h1]

/-- A three-term difference whose *first* term dominates. -/
lemma map_sub_sub_eq_of_lt_left (v : Valuation F Γ₀) {a b c : F}
    (hb : v b < v a) (hc : v c < v a) : v (a - b - c) = v a := by
  have h1 : v (a - b) = v a := Valuation.map_sub_eq_of_lt_left v hb
  rw [Valuation.map_sub_eq_of_lt_left v (h1 ▸ hc), h1]

end Helpers

theorem topPart_asPolyF_mul_gen {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g : F} (hg1 : 1 < v g)
    {A : Polynomial F} {i₁ : ℕ}
    (hmax : ∀ i, wt v g (A.coeff i) i ≤ wt v g (A.coeff i₁) i₁)
    (huniq : ∀ i, wt v g (A.coeff i) i = wt v g (A.coeff i₁) i₁ → i = i₁) :
    topPart v g (asPolyF g * A)
        = Polynomial.C ((asPolyF g * A).coeff (i₁ + 5)) * Polynomial.X ^ (i₁ + 5)
          + Polynomial.C ((asPolyF g * A).coeff i₁) * Polynomial.X ^ i₁
      ∧ (asPolyF g * A).coeff (i₁ + 5) ≠ 0
      ∧ wt v g ((asPolyF g * A).coeff i₁) i₁ = (v g) ^ 5 * wt v g (A.coeff i₁) i₁ := by
  have hgne : v g ≠ 0 := ne_of_gt (lt_trans zero_lt_one hg1)
  have hρ0 : 0 < v g := lt_trans zero_lt_one hg1
  have hρlt : v g < (v g) ^ 5 := by
    have h := pow_lt_pow_right₀ (M₀ := Γ₀) hg1 (by norm_num : 1 < 5)
    simpa using h
  have hρ5pos : 0 < (v g) ^ 5 := pow_pos hρ0 5
  -- the maximising coefficient is nonzero
  have hAi : A.coeff i₁ ≠ 0 := by
    intro h0
    have hwi : wt v g (A.coeff i₁) i₁ = 0 := wt_zero v g (A.coeff i₁) i₁ h0
    have hall : ∀ k, wt v g (A.coeff k) k = 0 := fun k =>
      le_antisymm (by rw [← hwi]; exact hmax k) zero_le
    have hbad : i₁ + 1 = i₁ := huniq (i₁ + 1) (by rw [hall (i₁ + 1), hall i₁])
    omega
  have hvi : v (A.coeff i₁) ≠ 0 := (Valuation.ne_zero_iff v).mpr hAi
  have hwine : wt v g (A.coeff i₁) i₁ ≠ 0 := by
    rw [wt]; exact mul_ne_zero (pow_ne_zero _ hgne) (pow_ne_zero _ hvi)
  have hwipos : 0 < wt v g (A.coeff i₁) i₁ := zero_lt_iff.mpr hwine
  have hstrict : ∀ j, j ≠ i₁ → wt v g (A.coeff j) j < wt v g (A.coeff i₁) i₁ :=
    fun j hj => lt_of_le_of_ne (hmax j) (fun heq => hj (huniq j heq))
  set M : Γ₀ := (v g) ^ 5 * wt v g (A.coeff i₁) i₁ with hM
  have hMpos : 0 < M := by rw [hM]; exact mul_pos hρ5pos hwipos
  -- the coefficient of `asPolyF g * A` as a difference of three terms
  have hcoeff : ∀ k : ℕ, (asPolyF g * A).coeff k
      = (Polynomial.X ^ 5 * A).coeff k - (Polynomial.X * A).coeff k
        - (Polynomial.C g * A).coeff k := by
    intro k
    have hb : asPolyF g * A = Polynomial.X ^ 5 * A - Polynomial.X * A - Polynomial.C g * A := by
      simp only [asPolyF]; ring
    rw [hb]; simp only [coeff_sub]
  -- bounds for the three contributions
  have hU5 : ∀ k : ℕ, wt v g ((Polynomial.X ^ 5 * A).coeff k) k ≤ M := by
    intro k
    rw [Polynomial.coeff_X_pow_mul']
    by_cases h5 : 5 ≤ k
    · rw [ite_eq_left h5, wt_shift_index v g (A.coeff (k - 5)) 5 h5, hM]
      exact mul_le_mul_right (hmax (k - 5)) _
    · rw [ite_eq_right h5, wt_zero_coeff]
      exact zero_le
  have hU5' : ∀ k : ℕ, k ≠ i₁ + 5 → wt v g ((Polynomial.X ^ 5 * A).coeff k) k < M := by
    intro k hk
    rw [Polynomial.coeff_X_pow_mul']
    by_cases h5 : 5 ≤ k
    · rw [ite_eq_left h5, wt_shift_index v g (A.coeff (k - 5)) 5 h5, hM]
      refine mul_lt_mul_of_pos_left (hstrict (k - 5) ?_) hρ5pos
      omega
    · rw [ite_eq_right h5, wt_zero_coeff]
      exact hMpos
  have hcoeffX : ∀ k : ℕ, (Polynomial.X * A).coeff k
      = if 1 ≤ k then A.coeff (k - 1) else 0 := by
    intro k
    have h := Polynomial.coeff_X_pow_mul' A 1 k
    simpa using h
  have hU1 : ∀ k : ℕ, wt v g ((Polynomial.X * A).coeff k) k ≤ M := by
    intro k
    rw [hcoeffX k]
    by_cases h1 : 1 ≤ k
    · rw [ite_eq_left h1, wt_shift_index v g (A.coeff (k - 1)) 1 h1, hM]
      have h1' : (v g) ^ 1 ≤ (v g) ^ 5 :=
        le_of_lt (by simpa using pow_lt_pow_right₀ (M₀ := Γ₀) hg1 (by norm_num : 1 < 5))
      calc (v g) ^ 1 * wt v g (A.coeff (k - 1)) (k - 1)
          ≤ (v g) ^ 5 * wt v g (A.coeff (k - 1)) (k - 1) := mul_le_mul_left h1' _
        _ ≤ (v g) ^ 5 * wt v g (A.coeff i₁) i₁ := mul_le_mul_right (hmax (k - 1)) _
    · rw [ite_eq_right h1, wt_zero_coeff]
      exact zero_le
  have hU1' : ∀ k : ℕ, wt v g ((Polynomial.X * A).coeff k) k < M := by
    intro k
    rw [hcoeffX k]
    by_cases h1 : 1 ≤ k
    · rw [ite_eq_left h1, wt_shift_index v g (A.coeff (k - 1)) 1 h1, hM, pow_one]
      calc (v g) * wt v g (A.coeff (k - 1)) (k - 1)
          ≤ (v g) * wt v g (A.coeff i₁) i₁ := mul_le_mul_right (hmax (k - 1)) _
        _ < (v g) ^ 5 * wt v g (A.coeff i₁) i₁ := mul_lt_mul_of_pos_right hρlt hwipos
    · rw [ite_eq_right h1, wt_zero_coeff]
      exact hMpos
  have hUC : ∀ k : ℕ, wt v g ((Polynomial.C g * A).coeff k) k ≤ M := by
    intro k
    rw [Polynomial.coeff_C_mul, wt_g_mul_coeff, hM]
    exact mul_le_mul_right (hmax k) _
  have hUC' : ∀ k : ℕ, k ≠ i₁ → wt v g ((Polynomial.C g * A).coeff k) k < M := by
    intro k hk
    rw [Polynomial.coeff_C_mul, wt_g_mul_coeff, hM]
    exact mul_lt_mul_of_pos_left (hstrict k hk) hρ5pos
  -- the ultrametric inequality for the coefficient of the product
  have hvc : ∀ k : ℕ, v ((asPolyF g * A).coeff k)
      ≤ max (v ((Polynomial.X ^ 5 * A).coeff k))
          (max (v ((Polynomial.X * A).coeff k)) (v ((Polynomial.C g * A).coeff k))) := by
    intro k
    rw [hcoeff k]
    have h1 : v ((Polynomial.X ^ 5 * A).coeff k + -((Polynomial.X * A).coeff k))
        ≤ max (v ((Polynomial.X ^ 5 * A).coeff k)) (v ((Polynomial.X * A).coeff k)) := by
      refine le_trans (Valuation.map_add v _ _) ?_
      rw [Valuation.map_neg]
    have h2 : v (-((Polynomial.C g * A).coeff k)) = v ((Polynomial.C g * A).coeff k) :=
      Valuation.map_neg v _
    have harg : (Polynomial.X ^ 5 * A).coeff k - (Polynomial.X * A).coeff k
          - (Polynomial.C g * A).coeff k
        = ((Polynomial.X ^ 5 * A).coeff k + -((Polynomial.X * A).coeff k))
          + -((Polynomial.C g * A).coeff k) := by ring
    rw [harg]
    calc v (((Polynomial.X ^ 5 * A).coeff k + -((Polynomial.X * A).coeff k))
            + -((Polynomial.C g * A).coeff k))
        ≤ max (v ((Polynomial.X ^ 5 * A).coeff k + -((Polynomial.X * A).coeff k)))
            (v (-((Polynomial.C g * A).coeff k))) := Valuation.map_add v _ _
      _ ≤ max (max (v ((Polynomial.X ^ 5 * A).coeff k)) (v ((Polynomial.X * A).coeff k)))
            (v ((Polynomial.C g * A).coeff k)) := max_le_max h1 (le_of_eq h2)
      _ = max (v ((Polynomial.X ^ 5 * A).coeff k))
            (max (v ((Polynomial.X * A).coeff k)) (v ((Polynomial.C g * A).coeff k))) :=
          max_assoc _ _ _
  have hbound : ∀ k : ℕ, wt v g ((asPolyF g * A).coeff k) k ≤ M := by
    intro k
    rcases le_max_iff.mp (hvc k) with h | h
    · exact le_trans (wt_le_wt_of_val_le v g h) (hU5 k)
    · rcases le_max_iff.mp h with h | h
      · exact le_trans (wt_le_wt_of_val_le v g h) (hU1 k)
      · exact le_trans (wt_le_wt_of_val_le v g h) (hUC k)
  have hbound' : ∀ k : ℕ, k ≠ i₁ → k ≠ i₁ + 5 →
      wt v g ((asPolyF g * A).coeff k) k < M := by
    intro k hk1 hk2
    rcases le_max_iff.mp (hvc k) with h | h
    · exact lt_of_le_of_lt (wt_le_wt_of_val_le v g h) (hU5' k hk2)
    · rcases le_max_iff.mp h with h | h
      · exact lt_of_le_of_lt (wt_le_wt_of_val_le v g h) (hU1' k)
      · exact lt_of_le_of_lt (wt_le_wt_of_val_le v g h) (hUC' k hk1)
  -- the exact value of the coefficients at degrees `i₁` and `i₁ + 5`
  have hX5 : (Polynomial.X ^ 5 * A).coeff (i₁ + 5) = A.coeff i₁ :=
    Polynomial.coeff_X_pow_mul A 5 i₁
  have hCT : wt v g (g * A.coeff (i₁ + 5)) (i₁ + 5) < M := by
    rw [wt_g_mul_coeff]
    exact mul_lt_mul_of_pos_left (hstrict (i₁ + 5) (by omega)) hρ5pos
  have hval_i : v ((asPolyF g * A).coeff i₁) = v (g * A.coeff i₁) := by
    rw [hcoeff i₁, Polynomial.coeff_C_mul]
    refine map_sub_sub_eq_of_lt_right v ?_ ?_
    · refine (wt_lt_wt_iff (v := v) (hg := hgne) (c := (Polynomial.X ^ 5 * A).coeff i₁)
        (d := g * A.coeff i₁) (l := i₁)).mp ?_
      rw [wt_g_mul_coeff, ← hM]
      exact hU5' i₁ (by omega)
    · refine (wt_lt_wt_iff (v := v) (hg := hgne) (c := (Polynomial.X * A).coeff i₁)
        (d := g * A.coeff i₁) (l := i₁)).mp ?_
      rw [wt_g_mul_coeff, ← hM]
      exact hU1' i₁
  have hbi : (asPolyF g * A).coeff i₁ ≠ 0 := by
    intro h0
    have h0' : v ((asPolyF g * A).coeff i₁) = 0 := by rw [h0]; simp
    rw [hval_i, Valuation.map_mul] at h0'
    exact mul_ne_zero hgne hvi h0'
  have hwt_i : wt v g ((asPolyF g * A).coeff i₁) i₁ = M := by
    have hthis : wt v g ((asPolyF g * A).coeff i₁) i₁ = wt v g (g * A.coeff i₁) i₁ := by
      rw [wt, wt, hval_i]
    rw [hthis, wt_g_mul_coeff, hM]
  have hval_i5 : v ((asPolyF g * A).coeff (i₁ + 5)) = v (A.coeff i₁) := by
    rw [hcoeff (i₁ + 5), hX5, Polynomial.coeff_C_mul]
    refine map_sub_sub_eq_of_lt_left v ?_ ?_
    · refine (wt_lt_wt_iff (v := v) (hg := hgne) (c := (Polynomial.X * A).coeff (i₁ + 5))
        (d := A.coeff i₁) (l := i₁ + 5)).mp ?_
      rw [wt_add_index v g (A.coeff i₁) i₁ 5, ← hM]
      exact hU1' (i₁ + 5)
    · refine (wt_lt_wt_iff (v := v) (hg := hgne) (c := g * A.coeff (i₁ + 5))
        (d := A.coeff i₁) (l := i₁ + 5)).mp ?_
      rw [wt_add_index v g (A.coeff i₁) i₁ 5, ← hM]
      exact hCT
  have hbi5 : (asPolyF g * A).coeff (i₁ + 5) ≠ 0 := by
    intro h0
    have h0' : v ((asPolyF g * A).coeff (i₁ + 5)) = 0 := by rw [h0]; simp
    rw [hval_i5] at h0'
    exact hvi h0'
  have hwt_i5 : wt v g ((asPolyF g * A).coeff (i₁ + 5)) (i₁ + 5) = M := by
    have hthis : wt v g ((asPolyF g * A).coeff (i₁ + 5)) (i₁ + 5)
        = wt v g (A.coeff i₁) (i₁ + 5) := by
      rw [wt, wt, hval_i5]
    rw [hthis, wt_add_index v g (A.coeff i₁) i₁ 5, hM]
  -- the maximum of the weights of the product
  have hWt : Wt v g (asPolyF g * A) = M := by
    rw [Wt]
    refine le_antisymm (Finset.sup_le fun l _ => hbound l) ?_
    rw [← hwt_i]
    exact Finset.le_sup (f := fun l => wt v g ((asPolyF g * A).coeff l) l)
      (Polynomial.mem_support_iff.mpr hbi)
  -- the top part
  have htop : topPart v g (asPolyF g * A)
      = Polynomial.C ((asPolyF g * A).coeff i₁) * Polynomial.X ^ i₁
        + Polynomial.C ((asPolyF g * A).coeff (i₁ + 5)) * Polynomial.X ^ (i₁ + 5) := by
    rw [topPart, hWt]
    have hsub : ({i₁, i₁ + 5} : Finset ℕ) ⊆ (asPolyF g * A).support := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact Polynomial.mem_support_iff.mpr hbi
      · rw [Finset.mem_singleton] at h
        rw [h]; exact Polynomial.mem_support_iff.mpr hbi5
    have hzero : ∀ x ∈ (asPolyF g * A).support, x ∉ ({i₁, i₁ + 5} : Finset ℕ) →
        (if wt v g ((asPolyF g * A).coeff x) x = M then
          Polynomial.C ((asPolyF g * A).coeff x) * Polynomial.X ^ x else 0) = 0 := by
      intro x _ hx
      have hx1 : x ≠ i₁ := fun h => hx (by rw [h]; simp)
      have hx2 : x ≠ i₁ + 5 := fun h => hx (by rw [h]; simp)
      rw [ite_eq_right (ne_of_lt (hbound' x hx1 hx2))]
    rw [← Finset.sum_subset hsub hzero]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton, ite_eq_left hwt_i, ite_eq_left hwt_i5]
  exact ⟨htop.trans (add_comm _ _), hbi5, hwt_i.trans hM⟩

end Work.MotV5
