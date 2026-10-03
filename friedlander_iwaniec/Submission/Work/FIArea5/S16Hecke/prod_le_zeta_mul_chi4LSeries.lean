import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A bound for a product over primes by `ζ(σ) · L(σ, χ₄)`

For `σ > 1` we prove
```
∏_p (if p ≡ 1 (mod 4) then (1 + p ^ (-σ)) ^ 2 else 1 + p ^ (-2σ)) ≤ ζ(σ) · L(σ, χ₄)
```
where the right-hand side is written as the product of the two absolutely convergent
series `∑ n ^ (-σ)` and `∑ χ₄(n) n ^ (-σ)`.

The proof uses the Euler products for the two completely multiplicative functions
`n ↦ n ^ (-σ)` and `n ↦ χ₄(n) n ^ (-σ)` (from `Mathlib.NumberTheory.EulerProduct`),
together with the elementary pointwise bound, valid for every prime `p`,
```
(if p ≡ 1 (mod 4) then (1 + x) ^ 2 else 1 + x ^ 2)
  ≤ (1 - x)⁻¹ * (1 - χ₄(p) x)⁻¹,      x = p ^ (-σ) ∈ [0, 1).
```
-/

namespace Work.FIArea5.S16Hecke

/-! ### The two completely multiplicative summands -/

/-- The completely multiplicative function `n ↦ n ^ (-σ)`, whose series is `ζ(σ)`. -/
noncomputable def zetaSummand (σ : ℝ) (hσ : σ ≠ 0) : ℕ →*₀ ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_zero' := by rw [Nat.cast_zero, Real.zero_rpow (x := -σ) (neg_ne_zero.mpr hσ)]
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

@[simp] lemma zetaSummand_apply (σ : ℝ) (hσ : σ ≠ 0) (n : ℕ) :
    zetaSummand σ hσ n = (n : ℝ) ^ (-σ) := rfl

/-- The completely multiplicative function `n ↦ χ₄(n) n ^ (-σ)`, whose series is `L(σ, χ₄)`. -/
noncomputable def chi4Summand (σ : ℝ) (hσ : σ ≠ 0) : ℕ →*₀ ℝ where
  toFun n := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ)
  map_zero' := by
    have h : ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (x := -σ) (neg_ne_zero.mpr hσ)]
    rw [h, mul_zero]
  map_one' := by simp
  map_mul' m n := by
    have h1 : ((ZMod.χ₄ ((m * n : ℕ) : ZMod 4) : ℤ) : ℝ)
        = ((ZMod.χ₄ (m : ZMod 4) : ℤ) : ℝ) * ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) := by
      rw [Nat.cast_mul, map_mul]; push_cast; ring
    have h2 : ((m * n : ℕ) : ℝ) ^ (-σ) = (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    rw [h1, h2]; ring

@[simp] lemma chi4Summand_apply (σ : ℝ) (hσ : σ ≠ 0) (n : ℕ) :
    chi4Summand σ hσ n = ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ) := rfl

/-! ### Elementary facts about `χ₄` -/

lemma chi4_cast_eq_one_of_mod_four (n : ℕ) (h : n % 4 = 1) :
    ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) = 1 := by
  rw [ZMod.χ₄_nat_one_mod_four h]; norm_num

lemma chi4_cast_ge_neg_one (n : ℕ) :
    (-1 : ℝ) ≤ ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) := by
  have h := ZMod.χ₄_nat_eq_if_mod_four n
  rw [h]; split_ifs <;> norm_num

lemma chi4_cast_le_one (n : ℕ) :
    ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) ≤ 1 := by
  have h := ZMod.χ₄_nat_eq_if_mod_four n
  rw [h]; split_ifs <;> norm_num

/-! ### Summability of the two summands -/

lemma summable_norm_zetaSummand {σ : ℝ} (hσ : 1 < σ) (hne : σ ≠ 0) :
    Summable (fun n : ℕ => ‖zetaSummand σ hne n‖) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ σ)⁻¹) := Real.summable_nat_rpow_inv.mpr hσ
  refine h.congr (fun n => ?_)
  rw [zetaSummand_apply, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.rpow_neg (Nat.cast_nonneg n) σ]

lemma summable_norm_chi4Summand {σ : ℝ} (hσ : 1 < σ) (hne : σ ≠ 0) :
    Summable (fun n : ℕ => ‖chi4Summand σ hne n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_zetaSummand hσ hne)
  have hc : ‖((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨chi4_cast_ge_neg_one n, chi4_cast_le_one n⟩
  rw [chi4Summand_apply, zetaSummand_apply, norm_mul]
  calc ‖((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)‖ * ‖(n : ℝ) ^ (-σ)‖
      ≤ 1 * ‖(n : ℝ) ^ (-σ)‖ := by gcongr
    _ = ‖(n : ℝ) ^ (-σ)‖ := one_mul _

/-! ### The pointwise bound at a prime -/

lemma one_add_le_inv_one_sub {x : ℝ} (_h0 : 0 ≤ x) (h1 : x < 1) : 1 + x ≤ (1 - x)⁻¹ := by
  have hpos : 0 < 1 - x := by linarith
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith [sq_nonneg x]

lemma one_add_sq_le_inv_one_sub_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    1 + x ^ 2 ≤ (1 - x ^ 2)⁻¹ := by
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith [sq_nonneg (x ^ 2)]

lemma inv_one_sub_sq_le_mul_inv {x c : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (hc : -1 ≤ c)
    (hc1 : c ≤ 1) :
    (1 - x ^ 2)⁻¹ ≤ (1 - x)⁻¹ * (1 - c * x)⁻¹ := by
  have hcx : 0 < 1 - c * x := by
    have : c * x ≤ x := by nlinarith [mul_le_mul_of_nonneg_right hc1 h0]
    linarith
  rw [← mul_inv]
  refine inv_le_inv₀ (by nlinarith) (by positivity) |>.mpr ?_
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + c) (by linarith : (0 : ℝ) ≤ 1 - x)]

lemma one_le_mul_inv {x c : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (hc : -1 ≤ c) (hc1 : c ≤ 1) :
    1 ≤ (1 - x)⁻¹ * (1 - c * x)⁻¹ := by
  have h := inv_one_sub_sq_le_mul_inv h0 h1 hc hc1
  have h2 : (1 : ℝ) ≤ (1 - x ^ 2)⁻¹ := by
    have hpos : 0 < 1 - x ^ 2 := by nlinarith
    rw [inv_eq_one_div, le_div_iff₀ hpos]; nlinarith
  linarith

lemma factor_le_case_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    (1 + x) ^ 2 ≤ (1 - x)⁻¹ * (1 - (1 : ℝ) * x)⁻¹ := by
  have h := one_add_le_inv_one_sub h0 h1
  have h2 : (1 + x) ^ 2 ≤ ((1 - x)⁻¹) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
  rw [one_mul]
  calc (1 + x) ^ 2 ≤ ((1 - x)⁻¹) ^ 2 := h2
    _ = (1 - x)⁻¹ * (1 - x)⁻¹ := by rw [pow_two]

lemma factor_le_case_other {x c : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (hc : -1 ≤ c) (hc1 : c ≤ 1) :
    1 + x ^ 2 ≤ (1 - x)⁻¹ * (1 - c * x)⁻¹ :=
  le_trans (one_add_sq_le_inv_one_sub_sq h0 h1) (inv_one_sub_sq_le_mul_inv h0 h1 hc hc1)

/-- The pointwise bound at a prime `q ≥ 2` with `σ > 0`. -/
lemma factor_le_aux {σ : ℝ} (hσ : 0 < σ) {q : ℕ} (hq : 2 ≤ q) :
    (if q % 4 = 1 then (1 + (q : ℝ) ^ (-σ)) ^ 2 else (1 + (q : ℝ) ^ (-2 * σ)))
    ≤ (1 - (q : ℝ) ^ (-σ))⁻¹
      * (1 - ((ZMod.χ₄ (q : ZMod 4) : ℤ) : ℝ) * (q : ℝ) ^ (-σ))⁻¹ := by
  have hx2 : (q : ℝ) ^ (-2 * σ) = ((q : ℝ) ^ (-σ)) ^ 2 := by
    rw [show (-2 * σ : ℝ) = (-σ) * 2 by ring, Real.rpow_mul (Nat.cast_nonneg q) (-σ) 2,
      Real.rpow_two]
  have hx0 : 0 ≤ (q : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hx1 : (q : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < q by omega)) (by linarith)
  by_cases h : q % 4 = 1
  · rw [if_pos h, chi4_cast_eq_one_of_mod_four q h]
    exact factor_le_case_one hx0 hx1
  · rw [if_neg h, hx2]
    exact factor_le_case_other hx0 hx1 (chi4_cast_ge_neg_one q) (chi4_cast_le_one q)

/-! ### Monotonicity of finite products of terms `≥ 1` -/

lemma prod_le_prod_of_subset_of_one_le_real {ι : Type*} [DecidableEq ι] {f : ι → ℝ}
    (h1 : ∀ i, 1 ≤ f i) {s t : Finset ι} (hst : s ⊆ t) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  have hs0 : 0 ≤ ∏ i ∈ s, f i := le_trans zero_le_one (Finset.one_le_prod₀ (fun i _ => h1 i))
  have hts1 : 1 ≤ ∏ i ∈ t \ s, f i := Finset.one_le_prod₀ (fun i _ => h1 i)
  rw [← Finset.prod_sdiff hst, mul_comm]
  simpa using mul_le_mul_of_nonneg_left hts1 hs0

/-! ### The main theorem -/

theorem prod_le_zeta_mul_chi4LSeries (σ : ℝ) (hσ : 1 < σ) :
    (∏' p : Nat.Primes,
      (if (p : ℕ) % 4 = 1 then (1 + ((p : ℕ) : ℝ) ^ (-σ)) ^ 2
       else (1 + ((p : ℕ) : ℝ) ^ (-2 * σ))))
    ≤ (∑' n : ℕ, (n : ℝ) ^ (-σ))
      * (∑' n : ℕ, ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ)) := by
  have hσpos : 0 < σ := by linarith
  have hne : σ ≠ 0 := ne_of_gt hσpos
  have hsumZ := summable_norm_zetaSummand hσ hne
  have hsumC := summable_norm_chi4Summand hσ hne
  have hZhas := EulerProduct.eulerProduct_completely_multiplicative_hasProd (F := ℝ) hsumZ
  have hChas := EulerProduct.eulerProduct_completely_multiplicative_hasProd (F := ℝ) hsumC
  set B : Nat.Primes → ℝ :=
    fun p => (1 - zetaSummand σ hne (p : ℕ))⁻¹ * (1 - chi4Summand σ hne (p : ℕ))⁻¹ with hB
  have hBmult : Multipliable B := (hZhas.mul hChas).multipliable
  have hBprod : ∏' p : Nat.Primes, B p
      = (∑' n : ℕ, (n : ℝ) ^ (-σ))
        * (∑' n : ℕ, ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ)) := by
    have h1 : ∏' p : Nat.Primes, (1 - zetaSummand σ hne (p : ℕ))⁻¹
        = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
      rw [EulerProduct.eulerProduct_completely_multiplicative_tprod hsumZ]
      simp only [zetaSummand_apply]
    have h2 : ∏' p : Nat.Primes, (1 - chi4Summand σ hne (p : ℕ))⁻¹
        = ∑' n : ℕ, ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ) := by
      rw [EulerProduct.eulerProduct_completely_multiplicative_tprod hsumC]
      simp only [chi4Summand_apply]
    rw [hB, Multipliable.tprod_mul hZhas.multipliable hChas.multipliable, h1, h2]
  have hB1 : ∀ p : Nat.Primes, 1 ≤ B p := by
    intro p
    have hp : 2 ≤ (p : ℕ) := p.prop.two_le
    have hx0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hx1 : ((p : ℕ) : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (show 1 < (p : ℕ) by omega))
        (by linarith)
    rw [hB]
    exact one_le_mul_inv hx0 hx1 (chi4_cast_ge_neg_one (p : ℕ)) (chi4_cast_le_one (p : ℕ))
  rw [← hBprod]
  have hB_lim : 1 ≤ ∏' p : Nat.Primes, B p :=
    ge_of_tendsto' hBmult.hasProd (fun s => Finset.one_le_prod₀ (fun i _ => hB1 i))
  refine tprod_le_of_prod_le' hB_lim (fun s => ?_)
  have hAB : ∀ p ∈ s,
      (if (p : ℕ) % 4 = 1 then (1 + ((p : ℕ) : ℝ) ^ (-σ)) ^ 2
       else (1 + ((p : ℕ) : ℝ) ^ (-2 * σ))) ≤ B p := by
    intro p _
    have h := factor_le_aux hσpos p.prop.two_le
    rw [hB]
    simpa only [zetaSummand_apply, chi4Summand_apply] using h
  have hA0 : ∀ p ∈ s,
      (0 : ℝ) ≤ if (p : ℕ) % 4 = 1 then (1 + ((p : ℕ) : ℝ) ^ (-σ)) ^ 2
       else (1 + ((p : ℕ) : ℝ) ^ (-2 * σ)) := by
    intro p _
    by_cases h : (p : ℕ) % 4 = 1
    · rw [if_pos h]; positivity
    · rw [if_neg h]; positivity
  calc ∏ p ∈ s, (if (p : ℕ) % 4 = 1 then (1 + ((p : ℕ) : ℝ) ^ (-σ)) ^ 2
          else (1 + ((p : ℕ) : ℝ) ^ (-2 * σ)))
      ≤ ∏ p ∈ s, B p := Finset.prod_le_prod₀ hA0 hAB
    _ ≤ ∏' p : Nat.Primes, B p :=
        ge_of_tendsto hBmult.hasProd
          (Filter.eventually_atTop.mpr
            ⟨s, fun t ht => prod_le_prod_of_subset_of_one_le_real hB1 ht⟩)

end Work.FIArea5.S16Hecke
