import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.criticalClass_gaussSum_primePow
import Submission.Commons.NumberTheory.GaussSum.quadratic_gauss_primitive_root

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.DirichletCharacter

variable {p e ℓ M : ℕ} [NeZero p]
/-- If all pairwise products `x i * x j` vanish, then `∏ (1 + x i) = 1 + ∑ x i`. -/
lemma prod_one_add_of_pairwise_eq_zero {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (x : ι → R) (h : ∀ i ∈ s, ∀ j ∈ s, x i * x j = 0) :
    ∏ i ∈ s, (1 + x i) = 1 + ∑ i ∈ s, x i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have hs : ∀ i ∈ s, ∀ j ∈ s, x i * x j = 0 :=
      fun i hi j hj => h i (Finset.mem_cons_of_mem hi) j (Finset.mem_cons_of_mem hj)
    rw [ih hs]
    have ha_all : ∀ j ∈ s, x a * x j = 0 :=
      fun j hj => h a (Finset.mem_cons_self a s) j (Finset.mem_cons_of_mem hj)
    have hsum : x a * ∑ j ∈ s, x j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => ha_all j hj)
    have : (1 + x a) * (1 + ∑ i ∈ s, x i) = 1 + (x a + ∑ i ∈ s, x i) := by
      linear_combination hsum
    rw [this]

/-- `(1 + x)⁻¹ = 1 - x` in `ZMod n` when `x ^ 2 = 0`. -/
lemma inv_one_add_eq_one_sub {n : ℕ} (x : ZMod n) (hx : x ^ 2 = 0) : (1 + x)⁻¹ = 1 - x := by
  refine ZMod.inv_eq_of_mul_eq_one n _ _ ?_
  rw [show (1 + x) * (1 - x) = 1 - x ^ 2 by ring, hx, sub_zero]
/-- The "product coordinate" for three plus-factors and three minus-factors. -/
noncomputable def prodCoord3 (p e ℓ : ℕ) (A C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    ZMod (p ^ e) :=
  (∏ l : Fin 3, (1 + pPow p e ℓ * A l * w)) * (∏ l : Fin 3, (1 + pPow p e ℓ * C l * w)⁻¹)

/-- The "phase" for three plus-factors and three minus-factors. -/
noncomputable def phase3 (p e ℓ : ℕ) (χ : DirichletCharacter ℂ (p ^ e))
    (A C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) : ℂ :=
  (∏ l : Fin 3, χ (1 + pPow p e ℓ * A l * w))
    * (∏ l : Fin 3, (starRingEnd ℂ) (χ (1 + pPow p e ℓ * C l * w)))

/-- The level-`ℓ` sum over the lifts of `ZMod (p^M)`. -/
noncomputable def levelSum3 (p e ℓ M : ℕ) [NeZero p] (χ : DirichletCharacter ℂ (p ^ e))
    (A C : Fin 3 → ZMod (p ^ e)) : ℂ :=
  ∑ w : ZMod (p ^ M), phase3 p e ℓ χ A C ((w.val : ℕ) : ZMod (p ^ e))

/-- The phase is the character of the product coordinate. -/
lemma phase3_eq_chi_prodCoord3 (hℓ : 1 ≤ ℓ) (χ : DirichletCharacter ℂ (p ^ e))
    (A C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    phase3 p e ℓ χ A C w = χ (prodCoord3 p e ℓ A C w) := by
  haveI : NeZero (p ^ e) := inferInstance
  have hunit : ∀ U : ZMod (p ^ e), IsUnit (1 + pPow p e ℓ * U * w) := by
    intro U; exact isUnit_one_add_pPow_mul (p := p) (e := e) hℓ U w
  have hC : ∏ l : Fin 3, (starRingEnd ℂ) (χ (1 + pPow p e ℓ * C l * w))
      = χ (∏ l : Fin 3, (1 + pPow p e ℓ * C l * w)⁻¹) := by
    rw [map_prod χ (fun l => (1 + pPow p e ℓ * C l * w)⁻¹) Finset.univ,
      Finset.prod_congr rfl (fun l _ => (star_chi_eq_chi_inv χ _ (hunit (C l))).symm)]
  have hA : ∏ l : Fin 3, χ (1 + pPow p e ℓ * A l * w)
      = χ (∏ l : Fin 3, (1 + pPow p e ℓ * A l * w)) :=
    (map_prod χ (fun l => (1 + pPow p e ℓ * A l * w)) Finset.univ).symm
  simp only [phase3, prodCoord3]
  rw [hC, hA, ← map_mul]
/-- The product `∏ (1 + p^ℓ A_l w)` for `2ℓ ≥ e` is `1 + (∑ A_l) p^ℓ w`. -/
lemma prod_one_add_pPow_eq (h : e ≤ 2 * ℓ) (A : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    ∏ l : Fin 3, (1 + pPow p e ℓ * A l * w) = 1 + (∑ l : Fin 3, A l) * pPow p e ℓ * w := by
  have hsq : pPow p e ℓ * pPow p e ℓ = 0 := by
    rw [pPow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rw [show (p ^ ℓ) * (p ^ ℓ) = p ^ (ℓ + ℓ) by ring]
    exact pow_dvd_pow p (by omega)
  have hpair : ∀ i j : Fin 3, (pPow p e ℓ * A i * w) * (pPow p e ℓ * A j * w) = 0 := by
    intro i j
    rw [show (pPow p e ℓ * A i * w) * (pPow p e ℓ * A j * w)
        = (pPow p e ℓ * pPow p e ℓ) * (A i * w * A j * w) by ring, hsq, zero_mul]
  rw [prod_one_add_of_pairwise_eq_zero Finset.univ (fun l => pPow p e ℓ * A l * w)
    (fun i _ j _ => hpair i j)]
  congr 1
  rw [Finset.sum_congr rfl (fun l _ => show pPow p e ℓ * A l * w = A l * (pPow p e ℓ * w) by ring),
    ← Finset.sum_mul]
  ring

/-- The inverse product `∏ (1 + p^ℓ C_l w)⁻¹` for `2ℓ ≥ e` is `1 - (∑ C_l) p^ℓ w`. -/
lemma prod_inv_eq (h : e ≤ 2 * ℓ) (C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    ∏ l : Fin 3, (1 + pPow p e ℓ * C l * w)⁻¹ = 1 - (∑ l : Fin 3, C l) * pPow p e ℓ * w := by
  have hsq : pPow p e ℓ * pPow p e ℓ = 0 := by
    rw [pPow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rw [show (p ^ ℓ) * (p ^ ℓ) = p ^ (ℓ + ℓ) by ring]
    exact pow_dvd_pow p (by omega)
  have hsqi : ∀ l : Fin 3, (pPow p e ℓ * C l * w) ^ 2 = 0 := by
    intro l
    rw [show (pPow p e ℓ * C l * w) ^ 2 = (pPow p e ℓ * pPow p e ℓ) * (C l * C l * w * w) by ring,
      hsq, zero_mul]
  rw [Finset.prod_congr rfl (fun l _ => inv_one_add_eq_one_sub _ (hsqi l))]
  rw [show (∏ l : Fin 3, (1 - pPow p e ℓ * C l * w))
      = ∏ l : Fin 3, (1 + -(pPow p e ℓ * C l * w)) by
    exact Finset.prod_congr rfl (fun l _ => by ring)]
  rw [prod_one_add_of_pairwise_eq_zero Finset.univ (fun l => -(pPow p e ℓ * C l * w))
    (fun i _ j _ => by
      rw [show -(pPow p e ℓ * C i * w) * -(pPow p e ℓ * C j * w)
          = (pPow p e ℓ * pPow p e ℓ) * (C i * w * C j * w) by ring, hsq, zero_mul])]
  congr 1
  rw [Finset.sum_congr rfl (fun l _ => show -(pPow p e ℓ * C l * w) = -(C l * (pPow p e ℓ * w)) by ring),
    Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

/-- **First-order expansion of the product coordinate** when `2ℓ ≥ e`. -/
lemma prodCoord3_eq_one_add (h : e ≤ 2 * ℓ) (A C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    prodCoord3 p e ℓ A C w
      = 1 + ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)) * pPow p e ℓ * w := by
  have hsq : pPow p e ℓ * pPow p e ℓ = 0 := by
    rw [pPow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rw [show (p ^ ℓ) * (p ^ ℓ) = p ^ (ℓ + ℓ) by ring]
    exact pow_dvd_pow p (by omega)
  have hX := prod_one_add_pPow_eq (p := p) (e := e) (ℓ := ℓ) h A w
  have hY := prod_inv_eq (p := p) (e := e) (ℓ := ℓ) h C w
  rw [prodCoord3, hX, hY]
  have hxy : ((∑ l : Fin 3, A l) * pPow p e ℓ * w) * ((∑ l : Fin 3, C l) * pPow p e ℓ * w) = 0 := by
    rw [show ((∑ l : Fin 3, A l) * pPow p e ℓ * w) * ((∑ l : Fin 3, C l) * pPow p e ℓ * w)
        = ((∑ l : Fin 3, A l) * (∑ l : Fin 3, C l)) * (pPow p e ℓ * pPow p e ℓ) * (w * w) by ring,
      hsq, mul_zero, zero_mul]
  linear_combination -hxy
/-- **The peel lemma for the product coordinate.**  Splitting off the last digit. -/
lemma prodCoord3_peel (hℓ : 1 ≤ ℓ) (hM : 1 ≤ M) (A C : Fin 3 → ZMod (p ^ e))
    (w' t : ZMod (p ^ e)) :
    prodCoord3 p e ℓ A C (w' + ((p : ℕ) ^ (M - 1) : ℕ) * t)
      = prodCoord3 p e ℓ A C w'
        * prodCoord3 p e (ℓ + M - 1)
            (fun l => A l * (1 + pPow p e ℓ * A l * w')⁻¹)
            (fun l => C l * (1 + pPow p e ℓ * C l * w')⁻¹) t := by
  have hℓ' : 1 ≤ ℓ + M - 1 := by omega
  simp only [prodCoord3]
  have hAfac : ∀ l : Fin 3,
      (1 + pPow p e ℓ * A l * (w' + ((p : ℕ) ^ (M - 1) : ℕ) * t))
        = (1 + pPow p e ℓ * A l * w')
          * (1 + pPow p e (ℓ + M - 1) * (A l * (1 + pPow p e ℓ * A l * w')⁻¹) * t) :=
    fun l => one_add_primePow_factor (p := p) (e := e) (ℓ := ℓ) (M := M) hℓ hM (A l) w' t
  have hCfac : ∀ l : Fin 3,
      (1 + pPow p e ℓ * C l * (w' + ((p : ℕ) ^ (M - 1) : ℕ) * t))⁻¹
        = (1 + pPow p e ℓ * C l * w')⁻¹
          * (1 + pPow p e (ℓ + M - 1) * (C l * (1 + pPow p e ℓ * C l * w')⁻¹) * t)⁻¹ := by
    intro l
    rw [one_add_primePow_factor (p := p) (e := e) (ℓ := ℓ) (M := M) hℓ hM (C l) w' t]
    exact inv_mul_eq_mul_inv _ _ (isUnit_one_add_pPow_mul (p := p) (e := e) hℓ (C l) w')
      (isUnit_one_add_pPow_mul (p := p) (e := e) hℓ' _ t)
  rw [Finset.prod_congr rfl (fun l _ => hAfac l), Finset.prod_mul_distrib,
    Finset.prod_congr rfl (fun l _ => hCfac l), Finset.prod_mul_distrib]
  ring
/-- The level sum as a sum over `Finset.range`. -/
lemma levelSum3_eq_range_sum (χ : DirichletCharacter ℂ (p ^ e)) (A C : Fin 3 → ZMod (p ^ e)) :
    levelSum3 p e ℓ M χ A C
      = ∑ n ∈ Finset.range (p ^ M), phase3 p e ℓ χ A C ((n : ℕ) : ZMod (p ^ e)) := by
  rw [levelSum3, Commons.NumberTheory.GaussSum.zmod_sum_range (p ^ M)
    (fun w : ZMod (p ^ M) => phase3 p e ℓ χ A C ((w.val : ℕ) : ZMod (p ^ e)))]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hval : (((n : ZMod (p ^ M))).val : ℕ) = n := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
  rw [hval]

/-- Pure algebra behind the first-order expansion of the derivative. -/
lemma sum_expand_algebra {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (z t : ι → R)
    (P X κ : R) (h : (∑ i ∈ s, z i) - (∑ i ∈ s, t i) = P * κ) :
    (∑ i ∈ s, (z i - P * z i ^ 2 * X)) - (∑ i ∈ s, (t i - P * t i ^ 2 * X))
      = P * κ - P * X * ((∑ i ∈ s, z i ^ 2) - (∑ i ∈ s, t i ^ 2)) := by
  have h1 : P * X * ((∑ i ∈ s, z i ^ 2) - (∑ i ∈ s, t i ^ 2))
      = (∑ i ∈ s, P * X * z i ^ 2) - ∑ i ∈ s, P * X * t i ^ 2 := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [show (∑ i ∈ s, P * z i ^ 2 * X) = ∑ i ∈ s, P * X * z i ^ 2 by
        exact Finset.sum_congr rfl (fun i _ => by ring),
      show (∑ i ∈ s, P * t i ^ 2 * X) = ∑ i ∈ s, P * X * t i ^ 2 by
        exact Finset.sum_congr rfl (fun i _ => by ring)]
  linear_combination h

/-- **Summed first-order expansion of the derivative modulo `p^(ℓ+1)`.** -/
lemma G_expand3 (hℓ : 1 ≤ ℓ) (hd : p ^ (ℓ + 1) ∣ p ^ e) (κ : ℕ)
    (A C : Fin 3 → ZMod (p ^ e))
    (hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (x : ZMod (p ^ e)) :
    ZMod.castHom hd (ZMod (p ^ (ℓ + 1)))
        ((∑ l : Fin 3, A l * (1 + pPow p e ℓ * A l * x)⁻¹)
          - (∑ l : Fin 3, C l * (1 + pPow p e ℓ * C l * x)⁻¹))
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ)
        * (((κ : ℕ) : ZMod (p ^ (ℓ + 1)))
          - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) x
            * ZMod.castHom hd (ZMod (p ^ (ℓ + 1)))
                ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2))) := by
  rw [map_sub, map_sum, map_sum]
  rw [Finset.sum_congr rfl (fun l _ => castHom_inv_expand hℓ hd (A l) x)]
  rw [Finset.sum_congr rfl (fun l _ => castHom_inv_expand hℓ hd (C l) x)]
  simp only [map_sub, map_sum, map_pow]
  have hkey : (∑ l : Fin 3, ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (A l))
      - (∑ l : Fin 3, ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (C l))
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ)
        * ((κ : ℕ) : ZMod (p ^ (ℓ + 1))) := by
    rw [← map_sum, ← map_sum, ← map_sub, hsum, map_natCast, castHom_pPow hd]
    simp only [pPow]; push_cast; ring
  rw [sum_expand_algebra Finset.univ (fun l => ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (A l))
    (fun l => ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (C l))
    (ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ))
    (ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) x) (κ : ZMod (p ^ (ℓ + 1))) hkey]
  ring
/-- The degree-`2` coefficient of the product coordinate (`r = 3` case). -/
noncomputable def K2_3 (p e : ℕ) (A C : Fin 3 → ZMod (p ^ e)) : ZMod (p ^ e) :=
  (A 0 * A 1 + A 0 * A 2 + A 1 * A 2)
    + (C 0 ^ 2 + C 1 ^ 2 + C 2 ^ 2)
    + (C 0 * C 1 + C 0 * C 2 + C 1 * C 2)
    - (A 0 + A 1 + A 2) * (C 0 + C 1 + C 2)

/-- Expansion of a product of three `(1 + P A_l w)` when `P ^ 3 = 0`. -/
lemma prod3_pA {R : Type*} [CommRing R] (P : R) (A : Fin 3 → R) (w : R) (h : P ^ 3 = 0) :
    ∏ l : Fin 3, (1 + P * A l * w)
      = 1 + P * (A 0 + A 1 + A 2) * w + P ^ 2 * (A 0 * A 1 + A 0 * A 2 + A 1 * A 2) * w ^ 2 := by
  rw [Fin.prod_univ_three]
  ring_nf
  simp only [h, mul_zero, zero_mul, add_zero]

/-- Expansion of a product of three `(1 + P C_l w)⁻¹` when `P ^ 3 = 0`. -/
lemma prod3_pA_inv {N : ℕ} (P : ZMod N) (C : Fin 3 → ZMod N) (w : ZMod N) (h : P ^ 3 = 0) :
    ∏ l : Fin 3, (1 + P * C l * w)⁻¹
      = 1 - P * (C 0 + C 1 + C 2) * w
        + P ^ 2 * (C 0 ^ 2 + C 1 ^ 2 + C 2 ^ 2 + C 0 * C 1 + C 0 * C 2 + C 1 * C 2) * w ^ 2 := by
  have hinv : ∀ C : ZMod N, (1 + P * C * w)⁻¹ = 1 - P * C * w + (P * C * w) ^ 2 := by
    intro C
    have h3 : (P * C * w) ^ 3 = 0 := by linear_combination (C ^ 3 * w ^ 3) * h
    refine ZMod.inv_eq_of_mul_eq_one N _ _ ?_
    rw [show (1 + P * C * w) * (1 - P * C * w + (P * C * w) ^ 2) = 1 + (P * C * w) ^ 3 by ring,
      h3, add_zero]
  have h4 : P ^ 4 = 0 := by rw [show P ^ 4 = P ^ 3 * P by ring, h, zero_mul]
  have h5 : P ^ 5 = 0 := by rw [show P ^ 5 = P ^ 4 * P by ring, h4, zero_mul]
  have h6 : P ^ 6 = 0 := by rw [show P ^ 6 = P ^ 5 * P by ring, h5, zero_mul]
  rw [Finset.prod_congr rfl (fun l _ => hinv (C l)), Fin.prod_univ_three]
  ring_nf
  simp only [h, h4, h5, h6, mul_zero, zero_mul, add_zero, sub_zero]

/-- **Second-order expansion of the product coordinate** when `3ℓ ≥ e`. -/
lemma prodCoord3_quad (hℓ : 1 ≤ ℓ) (h : e ≤ 3 * ℓ) (κ : ZMod (p ^ e))
    (A C : Fin 3 → ZMod (p ^ e))
    (hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = pPow p e ℓ * κ) (w : ZMod (p ^ e)) :
    prodCoord3 p e ℓ A C w
      = 1 + (pPow p e ℓ * pPow p e ℓ) * (κ * w + K2_3 p e A C * w ^ 2) := by
  have hP3 : (pPow p e ℓ) ^ 3 = 0 := by
    rw [pPow, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    rw [show (p ^ ℓ) ^ 3 = p ^ (3 * ℓ) by ring]
    exact pow_dvd_pow p h
  have hsum' : (A 0 + A 1 + A 2) - (C 0 + C 1 + C 2) = pPow p e ℓ * κ := by
    rw [← Fin.sum_univ_three A, ← Fin.sum_univ_three C]; exact hsum
  have hSA : (A 0 + A 1 + A 2) = (C 0 + C 1 + C 2) + pPow p e ℓ * κ := by
    linear_combination hsum'
  have h4 : (pPow p e ℓ) ^ 4 = 0 := by
    rw [show (pPow p e ℓ) ^ 4 = (pPow p e ℓ) ^ 3 * pPow p e ℓ by ring, hP3, zero_mul]
  have h5 : (pPow p e ℓ) ^ 5 = 0 := by
    rw [show (pPow p e ℓ) ^ 5 = (pPow p e ℓ) ^ 4 * pPow p e ℓ by ring, h4, zero_mul]
  have h6 : (pPow p e ℓ) ^ 6 = 0 := by
    rw [show (pPow p e ℓ) ^ 6 = (pPow p e ℓ) ^ 5 * pPow p e ℓ by ring, h5, zero_mul]
  rw [prodCoord3, prod3_pA (pPow p e ℓ) A w hP3, prod3_pA_inv (pPow p e ℓ) C w hP3,
    K2_3, hSA]
  ring_nf
  simp only [hP3, h4, h5, h6, mul_zero, zero_mul, add_zero, sub_zero]

/-- The quadratic coefficient is (up to sign) half the non-degeneracy invariant. -/
lemma two_mul_K2_generic {R : Type*} [CommRing R] (A C : Fin 3 → R)
    (h : A 0 + A 1 + A 2 = C 0 + C 1 + C 2) :
    2 * ((A 0 * A 1 + A 0 * A 2 + A 1 * A 2)
        + (C 0 ^ 2 + C 1 ^ 2 + C 2 ^ 2) + (C 0 * C 1 + C 0 * C 2 + C 1 * C 2)
        - (A 0 + A 1 + A 2) * (C 0 + C 1 + C 2))
      = -((A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) - (C 0 ^ 2 + C 1 ^ 2 + C 2 ^ 2)) := by
  linear_combination (A 0 + A 1 + A 2 - (C 0 + C 1 + C 2)) * h
/-- **Base case `M = 1`.**  With a single remaining digit `e = 2ℓ + 1`, the level-`ℓ` sum is a
non-degenerate quadratic Gauss sum modulo `p`, hence at most `2 √p`. -/
theorem levelSum_base_one3 (p e ℓ : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hℓ : 1 ≤ ℓ) (heq : e = 2 * ℓ + 1) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A C : Fin 3 → ZMod (p ^ e)) (κ : ℕ)
    (hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (hnd : ¬ (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val) :
    ‖levelSum3 p e ℓ 1 χ A C‖ ≤ 2 * Real.sqrt p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have he1 : 1 ≤ e := by omega
  have h3 : e ≤ 3 * ℓ := by omega
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p he1
  have h2ℓe : 2 * ℓ = e - 1 := by omega
  -- the primitive `p`-th root of unity
  set ζ : ℂ := χ (1 + pPow p e (e - 1)) with hζdef
  have hζprim : IsPrimitiveRoot ζ p := by
    rw [hζdef, pPow]
    simpa using chi_one_add_primePow_isPrimitiveRoot p e hp2 (by omega) χ hχ
  have hζp : ζ ^ p = 1 := hζprim.pow_eq_one
  set K2 : ZMod (p ^ e) := K2_3 p e A C with hK2def
  -- criticality modulo `p`
  have hcritp : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l)) = 0 := by
    rw [hsum, map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_of_dvd_left (by simpa using (pow_dvd_pow p hℓ : p ^ 1 ∣ p ^ ℓ)) κ
  have hcrit : ZMod.castHom hdiv1 (ZMod p) (A 0) + ZMod.castHom hdiv1 (ZMod p) (A 1)
      + ZMod.castHom hdiv1 (ZMod p) (A 2)
      = ZMod.castHom hdiv1 (ZMod p) (C 0) + ZMod.castHom hdiv1 (ZMod p) (C 1)
        + ZMod.castHom hdiv1 (ZMod p) (C 2) := by
    have h := hcritp
    rw [map_sub, map_sum, map_sum,
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (A l)),
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (C l))] at h
    exact sub_eq_zero.mp h
  -- the reduction of `K2`
  have hK2cast : ZMod.castHom hdiv1 (ZMod p) K2
      = (ZMod.castHom hdiv1 (ZMod p) (A 0) * ZMod.castHom hdiv1 (ZMod p) (A 1)
            + ZMod.castHom hdiv1 (ZMod p) (A 0) * ZMod.castHom hdiv1 (ZMod p) (A 2)
            + ZMod.castHom hdiv1 (ZMod p) (A 1) * ZMod.castHom hdiv1 (ZMod p) (A 2))
          + (ZMod.castHom hdiv1 (ZMod p) (C 0) ^ 2 + ZMod.castHom hdiv1 (ZMod p) (C 1) ^ 2
              + ZMod.castHom hdiv1 (ZMod p) (C 2) ^ 2)
          + (ZMod.castHom hdiv1 (ZMod p) (C 0) * ZMod.castHom hdiv1 (ZMod p) (C 1)
            + ZMod.castHom hdiv1 (ZMod p) (C 0) * ZMod.castHom hdiv1 (ZMod p) (C 2)
            + ZMod.castHom hdiv1 (ZMod p) (C 1) * ZMod.castHom hdiv1 (ZMod p) (C 2))
          - (ZMod.castHom hdiv1 (ZMod p) (A 0) + ZMod.castHom hdiv1 (ZMod p) (A 1)
              + ZMod.castHom hdiv1 (ZMod p) (A 2))
            * (ZMod.castHom hdiv1 (ZMod p) (C 0) + ZMod.castHom hdiv1 (ZMod p) (C 1)
              + ZMod.castHom hdiv1 (ZMod p) (C 2)) := by
    rw [hK2def]
    simp only [K2_3, map_add, map_sub, map_mul, map_pow]
  have hΔcast : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2))
      = (ZMod.castHom hdiv1 (ZMod p) (A 0) ^ 2 + ZMod.castHom hdiv1 (ZMod p) (A 1) ^ 2
          + ZMod.castHom hdiv1 (ZMod p) (A 2) ^ 2)
        - (ZMod.castHom hdiv1 (ZMod p) (C 0) ^ 2 + ZMod.castHom hdiv1 (ZMod p) (C 1) ^ 2
          + ZMod.castHom hdiv1 (ZMod p) (C 2) ^ 2) := by
    rw [map_sub, map_sum, map_sum,
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (A l ^ 2)),
      Fin.sum_univ_three (fun l => ZMod.castHom hdiv1 (ZMod p) (C l ^ 2)),
      map_pow, map_pow, map_pow, map_pow, map_pow, map_pow]
  have h2ne : (2 : ZMod p) ≠ 0 := GaussSum.zmod_two_ne_zero p hp2
  have hΔne : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2)) ≠ 0 := by
    intro h
    exact hnd ((castHom_eq_zero_iff_dvd_val_one hdiv1 _).mp h)
  have hK2cast' : 2 * ZMod.castHom hdiv1 (ZMod p) K2
      = -ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2)) := by
    rw [hK2cast, hΔcast]
    exact two_mul_K2_generic (fun l => ZMod.castHom hdiv1 (ZMod p) (A l))
      (fun l => ZMod.castHom hdiv1 (ZMod p) (C l)) hcrit
  have hK2castne : ZMod.castHom hdiv1 (ZMod p) K2 ≠ 0 := by
    intro h
    have hh := hK2cast'
    rw [h, mul_zero] at hh
    exact hΔne (neg_eq_zero.mp hh.symm)
  have hK2ne : ¬ (p : ℤ) ∣ ((K2.val : ℕ) : ℤ) := by
    intro hcon
    have hpvd : p ∣ K2.val := by exact_mod_cast hcon
    exact hK2castne ((castHom_eq_zero_iff_dvd_val_one hdiv1 K2).mpr hpvd)
  -- the second-order expansion of the product coordinate
  have hsum' : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = pPow p e ℓ * ((κ : ℕ) : ZMod (p ^ e)) := by
    rw [hsum, pPow]; push_cast; ring
  have hprod : ∀ w : ZMod (p ^ e), prodCoord3 p e ℓ A C w
      = 1 + pPow p e (e - 1) * (((κ : ℕ) : ZMod (p ^ e)) * w + K2 * w ^ 2) := by
    intro w
    have hPe : pPow p e ℓ * pPow p e ℓ = pPow p e (e - 1) := by
      rw [pPow_mul_pPow, show ℓ + ℓ = e - 1 by omega]
    rw [prodCoord3_quad (p := p) (e := e) (ℓ := ℓ) hℓ h3 ((κ : ℕ) : ZMod (p ^ e)) A C hsum' w,
      hK2def, hPe]
  -- the character value
  have hterm : ∀ n : ℕ, phase3 p e ℓ χ A C ((n : ℕ) : ZMod (p ^ e))
      = ζ ^ (((κ : ℤ) * (n : ZMod p)
          - ((-((K2.val : ℕ) : ℤ))) * (n : ZMod p) ^ 2 : ZMod p)).val := by
    intro n
    have hphase : phase3 p e ℓ χ A C ((n : ℕ) : ZMod (p ^ e))
        = χ (1 + pPow p e (e - 1) * (((κ : ℕ) : ZMod (p ^ e)) * ((n : ℕ) : ZMod (p ^ e))
            + K2 * ((n : ℕ) : ZMod (p ^ e)) ^ 2)) := by
      rw [phase3_eq_chi_prodCoord3 (p := p) (e := e) (ℓ := ℓ) hℓ χ A C, hprod]
    rw [hphase, chi_top_level (p := p) (e := e) (by omega) χ, hζdef]
    refine pow_eq_pow_of_modEq ?_ hζp
    have hred : ZMod.castHom hdiv1 (ZMod p)
        (((κ : ℕ) : ZMod (p ^ e)) * ((n : ℕ) : ZMod (p ^ e))
          + K2 * ((n : ℕ) : ZMod (p ^ e)) ^ 2)
        = (κ : ZMod p) * (n : ZMod p) + (K2.val : ZMod p) * (n : ZMod p) ^ 2 := by
      rw [map_add, map_mul, map_mul, map_pow]
      simp only [map_natCast]
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    have hWeq : (((κ : ℤ) * (n : ZMod p)
          - ((-((K2.val : ℕ) : ℤ))) * (n : ZMod p) ^ 2 : ZMod p))
        = (κ : ZMod p) * (n : ZMod p) + (K2.val : ZMod p) * (n : ZMod p) ^ 2 := by
      push_cast; ring
    rw [hWeq, ← hred, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact (Nat.mod_modEq _ _).symm
  rw [levelSum3_eq_range_sum, show p ^ 1 = p by norm_num,
    Finset.sum_congr rfl (fun n _ => hterm n)]
  rw [← Commons.NumberTheory.GaussSum.zmod_sum_range p
    (fun x : ZMod p => ζ ^ ((((κ : ℤ) * x - ((-((K2.val : ℕ) : ℤ))) * x ^ 2 : ZMod p))).val)]
  refine le_of_eq_of_le ?_ (Commons.NumberTheory.GaussSum.quadratic_gauss_primitive_root p hp2 ζ
    hζprim ((κ : ℤ)) ((-((K2.val : ℕ) : ℤ))) (fun h => hK2ne (by simpa using h)))
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  push_cast
  ring
/-- One stationary-phase step: the level-`ℓ` sum over `ZMod (p^M)` equals `p` times the
level-`(ℓ+1)` sum over `ZMod (p^(M-2))`, with residual units `A_l (1 + p^ℓ A_l c)⁻¹`. -/
theorem level_step3 (p e ℓ M : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e)
    (hℓ : 1 ≤ ℓ) (hM : 2 ≤ M) (heq : e = 2 * ℓ + M)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A C : Fin 3 → ZMod (p ^ e)) (κ : ℕ)
    (hsum : (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (hnd : ¬ (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val) :
    ∃ (A' C' : Fin 3 → ZMod (p ^ e)) (κ' : ℕ),
      (∑ l : Fin 3, A' l) - (∑ l : Fin 3, C' l) = ((p ^ (ℓ + 1) * κ' : ℕ) : ZMod (p ^ e))
      ∧ ¬ (p : ℕ) ∣ ((∑ l : Fin 3, A' l ^ 2) - (∑ l : Fin 3, C' l ^ 2) : ZMod (p ^ e)).val
      ∧ ‖levelSum3 p e ℓ M χ A C‖
          = (p : ℝ) * ‖levelSum3 p e (ℓ + 1) (M - 2) χ A' C'‖ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p (show 1 ≤ e by omega)
  have hdiv' : p ^ (ℓ + 1) ∣ p ^ e := pow_dvd_pow p (by omega)
  have h2ℓ : 2 * ℓ ≤ e := by omega
  have hℓ'e : ℓ + M - 1 = e - ℓ - 1 := by omega
  have h2ℓ' : e ≤ 2 * (ℓ + M - 1) := by omega
  set Δ : ZMod (p ^ e) := (∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) with hΔdef
  set δ : ZMod p := ZMod.castHom hdiv1 (ZMod p) Δ with hδdef
  have hδne : δ ≠ 0 := by
    intro h
    apply hnd
    rw [hΔdef, ← castHom_eq_zero_iff_dvd_val_one hdiv1
      ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2))]
    exact h
  -- ### the localisation class
  set c₀ : ℕ := ((κ : ZMod p) * δ⁻¹).val with hc₀def
  have hc₀lt : c₀ < p := ZMod.val_lt _
  have hc₀spec : (c₀ : ZMod p) = (κ : ZMod p) * δ⁻¹ := ZMod.natCast_zmod_val _
  set xc : ZMod (p ^ e) := ((c₀ : ℕ) : ZMod (p ^ e)) with hxcdef
  have hcond : ∀ n' : ℕ,
      (p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - ((n' : ℕ) : ZMod (p ^ e)) * Δ).val) ↔ n' % p = c₀ := by
    intro n'
    rw [← castHom_eq_zero_iff_dvd_val_one hdiv1
      ((((κ : ℕ)) : ZMod (p ^ e)) - ((n' : ℕ) : ZMod (p ^ e)) * Δ)]
    rw [map_sub, map_mul, map_natCast, map_natCast, ← hδdef]
    constructor
    · intro h
      have h2 : ((n' : ZMod p)) * δ = (κ : ZMod p) := (sub_eq_zero.mp h).symm
      have h3 : (n' : ZMod p) = (κ : ZMod p) * δ⁻¹ := by
        rw [← h2]
        rw [show (n' : ZMod p) * δ * δ⁻¹ = (n' : ZMod p) * (δ * δ⁻¹) by ring,
          mul_inv_cancel₀ hδne, mul_one]
      have h4 : (n' : ZMod p) = (c₀ : ZMod p) := by rw [h3, hc₀spec]
      have h5 := congrArg ZMod.val h4
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hc₀lt] at h5
      exact h5
    · intro h
      have h2 : (n' : ZMod p) = (c₀ : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' n' c₀ p).mpr (by rw [h, Nat.mod_eq_of_lt hc₀lt])
      rw [sub_eq_zero, h2, hc₀spec, mul_assoc, inv_mul_cancel₀ hδne, mul_one]
  have hcond2 : ∀ n' : ℕ,
      (p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * ((n' : ℕ) : ZMod (p ^ e))).val) ↔ n' % p = c₀ := by
    intro n'
    rw [show ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * ((n' : ℕ) : ZMod (p ^ e)))
        = ((((κ : ℕ)) : ZMod (p ^ e)) - ((n' : ℕ) : ZMod (p ^ e)) * Δ) by ring]
    exact hcond n'
  -- ### the residual units and the derivative
  set θA : ZMod (p ^ e) → Fin 3 → ZMod (p ^ e) :=
    fun x l => A l * (1 + pPow p e ℓ * A l * x)⁻¹ with hθA
  set θC : ZMod (p ^ e) → Fin 3 → ZMod (p ^ e) :=
    fun x l => C l * (1 + pPow p e ℓ * C l * x)⁻¹ with hθC
  set Gfun : ZMod (p ^ e) → ZMod (p ^ e) :=
    fun x => (∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l) with hGfun
  set ζ : ℂ := χ (1 + pPow p e (e - 1)) with hζdef
  have hζprim : IsPrimitiveRoot ζ p := by
    rw [hζdef, pPow]
    simpa using chi_one_add_primePow_isPrimitiveRoot p e hp2 (by omega) χ hχ
  -- ### the expansion of the derivative
  have hexpand : ∀ x : ZMod (p ^ e),
      pPow p e (ℓ + M - 1) * Gfun x
        = pPow p e (e - 1) * ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x) := by
    intro x
    have h1 : ∀ l : Fin 3, pPow p e (ℓ + M - 1) * θA x l
        = pPow p e (ℓ + M - 1) * A l - pPow p e (e - 1) * A l ^ 2 * x := by
      intro l
      rw [hℓ'e]
      exact pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ (A l) x
    have h2 : ∀ l : Fin 3, pPow p e (ℓ + M - 1) * θC x l
        = pPow p e (ℓ + M - 1) * C l - pPow p e (e - 1) * C l ^ 2 * x := by
      intro l
      rw [hℓ'e]
      exact pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ (C l) x
    have hpp : pPow p e (ℓ + M - 1) * ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l))
        = pPow p e (e - 1) * ((κ : ℕ) : ZMod (p ^ e)) := by
      rw [hsum, pPow, pPow]
      push_cast
      rw [← mul_assoc, ← pow_add, show ℓ + M - 1 + ℓ = e - 1 by omega]
    have hgx : Gfun x = (∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l) := by rw [hGfun]
    rw [hgx, mul_sub, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_congr rfl (fun l _ => h2 l)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [show (∑ l : Fin 3, pPow p e (ℓ + M - 1) * A l)
        = pPow p e (ℓ + M - 1) * (∑ l : Fin 3, A l) by rw [Finset.mul_sum]]
    rw [show (∑ l : Fin 3, pPow p e (ℓ + M - 1) * C l)
        = pPow p e (ℓ + M - 1) * (∑ l : Fin 3, C l) by rw [Finset.mul_sum]]
    rw [show (∑ l : Fin 3, pPow p e (e - 1) * A l ^ 2 * x)
        = pPow p e (e - 1) * (∑ l : Fin 3, A l ^ 2) * x by
      rw [Finset.sum_congr rfl (fun l _ => show pPow p e (e - 1) * A l ^ 2 * x
        = (pPow p e (e - 1) * x) * A l ^ 2 by ring), ← Finset.mul_sum]; ring]
    rw [show (∑ l : Fin 3, pPow p e (e - 1) * C l ^ 2 * x)
        = pPow p e (e - 1) * (∑ l : Fin 3, C l ^ 2) * x by
      rw [Finset.sum_congr rfl (fun l _ => show pPow p e (e - 1) * C l ^ 2 * x
        = (pPow p e (e - 1) * x) * C l ^ 2 by ring), ← Finset.mul_sum]; ring]
    rw [hΔdef]
    rw [show pPow p e (ℓ + M - 1) * (∑ l : Fin 3, A l)
          - (pPow p e (e - 1) * (∑ l : Fin 3, A l ^ 2)) * x
          - (pPow p e (ℓ + M - 1) * (∑ l : Fin 3, C l)
              - (pPow p e (e - 1) * (∑ l : Fin 3, C l ^ 2)) * x)
        = pPow p e (ℓ + M - 1) * ((∑ l : Fin 3, A l) - (∑ l : Fin 3, C l))
          - pPow p e (e - 1) * ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2)) * x by ring]
    rw [hpp]
    ring
  -- ### the character value of the inner exponential
  have hη : ∀ x : ZMod (p ^ e),
      χ (1 + pPow p e (ℓ + M - 1) * Gfun x)
        = ζ ^ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val := by
    intro x
    rw [hexpand x, chi_top_level (p := p) (e := e) (by omega) χ]
  have hηpow : ∀ x : ZMod (p ^ e),
      (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ p = 1 := by
    intro x
    rw [hη x, ← pow_mul, mul_comm, pow_mul, hζprim.pow_eq_one, one_pow]
  -- ### the inner sum over the last digit
  have hinner : ∀ x : ZMod (p ^ e),
      (∑ t ∈ Finset.range p,
          χ (prodCoord3 p e (ℓ + M - 1) (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e))))
        = (p : ℂ) * (if p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val then 1 else 0) := by
    intro x
    have hpc : ∀ t ∈ Finset.range p,
        χ (prodCoord3 p e (ℓ + M - 1) (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)))
          = (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ t := by
      intro t ht
      have hgt : Gfun x = (∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l) := by rw [hGfun]
      calc χ (prodCoord3 p e (ℓ + M - 1) (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)))
          = χ ((1 + pPow p e (ℓ + M - 1) * Gfun x) ^ t) := by
            rw [prodCoord3_eq_one_add (p := p) (e := e) (ℓ := ℓ + M - 1) h2ℓ'
              (θA x) (θC x) ((t : ℕ) : ZMod (p ^ e)), hgt]
            rw [show ((∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l)) * pPow p e (ℓ + M - 1)
                  * ((t : ℕ) : ZMod (p ^ e))
                = (t : ZMod (p ^ e)) * (pPow p e (ℓ + M - 1)
                  * ((∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l))) by ring]
            rw [← one_add_pPow_pow (p := p) (e := e) (ℓ := ℓ + M - 1) h2ℓ'
              ((∑ l : Fin 3, θA x l) - (∑ l : Fin 3, θC x l)) t]
        _ = (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ t := by rw [map_pow]
    rw [Finset.sum_congr rfl hpc, sum_range_pow_eq p (hηpow x)]
    by_cases h : p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val
    · have h2 : χ (1 + pPow p e (ℓ + M - 1) * Gfun x) = 1 := by
        rw [hη x, hζprim.pow_eq_one_iff_dvd]; exact h
      rw [if_pos h2, if_pos h, mul_one]
    · have h2 : χ (1 + pPow p e (ℓ + M - 1) * Gfun x) ≠ 1 := by
        intro hh
        exact h ((hζprim.pow_eq_one_iff_dvd _).mp (by rw [← hη x]; exact hh))
      rw [if_neg h2, if_neg h, mul_zero]
  -- ### the two-level decomposition of the level sum
  have hdecomp : levelSum3 p e ℓ M χ A C
      = ∑ n' ∈ Finset.range (p ^ (M - 1)),
          χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e)))
            * ((p : ℂ) * (if p ∣ ((((κ : ℕ)) : ZMod (p ^ e))
                - Δ * ((n' : ℕ) : ZMod (p ^ e))).val then 1 else 0)) := by
    rw [levelSum3_eq_range_sum]
    have h1 : ∀ n ∈ Finset.range (p ^ M),
        phase3 p e ℓ χ A C ((n : ℕ) : ZMod (p ^ e))
          = χ (prodCoord3 p e ℓ A C ((n : ℕ) : ZMod (p ^ e))) := by
      intro n hn
      exact phase3_eq_chi_prodCoord3 (p := p) (e := e) (ℓ := ℓ) hℓ χ A C _
    rw [Finset.sum_congr rfl h1]
    have h2 : p ^ M = p ^ (M - 1) * p := by
      conv_lhs => rw [show M = (M - 1) + 1 by omega]
      rw [pow_succ]
    rw [h2]
    rw [Commons.Algebra.BigOperators.sum_range_mul_eq
      (fun n => χ (prodCoord3 p e ℓ A C ((n : ℕ) : ZMod (p ^ e)))) (p ^ (M - 1)) p]
    refine Finset.sum_congr rfl fun n' hn' => ?_
    have hpeel : ∀ t ∈ Finset.range p,
        χ (prodCoord3 p e ℓ A C (((n' + p ^ (M - 1) * t : ℕ)) : ZMod (p ^ e)))
          = χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e)))
            * χ (prodCoord3 p e (ℓ + M - 1) (θA ((n' : ℕ) : ZMod (p ^ e)))
                (θC ((n' : ℕ) : ZMod (p ^ e))) ((t : ℕ) : ZMod (p ^ e))) := by
      intro t ht
      rw [show ((n' + p ^ (M - 1) * t : ℕ) : ZMod (p ^ e))
          = ((n' : ℕ) : ZMod (p ^ e)) + ((p : ℕ) ^ (M - 1) : ℕ) * ((t : ℕ) : ZMod (p ^ e)) by
        push_cast; ring]
      rw [prodCoord3_peel (p := p) (e := e) (ℓ := ℓ) (M := M) hℓ (by omega) A C _ _,
        map_mul]
    rw [Finset.sum_congr rfl hpeel, ← Finset.mul_sum, hinner ((n' : ℕ) : ZMod (p ^ e))]
  -- ### restrict to the localisation class
  have hclass : levelSum3 p e ℓ M χ A C
      = (p : ℂ) * ∑ n' ∈ (Finset.range (p ^ (M - 1))).filter (fun n' => n' % p = c₀),
          χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e))) := by
    rw [hdecomp]
    rw [show (∑ n' ∈ Finset.range (p ^ (M - 1)),
          χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e)))
            * ((p : ℂ) * (if p ∣ ((((κ : ℕ)) : ZMod (p ^ e))
                - Δ * ((n' : ℕ) : ZMod (p ^ e))).val then 1 else 0)))
        = ∑ n' ∈ Finset.range (p ^ (M - 1)),
          (if n' % p = c₀ then (p : ℂ) * χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e)))
            else 0) by
      refine Finset.sum_congr rfl fun n' hn' => ?_
      by_cases h : n' % p = c₀
      · rw [if_pos ((hcond2 n').mpr h), if_pos h]; ring
      · rw [if_neg (fun hh => h ((hcond2 n').mp hh)), if_neg h]; ring]
    rw [← Finset.sum_filter, Finset.mul_sum]
  -- ### the residual sum
  have hresidual :
      (∑ n' ∈ (Finset.range (p ^ (M - 1))).filter (fun n' => n' % p = c₀),
          χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e))))
        = χ (prodCoord3 p e ℓ A C xc)
          * levelSum3 p e (ℓ + 1) (M - 2) χ (θA xc) (θC xc) := by
    rw [show p ^ (M - 1) = p ^ ((M - 2) + 1) by congr 1; omega]
    rw [sum_range_filter_mod_eq p c₀ (M - 2) hc₀lt
      (fun n' => χ (prodCoord3 p e ℓ A C ((n' : ℕ) : ZMod (p ^ e))))]
    rw [levelSum3_eq_range_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show ((c₀ + p * m : ℕ) : ZMod (p ^ e))
        = xc + ((p : ℕ) ^ 1 : ℕ) * ((m : ℕ) : ZMod (p ^ e)) by
      rw [hxcdef]; push_cast; ring]
    rw [prodCoord3_peel (p := p) (e := e) (ℓ := ℓ) (M := 2) hℓ (by norm_num) A C _ _,
      map_mul]
    rw [show ℓ + 2 - 1 = ℓ + 1 by omega,
      phase3_eq_chi_prodCoord3 (p := p) (e := e) (ℓ := ℓ + 1) (by omega) χ
        (θA xc) (θC xc) ((m : ℕ) : ZMod (p ^ e))]
  -- ### the invariant and the norm
  have hGlocal : p ^ (ℓ + 1) ∣ (Gfun xc).val := by
    have hGe := G_expand3 (p := p) (e := e) (ℓ := ℓ) hℓ hdiv' κ A C hsum xc
    rw [castHom_pPow hdiv'] at hGe
    have hL : ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1)))
        ((∑ l : Fin 3, A l * (1 + pPow p e ℓ * A l * xc)⁻¹)
          - (∑ l : Fin 3, C l * (1 + pPow p e ℓ * C l * xc)⁻¹))
        = ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) (Gfun xc) := by
      rw [hGfun]
    rw [hL] at hGe
    have hw : ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ)
        = (((κ : ℕ)) : ZMod (p ^ (ℓ + 1))) - ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) xc
            * ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) Δ := by
      rw [map_sub, map_mul, map_natCast]
    rw [← hw] at hGe
    have hy : p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ).val := by
      rw [hxcdef]
      exact (hcond c₀).mpr (Nat.mod_eq_of_lt hc₀lt)
    have hval : p ∣ (ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1)))
        ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ)).val := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
      have h1 : ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ).val % p ^ (ℓ + 1) ≡ 0 [MOD p] :=
        (Nat.ModEq.of_dvd (show (p : ℕ) ∣ p ^ (ℓ + 1) by
            simpa using pow_dvd_pow p (show 1 ≤ ℓ + 1 by omega))
          (Nat.mod_modEq _ _)).trans (Nat.modEq_zero_iff_dvd.mpr hy)
      exact Nat.modEq_zero_iff_dvd.mp h1
    have hzero : pPow p (ℓ + 1) ℓ * ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1)))
        ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ) = 0 :=
      (pPow_mul_eq_zero_iff hp hℓ _).mpr hval
    rw [hzero] at hGe
    rw [← castHom_eq_zero_iff_dvd_val hdiv' (Gfun xc)]
    exact hGe
  have hnd' : ¬ (p : ℕ) ∣ ((∑ l : Fin 3, θA xc l ^ 2) - (∑ l : Fin 3, θC xc l ^ 2)).val := by
    have hθ : ∀ U : ZMod (p ^ e),
        ZMod.castHom hdiv1 (ZMod p) (U * (1 + pPow p e ℓ * U * xc)⁻¹)
          = ZMod.castHom hdiv1 (ZMod p) U := by
      intro U
      have h1 : ZMod.castHom hdiv1 (ZMod p) (1 + pPow p e ℓ * U * xc) = 1 := by
        rw [map_add, map_one, map_mul, map_mul, pPow, map_natCast]
        have hz : (((p : ℕ) ^ ℓ : ℕ) : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          simpa using (pow_dvd_pow p hℓ : p ^ 1 ∣ p ^ ℓ)
        rw [hz, zero_mul, zero_mul, add_zero]
      have h2 : ZMod.castHom hdiv1 (ZMod p) ((1 + pPow p e ℓ * U * xc)⁻¹) = 1 := by
        have hu : (1 + pPow p e ℓ * U * xc) * (1 + pPow p e ℓ * U * xc)⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (isUnit_one_add_pPow_mul hℓ U xc)
        have h3 := congrArg (ZMod.castHom hdiv1 (ZMod p)) hu
        rw [map_mul, h1, map_one, one_mul] at h3
        exact h3
      rw [map_mul, h2, mul_one]
    have hθA' : ∀ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (θA xc l)
        = ZMod.castHom hdiv1 (ZMod p) (A l) := by
      intro l
      rw [show θA xc l = A l * (1 + pPow p e ℓ * A l * xc)⁻¹ by rw [hθA]]
      exact hθ (A l)
    have hθC' : ∀ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (θC xc l)
        = ZMod.castHom hdiv1 (ZMod p) (C l) := by
      intro l
      rw [show θC xc l = C l * (1 + pPow p e ℓ * C l * xc)⁻¹ by rw [hθC]]
      exact hθ (C l)
    have hA2 : (∑ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (θA xc l ^ 2))
        = ∑ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (A l ^ 2) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_pow, map_pow, hθA' l]
    have hC2 : (∑ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (θC xc l ^ 2))
        = ∑ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (C l ^ 2) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_pow, map_pow, hθC' l]
    have hred : ZMod.castHom hdiv1 (ZMod p)
        ((∑ l : Fin 3, θA xc l ^ 2) - (∑ l : Fin 3, θC xc l ^ 2)) = δ := by
      rw [hδdef, hΔdef, map_sub, map_sum, map_sum, map_sub, map_sum, map_sum, hA2, hC2]
    intro hcon
    have h0 : ZMod.castHom hdiv1 (ZMod p) ((∑ l : Fin 3, θA xc l ^ 2) - (∑ l : Fin 3, θC xc l ^ 2))
        = 0 := (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mpr hcon
    exact hδne (by rw [← hred]; exact h0)
  -- ### conclusion
  obtain ⟨κ', hκ'⟩ := hGlocal
  refine ⟨θA xc, θC xc, κ', ?_, hnd', ?_⟩
  · change Gfun xc = ((p ^ (ℓ + 1) * κ' : ℕ) : ZMod (p ^ e))
    rw [← ZMod.natCast_zmod_val (Gfun xc), hκ']
  · rw [hclass, hresidual, norm_mul, norm_mul]
    have hnr : ‖χ (prodCoord3 p e ℓ A C xc)‖ = 1 := by
      rw [← phase3_eq_chi_prodCoord3 (p := p) (e := e) (ℓ := ℓ) hℓ χ A C]
      simp only [phase3, norm_mul, norm_prod, Complex.norm_conj]
      have h1 : ∀ l : Fin 3, ‖χ (1 + pPow p e ℓ * A l * xc)‖ = 1 :=
        fun l => norm_apply_unit χ (isUnit_one_add_pPow_mul hℓ (A l) xc).unit
      have h2 : ∀ l : Fin 3, ‖χ (1 + pPow p e ℓ * C l * xc)‖ = 1 :=
        fun l => norm_apply_unit χ (isUnit_one_add_pPow_mul hℓ (C l) xc).unit
      rw [Finset.prod_congr rfl (fun l _ => h1 l), Finset.prod_congr rfl (fun l _ => h2 l)]
      simp
    have hpnorm : ‖(p : ℂ)‖ = (p : ℝ) := by simp
    rw [hnr, hpnorm, one_mul]
/-- **The level bound.**  For `e = 2ℓ + M` the level-`ℓ` sum over `ZMod (p^M)` is bounded by
`2 p^(M/2)`. -/
theorem level_bound3 (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e) (M : ℕ) :
    ∀ ℓ : ℕ, e = 2 * ℓ + M → 1 ≤ ℓ →
      ∀ (χ : DirichletCharacter ℂ (p ^ e)), χ.IsPrimitive →
        ∀ (A C : Fin 3 → ZMod (p ^ e)) (κ : ℕ),
          (∑ l : Fin 3, A l) - (∑ l : Fin 3, C l) = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)) →
          ¬ (p : ℕ) ∣ ((∑ l : Fin 3, A l ^ 2) - (∑ l : Fin 3, C l ^ 2) : ZMod (p ^ e)).val →
          ‖levelSum3 p e ℓ M χ A C‖ ≤ 2 * (p : ℝ) ^ ((M : ℝ) / 2) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hppos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro ℓ heq hℓ χ hχ A C κ hsum hnd
    rcases Nat.lt_or_ge M 2 with hM | hM
    · interval_cases M
      · have h1 : levelSum3 p e ℓ 0 χ A C = 1 := by
          rw [levelSum3_eq_range_sum]
          rw [show p ^ 0 = 1 by norm_num, Finset.sum_range_one]
          simp [phase3]
        rw [h1, show ((0 : ℕ) : ℝ) / 2 = 0 by norm_num, Real.rpow_zero]
        norm_num
      · have h1 : e = 2 * ℓ + 1 := by omega
        refine (levelSum_base_one3 p e ℓ hp2 hℓ h1 χ hχ A C κ hsum hnd).trans_eq ?_
        rw [Real.sqrt_eq_rpow]
        norm_num
    · obtain ⟨A', C', κ', hsum', hnd', hnorm⟩ :=
        level_step3 p e ℓ M hp2 he hℓ hM heq χ hχ A C κ hsum hnd
      rw [hnorm]
      have hrec := ih (M - 2) (by omega) (ℓ + 1) (by omega) (by omega) χ hχ A' C' κ' hsum' hnd'
      calc (p : ℝ) * ‖levelSum3 p e (ℓ + 1) (M - 2) χ A' C'‖
          ≤ (p : ℝ) * (2 * (p : ℝ) ^ (((M - 2 : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hrec hppos.le
        _ = 2 * (p : ℝ) ^ ((M : ℝ) / 2) := by
            have hcast : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by
              rw [Nat.cast_sub (by omega)]; norm_num
            rw [show (M : ℝ) / 2 = ((M - 2 : ℕ) : ℝ) / 2 + 1 by rw [hcast]; ring,
              Real.rpow_add hppos, Real.rpow_one]
            ring
/-- The summand of the target is a constant times the level-`1` phase in the unit part. -/
lemma target_term_eq3 (p e : ℕ) [Fact p.Prime] (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) (r : ZMod p)
    (hun : ∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0 ∧ (r + (b l : ZMod p)) ≠ 0)
    (z : ZMod (p ^ (e - 2))) :
    χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
      = (∏ l : Fin 3, χ (((r.val + a l : ℕ) : ZMod (p ^ e))))
        * (∏ l : Fin 3, (starRingEnd ℂ) (χ (((r.val + b l : ℕ) : ZMod (p ^ e)))))
        * phase3 p e 1 χ (fun l => gammaU p e r (a l)) (fun l => gammaU p e r (b l))
            ((z.val : ℕ) : ZMod (p ^ e)) := by
  have he1 : 1 ≤ e := by omega
  have hfac : ∀ u : ℕ, (r + (u : ZMod p)) ≠ 0 →
      ((((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (u : ℕ)))
        = (((r.val + u : ℕ) : ZMod (p ^ e)))
          * (1 + (p : ZMod (p ^ e)) * gammaU p e r u * ((z.val : ℕ) : ZMod (p ^ e))) := by
    intro u hu
    have h1 : (((r.val + u : ℕ) : ZMod (p ^ e))) * gammaU p e r u = 1 := gammaU_mul p e r u hu he1
    rw [mul_add, mul_one,
      show (((r.val + u : ℕ) : ZMod (p ^ e))) * ((p : ZMod (p ^ e)) * gammaU p e r u * ((z.val : ℕ) : ZMod (p ^ e)))
        = (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) * ((((r.val + u : ℕ) : ZMod (p ^ e))) * gammaU p e r u) by ring,
      h1, mul_one]
    push_cast
    ring
  have hA : ∀ l : Fin 3,
      χ ((((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        = χ (((r.val + a l : ℕ) : ZMod (p ^ e)))
          * χ (1 + (p : ZMod (p ^ e)) * gammaU p e r (a l) * ((z.val : ℕ) : ZMod (p ^ e))) := by
    intro l; rw [hfac (a l) (hun l).1, map_mul]
  have hB : ∀ l : Fin 3,
      (starRingEnd ℂ) (χ ((((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))
        = (starRingEnd ℂ) (χ (((r.val + b l : ℕ) : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (1 + (p : ZMod (p ^ e)) * gammaU p e r (b l) * ((z.val : ℕ) : ZMod (p ^ e)))) := by
    intro l; rw [hfac (b l) (hun l).2, map_mul, map_mul]
  rw [map_prod χ (fun l => ((((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))) Finset.univ,
    map_prod χ (fun l => ((((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ)))) Finset.univ,
    map_prod (starRingEnd ℂ) (fun l => χ ((((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ)))) Finset.univ]
  rw [Finset.prod_congr rfl (fun l _ => hA l), Finset.prod_congr rfl (fun l _ => hB l)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [phase3, pPow, pow_one]
  ring

/-- **The target sum equals a constant times the level-`1` sum.** -/
theorem target_sum_eq3 (p e : ℕ) [Fact p.Prime] (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) (r : ZMod p)
    (hun : ∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0 ∧ (r + (b l : ZMod p)) ≠ 0) :
    (∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ)))))
      = (∏ l : Fin 3, χ (((r.val + a l : ℕ) : ZMod (p ^ e))))
        * (∏ l : Fin 3, (starRingEnd ℂ) (χ (((r.val + b l : ℕ) : ZMod (p ^ e)))))
        * levelSum3 p e 1 (e - 2) χ (fun l => gammaU p e r (a l)) (fun l => gammaU p e r (b l)) := by
  rw [levelSum3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact target_term_eq3 p e he χ a b r hun z
/-- **`r = 3` level sum: sharp Gauss-sum bound in the non-degenerate case.**

For an odd prime `p`, `e ≥ 3`, `χ` primitive modulo `p^e`, shifts `a b : Fin 3 → ℕ` and a
critical class `r : ZMod p` (all six shifts units, `∑_l (r+a l)⁻¹ = ∑_l (r+b l)⁻¹` in `ZMod p`)
whose *quadratic* phase coefficient is non-zero, i.e. `∑_l (r+b l)⁻² ≠ ∑_l (r+a l)⁻²` in
`ZMod p`, the level sum over the `p^(e-2)` lifts `z` of `r` satisfies
`‖∑_z χ (∏_l (r + p z + a l)) * conj (χ (∏_l (r + p z + b l)))‖ ≤ 2 * p^((e-2)/2)`. -/
theorem charCorrelation6_levelSum_nondegenerate {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (r : ZMod p)
    (hunit : ∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0 ∧ (r + (b l : ZMod p)) ≠ 0)
    (hcrit : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹))
    (hnd : (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹ ^ 2) ≠ (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹ ^ 2)) :
    ‖∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))‖
      ≤ 2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have he1 : 1 ≤ e := by omega
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p he1
  have hnormU : ∀ u : ℕ, (r + (u : ZMod p)) ≠ 0 →
      ‖χ (((r.val + u : ℕ) : ZMod (p ^ e)))‖ = 1 := by
    intro u hu
    have hunit : IsUnit ((((r.val + u : ℕ)) : ZMod (p ^ e))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he1]
      intro h
      refine hu ?_
      have h2 : ((r.val + u : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
      rw [Nat.cast_add, ZMod.natCast_zmod_val] at h2
      simpa using h2
    rw [← IsUnit.unit_spec hunit]
    exact norm_apply_unit χ hunit.unit
  have hinc : ∀ u : ℕ, (r + (u : ZMod p)) ≠ 0 →
      ZMod.castHom hdiv1 (ZMod p) (gammaU p e r u) = (r + (u : ZMod p))⁻¹ := by
    intro u hu
    have h1 : ((((r.val + u : ℕ)) : ZMod (p ^ e))) * gammaU p e r u = 1 :=
      gammaU_mul p e r u hu he1
    have h2 := congrArg (ZMod.castHom hdiv1 (ZMod p)) h1
    rw [map_mul, map_one, map_natCast, Nat.cast_add, ZMod.natCast_zmod_val] at h2
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)
  rw [target_sum_eq3 (p := p) (e := e) he χ a b r hunit, norm_mul]
  have hC : ‖(∏ l : Fin 3, χ (((r.val + a l : ℕ) : ZMod (p ^ e))))
      * (∏ l : Fin 3, (starRingEnd ℂ) (χ (((r.val + b l : ℕ) : ZMod (p ^ e)))))‖ = 1 := by
    rw [norm_mul, norm_prod, norm_prod]
    have h1 : ∀ l : Fin 3, ‖χ (((r.val + a l : ℕ) : ZMod (p ^ e)))‖ = 1 :=
      fun l => hnormU (a l) (hunit l).1
    have h2 : ∀ l : Fin 3, ‖(starRingEnd ℂ) (χ (((r.val + b l : ℕ) : ZMod (p ^ e))))‖ = 1 := by
      intro l; rw [Complex.norm_conj]; exact hnormU (b l) (hunit l).2
    rw [Finset.prod_congr rfl (fun l _ => h1 l), Finset.prod_congr rfl (fun l _ => h2 l)]
    simp
  rw [hC, one_mul]
  have hredsum : ZMod.castHom hdiv1 (ZMod p)
      ((∑ l : Fin 3, gammaU p e r (a l)) - (∑ l : Fin 3, gammaU p e r (b l))) = 0 := by
    rw [map_sub, map_sum, map_sum]
    rw [Finset.sum_congr rfl (fun l _ => hinc (a l) (hunit l).1),
      Finset.sum_congr rfl (fun l _ => hinc (b l) (hunit l).2), hcrit, sub_self]
  have hz : p ∣ ((∑ l : Fin 3, gammaU p e r (a l)) - (∑ l : Fin 3, gammaU p e r (b l))).val :=
    (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mp hredsum
  obtain ⟨κ, hκ⟩ := hz
  have hsumg : (∑ l : Fin 3, gammaU p e r (a l)) - (∑ l : Fin 3, gammaU p e r (b l))
      = ((p ^ 1 * κ : ℕ) : ZMod (p ^ e)) := by
    rw [← ZMod.natCast_zmod_val
      ((∑ l : Fin 3, gammaU p e r (a l)) - (∑ l : Fin 3, gammaU p e r (b l))), hκ, pow_one]
  have hA2 : (∑ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (gammaU p e r (a l) ^ 2))
      = ∑ l : Fin 3, (r + (a l : ZMod p))⁻¹ ^ 2 := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_pow, hinc (a l) (hunit l).1]
  have hC2 : (∑ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (gammaU p e r (b l) ^ 2))
      = ∑ l : Fin 3, (r + (b l : ZMod p))⁻¹ ^ 2 := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_pow, hinc (b l) (hunit l).2]
  have hredquad : ZMod.castHom hdiv1 (ZMod p)
      ((∑ l : Fin 3, gammaU p e r (a l) ^ 2) - (∑ l : Fin 3, gammaU p e r (b l) ^ 2))
      = (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹ ^ 2) - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹ ^ 2) := by
    rw [map_sub, map_sum, map_sum, hA2, hC2]
  have hndg : ¬ (p : ℕ) ∣ ((∑ l : Fin 3, gammaU p e r (a l) ^ 2)
      - (∑ l : Fin 3, gammaU p e r (b l) ^ 2)).val := by
    intro hcon
    refine hnd ?_
    have h0 : ZMod.castHom hdiv1 (ZMod p)
        ((∑ l : Fin 3, gammaU p e r (a l) ^ 2) - (∑ l : Fin 3, gammaU p e r (b l) ^ 2)) = 0 :=
      (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mpr hcon
    rw [hredquad] at h0
    exact (sub_eq_zero.mp h0).symm
  refine (level_bound3 p e hp2 he (e - 2) 1 (by omega) (by omega) χ hχ
    (fun l => gammaU p e r (a l)) (fun l => gammaU p e r (b l)) κ hsumg hndg).trans_eq ?_
  rw [show (((e - 2 : ℕ)) : ℝ) = (e : ℝ) - 2 by
    rw [Nat.cast_sub (by omega : 2 ≤ e)]; norm_num]
end Commons.NumberTheory.DirichletCharacter
