import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- Two factors with a commuting middle element may be re-bracketed:
`a * (b * x) * a' = b * (a * x * a')` when `a` and `b` commute. -/
private lemma conj_mul_comm {M : Type*} [Group M] (a b x a' : M) (hab : Commute a b) :
    a * (b * x) * a' = b * (a * x * a') := by
  rw [← mul_assoc a b x, hab.eq]
  group

/-- Conjugating `v` by `u` gives `c * v`, directly from the basic relation. -/
private lemma uv_conj {M : Type*} [Group M] (u v c : M) (huv : u * v = c * (v * u)) :
    u * v * u⁻¹ = c * v := by
  rw [huv]; group

/-- The inverse-direction commutation `u⁻¹ * v * u = c⁻¹ * v`. -/
private lemma inv_conj {M : Type*} [Group M] (u v c : M)
    (huv : u * v = c * (v * u)) (hcu : Commute c u) :
    u⁻¹ * v * u = c⁻¹ * v := by
  have h1 : u⁻¹ * v * u = u⁻¹ * c⁻¹ * (u * v) := by
    rw [mul_assoc, ← inv_mul_cancel_left c (v * u), ← huv, mul_assoc]
  rw [h1, (hcu.symm.inv_left.inv_right).eq]
  group

/-- Conjugation of `v` by any integer power `u ^ n` of `u` multiplies by `c ^ n`. -/
private lemma conj_zpow {M : Type*} [Group M] (u v c : M)
    (huv : u * v = c * (v * u)) (hcu : Commute c u) :
    ∀ n : ℤ, u ^ n * v * u ^ (-n) = c ^ n * v := by
  intro n
  refine Int.induction_on n (motive := fun k => u ^ k * v * u ^ (-k) = c ^ k * v) ?_ ?_ ?_
  · simp
  · intro i ih
    calc u ^ ((i : ℤ) + 1) * v * u ^ (-((i : ℤ) + 1))
        = u * (u ^ (i : ℤ) * v * u ^ (-(i : ℤ))) * u⁻¹ := by group
      _ = u * (c ^ (i : ℤ) * v) * u⁻¹ := by rw [ih]
      _ = c ^ (i : ℤ) * (u * v * u⁻¹) := by
            rw [conj_mul_comm u (c ^ (i : ℤ)) v u⁻¹ ((hcu.symm).zpow_right (i : ℤ))]
      _ = c ^ (i : ℤ) * (c * v) := by rw [uv_conj u v c huv]
      _ = c ^ ((i : ℤ) + 1) * v := by rw [← mul_assoc, ← zpow_add_one]
  · intro i ih
    calc u ^ (-(i : ℤ) - 1) * v * u ^ (-(-(i : ℤ) - 1))
        = u⁻¹ * (u ^ (-(i : ℤ)) * v * u ^ (-(-(i : ℤ)))) * u := by group
      _ = u⁻¹ * (c ^ (-(i : ℤ)) * v) * u := by rw [ih]
      _ = c ^ (-(i : ℤ)) * (u⁻¹ * v * u) := by
            rw [conj_mul_comm u⁻¹ (c ^ (-(i : ℤ))) v u
                  (((hcu.symm).inv_left).zpow_right (-(i : ℤ)))]
      _ = c ^ (-(i : ℤ)) * (c⁻¹ * v) := by rw [inv_conj u v c huv hcu]
      _ = c ^ (-(i : ℤ) - 1) * v := by rw [← mul_assoc, ← zpow_sub_one]

/-- The multiplication formula: `u ^ n` moves past `v ^ m` at the cost of `c ^ (n * m)`. -/
private lemma pow_mul_formula {M : Type*} [Group M] (u v c : M)
    (huv : u * v = c * (v * u)) (hcu : Commute c u) (hcv : Commute c v) :
    ∀ m n : ℤ, u ^ n * v ^ m = c ^ (n * m) * (v ^ m * u ^ n) := by
  intro m n
  have hconj := conj_zpow u v c huv hcu
  have hA : (MulAut.conj (u ^ n)) (v ^ m) = u ^ n * v ^ m * u ^ (-n) := by
    rw [MulAut.conj_apply, ← zpow_neg]
  have hB : (MulAut.conj (u ^ n)) v = u ^ n * v * u ^ (-n) := by
    rw [MulAut.conj_apply, ← zpow_neg]
  have h1 : u ^ n * v ^ m * u ^ (-n) = (u ^ n * v * u ^ (-n)) ^ m := by
    rw [← hA, ← hB, map_zpow]
  have h3 : u ^ n * v ^ m * u ^ (-n) = c ^ (n * m) * v ^ m := by
    rw [h1, hconj n, Commute.mul_zpow (hcv.zpow_left n) m, ← zpow_mul]
  calc u ^ n * v ^ m = (u ^ n * v ^ m * u ^ (-n)) * u ^ n := by group
    _ = (c ^ (n * m) * v ^ m) * u ^ n := by rw [h3]
    _ = c ^ (n * m) * (v ^ m * u ^ n) := by rw [mul_assoc]

lemma pow_swap {M : Type*} [Group M] (u v c : M)
    (huv : u * v = c * (v * u)) (hcu : Commute c u) (hcv : Commute c v) :
    ∀ m n : ℤ, v ^ m * u ^ n = c ^ (-(m * n)) * (u ^ n * v ^ m) := by
  intro m n
  have h := pow_mul_formula u v c huv hcu hcv m n
  have key : c ^ (-(m * n)) * (u ^ n * v ^ m) = v ^ m * u ^ n := by
    rw [zpow_neg, h, ← Int.mul_comm m n, inv_mul_cancel_left]
  exact key.symm

end Work.ThmF.ChV3.Prove
