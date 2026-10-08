import Mathlib
import Submission.Work.Higman.Q3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman.Q3

/-- The Frobenius automorphism `x ↦ x ^ 2` of `𝔽_{2ⁿ}`. -/
abbrev frob (n : ℕ) : GaloisField 2 n ≃+* GaloisField 2 n := frobeniusEquiv (GaloisField 2 n) 2

/-- Left multiplication by a nonzero element of a field, as an additive equivalence. -/
def mulLeftAddEquiv {K : Type*} [Field K] (c : K) (hc : c ≠ 0) : K ≃+ K where
  toFun x := c * x
  invFun x := c⁻¹ * x
  left_inv x := by show c⁻¹ * (c * x) = x; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv x := by show c * (c⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  map_add' x y := by show c * (x + y) = c * x + c * y; rw [mul_add]

@[simp] lemma mulLeftAddEquiv_apply {K : Type*} [Field K] (c : K) (hc : c ≠ 0) (x : K) :
    mulLeftAddEquiv c hc x = c * x := rfl

/-- The `k`-th iterated Frobenius of `𝔽_{2ⁿ}` is `x ↦ x ^ 2 ^ k`. -/
lemma frob_pow_apply {n : ℕ} (x : GaloisField 2 n) (k : ℕ) :
    (frob n ^ k) x = x ^ (2 ^ k) := by
  rw [← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def]

/-- `x ^ 2 ^ n = x` in `𝔽_{2ⁿ}`. -/
lemma pow_two_pow_card {n : ℕ} (hn : 1 ≤ n) (x : GaloisField 2 n) : x ^ (2 ^ n) = x := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n (by omega)]
  rw [← hcard]
  exact FiniteField.pow_card x

/-- The `n`-th power of the Frobenius of `𝔽_{2ⁿ}` is the identity. -/
lemma frob_pow_card_eq_one {n : ℕ} (hn : 1 ≤ n) : frob n ^ n = 1 := by
  ext x
  rw [frob_pow_apply, pow_two_pow_card hn x]
  rfl

/-- The `k`-th power of the Frobenius of `𝔽_{2ⁿ}` is the identity whenever `n ∣ k`. -/
lemma frob_pow_eq_one_of_dvd {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : n ∣ k) : frob n ^ k = 1 := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_mul, frob_pow_card_eq_one hn, one_pow]

/-- Composition of Frobenius powers. -/
lemma frob_pow_apply_add {n : ℕ} (a b : ℕ) (x : GaloisField 2 n) :
    (frob n ^ a) ((frob n ^ b) x) = (frob n ^ (a + b)) x := by
  rw [pow_add]
  rfl

/-- `frob n` applied to a Frobenius power. -/
lemma frob_apply_pow_apply {n : ℕ} (k : ℕ) (x : GaloisField 2 n) :
    frob n ((frob n ^ k) x) = (frob n ^ (k + 1)) x := by
  rw [pow_succ']
  rfl

/-- For `i < n` the exponent `((i + n - 1) % n) + (n - i) + 1` is divisible by `n`, so the
corresponding Frobenius power is the identity. -/
lemma dvd_mod_exponent {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : i < n) :
    n ∣ (i + n - 1) % n + (n - i) + 1 := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have h1 : (0 + n - 1) % n = n - 1 := by
      rw [zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    exact ⟨2, by omega⟩
  · have h1 : (i + n - 1) % n = i - 1 := by
      rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    exact ⟨1, by omega⟩

theorem reduce_ab_ab {n : ℕ} (hn : 1 ≤ n) {C C' f : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    ∃ (Φ : (GaloisField 2 n × GaloisField 2 n) ≃+ (GaloisField 2 n × GaloisField 2 n))
      (Ψ : GaloisField 2 n ≃+ GaloisField 2 n) (ε : GaloisField 2 n),
      ∀ v : GaloisField 2 n × GaloisField 2 n,
        Ψ (C * (Φ v).1 ^ (2 ^ i) + C' * (Φ v).2 ^ (2 ^ j) +
            f * (Φ v).1 ^ (2 ^ ((i + n - 1) % n)) * (Φ v).2 ^ (2 ^ ((j + n - 1) % n)))
          = v.1 ^ 2 + v.2 ^ 2 + ε * v.1 * v.2 := by
  classical
  -- The coordinate change is diagonal: it rescales each coordinate by `C⁻¹`, resp. `C'⁻¹`,
  -- and then applies the Frobenius power `n - i`, resp. `n - j`, so that the `2 ^ i`-th power
  -- of the first coordinate is `C⁻¹ * v.1` (and similarly for the second).
  let φ1 : GaloisField 2 n ≃+ GaloisField 2 n :=
    (mulLeftAddEquiv C⁻¹ (inv_ne_zero hC)).trans ((frob n ^ (n - i)).toAddEquiv)
  let φ2 : GaloisField 2 n ≃+ GaloisField 2 n :=
    (mulLeftAddEquiv C'⁻¹ (inv_ne_zero hC')).trans ((frob n ^ (n - j)).toAddEquiv)
  let Φ : (GaloisField 2 n × GaloisField 2 n) ≃+ (GaloisField 2 n × GaloisField 2 n) :=
    AddEquiv.prodCongr φ1 φ2
  refine ⟨Φ, (frob n).toAddEquiv, frob n f * (C⁻¹ * C'⁻¹), ?_⟩
  intro v
  have hx : (Φ v).1 = (frob n ^ (n - i)) (C⁻¹ * v.1) := rfl
  have hy : (Φ v).2 = (frob n ^ (n - j)) (C'⁻¹ * v.2) := rfl
  change frob n (C * (Φ v).1 ^ (2 ^ i) + C' * (Φ v).2 ^ (2 ^ j) +
      f * (Φ v).1 ^ (2 ^ ((i + n - 1) % n)) * (Φ v).2 ^ (2 ^ ((j + n - 1) % n)))
    = v.1 ^ 2 + v.2 ^ 2 + (frob n f * (C⁻¹ * C'⁻¹)) * v.1 * v.2
  -- The diagonal powers.
  have hxi : (Φ v).1 ^ (2 ^ i) = C⁻¹ * v.1 := by
    rw [← frob_pow_apply (Φ v).1 i, hx, frob_pow_apply_add,
      show i + (n - i) = n by omega, frob_pow_card_eq_one hn]
    rfl
  have hxj : (Φ v).2 ^ (2 ^ j) = C'⁻¹ * v.2 := by
    rw [← frob_pow_apply (Φ v).2 j, hy, frob_pow_apply_add,
      show j + (n - j) = n by omega, frob_pow_card_eq_one hn]
    rfl
  -- The cross term: one further Frobenius sends the extra `n - i` (resp. `n - j`) back to
  -- zero modulo `n`.
  have hxM : frob n ((Φ v).1 ^ (2 ^ ((i + n - 1) % n))) = C⁻¹ * v.1 := by
    rw [← frob_pow_apply (Φ v).1 ((i + n - 1) % n), hx, frob_pow_apply_add,
      frob_apply_pow_apply, frob_pow_eq_one_of_dvd hn (dvd_mod_exponent hn hi)]
    rfl
  have hyM : frob n ((Φ v).2 ^ (2 ^ ((j + n - 1) % n))) = C'⁻¹ * v.2 := by
    rw [← frob_pow_apply (Φ v).2 ((j + n - 1) % n), hy, frob_pow_apply_add,
      frob_apply_pow_apply, frob_pow_eq_one_of_dvd hn (dvd_mod_exponent hn hj)]
    rfl
  -- The three summands.
  have hA : frob n (C * (Φ v).1 ^ (2 ^ i)) = v.1 ^ 2 := by
    have h : C * (Φ v).1 ^ (2 ^ i) = v.1 := by
      rw [hxi, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]
    rw [h]
    rfl
  have hB : frob n (C' * (Φ v).2 ^ (2 ^ j)) = v.2 ^ 2 := by
    have h : C' * (Φ v).2 ^ (2 ^ j) = v.2 := by
      rw [hxj, ← mul_assoc, mul_inv_cancel₀ hC', one_mul]
    rw [h]
    rfl
  have hCc : frob n (f * (Φ v).1 ^ (2 ^ ((i + n - 1) % n)) *
        (Φ v).2 ^ (2 ^ ((j + n - 1) % n)))
      = frob n f * (C⁻¹ * v.1) * (C'⁻¹ * v.2) := by
    rw [map_mul, map_mul, hxM, hyM]
  rw [map_add, map_add, hA, hB, hCc]
  ring

end Work.Higman.Q3
