import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality

/-- **The logarithmised orthogonality identity, in the form needed for the Euler factors.**

For a finite commutative group `G`, an element `σ : G` and a real number `0 ≤ x < 1`, the sum over
the characters `χ` of `G` of the logarithms of the norms of the inverted linear factors
`(1 - χ(σ) x)⁻¹` equals `- (|G| / orderOf σ) · log (1 - x ^ orderOf σ)`.

This is the logarithm of the multiplicative identity
`∏_χ (1 - χ(σ) x)⁻¹ = ((1 - x ^ orderOf σ)⁻¹) ^ (|G| / orderOf σ)`
(`NK.HeckeL.Nonvanishing.prod_char_inv_one_sub_mul`): the product over the characters of the
norms is the norm of the product, `∏_χ ‖1 - χ(σ) x‖ = ‖(1 - x ^ orderOf σ)^(|G|/orderOf σ)‖`, and
every factor `1 - χ(σ) x` is nonzero because `‖χ(σ) x‖ = x < 1`. -/
lemma sum_log_norm_inv_one_sub_mul {G : Type*} [CommGroup G] [Fintype G] (σ : G) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑ χ : G →* ℂˣ, Real.log ‖(1 - (χ σ : ℂ) * (x : ℂ))⁻¹‖ =
      - (Nat.card G / orderOf σ : ℝ) * Real.log (1 - x ^ orderOf σ) := by
  classical
  have hd : 0 < orderOf σ := orderOf_pos σ
  have hxd : 0 < 1 - x ^ orderOf σ := by
    have h := pow_lt_one₀ hx0 hx1 (n := orderOf σ) (Nat.pos_iff_ne_zero.mp hd)
    linarith
  -- the norm of the prime term `χ(σ) x` is `x`
  have hnorm : ∀ χ : G →* ℂˣ, ‖(χ σ : ℂ) * (x : ℂ)‖ = x := by
    intro χ
    rw [norm_mul, NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ σ, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hx0]
  -- hence no factor `1 - χ(σ) x` vanishes
  have hne : ∀ χ : G →* ℂˣ, ‖1 - (χ σ : ℂ) * (x : ℂ)‖ ≠ 0 := by
    intro χ
    have h1 : (1 : ℝ) - x ≤ ‖(1 : ℂ) - (χ σ : ℂ) * (x : ℂ)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((χ σ : ℂ) * (x : ℂ))
      rwa [norm_one, hnorm χ] at h
    have h2 : 0 < ‖(1 : ℂ) - (χ σ : ℂ) * (x : ℂ)‖ := by linarith
    exact h2.ne'
  -- the product over the characters, from the multiplicative identity
  have hprod : ∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * (x : ℂ)) =
      ((1 - x ^ orderOf σ : ℝ) : ℂ) ^ (Nat.card G / orderOf σ) := by
    have hkey := NK.HeckeL.Nonvanishing.prod_char_inv_one_sub_mul G σ ((x : ℝ) : ℂ)
    rw [← Complex.ofReal_pow] at hkey
    have hpinv : (∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * (x : ℂ)))⁻¹ =
        (1 - ((x ^ orderOf σ : ℝ) : ℂ))⁻¹ ^ (Nat.card G / orderOf σ) := by
      rw [← Finset.prod_inv_distrib]
      exact hkey
    calc ∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * (x : ℂ))
        = ((∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * (x : ℂ)))⁻¹)⁻¹ := (inv_inv _).symm
      _ = (((1 - ((x ^ orderOf σ : ℝ) : ℂ))⁻¹) ^ (Nat.card G / orderOf σ))⁻¹ := by rw [hpinv]
      _ = (1 - ((x ^ orderOf σ : ℝ) : ℂ)) ^ (Nat.card G / orderOf σ) := by rw [inv_pow, inv_inv]
      _ = ((1 - x ^ orderOf σ : ℝ) : ℂ) ^ (Nat.card G / orderOf σ) := by
            rw [Complex.ofReal_sub, Complex.ofReal_one]
  calc ∑ χ : G →* ℂˣ, Real.log ‖(1 - (χ σ : ℂ) * (x : ℂ))⁻¹‖
      = ∑ χ : G →* ℂˣ, - Real.log ‖(1 : ℂ) - (χ σ : ℂ) * (x : ℂ)‖ :=
        Finset.sum_congr rfl fun χ _ => by rw [norm_inv, Real.log_inv]
    _ = - ∑ χ : G →* ℂˣ, Real.log ‖(1 : ℂ) - (χ σ : ℂ) * (x : ℂ)‖ :=
        Finset.sum_neg_distrib (fun χ : G →* ℂˣ => Real.log ‖(1 : ℂ) - (χ σ : ℂ) * (x : ℂ)‖)
    _ = - Real.log ‖∏ χ : G →* ℂˣ, ((1 : ℂ) - (χ σ : ℂ) * (x : ℂ))‖ := by
        rw [norm_prod, Real.log_prod (fun χ _ => hne χ)]
    _ = - Real.log ‖(((1 - x ^ orderOf σ : ℝ) : ℂ) ^ (Nat.card G / orderOf σ))‖ := by rw [hprod]
    _ = - Real.log ((1 - x ^ orderOf σ) ^ (Nat.card G / orderOf σ)) := by
        rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hxd.le]
    _ = - (Nat.card G / orderOf σ : ℝ) * Real.log (1 - x ^ orderOf σ) := by
        rw [Real.log_pow, Nat.cast_div_charZero (orderOf_dvd_natCard σ)]
        ring

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.tsum_log_norm_eulerFactor`,
-- namespace `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFTdeep.SecondInequality.Defs`.
--
-- This is the logarithmised *local factor identity* (Milne, Class Field Theory, VI §4, the
-- orthogonality computation in the proof of Theorem 4.8).  The workspace already has the
-- multiplicative form `NK.HeckeL.Nonvanishing.prod_char_inv_one_sub_mul`:
--   `∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * x)⁻¹ = ((1 - x ^ orderOf σ)⁻¹) ^ (Nat.card G / orderOf σ)`
-- for a finite commutative group `G`.  Taking norms and logarithms (all factors are positive
-- reals for `0 < x < 1`) gives the stated identity, with `x = primeWeight s 𝔭` and `σ = b 𝔭`;
-- note `orderOf (b 𝔭) ≠ 0` so `x ^ orderOf (b 𝔭) < 1` and `1 - x ^ orderOf (b 𝔭) > 0`.
-- `Nat.card B / orderOf (b 𝔭)` is the exact quotient by Lagrange's theorem.
theorem tsum_log_norm_eulerFactor {K : Type*} [Field K] [NumberField K] {B : Type*} [CommGroup B]
    [Fintype B] (b : PrimeIdeal K → B) {s : ℝ} (hs : 1 < s) (𝔭 : PrimeIdeal K) :
    ∑ χ : B →* ℂˣ, Real.log ‖eulerFactor b χ s 𝔭‖ =
      - (Nat.card B / orderOf (b 𝔭) : ℝ) * Real.log (1 - (primeWeight s 𝔭) ^ orderOf (b 𝔭)) := by
  classical
  set x : ℝ := primeWeight s 𝔭 with hxdef
  have hxpos : 0 < x := primeWeight_pos s 𝔭
  have hxlt : x < 1 := by
    rw [hxdef, primeWeight_def]
    exact Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one
      (lt_trans zero_lt_one hs) 𝔭
  have hgoal : (∑ χ : B →* ℂˣ, Real.log ‖eulerFactor b χ s 𝔭‖) =
      ∑ χ : B →* ℂˣ, Real.log ‖(1 - (χ (b 𝔭) : ℂ) * (x : ℂ))⁻¹‖ :=
    Finset.sum_congr rfl fun χ _ => by rw [eulerFactor_def, primeTerm_def, ← hxdef]
  rw [hgoal]
  exact sum_log_norm_inv_one_sub_mul (b 𝔭) hxpos.le hxlt

end NK.GlobalCFTdeep.SecondInequality
