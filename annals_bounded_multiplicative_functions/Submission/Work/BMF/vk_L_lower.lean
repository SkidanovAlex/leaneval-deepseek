import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The lower bound `1 ≤ ‖L(s, χ)‖ · ζ(σ)` for `σ = Re s > 1`

This is the elementary Euler-product lower bound for Dirichlet `L`-functions on the half-plane
of absolute convergence: for every Dirichlet character `χ` mod `N` and every complex `s` with
`1 < Re s`,

  `1 ≤ ‖L(s, χ)‖ * ζ(Re s)`.

The proof is the classical term-by-term comparison of the Euler products
`L(s, χ) = ∏_p (1 - χ(p) p^{-s})^{-1}` and `ζ(σ) = ∏_p (1 - p^{-σ})^{-1}`: since
`|1 - χ(p) p^{-s}| ≤ 1 + p^{-σ}`, each factor of `L` is at least `1 - p^{-σ}`, so
`‖L(s, χ)‖ ≥ ∏_p (1 - p^{-σ}) = 1/ζ(σ)`.  Multiplying by `ζ(σ) > 0` gives the claim.
-/

namespace Work.BMF

open Complex

/-- The sequence `p ↦ p^{-σ}` restricted to the primes is summable for `σ > 1`. -/
private lemma summable_primes_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ σ)⁻¹) := Real.summable_nat_rpow_inv.mpr hσ
  have h' : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    refine h.congr (fun n => ?_)
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact h'.subtype Nat.Prime

/-- For `σ > 1` and a prime `p` one has `p^{-σ} ≤ 1/2`. -/
private lemma primes_rpow_neg_le_half {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le)
      (by linarith)
  have h2 : (2 : ℝ) ^ (-σ) < (1 / 2 : ℝ) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num)
      (show -σ < -1 by linarith)
    have h21 : (2 : ℝ) ^ (-1 : ℝ) = (1 / 2 : ℝ) := by
      rw [Real.rpow_neg_one]; norm_num
    rwa [h21] at h
  linarith

/-- `|log (1 - a)| ≤ 2 a` for `0 < a ≤ 1/2`. -/
private lemma log_one_sub_abs_le {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    |Real.log (1 - a)| ≤ 2 * a := by
  have h1a_pos : 0 < 1 - a := by linarith
  have hlog : Real.log (1 - a) ≤ 0 := by
    have h := Real.log_le_log h1a_pos (by linarith : 1 - a ≤ 1)
    rwa [Real.log_one] at h
  rw [abs_of_nonpos hlog]
  calc -Real.log (1 - a) = Real.log ((1 - a)⁻¹) := (Real.log_inv _).symm
    _ ≤ (1 - a)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ ≤ 2 * a := by
        rw [show (1 - a)⁻¹ - 1 = a / (1 - a) from by field_simp; ring]
        rw [div_le_iff₀ h1a_pos]
        nlinarith [ha0, ha1]

/-- `‖χ(p) p^{-s}‖ ≤ p^{-Re s}`. -/
private lemma chiMul_norm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (p : Nat.Primes) :
    ‖χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s.re) := by
  rw [norm_mul, norm_natCast_cpow_of_pos p.prop.pos (-s), Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _).le
    (χ.norm_le_one _)

/-- `1 - p^{-Re s} ≤ ‖1 - χ(p) p^{-s}‖`. -/
private lemma one_sub_chiMul_norm_ge {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (p : Nat.Primes) :
    1 - (p : ℝ) ^ (-s.re) ≤ ‖1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ := by
  have h := abs_norm_sub_norm_le (1 : ℂ) (χ (p : ZMod N) * (p : ℂ) ^ (-s))
  simp only [norm_one] at h
  calc 1 - (p : ℝ) ^ (-s.re) ≤ 1 - ‖χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ := by
        linarith [chiMul_norm_le (s := s) χ p]
    _ ≤ |1 - ‖χ (p : ZMod N) * (p : ℂ) ^ (-s)‖| := le_abs_self _
    _ ≤ ‖(1 : ℂ) - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ := h

/-- `‖1 - χ(p) p^{-s}‖ ≤ 1 + p^{-Re s}`. -/
private lemma one_sub_chiMul_norm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (p : Nat.Primes) :
    ‖1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-s.re) := by
  have h := norm_sub_le (1 : ℂ) (χ (p : ZMod N) * (p : ℂ) ^ (-s))
  simp only [norm_one] at h
  linarith [chiMul_norm_le (s := s) χ p]

/-- Term-by-term Euler product comparison: `1 - p^{-σ} ≤ ‖(1 - χ(p) p^{-s})⁻¹‖`. -/
private lemma one_sub_le_norm_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (p : Nat.Primes) :
    1 - (p : ℝ) ^ (-s.re) ≤ ‖(1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))⁻¹‖ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have ha0 : 0 < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have ha1 : (p : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hA : 1 - (p : ℝ) ^ (-s.re) ≤ (1 + (p : ℝ) ^ (-s.re))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg ((p : ℝ) ^ (-s.re))]
  have hpos : 0 < ‖1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ := by
    have h := one_sub_chiMul_norm_ge (s := s) χ p
    linarith
  have hB : (1 + (p : ℝ) ^ (-s.re))⁻¹ ≤ ‖1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖⁻¹ :=
    inv_anti₀ hpos (one_sub_chiMul_norm_le (s := s) χ p)
  rw [norm_inv]
  linarith

/-- `log (1 - p^{-σ}) ≤ log ‖(1 - χ(p) p^{-s})⁻¹‖`. -/
private lemma log_one_sub_le_log_norm_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    Real.log (1 - (p : ℝ) ^ (-s.re)) ≤
      Real.log ‖(1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))⁻¹‖ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have ha_lt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  exact Real.log_le_log (by linarith) (one_sub_le_norm_inv χ hs p)

/-- `∑_p log (1 - p^{-σ})` converges for `σ > 1`. -/
private lemma summable_log_one_sub {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log (1 - (p : ℝ) ^ (-σ))) := by
  refine Summable.of_norm_bounded (g := fun p : Nat.Primes => 2 * (p : ℝ) ^ (-σ))
    ((summable_primes_rpow_neg hσ).mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs]
  exact log_one_sub_abs_le (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)
    (primes_rpow_neg_le_half hσ p)

/-- `∑_p log ‖(1 - χ(p) p^{-s})⁻¹‖` converges for `Re s > 1`. -/
private lemma summable_log_norm_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => Real.log ‖(1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))⁻¹‖) := by
  refine Summable.of_norm_bounded (g := fun p : Nat.Primes => 2 * (p : ℝ) ^ (-s.re))
    ((summable_primes_rpow_neg hs).mul_left 2) (fun p => ?_)
  have ha0 : 0 < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have ha1 : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := primes_rpow_neg_le_half hs p
  have hloglo : -(2 * (p : ℝ) ^ (-s.re)) ≤ Real.log ‖1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ := by
    have h := (abs_le.mp (log_one_sub_abs_le ha0 ha1)).1
    have h2 := Real.log_le_log (show 0 < 1 - (p : ℝ) ^ (-s.re) by linarith)
      (one_sub_chiMul_norm_ge (s := s) χ p)
    linarith
  have hloghi : Real.log ‖1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ ≤ 2 * (p : ℝ) ^ (-s.re) := by
    have hpos : 0 < ‖1 - χ (p : ZMod N) * (p : ℂ) ^ (-s)‖ := by
      have h := one_sub_chiMul_norm_ge (s := s) χ p
      linarith
    have h1 := Real.log_le_log hpos (one_sub_chiMul_norm_le (s := s) χ p)
    have h2 : Real.log (1 + (p : ℝ) ^ (-s.re)) ≤ (p : ℝ) ^ (-s.re) := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + (p : ℝ) ^ (-s.re) by linarith)
      linarith
    linarith
  rw [Real.norm_eq_abs, norm_inv, Real.log_inv, abs_neg]
  exact abs_le.mpr ⟨hloglo, hloghi⟩

/-- **The Riemann zeta function at a real point `σ > 1`, as the exponential of the prime sum.**
`ζ(σ) = exp (∑_p -log (1 - p^{-σ}))`, which is positive. -/
private lemma zeta_re_eq {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re = Real.exp (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ))) := by
  have hσc : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ))) = Complex.ofReal (-Real.log (1 - (p : ℝ) ^ (-σ))) := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hr_lt : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have h1r : 0 ≤ 1 - (p : ℝ) ^ (-σ) := by linarith
    have hcpow : Complex.ofReal ((p : ℝ) ^ (-σ)) = (p : ℂ) ^ (-(σ : ℂ)) := by
      have h := Complex.ofReal_cpow (show (0 : ℝ) ≤ (p : ℝ) by positivity) (-σ)
      simpa using h
    have h1c : Complex.ofReal (1 - (p : ℝ) ^ (-σ)) = 1 - (p : ℂ) ^ (-(σ : ℂ)) := by
      rw [← hcpow]; simp
    rw [← h1c, ← Complex.ofReal_log h1r, Complex.ofReal_neg]
  have hT : (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ))))
      = Complex.ofReal (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ))) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun p => hterm p)
  rw [← riemannZeta_eulerProduct_exp_log hσc, hT, ← Complex.ofReal_exp, Complex.ofReal_re]

/-- **Logarithm of `‖L(s, χ)‖` as a prime sum**, from the Euler product
`L(s, χ) = ∏_p (1 - χ(p) p^{-s})^{-1}`. -/
private lemma log_norm_LFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    Real.log ‖DirichletCharacter.LFunction χ s‖ =
      ∑' p : Nat.Primes, Real.log ‖(1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))⁻¹‖ := by
  have hsumB : Summable (fun p : Nat.Primes => χ (p : ZMod N) * (p : ℂ) ^ (-s)) :=
    Summable.of_norm_bounded (summable_primes_rpow_neg hs) (fun p => chiMul_norm_le (s := s) χ p)
  have hsumL : Summable (fun p : Nat.Primes => Complex.log (1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))) :=
    Complex.summable_log_one_add_of_summable
      (f := fun p : Nat.Primes => -(χ (p : ZMod N) * (p : ℂ) ^ (-s)))
      (by simpa using hsumB.neg)
  have hsumN : Summable (fun p : Nat.Primes => -Complex.log (1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))) :=
    hsumL.neg
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.LSeries_eulerProduct_exp_log χ hs, Complex.norm_exp, Real.log_exp,
    Complex.re_tsum hsumN]
  exact tsum_congr (fun p => by
    rw [Complex.neg_re, Complex.log_re, ← Real.log_inv, norm_inv])

/-- **Non-vanishing lower bound.** For a Dirichlet character `χ` modulo `N` and `1 < Re s`,
`1 ≤ ‖L(s, χ)‖ · ζ(Re s)`. -/
theorem vk_L_lower {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    1 ≤ ‖DirichletCharacter.LFunction χ s‖ * (riemannZeta (s.re : ℂ)).re := by
  have hζ := zeta_re_eq (σ := s.re) hs
  have hζpos : 0 < (riemannZeta (s.re : ℂ)).re := by rw [hζ]; exact Real.exp_pos _
  have hζlog : Real.log ((riemannZeta (s.re : ℂ)).re) =
      ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s.re)) := by
    rw [hζ, Real.log_exp]
  have hA' : (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s.re)))
      = -∑' p : Nat.Primes, Real.log (1 - (p : ℝ) ^ (-s.re)) := by rw [tsum_neg]
  have hLpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
      ← DirichletCharacter.LSeries_eulerProduct_exp_log χ hs, Complex.norm_exp]
    exact Real.exp_pos _
  have hcmp : (∑' p : Nat.Primes, Real.log (1 - (p : ℝ) ^ (-s.re)))
      ≤ ∑' p : Nat.Primes, Real.log ‖(1 - χ (p : ZMod N) * (p : ℂ) ^ (-s))⁻¹‖ :=
    Summable.tsum_le_tsum (fun p => log_one_sub_le_log_norm_inv χ hs p)
      (summable_log_one_sub hs) (summable_log_norm_inv χ hs)
  have hmain : -Real.log ((riemannZeta (s.re : ℂ)).re)
      ≤ Real.log ‖DirichletCharacter.LFunction χ s‖ := by
    rw [hζlog, hA', neg_neg, log_norm_LFunction_eq χ hs]
    exact hcmp
  have hexp := Real.exp_le_exp.mpr hmain
  rw [Real.exp_neg, Real.exp_log hζpos, Real.exp_log hLpos] at hexp
  calc (1 : ℝ) = (riemannZeta (s.re : ℂ)).re * ((riemannZeta (s.re : ℂ)).re)⁻¹ := by
        rw [mul_inv_cancel₀ hζpos.ne']
    _ ≤ (riemannZeta (s.re : ℂ)).re * ‖DirichletCharacter.LFunction χ s‖ :=
        mul_le_mul_of_nonneg_left hexp hζpos.le
    _ = ‖DirichletCharacter.LFunction χ s‖ * (riemannZeta (s.re : ℂ)).re := by ring

end Work.BMF
