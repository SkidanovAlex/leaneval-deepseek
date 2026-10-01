
import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.primesq_weil_bound
import Submission.Commons.NumberTheory.DirichletCharacter.chi_one_add_primePow_isPrimitiveRoot
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
namespace Commons.NumberTheory.DirichletCharacter
open MulChar

variable {p : ℕ}

/-- The "digits" map `ZMod p × ZMod p → ZMod (p^2)`, `(r,y) ↦ r + p*y`. -/
private def zmd [NeZero p] (r y : ZMod p) : ZMod (p ^ 2) :=
  ((r.val : ℕ) : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * ((y.val : ℕ) : ZMod (p ^ 2))

private lemma zmod_sq_add_digit [NeZero p] (a : ℕ) (r y : ZMod p) :
    ((r.val : ℕ) : ZMod (p^2)) + (p : ZMod (p^2)) * ((y.val : ℕ) : ZMod (p^2))
      + ((a : ℕ) : ZMod (p^2))
      = ((((r.val + a % p) % p) + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) : ℕ)
          : ZMod (p^2)) := by
  have hcast : ((a : ℕ) : ZMod (p^2)) = ((a % p^2 : ℕ) : ZMod (p^2)) := by
    rw [← ZMod.natCast_zmod_val (a : ZMod (p^2))]
    rw [ZMod.val_natCast]
  rw [hcast]
  have h1 : a % p^2 % p = a % p := Nat.mod_mod_of_dvd a (⟨p, by ring⟩ : p ∣ p ^ 2)
  have hL : a % p^2 = p * ((a % p^2) / p) + a % p := by
    rw [← h1, Nat.div_add_mod]
  have hR : r.val + a % p = p * ((r.val + a % p) / p) + (r.val + a % p) % p :=
    (Nat.div_add_mod _ _).symm
  have hkey : r.val + p * y.val + a % p^2
      = (r.val + a % p) % p + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) := by
    calc r.val + p * y.val + a % p^2
        = r.val + p * y.val + (p * ((a % p^2) / p) + a % p) := by
            conv_lhs => rw [hL]
      _ = (r.val + a % p) + p * (y.val + (a % p^2) / p) := by ring
      _ = (p * ((r.val + a % p) / p) + (r.val + a % p) % p)
            + p * (y.val + (a % p^2) / p) := by
            conv_lhs => rw [hR]
      _ = (r.val + a % p) % p + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) := by ring
  have hfinal : (((r.val + p * y.val + a % (p^2)) : ℕ) : ZMod (p^2))
      = ((((r.val + a % p) % p
          + p * ((r.val + a % p) / p + a % (p^2) / p + y.val)) : ℕ) : ZMod (p^2)) := by
    rw [hkey]
  rw [← hfinal]
  push_cast
  ring

private lemma zmd_add_natCast [NeZero p] (a : ℕ) (r y : ZMod p) :
    zmd r y + ((a : ℕ) : ZMod (p^2))
      = ((((r.val + a % p) % p)
          + p * ((r.val + a % p) / p + a % (p^2) / p + y.val) : ℕ) : ZMod (p^2)) := by
  simpa only [zmd] using zmod_sq_add_digit (p := p) a r y

private lemma zmd_castHom (hp : p.Prime) [NeZero p] (r y : ZMod p) :
    ZMod.castHom (show p ∣ p^2 from ⟨p, by ring⟩) (ZMod p) (zmd r y) = r := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hd : p ∣ p ^ 2 := ⟨p, by ring⟩
  have h1 : ZMod.castHom hd (ZMod p) ((r.val : ℕ) : ZMod (p^2)) = (r.val : ZMod p) := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hd]
  have h2 : ZMod.castHom hd (ZMod p) ((p : ℕ) : ZMod (p^2)) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hd, ZMod.natCast_self]
  have h3 : ZMod.castHom hd (ZMod p) ((y.val : ℕ) : ZMod (p^2)) = (y.val : ZMod p) := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast hd]
  unfold zmd
  rw [map_add, map_mul, h1, h2, h3, zero_mul, add_zero, ZMod.natCast_zmod_val]

/-- Logarithmic derivative of a product of three linear factors. -/
private lemma deriv_prod_linear_eval {K : Type*} [Field K] (c : Fin 3 → K) (r : K)
    (h : ∀ l, r + c l ≠ 0) :
    (∏ l : Fin 3, (Polynomial.X + Polynomial.C (c l))).derivative.eval r
      = (∏ l : Fin 3, (r + c l)) * (∑ l : Fin 3, (r + c l)⁻¹) := by
  simp only [Fin.prod_univ_three, Fin.sum_univ_three]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, add_zero, mul_one, one_mul]
  field_simp [h 0, h 1, h 2]

/-- Derivative at a simple root of a product of three linear factors. -/
private lemma deriv_prod_linear_eval_neg_ne_zero {K : Type*} [Field K] (c : Fin 3 → K) (i3 : Fin 3)
    (h : ∀ l, l ≠ i3 → c l ≠ c i3) :
    (∏ l : Fin 3, (Polynomial.X + Polynomial.C (c l))).derivative.eval (-(c i3)) ≠ 0 := by
  set A₁ : Polynomial K := ∏ l ∈ Finset.univ.erase i3, (Polynomial.X + Polynomial.C (c l)) with hA1
  have hfact : (∏ l : Fin 3, (Polynomial.X + Polynomial.C (c l)))
      = A₁ * (Polynomial.X + Polynomial.C (c i3)) := by
    rw [hA1]
    rw [Finset.prod_erase_mul (Finset.univ) (fun l => Polynomial.X + Polynomial.C (c l))
      (Finset.mem_univ i3)]
  rw [hfact]
  have hderiv : Polynomial.derivative (A₁ * (Polynomial.X + Polynomial.C (c i3)))
      = Polynomial.derivative A₁ * (Polynomial.X + Polynomial.C (c i3)) + A₁ := by
    rw [Polynomial.derivative_mul]
    simp
  rw [hderiv]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  rw [neg_add_cancel, mul_zero, zero_add]
  rw [hA1]
  rw [Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro l hl
  rw [Finset.mem_erase] at hl
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  intro hc
  refine h l hl.1 ?_
  have h2 : c l - c i3 = 0 := by
    rw [sub_eq_add_neg, add_comm]
    exact hc
  exact sub_eq_zero.mp h2

/-- The `1 + p`-kernel shift for a character modulo `p ^ 2`. -/
private theorem chi_shift [Fact p.Prime] (χ : DirichletCharacter ℂ (p^2))
    {m K δ : ℕ} (hm : m < p) (hδ : (δ : ZMod p) * (m : ZMod p) = 1) :
    χ (((m + p * K : ℕ)) : ZMod (p^2))
      = χ (((m : ℕ)) : ZMod (p^2)) * (χ (((1 + p : ℕ)) : ZMod (p^2))) ^ (K * δ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hδm : ((δ * m : ℕ) : ZMod p) = 1 := by
    have h : ((δ : ZMod p) * (m : ZMod p)) = ((δ * m : ℕ) : ZMod p) := by push_cast; ring
    rw [← h]; exact hδ
  have hmδ : ((m * δ : ℕ) : ZMod p) = 1 := by rw [Nat.mul_comm]; exact hδm
  have hmul : (((K * (m * δ) : ℕ)) : ZMod p) = ((K : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, hmδ, mul_one]
  have hprime : (p : ZMod (p^2)) * (((K * (m * δ) : ℕ)) : ZMod (p^2))
      = (p : ZMod (p^2)) * ((K : ℕ) : ZMod (p^2)) :=
    mul_prime_eq_of_cast_eq _ _ (by simpa [ZMod.castHom_apply] using hmul)
  have hkey : (m : ZMod (p^2)) * (1 + (p : ZMod (p^2)) * ((K * δ : ℕ) : ZMod (p^2)))
      = (((m + p * K : ℕ)) : ZMod (p^2)) := by
    have h1 : (m : ZMod (p^2)) * ((p : ZMod (p^2)) * ((K * δ : ℕ) : ZMod (p^2)))
        = (p : ZMod (p^2)) * (((K * (m * δ) : ℕ)) : ZMod (p^2)) := by
      push_cast
      ring
    rw [mul_add, mul_one, h1, hprime]
    push_cast
    ring
  rw [← hkey, map_mul]
  congr 1
  have h2 : (1 : ZMod (p^2)) + (p : ZMod (p^2)) * ((K * δ : ℕ) : ZMod (p^2))
      = (1 + (p : ZMod (p^2))) ^ (K * δ) := by
    rw [pow_one_add_prime_eq]
    ring
  rw [h2, map_pow]
  congr 1
  push_cast
  ring

/-- Single-factor ratio: the `y`-dependence of `χ (zmd r y + c)` is a `p`-th root of unity
raised to the power `y`. -/
private lemma chi_factor_ratio [Fact p.Prime] (χ : DirichletCharacter ℂ (p^2)) (c : ℕ) (r : ZMod p)
    (hc : r + (c : ZMod p) ≠ 0) (y : ZMod p) :
    χ (zmd r y + ((c : ℕ) : ZMod (p^2)))
      = χ (zmd r 0 + ((c : ℕ) : ZMod (p^2)))
        * (χ (((1 + p : ℕ)) : ZMod (p^2))) ^ (y.val * ((r + (c : ZMod p))⁻¹).val) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hm_val : (r + (c : ZMod p)).val = (r.val + c % p) % p := by
    rw [ZMod.val_add, ZMod.val_natCast]
  have hm_eq : (((r.val + c % p) % p : ℕ) : ZMod p) = r + (c : ZMod p) := by
    rw [← hm_val, ZMod.natCast_zmod_val]
  have hδ : ((((r + (c : ZMod p))⁻¹).val : ℕ) : ZMod p)
      * (((r.val + c % p) % p : ℕ) : ZMod p) = 1 := by
    rw [hm_eq, ZMod.natCast_zmod_val]
    exact inv_mul_cancel₀ hc
  have hmlt : (r.val + c % p) % p < p := Nat.mod_lt _ hp.pos
  have hd : ∀ y : ZMod p, zmd r y + ((c : ℕ) : ZMod (p^2))
      = (((r.val + c % p) % p
          + p * ((r.val + c % p) / p + c % (p^2) / p + y.val) : ℕ) : ZMod (p^2)) :=
    fun y => zmd_add_natCast c r y
  have h1 : χ (zmd r y + ((c : ℕ) : ZMod (p^2)))
      = χ ((((r.val + c % p) % p : ℕ)) : ZMod (p^2))
        * (χ (((1 + p : ℕ)) : ZMod (p^2)))
            ^ (((r.val + c % p) / p + c % (p^2) / p + y.val)
                * (((r + (c : ZMod p))⁻¹).val)) := by
    rw [hd y]; exact chi_shift χ hmlt hδ
  have h0 : χ (zmd r 0 + ((c : ℕ) : ZMod (p^2)))
      = χ ((((r.val + c % p) % p : ℕ)) : ZMod (p^2))
        * (χ (((1 + p : ℕ)) : ZMod (p^2)))
            ^ (((r.val + c % p) / p + c % (p^2) / p + (0 : ZMod p).val)
                * (((r + (c : ZMod p))⁻¹).val)) := by
    rw [hd 0]; exact chi_shift χ hmlt hδ
  rw [h1, h0]
  rw [ZMod.val_zero]
  have hexp : ((r.val + c % p) / p + c % (p^2) / p + y.val)
      * (((r + (c : ZMod p))⁻¹).val)
      = ((r.val + c % p) / p + c % (p^2) / p + 0) * (((r + (c : ZMod p))⁻¹).val)
        + y.val * (((r + (c : ZMod p))⁻¹).val) := by ring
  rw [hexp, pow_add]
  ring

/-- Product form: the `y`-dependence of `∏_l χ (zmd r y + c l)`. -/
private lemma prod_chi_ratio [Fact p.Prime] (χ : DirichletCharacter ℂ (p^2)) (c : Fin 3 → ℕ)
    (r : ZMod p) (h : ∀ l : Fin 3, r + (c l : ZMod p) ≠ 0) (y : ZMod p) :
    (∏ l : Fin 3, χ (zmd r y + ((c l : ℕ) : ZMod (p^2))))
      = (∏ l : Fin 3, χ (zmd r 0 + ((c l : ℕ) : ZMod (p^2))))
        * ((χ (((1 + p : ℕ)) : ZMod (p^2)))
            ^ (∑ l : Fin 3, ((r + (c l : ZMod p))⁻¹).val)) ^ y.val := by
  have hterm : ∀ l : Fin 3, χ (zmd r y + ((c l : ℕ) : ZMod (p^2)))
      = χ (zmd r 0 + ((c l : ℕ) : ZMod (p^2)))
        * (χ (((1 + p : ℕ)) : ZMod (p^2))) ^ (y.val * ((r + (c l : ZMod p))⁻¹).val) :=
    fun l => chi_factor_ratio χ (c l) r (h l) y
  rw [Finset.prod_congr rfl (fun l _ => hterm l), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 1
  rw [Nat.mul_comm (∑ l : Fin 3, ((r + (c l : ZMod p))⁻¹).val) y.val, Finset.mul_sum]


/-- The entries of the six-tuple `![a 0, a 1, a 2, b 0, b 1, b 2]` below index `3`. -/
private lemma vec6_apply_lt (a b : Fin 3 → ℕ) (k : Fin 6) (hk : k.val < 3) :
    (![a 0, a 1, a 2, b 0, b 1, b 2] : Fin 6 → ℕ) k = a ⟨k.val, hk⟩ := by
  have hkv : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hkv with h | h | h
  · have hk0 : k = (0 : Fin 6) := Fin.ext (by simpa using h)
    subst hk0; simp
  · have hk0 : k = (1 : Fin 6) := Fin.ext (by simpa using h)
    subst hk0; simp
  · have hk0 : k = (2 : Fin 6) := Fin.ext (by simpa using h)
    subst hk0; simp

/-- The entries of the six-tuple `![a 0, a 1, a 2, b 0, b 1, b 2]` from index `3` on. -/
private lemma vec6_apply_ge (a b : Fin 3 → ℕ) (k : Fin 6) (hk : 3 ≤ k.val) :
    (![a 0, a 1, a 2, b 0, b 1, b 2] : Fin 6 → ℕ) k = b ⟨k.val - 3, by omega⟩ := by
  have hkv : k.val = 3 ∨ k.val = 4 ∨ k.val = 5 := by omega
  rcases hkv with h | h | h
  · have hk0 : k = (3 : Fin 6) := Fin.ext (by simpa using h)
    subst hk0; simp
  · have hk0 : k = (4 : Fin 6) := Fin.ext (by simpa using h)
    subst hk0; simp
  · have hk0 : k = (5 : Fin 6) := Fin.ext (by simpa using h)
    subst hk0; simp

/-- Correlation bound in the case where the `a`-value at the index `k` occurs exactly once. -/
private theorem unique_bound_a [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p^2)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (k : Fin 3)
    (ha : ∀ l : Fin 3, l ≠ k → (a l : ZMod p) ≠ (a k : ZMod p))
    (hb : ∀ l : Fin 3, (b l : ZMod p) ≠ (a k : ZMod p)) :
    ‖∑ x : ZMod (p^2), χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2)))))‖ ≤ 5 * (p : ℝ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hd : p ∣ p ^ 2 := ⟨p, by ring⟩
  set ζ : ℂ := χ (((1 + p : ℕ)) : ZMod (p^2)) with hζdef
  have hζ : IsPrimitiveRoot ζ p := by
    simpa [hζdef] using chi_one_add_primePow_isPrimitiveRoot p 2 hp2 (le_refl 2) χ hχ
  have hζpow : ζ ^ p = 1 := hζ.pow_eq_one
  have hζne : ζ ≠ 1 := hζ.ne_one hp.one_lt
  set A : Polynomial (ZMod p) := ∏ l : Fin 3, (Polynomial.X + Polynomial.C ((a l : ZMod p))) with hA
  set B : Polynomial (ZMod p) := ∏ l : Fin 3, (Polynomial.X + Polynomial.C ((b l : ZMod p))) with hB
  set P : Polynomial (ZMod p) := A.derivative * B - A * B.derivative with hP
  have hAeval : ∀ r : ZMod p, A.eval r = ∏ l : Fin 3, (r + (a l : ZMod p)) := by
    intro r
    rw [hA, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun l _ => by simp)
  have hBeval : ∀ r : ZMod p, B.eval r = ∏ l : Fin 3, (r + (b l : ZMod p)) := by
    intro r
    rw [hB, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun l _ => by simp)
  have hAdeg : A.natDegree ≤ 3 := by
    rw [hA]
    calc (∏ l : Fin 3, (Polynomial.X + Polynomial.C ((a l : ZMod p)))).natDegree
        ≤ ∑ l : Fin 3, (Polynomial.X + Polynomial.C ((a l : ZMod p))).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ = 3 := by
        rw [Fin.sum_univ_three]
        rw [Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C]
  have hBdeg : B.natDegree ≤ 3 := by
    rw [hB]
    calc (∏ l : Fin 3, (Polynomial.X + Polynomial.C ((b l : ZMod p)))).natDegree
        ≤ ∑ l : Fin 3, (Polynomial.X + Polynomial.C ((b l : ZMod p))).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ = 3 := by
        rw [Fin.sum_univ_three]
        rw [Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C]
  have hPdeg : P.natDegree ≤ 5 := by
    rw [hP]
    have h1 : (A.derivative * B).natDegree ≤ 5 := by
      calc (A.derivative * B).natDegree ≤ A.derivative.natDegree + B.natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ (A.natDegree - 1) + 3 := by
            have := Polynomial.natDegree_derivative_le A; omega
        _ ≤ 5 := by omega
    have h2 : (A * B.derivative).natDegree ≤ 5 := by
      calc (A * B.derivative).natDegree ≤ A.natDegree + B.derivative.natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 3 + (B.natDegree - 1) := by
            have := Polynomial.natDegree_derivative_le B; omega
        _ ≤ 5 := by omega
    calc (A.derivative * B - A * B.derivative).natDegree
        ≤ max (A.derivative * B).natDegree (A * B.derivative).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ 5 := max_le h1 h2
  have hPne : P ≠ 0 := by
    intro hP0
    have hzero : A.derivative * B = A * B.derivative := by
      have hh := hP0; rw [hP] at hh; exact sub_eq_zero.mp hh
    set γ : ZMod p := (a k : ZMod p) with hγ
    have hAroot : A.eval (-γ) = 0 := by
      rw [hAeval]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hγ])
    have hAdne : A.derivative.eval (-γ) ≠ 0 := by
      have hh := deriv_prod_linear_eval_neg_ne_zero (fun l => (a l : ZMod p)) k
        (fun l hl => ha l hl)
      simpa [hA, hγ] using hh
    have hBeq := congrArg (fun q : Polynomial (ZMod p) => q.eval (-γ)) hzero
    rw [Polynomial.eval_mul, Polynomial.eval_mul, hAroot, zero_mul] at hBeq
    have hBroot : B.eval (-γ) = 0 := by
      rcases mul_eq_zero.mp hBeq with hh | hh
      · exact absurd hh hAdne
      · exact hh
    rw [hBeval] at hBroot
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hBroot
    have hbl : (b l : ZMod p) = (a k : ZMod p) := by
      have h2 : (b l : ZMod p) - (a k : ZMod p) = 0 := by
        rw [← hγ, sub_eq_add_neg, add_comm]
        exact hl
      exact sub_eq_zero.mp h2
    exact hb l hbl
  have hS : (∑ x : ZMod (p^2), χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2))))))
      = ∑ x : ZMod (p^2), (∏ l : Fin 3, χ (x + (a l : ZMod (p^2))))
        * (∏ l : Fin 3, (χ⁻¹) (x + (b l : ZMod (p^2)))) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_prod χ (fun l => x + (a l : ZMod (p^2))) Finset.univ,
      star_apply_char χ (∏ l : Fin 3, (x + (b l : ZMod (p^2)))),
      map_prod (χ⁻¹) (fun l => x + (b l : ZMod (p^2))) Finset.univ]
  rw [hS]
  have hbij : Function.Bijective (fun am : ZMod p × ZMod p => zmd am.1 am.2) := by
    simpa [zmd] using zmod_sq_digits_bijective p
  have hsum1 : (∑ x : ZMod (p^2), (∏ l : Fin 3, χ (x + (a l : ZMod (p^2))))
        * (∏ l : Fin 3, (χ⁻¹) (x + (b l : ZMod (p^2)))))
      = ∑ am : ZMod p × ZMod p, (∏ l : Fin 3, χ (zmd am.1 am.2 + (a l : ZMod (p^2))))
        * (∏ l : Fin 3, (χ⁻¹) (zmd am.1 am.2 + (b l : ZMod (p^2)))) :=
    (Fintype.sum_bijective (fun am : ZMod p × ZMod p => zmd am.1 am.2) hbij _ _
      (fun _ => rfl)).symm
  rw [hsum1, Fintype.sum_prod_type]
  have hfiber : ∀ r : ZMod p, ‖∑ y : ZMod p, (∏ l : Fin 3, χ (zmd r y + (a l : ZMod (p^2))))
        * (∏ l : Fin 3, (χ⁻¹) (zmd r y + (b l : ZMod (p^2))))‖
      ≤ if P.eval r = 0 then (p : ℝ) else 0 := by
    intro r
    by_cases hAB : A.eval r * B.eval r = 0
    · have hzero : ∀ y : ZMod p, (∏ l : Fin 3, χ (zmd r y + (a l : ZMod (p^2))))
            * (∏ l : Fin 3, (χ⁻¹) (zmd r y + (b l : ZMod (p^2)))) = 0 := by
        intro y
        rcases mul_eq_zero.mp hAB with hA0 | hB0
        · have hprod0 : (∏ l : Fin 3, (r + (a l : ZMod p))) = 0 := by
            rw [← hAeval r]; exact hA0
          obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hprod0
          have hfac : χ (zmd r y + (a l : ZMod (p^2))) = 0 := by
            apply MulChar.map_nonunit
            intro hunit
            have hcast : ZMod.castHom hd (ZMod p) (zmd r y + (a l : ZMod (p^2))) = 0 := by
              have h2 : ZMod.castHom hd (ZMod p) ((a l : ZMod (p^2))) = (a l : ZMod p) := by
                rw [ZMod.castHom_apply, ZMod.cast_natCast hd]
              rw [map_add, zmd_castHom hp r y, h2]
              exact hl
            have := hunit.map (ZMod.castHom hd (ZMod p))
            rw [hcast] at this
            exact not_isUnit_zero this
          rw [Finset.prod_eq_zero (Finset.mem_univ l) hfac, zero_mul]
        · have hprod0 : (∏ l : Fin 3, (r + (b l : ZMod p))) = 0 := by
            rw [← hBeval r]; exact hB0
          obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hprod0
          have hfac : (χ⁻¹) (zmd r y + (b l : ZMod (p^2))) = 0 := by
            apply MulChar.map_nonunit
            intro hunit
            have hcast : ZMod.castHom hd (ZMod p) (zmd r y + (b l : ZMod (p^2))) = 0 := by
              have h2 : ZMod.castHom hd (ZMod p) ((b l : ZMod (p^2))) = (b l : ZMod p) := by
                rw [ZMod.castHom_apply, ZMod.cast_natCast hd]
              rw [map_add, zmd_castHom hp r y, h2]
              exact hl
            have := hunit.map (ZMod.castHom hd (ZMod p))
            rw [hcast] at this
            exact not_isUnit_zero this
          rw [show (∏ l : Fin 3, (χ⁻¹) (zmd r y + (b l : ZMod (p^2)))) = 0 from
            Finset.prod_eq_zero (Finset.mem_univ l) hfac, mul_zero]
      rw [Finset.sum_eq_zero (fun y _ => hzero y), norm_zero]
      split <;> positivity
    · have hAnz : A.eval r ≠ 0 := fun hh => hAB (by rw [hh, zero_mul])
      have hBnz : B.eval r ≠ 0 := fun hh => hAB (by rw [hh, mul_zero])
      have hAnz_l : ∀ l : Fin 3, r + (a l : ZMod p) ≠ 0 := fun l =>
        (Finset.prod_ne_zero_iff.mp (by rw [← hAeval r]; exact hAnz)) l (Finset.mem_univ l)
      have hBnz_l : ∀ l : Fin 3, r + (b l : ZMod p) ≠ 0 := fun l =>
        (Finset.prod_ne_zero_iff.mp (by rw [← hBeval r]; exact hBnz)) l (Finset.mem_univ l)
      set DA : ℕ := ∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹).val with hDA
      set DB : ℕ := ∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹).val with hDB
      set G : ℕ := DA + (p - 1) * DB with hG
      have hζinv : ζ⁻¹ = ζ ^ (p - 1) := by
        have h1 : ζ ^ (p - 1) * ζ = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hζpow]
        exact inv_eq_of_mul_eq_one_left h1
      have hAeq : ∀ y : ZMod p, (∏ l : Fin 3, χ (zmd r y + (a l : ZMod (p^2))))
          = (∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2)))) * (ζ ^ DA) ^ y.val := by
        intro y
        have hh := prod_chi_ratio χ a r hAnz_l y
        simpa [hζdef, hDA] using hh
      have hBinv : (χ⁻¹) (1 + (p : ZMod (p^2))) = ζ⁻¹ := by
        have hu : IsUnit (1 + (p : ZMod (p^2))) := by
          rw [show (1 + (p : ZMod (p^2))) = (((1 + p : ℕ)) : ZMod (p^2)) by push_cast; ring]
          rw [ZMod.isUnit_iff_coprime]
          simpa using coprime_one_add_prime_pow_pred hp (le_refl 2 : 2 ≤ 2)
        have hχu : χ (1 + (p : ZMod (p^2))) = ζ := by
          rw [hζdef]
          congr 1
          push_cast
          ring
        have hmul : (χ⁻¹) (1 + (p : ZMod (p^2))) * χ (1 + (p : ZMod (p^2))) = 1 := by
          rw [← MulChar.mul_apply, inv_mul_cancel]
          exact MulChar.one_apply hu
        rw [hχu] at hmul
        exact (inv_eq_of_mul_eq_one_left hmul).symm
      have hBeq : ∀ y : ZMod p, (∏ l : Fin 3, (χ⁻¹) (zmd r y + (b l : ZMod (p^2))))
          = (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2))))
            * ((ζ⁻¹) ^ DB) ^ y.val := by
        intro y
        have hh := prod_chi_ratio (χ⁻¹) b r hBnz_l y
        simpa [hDB, hBinv] using hh
      have hratio : ∀ y : ZMod p,
          (∏ l : Fin 3, χ (zmd r y + (a l : ZMod (p^2))))
            * (∏ l : Fin 3, (χ⁻¹) (zmd r y + (b l : ZMod (p^2))))
          = ((∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
              * (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2)))))
            * (ζ ^ G) ^ y.val := by
        intro y
        rw [hAeq y, hBeq y, hG]
        have h1 : (ζ⁻¹) ^ DB = ζ ^ ((p - 1) * DB) := by rw [hζinv, pow_mul]
        rw [h1, ← pow_mul, ← pow_mul, ← pow_mul]
        calc ((∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
              * ζ ^ (DA * y.val))
              * ((∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2))))
                * ζ ^ ((p - 1) * DB * y.val))
            = ((∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
                * (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2)))))
              * (ζ ^ (DA * y.val) * ζ ^ ((p - 1) * DB * y.val)) := by ring
          _ = ((∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
                * (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2)))))
              * ζ ^ (DA * y.val + (p - 1) * DB * y.val) := by rw [pow_add]
          _ = ((∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
                * (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2)))))
              * ζ ^ ((DA + (p - 1) * DB) * y.val) := by
                congr 1
                ring
      have hAderiv : A.derivative.eval r = A.eval r * (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) := by
        rw [hAeval r, hA]
        exact deriv_prod_linear_eval (fun l => (a l : ZMod p)) r hAnz_l
      have hBderiv : B.derivative.eval r = B.eval r * (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) := by
        rw [hBeval r, hB]
        exact deriv_prod_linear_eval (fun l => (b l : ZMod p)) r hBnz_l
      have hPform : P.eval r = A.eval r * B.eval r
          * ((∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
              - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹)) := by
        rw [hP]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul]
        rw [hAderiv, hBderiv]
        ring
      have hGeq : (G : ZMod p) = (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
          - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) := by
        have h1 : ((∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹).val : ℕ) : ZMod p)
            = (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) := by
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl (fun l _ => ZMod.natCast_zmod_val _)
        have h2 : ((∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹).val : ℕ) : ZMod p)
            = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) := by
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl (fun l _ => ZMod.natCast_zmod_val _)
        have h3 : ((p - 1 : ℕ) : ZMod p) = -1 := by
          rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one, ZMod.natCast_self, zero_sub]
        rw [hG, hDA, hDB, Nat.cast_add, Nat.cast_mul, h1, h2, h3]
        ring
      have hGiff : ζ ^ G = 1 ↔ P.eval r = 0 := by
        constructor
        · intro hG1
          have hdvd : p ∣ G := (hζ.pow_eq_one_iff_dvd G).mp hG1
          have hcast : (G : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff G p).mpr hdvd
          rw [hGeq] at hcast
          rw [hPform, hcast, mul_zero]
        · intro hP0
          have hσ : (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹)
              - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹) = 0 := by
            have hh := hP0
            rw [hPform] at hh
            exact (mul_eq_zero.mp hh).resolve_left hAB
          have hcast : (G : ZMod p) = 0 := by rw [hGeq, hσ]
          have hdvd : p ∣ G := (ZMod.natCast_eq_zero_iff G p).mp hcast
          exact (hζ.pow_eq_one_iff_dvd G).mpr hdvd
      have hCnorm : ‖(∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
          * (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2))))‖ ≤ 1 := by
        rw [norm_mul]
        have h1 : ‖(∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))‖ ≤ 1 := by
          calc ‖(∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))‖
              ≤ ∏ l : Fin 3, ‖χ (zmd r 0 + (a l : ZMod (p^2)))‖ :=
                Finset.norm_prod_le _ _
            _ ≤ ∏ l : Fin 3, (1 : ℝ) := Finset.prod_le_prod₀ (fun l _ => norm_nonneg _)
                  (fun l _ => DirichletCharacter.norm_le_one χ _)
            _ = 1 := by simp
        have h2 : ‖(∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2))))‖ ≤ 1 := by
          calc ‖(∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2))))‖
              ≤ ∏ l : Fin 3, ‖(χ⁻¹) (zmd r 0 + (b l : ZMod (p^2)))‖ :=
                Finset.norm_prod_le _ _
            _ ≤ ∏ l : Fin 3, (1 : ℝ) := Finset.prod_le_prod₀ (fun l _ => norm_nonneg _)
                  (fun l _ => DirichletCharacter.norm_le_one (χ⁻¹) _)
            _ = 1 := by simp
        have h1' := norm_nonneg (∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
        have h2' := norm_nonneg (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2))))
        nlinarith
      rw [Finset.sum_congr rfl (fun y _ => hratio y), ← Finset.mul_sum, norm_mul]
      by_cases hP0 : P.eval r = 0
      · rw [if_pos hP0]
        have hG1 : ζ ^ G = 1 := hGiff.mpr hP0
        have hsum : (∑ y : ZMod p, (ζ ^ G) ^ y.val) = (p : ℂ) := by
          rw [hG1]
          simp [Finset.sum_const, ZMod.card]
        rw [hsum, Complex.norm_natCast]
        calc ‖(∏ l : Fin 3, χ (zmd r 0 + (a l : ZMod (p^2))))
              * (∏ l : Fin 3, (χ⁻¹) (zmd r 0 + (b l : ZMod (p^2))))‖ * (p : ℝ)
            ≤ 1 * (p : ℝ) := mul_le_mul_of_nonneg_right hCnorm (Nat.cast_nonneg p)
          _ = (p : ℝ) := one_mul _
      · rw [if_neg hP0]
        have hG1 : ζ ^ G ≠ 1 := fun hh => hP0 (hGiff.mp hh)
        have hsum : (∑ y : ZMod p, (ζ ^ G) ^ y.val) = 0 :=
          sum_val_pow_eq_zero (by rw [← pow_mul, Nat.mul_comm, pow_mul, hζpow, one_pow]) hG1
        rw [hsum, norm_zero, mul_zero]
  calc ‖∑ r : ZMod p, ∑ y : ZMod p, (∏ l : Fin 3, χ (zmd r y + (a l : ZMod (p^2))))
        * (∏ l : Fin 3, (χ⁻¹) (zmd r y + (b l : ZMod (p^2))))‖
      ≤ ∑ r : ZMod p, ‖∑ y : ZMod p, (∏ l : Fin 3, χ (zmd r y + (a l : ZMod (p^2))))
        * (∏ l : Fin 3, (χ⁻¹) (zmd r y + (b l : ZMod (p^2))))‖ := norm_sum_le _ _
    _ ≤ ∑ r : ZMod p, (if P.eval r = 0 then (p : ℝ) else 0) :=
        Finset.sum_le_sum (fun r _ => hfiber r)
    _ = (p : ℝ) * ((Finset.univ.filter (fun r : ZMod p => P.eval r = 0)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (p : ℝ) * (P.natDegree : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast card_roots_le P hPne) (Nat.cast_nonneg p)
    _ ≤ (p : ℝ) * 5 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hPdeg) (Nat.cast_nonneg p)
    _ = 5 * (p : ℝ) := by ring

/-- Swapping the two tuples conjugates the correlation sum. -/
private lemma sum_swap [NeZero (p^2)] (χ : DirichletCharacter ℂ (p^2)) (a b : Fin 3 → ℕ) :
    (∑ x : ZMod (p^2), χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2))))))
      = (starRingEnd ℂ) (∑ x : ZMod (p^2), χ (∏ l : Fin 3, (x + (b l : ZMod (p^2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (a l : ZMod (p^2)))))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [starRingEnd_apply, star_mul, star_star]

/-- Correlation bound in the case where the `b`-value at the index `k` occurs exactly once. -/
private theorem unique_bound_b [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p^2)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (k : Fin 3)
    (hb : ∀ l : Fin 3, l ≠ k → (b l : ZMod p) ≠ (b k : ZMod p))
    (ha : ∀ l : Fin 3, (a l : ZMod p) ≠ (b k : ZMod p)) :
    ‖∑ x : ZMod (p^2), χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2)))))‖ ≤ 5 * (p : ℝ) := by
  have h := unique_bound_a hp2 χ hχ b a k hb ha
  rw [sum_swap χ a b, Complex.norm_conj]
  exact h


/-- **Local cubic correlation bound at a prime square.**  For an odd prime `p`, a primitive
non-trivial character `χ` modulo `p^2`, and integers `a 0, a 1, a 2, b 0, b 1, b 2`, the cubic
correlation is bounded by `6 p` times the product over `j ≠ i` of `gcd (p^2) |v_i - v_j|`,
where `v : Fin 6 → ℕ` is `![](a0,a1,a2,b0,b1,b2)`.  This is the `e = 2` cubic analogue of
`charCorrelation_primePow_sharp`.  Proof sketch: split `x = r + p*y` and use the decomposition
of `χ` mod `p^2` into a character of `ZMod p` times the character `λ` of the kernel
`(1+pZ)/(1+p^2Z) ≅ Z/p`, with `χ (1 + p*k) = χ (1+p)^k` (`primePowKernel_char_pow`) and
`χ (1+p)` a primitive `p`-th root (`chi_one_add_primePow_isPrimitiveRoot`).  Then the inner
sum over `y` vanishes unless `p ∣ F'(r)`, where `F = A * B^(orderOf χ - 1)`; the contributing
`r` are the roots of the degree-`≤ 5` polynomial `A' B + ((orderOf χ - 1) mod p) A B'`, so
there are at most `5` of them unless it vanishes identically mod `p` (in which case
`A ≡ c B` mod `p`, which forces `p ∣ (v_i - v_j)` for some `j ≠ i`). -/
theorem charCorrelation6_primeSq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (χ : DirichletCharacter ℂ (p ^ 2)) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    (a b : Fin 3 → ℕ) (i : Fin 6) :
    ‖∑ x : ZMod (p ^ 2), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 2)))) *
        (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 2)))))‖
      ≤ 6 * (p : ℝ) * ∏ j ∈ Finset.univ.erase i,
          (((Nat.gcd (p ^ 2) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
             - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  set v : Fin 6 → ℕ := ![a 0, a 1, a 2, b 0, b 1, b 2] with hv
  have htriv : ‖∑ x : ZMod (p^2), χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2)))))‖ ≤ (p:ℝ)^2 := by
    calc _ ≤ ∑ x : ZMod (p^2), ‖χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2)))))‖ := norm_sum_le _ _
      _ ≤ ∑ x : ZMod (p^2), (1:ℝ) := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          rw [norm_mul, Complex.norm_conj]
          have h1 := DirichletCharacter.norm_le_one χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
          have h2 := DirichletCharacter.norm_le_one χ (∏ l : Fin 3, (x + (b l : ZMod (p^2))))
          have h1' := norm_nonneg (χ (∏ l : Fin 3, (x + (a l : ZMod (p^2)))))
          have h2' := norm_nonneg (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2)))))
          nlinarith
      _ = (p:ℝ)^2 := by
          simp [Finset.sum_const, ZMod.card, pow_two]
  have hzmod : ∀ j : Fin 6, (v i : ZMod p) = (v j : ZMod p) →
      p ∣ (((v i : ℤ) - (v j : ℤ)).natAbs) := by
    intro j h
    have h2 : (v i) ≡ (v j) [MOD p] := (ZMod.natCast_eq_natCast_iff (v i) (v j) p).mp h
    have h3 : (p : ℤ) ∣ ((v j : ℤ) - (v i : ℤ)) := Nat.ModEq.dvd h2
    have h4 : (p : ℤ) ∣ ((v i : ℤ) - (v j : ℤ)) := by
      rw [show ((v i : ℤ) - (v j : ℤ)) = -(((v j : ℤ) - (v i : ℤ))) by ring]
      exact dvd_neg.mpr h3
    obtain ⟨k, hk⟩ := h4
    exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul, Int.natAbs_natCast]⟩
  by_cases hcase : ∃ j ∈ Finset.univ.erase i, p ∣ (((v i : ℤ) - (v j : ℤ)).natAbs)
  · obtain ⟨j0, hj0mem, hj0dvd⟩ := hcase
    have hgj0 : p ≤ Nat.gcd (p^2) (((v i : ℤ) - (v j0 : ℤ)).natAbs) := by
      have h1 : p ∣ p^2 := ⟨p, by ring⟩
      have h3 : p ∣ Nat.gcd (p^2) (((v i : ℤ) - (v j0 : ℤ)).natAbs) := Nat.dvd_gcd h1 hj0dvd
      exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (pow_pos hp.pos 2)) h3
    have hprodNat : p ≤ ∏ j ∈ Finset.univ.erase i,
        Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) :=
      le_trans hgj0 (Finset.single_le_prod'
        (f := fun j => Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs))
        (fun j _ => Nat.succ_le_iff.mpr (Nat.gcd_pos_of_pos_left _ (pow_pos hp.pos 2))) hj0mem)
    have hprod : (p : ℝ) ≤ ∏ j ∈ Finset.univ.erase i,
        ((Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ) := by
      have hcast : ((∏ j ∈ Finset.univ.erase i,
          Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ)
          = ∏ j ∈ Finset.univ.erase i,
            ((Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ) := by
        push_cast
        rfl
      rw [← hcast]
      exact Nat.cast_le.mpr hprodNat
    calc ‖∑ x : ZMod (p ^ 2), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 2)))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 2)))))‖
        ≤ (p:ℝ)^2 := htriv
      _ ≤ 6 * (p : ℝ) * ∏ j ∈ Finset.univ.erase i,
            ((Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ) := by
          have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
          nlinarith [hprod, hp0]
  · have hnot : ∀ j ∈ Finset.univ.erase i, ¬ p ∣ (((v i : ℤ) - (v j : ℤ)).natAbs) := by
      intro j hj hh; exact hcase ⟨j, hj, hh⟩
    have hun2 : ∀ j : Fin 6, j ≠ i → (v i : ZMod p) ≠ (v j : ZMod p) := by
      intro j hj hcontra
      have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
      exact hnot j hjmem (hzmod j hcontra)
    have hgcd1 : ∀ j ∈ Finset.univ.erase i,
        Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) = 1 := by
      intro j hj
      have hcop : Nat.Coprime (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) := by
        rw [show p^2 = p * p from pow_two p, Nat.coprime_mul_iff_left]
        exact ⟨hp.coprime_iff_not_dvd.mpr (hnot j hj), hp.coprime_iff_not_dvd.mpr (hnot j hj)⟩
      exact hcop.gcd_eq_one
    have hprod1 : (∏ j ∈ Finset.univ.erase i,
        ((Nat.gcd (p^2) (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ)) = 1 := by
      rw [Finset.prod_congr rfl (fun j hj => by rw [hgcd1 j hj])]
      simp
    have hS5 : ‖∑ x : ZMod (p^2), χ (∏ l : Fin 3, (x + (a l : ZMod (p^2))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p^2)))))‖ ≤ 5 * (p : ℝ) := by
      rcases lt_or_ge i.val 3 with hi | hi
      · refine unique_bound_a hp2 χ hχ a b ⟨i.val, hi⟩ ?_ ?_
        · intro l hl
          have hjl : (⟨l.val, by omega⟩ : Fin 6) ≠ i := by
            intro hh; exact hl (Fin.ext (by simpa using congrArg Fin.val hh : l.val = i.val))
          have hh := hun2 ⟨l.val, by omega⟩ hjl
          rw [hv] at hh
          simp only [vec6_apply_lt a b i hi,
            vec6_apply_lt a b ⟨l.val, by omega⟩ (by omega : l.val < 3)] at hh
          intro hcontra
          exact hh (by simpa using hcontra.symm)
        · intro l
          have hjl : (⟨3 + l.val, by omega⟩ : Fin 6) ≠ i := by
            intro hh
            have h2 := congrArg Fin.val hh
            simp only [Fin.val_mk] at h2
            omega
          have hh := hun2 ⟨3 + l.val, by omega⟩ hjl
          rw [hv] at hh
          simp only [vec6_apply_lt a b i hi,
            vec6_apply_ge a b ⟨3 + l.val, by omega⟩ (by omega : 3 ≤ 3 + l.val)] at hh
          intro hcontra
          exact hh (by simpa using hcontra.symm)
      · refine unique_bound_b hp2 χ hχ a b ⟨i.val - 3, by omega⟩ ?_ ?_
        · intro l hl
          have hjl : (⟨3 + l.val, by omega⟩ : Fin 6) ≠ i := by
            intro hh
            apply hl
            have h2 := congrArg Fin.val hh
            simp only [Fin.val_mk] at h2
            exact Fin.ext (by omega : l.val = i.val - 3)
          have hh := hun2 ⟨3 + l.val, by omega⟩ hjl
          rw [hv] at hh
          simp only [vec6_apply_ge a b i hi,
            vec6_apply_ge a b ⟨3 + l.val, by omega⟩ (by omega : 3 ≤ 3 + l.val)] at hh
          intro hcontra
          exact hh (by simpa using hcontra.symm)
        · intro l
          have hjl : (⟨l.val, by omega⟩ : Fin 6) ≠ i := by
            intro hh
            have h2 := congrArg Fin.val hh
            simp only [Fin.val_mk] at h2
            omega
          have hh := hun2 ⟨l.val, by omega⟩ hjl
          rw [hv] at hh
          simp only [vec6_apply_ge a b i hi,
            vec6_apply_lt a b ⟨l.val, by omega⟩ (by omega : l.val < 3)] at hh
          intro hcontra
          exact hh (by simpa using hcontra.symm)
    rw [hprod1, mul_one]
    calc ‖∑ x : ZMod (p ^ 2), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ 2)))) *
          (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ 2)))))‖
        ≤ 5 * (p : ℝ) := hS5
      _ ≤ 6 * (p : ℝ) := by
          have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
          linarith

end Commons.NumberTheory.DirichletCharacter
