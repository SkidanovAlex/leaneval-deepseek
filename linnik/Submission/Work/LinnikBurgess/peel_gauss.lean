import Mathlib
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs

/-!
# The two-term stationary-phase peel (odd `p`)

This file proves `Work.LinnikBurgess.peel_gauss`, the `p`-odd analogue of
`Submission.Work.LinnikBurgess.twoPow_innerSum_factor`: the inner sum over the `p^(e-m)` lifts
`x = y + p^m w` of the cubic correlation summand factors as the constant
`χ (∏ (y+a_l)) · conj (χ (∏ (y+b_l)))` times the quadratic Gauss sum
`gaussQuad p (e-m) θ α γ` with `θ = psiFun p e m χ 1`, `α = defect1`, `γ = -(1/2) p^m defect2`.

The proof is assembled from three independent pieces, all proved below:

* `peelG_inner_factor` : the per-lift factorization of the summand as
  `C · ψ(W·D₁ − (p^m/2)W²D₂)` with `ψ = psiFun p e m χ = χ ∘ Efun`;
* `peelG_psiFun_castHom` : `ψ` factors through `ZMod (p^e) → ZMod (p^(e-m))` and equals
  `θ ^ (castHom u).val`, because `Efun` has period `p^(e-m)`;
* `peelG_castHom_phase` : the reduction of the quadratic phase `W·D₁ − (p^m/2)W²D₂` to
  `ZMod (p^(e-m))` is the quadratic polynomial `α w + γ w²` of the statement.
-/

open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.LinnikBurgess

variable {p e m : ℕ} [Fact p.Prime]

/-! ## Elementary facts about units and the truncated exponential -/

/-- `2` is a unit of `ZMod (p^e)` for an odd prime `p`. -/
lemma isUnit_two_zmod (hp2 : p ≠ 2) : IsUnit (2 : ZMod (p ^ e)) := by
  have h : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp2 h1
  exact ((ZMod.isUnit_iff_coprime 2 (p ^ e)).mpr (h.pow_right e))

/-- `(y + u : ZMod (p^e))` is a unit when `p ∤ y + u`. -/
lemma isUnit_shift_of_not_dvd (y u : ℕ) (h : ¬ p ∣ y + u) :
    IsUnit (((y + u : ℕ) : ZMod (p ^ e))) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (Nat.coprime_comm.mp (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr h)).pow_right e

/-- **The truncated exponential has period `p^(e-m)`:** `Efun p e m (p^(e-m)) = 1`. -/
lemma Efun_pow_sub_eq_one (hm : 1 ≤ m) (h2m : 2 * m ≤ e) :
    Efun p e m (((p ^ (e - m) : ℕ)) : ZMod (p ^ e)) = 1 := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hz : ((p ^ m : ℕ) : ZMod (p ^ e)) * (((p ^ (e - m) : ℕ)) : ZMod (p ^ e)) = 0 := by
    rw [← Nat.cast_mul, show p ^ m * p ^ (e - m) = p ^ e by rw [← pow_add]; congr 1; omega,
      ZMod.natCast_self]
  rw [Efun, hz]
  ring

/-! ## `psiFun` as an additive character of `ZMod (p^(e-m))` -/

/-- **`psiFun` factors through the reduction `ZMod (p^e) → ZMod (p^(e-m))`.**
`psiFun p e m χ u = θ ^ (castHom u).val` with `θ = psiFun p e m χ 1`: `ψ` is an additive
character of `ZMod (p^e)` of period dividing `p^(e-m)`. -/
theorem peelG_psiFun_castHom (hp2 : p ≠ 2) (hm : 1 ≤ m) (h3 : e ≤ 3 * m) (h2m : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (u : ZMod (p ^ e)) :
    psiFun p e m χ u
      = (psiFun p e m χ 1)
          ^ ((ZMod.castHom (pow_dvd_pow p (Nat.sub_le e m)) (ZMod (p ^ (e - m))) u).val) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hval : ((((p ^ (e - m) : ℕ)) : ZMod (p ^ e))).val = p ^ (e - m) := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  have hθ : (psiFun p e m χ 1) ^ (p ^ (e - m)) = 1 := by
    rw [← hval, (psiFun_eq_theta_pow hp2 h3 χ (((p ^ (e - m) : ℕ)) : ZMod (p ^ e))).symm,
      psiFun, Efun_pow_sub_eq_one (p := p) (e := e) (m := m) hm h2m, map_one]
  rw [psiFun_eq_theta_pow hp2 h3 χ u]
  have hred : (ZMod.castHom (pow_dvd_pow p (Nat.sub_le e m)) (ZMod (p ^ (e - m))) u).val
      = u.val % p ^ (e - m) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [hred]
  exact pow_eq_pow_mod u.val hθ

/-! ## The quadratic phase, reduced modulo `p^(e-m)` -/

/-- **The quadratic phase reduced modulo `p^(e-m)`.**  The image of `W·D₁ − (P/2)·W²·D₂` under
`ZMod.castHom` is `D₁·w − (p^m/2)·D₂·w²` in the variable `w : ZMod (p^(e-m))`. -/
theorem peelG_castHom_phase (hp2 : p ≠ 2) (hm : 1 ≤ m) (h2m : 2 * m ≤ e)
    (a b : Fin 3 → ℕ) (y : ℕ) (w : ZMod (p ^ (e - m))) :
    ZMod.castHom (pow_dvd_pow p (Nat.sub_le e m)) (ZMod (p ^ (e - m)))
        ((((w.val : ℕ) : ZMod (p ^ e))) * defect1 p e a b y
          - ((((p ^ m : ℕ) : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹)
              * (((w.val : ℕ) : ZMod (p ^ e))) ^ 2 * defect2 p e a b y))
      = (((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) * w
        + (-(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
            * (((defect2 p e a b y).val : ℕ) : ZMod (p ^ (e - m)))) * w ^ 2 := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ (e - m)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hd : p ^ (e - m) ∣ p ^ e := pow_dvd_pow p (Nat.sub_le e m)
  have hme : m < e := by omega
  have hW : ZMod.castHom hd (ZMod (p ^ (e - m))) (((w.val : ℕ) : ZMod (p ^ e))) = w := by
    have hlt : w.val < p ^ e :=
      lt_of_lt_of_le (ZMod.val_lt w) (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.sub_le e m))
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_cast_of_lt hlt, ZMod.natCast_zmod_val]
  have hD1 : ZMod.castHom hd (ZMod (p ^ (e - m))) (defect1 p e a b y)
      = (((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hD2 : ZMod.castHom hd (ZMod (p ^ (e - m))) (defect2 p e a b y)
      = (((defect2 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hP : ZMod.castHom hd (ZMod (p ^ (e - m))) (((p ^ m : ℕ) : ZMod (p ^ e)))
      = (((p ^ m : ℕ)) : ZMod (p ^ (e - m))) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val,
      ZMod.val_cast_of_lt (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hme)]
  have h2inv : ZMod.castHom hd (ZMod (p ^ (e - m))) ((2 : ZMod (p ^ e))⁻¹)
      = (2 : ZMod (p ^ (e - m)))⁻¹ := by
    refine (ZMod.inv_eq_of_mul_eq_one (p ^ (e - m)) (2 : ZMod (p ^ (e - m)))
      (ZMod.castHom hd (ZMod (p ^ (e - m))) ((2 : ZMod (p ^ e))⁻¹)) ?_).symm
    have h2c : (2 : ZMod (p ^ (e - m)))
        = ZMod.castHom hd (ZMod (p ^ (e - m))) (2 : ZMod (p ^ e)) := by
      rw [map_ofNat]
    rw [h2c, ← map_mul, ZMod.mul_inv_of_unit _ (isUnit_two_zmod (p := p) (e := e) hp2), map_one]
  simp only [map_sub, map_mul, map_pow]
  rw [hW, hD1, hD2, hP, h2inv]
  ring

/-! ## The per-lift factorization of the correlation summand -/

/-- Elementary factorization: if `x` is invertible (`x * x⁻¹ = 1`) then
`x + P * W = x * (1 + P * x⁻¹ * W)`. -/
lemma add_mul_eq_mul_one_add_inv {N : ℕ} (x P W : ZMod N) (h : x * x⁻¹ = 1) :
    x + P * W = x * (1 + P * x⁻¹ * W) := by
  have h2 : x * (P * x⁻¹ * W) = P * W := by
    rw [show x * (P * x⁻¹ * W) = P * (x * x⁻¹) * W by ring, h, mul_one]
  rw [mul_add, mul_one, h2]

/-- `psiFun` is an additive character: `ψ (∑ u_l) = ∏ ψ (u_l)` over `Fin 3`. -/
lemma psiFun_sum3 (hp2 : p ≠ 2) (h3 : e ≤ 3 * m) (χ : DirichletCharacter ℂ (p ^ e))
    (u : Fin 3 → ZMod (p ^ e)) :
    psiFun p e m χ (∑ l : Fin 3, u l) = ∏ l : Fin 3, psiFun p e m χ (u l) := by
  rw [Fin.sum_univ_three, Fin.prod_univ_three, psiFun_add (p := p) (e := e) (m := m) hp2 h3 χ
      (u 0 + u 1) (u 2),
    psiFun_add (p := p) (e := e) (m := m) hp2 h3 χ (u 0) (u 1)]

/-- The product of three factors `(1 + P t_l)` is the exponential of the sum of the phases. -/
lemma chi_prod_one_add_eq_psiFun (hp2 : p ≠ 2) (h3 : e ≤ 3 * m)
    (χ : DirichletCharacter ℂ (p ^ e)) (t : Fin 3 → ZMod (p ^ e)) :
    χ (∏ l : Fin 3, (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l))
      = psiFun p e m χ
          (∑ l : Fin 3,
            (t l - ((p ^ m : ℕ) : ZMod (p ^ e)) * (t l) ^ 2 * (2 : ZMod (p ^ e))⁻¹)) := by
  have hfac : ∀ l : Fin 3, χ (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l)
      = psiFun p e m χ
          (t l - ((p ^ m : ℕ) : ZMod (p ^ e)) * (t l) ^ 2 * (2 : ZMod (p ^ e))⁻¹) := by
    intro l
    rw [psiFun, ← Efun_one_add (p := p) (e := e) (m := m) hp2 h3 (t l)]
  rw [map_prod χ (fun l => 1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l) Finset.univ,
    Finset.prod_congr rfl (fun l _ => hfac l),
    ← psiFun_sum3 (p := p) (e := e) (m := m) hp2 h3 χ
      (fun l => t l - ((p ^ m : ℕ) : ZMod (p ^ e)) * (t l) ^ 2 * (2 : ZMod (p ^ e))⁻¹)]

/-- The conjugate of `χ (∏ (1 + P t_l))` is `ψ` of the negated sum of the phases. -/
lemma conj_chi_prod_one_add_eq_psiFun (hp2 : p ≠ 2) (h3 : e ≤ 3 * m) (hm : 1 ≤ m)
    (χ : DirichletCharacter ℂ (p ^ e)) (t : Fin 3 → ZMod (p ^ e)) :
    (starRingEnd ℂ) (χ (∏ l : Fin 3, (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l)))
      = psiFun p e m χ
          (-(∑ l : Fin 3,
            (t l - ((p ^ m : ℕ) : ZMod (p ^ e)) * (t l) ^ 2 * (2 : ZMod (p ^ e))⁻¹))) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hfac : ∀ l : Fin 3,
      (starRingEnd ℂ) (χ (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l))
        = psiFun p e m χ
            (-(t l - ((p ^ m : ℕ) : ZMod (p ^ e)) * (t l) ^ 2 * (2 : ZMod (p ^ e))⁻¹)) := by
    intro l
    have hE : Efun p e m
        (t l - ((p ^ m : ℕ) : ZMod (p ^ e)) * (t l) ^ 2 * (2 : ZMod (p ^ e))⁻¹)
        = 1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l :=
      Efun_one_add (p := p) (e := e) (m := m) hp2 h3 (t l)
    have hunit : IsUnit (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l) :=
      hE ▸ Efun_isUnit (p := p) (e := e) (m := m) hm _
    rw [Commons.NumberTheory.DirichletCharacter.star_chi_eq_chi_inv χ _ hunit, psiFun]
    congr 1
    rw [← hE, Efun_neg (p := p) (e := e) (m := m) hp2 h3]
  rw [map_prod χ (fun l => 1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l) Finset.univ,
    map_prod (starRingEnd ℂ)
      (fun l => χ (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * t l)) Finset.univ,
    Finset.prod_congr rfl (fun l _ => hfac l),
    ← psiFun_sum3 (p := p) (e := e) (m := m) hp2 h3 χ
      (fun l => -(t l - ((p ^ m : ℕ) : ZMod (p ^ e)) * (t l) ^ 2 * (2 : ZMod (p ^ e))⁻¹)),
    Finset.sum_neg_distrib]

/-- The sum of three two-term phases is the quadratic phase `W·Σu − (P·c)W²·Σu²`. -/
lemma fin3_phase_sum {R : Type*} [CommRing R] (u : Fin 3 → R) (P W c : R) :
    (∑ l : Fin 3, (u l * W - P * (u l * W) ^ 2 * c))
      = W * (∑ l : Fin 3, u l) - (P * c) * W ^ 2 * (∑ l : Fin 3, (u l) ^ 2) := by
  simp only [Fin.sum_univ_three]
  ring

/-- **The per-lift factorization of the cubic correlation summand.** -/
theorem peelG_inner_factor (hp2 : p ≠ 2) (hm : 1 ≤ m) (h3 : e ≤ 3 * m) (h2m : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) (y : ℕ) (hy : UnitAt p y a b)
    (w : ZMod (p ^ (e - m))) :
    χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
          * ((w.val : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
          * ((w.val : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e)))))
    = (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e))))))
      * psiFun p e m χ ((((w.val : ℕ) : ZMod (p ^ e))) * defect1 p e a b y
          - ((((p ^ m : ℕ) : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹)
              * (((w.val : ℕ) : ZMod (p ^ e))) ^ 2 * defect2 p e a b y)) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  set Pc : ZMod (p ^ e) := ((p ^ m : ℕ) : ZMod (p ^ e)) with hPc
  set Wc : ZMod (p ^ e) := ((w.val : ℕ) : ZMod (p ^ e)) with hWc
  set A : Fin 3 → ZMod (p ^ e) := fun l => ((y + a l : ℕ) : ZMod (p ^ e)) with hA
  set B : Fin 3 → ZMod (p ^ e) := fun l => ((y + b l : ℕ) : ZMod (p ^ e)) with hB
  have hAun : ∀ l : Fin 3, IsUnit (A l) :=
    fun l => isUnit_shift_of_not_dvd (p := p) (e := e) y (a l) ((hy l).1)
  have hBun : ∀ l : Fin 3, IsUnit (B l) :=
    fun l => isUnit_shift_of_not_dvd (p := p) (e := e) y (b l) ((hy l).2)
  -- bridge the statement's expressions with `A`, `B`, `Pc`, `Wc`
  have hconva : ∀ l : Fin 3,
      ((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
        + ((a l : ℕ) : ZMod (p ^ e)) = A l + Pc * Wc := by
    intro l
    simp only [hA, hPc, hWc]
    push_cast
    ring
  have hconvb : ∀ l : Fin 3,
      ((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
        + ((b l : ℕ) : ZMod (p ^ e)) = B l + Pc * Wc := by
    intro l
    simp only [hB, hPc, hWc]
    push_cast
    ring
  have hA0 : ∀ l : Fin 3, ((y : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e)) = A l := by
    intro l
    simp only [hA]
    push_cast
    ring
  have hB0 : ∀ l : Fin 3, ((y : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e)) = B l := by
    intro l
    simp only [hB]
    push_cast
    ring
  -- the product factorization
  have h1a : (∏ l : Fin 3, (A l + Pc * Wc))
      = (∏ l : Fin 3, A l) * ∏ l : Fin 3, (1 + Pc * (A l)⁻¹ * Wc) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl
      (fun l _ => add_mul_eq_mul_one_add_inv (A l) Pc Wc (ZMod.mul_inv_of_unit _ (hAun l)))
  have h1b : (∏ l : Fin 3, (B l + Pc * Wc))
      = (∏ l : Fin 3, B l) * ∏ l : Fin 3, (1 + Pc * (B l)⁻¹ * Wc) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl
      (fun l _ => add_mul_eq_mul_one_add_inv (B l) Pc Wc (ZMod.mul_inv_of_unit _ (hBun l)))
  -- apply `χ` to both sides
  have h2a : χ (∏ l : Fin 3, (A l + Pc * Wc))
      = χ (∏ l : Fin 3, A l) * χ (∏ l : Fin 3, (1 + Pc * (A l)⁻¹ * Wc)) := by
    rw [h1a, map_mul]
  have h2b : χ (∏ l : Fin 3, (B l + Pc * Wc))
      = χ (∏ l : Fin 3, B l) * χ (∏ l : Fin 3, (1 + Pc * (B l)⁻¹ * Wc)) := by
    rw [h1b, map_mul]
  have h2bc : (starRingEnd ℂ) (χ (∏ l : Fin 3, (B l + Pc * Wc)))
      = (starRingEnd ℂ) (χ (∏ l : Fin 3, B l))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (1 + Pc * (B l)⁻¹ * Wc))) := by
    rw [h2b, map_mul]
  -- the two phases
  have h3a : χ (∏ l : Fin 3, (1 + Pc * (A l)⁻¹ * Wc))
      = psiFun p e m χ
          (∑ l : Fin 3, ((A l)⁻¹ * Wc - Pc * ((A l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹)) := by
    rw [show (∏ l : Fin 3, (1 + Pc * (A l)⁻¹ * Wc))
        = ∏ l : Fin 3, (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((A l)⁻¹ * Wc)) from
      Finset.prod_congr rfl (fun l _ => by rw [hPc]; ring)]
    exact chi_prod_one_add_eq_psiFun (p := p) (e := e) (m := m) hp2 h3 χ
      (fun l => (A l)⁻¹ * Wc)
  have h3b : (starRingEnd ℂ) (χ (∏ l : Fin 3, (1 + Pc * (B l)⁻¹ * Wc)))
      = psiFun p e m χ
          (-(∑ l : Fin 3, ((B l)⁻¹ * Wc - Pc * ((B l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹))) := by
    rw [show (∏ l : Fin 3, (1 + Pc * (B l)⁻¹ * Wc))
        = ∏ l : Fin 3, (1 + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((B l)⁻¹ * Wc)) from
      Finset.prod_congr rfl (fun l _ => by rw [hPc]; ring)]
    exact conj_chi_prod_one_add_eq_psiFun (p := p) (e := e) (m := m) hp2 h3 hm χ
      (fun l => (B l)⁻¹ * Wc)
  -- the sums
  have hUa : (∑ l : Fin 3, ((A l)⁻¹ * Wc - Pc * ((A l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹))
      = Wc * (∑ l : Fin 3, (A l)⁻¹)
        - (Pc * (2 : ZMod (p ^ e))⁻¹) * Wc ^ 2 * (∑ l : Fin 3, ((A l)⁻¹) ^ 2) :=
    fin3_phase_sum (R := ZMod (p ^ e)) (fun l => (A l)⁻¹) Pc Wc (2 : ZMod (p ^ e))⁻¹
  have hUb : (∑ l : Fin 3, ((B l)⁻¹ * Wc - Pc * ((B l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹))
      = Wc * (∑ l : Fin 3, (B l)⁻¹)
        - (Pc * (2 : ZMod (p ^ e))⁻¹) * Wc ^ 2 * (∑ l : Fin 3, ((B l)⁻¹) ^ 2) :=
    fin3_phase_sum (R := ZMod (p ^ e)) (fun l => (B l)⁻¹) Pc Wc (2 : ZMod (p ^ e))⁻¹
  have hD1eq : defect1 p e a b y
      = (∑ l : Fin 3, (A l)⁻¹) - (∑ l : Fin 3, (B l)⁻¹) := by
    simp only [defect1, hA, hB]
  have hD2eq : defect2 p e a b y
      = (∑ l : Fin 3, ((A l)⁻¹) ^ 2) - (∑ l : Fin 3, ((B l)⁻¹) ^ 2) := by
    simp only [defect2, hA, hB]
  have hphase :
      (∑ l : Fin 3, ((A l)⁻¹ * Wc - Pc * ((A l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹))
        + (-(∑ l : Fin 3, ((B l)⁻¹ * Wc - Pc * ((B l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹)))
      = Wc * defect1 p e a b y
        - (Pc * (2 : ZMod (p ^ e))⁻¹) * Wc ^ 2 * defect2 p e a b y := by
    rw [hUa, hUb, hD1eq, hD2eq]
    ring
  -- assemble
  have hψ : psiFun p e m χ
        (∑ l : Fin 3, ((A l)⁻¹ * Wc - Pc * ((A l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹))
      * psiFun p e m χ
        (-(∑ l : Fin 3, ((B l)⁻¹ * Wc - Pc * ((B l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹)))
      = psiFun p e m χ (Wc * defect1 p e a b y
          - (Pc * (2 : ZMod (p ^ e))⁻¹) * Wc ^ 2 * defect2 p e a b y) := by
    rw [← psiFun_add (p := p) (e := e) (m := m) hp2 h3 χ _ _, hphase]
  calc χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
          * ((w.val : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
          + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
          + ((b l : ℕ) : ZMod (p ^ e)))))
      = χ (∏ l : Fin 3, (A l + Pc * Wc))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (B l + Pc * Wc))) := by
        rw [Finset.prod_congr rfl (fun l _ => hconva l),
          Finset.prod_congr rfl (fun l _ => hconvb l)]
    _ = (χ (∏ l : Fin 3, A l) * (starRingEnd ℂ) (χ (∏ l : Fin 3, B l)))
        * (psiFun p e m χ
            (∑ l : Fin 3, ((A l)⁻¹ * Wc - Pc * ((A l)⁻¹ * Wc) ^ 2 * (2 : ZMod (p ^ e))⁻¹))
          * psiFun p e m χ
            (-(∑ l : Fin 3, ((B l)⁻¹ * Wc - Pc * ((B l)⁻¹ * Wc) ^ 2
              * (2 : ZMod (p ^ e))⁻¹)))) := by
        rw [h2a, h2bc, h3a, h3b]
        ring
    _ = (χ (∏ l : Fin 3, A l) * (starRingEnd ℂ) (χ (∏ l : Fin 3, B l)))
        * psiFun p e m χ (Wc * defect1 p e a b y
            - (Pc * (2 : ZMod (p ^ e))⁻¹) * Wc ^ 2 * defect2 p e a b y) := by
        rw [hψ]
    _ = (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3,
            (((y : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e))))))
        * psiFun p e m χ ((((w.val : ℕ) : ZMod (p ^ e))) * defect1 p e a b y
            - ((((p ^ m : ℕ) : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹)
                * (((w.val : ℕ) : ZMod (p ^ e))) ^ 2 * defect2 p e a b y)) := by
        rw [show (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
            = ∏ l : Fin 3, A l from Finset.prod_congr rfl (fun l _ => hA0 l),
          show (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e))))
            = ∏ l : Fin 3, B l from Finset.prod_congr rfl (fun l _ => hB0 l)]

/-- **The two-term stationary-phase peel.**  Let `p` be an odd prime, `m ≥ 1`, `e ≤ 3m` and
`2m ≤ e`, `χ` a Dirichlet character mod `p^e`, `a b : Fin 3 → ℕ` and `y` a unit at `p`
(`UnitAt p y a b`).  Then the inner sum over the `p^(e-m)` lifts `x = y + p^m w` of the cubic
correlation factors as the constant `χ(∏(y+a_l))·conj χ(∏(y+b_l))` times the quadratic Gauss sum
`∑_w θ^((α w + γ w^2).val)`, where `θ = psiFun p e m χ 1 = χ(1 + p^m + p^{2m}/2)` is the
additive character of the peeled phase, `α = defect1 p e a b y` and `γ = -(1/2) p^m · defect2`.

Mathematically: `∏_l (y + p^m w + a_l) = (∏_l (y+a_l)) · Φ_a(w)` with
`Φ_a(w) = ∏_l (1 + p^m (y+a_l)^{-1} w)`, and `χ(Φ_a(w)) conj χ(Φ_b(w)) = ψ(phase(w))` where
`phase(w) = D₁(y) w - p^m D₂(y) w²/2`, by `Efun_add`, `Efun_one_add` and `conj χ u = χ u⁻¹`.
The p=2 analogue is `Submission.Work.LinnikBurgess.twoPow_innerSum_factor`. -/
theorem peel_gauss {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h3 : e ≤ 3 * m) (h2m : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) (y : ℕ) (hy : UnitAt p y a b) :
    (∑ w : ZMod (p ^ (e - m)),
        χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
              * ((w.val : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
              * ((w.val : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e))))))
      = (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e))))))
        * gaussQuad p (e - m) (psiFun p e m χ 1)
            (((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m)))
            (-(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
              * (((defect2 p e a b y).val : ℕ) : ZMod (p ^ (e - m)))) := by
  have key : ∀ w : ZMod (p ^ (e - m)),
      χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
            * ((w.val : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
            + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
            + ((b l : ℕ) : ZMod (p ^ e)))))
      = (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3,
            (((y : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e))))))
        * (psiFun p e m χ 1) ^ (((((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) * w
            + (-(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
                * (((defect2 p e a b y).val : ℕ) : ZMod (p ^ (e - m)))) * w ^ 2).val) := by
    intro w
    rw [peelG_inner_factor (p := p) (e := e) (m := m) hp2 hm h3 h2m χ a b y hy w,
      peelG_psiFun_castHom (p := p) (e := e) (m := m) hp2 hm h3 h2m χ
        ((((w.val : ℕ) : ZMod (p ^ e))) * defect1 p e a b y
          - ((((p ^ m : ℕ) : ZMod (p ^ e)) * (2 : ZMod (p ^ e))⁻¹)
              * (((w.val : ℕ) : ZMod (p ^ e))) ^ 2 * defect2 p e a b y)),
      peelG_castHom_phase (p := p) (e := e) (m := m) hp2 hm h2m a b y w]
  rw [Finset.sum_congr rfl (fun w _ => key w), gaussQuad, Finset.mul_sum]

end Work.LinnikBurgess
