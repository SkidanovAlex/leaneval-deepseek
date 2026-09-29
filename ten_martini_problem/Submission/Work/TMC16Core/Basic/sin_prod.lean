import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

open Finset

/-- For `ω` a primitive `q`-th root of unity, `∏_{j<q} (c - ω^j) = c^q - 1`. -/
lemma prod_range_primitive_root (q : ℕ) (hq : 0 < q) (ω : ℂ) (hω : IsPrimitiveRoot ω q)
    (c : ℂ) : ∏ j ∈ Finset.range q, (c - ω^j) = c^q - 1 := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hpoly := Polynomial.X_pow_sub_one_eq_prod hq hω
  have hset : Polynomial.nthRootsFinset q (1:ℂ) = (Finset.range q).image (fun j => ω^j) := by
    ext x
    rw [Polynomial.mem_nthRootsFinset hq, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hω hx
      exact ⟨i, Finset.mem_range.mpr hi, hix⟩
    · rintro ⟨j, hj, rfl⟩
      rw [← pow_mul, mul_comm j q, pow_mul, hω.pow_eq_one, one_pow]
  have hinj : Set.InjOn (fun j => ω^j) ↑(Finset.range q) := by
    intro a ha b hb hab
    exact IsPrimitiveRoot.pow_inj hω (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab
  rw [hset, Finset.prod_image hinj] at hpoly
  have := congrArg (fun p : Polynomial ℂ => p.eval c) hpoly
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_prod] at this
  exact this.symm

/-- For `ω` a primitive `q`-th root of unity, `∏_{j<q} (A ω^j - B) = (-1)^{q+1} (A^q - B^q)`. -/
lemma prod_range_shift (q : ℕ) (hq : 0 < q) (ω : ℂ) (hω : IsPrimitiveRoot ω q) (A B : ℂ) :
    ∏ j ∈ Finset.range q, (A * ω^j - B) = (-1 : ℂ)^(q+1) * (A^q - B^q) := by
  have key := prod_range_primitive_root q hq ω hω
  have hBA : ∏ j ∈ Finset.range q, (B - A * ω^j) = B^q - A^q := by
    rcases eq_or_ne A 0 with hA | hA
    · subst hA
      simp [Finset.prod_const, Finset.card_range, zero_pow hq.ne']
    · have hfac : ∀ j, B - A * ω^j = A * (B / A - ω^j) := by
        intro j; field_simp
      simp_rw [hfac]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, key (B/A)]
      have hAB : A * (B / A) = B := by field_simp
      rw [mul_sub, mul_one, ← mul_pow, hAB]
  calc ∏ j ∈ Finset.range q, (A * ω^j - B)
      = ∏ j ∈ Finset.range q, (-(B - A*ω^j)) := by
        apply Finset.prod_congr rfl; intro j hj; ring
    _ = (-1:ℂ)^q * ∏ j ∈ Finset.range q, (B - A*ω^j) := by
        rw [Finset.prod_neg, Finset.card_range]
    _ = (-1:ℂ)^q * (B^q - A^q) := by rw [hBA]
    _ = (-1:ℂ)^(q+1) * (A^q - B^q) := by rw [pow_succ]; ring

/-- `(e^{iπ/q})^{q(q-1)/2} = i^{q-1}`. -/
lemma eta_pow (q : ℕ) (hq : 0 < q) :
    (Complex.exp (((Real.pi/(q:ℝ)) : ℂ) * Complex.I))^(q*(q-1)/2) = Complex.I^(q-1) := by
  have h2 : 2 ∣ q*(q-1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self q)
  have hcast : ((q*(q-1)/2 : ℕ) : ℝ) = (q:ℝ)*((q-1:ℕ):ℝ)/2 := by
    rw [Nat.cast_div h2 (by norm_num)]; push_cast; ring
  have hI : Complex.exp (((Real.pi/2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [show (((Real.pi/2 : ℝ)) : ℂ) = (Real.pi : ℂ)/2 from by rw [Complex.ofReal_div]; norm_num]
    exact Complex.exp_pi_div_two_mul_I
  have hreal : ((q*(q-1)/2 : ℕ) : ℝ) * (Real.pi/(q:ℝ)) = ((q-1:ℕ):ℝ) * (Real.pi/2) := by
    rw [hcast]; field_simp
  have harg : ((q*(q-1)/2 : ℕ) : ℂ) * (((Real.pi/(q:ℝ)) : ℂ) * Complex.I)
      = (((q-1:ℕ):ℂ) * (((Real.pi/2 : ℝ) : ℂ) * Complex.I)) := by
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact_mod_cast hreal
  calc (Complex.exp (((Real.pi/(q:ℝ)) : ℂ) * Complex.I))^(q*(q-1)/2)
      = Complex.exp (((q*(q-1)/2 : ℕ) : ℂ) * (((Real.pi/(q:ℝ)) : ℂ) * Complex.I)) := by
        rw [Complex.exp_nat_mul]
    _ = Complex.exp ((((q-1:ℕ):ℂ)) * (((Real.pi/2 : ℝ) : ℂ) * Complex.I)) := by
        rw [harg]
    _ = Complex.exp (((Real.pi/2 : ℝ) : ℂ) * Complex.I)^(q-1) := by
        rw [Complex.exp_nat_mul]
    _ = Complex.I^(q-1) := by rw [hI]

/-- `(i^{q-1})^{-1} · (-1)^{q+1} = i^{q-1}`. -/
lemma I_pow_inv_const (q : ℕ) (hq : 0 < q) :
    (Complex.I^(q-1))⁻¹ * (-1 : ℂ)^(q+1) = Complex.I^(q-1) := by
  rw [← inv_pow, Complex.inv_I, neg_pow]
  have h1 : (-1:ℂ)^(q-1) * (-1)^(q+1) = 1 := by
    rw [← pow_add, show q-1 + (q+1) = 2*q by omega, pow_mul]; norm_num
  calc (-1:ℂ)^(q-1)*Complex.I^(q-1)*(-1)^(q+1)
      = ((-1:ℂ)^(q-1)*(-1)^(q+1)) * Complex.I^(q-1) := by ring
    _ = 1 * Complex.I^(q-1) := by rw [h1]
    _ = Complex.I^(q-1) := by ring

/-- `(-i)^q · i^{q-1} = -i`. -/
lemma neg_I_pow_const (q : ℕ) (hq : 0 < q) :
    (-Complex.I)^q * Complex.I^(q-1) = -Complex.I := by
  have hI2 : Complex.I^2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
  have hIpow : Complex.I^(2*q-1) = (-1)^(q-1) * Complex.I := by
    have h1 : 2*q-1 = 2*(q-1)+1 := by omega
    rw [h1, pow_add, pow_one, pow_mul, hI2]
  have hm1 : (-1:ℂ)^(2*q-1) = -1 := by
    have h1 : 2*q-1 = 2*(q-1)+1 := by omega
    rw [h1, pow_add, pow_one, pow_mul]; norm_num
  calc (-Complex.I)^q * Complex.I^(q-1)
      = (-1:ℂ)^q * (Complex.I^q * Complex.I^(q-1)) := by rw [neg_pow]; ring
    _ = (-1:ℂ)^q * Complex.I^(q + (q-1)) := by rw [← pow_add]
    _ = (-1:ℂ)^q * Complex.I^(2*q-1) := by rw [show q + (q-1) = 2*q-1 by omega]
    _ = (-1:ℂ)^q * ((-1)^(q-1) * Complex.I) := by rw [hIpow]
    _ = ((-1:ℂ)^q * (-1)^(q-1)) * Complex.I := by rw [← mul_assoc]
    _ = (-1:ℂ)^(q + (q-1)) * Complex.I := by rw [← pow_add]
    _ = (-1:ℂ)^(2*q-1) * Complex.I := by rw [show q + (q-1) = 2*q-1 by omega]
    _ = -Complex.I := by rw [hm1]; ring

/-- `((-1)^q · i^{q-1}) · (i/2)^q = -i/2^q`. -/
lemma coef_I (q : ℕ) (hq : 0 < q) :
    ((-1:ℂ)^q * Complex.I^(q-1)) * (Complex.I/2)^q = -Complex.I/2^q := by
  rw [div_pow]
  rw [show ((-1:ℂ)^q * Complex.I^(q-1)) * (Complex.I^q / 2^q)
        = ((-1)^q * Complex.I^q) * Complex.I^(q-1) / 2^q by ring]
  rw [← neg_pow, neg_I_pow_const q hq]

/-- The main complex product identity. -/
lemma prod_exp_diff (q : ℕ) (hq : 0 < q) (x : ℝ) :
    ∏ j ∈ Finset.range q,
        (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I)
          - (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹)
      = Complex.I^(q-1)
        * (Complex.exp (↑(q*x) * Complex.I) - (Complex.exp (↑(q*x) * Complex.I))⁻¹) := by
  set A : ℂ := Complex.exp ((x:ℂ)*Complex.I) with hA
  set η : ℂ := Complex.exp ((↑(Real.pi/(q:ℝ)) : ℂ)*Complex.I) with hη
  have hηne : η ≠ 0 := by rw [hη]; exact Complex.exp_ne_zero _
  have hE : ∀ j : ℕ, Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I) = A * η^j := by
    intro j; rw [hA, hη, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hEq : Complex.exp (↑(q*x) * Complex.I) = A^q := by
    rw [hA, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hω : IsPrimitiveRoot (η^2) q := by
    have hη2q : IsPrimitiveRoot η (2*q) := by
      rw [hη]
      have h := Complex.isPrimitiveRoot_exp (2*q) (by omega : 2*q ≠ 0)
      convert h using 2
      push_cast
      field_simp
      try ring
    exact hη2q.pow (by omega) rfl
  have hfac : ∀ j, A * η^j - (A*η^j)⁻¹ = (η⁻¹)^j * (A * (η^2)^j - A⁻¹) := by
    intro j
    have h1 : (η⁻¹)^j * (η^2)^j = η^j := by
      rw [← mul_pow, show η⁻¹ * η^2 = η by rw [sq, ← mul_assoc, inv_mul_cancel₀ hηne, one_mul]]
    rw [mul_inv, ← inv_pow, mul_sub, ← h1]
    ring
  have hshift : ∏ j ∈ Finset.range q, (A * (η^2)^j - A⁻¹) = (-1:ℂ)^(q+1) * (A^q - (A⁻¹)^q) :=
    prod_range_shift q hq (η^2) hω A A⁻¹
  have hprodη : ∏ j ∈ Finset.range q, (η⁻¹)^j = (Complex.I^(q-1))⁻¹ := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, inv_pow]
    congr 1
    rw [hη, Complex.ofReal_div]
    exact eta_pow q hq
  calc ∏ j ∈ Finset.range q,
        (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I)
          - (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹)
      = ∏ j ∈ Finset.range q, (A * η^j - (A*η^j)⁻¹) := by
        apply Finset.prod_congr rfl; intro j _; rw [hE j]
    _ = ∏ j ∈ Finset.range q, ((η⁻¹)^j * (A * (η^2)^j - A⁻¹)) :=
        Finset.prod_congr rfl (fun j _ => hfac j)
    _ = (∏ j ∈ Finset.range q, (η⁻¹)^j) * (∏ j ∈ Finset.range q, (A * (η^2)^j - A⁻¹)) :=
        Finset.prod_mul_distrib
    _ = (Complex.I^(q-1))⁻¹ * ((-1:ℂ)^(q+1) * (A^q - (A⁻¹)^q)) := by rw [hprodη, hshift]
    _ = Complex.I^(q-1) * (A^q - (A^q)⁻¹) := by
        rw [← mul_assoc, I_pow_inv_const q hq, inv_pow]
    _ = Complex.I^(q-1) * (Complex.exp (↑(q*x) * Complex.I)
          - (Complex.exp (↑(q*x) * Complex.I))⁻¹) := by rw [hEq]

/-- The complex sine product identity. -/
lemma prod_sin_c (q : ℕ) (hq : 0 < q) (x : ℝ) :
    ∏ j ∈ Finset.range q, Complex.sin (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) : ℂ)
      = Complex.sin (↑(q*x) : ℂ) / (2:ℂ)^(q-1) := by
  have hsin : ∀ θ : ℝ, Complex.sin (↑θ : ℂ)
      = ((Complex.exp ((↑θ : ℂ)*Complex.I))⁻¹ - Complex.exp ((↑θ : ℂ)*Complex.I))
          * (Complex.I/2) := by
    intro θ
    rw [Complex.sin, show -(↑θ : ℂ) * Complex.I = -((↑θ:ℂ) * Complex.I) by ring, Complex.exp_neg]
    ring
  have hdiff := prod_exp_diff q hq x
  have hneg : ∀ j ∈ Finset.range q,
      ((Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹
        - Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))
      = - (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I)
        - (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹) := by
    intro j _; ring
  have hsinq : Complex.sin (↑(q*x) : ℂ)
      = ((Complex.exp (↑(q*x) * Complex.I))⁻¹ - Complex.exp (↑(q*x) * Complex.I)) * (Complex.I/2) :=
    hsin (q*x)
  calc ∏ j ∈ Finset.range q, Complex.sin (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) : ℂ)
      = ∏ j ∈ Finset.range q, ((Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹
            - Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I)) * (Complex.I/2) :=
        Finset.prod_congr rfl (fun j _ => hsin _)
    _ = (∏ j ∈ Finset.range q, ((Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹
            - Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))) * (Complex.I/2)^q := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = ((-1:ℂ)^q * ∏ j ∈ Finset.range q, (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I)
            - (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹)) * (Complex.I/2)^q := by
        congr 1
        rw [show (∏ j ∈ Finset.range q, ((Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹
              - Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I)))
            = ∏ j ∈ Finset.range q, -(Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I)
              - (Complex.exp (↑(x + (j:ℝ)*Real.pi/(q:ℝ)) * Complex.I))⁻¹) from
            Finset.prod_congr rfl (fun j hj => hneg j hj)]
        rw [Finset.prod_neg, Finset.card_range]
    _ = ((-1:ℂ)^q * (Complex.I^(q-1) * (Complex.exp (↑(q*x) * Complex.I)
            - (Complex.exp (↑(q*x) * Complex.I))⁻¹))) * (Complex.I/2)^q := by rw [hdiff]
    _ = Complex.I * ((Complex.exp (↑(q*x) * Complex.I))⁻¹ - Complex.exp (↑(q*x) * Complex.I))
            / 2^q := by
        set E : ℂ := Complex.exp (↑(q*x) * Complex.I) with hEdef
        have hcoef := coef_I q hq
        rw [show ((-1:ℂ)^q * (Complex.I^(q-1) * (E - E⁻¹))) * (Complex.I/2)^q
              = (((-1:ℂ)^q * Complex.I^(q-1)) * (Complex.I/2)^q) * (E - E⁻¹) by ring]
        rw [hcoef]
        rw [show (-Complex.I/2^q) * (E - E⁻¹) = Complex.I * (E⁻¹ - E) / 2^q by
              rw [show (-Complex.I/2^q) * (E - E⁻¹) = (-Complex.I * (E - E⁻¹))/2^q by ring]
              congr 1; ring]
    _ = Complex.sin (↑(q*x) : ℂ) / (2:ℂ)^(q-1) := by
        rw [hsinq]
        have h2q : (2:ℂ)^q = (2:ℂ)^(q-1) * 2 := by rw [← pow_succ]; congr 1; omega
        rw [h2q]
        field_simp

/-- The real product identity used by the Ten Martini development. -/
theorem sin_prod (q : ℕ) (hq : 0 < q) (x : ℝ) :
    ∏ j ∈ Finset.range q, Real.sin (x + (j : ℝ) * Real.pi / (q : ℝ)) =
      Real.sin ((q : ℝ) * x) / 2 ^ (q - 1) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod]
  simp only [Complex.ofReal_sin]
  rw [Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_pow, Complex.ofReal_ofNat]
  exact prod_sin_c q hq x

end Work.TMC16Core.Basic
