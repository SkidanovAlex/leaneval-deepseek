import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.newton_series
import Submission.Work.BMF.adi_defs
import Submission.Work.N8.IntegralOnDilIff
import Submission.Work.N8.q0v2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial

/-!
# Arithmetic core of the "`q₀ ≪ 1`" step of the N8 assembly

Supporting lemmas for `Work.N8.q0_arith_v2`:

* `q0v2_fact_mul_binP_coeff` : `i! * (C(X,i)).coeff m` is the integer coefficient of
  `descPochhammer ℤ i`;
* `q0v2_fact_coeff_int` : `k!` times any coefficient of an integer-valued polynomial of degree
  `≤ k` is an integer (Newton series);
* `q0v2_isCoprime_aux` : coprimality of the numerator and the minimal denominator;
* `q0v2_denom_exists` : every coefficient of degree `≤ k` of a polynomial integral on `qℤ`
  has a denominator;
* `q0v2_le_prod_denom` : the minimal modulus is bounded by the product of the denominators;
* `q0v2_denom_dvd` : the Bézout/gcd step producing `(β / gcd β k!) ∣ Z`;
* `q0v2_root_le` : `q ≤ M^k` implies `q^(1/k)/k! ≤ M`.
-/

/-- The coefficient of `X^m` in `i! · C(X,i) = X(X-1)⋯(X-i+1)` is an integer. -/
theorem q0v2_fact_mul_binP_coeff (i m : ℕ) :
    (i.factorial : ℝ) * (Work.BMF.binP i).coeff m = ((descPochhammer ℤ i).coeff m : ℝ) := by
  have hfac : ((i.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  rw [Work.BMF.binP, Polynomial.coeff_C_mul, ← descPochhammer_map (Int.castRingHom ℝ) i,
    Polynomial.coeff_map]
  simp only [Int.coe_castRingHom]
  rw [← mul_assoc, mul_inv_cancel₀ hfac, one_mul]

/-- `k!` times any coefficient of a polynomial that is integer-valued on `ℤ` and has degree
`≤ k` is an integer. -/
theorem q0v2_fact_coeff_int {P : Polynomial ℝ} {k : ℕ} (hint : Work.BMF.IntegralOn 1 P)
    (hdeg : P.natDegree ≤ k) (m : ℕ) :
    ∃ z : ℤ, (k.factorial : ℝ) * P.coeff m = z := by
  obtain ⟨c, hc⟩ := Work.BMF.newton_series k P hint hdeg
  have hterm : ∀ i, i ≤ k → (k.factorial : ℝ) * (Work.BMF.binP i).coeff m
      = (((k.factorial / i.factorial : ℕ) * (descPochhammer ℤ i).coeff m : ℤ) : ℝ) := by
    intro i hik
    obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial hik
    have hdiv : k.factorial / i.factorial = d := by
      rw [hd, Nat.mul_div_cancel_left d (Nat.factorial_pos i)]
    rw [hdiv, hd]
    push_cast
    linear_combination (d : ℝ) * q0v2_fact_mul_binP_coeff i m
  refine ⟨∑ i ∈ Finset.range (k + 1),
    c i * ((k.factorial / i.factorial : ℕ) * (descPochhammer ℤ i).coeff m), ?_⟩
  have hcoeff : P.coeff m
      = ∑ i ∈ Finset.range (k + 1), (c i : ℝ) * (Work.BMF.binP i).coeff m := by
    rw [hc, Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_C_mul]
  rw [hcoeff, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [show (k.factorial : ℝ) * ((c i : ℝ) * (Work.BMF.binP i).coeff m)
        = (c i : ℝ) * ((k.factorial : ℝ) * (Work.BMF.binP i).coeff m) by ring,
      hterm i hik]
  push_cast
  ring

/-- If `β` is coprime to `|a|` then `IsCoprime (β : ℤ) a`. -/
theorem q0v2_isCoprime_aux {β : ℕ} {a : ℤ} (h : Nat.Coprime β a.natAbs) :
    IsCoprime (β : ℤ) a := by
  have h1 : IsCoprime (β : ℤ) ((a.natAbs : ℕ) : ℤ) := Nat.Coprime.isCoprime h
  rcases Int.natAbs_eq a with hh | hh
  · rwa [hh]
  · rw [hh, IsCoprime.neg_right_iff]
    exact h1

/-- Every coefficient of degree `≤ k` of a polynomial integral on `qℤ` (`q > 0`) has a
denominator. -/
theorem q0v2_denom_exists {γ : Polynomial ℝ} {k m q : ℕ}
    (hq : 0 < q) (hdeg : γ.natDegree ≤ k) (hm : m ≤ k)
    (hint : Work.BMF.IntegralOn (q : ℝ) γ) :
    ∃ β : ℕ, IsDenom γ m β := by
  have hPint : Work.BMF.IntegralOn 1 (Work.BMF.dil (q : ℝ) γ) :=
    (Work.N8.IntegralOnDilIff q γ).mp hint
  have hPdeg : (Work.BMF.dil (q : ℝ) γ).natDegree ≤ k :=
    le_trans (Work.BMF.natDegree_dil_le _ _) hdeg
  obtain ⟨z, hz⟩ := q0v2_fact_coeff_int hPint hPdeg m
  have hcoe : (Work.BMF.dil (q : ℝ) γ).coeff m = γ.coeff m * (q : ℝ) ^ m := by
    rw [Work.BMF.coeff_dil]
  have hz' : (z : ℝ) = (k.factorial : ℝ) * γ.coeff m * (q : ℝ) ^ m := by
    rw [← hz, hcoe]
    ring
  refine ⟨k.factorial * q ^ k, Nat.mul_pos (Nat.factorial_pos k) (pow_pos hq k), ?_⟩
  refine ⟨(q : ℤ) ^ (k - m) * z, ?_⟩
  have hsplit : (q : ℝ) ^ k = (q : ℝ) ^ (k - m) * (q : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  push_cast
  rw [hz', hsplit]
  ring

/-- If `γ` has degree `≤ k` and every coefficient `γ.coeff m` with `m ≤ k` has a denominator,
and `q` is the least positive integer with `IntegralOn q γ`, then `q` is at most the product of
the denominators of the non-constant coefficients up to degree `k`. -/
theorem q0v2_le_prod_denom (k q : ℕ) (γ : Polynomial ℝ) (hdeg : γ.natDegree ≤ k)
    (hden : ∀ m : ℕ, m ≤ k → ∃ β : ℕ, IsDenom γ m β)
    (hint : Work.BMF.IntegralOn (q : ℝ) γ)
    (hmin : ∀ r : ℕ, 1 ≤ r → Work.BMF.IntegralOn (r : ℝ) γ → q ≤ r) :
    q ≤ ∏ m ∈ Finset.Icc 1 k, denom γ m := by
  classical
  set D : ℕ := ∏ m ∈ Finset.Icc 1 k, denom γ m with hD
  have hDpos : 0 < D := by
    rw [hD]
    refine Finset.prod_pos fun m hm => ?_
    have h1 : 1 ≤ denom γ m := one_le_denom (hden m (Finset.mem_Icc.mp hm).2)
    omega
  have hAex : ∀ j : ℕ, ∃ z : ℤ, (z : ℝ) = (denom γ j : ℝ) * γ.coeff j := by
    intro j
    by_cases hjk : j ≤ k
    · exact (denom_spec (hden j hjk)).2
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (not_le.mp hjk)),
        mul_zero, Int.cast_zero]
  choose A hA using hAex
  have hDγ : ∀ j : ℕ, 1 ≤ j → (D : ℝ) * γ.coeff j
      = (A j : ℝ) * ((D / denom γ j : ℕ) : ℝ) := by
    intro j hj1
    by_cases hjk : j ≤ k
    · have hdvd : denom γ j ∣ D := by
        rw [hD]
        exact Finset.dvd_prod_of_mem (fun m => denom γ m) (Finset.mem_Icc.mpr ⟨hj1, hjk⟩)
      have hsplit : (D : ℝ) = (denom γ j : ℝ) * ((D / denom γ j : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hsplit, hA j]
      ring
    · have hγ0 : γ.coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (not_le.mp hjk))
      have hA0 : (A j : ℝ) = 0 := by rw [hA j, hγ0, mul_zero]
      rw [hγ0, mul_zero, hA0, zero_mul]
  obtain ⟨z0, hz0⟩ := hint 0
  have hz0' : γ.coeff 0 = (z0 : ℝ) := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa using hz0
  have hIntD : Work.BMF.IntegralOn (D : ℝ) γ := by
    intro n
    refine ⟨∑ i ∈ Finset.range (γ.natDegree + 1),
      (if i = 0 then z0 * n ^ i
        else A i * ((D / denom γ i : ℕ) : ℤ) * (D : ℤ) ^ (i - 1) * n ^ i), ?_⟩
    rw [Polynomial.eval_eq_sum_range, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos rfl, pow_zero, mul_one, pow_zero, mul_one]
      exact hz0'
    · have h1i : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      rw [if_neg hi0]
      have hcast : (((A i * ((D / denom γ i : ℕ) : ℤ) * (D : ℤ) ^ (i - 1) : ℤ)) : ℝ)
          = (A i : ℝ) * ((D / denom γ i : ℕ) : ℝ) * (D : ℝ) ^ (i - 1) := by
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [Int.cast_mul, hcast, mul_pow]
      have hpoweq : (D : ℝ) ^ i = (D : ℝ) * (D : ℝ) ^ (i - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel h1i]
      rw [hpoweq, ← hDγ i h1i, Int.cast_pow]
      ring
  exact hmin D hDpos hIntD

/-- If `a = β c` with `β` the least positive integer with `β c ∈ ℤ`, and `z = k! · Z · c` with
`z : ℤ`, then `(β / gcd β k!) ∣ Z`. -/
theorem q0v2_denom_dvd {β : ℕ} {c : ℝ} {a Z z : ℤ} {k : ℕ}
    (hβ : 1 ≤ β)
    (ha : (a : ℝ) = (β : ℝ) * c)
    (hmin : ∀ β' : ℕ, 1 ≤ β' → (∃ a' : ℤ, (a' : ℝ) = (β' : ℝ) * c) → β ≤ β')
    (hz : (z : ℝ) = (k.factorial : ℝ) * (Z : ℝ) * c) :
    ((β / Nat.gcd β k.factorial : ℕ) : ℤ) ∣ Z := by
  have hgcd : Nat.gcd β a.natAbs = 1 := by
    by_contra hne
    set g : ℕ := Nat.gcd β a.natAbs with hgdef
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hβ
    have hdvdβ : g ∣ β := Nat.gcd_dvd_left _ _
    have hdvda : (g : ℤ) ∣ a := by
      have h1 : g ∣ a.natAbs := Nat.gcd_dvd_right _ _
      rw [← Int.natAbs_natCast g] at h1
      exact Int.natAbs_dvd_natAbs.mp h1
    obtain ⟨d, hd⟩ := hdvdβ
    obtain ⟨a', ha'⟩ := hdvda
    have hdpos : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exfalso
        rw [h, mul_zero] at hd
        omega
      · exact h
    have hda' : (d : ℝ) * c = (a' : ℝ) := by
      have hg : (g : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hgpos)
      have key : (g : ℝ) * ((d : ℝ) * c) = (g : ℝ) * (a' : ℝ) := by
        calc (g : ℝ) * ((d : ℝ) * c) = ((g : ℝ) * (d : ℝ)) * c := by ring
          _ = ((g * d : ℕ) : ℝ) * c := by rw [Nat.cast_mul]
          _ = (β : ℝ) * c := by rw [hd]
          _ = (a : ℝ) := ha.symm
          _ = (g : ℝ) * (a' : ℝ) := by rw [ha']; push_cast; ring
      exact mul_left_cancel₀ hg key
    have hle := hmin d hdpos ⟨a', hda'.symm⟩
    have hlt : d < β := by
      have hg2 : 2 ≤ g := by omega
      calc d = 1 * d := by ring
        _ < g * d := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        _ = β := hd.symm
    omega
  have hcopab : IsCoprime (β : ℤ) a := q0v2_isCoprime_aux hgcd
  have hint_eq : (β : ℤ) * z = (k.factorial : ℤ) * Z * a :=
    Int.cast_injective (α := ℝ) (by push_cast; rw [hz, ha]; ring)
  set g : ℕ := Nat.gcd β k.factorial with hgdef2
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hβ
  have hβeq : β = g * (β / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left β k.factorial)).symm
  have hkeq : k.factorial = g * (k.factorial / g) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right β k.factorial)).symm
  have hβZ : (g : ℤ) * (((β / g : ℕ)) : ℤ) = (β : ℤ) := by
    rw [← Nat.cast_mul, ← hβeq]
  have hkZ : (g : ℤ) * (((k.factorial / g : ℕ)) : ℤ) = (k.factorial : ℤ) := by
    rw [← Nat.cast_mul, ← hkeq]
  have hcop2 : Nat.Coprime (β / g) (k.factorial / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have hcancel : ((β / g : ℕ) : ℤ) * z = ((k.factorial / g : ℕ) : ℤ) * Z * a := by
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hgpos)
    have key : (g : ℤ) * (((β / g : ℕ) : ℤ) * z)
        = (g : ℤ) * (((k.factorial / g : ℕ) : ℤ) * Z * a) := by
      calc (g : ℤ) * (((β / g : ℕ) : ℤ) * z)
          = ((g : ℤ) * ((β / g : ℕ) : ℤ)) * z := by ring
        _ = (β : ℤ) * z := by rw [hβZ]
        _ = (k.factorial : ℤ) * Z * a := hint_eq
        _ = ((g : ℤ) * ((k.factorial / g : ℕ) : ℤ)) * Z * a := by rw [← hkZ]
        _ = (g : ℤ) * (((k.factorial / g : ℕ) : ℤ) * Z * a) := by ring
    exact mul_left_cancel₀ hg0 key
  have hdiv1 : ((β / g : ℕ) : ℤ) ∣ ((k.factorial / g : ℕ) : ℤ) * Z * a := ⟨z, hcancel.symm⟩
  have hcopda : IsCoprime (((β / g : ℕ)) : ℤ) a := by
    have hdvd : β / g ∣ β := ⟨g, by rw [mul_comm, ← hβeq]⟩
    exact q0v2_isCoprime_aux (Nat.Coprime.coprime_dvd_left hdvd hgcd)
  have hcopk : IsCoprime (((β / g : ℕ)) : ℤ) (((k.factorial / g : ℕ)) : ℤ) :=
    Nat.Coprime.isCoprime hcop2
  have hdiv2 : ((β / g : ℕ) : ℤ) ∣ ((k.factorial / g : ℕ) : ℤ) * Z :=
    hcopda.dvd_of_dvd_mul_left (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv1)
  exact hcopk.dvd_of_dvd_mul_right
    (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv2)

/-- `q ≤ M^k` implies `q^(1/k) / k! ≤ M`. -/
theorem q0v2_root_le {q M k : ℕ} (hk : 1 ≤ k) (h : q ≤ M ^ k) :
    (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k.factorial : ℝ) ≤ (M : ℝ) := by
  have hkre : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ne_of_gt this
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hqle : (q : ℝ) ≤ ((M : ℝ)) ^ k := by
    have h' : (q : ℝ) ≤ ((M ^ k : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hroot : (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) ≤ (M : ℝ) := by
    have h1 : ((M : ℝ) ^ k) ^ ((1 : ℝ) / (k : ℝ)) = (M : ℝ) := by
      rw [← Real.rpow_natCast (M : ℝ) k, ← Real.rpow_mul hM0,
        show (k : ℝ) * ((1 : ℝ) / (k : ℝ)) = 1 by rw [mul_one_div, div_self hkre]]
      rw [Real.rpow_one]
    calc (q : ℝ) ^ ((1 : ℝ) / (k : ℝ))
        ≤ ((M : ℝ) ^ k) ^ ((1 : ℝ) / (k : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hqle (by positivity)
      _ = (M : ℝ) := h1
  calc (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k.factorial : ℝ)
      ≤ (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) :=
        div_le_self (by positivity)
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)))
    _ ≤ (M : ℝ) := hroot

theorem q0_arith_v2 (k : ℕ) (hk : 1 ≤ k) :
    ∀ (q : ℕ) (γ : Polynomial ℝ), 0 < q → γ.natDegree ≤ k →
      Work.BMF.IntegralOn (q : ℝ) γ →
      (∀ r : ℕ, 1 ≤ r → Work.BMF.IntegralOn (r : ℝ) γ → q ≤ r) →
      ∀ A B : ℕ, A ≠ B →
        Work.BMF.IntegralOn 1 (Work.BMF.dil (A : ℝ) γ - Work.BMF.dil (B : ℝ) γ) →
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ ∃ β : ℕ,
        (1 ≤ β ∧ (∃ a : ℤ, (a : ℝ) = (β : ℝ) * γ.coeff m) ∧
          (∀ β' : ℕ, 1 ≤ β' → (∃ a : ℤ, (a : ℝ) = (β' : ℝ) * γ.coeff m) → β ≤ β')) ∧
        (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k.factorial : ℝ) ≤ (β : ℝ) ∧
        ((β / Nat.gcd β k.factorial : ℕ) : ℤ) ∣ ((A : ℤ) ^ m - (B : ℤ) ^ m)
:= by
  intro q γ hq hdeg hint hmin A B hAB hdil
  classical
  have hden : ∀ m : ℕ, m ≤ k → ∃ β : ℕ, IsDenom γ m β :=
    fun m hm => q0v2_denom_exists hq hdeg hm hint
  have hprod : q ≤ ∏ m ∈ Finset.Icc 1 k, denom γ m :=
    q0v2_le_prod_denom k q γ hdeg hden hint hmin
  obtain ⟨m0, hm0mem, hm0eq⟩ :=
    Finset.exists_mem_eq_sup (Finset.Icc 1 k) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
      (fun m => denom γ m)
  have hm01 : 1 ≤ m0 := (Finset.mem_Icc.mp hm0mem).1
  have hm0k : m0 ≤ k := (Finset.mem_Icc.mp hm0mem).2
  have hcard : (Finset.Icc 1 k).card = k := by
    rw [Nat.card_Icc]; omega
  have hleM : (∏ m ∈ Finset.Icc 1 k, denom γ m) ≤ (denom γ m0) ^ k := by
    have h := Finset.prod_le_pow_card (Finset.Icc 1 k) (fun m => denom γ m)
      ((Finset.Icc 1 k).sup (fun m => denom γ m)) (fun m hm => Finset.le_sup hm)
    rw [hcard, hm0eq] at h
    exact h
  have hqM : q ≤ (denom γ m0) ^ k := le_trans hprod hleM
  refine ⟨m0, hm01, hm0k, denom γ m0, ?_, ?_, ?_⟩
  · refine ⟨(denom_spec (hden m0 hm0k)).1, (denom_spec (hden m0 hm0k)).2, ?_⟩
    intro β' hβ' ha'
    exact denom_le (hden m0 hm0k) ⟨hβ', ha'⟩
  · exact q0v2_root_le hk hqM
  · have hδdeg : (Work.BMF.dil (A : ℝ) γ - Work.BMF.dil (B : ℝ) γ).natDegree ≤ k := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [max_le_iff]
      exact ⟨le_trans (Work.BMF.natDegree_dil_le _ _) hdeg,
        le_trans (Work.BMF.natDegree_dil_le _ _) hdeg⟩
    obtain ⟨z, hz⟩ := q0v2_fact_coeff_int hdil hδdeg m0
    have hδcoeff : (Work.BMF.dil (A : ℝ) γ - Work.BMF.dil (B : ℝ) γ).coeff m0
        = γ.coeff m0 * ((A : ℝ) ^ m0 - (B : ℝ) ^ m0) := by
      rw [Polynomial.coeff_sub, Work.BMF.coeff_dil, Work.BMF.coeff_dil]
      ring
    have hz' : (z : ℝ) = (k.factorial : ℝ) * (((A : ℤ) ^ m0 - (B : ℤ) ^ m0 : ℤ) : ℝ)
        * γ.coeff m0 := by
      rw [← hz, hδcoeff]
      push_cast
      ring
    obtain ⟨b, hb⟩ := (denom_spec (hden m0 hm0k)).2
    exact q0v2_denom_dvd (hβ := (denom_spec (hden m0 hm0k)).1) (ha := hb)
      (hmin := fun β' hβ' ha' => denom_le (hden m0 hm0k) ⟨hβ', ha'⟩) (hz := hz')

end Work.N8
