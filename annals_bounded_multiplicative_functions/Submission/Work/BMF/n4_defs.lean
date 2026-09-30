import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.tuple_setup
import Submission.Work.BMF.mpow_char_orthogonality
import Submission.Work.BMF.primesIn_card_le_pi0
import Submission.Work.BMF.n4_majorant

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# N4 definitions and elementary lemmas for `prime_tuple_count`

The prime-character sum `psum`, the pair correlation `n4corr`, the counting set `n4set`,
the character expansion `n4corr_eq`, and the elementary bounds used by
`Submission.Work.BMF.prime_tuple_count`.  No `sorry`.
-/

namespace Work.BMF

open Polynomial Finset Real
open scoped BigOperators ComplexConjugate


open Polynomial Finset Real
open scoped BigOperators ComplexConjugate

/-! ## The prime-character sum and the pair correlation -/

/-- The `[P,2P]` prime-character sum over the primes not dividing `q`. -/
noncomputable def psum (P : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)

/-- The pair correlation of the products of two `ℓ`-tuples of admissible primes,
restricted to the pairs whose `m`-th powers are congruent mod `q`. -/
noncomputable def n4corr (ℓ m : ℕ) (P : ℝ) (q : ℕ) (t : ℝ) : ℂ :=
  ∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
    (if (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q] then
      ((((tprod v.2 : ℕ) : ℂ) ^ (Complex.I * t)) * conj ((((tprod v.1 : ℕ) : ℂ) ^ (Complex.I * t))))
     else 0)

/-- `((∏ n_i : ℕ) : ℂ)^z = ∏ ((n_i : ℕ) : ℂ)^z`. -/
lemma ofReal_prod_cpow {ι : Type*} (s : Finset ι) (n : ι → ℕ) (z : ℂ) :
    (((∏ i ∈ s, n i : ℕ)) : ℂ) ^ z = ∏ i ∈ s, (((n i : ℕ)) : ℂ) ^ z := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

/-- The product of a tuple of admissible primes, as a unit of `ZMod q`. -/
noncomputable def tupUnit {P : ℝ} {q ℓ : ℕ} (hP : 0 ≤ P) (v : Fin ℓ → ℕ)
    (hv : v ∈ tup P q ℓ) : (ZMod q)ˣ :=
  ∏ i : Fin ℓ, ZMod.unitOfCoprime (v i)
    ((Nat.Prime.coprime_iff_not_dvd (tup_prime hP hv i)).mpr
      (admP_notdvd hP ((mem_tup.mp hv) i)))

lemma tupUnit_val {P : ℝ} {q ℓ : ℕ} (hP : 0 ≤ P) (v : Fin ℓ → ℕ) (hv : v ∈ tup P q ℓ) :
    ((tupUnit hP v hv : (ZMod q)ˣ) : ZMod q) = ((tprod v : ℕ) : ZMod q) := by
  rw [tupUnit, Units.coe_prod, tprod, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact ZMod.coe_unitOfCoprime _ _

/-- The product of a tuple of admissible primes is coprime to `q`. -/
lemma coprime_tprod {P : ℝ} {q ℓ : ℕ} (hP : 0 ≤ P) {v : Fin ℓ → ℕ} (hv : v ∈ tup P q ℓ) :
    Nat.Coprime (tprod v) q := by
  have hunit : IsUnit (((tprod v : ℕ)) : ZMod q) := by
    rw [← tupUnit_val hP v hv]
    exact (tupUnit hP v hv).isUnit
  exact (ZMod.isUnit_iff_coprime (tprod v) q).mp hunit

/-- Orthogonality of the `m`-th powers of the characters mod `q`, at natural numbers
coprime to `q`. -/
lemma char_orthogonality_natCast {q m : ℕ} [NeZero q] {n₁ n₂ : ℕ}
    (h₁ : Nat.Coprime n₁ q) (h₂ : Nat.Coprime n₂ q) :
    (∑ ψ : DirichletCharacter ℂ q, (ψ ^ m) (n₁ : ZMod q) * conj ((ψ ^ m) (n₂ : ZMod q)))
      = (q.totient : ℂ) * (if n₁ ^ m ≡ n₂ ^ m [MOD q] then 1 else 0) := by
  have h₁' : ((ZMod.unitOfCoprime n₁ h₁ : (ZMod q)ˣ) : ZMod q) = (n₁ : ZMod q) :=
    ZMod.coe_unitOfCoprime n₁ h₁
  have h₂' : ((ZMod.unitOfCoprime n₂ h₂ : (ZMod q)ˣ) : ZMod q) = (n₂ : ZMod q) :=
    ZMod.coe_unitOfCoprime n₂ h₂
  have hmain := mpow_char_orthogonality q m (ZMod.unitOfCoprime n₁ h₁) (ZMod.unitOfCoprime n₂ h₂)
  rw [h₁', h₂'] at hmain
  simp only [Complex.star_def] at hmain
  rw [hmain]
  congr 1
  have hiff : ((ZMod.unitOfCoprime n₁ h₁) ^ m = (ZMod.unitOfCoprime n₂ h₂) ^ m)
      ↔ n₁ ^ m ≡ n₂ ^ m [MOD q] := by
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h₁', h₂',
      ← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
  by_cases hc : n₁ ^ m ≡ n₂ ^ m [MOD q]
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

/-- The indicator of the `m`-th power congruence, expanded in characters. -/
lemma cong_indicator {q m : ℕ} [NeZero q] {A B : ℕ}
    (hA : Nat.Coprime A q) (hB : Nat.Coprime B q) :
    (if A ^ m ≡ B ^ m [MOD q] then (1 : ℂ) else 0)
      = ((q.totient : ℂ))⁻¹ * ∑ ψ : DirichletCharacter ℂ q,
          (ψ ^ m) (B : ZMod q) * conj ((ψ ^ m) (A : ZMod q)) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    have h1 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast h1.ne'
  rw [char_orthogonality_natCast (m := m) hB hA, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
  by_cases hc : A ^ m ≡ B ^ m [MOD q]
  · rw [if_pos hc, if_pos hc.symm]
  · rw [if_neg hc, if_neg (fun h => hc h.symm)]

/-- The sum over the tuples of a multiplicative factor is the `ℓ`-th power of the
single-prime sum. -/
lemma sum_tup_char_cpow (P : ℝ) (q ℓ : ℕ) (hP : 0 ≤ P) (χ : DirichletCharacter ℂ q)
    (t : ℝ) :
    (∑ v ∈ tup P q ℓ,
        χ ((tprod v : ℕ) : ZMod q) * ((((tprod v : ℕ)) : ℂ) ^ (Complex.I * t)))
      = (psum P q χ t) ^ ℓ := by
  have key : ∀ v ∈ tup P q ℓ,
      χ ((tprod v : ℕ) : ZMod q) * ((((tprod v : ℕ)) : ℂ) ^ (Complex.I * t))
        = ∏ i : Fin ℓ, χ (((v i : ℕ)) : ZMod q) * ((((v i : ℕ)) : ℂ) ^ (Complex.I * t)) := by
    intro v hv
    rw [tprod, Nat.cast_prod, map_prod, ofReal_prod_cpow, Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl key, tup]
  rw [← Finset.sum_pow' (admP P q) (fun p => χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t))]
  rfl

/-- The conjugate of the tuple sum. -/
lemma sum_tup_conj (P : ℝ) (q ℓ : ℕ) (hP : 0 ≤ P) (χ : DirichletCharacter ℂ q)
    (t : ℝ) :
    (∑ v ∈ tup P q ℓ,
        conj (χ ((tprod v : ℕ) : ZMod q)) * conj ((((tprod v : ℕ)) : ℂ) ^ (Complex.I * t)))
      = conj ((psum P q χ t) ^ ℓ) := by
  have h := sum_tup_char_cpow P q ℓ hP χ t
  have h2 : (∑ v ∈ tup P q ℓ,
        conj (χ ((tprod v : ℕ) : ZMod q)) * conj ((((tprod v : ℕ)) : ℂ) ^ (Complex.I * t)))
      = conj (∑ v ∈ tup P q ℓ,
        χ ((tprod v : ℕ) : ZMod q) * ((((tprod v : ℕ)) : ℂ) ^ (Complex.I * t))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [map_mul]
  rw [h2, h]

/-- The inner sum for a fixed character. -/
lemma inner_sum_eq {ℓ m : ℕ} {P : ℝ} {q : ℕ} (hP : 0 ≤ P) (ψ : DirichletCharacter ℂ q)
    (t : ℝ) :
    (∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
        ((ψ ^ m) ((tprod v.2 : ℕ) : ZMod q) * conj ((ψ ^ m) ((tprod v.1 : ℕ) : ZMod q)))
          * (((((tprod v.2 : ℕ)) : ℂ) ^ (Complex.I * t))
              * conj (((((tprod v.1 : ℕ)) : ℂ) ^ (Complex.I * t)))))
      = (psum P q (ψ ^ m) t) ^ ℓ * conj ((psum P q (ψ ^ m) t) ^ ℓ) := by
  rw [Finset.sum_product]
  rw [show (∑ x ∈ tup P q ℓ, ∑ y ∈ tup P q ℓ,
        ((ψ ^ m) ((tprod (x, y).2 : ℕ) : ZMod q)
            * conj ((ψ ^ m) ((tprod (x, y).1 : ℕ) : ZMod q)))
          * (((((tprod (x, y).2 : ℕ)) : ℂ) ^ (Complex.I * t))
              * conj (((((tprod (x, y).1 : ℕ)) : ℂ) ^ (Complex.I * t)))))
      = ∑ v₁ ∈ tup P q ℓ, ∑ v₂ ∈ tup P q ℓ,
        (conj ((ψ ^ m) ((tprod v₁ : ℕ) : ZMod q))
            * conj (((((tprod v₁ : ℕ)) : ℂ) ^ (Complex.I * t))))
          * ((ψ ^ m) ((tprod v₂ : ℕ) : ZMod q)
              * (((((tprod v₂ : ℕ)) : ℂ) ^ (Complex.I * t)))) from by
    refine Finset.sum_congr rfl (fun v₁ _ => Finset.sum_congr rfl (fun v₂ _ => ?_))
    ring]
  rw [← Finset.sum_mul_sum]
  rw [sum_tup_conj P q ℓ hP (ψ ^ m) t, sum_tup_char_cpow P q ℓ hP (ψ ^ m) t]
  ring

/-- The pair correlation is the average over the characters of `|Σ_p χ(p) p^{it}|^{2ℓ}`. -/
lemma n4corr_eq {ℓ m : ℕ} {P : ℝ} {q : ℕ} (hP : 0 ≤ P) (hq : 1 ≤ q) (t : ℝ) :
    n4corr ℓ m P q t
      = ((q.totient : ℂ))⁻¹ * ∑ ψ : DirichletCharacter ℂ q,
          (psum P q (ψ ^ m) t) ^ ℓ * conj ((psum P q (ψ ^ m) t) ^ ℓ) := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  have hstep : ∀ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
      (if (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q] then
        ((((tprod v.2 : ℕ) : ℂ) ^ (Complex.I * t)) * conj ((((tprod v.1 : ℕ) : ℂ) ^ (Complex.I * t))))
       else 0)
      = ((q.totient : ℂ))⁻¹ * ((∑ ψ : DirichletCharacter ℂ q,
            (ψ ^ m) ((tprod v.2 : ℕ) : ZMod q) * conj ((ψ ^ m) ((tprod v.1 : ℕ) : ZMod q)))
          * ((((tprod v.2 : ℕ) : ℂ) ^ (Complex.I * t))
              * conj ((((tprod v.1 : ℕ) : ℂ) ^ (Complex.I * t))))) := by
    intro v hv
    rw [Finset.mem_product] at hv
    have h1 : Nat.Coprime (tprod v.2) q := coprime_tprod hP hv.2
    have h2 : Nat.Coprime (tprod v.1) q := coprime_tprod hP hv.1
    have hc := cong_indicator (m := m) h2 h1
    rw [show (if (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q] then
          ((((tprod v.2 : ℕ) : ℂ) ^ (Complex.I * t))
            * conj ((((tprod v.1 : ℕ) : ℂ) ^ (Complex.I * t))))
        else 0)
      = (if (tprod v.1) ^ m ≡ (tprod v.2) ^ m [MOD q] then (1 : ℂ) else 0)
          * ((((tprod v.2 : ℕ) : ℂ) ^ (Complex.I * t))
              * conj ((((tprod v.1 : ℕ) : ℂ) ^ (Complex.I * t)))) from by
        by_cases h : (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q]
        · rw [if_pos h, if_pos h.symm, one_mul]
        · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]]
    rw [hc]
    ring
  rw [n4corr, Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  congr 1
  rw [show (∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
        (∑ ψ : DirichletCharacter ℂ q,
            (ψ ^ m) ((tprod v.2 : ℕ) : ZMod q) * conj ((ψ ^ m) ((tprod v.1 : ℕ) : ZMod q)))
          * ((((tprod v.2 : ℕ) : ℂ) ^ (Complex.I * t))
              * conj ((((tprod v.1 : ℕ) : ℂ) ^ (Complex.I * t)))))
      = ∑ ψ : DirichletCharacter ℂ q, ∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
        ((ψ ^ m) ((tprod v.2 : ℕ) : ZMod q) * conj ((ψ ^ m) ((tprod v.1 : ℕ) : ZMod q)))
          * (((((tprod v.2 : ℕ)) : ℂ) ^ (Complex.I * t))
              * conj (((((tprod v.1 : ℕ)) : ℂ) ^ (Complex.I * t)))) from by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]]
  rw [Finset.sum_congr rfl (fun ψ _ => inner_sum_eq hP ψ t)]

/-! ## The majorant step: from the counting problem to an integral -/

/-- The filtered set of pairs of tuples counted by N4. -/
noncomputable def n4set (ℓ m : ℕ) (P N C₀ : ℝ) (q : ℕ) :
    Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
  ((tup P q ℓ) ×ˢ (tup P q ℓ)).filter (fun v ↦
    |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P^ℓ / N ∧
      (tprod v.2)^m ≡ (tprod v.1)^m [MOD q])

/-- `|log x - log y| ≤ |x - y| / min x y`. -/
lemma abs_log_sub_log_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log x - Real.log y| ≤ |x - y| / min x y := by
  have hmin : 0 < min x y := lt_min hx hy
  rw [abs_le']
  constructor
  · rw [← Real.log_div hx.ne' hy.ne']
    calc Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = (x - y) / y := by rw [sub_div, div_self hy.ne']
      _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy.le
      _ ≤ |x - y| / min x y := div_le_div_of_nonneg_left (abs_nonneg _) hmin (min_le_right x y)
  · rw [neg_sub, ← Real.log_div hy.ne' hx.ne']
    calc Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
      _ = (y - x) / x := by rw [sub_div, div_self hx.ne']
      _ ≤ |y - x| / x := div_le_div_of_nonneg_right (le_abs_self _) hx.le
      _ = |x - y| / x := by rw [abs_sub_comm]
      _ ≤ |x - y| / min x y := div_le_div_of_nonneg_left (abs_nonneg _) hmin (min_le_left x y)

/-- If `A, B ≥ P^ℓ` and `|A - B| ≤ C₀ P^ℓ / N` then `|N log (B/A)| ≤ C₀`. -/
lemma n4_log_window {ℓ : ℕ} {P N C₀ A B : ℝ} (hP : 1 ≤ P) (hN : 0 < N) (hC₀ : 0 ≤ C₀)
    (hA : P^ℓ ≤ A) (hB : P^ℓ ≤ B) (h : |B - A| ≤ C₀ * P^ℓ / N) :
    |N * (Real.log B - Real.log A)| ≤ C₀ := by
  have hP0 : (0:ℝ) < P := by linarith
  have hPℓ : 0 < P^ℓ := pow_pos hP0 ℓ
  have hA0 : 0 < A := lt_of_lt_of_le hPℓ hA
  have hB0 : 0 < B := lt_of_lt_of_le hPℓ hB
  have hmin : 0 < min B A := lt_min hB0 hA0
  have hlog : |Real.log B - Real.log A| ≤ C₀ / N := by
    calc |Real.log B - Real.log A| ≤ |B - A| / min B A := abs_log_sub_log_le hB0 hA0
      _ ≤ (C₀ * P^ℓ / N) / min B A := div_le_div_of_nonneg_right h hmin.le
      _ ≤ (C₀ * P^ℓ / N) / P^ℓ :=
          div_le_div_of_nonneg_left (by positivity) hPℓ (le_min hB hA)
      _ = C₀ / N := by field_simp
  rw [abs_mul, abs_of_pos hN]
  calc N * |Real.log B - Real.log A| ≤ N * (C₀ / N) := mul_le_mul_of_nonneg_left hlog hN.le
    _ = C₀ := by field_simp

/-- The number of pairs counted by N4 is at most the sum of `n4w C₀ (N log (B/A))` over
the congruent pairs. -/
lemma n4_count_le_sum {ℓ m : ℕ} {P N C₀ : ℝ} {q : ℕ} (hP : 1 ≤ P)
    (hN : 3 ≤ N) (hC₀ : 0 < C₀) :
    ((n4set ℓ m P N C₀ q).card : ℝ) ≤
      ∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
        (if (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q] then
          n4w C₀ (N * (Real.log (((tprod v.2 : ℕ)) : ℝ) - Real.log (((tprod v.1 : ℕ)) : ℝ)))
         else 0) := by
  obtain ⟨hw1, hw2, _⟩ := n4_majorant C₀ hC₀
  have hN0 : (0:ℝ) < N := by linarith
  have hP0 : (0:ℝ) < P := by linarith
  have hcard : ((n4set ℓ m P N C₀ q).card : ℝ)
      = ∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
          (if |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P^ℓ / N ∧
              (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q] then (1:ℝ) else 0) := by
    simp only [n4set, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hcard]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hcond : |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P^ℓ / N ∧
      (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q]
  · rw [if_pos hcond, if_pos hcond.2]
    refine hw2 _ ?_
    rw [Finset.mem_product] at hv
    have h := n4_log_window (ℓ := ℓ) hP hN0 hC₀.le
      (tprod_ge hP0.le hv.1) (tprod_ge hP0.le hv.2) hcond.1
    calc |N * (Real.log (((tprod v.2 : ℕ)) : ℝ) - Real.log (((tprod v.1 : ℕ)) : ℝ))| ≤ C₀ := h
      _ ≤ 2 * C₀ := by linarith
  · rw [if_neg hcond]
    by_cases hc : (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q]
    · rw [if_pos hc]
      exact hw1 _
    · rw [if_neg hc]



end Work.BMF
