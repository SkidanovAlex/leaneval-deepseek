import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_squarefree_r2
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime

open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

/-- For coprime `u`, `v`, the `gcd` with a product splits. -/
lemma gcd_mul_gcd_of_coprime {u v n : ℕ} (h : u.Coprime v) :
    Nat.gcd (u * v) n = Nat.gcd u n * Nat.gcd v n := by
  refine Nat.dvd_antisymm ?_ ?_
  · rw [Nat.gcd_comm (u * v) n, Nat.gcd_comm u n, Nat.gcd_comm v n]
    exact gcd_mul_dvd_mul_gcd n u v
  · have hcop : (Nat.gcd u n).Coprime (Nat.gcd v n) :=
      Nat.Coprime.of_dvd (Nat.gcd_dvd_left u n) (Nat.gcd_dvd_left v n) h
    apply Nat.dvd_gcd
    · exact Nat.mul_dvd_mul (Nat.gcd_dvd_left u n) (Nat.gcd_dvd_left v n)
    · exact hcop.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right u n) (Nat.gcd_dvd_right v n)

lemma card_primeFactors_mul_of_coprime {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) (h : u.Coprime v) :
    (u * v).primeFactors.card = u.primeFactors.card + v.primeFactors.card := by
  rw [Nat.primeFactors_mul hu hv, Finset.card_union_of_disjoint]
  exact (Nat.disjoint_primeFactors hu hv).mpr h

lemma exists_coprime_factorization {n : ℕ} (hn2 : 2 ≤ n) (hnp : ¬ IsPrimePow n) :
    ∃ u v : ℕ, 1 < u ∧ 1 < v ∧ u.Coprime v ∧ u * v = n := by
  have hn1 : n ≠ 1 := by omega
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have he : 0 < n.factorization n.minFac := hp.factorization_pos_of_dvd hn0 hpdvd
  refine ⟨n.minFac ^ n.factorization n.minFac, n / n.minFac ^ n.factorization n.minFac, ?_, ?_, ?_, ?_⟩
  · exact Nat.one_lt_pow (by omega) hp.one_lt
  · rcases lt_or_eq_of_le (show 1 ≤ n / n.minFac ^ n.factorization n.minFac from Nat.ordCompl_pos n.minFac hn0) with h | h
    · exact h
    · exfalso
      apply hnp
      rw [isPrimePow_iff_minFac_pow_factorization_eq hn1]
      have := Nat.ordProj_mul_ordCompl_eq_self n n.minFac
      rw [← h, mul_one] at this
      exact this
  · exact (Nat.coprime_ordCompl hp hn0).pow_left (n.factorization n.minFac)
  · exact Nat.ordProj_mul_ordCompl_eq_self n n.minFac

/-- CRT splitting of the quadratic correlation using the `factorLeft`/`factorRight` components. -/
lemma corr_crt_split {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)
    (χ : DirichletCharacter ℂ (u*v)) (a b c d : ℕ) :
    (∑ x : ZMod (u*v),
        χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d))))
      = (∑ y : ZMod u,
          factorLeft huv χ ((y + a) * (y + b)) * (starRingEnd ℂ) (factorLeft huv χ ((y + c) * (y + d))))
        * (∑ z : ZMod v,
          factorRight huv χ ((z + a) * (z + b)) * (starRingEnd ℂ) (factorRight huv χ ((z + c) * (z + d)))) := by
  have hcastu : ∀ x : ZMod (u*v),
      (((x + (a:ZMod (u*v))) * (x + (b:ZMod (u*v)))).cast : ZMod u)
        = ((x.cast : ZMod u) + (a:ZMod u)) * ((x.cast : ZMod u) + (b:ZMod u)) := by
    intro x
    simp only [ZMod.cast_mul (Nat.dvd_mul_right u v), ZMod.cast_add (Nat.dvd_mul_right u v),
      ZMod.cast_natCast (Nat.dvd_mul_right u v)]
  have hcastu' : ∀ x : ZMod (u*v),
      (((x + (c:ZMod (u*v))) * (x + (d:ZMod (u*v)))).cast : ZMod u)
        = ((x.cast : ZMod u) + (c:ZMod u)) * ((x.cast : ZMod u) + (d:ZMod u)) := by
    intro x
    simp only [ZMod.cast_mul (Nat.dvd_mul_right u v), ZMod.cast_add (Nat.dvd_mul_right u v),
      ZMod.cast_natCast (Nat.dvd_mul_right u v)]
  have hcastv : ∀ x : ZMod (u*v),
      (((x + (a:ZMod (u*v))) * (x + (b:ZMod (u*v)))).cast : ZMod v)
        = ((x.cast : ZMod v) + (a:ZMod v)) * ((x.cast : ZMod v) + (b:ZMod v)) := by
    intro x
    simp only [ZMod.cast_mul (Nat.dvd_mul_left v u), ZMod.cast_add (Nat.dvd_mul_left v u),
      ZMod.cast_natCast (Nat.dvd_mul_left v u)]
  have hcastv' : ∀ x : ZMod (u*v),
      (((x + (c:ZMod (u*v))) * (x + (d:ZMod (u*v)))).cast : ZMod v)
        = ((x.cast : ZMod v) + (c:ZMod v)) * ((x.cast : ZMod v) + (d:ZMod v)) := by
    intro x
    simp only [ZMod.cast_mul (Nat.dvd_mul_left v u), ZMod.cast_add (Nat.dvd_mul_left v u),
      ZMod.cast_natCast (Nat.dvd_mul_left v u)]
  have hkey : ∀ x : ZMod (u*v),
      χ ((x + (a:ZMod (u*v))) * (x + (b:ZMod (u*v)))) *
          (starRingEnd ℂ) (χ ((x + (c:ZMod (u*v))) * (x + (d:ZMod (u*v)))))
      = (factorLeft huv χ (((x.cast : ZMod u) + (a:ZMod u)) * ((x.cast : ZMod u) + (b:ZMod u))) *
            (starRingEnd ℂ) (factorLeft huv χ (((x.cast : ZMod u) + (c:ZMod u)) * ((x.cast : ZMod u) + (d:ZMod u)))))
        * (factorRight huv χ (((x.cast : ZMod v) + (a:ZMod v)) * ((x.cast : ZMod v) + (b:ZMod v))) *
            (starRingEnd ℂ) (factorRight huv χ (((x.cast : ZMod v) + (c:ZMod v)) * ((x.cast : ZMod v) + (d:ZMod v))))) := by
    intro x
    rw [chi_eq_factors huv χ ((x + (a:ZMod (u*v))) * (x + (b:ZMod (u*v)))),
        chi_eq_factors huv χ ((x + (c:ZMod (u*v))) * (x + (d:ZMod (u*v)))), map_mul,
        hcastu x, hcastu' x, hcastv x, hcastv' x]
    ring
  simp_rw [hkey]
  have hstep := Fintype.sum_equiv (crtE huv).toEquiv
    (fun x : ZMod (u*v) =>
      (factorLeft huv χ (((x.cast : ZMod u) + (a:ZMod u)) * ((x.cast : ZMod u) + (b:ZMod u))) *
            (starRingEnd ℂ) (factorLeft huv χ (((x.cast : ZMod u) + (c:ZMod u)) * ((x.cast : ZMod u) + (d:ZMod u)))))
        * (factorRight huv χ (((x.cast : ZMod v) + (a:ZMod v)) * ((x.cast : ZMod v) + (b:ZMod v))) *
            (starRingEnd ℂ) (factorRight huv χ (((x.cast : ZMod v) + (c:ZMod v)) * ((x.cast : ZMod v) + (d:ZMod v))))))
    (fun w : ZMod u × ZMod v =>
      (factorLeft huv χ ((w.1 + (a:ZMod u)) * (w.1 + (b:ZMod u))) *
            (starRingEnd ℂ) (factorLeft huv χ ((w.1 + (c:ZMod u)) * (w.1 + (d:ZMod u)))))
        * (factorRight huv χ ((w.2 + (a:ZMod v)) * (w.2 + (b:ZMod v))) *
            (starRingEnd ℂ) (factorRight huv χ ((w.2 + (c:ZMod v)) * (w.2 + (d:ZMod v))))))
    (fun x => by
      have h1 : ((crtE huv).toEquiv x).1 = x.cast := crtE_fst huv x
      have h2 : ((crtE huv).toEquiv x).2 = x.cast := crtE_snd huv x
      rw [h1, h2])
  rw [hstep, Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
    (f := fun y : ZMod u => factorLeft huv χ ((y + (a:ZMod u)) * (y + (b:ZMod u))) *
      (starRingEnd ℂ) (factorLeft huv χ ((y + (c:ZMod u)) * (y + (d:ZMod u)))))
    (g := fun z : ZMod v => factorRight huv χ ((z + (a:ZMod v)) * (z + (b:ZMod v))) *
      (starRingEnd ℂ) (factorRight huv χ ((z + (c:ZMod v)) * (z + (d:ZMod v)))))]

/-- `Real.sqrt (p^e) = p^(e/2)`. -/
lemma sqrt_natPow_eq_rpow (p e : ℕ) :
    Real.sqrt (((p ^ e : ℕ)) : ℝ) = (p : ℝ) ^ ((e : ℝ) / 2) := by
  rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (p:ℝ) e,
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (p:ℝ))]
  congr 1
  ring

/-- **Global (all moduli) correlation bound, conditional on the prime-power case.**

Assuming the sharp prime-power bound `hloc` (the prime-power form of Burgess's Lemma 7,
whose statement is `charCorrelation_primePow_sharp`), the same inequality -- with the weight
`∏_{j≠i} gcd(q, |v_i - v_j|)` and the loss `8^(ω q) = 8^(q.primeFactors.card)`, and the extra
factor `√q` -- holds for *every* modulus `q`, provided `v_i` is distinct from the other three
values `v_j`.

Proof outline: strong induction on `q`.  If `q = p^e` is a prime power this is `hloc`.
Otherwise write `q = u * v` with `u = p^e` (`p = q.minFac`, `e = q.factorization p`) and
`v = q / u`, so that `u, v > 1` are coprime and `u, v < q`; by
`charCorrelation_crt_factor` (with the `(∀ m : ℤ, χ m = χu m * χv m)` clause) the correlation
factors as a product of the correlations of the two CRT component characters, which
`primitive_factor_coprime` shows to be primitive; the two factors are handled by the induction
hypothesis and multiplied, using `Nat.gcd_mul_gcd_of_coprime`-style identities
(`gcd (u*v) x = gcd u x * gcd v x` for coprime `u`, `v`), `ω(q) = ω(u) + ω(v)` and
`√(uv) = √u * √v`. -/
theorem charCorrelation_global_sharp_aux
    (hloc : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 1 ≤ e →
      ∀ (χ : DirichletCharacter ℂ (p ^ e)), χ.IsPrimitive → χ ≠ 1 →
      ∀ (a b c d : ℕ) (i : Fin 4),
        (∀ j : Fin 4, j ≠ i → (![a, b, c, d] i) ≠ (![a, b, c, d] j)) →
        ‖∑ x : ZMod (p ^ e), χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d)))‖
          ≤ 8 * (p : ℝ) ^ ((e : ℝ) / 2) *
              ∏ j ∈ Finset.univ.erase i,
                (((Nat.gcd (p ^ e) (((![a, b, c, d] i : ℤ) - (![a, b, c, d] j : ℤ)).natAbs)) : ℕ) : ℝ))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    (a b c d : ℕ) (i : Fin 4)
    (hi : ∀ j : Fin 4, j ≠ i → (![a, b, c, d] i) ≠ (![a, b, c, d] j)) :
    ‖∑ x : ZMod q, χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d)))‖
      ≤ 8 ^ (q.primeFactors.card) * Real.sqrt (q : ℝ) *
          ∏ j ∈ Finset.univ.erase i,
            (((Nat.gcd q (((![a, b, c, d] i : ℤ) - (![a, b, c, d] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
  have key : ∀ (n : ℕ) [NeZero n], ∀ (χ : DirichletCharacter ℂ n), χ.IsPrimitive → χ ≠ 1 →
      ∀ (a b c d : ℕ) (i : Fin 4),
        (∀ j : Fin 4, j ≠ i → (![a, b, c, d] i) ≠ (![a, b, c, d] j)) →
        ‖∑ x : ZMod n, χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d)))‖
          ≤ 8 ^ (n.primeFactors.card) * Real.sqrt (n : ℝ) *
              ∏ j ∈ Finset.univ.erase i,
                (((Nat.gcd n (((![a, b, c, d] i : ℤ) - (![a, b, c, d] j : ℤ)).natAbs)) : ℕ) : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn χ hχ h1 a b c d i hi
      by_cases hpp : IsPrimePow n
      · obtain ⟨p, e, hp, he, hn_eq⟩ := (isPrimePow_nat_iff n).mp hpp
        subst n
        have : Fact p.Prime := ⟨hp⟩
        have hcard : (p ^ e).primeFactors.card = 1 :=
          isPrimePow_iff_card_primeFactors_eq_one.mp ((isPrimePow_nat_iff (p^e)).mpr ⟨p, e, hp, he, rfl⟩)
        refine (hloc p e he χ hχ h1 a b c d i hi).trans (le_of_eq ?_)
        rw [hcard, sqrt_natPow_eq_rpow]
        ring
      · by_cases hn1 : n = 1
        · subst n
          have hnorm : ‖∑ x : ZMod 1, χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d)))‖ ≤ 1 := by
            calc ‖∑ x : ZMod 1, χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d)))‖
                ≤ ∑ x : ZMod 1, ‖χ ((x + a) * (x + b)) * (starRingEnd ℂ) (χ ((x + c) * (x + d)))‖ :=
                  norm_sum_le _ _
              _ ≤ ∑ _x : ZMod 1, (1:ℝ) := by
                  apply Finset.sum_le_sum
                  intro x _
                  rw [norm_mul]
                  have h2 := DirichletCharacter.norm_le_one χ ((x + a) * (x + b))
                  have h3 := DirichletCharacter.norm_le_one χ ((x + c) * (x + d))
                  have h4 : ‖(starRingEnd ℂ) (χ ((x + c) * (x + d)))‖ = ‖χ ((x + c) * (x + d))‖ := norm_star _
                  rw [h4]
                  nlinarith [norm_nonneg (χ ((x + a) * (x + b))), norm_nonneg (χ ((x + c) * (x + d)))]
              _ = 1 := by
                  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
                  norm_num
          refine hnorm.trans (le_of_eq ?_)
          simp [Nat.primeFactors_one]
        · have hn2 : 2 ≤ n := by
            have hnz : n ≠ 0 := NeZero.ne n
            omega
          obtain ⟨u, v, hu1, hv1, huv, huv_eq⟩ := exists_coprime_factorization hn2 hpp
          subst n
          have huNZ : NeZero u := ⟨by omega⟩
          have hvNZ : NeZero v := ⟨by omega⟩
          have hu0 : u ≠ 0 := by omega
          have hv0 : v ≠ 0 := by omega
          have hu_lt : u < u * v := by nlinarith [hv1]
          have hv_lt : v < u * v := by nlinarith [hu1]
          have hFLprim : (factorLeft huv χ).IsPrimitive := factorLeft_isPrimitive huv χ hχ
          have hFRprim : (factorRight huv χ).IsPrimitive := factorRight_isPrimitive huv χ hχ
          have hFLne : factorLeft huv χ ≠ 1 := by
            intro h
            have hc : (factorLeft huv χ).conductor = 1 := by
              rw [h]; exact DirichletCharacter.conductor_one
            rw [DirichletCharacter.isPrimitive_def] at hFLprim
            omega
          have hFRne : factorRight huv χ ≠ 1 := by
            intro h
            have hc : (factorRight huv χ).conductor = 1 := by
              rw [h]; exact DirichletCharacter.conductor_one
            rw [DirichletCharacter.isPrimitive_def] at hFRprim
            omega
          have hIu := ih u hu_lt (factorLeft huv χ) hFLprim hFLne a b c d i hi
          have hIv := ih v hv_lt (factorRight huv χ) hFRprim hFRne a b c d i hi
          rw [corr_crt_split huv χ a b c d, norm_mul]
          refine (mul_le_mul hIu hIv (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
          have hprod : (∏ j ∈ Finset.univ.erase i,
                  (((Nat.gcd (u * v) (((![a, b, c, d] i : ℤ) - (![a, b, c, d] j : ℤ)).natAbs)) : ℕ) : ℝ))
              = (∏ j ∈ Finset.univ.erase i,
                    (((Nat.gcd u (((![a, b, c, d] i : ℤ) - (![a, b, c, d] j : ℤ)).natAbs)) : ℕ) : ℝ))
                * (∏ j ∈ Finset.univ.erase i,
                    (((Nat.gcd v (((![a, b, c, d] i : ℤ) - (![a, b, c, d] j : ℤ)).natAbs)) : ℕ) : ℝ)) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro j hj
            rw [gcd_mul_gcd_of_coprime huv]
            push_cast
            ring
          rw [hprod, card_primeFactors_mul_of_coprime hu0 hv0 huv, pow_add, Nat.cast_mul,
            Real.sqrt_mul (by positivity : (0:ℝ) ≤ (u:ℝ))]
          ring
  exact key q χ hχ h1 a b c d i hi

end Commons.NumberTheory.DirichletCharacter
