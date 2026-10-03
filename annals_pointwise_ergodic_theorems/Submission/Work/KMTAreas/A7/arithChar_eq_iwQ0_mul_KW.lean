import Mathlib
import Submission.Work.KMTAreas.coprime_prod_primePow_iwQ0
import Submission.Work.KMTAreas.prod_primePow_mem_iwW
import Submission.Work.KMTAreas.A7.Large.ArithFactor

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger

noncomputable section

/-! ## 0. Arithmetic preliminaries

`MW ρ l = ∏_{p ∈ (N₀,2^l]} p^{D}` is (definitionally) the product `iwProd ρ l` of the large prime
powers, hence nonzero, and coprime to `iwQ0 ρ l = (N₀!)^{D}`:  the primes of the range are larger
than `N₀`, so they do not divide `N₀!`. -/

private lemma iwQ0_pos (ρ : ℝ) (l : ℕ) : 0 < iwQ0 ρ l :=
  Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l)

/-- `a * b ∣ n` when `a ∣ n`, `b ∣ n` and `a`, `b` are coprime. -/
private lemma mul_dvd_of_coprime_of_dvd_of_dvd {a b n : ℕ} (hc : Nat.Coprime a b)
    (ha : a ∣ n) (hb : b ∣ n) : a * b ∣ n := by
  obtain ⟨k, rfl⟩ := ha
  have hbk : b ∣ k := (hc.symm.dvd_mul_right).mp (by rwa [mul_comm] at hb)
  obtain ⟨j, rfl⟩ := hbk
  exact ⟨j, by ring⟩

/-- A product of numbers each coprime to `k` is coprime to `k`. -/
private lemma coprime_prod_right {k : ℕ} {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ p ∈ s, Nat.Coprime k (f p)) : Nat.Coprime k (∏ p ∈ s, f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul_right
        (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

/-- A finite product of pairwise coprime divisors of `n` divides `n`. -/
private lemma prod_dvd_of_pairwise_coprime {s : Finset ℕ} {f : ℕ → ℕ} {n : ℕ}
    (hdvd : ∀ p ∈ s, f p ∣ n)
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (f p) (f q)) :
    (∏ p ∈ s, f p) ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hc : Nat.Coprime (f a) (∏ p ∈ s, f p) :=
        coprime_prod_right fun p hp =>
          (hcop p (Finset.mem_insert_of_mem hp) a (Finset.mem_insert_self a s)
            (fun h => ha (h ▸ hp))).symm
      exact mul_dvd_of_coprime_of_dvd_of_dvd hc (hdvd a (Finset.mem_insert_self a s))
        (ih (fun p hp => hdvd p (Finset.mem_insert_of_mem hp))
            (fun p hp q hq hpq => hcop p (Finset.mem_insert_of_mem hp)
              q (Finset.mem_insert_of_mem hq) hpq))

/-! ## 1. The combinatorial description of `KWfreqs`

`KWfreqs ρ l` is the set of `b < MW ρ l` for which there is `w ∈ W_{≤l}` with `MW ρ l ∣ w * b`.
This is the "at most `D_ρ` bad primes" condition rewritten in divisibility form. -/

/-! ## 2. The Fourier sum over a cyclic subgroup

`∑_{a<q} e(z·a/q) = q` when `q ∣ z` and `0` otherwise. -/

private lemma fourier_add_point {T : ℝ} {n : ℤ} {x y : AddCircle T} :
    fourier (T := T) n (x + y) = fourier (T := T) n x * fourier (T := T) n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

private lemma fourier_nsmul_point {T : ℝ} {n : ℤ} {x : AddCircle T} (m : ℕ) :
    fourier (T := T) n (m • x) = fourier (T := T) n x ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, fourier_eval_zero]
  | succ m ih => rw [succ_nsmul, fourier_add_point, ih, pow_succ]

/-- The finite geometric sum `∑_{a<q} ω^a` for a `q`-th root of unity `ω`. -/
private lemma geom_sum_range (q : ℕ) (ω : ℂ) (hω : ω ^ q = 1) :
    ∑ a ∈ Finset.range q, ω ^ a = if ω = 1 then (q : ℂ) else 0 := by
  have htel : (∑ a ∈ Finset.range q, ω ^ a) * (ω - 1) = 0 := by
    have h0 := Finset.sum_range_sub (fun i : ℕ => ω ^ i) q
    have hc : ∑ i ∈ Finset.range q, (ω ^ (i + 1) - ω ^ i)
        = ∑ i ∈ Finset.range q, ω ^ i * (ω - 1) :=
      Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    rw [hc] at h0
    rw [← Finset.sum_mul] at h0
    rw [hω, pow_zero, sub_self] at h0
    exact h0
  by_cases h1 : ω = 1
  · rw [if_pos h1]
    rw [h1]
    simp
  · rw [if_neg h1]
    rcases mul_eq_zero.mp htel with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) h1

/-- `z • (1/q) = 0` in `ℝ/ℤ` iff `q ∣ z`. -/
private lemma zsmul_div_eq_zero_iff {q : ℕ} (hq : 0 < q) (z : ℤ) :
    (z : ℤ) • (((1 : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)) = 0 ↔ (q : ℤ) ∣ z := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hcoe : (z : ℤ) • (((1 : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))
      = (((z : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_zsmul (p := (1 : ℝ)) (n := z) (x := (1 : ℝ) / (q : ℝ))]
    congr 1
    rw [zsmul_eq_mul, mul_one_div]
  rw [hcoe, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    have hkZ : (q : ℤ) * k = z := by
      have h1 : (((q : ℤ) * k : ℤ) : ℝ) = (z : ℝ) := by
        push_cast
        rw [hk]
        field_simp
      exact_mod_cast h1
    exact ⟨k, by rw [hkZ]⟩
  · rintro ⟨c, hc⟩
    refine ⟨(c : ℤ), ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    rw [hc]
    push_cast
    field_simp <;> ring

theorem fourier_sum_range_div (q : ℕ) (hq : 0 < q) (z : ℤ) :
    ∑ a ∈ Finset.range q,
        fourier (T := 1) z ((a : ℝ) / (q : ℝ) : AddCircle (1 : ℝ))
      = if (q : ℤ) ∣ z then (q : ℂ) else 0 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  set x : AddCircle (1 : ℝ) := ((1 : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)) with hx
  have hterm : ∀ a : ℕ, fourier (T := 1) z ((a : ℝ) / (q : ℝ) : AddCircle (1 : ℝ))
      = fourier (T := 1) z x ^ a := by
    intro a
    have hcoe : ((a : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)) = a • x := by
      rw [hx, ← AddCircle.coe_nsmul (p := (1 : ℝ)) (n := a) (x := (1 : ℝ) / (q : ℝ))]
      congr 1
      rw [nsmul_eq_mul, mul_one_div]
    rw [hcoe, fourier_nsmul_point]
  have hωq : fourier (T := 1) z x ^ q = 1 := by
    rw [← fourier_nsmul_point (n := z) (x := x) (m := q)]
    have hqx : q • x = 0 := by
      rw [hx, ← AddCircle.coe_nsmul (p := (1 : ℝ)) (n := q) (x := (1 : ℝ) / (q : ℝ))]
      rw [nsmul_eq_mul]
      have h1 : (q : ℝ) * ((1 : ℝ) / (q : ℝ)) = 1 := by field_simp
      rw [h1]
      exact AddCircle.coe_period (p := (1 : ℝ))
    rw [hqx, fourier_eval_zero]
  have hcrit : fourier (T := 1) z x = 1 ↔ (q : ℤ) ∣ z := by
    have h1 : fourier (T := 1) z x = 1 ↔ z • x = 0 := by
      rw [fourier_apply]
      constructor
      · intro hh
        have h2 : AddCircle.toCircle (z • x) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
          rw [AddCircle.toCircle_zero]
          exact Subtype.ext (by simpa using hh)
        exact AddCircle.injective_toCircle (by norm_num) h2
      · intro hh
        rw [hh]
        exact fourier_zero'
    have h2 : z • x = 0 ↔ (q : ℤ) ∣ z := by
      rw [hx]
      exact zsmul_div_eq_zero_iff hq z
    rw [h1, h2]
  rw [show (∑ a ∈ Finset.range q,
        fourier (T := 1) z ((a : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)))
      = ∑ a ∈ Finset.range q, fourier (T := 1) z x ^ a from
        Finset.sum_congr rfl fun a _ => hterm a]
  rw [geom_sum_range q (fourier (T := 1) z x) hωq]
  by_cases hh : (q : ℤ) ∣ z
  · rw [if_pos hh, if_pos (hcrit.mpr hh)]
  · rw [if_neg hh, if_neg (fun hc => hh (hcrit.mp hc))]

/-! ## 3. The CRT injectivity `ℤ/Q × ℤ/M ↪ ℝ/ℤ` for coprime `Q`, `M` -/

theorem div_add_div_injective {Q M : ℕ} (hQ : 0 < Q) (hM : 0 < M) (hcop : Nat.Coprime Q M)
    {a a' b b' : ℕ} (ha : a < Q) (ha' : a' < Q) (hb : b < M) (hb' : b' < M)
    (h : ((a : ℝ) / (Q : ℝ) + (b : ℝ) / (M : ℝ) : AddCircle (1 : ℝ))
       = ((a' : ℝ) / (Q : ℝ) + (b' : ℝ) / (M : ℝ) : AddCircle (1 : ℝ))) :
    a = a' ∧ b = b' := by
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hdiff : (((a : ℝ) / (Q : ℝ) + (b : ℝ) / (M : ℝ))
      - ((a' : ℝ) / (Q : ℝ) + (b' : ℝ) / (M : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at hdiff
  obtain ⟨k, hk⟩ := hdiff
  simp only [zsmul_eq_mul, mul_one] at hk
  have hZ : (M : ℤ) * ((a : ℤ) - a') + (Q : ℤ) * ((b : ℤ) - b') = k * (Q : ℤ) * M := by
    have hcast : (((M : ℤ) * ((a : ℤ) - a') + (Q : ℤ) * ((b : ℤ) - b') : ℤ) : ℝ)
        = (((k * (Q : ℤ) * M : ℤ)) : ℝ) := by
      push_cast
      rw [hk]
      field_simp
      ring
    exact_mod_cast hcast
  have hQA : (Q : ℤ) ∣ (M : ℤ) * ((a : ℤ) - a') := by
    have h1 : (M : ℤ) * ((a : ℤ) - a')
        = k * (Q : ℤ) * M - (Q : ℤ) * ((b : ℤ) - b') := by rw [← hZ]; ring
    have h2 : (Q : ℤ) ∣ k * (Q : ℤ) * M - (Q : ℤ) * ((b : ℤ) - b') :=
      ⟨k * M - ((b : ℤ) - b'), by ring⟩
    rwa [← h1] at h2
  have hQA' : (Q : ℤ) ∣ (a : ℤ) - a' :=
    hcop.isCoprime.dvd_of_dvd_mul_right (by rwa [mul_comm] at hQA)
  have hAnat : Q ∣ ((a : ℤ) - a').natAbs := Int.natCast_dvd.mp hQA'
  have hAlt : ((a : ℤ) - a').natAbs < Q := by
    rcases le_total a a' with hle | hle
    · rw [Int.natAbs_natCast_sub_natCast_of_le hle]; omega
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hle]; omega
  have hA0 : ((a : ℤ) - a').natAbs = 0 := by
    by_contra hne
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hAnat) (not_le.mpr hAlt)
  have haa : a = a' := by
    have h0 : (a : ℤ) - a' = 0 := Int.natAbs_eq_zero.mp hA0
    omega
  have hMB : (M : ℤ) ∣ (Q : ℤ) * ((b : ℤ) - b') := by
    have h1 : (Q : ℤ) * ((b : ℤ) - b')
        = k * (Q : ℤ) * M - (M : ℤ) * ((a : ℤ) - a') := by rw [← hZ]; ring
    have h2 : (M : ℤ) ∣ k * (Q : ℤ) * M - (M : ℤ) * ((a : ℤ) - a') :=
      ⟨k * Q - ((a : ℤ) - a'), by ring⟩
    rwa [← h1] at h2
  have hMB' : (M : ℤ) ∣ (b : ℤ) - b' :=
    hcop.symm.isCoprime.dvd_of_dvd_mul_left hMB
  have hBnat : M ∣ ((b : ℤ) - b').natAbs := Int.natCast_dvd.mp hMB'
  have hBlt : ((b : ℤ) - b').natAbs < M := by
    rcases le_total b b' with hle | hle
    · rw [Int.natAbs_natCast_sub_natCast_of_le hle]; omega
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hle]; omega
  have hB0 : ((b : ℤ) - b').natAbs = 0 := by
    by_contra hne
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hBnat) (not_le.mpr hBlt)
  refine ⟨haa, ?_⟩
  have h0 : (b : ℤ) - b' = 0 := Int.natAbs_eq_zero.mp hB0
  omega

/-! ## 4. The coprime splitting of a torsion element -/

theorem eq_add_of_coprime_nsmul_eq_zero {G : Type*} [AddCommGroup G] {Q w : ℕ}
    (hcop : Nat.Coprime Q w) {α : G} (h : (Q * w) • α = 0) :
    ∃ x y : G, Q • x = 0 ∧ w • y = 0 ∧ α = x + y := by
  obtain ⟨u, v, huv⟩ := hcop.isCoprime
  refine ⟨(v * (w : ℤ)) • α, (u * (Q : ℤ)) • α, ?_, ?_, ?_⟩
  · rw [← natCast_zsmul, ← mul_zsmul]
    rw [show ((Q : ℤ) * (v * (w : ℤ))) = v * ((Q * w : ℕ) : ℤ) by push_cast; ring]
    rw [mul_zsmul, natCast_zsmul, h, zsmul_zero]
  · rw [← natCast_zsmul, ← mul_zsmul]
    rw [show ((w : ℤ) * (u * (Q : ℤ))) = u * ((Q * w : ℕ) : ℤ) by push_cast; ring]
    rw [mul_zsmul, natCast_zsmul, h, zsmul_zero]
  · rw [← add_zsmul, show v * (w : ℤ) + u * (Q : ℤ) = 1 by linarith [huv], one_zsmul]

/-! ## 5. `w • (b/M) = 0` iff `M ∣ w * b` -/

/-- `n/M ∈ ℝ/ℤ` vanishes iff `M ∣ n`. -/
private lemma coe_div_eq_zero_iff {M n : ℕ} (hM : 0 < M) :
    (((n : ℝ) / (M : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 0 ↔ M ∣ n := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    have hkZ : (M : ℤ) * k = (n : ℤ) := by
      have h2 : (M : ℝ) * (k : ℝ) = (n : ℝ) := by
        rw [hk]
        field_simp
      exact_mod_cast h2
    exact Int.natCast_dvd.mp ⟨k, hkZ.symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨(c : ℤ), ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    rw [hc]
    push_cast
    field_simp <;> ring

/-- `w • (b/M) = 0` in `ℝ/ℤ` iff `M ∣ w * b`. -/
private lemma nsmul_div_eq_zero_iff {M w b : ℕ} (hM : 0 < M) :
    (w : ℕ) • (((b : ℝ) / (M : ℝ)) : AddCircle (1 : ℝ)) = 0 ↔ M ∣ w * b := by
  have hcoe : (w : ℕ) • (((b : ℝ) / (M : ℝ)) : AddCircle (1 : ℝ))
      = ((((w * b : ℕ) : ℝ) / (M : ℝ)) : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_nsmul (p := (1 : ℝ)) (n := w) (x := (b : ℝ) / (M : ℝ))]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    rw [mul_div_assoc]
  rw [hcoe]
  exact coe_div_eq_zero_iff hM

/-! ## 6. The two inclusions describing `(ℚ/ℤ)_{≤l}` as a sum of torsion subgroups -/

/-! ## 7. The character sum -/

end

end Work.KMTAreas.A7
