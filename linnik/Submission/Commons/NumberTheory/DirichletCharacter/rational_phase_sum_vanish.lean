import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.primePowSubgroup_quadratic_sum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

private lemma isUnit_intCast_zmod_primePow {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) : IsUnit (((x : ℤ)) : ZMod (p ^ e)) := by
  have hcop : x.natAbs.Coprime (p ^ e) := by
    rw [Nat.coprime_pow_right_iff (by omega : 0 < e), Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    intro hdvd
    exact hx (Int.natAbs_dvd_natAbs.mp (by simpa using hdvd))
  have hunit : IsUnit (((x.natAbs : ℕ)) : ZMod (p ^ e)) :=
    (ZMod.isUnit_iff_coprime x.natAbs (p ^ e)).mpr hcop
  have hcast : (((x.natAbs : ℤ)) : ZMod (p ^ e)) = ((x.natAbs : ℕ) : ZMod (p ^ e)) :=
    Int.cast_natCast _
  rcases Int.natAbs_eq x with h | h
  · have heq : (((x : ℤ)) : ZMod (p ^ e)) = (((x.natAbs : ℤ)) : ZMod (p ^ e)) := by
      nth_rewrite 1 [h]; rfl
    rw [heq, hcast]; exact hunit
  · have heq : (((x : ℤ)) : ZMod (p ^ e)) = - (((x.natAbs : ℤ)) : ZMod (p ^ e)) := by
      nth_rewrite 1 [h]
      push_cast
      ring
    rw [heq, hcast]; exact hunit.neg

private lemma eval_eq_coeff' (Q : Polynomial ℤ) (h : Q.natDegree ≤ 2) (x : ℤ) :
    Q.eval x = Q.coeff 0 + Q.coeff 1 * x + Q.coeff 2 * x ^ 2 := by
  have hsum : (∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (Q.coeff i) * Polynomial.X ^ i)
      = ∑ i ∈ Finset.range 3, Polynomial.C (Q.coeff i) * Polynomial.X ^ i := by
    refine Finset.sum_subset (fun i hi => ?_) (fun i hi3 hni => ?_)
    · simp only [Finset.mem_range] at hi ⊢; omega
    · simp only [Finset.mem_range] at hi3 hni
      have : Q.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  conv_lhs => rw [Q.as_sum_range_C_mul_X_pow, hsum, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_zero, Polynomial.eval_one]

private lemma derivative_eval_eq_coeff' (Q : Polynomial ℤ) (h : Q.natDegree ≤ 2) (x : ℤ) :
    (Polynomial.derivative Q).eval x = Q.coeff 1 + 2 * Q.coeff 2 * x := by
  have hsum : (∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (Q.coeff i) * Polynomial.X ^ i)
      = ∑ i ∈ Finset.range 3, Polynomial.C (Q.coeff i) * Polynomial.X ^ i := by
    refine Finset.sum_subset (fun i hi => ?_) (fun i hi3 hni => ?_)
    · simp only [Finset.mem_range] at hi ⊢; omega
    · simp only [Finset.mem_range] at hi3 hni
      have : Q.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  conv_lhs => rw [Q.as_sum_range_C_mul_X_pow, hsum, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_zero,
    Polynomial.eval_one]
  ring

private lemma eval_add_mul_eq (Q : Polynomial ℤ) (h : Q.natDegree ≤ 2) (y M t : ℤ) :
    Q.eval (y + M * t) =
      Q.eval y + M * t * (Polynomial.derivative Q).eval y + (M * t) ^ 2 * Q.coeff 2 := by
  rw [eval_eq_coeff' Q h (y + M * t), eval_eq_coeff' Q h y, derivative_eval_eq_coeff' Q h y]
  ring

private lemma inv_sub_inv {R : Type*} [CommRing R] [Inv R] {u v : R}
    (hu : u * u⁻¹ = 1) (hv : v * v⁻¹ = 1) :
    u⁻¹ - v⁻¹ = u⁻¹ * v⁻¹ * (v - u) := by
  have h : u⁻¹ * v⁻¹ * (v - u) = u⁻¹ - v⁻¹ := by
    calc u⁻¹ * v⁻¹ * (v - u)
        = u⁻¹ * (v⁻¹ * v) - (u⁻¹ * u) * v⁻¹ := by ring
      _ = u⁻¹ * (v * v⁻¹) - (u * u⁻¹) * v⁻¹ := by rw [mul_comm v⁻¹ v, mul_comm u⁻¹ u]
      _ = u⁻¹ * 1 - 1 * v⁻¹ := by rw [hv, hu]
      _ = u⁻¹ - v⁻¹ := by ring
  rw [h]

private lemma rational_chirp (p e a K : ℕ) [Fact p.Prime] (he : 2 ≤ e)
    (ha : 1 ≤ a) (hK : 1 ≤ K) (hKsum : a + K = e - 1)
    (A : ZMod (p^e)) (hA : (p : ZMod (p^e)) ∣ A - 1)
    (N G : Polynomial ℤ) (hN : N.natDegree ≤ 2) (hG : G.natDegree ≤ 2)
    (hN1 : ¬ (p:ℤ) ∣ N.coeff 1) (hN2 : (p:ℤ) ∣ N.coeff 2)
    (hG1 : (p:ℤ) ∣ G.coeff 1) (hG2 : (p:ℤ) ∣ G.coeff 2)
    (hG0 : ¬ (p:ℤ) ∣ G.coeff 0) (y : ℤ) :
    ∃ b : ℤ, ¬ (p:ℤ) ∣ b ∧ ∀ t : ℤ,
      A + (p : ZMod (p^e))^a * ((N.eval (y + (p:ℤ)^K * t) : ℤ) : ZMod (p^e))
              * (((G.eval (y + (p:ℤ)^K * t) : ℤ) : ZMod (p^e)))⁻¹
        = (A + (p : ZMod (p^e))^a * ((N.eval y : ℤ) : ZMod (p^e))
              * (((G.eval y : ℤ) : ZMod (p^e)))⁻¹)
          * (((1 + (p:ℤ)^(e-1) * (t * b) : ℤ)) : ZMod (p^e)) := by
  have he1 : 1 ≤ e := by omega
  set pz : ZMod (p^e) := (p : ZMod (p^e)) with hpzdef
  have hpze : pz^e = 0 := by rw [hpzdef, ← Nat.cast_pow]; exact ZMod.natCast_self (p^e)
  have hpnil : IsNilpotent pz := ⟨e, hpze⟩
  have hGunit : ∀ z : ℤ, IsUnit (((G.eval z : ℤ)) : ZMod (p^e)) := by
    intro z
    refine isUnit_intCast_zmod_primePow he1 ?_
    intro hdvd
    have hcoe := eval_eq_coeff' G hG z
    have hpdiv : (p:ℤ) ∣ G.coeff 1 * z + G.coeff 2 * z^2 :=
      dvd_add (dvd_mul_of_dvd_left hG1 z) (dvd_mul_of_dvd_left hG2 (z^2))
    have hmem : (p:ℤ) ∣ G.coeff 0 := by
      have heq : G.coeff 0 = G.eval z - (G.coeff 1 * z + G.coeff 2 * z^2) := by
        rw [hcoe]; ring
      rw [heq]; exact dvd_sub hdvd hpdiv
    exact hG0 hmem
  set ν : ZMod (p^e) := ((N.eval y : ℤ) : ZMod (p^e)) with hνdef
  set γ : ZMod (p^e) := ((G.eval y : ℤ) : ZMod (p^e)) with hγdef
  set ν' : ZMod (p^e) := ((N.derivative.eval y : ℤ) : ZMod (p^e)) with hν'def
  set γ' : ZMod (p^e) := ((G.derivative.eval y : ℤ) : ZMod (p^e)) with hγ'def
  have hγunit : IsUnit γ := by rw [hγdef]; exact hGunit y
  have hγmul : γ * γ⁻¹ = 1 := ZMod.mul_inv_of_unit γ hγunit
  have hγmul' : γ⁻¹ * γ = 1 := ZMod.inv_mul_of_unit γ hγunit
  have hUyunit : IsUnit (A + pz^a * ν * γ⁻¹) := by
    obtain ⟨δ, hδ⟩ := hA
    have hAeq : A = 1 + pz * δ := by
      rw [hpzdef] at hδ ⊢
      linear_combination hδ
    have hpza : pz^a = pz * pz^(a-1) := by
      conv_lhs => rw [show a = (a-1)+1 by omega, pow_succ']
    have hfac : 1 + pz * δ + pz * pz^(a-1) * ν * γ⁻¹
        = 1 + pz * (δ + pz^(a-1) * ν * γ⁻¹) := by ring
    have hnil : IsNilpotent (pz * (δ + pz^(a-1) * ν * γ⁻¹)) := by
      rcases hpnil with ⟨n, hn⟩
      exact ⟨n, by rw [mul_pow, hn, zero_mul]⟩
    rw [hAeq, hpza, hfac]
    exact hnil.isUnit_one_add

  have hUymul : (A + pz^a * ν * γ⁻¹) * (A + pz^a * ν * γ⁻¹)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hUyunit
  have hUyinv : (A + pz^a * ν * γ⁻¹)⁻¹ * (A + pz^a * ν * γ⁻¹) = 1 :=
    ZMod.inv_mul_of_unit _ hUyunit
  set c : ZMod (p^e) := (ν' * γ - ν * γ') * γ⁻¹ * γ⁻¹ * (A + pz^a * ν * γ⁻¹)⁻¹ with hcdef
  have hkey : ∀ t : ℤ,
      A + pz^a * ((N.eval (y + (p:ℤ)^K * t) : ℤ) : ZMod (p^e))
              * (((G.eval (y + (p:ℤ)^K * t) : ℤ) : ZMod (p^e)))⁻¹
        = (A + pz^a * ν * γ⁻¹) * (1 + pz^(e-1) * (t : ZMod (p^e)) * c) := by
    intro t
    set tt : ZMod (p^e) := (t : ZMod (p^e)) with httdef
    set Nt : ZMod (p^e) := ((N.eval (y + (p:ℤ)^K * t) : ℤ) : ZMod (p^e)) with hNtdef
    set Gt : ZMod (p^e) := ((G.eval (y + (p:ℤ)^K * t) : ℤ) : ZMod (p^e)) with hGtdef
    change A + pz^a * Nt * Gt⁻¹ = (A + pz^a * ν * γ⁻¹) * (1 + pz^(e-1) * tt * c)
    have hGtunit : IsUnit Gt := by rw [hGtdef]; exact hGunit _
    have hGtmul : Gt * Gt⁻¹ = 1 := ZMod.mul_inv_of_unit Gt hGtunit
    have hNtval : Nt = ν + (pz^K * tt) * ν' + (pz^K * tt)^2 * ((N.coeff 2 : ℤ) : ZMod (p^e)) := by
      rw [hNtdef, hνdef, hν'def, eval_add_mul_eq N hN y ((p:ℤ)^K) t]
      push_cast
      rw [httdef, ← hpzdef]
      try ring
    have hGtval : Gt = γ + (pz^K * tt) * γ' + (pz^K * tt)^2 * ((G.coeff 2 : ℤ) : ZMod (p^e)) := by
      rw [hGtdef, hγdef, hγ'def, eval_add_mul_eq G hG y ((p:ℤ)^K) t]
      push_cast
      rw [httdef, ← hpzdef]
      try ring
    have hR : Nt * γ - ν * Gt
        = (pz^K*tt)*(ν'*γ - ν*γ') + (pz^K*tt)^2
            * (((N.coeff 2 : ℤ) : ZMod (p^e)) * γ - ν * ((G.coeff 2 : ℤ) : ZMod (p^e))) := by
      rw [hNtval, hGtval]; ring
    have hpa : pz^a * pz^K = pz^(e-1) := by
      rw [← pow_add, hKsum]
    have hpa2 : pz^a * (pz^K)^2 = 0 := by
      rw [← pow_mul, ← pow_add]
      rw [show a + K * 2 = e + (a + K*2 - e) by omega, pow_add, hpze, zero_mul]
    have hRval : A + pz^a * Nt * Gt⁻¹ - (A + pz^a * ν * γ⁻¹)
        = pz^(e-1) * tt * ((ν'*γ - ν*γ') * γ⁻¹ * Gt⁻¹) := by
      have e1 : Nt * Gt⁻¹ - ν * γ⁻¹ = (Nt*γ - ν*Gt) * γ⁻¹ * Gt⁻¹ := by
        linear_combination (-(Nt*Gt⁻¹)) * hγmul + (ν*γ⁻¹) * hGtmul
      rw [show A + pz^a * Nt * Gt⁻¹ - (A + pz^a * ν * γ⁻¹) = pz^a * (Nt*Gt⁻¹ - ν*γ⁻¹) by ring]
      rw [e1, hR]
      rw [show pz^a * (((pz^K*tt)*(ν'*γ - ν*γ') + (pz^K*tt)^2 * (((N.coeff 2 : ℤ) : ZMod (p^e)) * γ - ν * ((G.coeff 2 : ℤ) : ZMod (p^e)))) * γ⁻¹ * Gt⁻¹)
            = (pz^a * pz^K) * tt * (ν'*γ - ν*γ') * γ⁻¹ * Gt⁻¹
              + (pz^a * (pz^K)^2) * tt^2 * (((N.coeff 2 : ℤ) : ZMod (p^e)) * γ - ν * ((G.coeff 2 : ℤ) : ZMod (p^e))) * γ⁻¹ * Gt⁻¹ by ring]
      rw [hpa, hpa2]; ring
    have hγGt : ∃ W : ZMod (p^e), γ - Gt = pz * W := by
      refine ⟨-(pz^(K-1) * tt * (γ' + (pz^K*tt)*((G.coeff 2:ℤ):ZMod (p^e)))), ?_⟩
      have hMz' : pz^K = pz * pz^(K-1) := by
        conv_lhs => rw [show K = (K-1)+1 by omega, pow_succ']
      rw [hGtval, hMz']
      ring
    have ht2 : pz^(e-1) * tt * ((ν'*γ - ν*γ') * γ⁻¹ * Gt⁻¹)
        = pz^(e-1) * tt * ((ν'*γ - ν*γ') * γ⁻¹ * γ⁻¹) := by
      obtain ⟨W, hW⟩ := hγGt
      have hGi : Gt⁻¹ - γ⁻¹ = Gt⁻¹ * γ⁻¹ * (γ - Gt) := inv_sub_inv hGtmul hγmul
      have hpze1 : pz^(e-1) * pz = pz^e := by
        conv_lhs => rw [← pow_succ, show (e-1)+1 = e by omega]
      rw [← sub_eq_zero]
      rw [show pz^(e-1)*tt*((ν'*γ-ν*γ')*γ⁻¹*Gt⁻¹) - pz^(e-1)*tt*((ν'*γ-ν*γ')*γ⁻¹*γ⁻¹)
            = pz^(e-1)*tt*(ν'*γ-ν*γ')*γ⁻¹*(Gt⁻¹ - γ⁻¹) by ring]
      rw [hGi, hW]
      rw [show pz^(e-1)*tt*(ν'*γ-ν*γ')*γ⁻¹*(Gt⁻¹*γ⁻¹*(pz*W))
            = (pz^(e-1)*pz) * (tt*(ν'*γ-ν*γ')*γ⁻¹*(Gt⁻¹*γ⁻¹*W)) by ring]
      rw [hpze1, hpze, zero_mul]
    have hUyc : (A + pz^a * ν * γ⁻¹) * c = (ν'*γ - ν*γ') * γ⁻¹ * γ⁻¹ := by
      rw [hcdef]
      rw [show (A+pz^a*ν*γ⁻¹)*((ν'*γ-ν*γ')*γ⁻¹*γ⁻¹*(A+pz^a*ν*γ⁻¹)⁻¹)
            = (ν'*γ-ν*γ')*γ⁻¹*γ⁻¹*((A+pz^a*ν*γ⁻¹)*(A+pz^a*ν*γ⁻¹)⁻¹) by ring]
      rw [hUymul, mul_one]
    have hcomb : A + pz^a * Nt * Gt⁻¹
        = (A + pz^a * ν * γ⁻¹) + pz^(e-1) * tt * ((ν'*γ - ν*γ') * γ⁻¹ * Gt⁻¹) := by
      linear_combination hRval
    rw [hcomb, ht2]
    rw [show pz^(e-1) * tt * ((ν'*γ - ν*γ') * γ⁻¹ * γ⁻¹)
          = (A + pz^a * ν * γ⁻¹) * (pz^(e-1) * tt * c) from by rw [← hUyc]; ring]
    ring
  have hp_dvd_pe : p ∣ p^e := ⟨p^(e-1), by conv_lhs => rw [show e = (e-1)+1 by omega, pow_succ']⟩
  have hφcast : ∀ n : ℤ,
      (ZMod.castHom hp_dvd_pe (ZMod p)) (((n : ℤ) : ZMod (p^e))) = ((n : ℤ) : ZMod p) := by
    intro n
    rw [ZMod.castHom_apply, ZMod.cast_intCast hp_dvd_pe]
  have hφγ : (ZMod.castHom hp_dvd_pe (ZMod p)) γ = ((G.coeff 0 : ℤ) : ZMod p) := by
    rw [hγdef, hφcast, eval_eq_coeff' G hG y]
    have h1 : ((G.coeff 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hG1
    have h2 : ((G.coeff 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hG2
    push_cast
    rw [h1, h2]; ring
  have hφγ_ne : (ZMod.castHom hp_dvd_pe (ZMod p)) γ ≠ 0 := by
    rw [hφγ]
    exact fun h => hG0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hφν' : (ZMod.castHom hp_dvd_pe (ZMod p)) ν' = ((N.coeff 1 : ℤ) : ZMod p) := by
    rw [hν'def, hφcast, derivative_eval_eq_coeff' N hN y]
    have h2 : ((N.coeff 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hN2
    push_cast
    rw [h2]; ring
  have hφν'_ne : (ZMod.castHom hp_dvd_pe (ZMod p)) ν' ≠ 0 := by
    rw [hφν']
    exact fun h => hN1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hφγ' : (ZMod.castHom hp_dvd_pe (ZMod p)) γ' = 0 := by
    rw [hγ'def, hφcast, derivative_eval_eq_coeff' G hG y]
    have h1 : ((G.coeff 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hG1
    have h2 : ((G.coeff 2 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hG2
    push_cast
    rw [h1, h2]; ring
  have hφR : (ZMod.castHom hp_dvd_pe (ZMod p)) (ν'*γ - ν*γ')
      = (ZMod.castHom hp_dvd_pe (ZMod p)) ν' * (ZMod.castHom hp_dvd_pe (ZMod p)) γ := by
    rw [map_sub, map_mul, map_mul, hφγ', mul_zero, sub_zero]
  have hφR_ne : (ZMod.castHom hp_dvd_pe (ZMod p)) (ν'*γ - ν*γ') ≠ 0 := by
    rw [hφR]; exact mul_ne_zero hφν'_ne hφγ_ne
  have hγsq : γ⁻¹ * γ⁻¹ * γ^2 = 1 := by
    rw [show γ⁻¹*γ⁻¹*γ^2 = (γ⁻¹*γ)*(γ⁻¹*γ) by ring, hγmul', mul_one]
  have hφc_ne : (ZMod.castHom hp_dvd_pe (ZMod p)) c ≠ 0 := by
    have hφcR : (ZMod.castHom hp_dvd_pe (ZMod p)) c
          * ((ZMod.castHom hp_dvd_pe (ZMod p)) γ)^2
          * (ZMod.castHom hp_dvd_pe (ZMod p)) (A + pz^a * ν * γ⁻¹)
        = (ZMod.castHom hp_dvd_pe (ZMod p)) (ν'*γ - ν*γ') := by
      rw [← map_pow, ← map_mul, ← map_mul]
      congr 1
      rw [hcdef]
      rw [show (ν'*γ-ν*γ')*γ⁻¹*γ⁻¹*(A+pz^a*ν*γ⁻¹)⁻¹ * γ^2 * (A+pz^a*ν*γ⁻¹)
            = (ν'*γ-ν*γ') * (γ⁻¹*γ⁻¹*γ^2) * ((A+pz^a*ν*γ⁻¹)⁻¹*(A+pz^a*ν*γ⁻¹)) by ring]
      rw [hγsq, hUyinv, mul_one, mul_one]
    intro hc0
    have : (ZMod.castHom hp_dvd_pe (ZMod p)) (ν'*γ - ν*γ') = 0 := by
      rw [← hφcR, hc0, zero_mul, zero_mul]
    exact hφR_ne this
  have hcv : ((c.val : ℤ) : ZMod (p^e)) = c := by
    rw [show ((c.val : ℤ) : ZMod (p^e)) = ((c.val : ℕ) : ZMod (p^e)) from Int.cast_natCast _,
      ZMod.natCast_zmod_val]
  set b : ℤ := (c.val : ℤ) with hbdef
  have hbc : ((b : ℤ) : ZMod (p^e)) = c := hcv
  have hb_ne : ¬ (p:ℤ) ∣ b := by
    intro hdvd
    have h0 : ((b : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    refine hφc_ne ?_
    rw [← hbc, hφcast]
    exact h0
  refine ⟨b, hb_ne, ?_⟩
  intro t
  rw [hkey t]
  rw [show (1 : ZMod (p^e)) + pz^(e-1) * (t : ZMod (p^e)) * c
        = (((1 + (p:ℤ)^(e-1) * (t * b) : ℤ)) : ZMod (p^e)) from by
      rw [← hbc, hpzdef]
      push_cast
      ring]


private theorem chirp_sum_vanish (p e N : ℕ) [Fact p.Prime] (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p^e))
    (htop : χ ((((1 + p^(e-1) : ℕ)) : ZMod (p^e))) ≠ 1)
    (hN : 1 ≤ N) (b : ℤ) (hb : ¬ (p:ℤ) ∣ b) :
    ∑ t ∈ Finset.range (p^N), χ (((1 + (p:ℤ)^(e-1) * ((t:ℤ) * b) : ℤ) : ZMod (p^e))) = 0 := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  set f : ℕ → ℂ := fun t => χ (((1 + (p:ℤ)^(e-1) * ((t:ℤ) * b) : ℤ) : ZMod (p^e))) with hf
  have hper : ∀ a s : ℕ, f (a + p * s) = f a := by
    intro a s
    simp only [hf]
    congr 1
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-(b * (s:ℤ)), ?_⟩
    push_cast
    rw [show ((p:ℤ))^e = (p:ℤ)^(e-1) * (p:ℤ) by rw [← pow_succ]; congr 1; omega]
    ring
  rw [pow_succ']
  rw [Commons.Algebra.BigOperators.sum_range_mul_eq f p (p^N')]
  have hinner : ∀ a : ℕ, (∑ s ∈ Finset.range (p^N'), f (a + p * s)) = ((p^N' : ℕ) : ℂ) * f a := by
    intro a
    rw [Finset.sum_congr rfl (fun s _ => hper a s), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.mul_sum]
  have horth : (∑ a ∈ Finset.range p, f a) = 0 := by
    simp only [hf]
    rw [Commons.NumberTheory.DirichletCharacter.primePowKernel_sum_orthogonality p e he χ htop b, if_neg hb]
  rw [horth, mul_zero]


/-- **Vanishing of a `p`-adically shallow rational phase sum with a linear numerator.**

`p` odd prime, `e ≥ 2`, `χ` a Dirichlet character modulo `p^e` which is non-trivial on the top kernel
`1 + p^(e-1)`.  Let `a ≥ 1`, `n ≥ 0` with `a ≤ e-2` and `e ≤ a+n`, let `A : ZMod (p^e)` satisfy
`A ≡ 1 (mod p)`, let `N₂ ∈ ℤ[X]` have degree `≤ 2` with `p ∣ N₂.coeff 2` and `p ∤ N₂.coeff 1`
(so `N₂` is linear with non-zero slope modulo `p`), and let `G₂ ∈ ℤ[X]` have degree `≤ 2` with
`p ∣ G₂.coeff 1`, `p ∣ G₂.coeff 2` and `p ∤ G₂.coeff 0`.  Then the sum vanishes identically:

`∑_{z < p^n} χ (A + p^a * N₂(z) * G₂(z)⁻¹) = 0`.

Proof plan: as in `rational_phase_sum_bound`, put `k = e-1-a` (so `1 ≤ k ≤ n`), split `z = y + p^k t`,
and use orthogonality on the top kernel to reduce to `p^(n-k) · ∑_{y < p^k} [p ∣ (N₂'G₂-N₂G₂')(y)] · χ(V y)`.
But now `N₂' ≡ N₂.coeff 1 ≢ 0` and `G₂' ≡ 0`, `G₂ ≡ G₂.coeff 0 ≢ 0` modulo `p`, so
`N₂'G₂ - N₂G₂' ≡ N₂.coeff 1 * G₂.coeff 0 ≢ 0 (mod p)`; the condition `p ∣ (N₂'G₂-N₂G₂')(y)` is never
satisfied and the sum is `0`. -/
theorem rational_phase_sum_vanish (p e a n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e))
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1)
    (ha : 1 ≤ a) (hak : a ≤ e - 2) (han : e ≤ a + n)
    (A : ZMod (p ^ e)) (hA : (p : ZMod (p ^ e)) ∣ A - 1)
    (N₂ G₂ : Polynomial ℤ) (hN : N₂.natDegree ≤ 2)
    (hN2 : (p : ℤ) ∣ N₂.coeff 2) (hN1 : ¬ (p : ℤ) ∣ N₂.coeff 1)
    (hG : G₂.natDegree ≤ 2) (hG1 : (p : ℤ) ∣ G₂.coeff 1) (hG2 : (p : ℤ) ∣ G₂.coeff 2)
    (hG0 : ¬ (p : ℤ) ∣ G₂.coeff 0) :
    ∑ z ∈ Finset.range (p ^ n), χ (A + (p : ZMod (p ^ e)) ^ a *
        ((N₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)) * (((G₂.eval (z : ℤ) : ℤ) : ZMod (p ^ e)))⁻¹) = 0 := by
  set K := e - 1 - a with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKsum : a + K = e - 1 := by omega
  have hKn : K ≤ n := by omega
  have hNKn : 1 ≤ n - K := by omega
  set F : ℕ → ℂ := fun z => χ (A + (p : ZMod (p^e))^a * ((N₂.eval (z:ℤ):ℤ):ZMod (p^e))
        * (((G₂.eval (z:ℤ):ℤ):ZMod (p^e)))⁻¹) with hF
  change ∑ z ∈ Finset.range (p^n), F z = 0
  rw [show p^n = p^K * p^(n-K) by rw [← pow_add]; congr 1; omega]
  rw [Commons.Algebra.BigOperators.sum_range_mul_eq F (p^K) (p^(n-K))]
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨b, hb, hcong⟩ := rational_chirp p e a K he ha hK1 hKsum A hA N₂ G₂ hN hG hN1 hN2 hG1 hG2 hG0 (y:ℤ)
  have hper : ∀ t : ℕ,
      F (y + p^K * t) = F y * χ (((1 + (p:ℤ)^(e-1) * ((t:ℤ) * b) : ℤ) : ZMod (p^e))) := by
    intro t
    simp only [hF]
    rw [show ((y + p^K * t : ℕ) : ℤ) = (y:ℤ) + (p:ℤ)^K * (t:ℤ) by push_cast; ring]
    rw [hcong (t:ℤ), map_mul]
  rw [Finset.sum_congr rfl (fun t _ => hper t), ← Finset.mul_sum,
    chirp_sum_vanish p e (n - K) he χ htop hNKn b hb, mul_zero]

end Commons.NumberTheory.DirichletCharacter
