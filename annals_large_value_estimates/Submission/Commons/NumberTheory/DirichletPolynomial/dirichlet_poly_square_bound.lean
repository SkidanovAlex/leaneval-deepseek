import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length
import Submission.Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_mean_value

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.DirichletPolynomial

private noncomputable def FF (u : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (Complex.I * (u : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)

private lemma FF_mul (u : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    FF u n * FF u m = FF u (n * m) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hnm1 : 1 ≤ n*m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlog : Real.log ((n*m : ℕ) : ℝ) = Real.log (n:ℝ) + Real.log (m:ℝ) := by
    rw [show ((n*m : ℕ) : ℝ) = (n:ℝ)*(m:ℝ) by push_cast; ring, Real.log_mul hn0.ne' hm0.ne']
  have hsq : (Real.sqrt ((n*m : ℕ) : ℝ) : ℂ)
      = (Real.sqrt (n:ℝ) : ℂ) * (Real.sqrt (m:ℝ) : ℂ) := by
    rw [show ((n*m : ℕ) : ℝ) = (n:ℝ)*(m:ℝ) by push_cast; ring, Real.sqrt_mul hn0.le]
    push_cast; ring
  unfold FF
  rw [hsq, cn_pow_exp (n*m) u hnm1, cn_pow_exp n u hn, cn_pow_exp m u hm, hlog]
  rw [div_mul_div_comm, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma term_eq (u : ℝ) (c : ℕ → ℂ) (n : ℕ) :
    c n * (n : ℂ) ^ (Complex.I * (u : ℂ)) / (Real.sqrt (n : ℝ) : ℂ) = c n * FF u n := by
  unfold FF; ring

private noncomputable def reprCoeff (N : ℕ) (c : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc N (2*N)).product (Finset.Icc N (2*N)),
    (if p.1*p.2 = k then c p.1 * c p.2 else 0)

private lemma sq_expansion (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ) (u : ℝ) :
    (∑ n ∈ Finset.Icc N (2*N), c n * (n:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (n:ℝ):ℂ))^2
    = ∑ k ∈ Finset.Icc (N*N) (4*(N*N)),
        reprCoeff N c k *
        ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ)) := by
  set s : Finset ℕ := Finset.Icc N (2*N) with hs
  set t : Finset ℕ := Finset.Icc (N*N) (4*(N*N)) with ht
  have hmem_s : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    rw [hs, Finset.mem_Icc] at hn
    exact le_trans hN hn.1
  have hprod : ∀ p ∈ s.product s, p.1 * p.2 ∈ t := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    obtain ⟨hp1, hp2⟩ := hp'
    have h1 : N ≤ p.1 := (Finset.mem_Icc.mp (hs ▸ hp1)).1
    have h2 : N ≤ p.2 := (Finset.mem_Icc.mp (hs ▸ hp2)).1
    have h3 : p.1 ≤ 2*N := (Finset.mem_Icc.mp (hs ▸ hp1)).2
    have h4 : p.2 ≤ 2*N := (Finset.mem_Icc.mp (hs ▸ hp2)).2
    rw [ht, Finset.mem_Icc]
    constructor
    · exact Nat.mul_le_mul h1 h2
    · calc p.1 * p.2 ≤ (2*N)*(2*N) := Nat.mul_le_mul h3 h4
        _ = 4*(N*N) := by ring
  have h1 : (∑ n ∈ s, c n * (n:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (n:ℝ):ℂ))^2
      = ∑ p ∈ s.product s, c p.1 * c p.2 * FF u (p.1*p.2) := by
    rw [pow_two, Finset.sum_mul_sum]
    rw [show s.product s = s ×ˢ s from rfl, Finset.sum_product]
    refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => ?_))
    rw [term_eq u c n, term_eq u c m]
    rw [show c n * FF u n * (c m * FF u m) = c n * c m * (FF u n * FF u m) by ring]
    rw [FF_mul u (hmem_s n hn) (hmem_s m hm)]
  have h2 : ∑ p ∈ s.product s, c p.1 * c p.2 * FF u (p.1*p.2)
      = ∑ k ∈ t, (∑ p ∈ s.product s, (if p.1*p.2 = k then c p.1*c p.2 else 0)) * FF u k := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s.product s) (t := t) (g := fun p : ℕ×ℕ => p.1*p.2) hprod (fun p : ℕ×ℕ => c p.1 * c p.2 * FF u (p.1*p.2))]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    by_cases h : p.1*p.2 = k
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h]; ring
  rw [h1, h2]
  simp only [FF, reprCoeff, hs]

private noncomputable def blockCoeff1 (N : ℕ) (c : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k ∈ Finset.Icc (N*N) (2*(N*N)) then reprCoeff N c k else 0

private noncomputable def blockCoeff2 (N : ℕ) (c : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k ∈ Finset.Icc (2*(N*N)+1) (4*(N*N)) then reprCoeff N c k else 0

private lemma sum_Icc_split {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) (f : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc A C, f k = ∑ k ∈ Finset.Icc A B, f k + ∑ k ∈ Finset.Icc (B+1) C, f k := by
  have h1 : Finset.Icc A C = Finset.Ico A (C+1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have h2 : Finset.Icc A B = Finset.Ico A (B+1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have h3 : Finset.Icc (B+1) C = Finset.Ico (B+1) (C+1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h1, h2, h3]
  exact (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm

private lemma sum_Icc_of_eq_zero {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) (f : ℕ → ℂ)
    (hf : ∀ k, B < k → f k = 0) :
    ∑ k ∈ Finset.Icc A C, f k = ∑ k ∈ Finset.Icc A B, f k := by
  rw [sum_Icc_split hAB hBC f]
  have h0 : ∑ k ∈ Finset.Icc (B+1) C, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact hf k (by omega)
  rw [h0, add_zero]

private lemma sq_split (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ) (u : ℝ) :
    (∑ n ∈ Finset.Icc N (2*N), c n * (n:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (n:ℝ):ℂ))^2
    = (∑ k ∈ Finset.Icc (N*N) (2*(N*N)), blockCoeff1 N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ)))
    + (∑ k ∈ Finset.Icc (2*(N*N)+1) (2*(2*(N*N)+1)), blockCoeff2 N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ))) := by
  have hNN : 1 ≤ N*N := by
    have h1 : 0 < N := by omega
    have h2 : 0 < N*N := Nat.mul_pos h1 h1
    omega
  rw [sq_expansion N hN c u]
  have hsplit := sum_Icc_split (A:=N*N) (B:=2*(N*N)) (C:=4*(N*N))
      (by omega) (by omega)
      (fun k => reprCoeff N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ)))
  rw [hsplit]
  congr 1
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [blockCoeff1, hk, if_true]
  · have h1 : (∑ k ∈ Finset.Icc (2*(N*N)+1) (4*(N*N)),
          reprCoeff N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ)))
        = ∑ k ∈ Finset.Icc (2*(N*N)+1) (4*(N*N)),
          blockCoeff2 N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ)) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [blockCoeff2, hk, if_true]
    rw [h1]
    exact (sum_Icc_of_eq_zero (A:=2*(N*N)+1) (B:=4*(N*N)) (C:=2*(2*(N*N)+1))
        (by omega) (by omega)
        (fun k => blockCoeff2 N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ))) (by
          intro k hk
          have hk' : k ∉ Finset.Icc (2*(N*N)+1) (4*(N*N)) := by
            rw [Finset.mem_Icc]; omega
          simp only [blockCoeff2, hk', if_false, zero_mul])).symm

private lemma card_filter_repr_le (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ) :
    ((s.product s).filter (fun p : ℕ×ℕ => p.1 * p.2 = k)).card ≤ k.divisors.card := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : ((s.product s).filter (fun p : ℕ×ℕ => p.1 * p.2 = 0)).card = 0 := by
      rw [Finset.card_filter_eq_zero_iff]
      intro p hp hcon
      have h1 : 1 ≤ p.1 := hs p.1 (Finset.mem_product.mp hp).1
      have h2 : 1 ≤ p.2 := hs p.2 (Finset.mem_product.mp hp).2
      have : 0 < p.1 * p.2 := Nat.mul_pos (by omega) (by omega)
      omega
    rw [h0]; exact Nat.zero_le _
  · have hinj : Set.InjOn (fun p : ℕ×ℕ => p.1) ↑((s.product s).filter (fun p : ℕ×ℕ => p.1 * p.2 = k)) := by
      intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      obtain ⟨hpp, heqp⟩ := hp
      obtain ⟨hqp, heqq⟩ := hq
      change p.1 = q.1 at hpq
      have hp1 : 1 ≤ p.1 := hs p.1 (Finset.mem_product.mp hpp).1
      have h2 : p.2 = q.2 := by
        have hmul : p.1 * p.2 = p.1 * q.2 := by rw [heqp, hpq, heqq]
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p.1) hmul
      ext <;> simp [hpq, h2]
    have himg : ((s.product s).filter (fun p : ℕ×ℕ => p.1 * p.2 = k)).image (fun p => p.1) ⊆ k.divisors := by
      intro d hd
      rw [Finset.mem_image] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_divisors]
      exact ⟨⟨p.2, hp.2.symm⟩, hk.ne'⟩
    calc ((s.product s).filter (fun p : ℕ×ℕ => p.1 * p.2 = k)).card
        = (((s.product s).filter (fun p : ℕ×ℕ => p.1 * p.2 = k)).image (fun p => p.1)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ k.divisors.card := Finset.card_le_card himg

private lemma cs_double {R : ℕ} (f g : Fin R → Fin R → ℝ) :
    (∑ i, ∑ j, f i j * g i j)^2 ≤ (∑ i, ∑ j, (f i j)^2) * (∑ i, ∑ j, (g i j)^2) := by
  rw [← Fintype.sum_prod_type (f := fun p : Fin R × Fin R => f p.1 p.2 * g p.1 p.2),
      ← Fintype.sum_prod_type (f := fun p : Fin R × Fin R => (f p.1 p.2)^2),
      ← Fintype.sum_prod_type (f := fun p : Fin R × Fin R => (g p.1 p.2)^2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

-- main theorem
theorem dirichlet_poly_square_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N M : ℕ), 1 ≤ N → 8 * N ^ 2 ≤ M → ∀ (Δ : ℝ), 1 ≤ Δ → ∀ (B : ℝ), 1 ≤ B →
    ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
    (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0)) ^ 2
    ≤ C * B ^ 4 * (M : ℝ) ^ ε *
      (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1 : ℝ) else 0)) *
      (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc M (2 * M),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) := by
  intro ε hε
  set η : ℝ := ε / 3 with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηle : η ≤ ε := by rw [hηdef]; linarith
  have h3η : 3 * η = ε := by rw [hηdef]; ring
  obtain ⟨CI, hCIpos, hINCR⟩ := dirichlet_poly_increase_length η hη
  obtain ⟨Cd, hCdpos, hCd⟩ := Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow η hη
  refine ⟨8 * CI * (1 + Cd ^ 2), by positivity, ?_⟩
  intro N M hN hM Δ hΔ B hB c hc R t ht
  have hNpos : 0 < N := by omega
  have hNsq : 1 ≤ N^2 := by have := pow_pos hNpos 2; omega
  have hM1 : 1 ≤ M := le_trans (le_trans hNsq (Nat.le_mul_of_pos_left (N^2) (by norm_num))) hM
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
  have hM1R : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hBnn : (0:ℝ) ≤ B := by linarith
  have hNN : 1 ≤ N*N := by
    have h1 : 0 < N*N := Nat.mul_pos hNpos hNpos
    omega
  have h8 : (8:ℕ) * N^2 = 8*(N*N) := by ring
  have h2L1 : 2*(N*N) ≤ M := by
    have h48 : 2*(N*N) ≤ 8*(N*N) := Nat.mul_le_mul_right (N*N) (by norm_num)
    have h8M : 8*(N*N) ≤ M := by have h := hM; rw [h8] at h; exact h
    exact le_trans h48 h8M
  have h2L2 : 2*(2*(N*N)+1) ≤ M := by
    have h48 : 2*(2*(N*N)+1) ≤ 8*(N*N) := by omega
    have h8M : 8*(N*N) ≤ M := by have h := hM; rw [h8] at h; exact h
    exact le_trans h48 h8M
  set β : ℝ := max 1 (B^2 * Cd * (M:ℝ)^η) with hβ
  have hβ1 : 1 ≤ β := le_max_left _ _
  have hβnn : 0 ≤ β := le_trans zero_le_one hβ1
  have hβge : B^2 * Cd * (M:ℝ)^η ≤ β := le_max_right _ _
  have hsNpos : ∀ n ∈ Finset.Icc N (2*N), 1 ≤ n := by
    intro n hn; rw [Finset.mem_Icc] at hn; omega
  have hcardk : ∀ k, (((Finset.Icc N (2*N)).product (Finset.Icc N (2*N))).filter (fun p : ℕ×ℕ => p.1*p.2 = k)).card ≤ k.divisors.card :=
    fun k => card_filter_repr_le _ hsNpos k
  have hcardR : ∀ k, 1 ≤ k → ((((Finset.Icc N (2*N)).product (Finset.Icc N (2*N))).filter (fun p : ℕ×ℕ => p.1*p.2 = k)).card : ℝ) ≤ Cd * (k:ℝ)^η := by
    intro k hk1
    have h1 : ((((Finset.Icc N (2*N)).product (Finset.Icc N (2*N))).filter (fun p : ℕ×ℕ => p.1*p.2 = k)).card : ℝ) ≤ ((k.divisors.card : ℕ):ℝ) := by
      exact_mod_cast hcardk k
    exact le_trans h1 (hCd k hk1)
  have hDk : ∀ k, ‖reprCoeff N c k‖ ≤ β := by
    intro k
    by_cases hk : k ∈ Finset.Icc (N*N) (4*(N*N))
    · have hkge : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
      have hkle : k ≤ M := by
        have hk4 : k ≤ 4*(N*N) := (Finset.mem_Icc.mp hk).2
        have h48 : 4*(N*N) ≤ 8*(N*N) := Nat.mul_le_mul_right (N*N) (by norm_num)
        have h8M : 8*(N*N) ≤ M := by have h := hM; rw [h8] at h; exact h
        exact le_trans hk4 (le_trans h48 h8M)
      have hnorm : ‖reprCoeff N c k‖ ≤ B^2 * ((((Finset.Icc N (2*N)).product (Finset.Icc N (2*N))).filter (fun p : ℕ×ℕ => p.1*p.2 = k)).card : ℝ) := by
        unfold reprCoeff
        calc ‖∑ p ∈ (Finset.Icc N (2*N)).product (Finset.Icc N (2*N)), (if p.1*p.2 = k then c p.1*c p.2 else 0)‖
            ≤ ∑ p ∈ (Finset.Icc N (2*N)).product (Finset.Icc N (2*N)), ‖(if p.1*p.2 = k then c p.1*c p.2 else 0)‖ := norm_sum_le _ _
          _ ≤ ∑ p ∈ (Finset.Icc N (2*N)).product (Finset.Icc N (2*N)), (if p.1*p.2 = k then B^2 else 0) := by
              apply Finset.sum_le_sum
              intro p hp
              by_cases h : p.1*p.2 = k
              · rw [if_pos h, if_pos h, norm_mul]
                nlinarith [hc p.1, hc p.2, norm_nonneg (c p.1), norm_nonneg (c p.2)]
              · rw [if_neg h, if_neg h, norm_zero]
          _ = B^2 * ((((Finset.Icc N (2*N)).product (Finset.Icc N (2*N))).filter (fun p : ℕ×ℕ => p.1*p.2 = k)).card : ℝ) := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
      have hketa : (k:ℝ)^η ≤ (M:ℝ)^η := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkle) (le_of_lt hη)
      calc ‖reprCoeff N c k‖ ≤ B^2 * ((((Finset.Icc N (2*N)).product (Finset.Icc N (2*N))).filter (fun p : ℕ×ℕ => p.1*p.2 = k)).card : ℝ) := hnorm
        _ ≤ B^2 * (Cd * (k:ℝ)^η) := by
            apply mul_le_mul_of_nonneg_left (hcardR k hkge) (by positivity)
        _ ≤ B^2 * (Cd * (M:ℝ)^η) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hketa (le_of_lt hCdpos)
        _ = B^2 * Cd * (M:ℝ)^η := by ring
        _ ≤ β := hβge
    · have hzero : reprCoeff N c k = 0 := by
        unfold reprCoeff
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have h1 : N*N ≤ p.1*p.2 := Nat.mul_le_mul (Finset.mem_Icc.mp hp'.1).1 (Finset.mem_Icc.mp hp'.2).1
        have h2 : p.1*p.2 ≤ 4*(N*N) := by
          calc p.1*p.2 ≤ (2*N)*(2*N) := Nat.mul_le_mul (Finset.mem_Icc.mp hp'.1).2 (Finset.mem_Icc.mp hp'.2).2
            _ = 4*(N*N) := by ring
        have hmem : p.1*p.2 ∈ Finset.Icc (N*N) (4*(N*N)) := Finset.mem_Icc.mpr ⟨h1,h2⟩
        rw [if_neg (fun h => hk (by rw [← h]; exact hmem))]
      rw [hzero, norm_zero]; exact hβnn
  have hb1 : ∀ k, ‖blockCoeff1 N c k‖ ≤ β := by
    intro k
    by_cases hk : k ∈ Finset.Icc (N*N) (2*(N*N))
    · simp only [blockCoeff1, hk, if_true]; exact hDk k
    · simp only [blockCoeff1, hk, if_false, norm_zero]; exact hβnn
  have hb2 : ∀ k, ‖blockCoeff2 N c k‖ ≤ β := by
    intro k
    by_cases hk : k ∈ Finset.Icc (2*(N*N)+1) (4*(N*N))
    · simp only [blockCoeff2, hk, if_true]; exact hDk k
    · simp only [blockCoeff2, hk, if_false, norm_zero]; exact hβnn
  set S : ℝ → ℂ := fun u => ∑ n ∈ Finset.Icc N (2*N), c n * (n:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (n:ℝ):ℂ) with hS
  set P1 : ℝ → ℂ := fun u => ∑ k ∈ Finset.Icc (N*N) (2*(N*N)), blockCoeff1 N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ)) with hP1
  set P2 : ℝ → ℂ := fun u => ∑ k ∈ Finset.Icc (2*(N*N)+1) (2*(2*(N*N)+1)), blockCoeff2 N c k * ((k:ℂ)^(Complex.I*(u:ℂ))/(Real.sqrt (k:ℝ):ℂ)) with hP2
  set bT : ℝ := ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖∑ n ∈ Finset.Icc M (2*M), (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))/(Real.sqrt (n:ℝ):ℂ)‖^2 else 0) with hbT
  set bK : ℝ := ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1:ℝ) else 0) with hbK
  have hsplitS : ∀ u : ℝ, (S u)^2 = P1 u + P2 u := by
    intro u; rw [hS, hP1, hP2]; exact sq_split N hN c u
  have hTnn : 0 ≤ bT := by rw [hbT]; positivity
  have hKnn : 0 ≤ bK := by rw [hbK]; positivity
  have hIN1 : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖P1 (t i - t j)‖^2 else 0)) ≤ CI*β^2*(M:ℝ)^η*bT := by
    have h := hINCR (N*N) M hNN h2L1 Δ hΔ β hβ1 (blockCoeff1 N c) hb1 R t ht
    simpa only [hP1, hbT, mul_div_assoc] using h
  have hIN2 : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖P2 (t i - t j)‖^2 else 0)) ≤ CI*β^2*(M:ℝ)^η*bT := by
    have h := hINCR (2*(N*N)+1) M (by omega) h2L2 Δ hΔ β hβ1 (blockCoeff2 N c) hb2 R t ht
    simpa only [hP2, hbT, mul_div_assoc] using h
  have hterm : ∀ i j : Fin R, (if |t i - t j| ≤ Δ then ‖(S (t i - t j))^2‖^2 else 0)
      ≤ (if |t i - t j| ≤ Δ then (2*‖P1 (t i - t j)‖^2 + 2*‖P2 (t i - t j)‖^2) else 0) := by
    intro i j
    by_cases hc2 : |t i - t j| ≤ Δ
    · rw [if_pos hc2, if_pos hc2, hsplitS (t i - t j)]
      have h1 : ‖P1 (t i - t j) + P2 (t i - t j)‖ ≤ ‖P1 (t i - t j)‖ + ‖P2 (t i - t j)‖ := norm_add_le _ _
      have h2 : ‖P1 (t i - t j)‖ * ‖P2 (t i - t j)‖ ≤ ‖P1 (t i - t j)‖^2 + ‖P2 (t i - t j)‖^2 := by
        nlinarith [sq_nonneg (‖P1 (t i - t j)‖ - ‖P2 (t i - t j)‖)]
      have h3 : ‖P1 (t i - t j) + P2 (t i - t j)‖^2 ≤ (‖P1 (t i - t j)‖ + ‖P2 (t i - t j)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h4 : (‖P1 (t i - t j)‖ + ‖P2 (t i - t j)‖)^2 ≤ 2*‖P1 (t i - t j)‖^2 + 2*‖P2 (t i - t j)‖^2 := by
        nlinarith [sq_nonneg (‖P1 (t i - t j)‖ - ‖P2 (t i - t j)‖)]
      linarith [h3, h4]
    · rw [if_neg hc2, if_neg hc2]
  have hZbound : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖(S (t i - t j))^2‖^2 else 0))
      ≤ 4*CI*β^2*(M:ℝ)^η*bT := by
    calc (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖(S (t i - t j))^2‖^2 else 0))
        ≤ ∑ i, ∑ j, (if |t i - t j| ≤ Δ then (2*‖P1 (t i - t j)‖^2 + 2*‖P2 (t i - t j)‖^2) else 0) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          exact hterm i j
      _ = 2 * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖P1 (t i - t j)‖^2 else 0))
            + 2 * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖P2 (t i - t j)‖^2 else 0)) := by
          simp only [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro j _
          by_cases h : |t i - t j| ≤ Δ <;> simp [h]
      _ ≤ 2 * (CI*β^2*(M:ℝ)^η*bT) + 2 * (CI*β^2*(M:ℝ)^η*bT) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hIN1 (by norm_num)
          · exact mul_le_mul_of_nonneg_left hIN2 (by norm_num)
      _ = 4*CI*β^2*(M:ℝ)^η*bT := by ring
  have hCS : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖S (t i - t j)‖^2 else 0))^2
      ≤ bK * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖(S (t i - t j))^2‖^2 else 0)) := by
    have h := cs_double (R:=R)
      (fun i j => if |t i - t j| ≤ Δ then ‖S (t i - t j)‖^2 else 0)
      (fun i j => if |t i - t j| ≤ Δ then (1:ℝ) else 0)
    have hXY : (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖S (t i - t j)‖^2 else 0))
        = ∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖S (t i - t j)‖^2 else 0) *
            (if |t i - t j| ≤ Δ then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      by_cases h : |t i - t j| ≤ Δ <;> simp [h]
    have hX2 : (∑ i, ∑ j, ((if |t i - t j| ≤ Δ then ‖S (t i - t j)‖^2 else 0))^2)
        = ∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖(S (t i - t j))^2‖^2 else 0) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      by_cases h : |t i - t j| ≤ Δ
      · rw [if_pos h, if_pos h]
        rw [show ‖(S (t i - t j))^2‖ = ‖S (t i - t j)‖^2 by rw [pow_two, norm_mul, sq]]
      · rw [if_neg h, if_neg h]; ring
    have hY2 : (∑ i, ∑ j, ((if |t i - t j| ≤ Δ then (1:ℝ) else 0))^2) = bK := by
      rw [hbK]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      by_cases h : |t i - t j| ≤ Δ <;> simp [h]
    rw [hXY]
    refine le_trans h ?_
    rw [hX2, hY2]
    exact le_of_eq (mul_comm _ _)
  have hβbound : 4*CI*β^2*(M:ℝ)^η ≤ 8*CI*(1+Cd^2)*B^4*(M:ℝ)^ε := by
    set x : ℝ := B^2 * Cd * (M:ℝ)^η with hx
    have hxnn : 0 ≤ x := by rw [hx]; positivity
    have hβle : β ≤ 1 + x := by rw [hβ, hx]; exact max_le (by linarith) (by linarith)
    have hβle2 : β^2 ≤ 2*(1+x^2) := by
      have h1 : β^2 ≤ (1+x)^2 := pow_le_pow_left₀ hβnn hβle 2
      nlinarith [h1, sq_nonneg (x-1)]
    have hx2 : x^2 * (M:ℝ)^η = B^4*Cd^2*(M:ℝ)^ε := by
      rw [hx]
      have hadd : (M:ℝ)^η*(M:ℝ)^η*(M:ℝ)^η = (M:ℝ)^(3*η) := by
        rw [← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
        congr 1; ring
      calc (B^2*Cd*(M:ℝ)^η)^2 * (M:ℝ)^η
          = B^4*Cd^2*((M:ℝ)^η*(M:ℝ)^η*(M:ℝ)^η) := by ring
        _ = B^4*Cd^2*((M:ℝ)^(3*η)) := by rw [hadd]
        _ = B^4*Cd^2*(M:ℝ)^ε := by rw [h3η]
    have heta : (M:ℝ)^η ≤ B^4*(M:ℝ)^ε := by
      have h1 : (M:ℝ)^η ≤ (M:ℝ)^ε := Real.rpow_le_rpow_of_exponent_le hM1R hηle
      have h2 : (1:ℝ) ≤ B^4 := one_le_pow₀ hB
      calc (M:ℝ)^η ≤ (M:ℝ)^ε := h1
        _ = 1*(M:ℝ)^ε := by ring
        _ ≤ B^4*(M:ℝ)^ε := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hMpos.le ε)
    calc 4*CI*β^2*(M:ℝ)^η ≤ 4*CI*(2*(1+x^2))*(M:ℝ)^η := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hβle2 (by positivity)
      _ = 8*CI*(M:ℝ)^η + 8*CI*(B^4*Cd^2*(M:ℝ)^ε) := by
          rw [show 4*CI*(2*(1+x^2))*(M:ℝ)^η = 8*CI*(1+x^2)*(M:ℝ)^η by ring]
          rw [show 8*CI*(1+x^2)*(M:ℝ)^η = 8*CI*(M:ℝ)^η + 8*CI*(x^2*(M:ℝ)^η) by ring]
          rw [hx2]
      _ ≤ 8*CI*(B^4*(M:ℝ)^ε) + 8*CI*(B^4*Cd^2*(M:ℝ)^ε) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left heta (by positivity)
          · exact le_refl _
      _ = 8*CI*(1+Cd^2)*B^4*(M:ℝ)^ε := by ring
  calc (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖S (t i - t j)‖^2 else 0))^2
      ≤ bK * (∑ i, ∑ j, (if |t i - t j| ≤ Δ then ‖(S (t i - t j))^2‖^2 else 0)) := hCS
    _ ≤ bK * (4*CI*β^2*(M:ℝ)^η*bT) := mul_le_mul_of_nonneg_left hZbound hKnn
    _ ≤ bK * (8*CI*(1+Cd^2)*B^4*(M:ℝ)^ε*bT) := by
        apply mul_le_mul_of_nonneg_left _ hKnn
        exact mul_le_mul_of_nonneg_right hβbound hTnn
    _ = 8 * CI * (1 + Cd ^ 2) * B ^ 4 * (M : ℝ) ^ ε * bK * bT := by ring

end Commons.NumberTheory.DirichletPolynomial
