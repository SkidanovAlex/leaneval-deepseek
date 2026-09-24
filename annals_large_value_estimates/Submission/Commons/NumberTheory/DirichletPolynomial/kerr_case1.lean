import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_square_bound
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length

namespace Commons.NumberTheory.DirichletPolynomial

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

private lemma norm_poly_sq_le (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) :
    ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2 ≤ 4 * (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos_of_pos hNpos
  have hs : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hterm : ∀ n ∈ Finset.Icc N (2 * N),
      ‖(n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ = 1 / Real.sqrt (n : ℝ) := by
    intro n hn
    have hn1 : (1 : ℕ) ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnorm1 : ‖(n : ℂ) ^ (Complex.I * (θ : ℂ))‖ = 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp
    have hnorm2 : ‖((Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ = Real.sqrt (n : ℝ) := by
      rw [show ‖((Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ = |Real.sqrt (n : ℝ)| from RCLike.norm_ofReal _,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [norm_div, hnorm1, hnorm2, one_div]
  have hsum : ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc N (2 * N), 1 / Real.sqrt (n : ℝ) := by
    calc ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Finset.Icc N (2 * N),
            ‖(n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc N (2 * N), 1 / Real.sqrt (n : ℝ) :=
          Finset.sum_congr rfl hterm
  have hstep : ∑ n ∈ Finset.Icc N (2 * N), 1 / Real.sqrt (n : ℝ)
      ≤ ∑ _n ∈ Finset.Icc N (2 * N), 1 / Real.sqrt (N : ℝ) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    refine one_div_le_one_div_of_le hsqrtN ?_
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  have hcard : (∑ _n ∈ Finset.Icc N (2 * N), (1 : ℝ) / Real.sqrt (N : ℝ))
      = ((N : ℝ) + 1) / Real.sqrt (N : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc]
    have h : 2 * N + 1 - N = N + 1 := by omega
    rw [h]
    simp [nsmul_eq_mul]
    ring
  have hfinal : ((N : ℝ) + 1) / Real.sqrt (N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    rw [div_le_iff₀ hsqrtN]
    have hss : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by rw [← sq]; exact hs
    rw [mul_assoc, hss]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hbd : ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * (θ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ≤ 2 * Real.sqrt (N : ℝ) := by
    calc _ ≤ ∑ n ∈ Finset.Icc N (2 * N), 1 / Real.sqrt (n : ℝ) := hsum
      _ ≤ ∑ _n ∈ Finset.Icc N (2 * N), 1 / Real.sqrt (N : ℝ) := hstep
      _ = ((N : ℝ) + 1) / Real.sqrt (N : ℝ) := hcard
      _ ≤ 2 * Real.sqrt (N : ℝ) := hfinal
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbd 2
  have h2 : (2 * Real.sqrt (N : ℝ)) ^ 2 = 4 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hNpos.le]; norm_num
  rwa [h2] at hsq

private lemma window_le {R : ℕ} (T : ℝ) (t : Fin R → ℝ) (htIcc : ∀ i, t i ∈ Set.Icc 0 T)
    (i j : Fin R) : |t i - t j| ≤ T := by
  have hi := Set.mem_Icc.mp (htIcc i)
  have hj := Set.mem_Icc.mp (htIcc j)
  rw [abs_le]
  exact ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩

private lemma sum_window_eq {R : ℕ} (T : ℝ) (t : Fin R → ℝ) (htIcc : ∀ i, t i ∈ Set.Icc 0 T)
    (f : Fin R → Fin R → ℝ) :
    (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ T then f i j else 0))
      = ∑ i : Fin R, ∑ j : Fin R, f i j := by
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [if_pos (window_le T t htIcc i j)]

private lemma sum_window_one {R : ℕ} (T : ℝ) (t : Fin R → ℝ) (htIcc : ∀ i, t i ∈ Set.Icc 0 T) :
    (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ T then (1 : ℝ) else 0)) = (R : ℝ) ^ 2 := by
  rw [sum_window_eq T t htIcc (fun _ _ => (1 : ℝ))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma quad_le {X α β : ℝ} (hX : 0 ≤ X) (_hβ : 0 ≤ β)
    (h : X ≤ α * Real.sqrt X + β) : X ≤ 2 * α ^ 2 + 2 * β := by
  have hs : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
  have h0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  nlinarith [h, hs, sq_nonneg (Real.sqrt X - α), sq_nonneg α, sq_nonneg β]

set_option maxHeartbeats 2000000 in
theorem kerr_case1
    (hRef : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ → ∀ (B : ℝ), 1 ≤ B →
      ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      ≤ C * B ^ 2 * Δ ^ ε *
        ((∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ Δ then
            ‖∑ n ∈ Finset.Icc (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)),
              (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
           else 0))
        + (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1 : ℝ) else 0))
        + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 1 ≤ T → (N : ℝ) ≤ T → (N : ℝ) ^ 3 ≥ 256 * T ^ 2 →
      ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i, t i ∈ Set.Icc 0 T) →
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i : Fin R, ∑ j : Fin R,
        ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2)
      ≤ C * T ^ ε * ((R : ℝ) ^ 2 + (N : ℝ) * (R : ℝ)) := by
  intro ε hε
  set e : ℝ := ε / 3 with hedef
  have hepos : 0 < e := by rw [hedef]; positivity
  have hele : e ≤ ε := by rw [hedef]; linarith
  have h3e : 3 * e = ε := by rw [hedef]; ring
  have h2ele : 2 * e ≤ ε := by rw [hedef]; linarith
  obtain ⟨C0, hC0, hREF⟩ := hRef e hepos
  obtain ⟨Cq, hCq, hSQ⟩ := dirichlet_poly_square_bound e hepos
  refine ⟨max (max (2 * C0 ^ 2 * Cq + 6 * C0) 400) 1, ?_, ?_⟩
  · positivity
  intro N hN T hT hNT hbig R t htIcc htsep
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  set Sg : ℝ := (∑ i : Fin R, ∑ j : Fin R,
      ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2) with hSg
  set K : ℝ := (R : ℝ) ^ 2 + (N : ℝ) * (R : ℝ) with hK
  have hSgnn : 0 ≤ Sg := by
    rw [hSg]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hTe1 : (1 : ℝ) ≤ T ^ ε := Real.one_le_rpow hT hε.le
  rcases Nat.eq_zero_or_pos R with hRz | hRpos
  · subst hRz
    have : Sg = 0 := by rw [hSg]; simp
    rw [this, hK]
    norm_num
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRpos
  by_cases hsmall : N ≤ 99
  · -- trivial regime
    have hN99 : (N : ℝ) ≤ 99 := by exact_mod_cast hsmall
    have hpt : ∀ i j : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N),
        (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
        ≤ 4 * (N : ℝ) := fun i j => norm_poly_sq_le N hN _
    have hSgle : Sg ≤ 4 * (N : ℝ) * (R : ℝ) ^ 2 := by
      rw [hSg]
      calc (∑ i : Fin R, ∑ j : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2)
          ≤ ∑ i : Fin R, ∑ j : Fin R, 4 * (N : ℝ) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
        _ = 4 * (N : ℝ) * (R : ℝ) ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have h4N : 4 * (N : ℝ) * (R : ℝ) ^ 2 ≤ 400 * K := by
      rw [hK]
      nlinarith [hR0, hN0, hN99, sq_nonneg ((R : ℝ) - 1), mul_nonneg hN0 hR0]
    have h400Cle : (400 : ℝ) ≤ max (max (2 * C0 ^ 2 * Cq + 6 * C0) 400) 1 := by
      exact le_trans (le_max_right _ 400) (le_max_left _ 1)
    calc Sg ≤ 4 * (N : ℝ) * (R : ℝ) ^ 2 := hSgle
      _ ≤ 400 * K := h4N
      _ ≤ 400 * T ^ ε * K := by
          have h : (400 : ℝ) * K * 1 ≤ 400 * K * T ^ ε :=
            mul_le_mul_of_nonneg_left hTe1 (by positivity)
          nlinarith [h]
      _ ≤ max (max (2 * C0 ^ 2 * Cq + 6 * C0) 400) 1 * T ^ ε * K := by
          have hTepos : (0 : ℝ) ≤ T ^ ε := le_trans (by norm_num) hTe1
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h400Cle hTepos) hKnn
  have hN100 : 100 ≤ N := by omega
  -- ============ main case ============
  set A : ℕ := Nat.ceil (4 * T / (N : ℝ)) with hAdef
  set S1 : ℝ := (∑ i : Fin R, ∑ j : Fin R,
      ‖∑ n ∈ Finset.Icc A (2 * A),
        (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2) with hS1
  have hA1 : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ (A : ℝ) := by
      have h2 : (1 : ℝ) ≤ 4 * T / (N : ℝ) := by
        rw [le_div_iff₀ hNpos]; linarith
      calc (1 : ℝ) ≤ 4 * T / (N : ℝ) := h2
        _ ≤ (Nat.ceil (4 * T / (N : ℝ)) : ℝ) := Nat.le_ceil _
        _ = (A : ℝ) := by rw [hAdef]
    exact_mod_cast h1
  have hx0 : (0 : ℝ) ≤ 4 * T / (N : ℝ) := by positivity
  have hxle : 4 * T / (N : ℝ) ≤ Real.sqrt (N : ℝ) / 4 := by
    have hsq : (4 * T / (N : ℝ)) ^ 2 ≤ (Real.sqrt (N : ℝ) / 4) ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt hN0]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 2) (by norm_num : (0 : ℝ) < 4 ^ 2)]
      nlinarith [hbig]
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hx0, abs_of_nonneg (by positivity)] at h
  have hAle : (A : ℝ) ≤ Real.sqrt (N : ℝ) / 4 + 1 := by
    have h := Nat.ceil_lt_add_one hx0
    rw [hAdef]
    linarith
  have h8A2 : 8 * A ^ 2 ≤ N := by
    have hN100' : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN100
    have hsqrt10 : 10 ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      linarith [hN100']
    have hsN : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN0
    have hsqA : (A : ℝ) ^ 2 ≤ (Real.sqrt (N : ℝ) / 4 + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hAle 2
    have hreal : (8 * A ^ 2 : ℕ) ≤ N := by
      have : ((8 * A ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        nlinarith [hsqA, hsqrt10, hsN, Real.sqrt_nonneg (N : ℝ)]
      exact_mod_cast this
    exact hreal
  -- REF application
  have href := hREF N hN T hT hNT 1 (le_refl 1) (fun _ => (1 : ℂ)) (fun n => by simp) R t htsep
  have hSL : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ T then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (1 : ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) = Sg := by
    rw [sum_window_eq T t htIcc (fun i j => ‖∑ n ∈ Finset.Icc N (2 * N),
            (1 : ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2)]
    simp only [one_mul]
    rw [hSg]
  have hSR : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ T then
          ‖∑ n ∈ Finset.Icc (Nat.ceil (4 * T / (N : ℝ))) (2 * Nat.ceil (4 * T / (N : ℝ))),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) = S1 := by
    rw [sum_window_eq T t htIcc (fun i j => ‖∑ n ∈ Finset.Icc (Nat.ceil (4 * T / (N : ℝ)))
            (2 * Nat.ceil (4 * T / (N : ℝ))),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2)]
  have hPC : (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ T then (1 : ℝ) else 0))
      = (R : ℝ) ^ 2 := sum_window_one T t htIcc
  have hrefS : Sg ≤ C0 * T ^ e * (S1 + (R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)) := by
    rw [← hSL, ← hSR, ← hPC]
    simpa [one_pow, one_mul] using href
  -- SQ application
  have hsq := hSQ A N hA1 h8A2 T hT 1 (le_refl 1) (fun _ => (1 : ℂ)) (fun n => by simp) R t htsep
  have hsqS : S1 ^ 2 ≤ Cq * (N : ℝ) ^ e * (R : ℝ) ^ 2 * Sg := by
    rw [← hSR, ← hPC, ← hSL]
    simpa [one_pow, one_mul, mul_assoc] using hsq
  -- quadratic
  have hCqNe_nn : 0 ≤ Cq * (N : ℝ) ^ e := by positivity
  have hS1nn : 0 ≤ S1 := by rw [hS1]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
  have hsqrtS1 : S1 ≤ Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ) * Real.sqrt Sg := by
    have h1 : S1 ≤ Real.sqrt (Cq * (N : ℝ) ^ e * (R : ℝ) ^ 2 * Sg) := by
      have h := Real.sqrt_le_sqrt hsqS
      rwa [Real.sqrt_sq hS1nn] at h
    calc S1 ≤ Real.sqrt (Cq * (N : ℝ) ^ e * (R : ℝ) ^ 2 * Sg) := h1
      _ = Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ) * Real.sqrt Sg := by
          rw [show Cq * (N : ℝ) ^ e * (R : ℝ) ^ 2 * Sg
              = (Cq * (N : ℝ) ^ e) * ((R : ℝ) ^ 2 * Sg) by ring]
          rw [Real.sqrt_mul hCqNe_nn, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (R : ℝ) ^ 2),
            Real.sqrt_sq hR0]
          ring
  have hquad : Sg ≤ (C0 * T ^ e * (Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ))) * Real.sqrt Sg
      + C0 * T ^ e * ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)) := by
    have hstep : S1 + ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1))
        ≤ (Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ)) * Real.sqrt Sg
          + ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)) := by
      linarith [hsqrtS1]
    calc Sg ≤ C0 * T ^ e * (S1 + (R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)) := hrefS
      _ = C0 * T ^ e * (S1 + ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1))) := by ring
      _ ≤ C0 * T ^ e * ((Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ)) * Real.sqrt Sg
            + ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (C0 * T ^ e * (Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ))) * Real.sqrt Sg
            + C0 * T ^ e * ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)) := by ring
  have hβnn : 0 ≤ C0 * T ^ e * ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)) := by positivity
  have hfinal := quad_le hSgnn hβnn hquad
  -- powers
  have hNeTe : (N : ℝ) ^ e ≤ T ^ e := Real.rpow_le_rpow hN0 hNT hepos.le
  have hpow : T ^ (2 * e) * (N : ℝ) ^ e ≤ T ^ ε := by
    have h2 : T ^ (2 * e) * (N : ℝ) ^ e ≤ T ^ (2 * e) * T ^ e :=
      mul_le_mul_of_nonneg_left hNeTe (Real.rpow_nonneg hT0 _)
    have h3 : T ^ (2 * e) * T ^ e = T ^ (3 * e) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < T)]
      congr 1; ring
    rw [h3, h3e] at h2
    exact h2
  have hTe_le : T ^ e ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT hele
  have hT2e_le : T ^ (2 * e) ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT h2ele
  -- first term
  have hTe2 : (T ^ e) ^ 2 = T ^ (2 * e) := by
    rw [pow_two, ← Real.rpow_add (by linarith : (0:ℝ) < T)]
    congr 1; ring
  have hXX : (C0 * T ^ e * (Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ))) ^ 2
      = C0 ^ 2 * T ^ (2 * e) * (Cq * (N : ℝ) ^ e) * (R : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hCqNe_nn, hTe2]
    ring
  have hterm1 : 2 * (C0 * T ^ e * (Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ))) ^ 2
      ≤ 2 * C0 ^ 2 * Cq * T ^ ε * (R : ℝ) ^ 2 := by
    rw [hXX]
    calc 2 * (C0 ^ 2 * T ^ (2 * e) * (Cq * (N : ℝ) ^ e) * (R : ℝ) ^ 2)
        = (2 * C0 ^ 2 * Cq * (R : ℝ) ^ 2) * (T ^ (2 * e) * (N : ℝ) ^ e) := by ring
      _ ≤ (2 * C0 ^ 2 * Cq * (R : ℝ) ^ 2) * T ^ ε :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 * C0 ^ 2 * Cq * T ^ ε * (R : ℝ) ^ 2 := by ring
  -- second term
  have hN1e : (N : ℝ) ^ (1 + e) = (N : ℝ) * (N : ℝ) ^ e := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  have hterm2 : 2 * (C0 * T ^ e * ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)))
      ≤ 6 * C0 * T ^ ε * K := by
    have hR1' : ((R : ℝ) + 1) ≤ 2 * (R : ℝ) := by linarith
    have hN1e' : (N : ℝ) ^ (1 + e) ≤ (N : ℝ) * T ^ e := by
      rw [hN1e]; exact mul_le_mul_of_nonneg_left hNeTe hN0
    rw [hK]
    -- 2*C0*T^e*(R² + N^{1+e}(R+1))
    have hsplit : 2 * (C0 * T ^ e * ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)))
        = 2 * C0 * T ^ e * (R : ℝ) ^ 2 + 2 * C0 * T ^ e * ((N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)) := by
      ring
    rw [hsplit]
    have hA : 2 * C0 * T ^ e * (R : ℝ) ^ 2 ≤ 2 * C0 * T ^ ε * (R : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTe_le (by positivity))
        (by positivity : (0:ℝ) ≤ (R:ℝ)^2)
      nlinarith [this]
    have hB : 2 * C0 * T ^ e * ((N : ℝ) ^ (1 + e) * ((R : ℝ) + 1))
        ≤ 4 * C0 * T ^ ε * ((N : ℝ) * (R : ℝ)) := by
      have h3 : (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1) ≤ ((N : ℝ) * T ^ e) * (2 * (R : ℝ)) :=
        mul_le_mul hN1e' hR1' (by positivity) (by positivity)
      have h4 : 2 * C0 * T ^ e * (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)
          ≤ 2 * C0 * T ^ e * (((N : ℝ) * T ^ e) * (2 * (R : ℝ))) := by
        have := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * C0 * T ^ e)
        nlinarith [this]
      have h5 : 2 * C0 * T ^ e * ((N : ℝ) ^ (1 + e) * ((R : ℝ) + 1))
          = 2 * C0 * T ^ e * (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1) := by ring
      have h6 : 4 * C0 * T ^ ε * ((N : ℝ) * (R : ℝ)) = 4 * C0 * T ^ ε * ((N : ℝ) * (R : ℝ)) := rfl
      rw [h5]
      calc 2 * C0 * T ^ e * (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1)
          ≤ 2 * C0 * T ^ e * (((N : ℝ) * T ^ e) * (2 * (R : ℝ))) := h4
        _ = 4 * C0 * (T ^ e * T ^ e) * ((N : ℝ) * (R : ℝ)) := by ring
        _ = 4 * C0 * T ^ (2 * e) * ((N : ℝ) * (R : ℝ)) := by
              rw [show T ^ e * T ^ e = T ^ (2 * e) by
                rw [← Real.rpow_add (by linarith : (0:ℝ) < T)]
                congr 1; ring]
        _ ≤ 4 * C0 * T ^ ε * ((N : ℝ) * (R : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2e_le (by positivity)) (by positivity)
    have hsum : 2 * C0 * T ^ ε * (R : ℝ) ^ 2 + 4 * C0 * T ^ ε * ((N : ℝ) * (R : ℝ))
        ≤ 6 * C0 * T ^ ε * ((R : ℝ) ^ 2 + (N : ℝ) * (R : ℝ)) := by
      have hC0nn : 0 ≤ C0 := hC0.le
      nlinarith [hTe1, hC0nn, hR0, hN0, sq_nonneg (R:ℝ)]
    linarith [hA, hB, hsum]
  -- combine
  have hCval : (2 * C0 ^ 2 * Cq + 6 * C0) ≤ max (max (2 * C0 ^ 2 * Cq + 6 * C0) 400) 1 :=
    le_trans (le_max_left _ 400) (le_max_left _ 1)
  calc Sg ≤ 2 * (C0 * T ^ e * (Real.sqrt (Cq * (N : ℝ) ^ e) * (R : ℝ))) ^ 2
        + 2 * (C0 * T ^ e * ((R : ℝ) ^ 2 + (N : ℝ) ^ (1 + e) * ((R : ℝ) + 1))) := hfinal
    _ ≤ 2 * C0 ^ 2 * Cq * T ^ ε * (R : ℝ) ^ 2 + 6 * C0 * T ^ ε * K := add_le_add hterm1 hterm2
    _ ≤ (2 * C0 ^ 2 * Cq + 6 * C0) * T ^ ε * K := by
        rw [hK] at *
        nlinarith [hTe1, hC0, hCq, hR0, hN0, sq_nonneg (R:ℝ)]
    _ ≤ max (max (2 * C0 ^ 2 * Cq + 6 * C0) 400) 1 * T ^ ε * K := by
        have hTepos : (0 : ℝ) ≤ T ^ ε := le_trans (by norm_num) hTe1
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCval hTepos) hKnn

end
end Commons.NumberTheory.DirichletPolynomial
