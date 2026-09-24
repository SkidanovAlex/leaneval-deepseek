import Mathlib
import Submission.Work.GM.S2.Defs
import Submission.Work.GM.S2.hb_interval
import Submission.Work.GM.S2.sq_poly_expand

/-!
# Guth–Maynard §6, `k = 4` Hölder step against Heath–Brown

Assuming Heath–Brown's large value estimate (`Submission.GM.HBStatement`) and the standard
divisor bound `d(n) ≪_δ n^δ`, this file proves the `k = 4` form of (6.2)–(6.4) of
Guth–Maynard: for a Dirichlet polynomial of length `X ≤ N` with coefficients bounded by `1`,
the pair sum over a `1`-separated set of `R` points in `[0,T]`, `T ≤ N²`, is

`≤ C N^δ (R² X + R^{7/4} X² + R^{29/16} T^{1/8} X)`.

The proof is the `k = 4` instance of Hölder's inequality:

`∑_{i,j} |P_{ij}|² ≤ (R²)^{3/4} (∑_{i,j} |P_{ij}|⁸)^{1/4}`,

with `P_{ij}⁴` a Dirichlet polynomial of length `K⁴` whose coefficients are bounded by the
divisor function (via the divisor bound), to which `hb_interval` (Heath–Brown for an initial
interval) is applied.
-/

namespace Work.GM.S2

set_option maxHeartbeats 1600000

open Complex Finset
open scoped BigOperators

/-- `(x^y)^n = x^(y*n)` for `x ≥ 0`, `y` real, `n` natural. -/
lemma rpow_nat_pow (x : ℝ) (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x^y)^n = x^(y*n) := by
  rw [← Real.rpow_natCast (x^y) n, ← Real.rpow_mul hx]

/-- Fourth-power Hölder inequality: for a finite family of nonnegative reals,
`(∑ xᵢ)⁴ ≤ (#ι)³ · ∑ xᵢ⁴`. -/
lemma sum_fourth_pow_le (ι : Type*) [Fintype ι] (x : ι → ℝ) (_hx : ∀ i, 0 ≤ x i) :
    (∑ i, x i) ^ 4 ≤ (Fintype.card ι : ℝ) ^ 3 * ∑ i, (x i) ^ 4 := by
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  have hA : (∑ i, x i)^2 ≤ c * ∑ i, (x i)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1:ℝ)) x
    simpa [c, Finset.sum_const, nsmul_eq_mul] using h
  have hB : (∑ i, (x i)^2)^2 ≤ c * ∑ i, ((x i)^2)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1:ℝ))
      (fun i => (x i)^2)
    simpa [c, Finset.sum_const, nsmul_eq_mul] using h
  calc (∑ i, x i)^4 = ((∑ i, x i)^2)^2 := by ring
    _ ≤ (c * ∑ i, (x i)^2)^2 := pow_le_pow_left₀ (by positivity) hA 2
    _ = c^2 * (∑ i, (x i)^2)^2 := by ring
    _ ≤ c^2 * (c * ∑ i, ((x i)^2)^2) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = c^3 * ∑ i, (x i)^4 := by
        rw [show (∑ i, ((x i)^2)^2) = ∑ i, (x i)^4 from
          Finset.sum_congr rfl (fun i _ => by ring)]
        ring

/-- For nonnegative `a b c`: `a⁴ + b⁴ + c⁴ ≤ (a+b+c)⁴`. -/
lemma four_pow_add_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a^4 + b^4 + c^4 ≤ (a+b+c)^4 := by
  have expand : (a+b+c)^4 - (a^4+b^4+c^4)
      = 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + 4*a^3*c + 12*a^2*b*c + 12*a*b^2*c + 6*a^2*c^2
        + 12*a*b*c^2 + 4*a*c^3 + 4*b^3*c + 6*b^2*c^2 + 4*b*c^3 := by ring_nf
  have h1 : 0 ≤ 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + 4*a^3*c + 12*a^2*b*c + 12*a*b^2*c + 6*a^2*c^2
        + 12*a*b*c^2 + 4*a*c^3 + 4*b^3*c + 6*b^2*c^2 + 4*b*c^3 := by positivity
  linarith [expand, h1]

/-- Arithmetic core of the `k = 4` Hölder step: the three summands on the left are each
dominated by the corresponding fourth power of a summand on the right. -/
lemma holder4_pow_arith (R K X T : ℝ) (hR : 1 ≤ R) (hK : 0 ≤ K) (hKX : K ≤ X) (hT : 0 ≤ T) :
    (R^2)^3 * (R^2 * K^4 + R * K^8 + R ^ ((5:ℝ)/4) * T ^ ((1:ℝ)/2) * K^4)
      ≤ (R^2 * X + R ^ ((7:ℝ)/4) * X^2 + R ^ ((29:ℝ)/16) * T ^ ((1:ℝ)/8) * X)^4 := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hX0 : 0 ≤ X := le_trans hK hKX
  have hK4 : K^4 ≤ X^4 := pow_le_pow_left₀ hK hKX 4
  have hK8 : K^8 ≤ X^8 := pow_le_pow_left₀ hK hKX 8
  have hp1 : (R ^ ((7:ℝ)/4))^4 = R^7 := by
    rw [← Real.rpow_natCast (R ^ ((7:ℝ)/4)) 4, ← Real.rpow_mul hR0]; norm_num
  have hp2 : (R ^ ((29:ℝ)/16))^4 = R ^ ((29:ℝ)/4) := by
    rw [← Real.rpow_natCast (R ^ ((29:ℝ)/16)) 4, ← Real.rpow_mul hR0]; norm_num
  have hp3 : (T ^ ((1:ℝ)/8))^4 = T ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_natCast (T ^ ((1:ℝ)/8)) 4, ← Real.rpow_mul hT]; norm_num
  have hRpow : R ^ ((29:ℝ)/4) = (R^2)^3 * R ^ ((5:ℝ)/4) := by
    rw [show ((29:ℝ)/4) = (6:ℝ) + 5/4 by norm_num, Real.rpow_add (by linarith)]
    have h6 : R ^ (6:ℝ) = (R^2)^3 := by
      rw [show (6:ℝ) = ((6:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [h6]
  have hsum4 : (R^2*X)^4 + (R ^ ((7:ℝ)/4)*X^2)^4 + (R ^ ((29:ℝ)/16)*T ^ ((1:ℝ)/8)*X)^4
      ≤ (R^2 * X + R ^ ((7:ℝ)/4) * X^2 + R ^ ((29:ℝ)/16) * T ^ ((1:ℝ)/8) * X)^4 :=
    four_pow_add_le _ _ _ (by positivity) (by positivity) (by positivity)
  have hA : (R^2)^3 * (R^2 * K^4) ≤ (R^2 * X)^4 := by
    have h1 : (R^2 * X)^4 = (R^2)^3 * (R^2 * X^4) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK4 (by positivity)) (by positivity)
  have hB : (R^2)^3 * (R * K^8) ≤ (R ^ ((7:ℝ)/4) * X^2)^4 := by
    have h1 : (R ^ ((7:ℝ)/4) * X^2)^4 = (R^2)^3 * (R * X^8) := by rw [mul_pow, hp1]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK8 hR0) (by positivity)
  have hC : (R^2)^3 * (R ^ ((5:ℝ)/4) * T ^ ((1:ℝ)/2) * K^4)
      ≤ (R ^ ((29:ℝ)/16) * T ^ ((1:ℝ)/8) * X)^4 := by
    have h1 : (R ^ ((29:ℝ)/16) * T ^ ((1:ℝ)/8) * X)^4
        = (R^2)^3 * (R ^ ((5:ℝ)/4) * T ^ ((1:ℝ)/2) * X^4) := by
      rw [mul_pow, mul_pow, hp2, hp3, hRpow]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK4 (by positivity)) (by positivity)
  calc (R^2)^3 * (R^2 * K^4 + R * K^8 + R ^ ((5:ℝ)/4) * T ^ ((1:ℝ)/2) * K^4)
      = (R^2)^3 * (R^2 * K^4) + (R^2)^3 * (R * K^8)
        + (R^2)^3 * (R ^ ((5:ℝ)/4) * T ^ ((1:ℝ)/2) * K^4) := by ring
    _ ≤ (R^2*X)^4 + (R ^ ((7:ℝ)/4)*X^2)^4 + (R ^ ((29:ℝ)/16)*T ^ ((1:ℝ)/8)*X)^4 := by
        linarith [hA, hB, hC]
    _ ≤ (R^2 * X + R ^ ((7:ℝ)/4) * X^2 + R ^ ((29:ℝ)/16) * T ^ ((1:ℝ)/8) * X)^4 := hsum4

theorem holder_hb4 (hHB : Submission.GM.HBStatement)
    (hDiv : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ δ) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (T X : ℝ), 1 ≤ T → T ≤ (N : ℝ) ^ 2 → 1 ≤ X → X ≤ (N : ℝ) →
    ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i, t i ∈ Set.Icc 0 T) → (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      (∀ (a : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ m : ℕ, X < (m : ℝ) → a m = 0) →
        (∑ i : Fin R, ∑ j : Fin R,
          ‖∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor X),
              a m * (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        ≤ C * (N : ℝ) ^ δ * ((R : ℝ) ^ 2 * X + (R : ℝ) ^ ((7 : ℝ) / 4) * X ^ 2
            + (R : ℝ) ^ ((29 : ℝ) / 16) * T ^ ((1 : ℝ) / 8) * X)) := by
  intro δ hδ
  have hδ16 : (0:ℝ) < δ/16 := by linarith
  have hδ8 : (0:ℝ) < δ/8 := by linarith
  obtain ⟨Cdiv, hCdivpos, hCdivb⟩ := hDiv (δ/16) hδ16
  obtain ⟨Cint, hCintpos, hCintb⟩ := hb_interval hHB (δ/8) hδ8 (δ/16) hδ16
  have hCpos : 0 < Cint * Cdiv^6 := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max 1 ((Cint * Cdiv^6) ^ (1/(2*δ))))
  refine ⟨max 1 (Cint * Cdiv^6), ?_, N₀, ?_⟩
  · rw [lt_max_iff]; left; norm_num
  intro N hN T X hT1 hTN hX1 hXN R t htIcc htsep a ha1 hasupp
  have hNge : (1:ℝ) ≤ (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (N₀:ℝ) := le_trans (le_max_left _ _) hN₀
    have h2 : (N₀:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNgrow : Cint * Cdiv^6 ≤ (N:ℝ)^(2*δ) := by
    have h1 : (Cint * Cdiv^6) ^ (1/(2*δ)) ≤ (N₀:ℝ) := le_trans (le_max_right _ _) hN₀
    have h2 : (N₀:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have h3 : ((Cint*Cdiv^6)^(1/(2*δ)))^(2*δ) ≤ (N:ℝ)^(2*δ) :=
      Real.rpow_le_rpow (by positivity) (le_trans h1 h2) (by linarith)
    have h4 : ((Cint*Cdiv^6)^(1/(2*δ)))^(2*δ) = Cint*Cdiv^6 := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ Cint*Cdiv^6)]
      rw [show (1/(2*δ)) * (2*δ) = 1 by field_simp]
      rw [Real.rpow_one]
    rw [h4] at h3
    exact h3
  by_cases hR0 : R = 0
  · subst hR0
    simp [Real.zero_rpow]
  · have hR1 : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr hR0
    have hR1' : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR1
    set K : ℕ := Nat.floor X with hKdef
    have hK1 : 1 ≤ K := by rw [hKdef]; exact Nat.le_floor (by simpa using hX1)
    have hKX : (K:ℝ) ≤ X := by rw [hKdef]; exact Nat.floor_le (by linarith)
    have hKN : (K:ℝ) ≤ (N:ℝ) := le_trans hKX hXN
    have hK0 : (0:ℝ) ≤ (K:ℝ) := by positivity
    have hKKN4 : (K:ℝ)^4 ≤ (N:ℝ)^4 := pow_le_pow_left₀ hK0 hKN 4
    have hKpos : 0 < K := by omega
    set KK : ℕ := (K*K)*(K*K) with hKKdef
    have hKK1 : 1 ≤ KK := by
      rw [hKKdef]
      exact Nat.mul_pos (Nat.mul_pos hKpos hKpos) (Nat.mul_pos hKpos hKpos)
    have hKKcast : ((KK:ℕ):ℝ) = (K:ℝ)^4 := by rw [hKKdef]; push_cast; ring
    set Kc : ℝ := (Cdiv * (N:ℝ)^(δ/4))^3 with hKcdef
    have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
    -- ### the coefficients of the fourth power
    set b2 : ℕ → ℂ := fun m =>
      ∑ e ∈ (Finset.Icc 1 K).filter (fun e => e ∣ m ∧ m / e ≤ K), a e * a (m / e) with hb2def
    set b4 : ℕ → ℂ := fun n =>
      ∑ m ∈ (Finset.Icc 1 (K*K)).filter (fun m => m ∣ n ∧ n / m ≤ K*K), b2 m * b2 (n / m)
      with hb4def
    set c : ℕ → ℂ := fun n => if n ∈ Finset.Icc 1 KK then b4 n / (Kc:ℂ) else 0 with hcdef
    have hb2le : ∀ m : ℕ, 1 ≤ m → ‖b2 m‖ ≤ (m.divisors.card : ℝ) := by
      intro m hm1
      rw [hb2def]
      have hmne : m ≠ 0 := by omega
      have hsub : (Finset.Icc 1 K).filter (fun e => e ∣ m ∧ m / e ≤ K) ⊆ m.divisors := by
        intro e he
        simp only [Finset.mem_filter, Finset.mem_Icc] at he
        exact Nat.mem_divisors.mpr ⟨he.2.1, hmne⟩
      calc ‖∑ e ∈ (Finset.Icc 1 K).filter (fun e => e ∣ m ∧ m / e ≤ K), a e * a (m/e)‖
          ≤ ∑ e ∈ (Finset.Icc 1 K).filter (fun e => e ∣ m ∧ m / e ≤ K), ‖a e * a (m/e)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ e ∈ (Finset.Icc 1 K).filter (fun e => e ∣ m ∧ m / e ≤ K), (1:ℝ) := by
            apply Finset.sum_le_sum
            intro e he
            rw [norm_mul]
            nlinarith [ha1 e, ha1 (m/e), norm_nonneg (a e), norm_nonneg (a (m/e))]
        _ = (((Finset.Icc 1 K).filter (fun e => e ∣ m ∧ m / e ≤ K)).card : ℝ) := by simp
        _ ≤ (m.divisors.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hdvd_card_le : ∀ p q : ℕ, q ≠ 0 → p ∣ q →
        (p.divisors.card : ℝ) ≤ (q.divisors.card : ℝ) := by
      intro p q hq hpq
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hq hpq)
    have hb4le : ∀ n, n ∈ Finset.Icc 1 KK → ‖b4 n‖ ≤ Kc := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      obtain ⟨hn1, hnKK⟩ := hn
      have hnne : n ≠ 0 := by omega
      rw [hb4def]
      set F : Finset ℕ := (Finset.Icc 1 (K*K)).filter (fun m => m ∣ n ∧ n / m ≤ K*K)
        with hFdef
      have hFsub : F ⊆ n.divisors := by
        intro m hm
        rw [hFdef] at hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm
        exact Nat.mem_divisors.mpr ⟨hm.2.1, hnne⟩
      have hstep : ‖∑ m ∈ F, b2 m * b2 (n/m)‖
          ≤ ∑ m ∈ F, (n.divisors.card : ℝ) * (n.divisors.card : ℝ) := by
        calc ‖∑ m ∈ F, b2 m * b2 (n/m)‖ ≤ ∑ m ∈ F, ‖b2 m * b2 (n/m)‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ F, (n.divisors.card : ℝ) * (n.divisors.card : ℝ) := by
              apply Finset.sum_le_sum
              intro m hmF
              have hmF' := hmF
              rw [hFdef] at hmF'
              simp only [Finset.mem_filter, Finset.mem_Icc] at hmF'
              have hm1 : 1 ≤ m := hmF'.1.1
              have hmdvd : m ∣ n := hmF'.2.1
              have hndvd : n/m ∣ n := ⟨m, (Nat.div_mul_cancel hmdvd).symm⟩
              have hnm1 : 1 ≤ n/m := by
                rcases Nat.eq_zero_or_pos (n/m) with h | h
                · exfalso
                  have : n = 0 := by rw [← Nat.div_mul_cancel hmdvd, h, zero_mul]
                  omega
                · exact h
              rw [norm_mul]
              calc ‖b2 m‖ * ‖b2 (n/m)‖ ≤ (m.divisors.card : ℝ) * ((n/m).divisors.card : ℝ) :=
                    mul_le_mul (hb2le m hm1) (hb2le (n/m) hnm1) (norm_nonneg _) (by positivity)
                _ ≤ (n.divisors.card : ℝ) * (n.divisors.card : ℝ) :=
                    mul_le_mul (hdvd_card_le m n hnne hmdvd) (hdvd_card_le (n/m) n hnne hndvd)
                      (by positivity) (by positivity)
      calc ‖∑ m ∈ F, b2 m * b2 (n/m)‖
          ≤ ∑ m ∈ F, (n.divisors.card : ℝ) * (n.divisors.card : ℝ) := hstep
        _ = (F.card : ℝ) * ((n.divisors.card : ℝ) * (n.divisors.card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) * (n.divisors.card : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_le_card hFsub
        _ = (n.divisors.card : ℝ)^3 := by ring
        _ ≤ Kc := by
            have h1 : (n.divisors.card : ℝ) ≤ Cdiv * (n:ℝ)^(δ/16) := hCdivb n hn1
            have hn4 : (n:ℝ) ≤ (N:ℝ)^4 := by
              calc (n:ℝ) ≤ ((KK:ℕ):ℝ) := by exact_mod_cast hnKK
                _ = (K:ℝ)^4 := hKKcast
                _ ≤ (N:ℝ)^4 := hKKN4
            have h2 : (n:ℝ)^(δ/16) ≤ (N:ℝ)^(δ/4) := by
              calc (n:ℝ)^(δ/16) ≤ ((N:ℝ)^4)^(δ/16) :=
                    Real.rpow_le_rpow (by positivity) hn4 (by linarith)
                _ = (N:ℝ)^(δ/4) := by
                    rw [← Real.rpow_natCast (N:ℝ) 4,
                      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]
                    congr 1
                    push_cast
                    ring
            have h3 : (n.divisors.card : ℝ) ≤ Cdiv * (N:ℝ)^(δ/4) :=
              le_trans h1 (mul_le_mul_of_nonneg_left h2 hCdivpos.le)
            calc (n.divisors.card : ℝ)^3 ≤ (Cdiv * (N:ℝ)^(δ/4))^3 :=
                  pow_le_pow_left₀ (by positivity) h3 3
              _ = Kc := by rw [hKcdef]
    have hcle : ∀ n, ‖c n‖ ≤ 1 := by
      intro n
      by_cases hn : n ∈ Finset.Icc 1 KK
      · have hcn : c n = b4 n / (Kc:ℂ) := by simp only [hcdef]; rw [if_pos hn]
        rw [hcn, norm_div]
        have hnorm : ‖(Kc:ℂ)‖ = Kc := by simp [abs_of_pos hKcpos]
        rw [hnorm]
        exact div_le_one_of_le₀ (hb4le n hn) hKcpos.le
      · have hcn : c n = 0 := by simp only [hcdef]; rw [if_neg hn]
        rw [hcn]; simp
    have hcsupp : ∀ n, n ∉ Finset.Icc 1 KK → c n = 0 := by
      intro n hn
      simp only [hcdef]; rw [if_neg hn]
    -- ### the pair sums
    set P : Fin R → Fin R → ℂ := fun i j =>
      ∑ m ∈ Finset.Icc 1 K, a m * (m:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ)) with hPdef
    set Q : Fin R → Fin R → ℂ := fun i j =>
      ∑ n ∈ Finset.Icc 1 KK, c n * (n:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ)) with hQdef
    set J : ℝ := (R:ℝ)^2*((KK:ℕ):ℝ) + (R:ℝ)*(((KK:ℕ):ℝ))^2
      + (R:ℝ)^((5:ℝ)/4)*T^((1:ℝ)/2)*((KK:ℕ):ℝ) with hJdef
    set B : ℝ := (R:ℝ)^2*X + (R:ℝ)^((7:ℝ)/4)*X^2
      + (R:ℝ)^((29:ℝ)/16)*T^((1:ℝ)/8)*X with hBdef
    have hP4 : ∀ i j, ‖P i j‖^8 = Kc^2 * ‖Q i j‖^2 := by
      intro i j
      have hsq1 : P i j ^ 2 = ∑ n ∈ Finset.Icc 1 (K*K),
          b2 n * (n:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ)) := by
        rw [hPdef, hb2def]
        exact sq_poly_expand K a (t i - t j)
      have hsq2 : (∑ n ∈ Finset.Icc 1 (K*K), b2 n * (n:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ)))^2
          = ∑ n ∈ Finset.Icc 1 KK, b4 n * (n:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ)) := by
        rw [hKKdef, hb4def]
        exact sq_poly_expand (K*K) b2 (t i - t j)
      have hP4eq : P i j ^ 4 = ∑ n ∈ Finset.Icc 1 KK,
          b4 n * (n:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ)) := by
        rw [show P i j ^ 4 = (P i j ^ 2)^2 by ring, hsq1, hsq2]
      have hbeq : (∑ n ∈ Finset.Icc 1 KK, b4 n * (n:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ)))
          = (Kc:ℂ) * Q i j := by
        rw [hQdef, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have hcn : c n = b4 n / (Kc:ℂ) := by simp only [hcdef]; rw [if_pos hn]
        rw [hcn]
        have hKcne : (Kc:ℂ) ≠ 0 := by exact_mod_cast hKcpos.ne'
        field_simp
      calc ‖P i j‖^8 = ‖P i j^4‖^2 := by rw [Complex.norm_pow]; ring
        _ = ‖∑ n ∈ Finset.Icc 1 KK, b4 n * (n:ℂ)^(Complex.I*((t i - t j : ℝ):ℂ))‖^2 := by
              rw [hP4eq]
        _ = ‖(Kc:ℂ) * Q i j‖^2 := by rw [hbeq]
        _ = Kc^2 * ‖Q i j‖^2 := by
            rw [norm_mul]
            have hnorm : ‖(Kc:ℂ)‖ = Kc := by simp [abs_of_pos hKcpos]
            rw [hnorm]; ring
    have hHolder : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2)^4
        ≤ ((R:ℝ)^2)^3 * (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^8) := by
      have h1 : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2)
          = ∑ p : Fin R × Fin R, ‖P p.1 p.2‖^2 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      have h2 : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^8)
          = ∑ p : Fin R × Fin R, ‖P p.1 p.2‖^8 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      rw [h1, h2]
      have hcard : (Fintype.card (Fin R × Fin R) : ℝ) = (R:ℝ)^2 := by
        rw [Fintype.card_prod, Fintype.card_fin]
        push_cast; ring
      have hmain := sum_fourth_pow_le (Fin R × Fin R) (fun p => ‖P p.1 p.2‖^2)
        (fun p => by positivity)
      rw [hcard] at hmain
      have hcong : (∑ p : Fin R × Fin R, (‖P p.1 p.2‖^2)^4)
          = ∑ p : Fin R × Fin R, ‖P p.1 p.2‖^8 :=
        Finset.sum_congr rfl (fun p _ => by ring)
      rw [hcong] at hmain
      exact hmain
    have hQsum := hCintb KK hKK1 T hT1 c hcle hcsupp R t htIcc htsep
    have hQsum' : (∑ i : Fin R, ∑ j : Fin R, ‖Q i j‖^2)
        ≤ Cint * T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16) * J := by
      simp only [hQdef, hJdef]
      exact hQsum
    have hKc2 : Kc^2 = Cdiv^6 * (N:ℝ)^((3:ℝ)*δ/2) := by
      rw [hKcdef, ← pow_mul, mul_pow, rpow_nat_pow (N:ℝ) (by positivity) (δ/4) 6]
      rw [show (δ/4) * ((6:ℕ):ℝ) = (3:ℝ)*δ/2 by push_cast; ring]
    have hNadd : ∀ a b : ℝ, (N:ℝ)^a * (N:ℝ)^b = (N:ℝ)^(a+b) :=
      fun a b => (Real.rpow_add hNpos a b).symm
    have hT8 : T^(δ/8) ≤ (N:ℝ)^(δ/4) := by
      calc T^(δ/8) ≤ ((N:ℝ)^2)^(δ/8) := Real.rpow_le_rpow (by linarith) hTN (by linarith)
        _ = (N:ℝ)^(δ/4) := by
            rw [← Real.rpow_natCast (N:ℝ) 2, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]
            congr 1
            push_cast
            ring
    have hKK16 : ((KK:ℕ):ℝ)^(δ/16) ≤ (N:ℝ)^(δ/4) := by
      rw [hKKcast]
      calc ((K:ℝ)^4)^(δ/16) ≤ ((N:ℝ)^4)^(δ/16) :=
            Real.rpow_le_rpow (by positivity) hKKN4 (by linarith)
        _ = (N:ℝ)^(δ/4) := by
            rw [← Real.rpow_natCast (N:ℝ) 4, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]
            congr 1
            push_cast
            ring
    have hSca : Kc^2 * (Cint * T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16)) ≤ (N:ℝ)^(4*δ) := by
      have hstep1 : Cint * T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16)
          ≤ Cint * (N:ℝ)^(δ/4) * (N:ℝ)^(δ/4) := by
        have h1 : T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16) ≤ (N:ℝ)^(δ/4) * (N:ℝ)^(δ/4) :=
          mul_le_mul hT8 hKK16 (by positivity) (by positivity)
        calc Cint * T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16)
            = Cint * (T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16)) := by ring
          _ ≤ Cint * ((N:ℝ)^(δ/4) * (N:ℝ)^(δ/4)) := mul_le_mul_of_nonneg_left h1 hCintpos.le
          _ = Cint * (N:ℝ)^(δ/4) * (N:ℝ)^(δ/4) := by ring
      calc Kc^2 * (Cint * T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16))
          ≤ (Cdiv^6 * (N:ℝ)^((3:ℝ)*δ/2)) * (Cint * (N:ℝ)^(δ/4) * (N:ℝ)^(δ/4)) := by
            rw [hKc2]
            exact mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ = (Cint * Cdiv^6) * ((N:ℝ)^((3:ℝ)*δ/2) * ((N:ℝ)^(δ/4) * (N:ℝ)^(δ/4))) := by ring
        _ = (Cint * Cdiv^6) * (N:ℝ)^(2*δ) := by
            rw [hNadd, hNadd]
            rw [show (3:ℝ)*δ/2 + (δ/4 + δ/4) = 2*δ by ring]
        _ ≤ (N:ℝ)^(2*δ) * (N:ℝ)^(2*δ) := mul_le_mul_of_nonneg_right hNgrow (by positivity)
        _ = (N:ℝ)^(4*δ) := by
            rw [hNadd]
            rw [show (2:ℝ)*δ + 2*δ = 4*δ by ring]
    have hJ : ((R:ℝ)^2)^3 * J ≤ B^4 := by
      rw [hJdef, hBdef, hKKcast]
      rw [show ((K:ℝ)^4)^2 = (K:ℝ)^8 by ring]
      exact holder4_pow_arith (R:ℝ) (K:ℝ) X T hR1' hK0 hKX (by linarith)
    have hP8 : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^8)
        = Kc^2 * (∑ i : Fin R, ∑ j : Fin R, ‖Q i j‖^2) := by
      simp only [hP4, Finset.mul_sum]
    have hS4 : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2)^4 ≤ (N:ℝ)^(4*δ) * B^4 := by
      calc (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2)^4
          ≤ ((R:ℝ)^2)^3 * (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^8) := hHolder
        _ = ((R:ℝ)^2)^3 * (Kc^2 * (∑ i : Fin R, ∑ j : Fin R, ‖Q i j‖^2)) := by rw [hP8]
        _ ≤ ((R:ℝ)^2)^3 * (Kc^2 * (Cint * T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16) * J)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hQsum' (by positivity)
        _ = (Kc^2 * (Cint * T^(δ/8) * ((KK:ℕ):ℝ)^(δ/16))) * (((R:ℝ)^2)^3 * J) := by ring
        _ ≤ (N:ℝ)^(4*δ) * B^4 := mul_le_mul hSca hJ (by positivity) (by positivity)
    have hB0 : 0 ≤ B := by rw [hBdef]; positivity
    have hS : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2) ≤ (N:ℝ)^δ * B := by
      have h4 : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2)^4 ≤ ((N:ℝ)^δ * B)^4 := by
        calc (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2)^4 ≤ (N:ℝ)^(4*δ) * B^4 := hS4
          _ = ((N:ℝ)^δ * B)^4 := by
              rw [mul_pow, rpow_nat_pow (N:ℝ) (by positivity) δ 4]
              rw [show δ * ((4:ℕ):ℝ) = 4*δ by push_cast; ring]
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h4
    have hfinal : (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2)
        ≤ max 1 (Cint * Cdiv^6) * (N:ℝ)^δ * B := by
      calc (∑ i : Fin R, ∑ j : Fin R, ‖P i j‖^2) ≤ (N:ℝ)^δ * B := hS
        _ ≤ max 1 (Cint * Cdiv^6) * (N:ℝ)^δ * B := by
            have h1 : (1:ℝ) ≤ max 1 (Cint * Cdiv^6) := le_max_left _ _
            have h2 : 0 ≤ (N:ℝ)^δ * B := mul_nonneg (by positivity) hB0
            nlinarith [h1, h2]
    simpa [hPdef, hBdef, hKdef] using hfinal

end Work.GM.S2
