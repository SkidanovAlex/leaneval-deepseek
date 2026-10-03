import Mathlib

namespace Work.FIArea2.Count

open scoped BigOperators

noncomputable section

lemma dls_add_pow_le (x y : ℝ) (K : ℕ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ K ≤ (2:ℝ) ^ K * (x ^ K + y ^ K) := by
  rcases le_total x y with h | h
  · have hxy : x + y ≤ 2 * y := by linarith
    calc (x + y) ^ K ≤ (2 * y) ^ K := pow_le_pow_left₀ (add_nonneg hx hy) hxy K
      _ = (2:ℝ) ^ K * y ^ K := by rw [mul_pow]
      _ ≤ (2:ℝ) ^ K * (x ^ K + y ^ K) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) K)
            linarith [pow_nonneg hx K]
  · have hxy : x + y ≤ 2 * x := by linarith
    calc (x + y) ^ K ≤ (2 * x) ^ K := pow_le_pow_left₀ (add_nonneg hx hy) hxy K
      _ = (2:ℝ) ^ K * x ^ K := by rw [mul_pow]
      _ ≤ (2:ℝ) ^ K * (x ^ K + y ^ K) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) K)
            linarith [pow_nonneg hy K]

lemma dls_log_le (H R Xj Xk : ℝ) (j k : ℕ)
    (hXj : Xj ≤ (2:ℝ)^j * (H+1)) (hXk : Xk ≤ (2:ℝ)^k * (H+1))
    (hR : 1 ≤ R) (hXj0 : 0 ≤ Xj) (hXk0 : 0 ≤ Xk) :
    Real.log (R + Xj + Xk + 2)
      ≤ Real.log (R + 2 + (2:ℝ)^j * (H+1)) + Real.log (R + 2 + (2:ℝ)^k * (H+1)) := by
  have hAj : 0 ≤ (2:ℝ)^j * (H+1) := le_trans hXj0 hXj
  have hAk : 0 ≤ (2:ℝ)^k * (H+1) := le_trans hXk0 hXk
  have hprod : R + Xj + Xk + 2
      ≤ (R + 2 + (2:ℝ)^j*(H+1)) * (R + 2 + (2:ℝ)^k*(H+1)) := by
    have key : (R + 2 + (2:ℝ)^j*(H+1)) * (R + 2 + (2:ℝ)^k*(H+1)) - (R + Xj + Xk + 2)
        = (R+2-1)*(R+2+(2:ℝ)^j*(H+1)+(2:ℝ)^k*(H+1)) + ((2:ℝ)^j*(H+1) - Xj)
          + ((2:ℝ)^k*(H+1) - Xk) + ((2:ℝ)^j*(H+1))*((2:ℝ)^k*(H+1)) := by ring
    have h1 : 0 ≤ (R+2-1)*(R+2+(2:ℝ)^j*(H+1)+(2:ℝ)^k*(H+1)) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (2:ℝ)^j*(H+1) - Xj := by linarith
    have h3 : 0 ≤ (2:ℝ)^k*(H+1) - Xk := by linarith
    have h4 : 0 ≤ ((2:ℝ)^j*(H+1))*((2:ℝ)^k*(H+1)) := mul_nonneg hAj hAk
    linarith [key, h1, h2, h3, h4]
  have hp1 : 0 < R + Xj + Xk + 2 := by linarith
  have hp2 : 0 < R + 2 + (2:ℝ)^j*(H+1) := by linarith
  have hp3 : 0 < R + 2 + (2:ℝ)^k*(H+1) := by linarith
  calc Real.log (R + Xj + Xk + 2)
      ≤ Real.log ((R + 2 + (2:ℝ)^j*(H+1)) * (R + 2 + (2:ℝ)^k*(H+1))) :=
        Real.log_le_log hp1 hprod
    _ = Real.log (R + 2 + (2:ℝ)^j*(H+1)) + Real.log (R + 2 + (2:ℝ)^k*(H+1)) :=
        Real.log_mul (ne_of_gt hp2) (ne_of_gt hp3)

theorem dyadic_log_series_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℝ) (hH : 1 ≤ H) (X : ℕ → ℕ)
        (hX : ∀ j, (2:ℝ) ^ j * H ≤ (X j : ℝ))
        (hXu : ∀ j, (X j : ℝ) ≤ (2:ℝ) ^ j * (H + 1))
        (R : ℕ) (hR : 1 ≤ R),
      Summable (fun j : ℕ × ℕ =>
          (1/4 : ℝ) ^ (j.1 + j.2) * ((X j.1 : ℝ) * (X j.2 : ℝ))
            * (Real.log ((R : ℝ) + (X j.1 : ℝ) + (X j.2 : ℝ) + 2)) ^ K) ∧
      (∑' j : ℕ × ℕ,
          (1/4 : ℝ) ^ (j.1 + j.2) * ((X j.1 : ℝ) * (X j.2 : ℝ))
            * (Real.log ((R : ℝ) + (X j.1 : ℝ) + (X j.2 : ℝ) + 2)) ^ K)
        ≤ C * (H ^ 2 + 1) * (Real.log (H + (R : ℝ) + 2)) ^ K := by
  have hTKsumm : Summable (fun j : ℕ => ((j:ℝ)^K) * (1/2:ℝ)^j) :=
    summable_pow_mul_geometric_of_norm_lt_one K (by norm_num)
  let T : ℝ := ∑' j : ℕ, ((j:ℝ)^K) * (1/2:ℝ)^j
  have hTnn : 0 ≤ T := by
    dsimp only [T]
    exact tsum_nonneg (fun j => mul_nonneg (pow_nonneg (Nat.cast_nonneg j) K) (pow_nonneg (by norm_num) _))
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let CK : ℝ := (2:ℝ)^K * (Real.log 2)^K * T / (Real.log 4)^K + 2 * (4:ℝ)^K
  have hCKpos : 0 < CK := by
    have h2 : 0 ≤ (2:ℝ)^K * (Real.log 2)^K * T / (Real.log 4)^K :=
      div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) K) (pow_nonneg hlog2nn K)) hTnn)
        (pow_nonneg hlog4pos.le K)
    have h3 : 0 < 2 * (4:ℝ)^K := by positivity
    dsimp only [CK]
    linarith
  refine ⟨(2:ℝ)^(K+3) * CK, mul_pos (by positivity) hCKpos, ?_⟩
  intro H hH X hX hXu R hR
  have hRr : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hH1nn : 0 ≤ H + 1 := by linarith
  have h2jnn : ∀ j : ℕ, 0 ≤ (2:ℝ)^j * (H+1) :=
    fun j => mul_nonneg (pow_nonneg (by norm_num) j) hH1nn
  set L : ℝ := Real.log (H + (R:ℝ) + 2) with hLdef
  let Y : ℕ → ℝ := fun j => (R:ℝ) + 2 + (2:ℝ)^j * (H+1)
  let g : ℕ → ℝ := fun j => (1/2:ℝ)^j * (Real.log (Y j))^K
  let HH : ℕ → ℝ := fun j => (1/2:ℝ)^j
  let A1 : ℝ := (H+1)^2 * (2:ℝ)^K
  let G1 : ℕ × ℕ → ℝ := fun p => A1 * (g p.1 * HH p.2)
  let G2 : ℕ × ℕ → ℝ := fun p => A1 * (HH p.1 * g p.2)
  let G : ℕ × ℕ → ℝ := fun p => G1 p + G2 p
  set f : ℕ × ℕ → ℝ := (fun p => (1/4 : ℝ) ^ (p.1 + p.2) * ((X p.1 : ℝ) * (X p.2 : ℝ))
      * (Real.log ((R : ℝ) + (X p.1 : ℝ) + (X p.2 : ℝ) + 2)) ^ K) with hfdef
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    linarith [hRr, hH]
  have hY_ge1 : ∀ j, 1 ≤ Y j := by
    intro j
    have h := h2jnn j
    dsimp only [Y]
    linarith [hRr]
  have hYpos : ∀ j, 0 < Y j := fun j => lt_of_lt_of_le one_pos (hY_ge1 j)
  -- pointwise bound
  have hpt : ∀ p : ℕ × ℕ, f p ≤ G p := by
    rintro ⟨j, k⟩
    have hXj0 : 0 ≤ (X j : ℝ) := Nat.cast_nonneg _
    have hXk0 : 0 ≤ (X k : ℝ) := Nat.cast_nonneg _
    have hweight : (1/4:ℝ)^(j+k) * ((X j:ℝ)*(X k:ℝ)) ≤ (1/2:ℝ)^j * (1/2:ℝ)^k * (H+1)^2 := by
      have hXjk : (X j:ℝ)*(X k:ℝ) ≤ ((2:ℝ)^j*(H+1)) * ((2:ℝ)^k*(H+1)) :=
        mul_le_mul (hXu j) (hXu k) hXk0 (by positivity)
      refine le_trans (mul_le_mul_of_nonneg_left hXjk (pow_nonneg (by norm_num) _)) ?_
      have hdecomp : ((2:ℝ)^j*(H+1)) * ((2:ℝ)^k*(H+1)) = (2:ℝ)^(j+k) * (H+1)^2 := by
        calc ((2:ℝ)^j*(H+1)) * ((2:ℝ)^k*(H+1))
            = ((2:ℝ)^j * (2:ℝ)^k) * ((H+1)*(H+1)) := by ring
          _ = (2:ℝ)^(j+k) * (H+1)^2 := by rw [← pow_add, ← pow_two]
      have hquarter : (1/4:ℝ)^(j+k) * (2:ℝ)^(j+k) = (1/2:ℝ)^(j+k) := by
        rw [← mul_pow]; norm_num
      have hE : (1/4:ℝ)^(j+k) * ((2:ℝ)^(j+k) * (H+1)^2)
          = (1/2:ℝ)^j * (1/2:ℝ)^k * (H+1)^2 := by
        calc (1/4:ℝ)^(j+k) * ((2:ℝ)^(j+k) * (H+1)^2)
            = ((1/4:ℝ)^(j+k) * (2:ℝ)^(j+k)) * (H+1)^2 := by ring
          _ = (1/2:ℝ)^(j+k) * (H+1)^2 := by rw [hquarter]
          _ = (1/2:ℝ)^j * (1/2:ℝ)^k * (H+1)^2 := by rw [pow_add]
      rw [hdecomp, hE]
    have hlogpair : Real.log ((R:ℝ) + X j + X k + 2) ≤ Real.log (Y j) + Real.log (Y k) := by
      dsimp only [Y]
      exact dls_log_le H (R:ℝ) (X j) (X k) j k (hXu j) (hXu k) hRr hXj0 hXk0
    have hlogsum0 : 0 ≤ Real.log ((R:ℝ) + X j + X k + 2) := by
      apply Real.log_nonneg
      linarith [hRr, hXj0, hXk0]
    have hlogj0 : 0 ≤ Real.log (Y j) := Real.log_nonneg (hY_ge1 j)
    have hlogk0 : 0 ≤ Real.log (Y k) := Real.log_nonneg (hY_ge1 k)
    have hlogpow : (Real.log ((R:ℝ) + X j + X k + 2))^K
        ≤ (2:ℝ)^K * ((Real.log (Y j))^K + (Real.log (Y k))^K) := by
      calc (Real.log ((R:ℝ) + X j + X k + 2))^K
          ≤ (Real.log (Y j) + Real.log (Y k))^K := pow_le_pow_left₀ hlogsum0 hlogpair K
        _ ≤ (2:ℝ)^K * ((Real.log (Y j))^K + (Real.log (Y k))^K) :=
            dls_add_pow_le _ _ K hlogj0 hlogk0
    have hlogpownn : 0 ≤ (Real.log ((R:ℝ) + X j + X k + 2))^K := pow_nonneg hlogsum0 K
    calc f (j,k)
        = ((1/4:ℝ)^(j+k) * ((X j:ℝ)*(X k:ℝ))) * (Real.log ((R:ℝ) + X j + X k + 2))^K := rfl
      _ ≤ ((1/2:ℝ)^j * (1/2:ℝ)^k * (H+1)^2)
            * ((2:ℝ)^K * ((Real.log (Y j))^K + (Real.log (Y k))^K)) :=
          mul_le_mul hweight hlogpow hlogpownn (by positivity)
      _ = G (j,k) := by dsimp only [G, G1, G2, A1, g, HH, Y]; ring
  -- summability helpers
  have hHH_sum : Summable HH := by
    dsimp only [HH]
    exact summable_geometric_of_norm_lt_one (by norm_num)
  have hgnn : ∀ j, 0 ≤ g j := by
    intro j
    dsimp only [g]
    exact mul_nonneg (pow_nonneg (by norm_num) j) (pow_nonneg (Real.log_nonneg (hY_ge1 j)) K)
  have hHHnn : ∀ j, 0 ≤ HH j := fun j => by dsimp only [HH]; positivity
  let maj : ℕ → ℝ := fun j =>
    (2:ℝ)^K * (Real.log 2)^K * ((j:ℝ)^K * (1/2:ℝ)^j) + (4:ℝ)^K * L^K * (1/2:ℝ)^j
  have hmaj_sum : Summable maj := by
    dsimp only [maj]
    exact (hTKsumm.mul_left ((2:ℝ)^K * (Real.log 2)^K)).add (hHH_sum.mul_left ((4:ℝ)^K * L^K))
  have hpt_g : ∀ j, g j ≤ maj j := by
    intro j
    have hj0 : 0 ≤ (j:ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg j) hlog2nn
    have hl0 : 0 ≤ 2 * L := by linarith
    have hlognn : 0 ≤ Real.log (Y j) := Real.log_nonneg (hY_ge1 j)
    have hlogle : Real.log (Y j) ≤ (j:ℝ) * Real.log 2 + 2 * L := by
      have huj : (1:ℝ) ≤ (2:ℝ)^j * (H+1) := by
        have h1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
        have h2 : (1:ℝ) ≤ H+1 := by linarith
        have := mul_le_mul h1 h2 (by norm_num) (pow_nonneg (by norm_num) j)
        simpa using this
      have hYle : Y j ≤ ((2:ℝ)^j*(H+1)) * ((R:ℝ)+3) := by
        have key : ((2:ℝ)^j*(H+1))*((R:ℝ)+3) - ((R:ℝ)+2+(2:ℝ)^j*(H+1))
            = ((R:ℝ)+2) * ((2:ℝ)^j*(H+1) - 1) := by ring
        have hn : 0 ≤ ((R:ℝ)+2) * ((2:ℝ)^j*(H+1) - 1) :=
          mul_nonneg (by linarith) (by linarith)
        dsimp only [Y]
        linarith [key, hn]
      calc Real.log (Y j)
          ≤ Real.log (((2:ℝ)^j*(H+1)) * ((R:ℝ)+3)) := Real.log_le_log (hYpos j) hYle
        _ = Real.log ((2:ℝ)^j*(H+1)) + Real.log ((R:ℝ)+3) := by
              rw [Real.log_mul (by positivity) (by linarith)]
        _ = (Real.log ((2:ℝ)^j) + Real.log (H+1)) + Real.log ((R:ℝ)+3) := by
              rw [Real.log_mul (by positivity) (by linarith)]
        _ = (j:ℝ) * Real.log 2 + Real.log (H+1) + Real.log ((R:ℝ)+3) := by
              rw [Real.log_pow]
        _ ≤ (j:ℝ) * Real.log 2 + L + L := by
              have h1 : Real.log (H+1) ≤ L := by
                rw [hLdef]; apply Real.log_le_log (by linarith); linarith [hRr]
              have h2 : Real.log ((R:ℝ)+3) ≤ L := by
                rw [hLdef]; apply Real.log_le_log (by linarith); linarith [hH]
              linarith
        _ = (j:ℝ) * Real.log 2 + 2 * L := by ring
    have hpow : (Real.log (Y j))^K ≤ (2:ℝ)^K * (((j:ℝ)*Real.log 2)^K + (2*L)^K) :=
      (pow_le_pow_left₀ hlognn hlogle K).trans (dls_add_pow_le _ _ K hj0 hl0)
    dsimp only [g, maj]
    calc (1/2:ℝ)^j * (Real.log (Y j))^K
        ≤ (1/2:ℝ)^j * ((2:ℝ)^K * (((j:ℝ)*Real.log 2)^K + (2*L)^K)) :=
          mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) j)
      _ = (2:ℝ)^K * (Real.log 2)^K * ((j:ℝ)^K * (1/2:ℝ)^j) + (4:ℝ)^K * L^K * (1/2:ℝ)^j := by
          rw [show (4:ℝ)^K = (2:ℝ)^K * 2^K by rw [← mul_pow]; norm_num]
          rw [mul_pow, mul_pow]
          ring
  have hg_sum : Summable g := Summable.of_nonneg_of_le (f := maj) hgnn hpt_g hmaj_sum
  let S : ℝ := ∑' j : ℕ, g j
  have hS_le : S ≤ ∑' j : ℕ, maj j := by
    dsimp only [S]
    exact Summable.tsum_le_tsum hpt_g hg_sum hmaj_sum
  have hhh_val : (∑' j : ℕ, HH j) = 2 := by
    dsimp only [HH]
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)]
    norm_num
  have htT : (∑' j : ℕ, ((j:ℝ)^K) * (1/2:ℝ)^j) = T := by dsimp only [T]
  have hmaj_tsum : (∑' j : ℕ, maj j) = (2:ℝ)^K * (Real.log 2)^K * T + (4:ℝ)^K * L^K * 2 := by
    dsimp only [maj]
    rw [Summable.tsum_add (hTKsumm.mul_left ((2:ℝ)^K * (Real.log 2)^K))
          (hHH_sum.mul_left ((4:ℝ)^K * L^K))]
    simp_rw [tsum_mul_left]
    rw [htT, hhh_val]
  have hL4 : Real.log 4 ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by norm_num)
    linarith [hRr, hH]
  have hLK : (Real.log 4)^K ≤ L^K := pow_le_pow_left₀ hlog4pos.le hL4 K
  have hS_bound : S ≤ CK * L^K := by
    have hd : 0 < (Real.log 4)^K := pow_pos hlog4pos K
    have hATnn : 0 ≤ (2:ℝ)^K * (Real.log 2)^K * T :=
      mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) K) (pow_nonneg hlog2nn K)) hTnn
    have hstep : (2:ℝ)^K * (Real.log 2)^K * T
        ≤ (2:ℝ)^K * (Real.log 2)^K * T / (Real.log 4)^K * L^K := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      exact mul_le_mul_of_nonneg_left hLK hATnn
    have hCK : CK * L^K = (2:ℝ)^K * (Real.log 2)^K * T / (Real.log 4)^K * L^K
        + 2 * (4:ℝ)^K * L^K := by
      dsimp only [CK]; ring
    rw [hCK]
    have h4L : (4:ℝ)^K * L^K * 2 = 2 * (4:ℝ)^K * L^K := by ring
    linarith [hS_le, hmaj_tsum, hstep, h4L]
  -- summability of G1, G2, G
  have hgh_sum : Summable (fun p : ℕ × ℕ => g p.1 * HH p.2) :=
    hg_sum.mul_of_nonneg hHH_sum hgnn hHHnn
  have hhg_sum : Summable (fun p : ℕ × ℕ => HH p.1 * g p.2) :=
    hHH_sum.mul_of_nonneg hg_sum hHHnn hgnn
  have hG1_sum : Summable G1 := by dsimp only [G1]; exact hgh_sum.mul_left A1
  have hG2_sum : Summable G2 := by dsimp only [G2]; exact hhg_sum.mul_left A1
  have hG_sum : Summable G := by dsimp only [G]; exact hG1_sum.add hG2_sum
  have hfnn : ∀ p : ℕ × ℕ, 0 ≤ f p := by
    rintro ⟨j,k⟩
    have h1 : 0 ≤ (1/4:ℝ)^(j+k) := pow_nonneg (by norm_num) _
    have h2 : 0 ≤ (X j:ℝ)*(X k:ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hXj0 : 0 ≤ (X j : ℝ) := Nat.cast_nonneg _
    have hXk0 : 0 ≤ (X k : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ (Real.log ((R:ℝ) + X j + X k + 2))^K :=
      pow_nonneg (Real.log_nonneg (by linarith [hRr, hXj0, hXk0])) K
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hf_sum : Summable f := Summable.of_nonneg_of_le (f := G) hfnn hpt hG_sum
  have htsum_le : (∑' p : ℕ × ℕ, f p) ≤ ∑' p : ℕ × ℕ, G p :=
    Summable.tsum_le_tsum hpt hf_sum hG_sum
  have hgh_tsum : (∑' p : ℕ × ℕ, g p.1 * HH p.2) = S * (∑' j : ℕ, HH j) := by
    rw [Summable.tsum_prod' hgh_sum (fun a => hHH_sum.mul_left (g a))]
    simp_rw [tsum_mul_left]
    rw [tsum_mul_right]
  have hhg_tsum : (∑' p : ℕ × ℕ, HH p.1 * g p.2) = (∑' j : ℕ, HH j) * S := by
    rw [Summable.tsum_prod' hhg_sum (fun a => hg_sum.mul_left (HH a))]
    simp_rw [tsum_mul_left]
    rw [tsum_mul_right]
  have hG_tsum : (∑' p : ℕ × ℕ, G p) = (H+1)^2 * (2:ℝ)^(K+2) * S := by
    have e1 : (∑' p : ℕ × ℕ, G1 p) = A1 * (S * (∑' j : ℕ, HH j)) := by
      dsimp only [G1]
      rw [tsum_mul_left, hgh_tsum]
    have e2 : (∑' p : ℕ × ℕ, G2 p) = A1 * ((∑' j : ℕ, HH j) * S) := by
      dsimp only [G2]
      rw [tsum_mul_left, hhg_tsum]
    dsimp only [G]
    rw [Summable.tsum_add hG1_sum hG2_sum, e1, e2, hhh_val]
    have h2K : (2:ℝ)^(K+2) = (2:ℝ)^K * 4 := by
      rw [show (2:ℝ)^(K+2) = (2:ℝ)^K * (2:ℝ)^2 by rw [pow_add]]; norm_num
    rw [h2K]
    dsimp only [A1]
    ring
  have htsum_bound : (∑' p : ℕ × ℕ, f p) ≤ (H+1)^2 * (2:ℝ)^(K+2) * S := by
    rw [hG_tsum] at htsum_le
    exact htsum_le
  have hHsq : (H+1)^2 ≤ 2 * (H^2+1) := by nlinarith [sq_nonneg (H-1)]
  have h2K3 : (2:ℝ)^(K+3) = 2 * (2:ℝ)^(K+2) := by
    have hK : K + 3 = (K+2) + 1 := by omega
    rw [hK, pow_succ']
  refine ⟨hf_sum, ?_⟩
  calc (∑' p : ℕ × ℕ, f p)
      ≤ (H+1)^2 * (2:ℝ)^(K+2) * S := htsum_bound
    _ ≤ (H+1)^2 * (2:ℝ)^(K+2) * (CK * L^K) :=
        mul_le_mul_of_nonneg_left hS_bound (by positivity)
    _ ≤ (2 * (H^2+1)) * (2:ℝ)^(K+2) * (CK * L^K) := by
        have hPnn : 0 ≤ (2:ℝ)^(K+2) * (CK * L^K) :=
          mul_nonneg (by positivity) (mul_nonneg hCKpos.le (pow_nonneg hLnn K))
        have h := mul_le_mul_of_nonneg_right hHsq hPnn
        calc (H+1)^2 * (2:ℝ)^(K+2) * (CK * L^K)
            = (H+1)^2 * ((2:ℝ)^(K+2) * (CK * L^K)) := by ring
          _ ≤ (2 * (H^2+1)) * ((2:ℝ)^(K+2) * (CK * L^K)) := h
          _ = (2 * (H^2+1)) * (2:ℝ)^(K+2) * (CK * L^K) := by ring
    _ = (2:ℝ)^(K+3) * CK * (H^2+1) * L^K := by rw [h2K3]; ring

end

end Work.FIArea2.Count
