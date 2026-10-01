import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.dvd_sq_two_mul_orderOf_of_primitive
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_v_of_cubefree

namespace Commons.NumberTheory.DirichletCharacter

private lemma rpow_cubeful_step {V m β γ : ℝ} (hV : 0 ≤ V) (hm : 1 ≤ m) (hVle : V ≤ 4 * m^2)
    (hβ0 : 0 ≤ β) (hβγ : 2 * β ≤ γ) :
    V^β ≤ 4^β * m^γ := by
  calc V^β ≤ (4 * m^2)^β := Real.rpow_le_rpow hV hVle hβ0
    _ = 4^β * m^(2*β) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        rw [show m^2 = m^((2:ℝ)) by exact (Real.rpow_natCast m 2).symm,
            Real.rpow_mul (by linarith : (0:ℝ) ≤ m)]
    _ ≤ 4^β * m^γ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm hβγ)
          (Real.rpow_nonneg (by norm_num) β)

private theorem burgess_order_arith {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    {CB : ℝ} (hCB : 0 < CB)
    (hV : ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (((∏ p ∈ q.primeFactors.filter (fun p => 3 ≤ q.factorization p),
                    p ^ q.factorization p) : ℕ) : ℝ)
                ^ ((3 * (k : ℝ) - 1) / (4 * (k : ℝ) ^ 2))
            * (q : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hV
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℕ) ≤ k := by omega
    exact_mod_cast this
  set β : ℝ := (3 * (k : ℝ) - 1) / (4 * (k : ℝ) ^ 2) with hβdef
  set α : ℝ := ((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε with hαdef
  set b : ℝ := 1 - 1 / (k : ℝ) with hbdef
  have hβ0 : 0 ≤ β := by
    rw [hβdef]; apply div_nonneg <;> [nlinarith [hk1]; positivity]
  have hβle : 2 * β ≤ 3 / (2 * (k : ℝ)) := by
    rw [hβdef,
      show 2 * ((3 * (k:ℝ) - 1) / (4 * (k:ℝ)^2)) = (2 * (3 * (k:ℝ) - 1)) / (4 * (k:ℝ)^2) by ring]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * (k:ℝ)^2) (by positivity : (0:ℝ) < 2 * (k:ℝ))]
    nlinarith [hkpos]
  refine ⟨C₁ * 4 ^ β, by positivity, ?_⟩
  intro q _ χ hχ h1 N H hN hH hHq
  set V : ℕ := ∏ p ∈ q.primeFactors.filter (fun p => 3 ≤ q.factorization p),
        p ^ q.factorization p with hVdef
  have hVdvd : V ∣ (2 * orderOf χ) ^ 2 := by
    rw [hVdef]; exact dvd_sq_two_mul_orderOf_of_primitive χ hχ
  have hmem : 1 ≤ orderOf χ := by
    haveI : Finite (DirichletCharacter ℂ q) := inferInstance
    exact orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)
  have h2mpos : 0 < (2 * orderOf χ) ^ 2 := pow_pos (by omega) 2
  have hVle : V ≤ (2 * orderOf χ) ^ 2 := Nat.le_of_dvd h2mpos hVdvd
  have hmR : (1:ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hmem
  have hVleR : (V:ℝ) ≤ 4 * (orderOf χ : ℝ)^2 := by
    have h2 : (V:ℝ) ≤ ((2 * orderOf χ)^2 : ℕ) := by exact_mod_cast hVle
    have h3 : ((2 * orderOf χ)^2 : ℕ) = 4 * (orderOf χ)^2 := by ring
    rw [h3] at h2
    push_cast at h2
    nlinarith [h2]
  have hVβ : (V:ℝ)^β ≤ 4^β * (orderOf χ : ℝ) ^ ((3:ℝ)/(2*(k:ℝ))) :=
    rpow_cubeful_step (by positivity) hmR hVleR hβ0 hβle
  have hqnn : (0:ℝ) ≤ (q:ℝ)^α := Real.rpow_nonneg (by positivity) _
  have hHnn : (0:ℝ) ≤ (H:ℝ)^b := Real.rpow_nonneg (by positivity) _
  have hprod : (V:ℝ)^β * (q:ℝ)^α * (H:ℝ)^b
      ≤ (4^β * (orderOf χ : ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (q:ℝ)^α * (H:ℝ)^b := by
    apply mul_le_mul_of_nonneg_right _ hHnn
    apply mul_le_mul_of_nonneg_right _ hqnn
    exact hVβ
  have hmain : ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖
      ≤ C₁ * (V:ℝ)^β * (q:ℝ)^α * (H:ℝ)^b := hC₁ χ hχ h1 hN hH hHq
  have key : C₁ * (V:ℝ)^β * (q:ℝ)^α * (H:ℝ)^b
      = C₁ * ((V:ℝ)^β * (q:ℝ)^α * (H:ℝ)^b) := by ring
  rw [key] at hmain
  calc ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖
      ≤ C₁ * ((V:ℝ)^β * (q:ℝ)^α * (H:ℝ)^b) := hmain
    _ ≤ C₁ * ((4^β * (orderOf χ : ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (q:ℝ)^α * (H:ℝ)^b) :=
        mul_le_mul_of_nonneg_left hprod hC₁pos.le
    _ = (C₁ * 4^β) * (orderOf χ : ℝ)^((3:ℝ)/(2*(k:ℝ))) * (q:ℝ)^α * (H:ℝ)^b := by ring

theorem burgess_charSum_order_of_cubefree {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    {CB : ℝ} (hCB : 0 < CB)
    (hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) :=
  burgess_order_arith hε k hk hCB (burgess_charSum_v_of_cubefree hε k hk hCB hB)

end Commons.NumberTheory.DirichletCharacter
