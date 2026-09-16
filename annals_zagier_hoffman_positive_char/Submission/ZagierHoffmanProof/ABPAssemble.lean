import Submission.ZagierHoffmanProof.ABPZeros
import Submission.Commons.Topology.Algebra.Valued.gauss_coeff_sum_mul_polynomial
import Submission.ZagierHoffmanProof.ABPFinal

/-!
# Step (C) of the ABP criterion: the endgame

This module assembles the vanishing of the auxiliary function `E = ∑ᵢ hᵢψᵢ` and the ABP
criterion from steps (A) and (B).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §1. The arithmetic of `N → ∞` -/

lemma ambKappa_zero_eq : (ambKappa F 0 : ℚᵐ⁰) = WithZero.exp ((Nat.card F : ℚ) - 1) := by
  rw [ambKappa, pow_zero, div_one]

lemma ambKappa_div (N : ℕ) : ((ambKappa F N) / (ambKappa F 0) : ℚᵐ⁰)
    = WithZero.exp (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ N - ((Nat.card F : ℚ) - 1)) := by
  rw [ambKappa_zero_eq, ambKappa, div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr 1
  ring

/-- **The key estimate**: for `N` large the product `exp cAb * (exp c * κ^(auxDeg N ℓ) * Aψ) *
(κ_N/κ_0)^N` is `< 1`. -/
lemma exists_aux_N {c cAb : ℚ} {Aψ : ℚᵐ⁰} (hAψ : 0 < Aψ) (hℓ1 : 1 ≤ ℓ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      WithZero.exp cAb * (WithZero.exp c * (ambKappa F 0) ^ (auxDeg N ℓ) * Aψ)
        * ((ambKappa F N) / (ambKappa F 0)) ^ N < 1 := by
  have hq1 : (1 : ℚ) < Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 1 < Nat.card F)
  have hℓpos : (0 : ℚ) < 2 * (ℓ : ℚ) := by positivity
  set a : ℚᵐ⁰ := WithZero.exp (-(((Nat.card F : ℚ) - 1) / (2 * (ℓ : ℚ)))) with ha
  have ha1 : a < 1 := by
    rw [ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    have : (0 : ℚ) < ((Nat.card F : ℚ) - 1) / (2 * (ℓ : ℚ)) :=
      div_pos (by linarith) hℓpos
    linarith
  set K : ℚᵐ⁰ := WithZero.exp (cAb + c) * Aψ * WithZero.exp (2 * ((Nat.card F : ℚ) - 1)) with hK
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (mul_pos WithZero.exp_pos hAψ) WithZero.exp_pos
  have hK0 : K ≠ 0 := ne_of_gt hKpos
  obtain ⟨N₀, hN₀⟩ := gammaArchimedean_rat a ha1 K⁻¹ (inv_ne_zero hK0)
  refine ⟨max N₀ (max 1 (4 * ℓ)), fun N hN => ?_⟩
  have hNge : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right N₀ _) hN)
  have haN : a ^ N < K⁻¹ :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (zero_le : (0 : ℚᵐ⁰) ≤ a) ha1.le hNge) hN₀
  -- the exponents
  have hexpA : (ambKappa F 0) ^ (auxDeg N ℓ)
      = WithZero.exp (((Nat.card F : ℚ) - 1) * (auxDeg N ℓ : ℚ)) := by
    rw [ambKappa_zero_eq, expmul_rat]
  have hexpB : ((ambKappa F N) / (ambKappa F 0)) ^ N
      = WithZero.exp ((N : ℚ) * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ N
          - ((Nat.card F : ℚ) - 1))) := by
    rw [ambKappa_div F N, expmul_rat]
    congr 1
    ring
  have hdiv : (N : ℚ) / (2 * (ℓ : ℚ)) - 1 ≤ ((N / (2 * ℓ) : ℕ) : ℚ) := by
    have h1 : N < (N / (2 * ℓ) + 1) * (2 * ℓ) := by
      have h2 := Nat.div_add_mod N (2 * ℓ)
      have h3 := Nat.mod_lt N (by positivity : 0 < 2 * ℓ)
      nlinarith [h2]
    have h4 : (N : ℚ) < (((N / (2 * ℓ) : ℕ) : ℚ) + 1) * (2 * ℓ) := by exact_mod_cast h1
    have g : (N : ℚ) / (2 * (ℓ : ℚ)) ≤ ((N / (2 * ℓ) : ℕ) : ℚ) + 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 * (ℓ : ℚ))]
      push_cast
      linarith
    linarith
  have hNd : (auxDeg N ℓ : ℚ) ≤ (N : ℚ) - (N : ℚ) / (2 * (ℓ : ℚ)) + 1 := by
    have h3 : ((N / (2 * ℓ) : ℕ) : ℚ) ≤ (N : ℚ) := by
      exact_mod_cast Nat.div_le_self N (2 * ℓ)
    have h4 : (auxDeg N ℓ : ℚ) = (N : ℚ) - ((N / (2 * ℓ) : ℕ) : ℚ) := by
      rw [auxDeg, Nat.cast_sub (Nat.div_le_self N (2 * ℓ))]
    rw [h4]
    linarith [hdiv]
  have hNq : (N : ℚ) ≤ (Nat.card F : ℚ) ^ N := by
    have h4 : (2 : ℚ) ≤ Nat.card F := by
      have := two_le_card_field F; exact_mod_cast this
    calc (N : ℚ) ≤ (2 : ℚ) ^ N := by
          exact_mod_cast le_of_lt (Nat.lt_two_pow_self (n := N))
      _ ≤ (Nat.card F : ℚ) ^ N := pow_le_pow_left₀ (by norm_num) h4 N
  have hkey : ((Nat.card F : ℚ) - 1) * (auxDeg N ℓ : ℚ)
      + (N : ℚ) * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ N - ((Nat.card F : ℚ) - 1))
      ≤ -(((Nat.card F : ℚ) - 1) * (N : ℚ) / (2 * (ℓ : ℚ))) + 2 * ((Nat.card F : ℚ) - 1) := by
    have hle1 : (N : ℚ) / (Nat.card F : ℚ) ^ N ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hNq
    have hmain : (auxDeg N ℓ : ℚ) - (N : ℚ) + (N : ℚ) / (Nat.card F : ℚ) ^ N
        + (N : ℚ) / (2 * (ℓ : ℚ)) ≤ 2 := by
      linarith [hNd, hle1]
    calc ((Nat.card F : ℚ) - 1) * (auxDeg N ℓ : ℚ)
          + (N : ℚ) * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ N - ((Nat.card F : ℚ) - 1))
        = ((Nat.card F : ℚ) - 1) * ((auxDeg N ℓ : ℚ) - (N : ℚ) + (N : ℚ) / (Nat.card F : ℚ) ^ N
            + (N : ℚ) / (2 * (ℓ : ℚ))) - ((Nat.card F : ℚ) - 1) * (N : ℚ) / (2 * (ℓ : ℚ)) := by ring
      _ ≤ ((Nat.card F : ℚ) - 1) * 2 - ((Nat.card F : ℚ) - 1) * (N : ℚ) / (2 * (ℓ : ℚ)) :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left hmain (by linarith)) _
      _ = -(((Nat.card F : ℚ) - 1) * (N : ℚ) / (2 * (ℓ : ℚ))) + 2 * ((Nat.card F : ℚ) - 1) := by ring
  have hbound : (ambKappa F 0) ^ (auxDeg N ℓ) * ((ambKappa F N) / (ambKappa F 0)) ^ N
      ≤ a ^ N * WithZero.exp (2 * ((Nat.card F : ℚ) - 1)) := by
    rw [hexpA, hexpB, ha, expmul_rat, ← WithZero.exp_add]
    refine WithZero.exp_le_exp.mpr ?_
    show ((Nat.card F : ℚ) - 1) * (auxDeg N ℓ : ℚ)
        + (N : ℚ) * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ N - ((Nat.card F : ℚ) - 1))
      ≤ -(((Nat.card F : ℚ) - 1) / (2 * (ℓ : ℚ))) * (N : ℚ) + 2 * ((Nat.card F : ℚ) - 1)
    have h2 : -(((Nat.card F : ℚ) - 1) / (2 * (ℓ : ℚ))) * (N : ℚ)
        = -(((Nat.card F : ℚ) - 1) * (N : ℚ) / (2 * (ℓ : ℚ))) := by ring
    rw [h2]
    exact hkey
  calc WithZero.exp cAb * (WithZero.exp c * (ambKappa F 0) ^ (auxDeg N ℓ) * Aψ)
        * ((ambKappa F N) / (ambKappa F 0)) ^ N
      = (WithZero.exp cAb * WithZero.exp c) * Aψ
          * ((ambKappa F 0) ^ (auxDeg N ℓ) * ((ambKappa F N) / (ambKappa F 0)) ^ N) := by ac_rfl
    _ = WithZero.exp (cAb + c) * Aψ
          * ((ambKappa F 0) ^ (auxDeg N ℓ) * ((ambKappa F N) / (ambKappa F 0)) ^ N) := by
        rw [WithZero.exp_add]
    _ ≤ WithZero.exp (cAb + c) * Aψ * (a ^ N * WithZero.exp (2 * ((Nat.card F : ℚ) - 1))) :=
        mul_le_mul_of_nonneg_left hbound (mul_nonneg WithZero.exp_pos.le hAψ.le)
    _ = K * a ^ N := by rw [hK]; ac_rfl
    _ < K * K⁻¹ := mul_lt_mul_of_pos_left haN hKpos
    _ = 1 := mul_inv_cancel₀ hK0

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §2. The Gauss norm of `E = ∑ᵢ hᵢψᵢ` -/

/-- **The Gauss norm of the auxiliary function is bounded** by `C * r^d * Aψ`. -/
lemma isGaussNormAt_auxFun_le {γ : ℚᵐ⁰} (hγ : γ < 1) {r C Aψ : ℚᵐ⁰} (hr : 1 ≤ r) {d : ℕ}
    {h : Fin ℓ → Polynomial (Ambient F)} (hdeg : ∀ j, (h j).natDegree ≤ d)
    (hsz : ∀ j k, Valued.v ((h j).coeff k) ≤ C)
    {ψ : Fin ℓ → PowerSeries (Ambient F)}
    (hAψ : ∀ i n, Valued.v (PowerSeries.coeff n (ψ i)) * r ^ n ≤ Aψ)
    (hse : GSuperEntire γ (∑ i, coeHom (K := Ambient F) (h i) * ψ i)) :
    ∃ A : ℚᵐ⁰, IsGaussNormAt r (∑ i, coeHom (K := Ambient F) (h i) * ψ i) A ∧
      A ≤ C * r ^ d * Aψ := by
  obtain ⟨A, hA⟩ := exists_isGaussNormAt_of_GSuperEntire hγ gammaArchimedean_rat hse r
  refine ⟨A, hA, ?_⟩
  obtain ⟨n₀, hn₀⟩ := hA.2
  have hb := Commons.Topology.Algebra.Valued.gauss_coeff_sum_mul_polynomial
    (K := Ambient F) (Γ₀ := ℚᵐ⁰) (ι := Fin ℓ) hr (p := h) (g := ψ) hdeg hsz hAψ n₀
  rw [← hn₀]
  simpa only [coeHom_apply] using hb

/-- The level-`ν` size of the functional-equation solution, measured in the level-0 value group,
is bounded by an explicit constant. -/
lemma ambKappa_funcEqMu_le (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) {c : ℚ}
    (hc : 0 ≤ c) (ν : ℕ) :
    (ambKappa F ν) ^ (2 * ℓ * funcEqMu F Φ c ν)
      ≤ WithZero.exp (2 * (ℓ : ℚ) * funcEqC F Φ c + 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1)) := by
  have hq1 : (1 : ℚ) < Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 1 < Nat.card F)
  have hqm1 : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by linarith
  have hqν : (0 : ℚ) < (Nat.card F : ℚ) ^ ν := by positivity
  have hqn : (1 : ℚ) ≤ (Nat.card F : ℚ) ^ ν := one_le_pow₀ hq1.le
  have hPB : (0 : ℚ) ≤ phiProdBound F Φ := by
    have h1 : (1 : ℚ) ≤ valBound F
        (fun p : Fin ℓ × Fin ℓ => phiProd F Φ ((0 : Fin (ℓ + 1)) : ℕ) p.1 p.2) := by
      rw [valBound]
      exact le_max_left _ _
    have h2 : valBound F
        (fun p : Fin ℓ × Fin ℓ => phiProd F Φ ((0 : Fin (ℓ + 1)) : ℕ) p.1 p.2)
        ≤ phiProdBound F Φ := by
      rw [phiProdBound]
      exact Finset.le_sup'
        (fun j : Fin (ℓ + 1) => valBound F (fun p : Fin ℓ × Fin ℓ => phiProd F Φ (j : ℕ) p.1 p.2))
        (Finset.mem_univ 0)
    linarith
  have hC0 : (0 : ℚ) ≤ funcEqC F Φ c := by
    rw [funcEqC]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg ℓ)) hc) (by positivity))
      hPB
  have hμ : (funcEqMu F Φ c ν : ℚ) ≤ (Nat.card F : ℚ) ^ ν * funcEqC F Φ c / ((Nat.card F : ℚ) - 1) + 1 := by
    rw [funcEqMu]
    refine le_of_lt (Nat.ceil_lt_add_one ?_)
    exact div_nonneg (mul_nonneg (by positivity) hC0) hqm1.le
  have hκ : (ambKappa F ν) ^ (2 * ℓ * funcEqMu F Φ c ν)
      = WithZero.exp (((2 * ℓ * funcEqMu F Φ c ν : ℕ) : ℚ)
          * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν)) := by
    rw [ambKappa, expmul_rat]
    congr 1
    ring
  rw [hκ]
  refine WithZero.exp_le_exp.mpr ?_
  have h2 : ((2 * ℓ * funcEqMu F Φ c ν : ℕ) : ℚ)
      * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν)
      ≤ 2 * (ℓ : ℚ) * funcEqC F Φ c + 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) := by
    have h3 : ((2 * ℓ * funcEqMu F Φ c ν : ℕ) : ℚ)
        = 2 * (ℓ : ℚ) * (funcEqMu F Φ c ν : ℚ) := by push_cast; ring
    rw [h3, mul_div_assoc']
    calc 2 * (ℓ : ℚ) * (funcEqMu F Φ c ν : ℚ) * ((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν
        ≤ 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) ^ ν * funcEqC F Φ c / ((Nat.card F : ℚ) - 1) + 1)
            * ((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν := by
          refine div_le_div_of_nonneg_right ?_ hqν.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hμ (mul_nonneg (by norm_num) (Nat.cast_nonneg ℓ))) hqm1.le
      _ = 2 * (ℓ : ℚ) * funcEqC F Φ c
            + 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν := by
          field_simp
          try ring
      _ ≤ 2 * (ℓ : ℚ) * funcEqC F Φ c + 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) := by
          have h4 : 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν
              ≤ 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) := by
            rw [div_le_iff₀ hqν]
            have hA : (0 : ℚ) ≤ 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) :=
              mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg ℓ)) hqm1.le
            calc 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1)
                = 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) * 1 := by ring
              _ ≤ 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) * ((Nat.card F : ℚ) ^ ν) :=
                  mul_le_mul_of_nonneg_left hqn hA
          linarith [h4]
  linarith [h2]

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §3. The vanishing of the auxiliary function -/

lemma ambKappa_le {ν μ : ℕ} (h : ν ≤ μ) : ambKappa F μ ≤ ambKappa F ν := by
  rw [ambKappa, ambKappa, WithZero.exp_le_exp]
  have hq1 : (1 : ℚ) ≤ Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 1 ≤ Nat.card F)
  have hqm1 : (0 : ℚ) ≤ (Nat.card F : ℚ) - 1 := by
    have := two_le_card_field F
    have : (1 : ℚ) ≤ Nat.card F := by exact_mod_cast (by omega : 1 ≤ Nat.card F)
    linarith
  rw [div_eq_mul_inv, div_eq_mul_inv, ← one_div, ← one_div]
  exact mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hq1 h)) hqm1

/-- **The auxiliary function vanishes identically** (ABP, Step 6). -/
theorem auxFun_eq_zero {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1) (hℓ : 2 ≤ ℓ)
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {ψ : Fin ℓ → PowerSeries (Ambient F)} (hse : ∀ i, GSuperEntire γ (ψ i))
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    {h : Fin ℓ → Polynomial (Ambient F)} {c : ℚ}
    (hsz : ∀ j k, Valued.v ((h j).coeff k) ≤ WithZero.exp c)
    {d : ℕ} (hdeg : ∀ j, (h j).natDegree ≤ d)
    {b : Fin (ℓ + 1) → Polynomial (Ambient F)}
    (hbint : ∀ j, (b j).coeff 0 ≠ 0 → 1 ≤ Valued.v ((b j).coeff 0))
    {Ab : ℚᵐ⁰} (hbnd : ∀ j, Valued.v ((b j).coeff 0) ≤ Ab)
    (hne : ∃ j, (b j).coeff 0 ≠ 0)
    (hfun : ∑ j, ((b j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        * frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ)
            (∑ i, coeHom (K := Ambient F) (h i) * ψ i) = 0)
    {Aψ : ℚᵐ⁰} (hAψpos : 0 < Aψ)
    (hAψ : ∀ i n, Valued.v (PowerSeries.coeff n (ψ i)) * (ambKappa F 0) ^ n ≤ Aψ)
    {N : ℕ} (hN : 1 ≤ N)
    (hroot : ∀ i : Fin N, evalSeriesGen (∑ i, coeHom (K := Ambient F) (h i) * ψ i)
        (ambThetaNu F (N + (i : ℕ))) = 0)
    (hsmall : Ab * (WithZero.exp c * (ambKappa F 0) ^ d * Aψ)
        * ((ambKappa F N) / (ambKappa F 0)) ^ N < 1) :
    (∑ i, coeHom (K := Ambient F) (h i) * ψ i) = 0 := by
  classical
  set E := ∑ i, coeHom (K := Ambient F) (h i) * ψ i with hE
  have hEse : GSuperEntire γ E :=
    GSuperEntire.sum hγ.le _ _ (fun i _ => (GSuperEntire.polynomial hγ0 hγ.le _).mul hγ.le (hse i))
  have hr1 : 1 ≤ ambKappa F 0 := le_of_lt (one_lt_ambKappa F 0)
  obtain ⟨A, hA, hAle⟩ := isGaussNormAt_auxFun_le F hγ (r := ambKappa F 0)
    (C := WithZero.exp c) (Aψ := Aψ) (d := d) hr1 hdeg hsz hAψ hEse
  have hsmall' : Ab * (A * ((ambKappa F N) / ambKappa F 0) ^ N) < 1 := by
    have hR : (0 : ℚᵐ⁰) ≤ ((ambKappa F N) / ambKappa F 0) ^ N :=
      pow_nonneg (div_nonneg zero_le zero_le) N
    calc Ab * (A * ((ambKappa F N) / ambKappa F 0) ^ N)
        = Ab * A * ((ambKappa F N) / ambKappa F 0) ^ N := by rw [mul_assoc]
      _ ≤ Ab * (WithZero.exp c * (ambKappa F 0) ^ d * Aψ) * ((ambKappa F N) / ambKappa F 0) ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAle zero_le) hR
      _ < 1 := hsmall
  -- the functional equation in `Finset.range` form
  set bN : ℕ → Polynomial (Ambient F) := fun j => if h : j < ℓ + 1 then b ⟨j, h⟩ else 0
    with hbN
  have hfe' : ∑ j ∈ Finset.range (ℓ + 1),
      ((bN j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        * frobTwist (R := Ambient F) (p := Nat.card F) j E = 0 := by
    rw [← hfun, Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hbN]
    simp only [dif_pos (Finset.mem_range.mp hj)]
  have hbint' : ∀ j, (bN j).coeff 0 ≠ 0 → 1 ≤ Valued.v ((bN j).coeff 0) := by
    intro j hj
    rw [hbN] at hj ⊢
    by_cases h : j < ℓ + 1
    · simp only [dif_pos h] at hj ⊢
      exact hbint ⟨j, h⟩ hj
    · exfalso
      simp only [dif_neg h, Polynomial.coeff_zero] at hj
      exact hj rfl
  have hbnd' : ∀ j, Valued.v ((bN j).coeff 0) ≤ Ab := by
    intro j
    rw [hbN]
    by_cases h : j < ℓ + 1
    · simp only [dif_pos h]
      exact hbnd ⟨j, h⟩
    · simp only [dif_neg h, Polynomial.coeff_zero, map_zero]
      exact (zero_le : (0 : ℚᵐ⁰) ≤ Ab)
  have hne' : ∃ j ∈ Finset.range (ℓ + 1), (bN j).coeff 0 ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    refine ⟨(j : ℕ), Finset.mem_range.mpr j.isLt, ?_⟩
    rw [hbN]
    simpa only [dif_pos j.isLt] using hj
  have hrr : ambKappa F N < ambKappa F 0 := by
    refine lt_of_le_of_ne (ambKappa_le F (show 0 ≤ N by omega)) ?_
    intro hcon
    exact absurd (ambKappa_injective F hcon) (by omega)
  have hω1 : ∀ i : Fin N, 1 ≤ Valued.v (ambThetaNu F (N + (i : ℕ))) := by
    intro i
    rw [v_ambThetaNu]
    exact le_of_lt (one_lt_ambKappa F _)
  have hω2 : ∀ i : Fin N, Valued.v (ambThetaNu F (N + (i : ℕ))) ≤ ambKappa F N := by
    intro i
    rw [v_ambThetaNu]
    exact ambKappa_le F (by omega)
  have hinj : Function.Injective (fun i : Fin N => ambThetaNu F (N + (i : ℕ))) := by
    intro a b hab
    have h := ambThetaNu_injective F hab
    omega
  have hroot' : ∀ i : Fin N, evalSeriesGen E (ambThetaNu F (N + (i : ℕ))) = 0 := fun i => hroot i
  exact eq_zero_of_functional_eq hγ0 hγ gammaArchimedean_rat (two_le_card_field F) hEse hfe'
    hbint' hbnd' hne' (le_of_lt (one_lt_ambKappa F N)) hrr hω1 hω2 hinj hroot' hA hsmall'

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §4. A common Gauss bound for `ψ` -/

lemma exists_gauss_bound_psi {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1) {κ : ℚᵐ⁰} (hκ : 0 < κ)
    {ψ : Fin ℓ → PowerSeries (Ambient F)} (hse : ∀ i, GSuperEntire γ (ψ i)) :
    ∃ Aψ : ℚᵐ⁰, 0 < Aψ ∧ ∀ i n, Valued.v (PowerSeries.coeff n (ψ i)) * κ ^ n ≤ Aψ := by
  obtain ⟨M, hM⟩ := gammaArchimedean_rat γ hγ κ⁻¹ (inv_ne_zero (ne_of_gt hκ))
  have hMκ : γ ^ M * κ < 1 := by
    have h := mul_lt_mul_of_pos_right hM hκ
    rwa [inv_mul_cancel₀ (ne_of_gt hκ)] at h
  choose a ha using fun i => hse i M
  refine ⟨∏ i, max (a i) 1,
    Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (le_max_right (a i) 1)), fun i n => ?_⟩
  have hpos : (0 : ℚᵐ⁰) < ∏ i, max (a i) 1 :=
    Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (le_max_right (a i) 1))
  have h1 : Valued.v (PowerSeries.coeff n (ψ i)) * κ ^ n ≤ max (a i) 1 * (γ ^ M * κ) ^ n := by
    calc Valued.v (PowerSeries.coeff n (ψ i)) * κ ^ n
        ≤ a i * γ ^ (M * n) * κ ^ n :=
          mul_le_mul_of_nonneg_right (ha i n) (pow_nonneg (zero_le : (0 : ℚᵐ⁰) ≤ κ) n)
      _ ≤ max (a i) 1 * γ ^ (M * n) * κ ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (pow_nonneg (zero_le : (0 : ℚᵐ⁰) ≤ γ) (M * n)))
            (pow_nonneg (zero_le : (0 : ℚᵐ⁰) ≤ κ) n)
      _ = max (a i) 1 * (γ ^ M * κ) ^ n := by
        rw [mul_pow, ← pow_mul, mul_assoc]
  refine le_trans h1 ?_
  calc max (a i) 1 * (γ ^ M * κ) ^ n ≤ max (a i) 1 * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le hMκ.le)
          (le_trans (zero_le : (0 : ℚᵐ⁰) ≤ 1) (le_max_right (a i) 1))
    _ = max (a i) 1 := mul_one _
    _ ≤ ∏ i, max (a i) 1 :=
        Finset.single_le_prod' (fun j _ => le_max_right (a j) 1) (Finset.mem_univ i)

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §5. The ABP criterion -/

/-- ★★★ **The Anderson–Brownawell–Papanikolas criterion** (ABP04 Thm 3.1.1, Dac Thm 4.2),
assembled from steps (A), (B) and (C): for a polynomial matrix `Φ` with `det Φ = c(t-θ)^s`,
a super-entire solution `ψ` of the twisted functional equation, and a row vector `ρ` with
`ρψ(θ) = 0`, there is a polynomial row vector `P` with `Pψ = 0` and `P(θ) = ρ`.

The hypothesis on `Φ` and `ϑ` is stated at a level `ν`: all the coefficients lie in
`A_ν = F_q[θ_ν]` (the case `ν = 0`, `A_0 = F_q[θ]`, is what ABP's own statement uses; Dac's
t-motive has `A_1`-coefficients because of the `(−1)`-twist of the Anderson–Thakur polynomials). -/
theorem ABP_criterion {ℓ : ℕ} (ν : ℕ) (hℓ : 2 ≤ ℓ)
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambA F ν)
    {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)} (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1)
    {ψ : Fin ℓ → PowerSeries (Ambient F)} (hse : ∀ i, GSuperEntire γ (ψ i))
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    (hind : LinearIndependent (Ambient F) (fun i : Fin (ℓ - 1) => fun j : Fin ℓ => ϑ j i))
    {ρ : Fin ℓ → Ambient F} (hρ : Matrix.vecMul ρ ϑ = 0) (hρ0 : ρ ≠ 0)
    (hval : dotProduct ρ (fun i => evalSeriesGen (ψ i) (ambTheta F)) = 0)
    {c : Ambient F} (hc : c ≠ 0) {s : ℕ}
    (hdet : Φ.det = Polynomial.C c * (Polynomial.X - Polynomial.C (ambTheta F)) ^ s) :
    ∃ P : Fin ℓ → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * ψ j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = ρ j) := by
  classical
  have hℓ1 : 1 ≤ ℓ := by omega
  have hΘ : ∀ i j m, (Φ.adjugate i j).coeff m ∈ ambA F ν :=
    fun i j m => adjugate_coeff_mem F hΦ i j m
  obtain ⟨Aψ, hAψpos, hAψ⟩ := exists_gauss_bound_psi F hγ0 hγ (lt_trans zero_lt_one (one_lt_ambKappa F 0)) hse
  set cc : ℚ := 2 * ℓ * auxC F ν Φ.adjugate hΘ ϑ hϑ with hcc
  have hccpos : 0 < cc := by
    rw [hcc]
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (by omega))) (auxC_pos F ν _ hΘ ϑ hϑ)
  set cAb : ℚ := 2 * (ℓ : ℚ) * funcEqC F Φ cc + 2 * (ℓ : ℚ) * ((Nat.card F : ℚ) - 1) with hcAb
  obtain ⟨N₀, hN₀⟩ := exists_aux_N F (c := cc) (cAb := cAb) (Aψ := Aψ) hAψpos hℓ1
  set N : ℕ := max (4 * ℓ) (max N₀ 1) with hNdef
  have hN4 : 4 * ℓ ≤ N := by
    rw [hNdef]; exact le_max_left _ _
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact le_trans (le_max_right N₀ 1) (le_max_right (4 * ℓ) (max N₀ 1))
  have hNge : N₀ ≤ N := by
    rw [hNdef]
    exact le_trans (le_max_left N₀ 1) (le_max_right (4 * ℓ) (max N₀ 1))
  -- (A) the auxiliary function
  obtain ⟨ν', h, hν', hh0, hhmem, hhdeg, hhsz, hhaux, hhne⟩ :=
    aux_function_exists F ν hℓ Φ.adjugate hΘ ϑ hϑ hN4
  have hνle : ν ≤ ν' := le_trans (Nat.le_add_right ν (2 * N)) hν'
  -- (B) the functional equation for `E`
  obtain ⟨b, hb0, hbmem, hbfun⟩ :=
    func_eq_exists F (ν := ν') hℓ1 (fun i j m => ambA_mono F hνle (hΦ i j m)) hfe hhmem
      hccpos hhsz
  -- (C3) a solution with a non-vanishing constant term
  obtain ⟨b', hb'0, hb'ne, hb'fun, hb'mem, hb'sz, _⟩ :=
    exists_no_t_factor F (ι := Fin (ℓ + 1)) (ν := ν')
      (Ab := (ambKappa F ν') ^ (2 * ℓ * funcEqMu F Φ cc ν'))
      (g := fun j => frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ)
        (∑ i, coeHom (K := Ambient F) (h i) * ψ i))
      (∑ j, (b j).natDegree) b rfl hb0 hbfun (fun j k => (hbmem j k).1) (fun j k => (hbmem j k).2)
  -- (C1) the zeros of `E`
  have hroot : ∀ i : Fin N, evalSeriesGen (∑ i, coeHom (K := Ambient F) (h i) * ψ i)
      (ambThetaNu F (N + (i : ℕ))) = 0 := by
    intro i
    exact eval_auxFun_thetaNu_eq_zero F hγ0 hγ hℓ hse hfe (by omega) hind hρ hρ0 hval
      (hhaux i) hc hdet
  -- (C2) the vanishing of `E`
  have hAb : (ambKappa F ν') ^ (2 * ℓ * funcEqMu F Φ cc ν') ≤ WithZero.exp cAb := by
    rw [hcAb]
    exact ambKappa_funcEqMu_le F Φ (le_of_lt hccpos) ν'
  have hsmall0 := hN₀ N hNge
  have hsmall : (ambKappa F ν') ^ (2 * ℓ * funcEqMu F Φ cc ν')
      * (WithZero.exp cc * (ambKappa F 0) ^ (auxDeg N ℓ) * Aψ)
      * ((ambKappa F N) / (ambKappa F 0)) ^ N < 1 := by
    have hY : (0 : ℚᵐ⁰) ≤ WithZero.exp cc * (ambKappa F 0) ^ (auxDeg N ℓ) * Aψ :=
      mul_nonneg (mul_nonneg WithZero.exp_pos.le (pow_nonneg (zero_le : (0 : ℚᵐ⁰) ≤ ambKappa F 0) _))
        hAψpos.le
    have hW : (0 : ℚᵐ⁰) ≤ ((ambKappa F N) / (ambKappa F 0)) ^ N :=
      pow_nonneg (div_nonneg zero_le zero_le) N
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAb hY) hW) hsmall0
  have hE0 : (∑ i, coeHom (K := Ambient F) (h i) * ψ i) = 0 :=
    auxFun_eq_zero F hγ0 hγ hℓ hse hfe (fun j k => hhsz j k) (fun j => le_of_lt (hhdeg j))
      (fun j => one_le_v_of_mem_ambA F (hb'mem j 0)) (fun j => hb'sz j 0) hb'ne hb'fun
      hAψpos hAψ hN1 hroot hsmall
  -- the final step
  obtain ⟨i0, j0, hj0⟩ := hhne
  have hM1 : 1 ≤ N + (i0 : ℕ) := by omega
  have hdetΘ : ∀ k, 1 ≤ k → ((Φ.adjugate).det).eval (ambThetaNu F k) ≠ 0 := by
    intro k hk
    rw [Matrix.det_adjugate, Polynomial.eval_pow]
    exact pow_ne_zero _ (det_eval_ne_zero F hc hdet hk)
  have hv : (fun i => (polyTwist (q := Nat.card F) (N + (i0 : ℕ)) (h i)).eval (ambTheta F)) ≠ 0 := by
    intro hcon
    have h1 : (polyTwist (q := Nat.card F) (N + (i0 : ℕ)) (h j0)).eval (ambTheta F) = 0 :=
      congrFun hcon j0
    rw [eval_polyTwist] at h1
    have hpow : Nat.card F ^ (N + (i0 : ℕ)) ≠ 0 :=
      pow_ne_zero (N + (i0 : ℕ)) (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
    exact hj0 ((pow_eq_zero_iff hpow).mp h1)
  exact criterion_final (q := Nat.card F) hℓ hfe hind hρ hρ0 hE0 (hhaux i0)
    (finalP_eval_ne_zero F hdetΘ hM1 hv)

end

end ZagierHoffmanPositiveChar
